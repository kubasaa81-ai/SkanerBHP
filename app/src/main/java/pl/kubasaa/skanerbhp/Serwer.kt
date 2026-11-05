package pl.kubasaa.skanerbhp

import java.io.ByteArrayOutputStream
import java.io.InputStream
import java.net.ServerSocket
import java.net.Socket
import java.net.URLDecoder
import java.util.concurrent.Executors

/**
 * Mały serwer HTTP w telefonie (port 8080). Program BHP na komputerze łączy się z nim przez GlobalProtect:
 *   GET  /ping            -> "SKANER_BHP|<tryb>"
 *   POST /lista           -> lista do wydania (tekst BHP1 ...), telefon ją pokazuje
 *   GET  /skany?od=N      -> zeskanowane kody od numeru N, linie "N|kod"
 *   POST /wynik           -> "N|kolor|tekst" - wynik sprawdzenia skanu w komputerze (1 OK, 2 błąd, 3 uwaga)
 *   POST /koniec          -> wydanie zapisane - lista zamknięta
 *   POST /katalog         -> katalog pozycji magazynu (Dostawa / Inwentura / Kody)
 */
class Serwer(private val obsluga: Obsluga) {

    interface Obsluga {
        fun ping(): String
        fun lista(tekst: String)
        fun skany(od: Int): String
        fun wynik(tekst: String)
        fun koniec(tekst: String)
        fun komputer(adres: String)
        fun katalog(tekst: String)
    }

    @Volatile private var gniazdo: ServerSocket? = null
    private val watki = Executors.newFixedThreadPool(4)

    fun start(port: Int = 8080): String? {
        if (gniazdo != null) return null
        return try {
            val s = ServerSocket(port)
            gniazdo = s
            Thread {
                while (!s.isClosed) {
                    try {
                        val k = s.accept()
                        watki.execute { obsluz(k) }
                    } catch (e: Exception) {
                    }
                }
            }.start()
            null
        } catch (e: Exception) {
            e.message ?: "błąd"
        }
    }

    fun stop() {
        try {
            gniazdo?.close()
        } catch (e: Exception) {
        }
        gniazdo = null
        watki.shutdownNow()
    }

    private fun czytajLinie(we: InputStream): String {
        val b = ByteArrayOutputStream()
        while (true) {
            val c = we.read()
            if (c < 0 || c == '\n'.code) break
            if (c != '\r'.code) b.write(c)
        }
        return b.toString("UTF-8")
    }

    private fun obsluz(k: Socket) {
        try {
            k.soTimeout = 5000
            val we = k.getInputStream()
            val pierwsza = czytajLinie(we)
            val czesci = pierwsza.split(" ")
            if (czesci.size < 2) {
                k.close()
                return
            }
            val metoda = czesci[0]
            val adres = czesci[1]
            var dlugosc = 0
            while (true) {
                val l = czytajLinie(we)
                if (l.isEmpty()) break
                val i = l.indexOf(':')
                if (i > 0 && l.substring(0, i).trim().equals("Content-Length", ignoreCase = true)) {
                    dlugosc = l.substring(i + 1).trim().toIntOrNull() ?: 0
                }
            }
            val dane = ByteArray(dlugosc)
            var n = 0
            while (n < dlugosc) {
                val r = we.read(dane, n, dlugosc - n)
                if (r < 0) break
                n += r
            }
            val cialo = String(dane, 0, n, Charsets.UTF_8)
            val sciezka = adres.substringBefore('?')
            val parametry = adres.substringAfter('?', "")
            obsluga.komputer(k.inetAddress.hostAddress ?: "")

            val odp: String = when {
                sciezka == "/ping" -> obsluga.ping()
                sciezka == "/lista" && metoda == "POST" -> { obsluga.lista(cialo); "OK" }
                sciezka == "/skany" -> {
                    val od = parametry.split("&").firstOrNull { it.startsWith("od=") }
                        ?.substringAfter("=")?.let { URLDecoder.decode(it, "UTF-8").toIntOrNull() } ?: 0
                    obsluga.skany(od)
                }
                sciezka == "/wynik" && metoda == "POST" -> { obsluga.wynik(cialo); "OK" }
                sciezka == "/koniec" && metoda == "POST" -> { obsluga.koniec(cialo); "OK" }
                sciezka == "/katalog" && metoda == "POST" -> { obsluga.katalog(cialo); "OK" }
                sciezka == "/" -> "Skaner BHP - połączenie działa ✔"
                else -> "?"
            }
            val b = odp.toByteArray(Charsets.UTF_8)
            val nag = "HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\n" +
                    "Content-Length: ${b.size}\r\nConnection: close\r\nCache-Control: no-cache\r\n\r\n"
            val wy = k.getOutputStream()
            wy.write(nag.toByteArray(Charsets.US_ASCII))
            wy.write(b)
            wy.flush()
        } catch (e: Exception) {
        } finally {
            try {
                k.close()
            } catch (e: Exception) {
            }
        }
    }
}
