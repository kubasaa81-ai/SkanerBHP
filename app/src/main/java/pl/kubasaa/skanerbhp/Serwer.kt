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
 *   GET  /stan            -> "STAN|tryb|wersja spisu chemii|zdjęć chemii|wersja maszyn|połączeń maszyn|wersja spraw|zdjęć wypadków"
 *                            (Program BHP otwarty odpytuje w tle i sam wysyła listy / zabiera zdjęcia)
 *   POST /chemia_wyniki   -> linie tekstu: co komputer zrobił ze zdjęciami etykiet
 *   POST /zdjecia_sprawy  -> "WSL|wersja" + linie "id|opis" - otwarte sprawy wypadkowe (bez nazwisk)
 *   POST /lista           -> lista do wydania (tekst BHP1 ...), telefon ją pokazuje
 *   GET  /skany?od=N      -> zeskanowane kody od numeru N, linie "N|kod"
 *   POST /wynik           -> "N|kolor|tekst" - wynik sprawdzenia skanu w komputerze (1 OK, 2 błąd, 3 uwaga)
 *   POST /koniec          -> wydanie zapisane - lista zamknięta
 *   POST /katalog         -> katalog pozycji magazynu (Dostawa / Inwentura / Kody)
 *   GET  /zdjecia         -> zdjęcia czekające w telefonie (Zdjęcia - wypadki), linie "nr|opis|id sprawy (0 = nie wybrano)"
 *   GET  /zdjecie?nr=N    -> plik JPG zdjęcia N
 *   POST /odebrane        -> "nr,nr,..." komputer zapisał zdjęcia - telefon je kasuje
 *   POST /zdjecia_sprawa  -> opis sprawy (np. "Wypadek nr 4/2026") - pokazuje się na ekranie Zdjęcia
 *   POST /chemia          -> spis substancji (produkt x wydział) do zdjęć etykiet - zostaje w telefonie
 *   GET  /chemia_zdjecia  -> zdjęcia etykiet czekające w telefonie, linie "nr|id produktu|kod wydziału|nazwa"
 *   GET  /chemia_zdjecie?nr=N -> plik JPG
 *   POST /chemia_odebrane -> "nr,nr,..." komputer zapisał zdjęcia - telefon je kasuje
 *   POST /maszyny         -> źródła z pomiarów + kartoteka maszyn (łączenie na hali)
 *   GET  /maszyny_powiazania -> przypisania z telefonu, linie "id źródła|P/R/X|id maszyn"
 *   POST /maszyny_odebrane -> "id,id" komputer zapisał połączenia
 *   POST /sms             -> "numer\ntreść" - telefon wysyła SMS (np. hasło do pliku z danymi osobowymi);
 *                            odpowiedź: OK | OTWARTO (bez zgody na SMS: otwarte Wiadomości z gotowym tekstem) | BLAD|opis
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
        fun zdjecia(): String
        fun zdjecie(nr: Int): ByteArray?
        fun odebrane(tekst: String)
        fun zdjeciaSprawa(tekst: String)
        fun sms(tekst: String): String
        fun chemia(tekst: String)
        fun chemiaZdjecia(): String
        fun chemiaZdjecie(nr: Int): ByteArray?
        fun chemiaOdebrane(tekst: String)
        fun maszyny(tekst: String)
        fun maszynyPowiazania(): String
        fun maszynyOdebrane(tekst: String)
        fun stan(): String
        fun chemiaWyniki(tekst: String)
        fun zdjeciaSprawy(tekst: String)
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

    private fun wyslij(k: Socket, b: ByteArray, typ: String, status: String) {
        val nag = "HTTP/1.1 $status\r\nContent-Type: $typ\r\n" +
                "Content-Length: ${b.size}\r\nConnection: close\r\nCache-Control: no-cache\r\n\r\n"
        val wy = k.getOutputStream()
        wy.write(nag.toByteArray(Charsets.US_ASCII))
        wy.write(b)
        wy.flush()
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

            val nrParam = parametry.split("&").firstOrNull { it.startsWith("nr=") }
                ?.substringAfter("=")?.toIntOrNull() ?: -1
            if (sciezka == "/zdjecie" || sciezka == "/chemia_zdjecie") {
                val jpg = if (sciezka == "/zdjecie") obsluga.zdjecie(nrParam) else obsluga.chemiaZdjecie(nrParam)
                if (jpg != null) {
                    wyslij(k, jpg, "image/jpeg", "200 OK")
                } else {
                    wyslij(k, "brak".toByteArray(Charsets.UTF_8), "text/plain; charset=utf-8", "404 Not Found")
                }
                return
            }
            val odp: String = when {
                sciezka == "/ping" -> obsluga.ping()
                sciezka == "/stan" -> obsluga.stan()
                sciezka == "/chemia_wyniki" && metoda == "POST" -> { obsluga.chemiaWyniki(cialo); "OK" }
                sciezka == "/zdjecia_sprawy" && metoda == "POST" -> { obsluga.zdjeciaSprawy(cialo); "OK" }
                sciezka == "/lista" && metoda == "POST" -> { obsluga.lista(cialo); "OK" }
                sciezka == "/skany" -> {
                    val od = parametry.split("&").firstOrNull { it.startsWith("od=") }
                        ?.substringAfter("=")?.let { URLDecoder.decode(it, "UTF-8").toIntOrNull() } ?: 0
                    obsluga.skany(od)
                }
                sciezka == "/wynik" && metoda == "POST" -> { obsluga.wynik(cialo); "OK" }
                sciezka == "/koniec" && metoda == "POST" -> { obsluga.koniec(cialo); "OK" }
                sciezka == "/katalog" && metoda == "POST" -> { obsluga.katalog(cialo); "OK" }
                sciezka == "/zdjecia" -> obsluga.zdjecia()
                sciezka == "/odebrane" && metoda == "POST" -> { obsluga.odebrane(cialo); "OK" }
                sciezka == "/zdjecia_sprawa" && metoda == "POST" -> { obsluga.zdjeciaSprawa(cialo); "OK" }
                sciezka == "/sms" && metoda == "POST" -> obsluga.sms(cialo)
                sciezka == "/chemia" && metoda == "POST" -> { obsluga.chemia(cialo); "OK" }
                sciezka == "/chemia_zdjecia" -> obsluga.chemiaZdjecia()
                sciezka == "/chemia_odebrane" && metoda == "POST" -> { obsluga.chemiaOdebrane(cialo); "OK" }
                sciezka == "/maszyny" && metoda == "POST" -> { obsluga.maszyny(cialo); "OK" }
                sciezka == "/maszyny_powiazania" -> obsluga.maszynyPowiazania()
                sciezka == "/maszyny_odebrane" && metoda == "POST" -> { obsluga.maszynyOdebrane(cialo); "OK" }
                sciezka == "/" -> "Skaner BHP - połączenie działa ✔"
                else -> "?"
            }
            wyslij(k, odp.toByteArray(Charsets.UTF_8), "text/plain; charset=utf-8", "200 OK")
        } catch (e: Exception) {
        } finally {
            try {
                k.close()
            } catch (e: Exception) {
            }
        }
    }
}
