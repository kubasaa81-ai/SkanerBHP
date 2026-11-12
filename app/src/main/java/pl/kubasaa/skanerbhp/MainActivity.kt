package pl.kubasaa.skanerbhp

import android.Manifest
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.media.AudioManager
import android.media.ToneGenerator
import android.net.ConnectivityManager
import android.net.NetworkCapabilities
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.telephony.SmsManager
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.text.InputType
import android.util.TypedValue
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.View
import android.view.WindowManager
import android.app.AlertDialog
import android.widget.AdapterView
import android.widget.ArrayAdapter
import android.widget.Button
import android.widget.Spinner
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.TextView
import android.widget.Toast
import androidx.activity.addCallback
import androidx.activity.result.contract.ActivityResultContracts
import androidx.appcompat.app.AppCompatActivity
import androidx.camera.core.Camera
import androidx.camera.core.CameraSelector
import androidx.camera.core.ExperimentalGetImage
import androidx.camera.core.ImageAnalysis
import android.graphics.Bitmap
import android.graphics.BitmapFactory
import android.graphics.Matrix
import android.media.ExifInterface
import android.text.Editable
import android.text.TextWatcher
import android.widget.ImageView
import androidx.activity.result.PickVisualMediaRequest
import java.io.File
import java.io.FileOutputStream
import androidx.camera.core.ImageProxy
import androidx.camera.core.Preview
import androidx.camera.lifecycle.ProcessCameraProvider
import androidx.camera.view.PreviewView
import androidx.core.content.ContextCompat
import com.google.mlkit.vision.barcode.BarcodeScanner
import com.google.mlkit.vision.barcode.BarcodeScannerOptions
import com.google.mlkit.vision.barcode.BarcodeScanning
import com.google.mlkit.vision.barcode.common.Barcode
import com.google.mlkit.vision.common.InputImage
import java.net.Inet4Address
import java.net.NetworkInterface
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import kotlin.system.exitProcess

/**
 * Skaner BHP - telefon jako skaner dla Programu BHP (Excel) przez sieć firmową (GlobalProtect).
 * Ekran startowy: Wydanie / Dostawa / Inwentura / Kody / Zakończ.
 * Wydanie: komputer wysyła listę "co wydać", aparat czyta kody, komputer pobiera skany i odsyła wynik.
 * Dostawa / Inwentura / Kody: katalog z komputera (warianty, rozmiary, stany, kody producenta) -
 *   znany kod = od razu pozycja, nieznany = wybór z listy i przypisanie kodu; polecenia @DOST / @INW / @KOD.
 * Zdjęcia (wypadki): zdjęcia zrobione zwykłym aparatem wybierasz z galerii (podgląd, opis każdego) -
 *   kopie (pomniejszone) czekają w aplikacji, komputer pobiera je do protokołu oględzin
 *   (Oględziny -> "Z telefonu") i wtedy aplikacja kasuje swoje kopie.
 */
class MainActivity : AppCompatActivity(), Serwer.Obsluga {

    private val zielony = Color.rgb(46, 125, 50)
    private val czerwony = Color.rgb(198, 40, 40)
    private val pomaranczowy = Color.rgb(230, 81, 0)
    private val szary = Color.rgb(96, 125, 139)
    private val niebieski = Color.rgb(21, 101, 192)

    private lateinit var ekranStart: LinearLayout
    private lateinit var ekranWydanie: LinearLayout
    private lateinit var ekranMag: LinearLayout
    private lateinit var ekranZdj: LinearLayout
    @Volatile private var tryb = "MENU"            // MENU / WYDANIE / DOSTAWA / INWENTURA / KODY / ZDJECIA
    private val naWydaniu: Boolean get() = tryb == "WYDANIE"

    // magazyn (dostawa / inwentura / kody)
    private lateinit var podgladWyd: PreviewView
    private lateinit var podgladMag: PreviewView
    private lateinit var tTytulMag: TextView
    private lateinit var tKomputerMag: TextView
    private lateinit var tPozycja: TextView
    private lateinit var tStanProg: TextView
    private lateinit var wIlosc: LinearLayout
    private lateinit var eIlosc: EditText
    private lateinit var bAkcja: Button
    private lateinit var tWynikMag: TextView
    private lateinit var historiaMag: LinearLayout
    private var wybrana: Kat? = null
    private var oknoOtwarte = false

    // katalog z komputera
    private class Kat(val w: Int, val r: Int, val asort: String, val wariant: String, val rozm: String, var stan: Int, val kody: MutableList<String>)
    private var katalog: List<Kat> = emptyList()
    @Volatile private var katWersja = "0"

    // zdjęcia (wypadki): pliki w katalogu aplikacji  zdjecia/zdj_<nr>.jpg  +  zdj_<nr>.txt (opis)
    private lateinit var tSprawaZdj: TextView
    private lateinit var tKomputerZdj: TextView
    private lateinit var bGaleria: Button
    private lateinit var tStanZdj: TextView
    private lateinit var listaZdj: LinearLayout
    private val wyborZdjec = registerForActivityResult(ActivityResultContracts.PickMultipleVisualMedia(30)) { uris ->
        if (uris.isNotEmpty()) importujZdjecia(uris)
    }
    @Volatile private var sprawaZdj = ""
    private val folderZdj: File by lazy { File(filesDir, "zdjecia").apply { mkdirs() } }

    // start
    private lateinit var tSiec: TextView
    private lateinit var tKomputerStart: TextView
    private lateinit var bVpn: Button

    // wydanie
    private lateinit var tKomputer: TextView
    private var podgladAkt: PreviewView? = null
    private lateinit var tKod: TextView
    private lateinit var tWynik: TextView
    private lateinit var listaWidok: LinearLayout
    private lateinit var eReczny: EditText
    private lateinit var bLatarka: Button

    private val serwer = Serwer(this)
    private val handler = Handler(Looper.getMainLooper())
    private var kamera: Camera? = null
    private var dostawcaKamery: ProcessCameraProvider? = null
    private var latarka = false
    private lateinit var watekKamery: ExecutorService
    private var skaner: BarcodeScanner? = null
    private var ton: ToneGenerator? = null

    // kontakt z komputerem
    @Volatile private var ostatniKontakt = 0L
    @Volatile private var adresKomputera = ""

    // skany (komputer pobiera je przez /skany)
    private class Skan(val nr: Int, val kod: String)
    private val skany = mutableListOf<Skan>()
    private var nastepnyNr = 1
    private var sesja = System.currentTimeMillis() % 1000000      // zmienia się przy nowej liście / starcie

    // ten sam kod nie wysyła się drugi raz, dopóki nie zniknie z kadru
    private var kodWKadrze: String? = null
    private var ostatnioWidziany = 0L
    private var ostatnioWyslany = 0L
    private var ostatniWyslanyKod: String? = null

    // lista do wydania
    private class Wpis(val rozmiar: String, val wariant: Int)
    // sztuka zeskanowana: nr skanu (do wyniku z komputera), kod (do cofnięcia), ok = komputer policzył
    private class Sztuka(val wpis: Wpis, val nr: Int, val kod: String) {
        var ok = false
    }
    private class Pozycja(
        val nazwa: String, val ilosc: Int, val rozmiar: String,
        val warianty: List<String>, val wpisy: Map<String, Wpis>
    ) {
        val skany = mutableListOf<Sztuka>()
        var uwaga = false
    }
    private val lista = mutableListOf<Pozycja>()
    private var listaTekst: String? = null
    @Volatile private var maListe = false       // dla komputera: czy telefon ma listę (gdy nie - komputer ją wyśle)
    private val cofanie = ArrayDeque<Int>()      // numery skanów sztuk na liście (kolejność - do "Cofnij")

    // skan tylko po naciśnięciu SKANUJ (przytrzymanie aparatu nie dodaje kilku sztuk)
    private var uzbrojony = false
    private lateinit var bSkanuj: Button
    private val rozbroj = Runnable { ustawSkanuj(false) }

    private val prosbaKamera = registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
        if (ok) uruchomKamere() else {
            tKod.text = "Brak zgody na aparat"
            tKod.setTextColor(czerwony)
        }
    }

    // SMS z komputera (np. hasło do pliku z danymi osobowymi) - zgoda pytana przy starcie aplikacji
    private val prosbaSms = registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
        if (!ok) Toast.makeText(this, "Bez zgody na SMS program BHP nie wyśle hasła z telefonu", Toast.LENGTH_LONG).show()
    }

    private val odswiezanie = object : Runnable {
        override fun run() {
            pokazStan()
            handler.postDelayed(this, 1500)
        }
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        watekKamery = Executors.newSingleThreadExecutor()
        ton = try {
            ToneGenerator(AudioManager.STREAM_NOTIFICATION, 90)
        } catch (e: Exception) {
            null
        }
        zbudujStart()
        zbudujWydanie()
        zbudujMagazyn()
        zbudujZdjecia()
        pokazStart()
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.SEND_SMS) != PackageManager.PERMISSION_GRANTED) {
            prosbaSms.launch(Manifest.permission.SEND_SMS)
        }
        val blad = serwer.start(8080)
        if (blad != null) Toast.makeText(this, "Serwer: $blad", Toast.LENGTH_LONG).show()
        onBackPressedDispatcher.addCallback(this) {
            if (tryb != "MENU") pokazStart() else moveTaskToBack(true)
        }
    }

    override fun onResume() {
        super.onResume()
        handler.post(odswiezanie)
    }

    override fun onPause() {
        super.onPause()
        handler.removeCallbacks(odswiezanie)
    }

    // ------------------------------------------------------------------
    //  WIDOKI
    // ------------------------------------------------------------------
    private fun dp(v: Int) = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, v.toFloat(), resources.displayMetrics).toInt()

    private fun przycisk(tekst: String, kolor: Int, rozmiar: Float = 15f, akcja: () -> Unit): Button {
        val b = Button(this)
        b.text = tekst
        b.isAllCaps = false
        b.setTextColor(Color.WHITE)
        b.textSize = rozmiar
        val tlo = GradientDrawable()
        tlo.cornerRadius = dp(10).toFloat()
        tlo.setColor(kolor)
        b.background = tlo
        b.setPadding(dp(10), dp(8), dp(10), dp(8))
        b.setOnClickListener { akcja() }
        return b
    }

    private fun wiersz(): LinearLayout {
        val l = LinearLayout(this)
        l.orientation = LinearLayout.HORIZONTAL
        l.gravity = Gravity.CENTER_VERTICAL
        return l
    }

    private fun lp(waga: Float, lewy: Int = 0): LinearLayout.LayoutParams {
        val p = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, waga)
        p.leftMargin = dp(lewy)
        return p
    }

    private fun lpPelny(gora: Int): LinearLayout.LayoutParams {
        val p = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(64))
        p.topMargin = dp(gora)
        return p
    }

    private fun tekst(t: String, rozmiar: Float, kolor: Int, gruby: Boolean = false): TextView {
        val v = TextView(this)
        v.text = t
        v.textSize = rozmiar
        v.setTextColor(kolor)
        if (gruby) v.setTypeface(null, Typeface.BOLD)
        return v
    }

    private fun zbudujStart() {
        ekranStart = LinearLayout(this)
        ekranStart.orientation = LinearLayout.VERTICAL
        ekranStart.setPadding(dp(18), dp(24), dp(18), dp(18))
        ekranStart.setBackgroundColor(Color.rgb(245, 248, 252))

        ekranStart.addView(tekst("Skaner BHP", 30f, Color.rgb(0, 105, 92), true))
        ekranStart.addView(tekst("Program BHP - odzież i ŚOI, wypadki", 15f, szary))

        tSiec = tekst("", 15f, szary, true)
        tSiec.setPadding(0, dp(16), 0, 0)
        ekranStart.addView(tSiec)
        tKomputerStart = tekst("", 14f, szary)
        tKomputerStart.setPadding(0, dp(4), 0, dp(8))
        ekranStart.addView(tKomputerStart)

        bVpn = przycisk("Włącz GlobalProtect", niebieski, 17f) { otworzGlobalProtect() }
        ekranStart.addView(bVpn, lpPelny(4))

        ekranStart.addView(przycisk("Wydanie", Color.rgb(46, 125, 50), 22f) { pokazWydanie() }, lpPelny(18))
        ekranStart.addView(przycisk("Dostawa", Color.rgb(93, 64, 55), 22f) { pokazMagazyn("DOSTAWA") }, lpPelny(12))
        ekranStart.addView(przycisk("Inwentura", Color.rgb(2, 119, 189), 22f) { pokazMagazyn("INWENTURA") }, lpPelny(12))
        ekranStart.addView(przycisk("Kody producenta", Color.rgb(239, 108, 0), 20f) { pokazMagazyn("KODY") }, lpPelny(12))
        ekranStart.addView(przycisk("Zdjęcia - wypadki", Color.rgb(198, 40, 40), 20f) { pokazZdjecia() }, lpPelny(12))

        val odstep = View(this)
        ekranStart.addView(odstep, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))
        ekranStart.addView(przycisk("Zakończ", czerwony, 20f) { zakoncz() }, lpPelny(12))
    }

    private fun zbudujWydanie() {
        ekranWydanie = LinearLayout(this)
        ekranWydanie.orientation = LinearLayout.VERTICAL
        ekranWydanie.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranWydanie.setBackgroundColor(Color.rgb(245, 248, 252))

        val w1 = wiersz()
        w1.addView(przycisk("← Menu", szary) { pokazStart() })
        val tyt = tekst("  Wydanie", 22f, Color.rgb(46, 125, 50), true)
        w1.addView(tyt, lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranWydanie.addView(w1)

        tKomputer = tekst("", 14f, szary, true)
        tKomputer.setPadding(0, dp(6), 0, dp(6))
        ekranWydanie.addView(tKomputer)

        podgladWyd = PreviewView(this)
        podgladWyd.scaleType = PreviewView.ScaleType.FILL_CENTER
        ekranWydanie.addView(podgladWyd, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        tKod = tekst("Naciśnij SKANUJ i skieruj aparat na kod", 20f, szary, true)
        tKod.gravity = Gravity.CENTER
        tKod.setPadding(0, dp(6), 0, dp(2))
        ekranWydanie.addView(tKod)

        tWynik = tekst("", 15f, szary, true)
        tWynik.gravity = Gravity.CENTER
        tWynik.setPadding(0, 0, 0, dp(4))
        ekranWydanie.addView(tWynik)

        bSkanuj = przycisk("SKANUJ", niebieski, 22f) { ustawSkanuj(!uzbrojony) }
        ekranWydanie.addView(bSkanuj, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(64)))

        val w3 = wiersz()
        w3.setPadding(0, dp(6), 0, 0)
        w3.addView(przycisk("+1 ten sam", Color.rgb(46, 125, 50)) { ponowTenSam() }, lp(1f))
        w3.addView(przycisk("Cofnij", Color.rgb(121, 85, 72)) { cofnij() }, lp(1f, 6))
        bLatarka = przycisk("Latarka", Color.rgb(96, 125, 139)) { przelaczLatarke() }
        w3.addView(bLatarka, lp(1f, 6))
        ekranWydanie.addView(w3)

        val przew = ScrollView(this)
        listaWidok = LinearLayout(this)
        listaWidok.orientation = LinearLayout.VERTICAL
        listaWidok.setPadding(0, dp(6), 0, dp(6))
        przew.addView(listaWidok)
        ekranWydanie.addView(przew, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        val w4 = wiersz()
        eReczny = EditText(this)
        eReczny.hint = "kod ręcznie"
        eReczny.inputType = InputType.TYPE_CLASS_NUMBER
        w4.addView(eReczny, lp(1f))
        w4.addView(przycisk("Wyślij", Color.rgb(106, 27, 154)) { wyslijRecznie() }, lp(0.5f, 6))
        ekranWydanie.addView(w4)
        pokazListe()
    }

    private fun pokazStart() {
        tryb = "MENU"
        zatrzymajKamere()
        setContentView(ekranStart)
        pokazStan()
    }

    private fun pokazWydanie() {
        zatrzymajKamere()
        tryb = "WYDANIE"
        podgladAkt = podgladWyd
        setContentView(ekranWydanie)
        wlaczKamere()
        pokazStan()
    }

    private fun wlaczKamere() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            uruchomKamere()
        } else {
            prosbaKamera.launch(Manifest.permission.CAMERA)
        }
    }

    // ------------------------------------------------------------------
    //  SIEĆ / VPN / KOMPUTER
    // ------------------------------------------------------------------
    private fun vpnWlaczony(): Boolean {
        return try {
            val cm = getSystemService(ConnectivityManager::class.java)
            cm.allNetworks.any { n -> cm.getNetworkCapabilities(n)?.hasTransport(NetworkCapabilities.TRANSPORT_VPN) == true }
        } catch (e: Exception) {
            false
        }
    }

    private fun adresTelefonu(): String {
        var wynik = ""
        try {
            for (ni in NetworkInterface.getNetworkInterfaces()) {
                if (!ni.isUp || ni.isLoopback) continue
                for (a in ni.inetAddresses) {
                    if (a is Inet4Address && !a.isLoopbackAddress) {
                        val ip = a.hostAddress ?: continue
                        if (ni.name.startsWith("tun") || ni.name.startsWith("ppp") || wynik.isEmpty()) wynik = ip
                    }
                }
            }
        } catch (e: Exception) {
        }
        return wynik
    }

    private fun komputerWidziany(): Boolean = ostatniKontakt > 0 && SystemClock.elapsedRealtime() - ostatniKontakt < 5000

    private fun pokazStan() {
        val vpn = vpnWlaczony()
        val ip = adresTelefonu()
        if (vpn) {
            tSiec.text = "✔ GlobalProtect włączony   (telefon: $ip)"
            tSiec.setTextColor(zielony)
            bVpn.visibility = View.GONE
        } else {
            tSiec.text = "GlobalProtect wyłączony - włącz, żeby komputer widział telefon"
            tSiec.setTextColor(czerwony)
            bVpn.visibility = View.VISIBLE
        }
        val k = if (komputerWidziany()) {
            "✔ Komputer połączony ($adresKomputera)"
        } else if (ostatniKontakt > 0) {
            "Komputer nie odpytuje - w Programie BHP otwórz Wydanie"
        } else {
            "Komputer jeszcze się nie połączył - Wydanie -> \"Lista na telefon\""
        }
        val kolor = if (komputerWidziany()) zielony else pomaranczowy
        tKomputerStart.text = k
        tKomputerStart.setTextColor(kolor)
        if (::tKomputer.isInitialized) {
            tKomputer.text = if (vpn) k else "GlobalProtect wyłączony - wróć do Menu i włącz"
            tKomputer.setTextColor(if (vpn) kolor else czerwony)
        }
        if (::tKomputerZdj.isInitialized) {
            tKomputerZdj.text = when {
                !vpn -> "GlobalProtect wyłączony - zdjęcia czekają w telefonie, komputer pobierze je później"
                komputerWidziany() -> "\u2714 Komputer połączony ($adresKomputera)"
                else -> "Komputer pobierze zdjęcia: Oględziny -> \"Z telefonu\""
            }
            tKomputerZdj.setTextColor(if (vpn && komputerWidziany()) zielony else szary)
        }
        if (::tKomputerMag.isInitialized) {
            tKomputerMag.text = when {
                !vpn -> "GlobalProtect wyłączony - wróć do Menu i włącz"
                katalog.isEmpty() -> "Czekam na katalog - w komputerze otwórz Magazyn odzieży"
                komputerWidziany() -> "\u2714 Komputer połączony, katalog: ${katalog.size} poz."
                else -> "Komputer nie odpytuje - w komputerze otwórz Magazyn odzieży"
            }
            tKomputerMag.setTextColor(if (vpn && komputerWidziany() && katalog.isNotEmpty()) zielony else pomaranczowy)
        }
    }

    private fun otworzGlobalProtect() {
        val i = packageManager.getLaunchIntentForPackage("com.paloaltonetworks.globalprotect")
        if (i != null) {
            startActivity(i)
        } else {
            try {
                startActivity(Intent(Intent.ACTION_VIEW, Uri.parse("market://details?id=com.paloaltonetworks.globalprotect")))
            } catch (e: Exception) {
                Toast.makeText(this, "Otwórz GlobalProtect ręcznie", Toast.LENGTH_LONG).show()
            }
        }
    }

    // --- serwer (wątki sieciowe) ---
    override fun ping(): String = "SKANER_BHP|$tryb"

    override fun komputer(adres: String) {
        ostatniKontakt = SystemClock.elapsedRealtime()
        adresKomputera = adres
    }

    override fun lista(tekst: String) {
        synchronized(skany) {
            skany.clear()
            nastepnyNr = 1
            sesja = System.currentTimeMillis() % 1000000
        }
        runOnUiThread {
            if (tryb == "MENU") pokazWydanie()          // w Dostawie / Inwenturze lista tylko się wczytuje
            wczytajListe(tekst)
        }
    }

    override fun skany(od: Int): String {
        synchronized(skany) {
            val linie = skany.filter { it.nr >= od }.joinToString("") { "\n${it.nr}|${it.kod}" }
            return "SESJA|$sesja$linie\nLISTA|" + (if (maListe) "1" else "0") + "\nKATALOG|$katWersja"
        }
    }

    override fun wynik(tekst: String) {
        // "nr|kolor|D|tekst"  (D: 1 = komputer policzył sztukę, 0 = odrzucił)  albo stare "nr|kolor|tekst"
        val p4 = tekst.split("|", limit = 4)
        val nowy = p4.size >= 4 && (p4[2] == "0" || p4[2] == "1")
        val p = if (nowy) listOf(p4[0], p4[1], p4[3]) else tekst.split("|", limit = 3)
        if (p.size < 3) return
        val nrSkanu = p[0].toIntOrNull() ?: -1
        val dodano = if (nowy) p4[2] == "1" else true
        runOnUiThread { potwierdzSztuke(nrSkanu, dodano) }
        val kolor = when (p[1]) {
            "1" -> zielony
            "2" -> czerwony
            "3" -> pomaranczowy
            else -> szary
        }
        runOnUiThread {
            val t = if (naWydaniu || !::tWynikMag.isInitialized) tWynik else tWynikMag
            t.text = "Komputer: " + p[2]
            t.setTextColor(kolor)
            if (p[1] == "2" || p[1] == "3") ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 300)
        }
    }

    override fun koniec(tekst: String) {
        runOnUiThread {
            lista.clear()
            cofanie.clear()
            listaTekst = null
            maListe = false
            pokazListe()
            tKod.text = "Wydano ✔"
            tKod.setTextColor(zielony)
            tWynik.text = if (tekst.isNotBlank()) tekst else "Wydanie zapisane w komputerze"
            tWynik.setTextColor(zielony)
            ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 300)
        }
    }

    // ------------------------------------------------------------------
    //  ZDJĘCIA (wypadki)
    // ------------------------------------------------------------------
    private fun zbudujZdjecia() {
        ekranZdj = LinearLayout(this)
        ekranZdj.orientation = LinearLayout.VERTICAL
        ekranZdj.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranZdj.setBackgroundColor(Color.rgb(245, 248, 252))

        val w1 = wiersz()
        w1.addView(przycisk("← Menu", szary) { pokazStart() })
        w1.addView(tekst("  Zdjęcia - wypadki", 22f, czerwony, true), lp(1f))
        ekranZdj.addView(w1)

        tSprawaZdj = tekst("", 15f, Color.rgb(173, 20, 87), true)
        tSprawaZdj.setPadding(0, dp(6), 0, 0)
        ekranZdj.addView(tSprawaZdj)
        tKomputerZdj = tekst("", 13f, szary)
        tKomputerZdj.setPadding(0, dp(2), 0, dp(6))
        ekranZdj.addView(tKomputerZdj)

        bGaleria = przycisk("Wybierz zdjęcia z galerii", czerwony, 20f) {
            wyborZdjec.launch(PickVisualMediaRequest(ActivityResultContracts.PickVisualMedia.ImageOnly))
        }
        ekranZdj.addView(bGaleria, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(64)))

        tStanZdj = tekst("", 15f, szary, true)
        tStanZdj.gravity = Gravity.CENTER
        tStanZdj.setPadding(0, dp(6), 0, dp(6))
        ekranZdj.addView(tStanZdj)

        val przew = ScrollView(this)
        listaZdj = LinearLayout(this)
        listaZdj.orientation = LinearLayout.VERTICAL
        przew.addView(listaZdj)
        ekranZdj.addView(przew, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        ekranZdj.addView(przycisk("Usuń wszystkie z aplikacji", szary) { usunWszystkieZdjecia() },
            LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(52)))
        pokazListeZdjec()
    }

    private fun pokazZdjecia() {
        zatrzymajKamere()
        tryb = "ZDJECIA"
        setContentView(ekranZdj)
        tSprawaZdj.text = if (sprawaZdj.isNotBlank()) sprawaZdj else "Zdjęcia trafią do sprawy otwartej w komputerze"
        pokazListeZdjec()
        pokazStan()
    }

    private fun plikiZdjec(): List<Pair<Int, File>> {
        val f = folderZdj.listFiles() ?: return emptyList()
        return f.filter { it.name.startsWith("zdj_") && it.name.endsWith(".jpg") }
            .mapNotNull { pl -> pl.name.removePrefix("zdj_").removeSuffix(".jpg").toIntOrNull()?.let { Pair(it, pl) } }
            .sortedBy { it.first }
    }

    private fun opisZdjecia(nr: Int): String {
        val t = File(folderZdj, "zdj_$nr.txt")
        return if (t.exists()) t.readText(Charsets.UTF_8) else ""
    }

    private fun pokazLicznikZdjec() {
        if (!::tStanZdj.isInitialized) return
        val n = plikiZdjec().size
        tStanZdj.text = if (n == 0) "Brak zdjęć - wybierz je z galerii" else "Wybrane: $n zdj. - czekają na komputer (dotknij zdjęcia = podgląd)"
        tStanZdj.setTextColor(if (n == 0) szary else pomaranczowy)
    }

    // obraz z galerii / pliku: najdłuższy bok do max px, obrót wg EXIF
    private fun wczytajObraz(otworz: () -> java.io.InputStream?, max: Int): Bitmap? {
        val o = BitmapFactory.Options()
        o.inJustDecodeBounds = true
        otworz()?.use { BitmapFactory.decodeStream(it, null, o) }
        if (o.outWidth <= 0 || o.outHeight <= 0) return null
        var sk = 1
        while (maxOf(o.outWidth, o.outHeight) / (sk * 2) >= max) sk *= 2
        val o2 = BitmapFactory.Options()
        o2.inSampleSize = sk
        var bmp = otworz()?.use { BitmapFactory.decodeStream(it, null, o2) } ?: return null
        val dl = maxOf(bmp.width, bmp.height)
        if (dl > max) {
            val k = max.toFloat() / dl
            bmp = Bitmap.createScaledBitmap(bmp, (bmp.width * k).toInt(), (bmp.height * k).toInt(), true)
        }
        val orient = try {
            otworz()?.use { ExifInterface(it).getAttributeInt(ExifInterface.TAG_ORIENTATION, ExifInterface.ORIENTATION_NORMAL) }
                ?: ExifInterface.ORIENTATION_NORMAL
        } catch (e: Exception) {
            ExifInterface.ORIENTATION_NORMAL
        }
        val obrot = when (orient) {
            ExifInterface.ORIENTATION_ROTATE_90 -> 90f
            ExifInterface.ORIENTATION_ROTATE_180 -> 180f
            ExifInterface.ORIENTATION_ROTATE_270 -> 270f
            else -> 0f
        }
        if (obrot != 0f) {
            val m = Matrix()
            m.postRotate(obrot)
            bmp = Bitmap.createBitmap(bmp, 0, 0, bmp.width, bmp.height, m, true)
        }
        return bmp
    }

    private fun importujZdjecia(uris: List<Uri>) {
        bGaleria.isEnabled = false
        tStanZdj.text = "Kopiuję zdjęcia (${uris.size}) ..."
        tStanZdj.setTextColor(niebieski)
        watekKamery.execute {
            var ok = 0
            for (u in uris) {
                try {
                    val bmp = wczytajObraz({ contentResolver.openInputStream(u) }, 1600) ?: continue
                    val nr = (plikiZdjec().maxOfOrNull { it.first } ?: 0) + 1
                    FileOutputStream(File(folderZdj, "zdj_$nr.jpg")).use { bmp.compress(Bitmap.CompressFormat.JPEG, 85, it) }
                    ok++
                } catch (e: Exception) {
                }
            }
            runOnUiThread {
                bGaleria.isEnabled = true
                pokazListeZdjec()
                if (ok < uris.size) Toast.makeText(this, "Nie udało się skopiować: ${uris.size - ok}", Toast.LENGTH_LONG).show()
            }
        }
    }

    private fun pokazListeZdjec() {
        if (!::listaZdj.isInitialized) return
        listaZdj.removeAllViews()
        for ((nr, plik) in plikiZdjec()) {
            val w = wiersz()
            w.setPadding(0, dp(6), 0, dp(6))
            val iv = ImageView(this)
            iv.scaleType = ImageView.ScaleType.CENTER_CROP
            try {
                iv.setImageBitmap(wczytajObraz({ plik.inputStream() }, 300))
            } catch (e: Exception) {
            }
            iv.setOnClickListener { podgladZdjecia(plik) }
            w.addView(iv, LinearLayout.LayoutParams(dp(110), dp(110)))

            val kol = LinearLayout(this)
            kol.orientation = LinearLayout.VERTICAL
            kol.setPadding(dp(8), 0, 0, 0)
            val opis = EditText(this)
            opis.hint = "Opis zdjęcia (co widać)"
            opis.setText(opisZdjecia(nr))
            opis.textSize = 15f
            opis.minLines = 2
            opis.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_SENTENCES or InputType.TYPE_TEXT_FLAG_MULTI_LINE
            opis.addTextChangedListener(object : TextWatcher {
                override fun beforeTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
                override fun onTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
                override fun afterTextChanged(e: Editable?) {
                    try {
                        File(folderZdj, "zdj_$nr.txt").writeText(e?.toString()?.trim() ?: "", Charsets.UTF_8)
                    } catch (x: Exception) {
                    }
                }
            })
            kol.addView(opis, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT))
            val wb = wiersz()
            wb.addView(przycisk("Podgląd", niebieski, 13f) { podgladZdjecia(plik) }, lp(1f))
            wb.addView(przycisk("Usuń", Color.rgb(121, 85, 72), 13f) {
                AlertDialog.Builder(this)
                    .setTitle("Usunąć to zdjęcie z aplikacji?")
                    .setMessage("Zdjęcie w galerii telefonu zostaje.")
                    .setPositiveButton("Usuń") { _, _ -> usunZdjecie(nr); pokazListeZdjec() }
                    .setNegativeButton("Nie", null)
                    .show()
            }, lp(1f, 6))
            kol.addView(wb)
            w.addView(kol, lp(1f))
            listaZdj.addView(w)
        }
        pokazLicznikZdjec()
    }

    private fun podgladZdjecia(plik: File) {
        val iv = ImageView(this)
        iv.adjustViewBounds = true
        iv.scaleType = ImageView.ScaleType.FIT_CENTER
        iv.setBackgroundColor(Color.BLACK)
        try {
            iv.setImageBitmap(BitmapFactory.decodeFile(plik.absolutePath))
        } catch (e: Exception) {
        }
        val d = AlertDialog.Builder(this).setView(iv).setPositiveButton("Zamknij", null).create()
        iv.setOnClickListener { d.dismiss() }
        d.show()
    }

    private fun usunZdjecie(nr: Int) {
        File(folderZdj, "zdj_$nr.jpg").delete()
        File(folderZdj, "zdj_$nr.txt").delete()
    }

    private fun usunWszystkieZdjecia() {
        val n = plikiZdjec().size
        if (n == 0) return
        AlertDialog.Builder(this)
            .setTitle("Usunąć wszystkie zdjęcia z aplikacji ($n)?")
            .setMessage("Komputer ich już nie pobierze. Zdjęcia w galerii telefonu zostają.")
            .setPositiveButton("Usuń") { _, _ -> plikiZdjec().forEach { usunZdjecie(it.first) }; pokazListeZdjec() }
            .setNegativeButton("Nie", null)
            .show()
    }

    // polskie litery -> ~a ~c ... (jak komputer), | i nowa linia -> spacja
    private fun naKomputer(s: String): String {
        val z = "acelnosxzACELNOSXZ"
        val na = "ąćęłńóśźżĄĆĘŁŃÓŚŹŻ"
        val b = StringBuilder()
        for (c in s) {
            val k = na.indexOf(c)
            when {
                k >= 0 -> b.append('~').append(z[k])
                c == '|' || c == '\n' || c == '\r' -> b.append(' ')
                else -> b.append(c)
            }
        }
        return b.toString()
    }

    override fun zdjecia(): String {
        val l = plikiZdjec()
        return "ZDJ|" + l.size + l.joinToString("") { "\n${it.first}|" + naKomputer(opisZdjecia(it.first)) }
    }

    override fun zdjecie(nr: Int): ByteArray? {
        val f = File(folderZdj, "zdj_$nr.jpg")
        return if (f.exists()) f.readBytes() else null
    }

    override fun odebrane(tekst: String) {
        for (t in tekst.split(",")) {
            val nr = t.trim().toIntOrNull() ?: continue
            usunZdjecie(nr)
        }
        runOnUiThread {
            pokazListeZdjec()
            if (tryb == "ZDJECIA") {
                tStanZdj.text = "\u2714 Komputer pobrał zdjęcia - " + tStanZdj.text
                ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 300)
            }
        }
    }

    // POST /sms: "numer\ntreść" (polskie litery jako ~a ...).  Numer 9 cyfr -> +48.
    override fun sms(tekst: String): String {
        val linie = tekst.replace("\r", "").split("\n", limit = 2)
        if (linie.size < 2) return "BLAD|brak numeru albo treści"
        var numer = linie[0].filter { it.isDigit() || it == '+' }
        if (numer.length == 9 && !numer.startsWith("+")) numer = "+48$numer"
        if (numer.length < 9) return "BLAD|zły numer: ${linie[0]}"
        val tresc = polskie(linie[1].trim())
        if (tresc.isEmpty()) return "BLAD|pusta treść"
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.SEND_SMS) != PackageManager.PERMISSION_GRANTED) {
            runOnUiThread { prosbaSms.launch(Manifest.permission.SEND_SMS) }
            return "BRAK_UPRAWNIEN"
        }
        return try {
            @Suppress("DEPRECATION")
            val sm: SmsManager = if (Build.VERSION.SDK_INT >= 31) getSystemService(SmsManager::class.java) else SmsManager.getDefault()
            val czesci = sm.divideMessage(tresc)
            if (czesci.size > 1) sm.sendMultipartTextMessage(numer, null, czesci, null, null)
            else sm.sendTextMessage(numer, null, tresc, null, null)
            val koncowka = numer.takeLast(3)
            runOnUiThread { Toast.makeText(this, "Wysłano SMS z komputera na numer ...$koncowka", Toast.LENGTH_LONG).show() }
            "OK"
        } catch (e: Exception) {
            "BLAD|" + (e.message ?: "nie udało się wysłać SMS")
        }
    }

    override fun zdjeciaSprawa(tekst: String) {
        sprawaZdj = polskie(tekst.trim())
        runOnUiThread {
            if (::tSprawaZdj.isInitialized && sprawaZdj.isNotBlank()) tSprawaZdj.text = sprawaZdj
        }
    }

    // ------------------------------------------------------------------
    //  APARAT
    // ------------------------------------------------------------------
    private fun uruchomKamere() {
        if (skaner == null) {
            val opcje = BarcodeScannerOptions.Builder()
                .setBarcodeFormats(
                    Barcode.FORMAT_EAN_8, Barcode.FORMAT_EAN_13, Barcode.FORMAT_UPC_A,
                    Barcode.FORMAT_UPC_E, Barcode.FORMAT_CODE_128, Barcode.FORMAT_CODE_39,
                    Barcode.FORMAT_QR_CODE
                )
                .build()
            skaner = BarcodeScanning.getClient(opcje)
        }
        val przyszly = ProcessCameraProvider.getInstance(this)
        przyszly.addListener({
            try {
                val dostawca = przyszly.get()
                dostawcaKamery = dostawca
                if (tryb == "MENU") return@addListener
                val preview = Preview.Builder().build()
                preview.setSurfaceProvider((podgladAkt ?: podgladWyd).surfaceProvider)
                val analiza = ImageAnalysis.Builder()
                    .setBackpressureStrategy(ImageAnalysis.STRATEGY_KEEP_ONLY_LATEST)
                    .build()
                analiza.setAnalyzer(watekKamery) { proxy -> analizuj(proxy) }
                dostawca.unbindAll()
                kamera = dostawca.bindToLifecycle(this, CameraSelector.DEFAULT_BACK_CAMERA, preview, analiza)
            } catch (e: Exception) {
                tKod.text = "Błąd aparatu: ${e.message}"
                tKod.setTextColor(czerwony)
            }
        }, ContextCompat.getMainExecutor(this))
    }

    private fun zatrzymajKamere() {
        try {
            dostawcaKamery?.unbindAll()
        } catch (e: Exception) {
        }
        kamera = null
        latarka = false
        if (::bLatarka.isInitialized) bLatarka.text = "Latarka"
    }

    @androidx.annotation.OptIn(ExperimentalGetImage::class)
    private fun analizuj(proxy: ImageProxy) {
        val obrazKamery = proxy.image
        val s = skaner
        if (obrazKamery == null || s == null) {
            proxy.close()
            return
        }
        val obraz = InputImage.fromMediaImage(obrazKamery, proxy.imageInfo.rotationDegrees)
        s.process(obraz)
            .addOnSuccessListener { kody -> obsluzKody(kody) }
            .addOnCompleteListener { proxy.close() }
    }

    private fun obsluzKody(kody: List<Barcode>) {
        if (tryb == "MENU") return
        if (!naWydaniu) {
            if (oknoOtwarte) return
            val teraz = SystemClock.elapsedRealtime()
            val kod = kody.firstOrNull { it.format != Barcode.FORMAT_QR_CODE && !it.rawValue.isNullOrEmpty() }?.rawValue
            if (kod == null) {
                if (teraz - ostatnioWidziany > 700) kodWKadrze = null
                return
            }
            ostatnioWidziany = teraz
            if (kod == kodWKadrze) return
            if (teraz - ostatnioWyslany < 800) return
            kodWKadrze = kod
            ostatnioWyslany = teraz
            kodMagazynu(kod)
            return
        }
        // QR z listą (zapasowo, gdy nie ma sieci)
        val qr = kody.firstOrNull { it.format == Barcode.FORMAT_QR_CODE && (it.rawValue ?: "").startsWith("BHP1") }
        if (qr != null) {
            val t = qr.rawValue ?: return
            if (t != listaTekst) wczytajListe(t)
            return
        }
        if (!uzbrojony) return                       // bez SKANUJ aparat tylko pokazuje obraz
        val kod = kody.firstOrNull { it.format != Barcode.FORMAT_QR_CODE && !it.rawValue.isNullOrEmpty() }?.rawValue ?: return
        ustawSkanuj(false)                            // jeden kod na jedno naciśnięcie
        kodWKadrze = kod
        ostatnioWidziany = SystemClock.elapsedRealtime()
        wyslij(kod)
    }

    private fun ustawSkanuj(tak: Boolean) {
        uzbrojony = tak
        handler.removeCallbacks(rozbroj)
        if (!::bSkanuj.isInitialized) return
        val tlo = GradientDrawable()
        tlo.cornerRadius = dp(10).toFloat()
        tlo.setColor(if (tak) pomaranczowy else niebieski)
        bSkanuj.background = tlo
        bSkanuj.text = if (tak) "SKANUJĘ... (dotknij = stop)" else "SKANUJ"
        if (tak) handler.postDelayed(rozbroj, 6000)
    }

    private fun wyslij(kod: String) {
        ostatnioWyslany = SystemClock.elapsedRealtime()
        val polecenie = kod.startsWith("-")           // "-" cofnij ostatni, "-<kod>" cofnij tę sztukę
        if (!polecenie) ostatniWyslanyKod = kod
        val nr: Int
        synchronized(skany) {
            nr = nastepnyNr
            skany.add(Skan(nastepnyNr, kod))
            nastepnyNr++
            while (skany.size > 500) skany.removeAt(0)
        }
        if (polecenie) return
        tKod.text = kod
        tKod.setTextColor(niebieski)
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
        (podgladAkt ?: podgladWyd).performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
        if (!komputerWidziany()) {
            tWynik.text = "Komputer nie odbiera - kod czeka. Otwórz Wydanie i kliknij \"Lista na telefon\"."
            tWynik.setTextColor(czerwony)
        }
        sprawdzNaLiscie(kod, nr)
    }

    private fun ponowTenSam() {
        val k = ostatniWyslanyKod
        if (k == null) {
            Toast.makeText(this, "Najpierw zeskanuj kod", Toast.LENGTH_SHORT).show()
            return
        }
        wyslij(k)
    }

    private fun wyslijRecznie() {
        val k = eReczny.text.toString().trim()
        if (k.isEmpty()) return
        wyslij(k)
        eReczny.setText("")
    }

    private fun cofnij() {
        wyslij("-")
        val nr = cofanie.removeLastOrNull()
        if (nr != null) usunSztuke(nr)
        tWynik.text = "Cofnięto ostatni skan (też w komputerze)"
        tWynik.setTextColor(szary)
        pokazListe()
    }

    // sztuka o numerze skanu - usunięcie z listy
    private fun usunSztuke(nr: Int): Boolean {
        for (p in lista) {
            val i = p.skany.indexOfFirst { it.nr == nr }
            if (i >= 0) {
                p.skany.removeAt(i)
                p.uwaga = przelicUwage(p)
                return true
            }
        }
        return false
    }

    private fun przelicUwage(p: Pozycja): Boolean {
        val inny = p.skany.any { s ->
            p.rozmiar.isNotBlank() && p.rozmiar != "-" && s.wpis.rozmiar != "-" && !s.wpis.rozmiar.equals(p.rozmiar, ignoreCase = true)
        }
        return inny || p.skany.size > p.ilosc
    }

    // wynik z komputera: odrzucona sztuka znika z listy telefonu (lista = to, co w komputerze)
    private fun potwierdzSztuke(nr: Int, dodano: Boolean) {
        if (nr < 0) return
        if (dodano) {
            for (p in lista) p.skany.firstOrNull { it.nr == nr }?.ok = true
        } else if (usunSztuke(nr)) {
            cofanie.remove(nr)
        }
        pokazListe()
    }

    // dotknięcie pozycji na liście - wybór sztuki do cofnięcia
    private fun cofnijWybrana(p: Pozycja) {
        if (p.skany.isEmpty()) {
            Toast.makeText(this, "Ta pozycja nie ma zeskanowanych sztuk", Toast.LENGTH_SHORT).show()
            return
        }
        val opisy = p.skany.map { s ->
            (if (p.warianty.size > 1 && s.wpis.wariant < p.warianty.size) p.warianty[s.wpis.wariant] + " " else "") +
                    (if (s.wpis.rozmiar == "-") "bez rozmiaru" else "rozm. " + s.wpis.rozmiar) + "   (kod " + s.kod + ")"
        }.toTypedArray()
        AlertDialog.Builder(this)
            .setTitle("Cofnij sztukę: " + p.nazwa)
            .setItems(opisy) { _, i ->
                val s = p.skany.getOrNull(i) ?: return@setItems
                wyslij("-" + s.kod)
                p.skany.removeAt(i)
                cofanie.remove(s.nr)
                p.uwaga = przelicUwage(p)
                tWynik.text = "Cofnięto: " + opisy[i] + " (też w komputerze)"
                tWynik.setTextColor(szary)
                pokazListe()
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    private fun przelaczLatarke() {
        val k = kamera ?: return
        latarka = !latarka
        k.cameraControl.enableTorch(latarka)
        bLatarka.text = if (latarka) "Latarka: wł." else "Latarka"
    }

    // ------------------------------------------------------------------
    //  LISTA DO WYDANIA
    //  BHP1 \n nazwa|ilosc|rozmiar|wariant0,wariant1|r195=35.0;w12=-.0;e5902...=42.1
    // ------------------------------------------------------------------
    private fun polskie(s: String): String {
        val z = "acelnosxzACELNOSXZ"
        val na = "ąćęłńóśźżĄĆĘŁŃÓŚŹŻ"
        val b = StringBuilder()
        var i = 0
        while (i < s.length) {
            val c = s[i]
            if (c == '~' && i + 1 < s.length) {
                val k = z.indexOf(s[i + 1])
                if (k >= 0) {
                    b.append(na[k])
                    i += 2
                    continue
                }
            }
            b.append(c)
            i++
        }
        return b.toString()
    }

    private fun wczytajListe(tekst: String) {
        val nowa = mutableListOf<Pozycja>()
        try {
            for (l in tekst.split("\n").drop(1)) {
                if (l.isBlank()) continue
                val p = l.trimEnd('\r').split("|")
                if (p.size < 5) continue
                val warianty = p[3].split(",").map { polskie(it.trim()) }
                val wpisy = HashMap<String, Wpis>()
                for (w in p[4].split(";")) {
                    val r = w.indexOf('=')
                    val kropka = w.lastIndexOf('.')
                    if (r <= 0 || kropka < r) continue
                    wpisy[w.substring(0, r)] = Wpis(polskie(w.substring(r + 1, kropka)), w.substring(kropka + 1).toIntOrNull() ?: 0)
                }
                nowa.add(Pozycja(polskie(p[0]), p[1].toIntOrNull() ?: 1, polskie(p[2]), warianty, wpisy))
            }
        } catch (e: Exception) {
            tWynik.text = "Nie udało się odczytać listy: ${e.message}"
            tWynik.setTextColor(czerwony)
            return
        }
        lista.clear()
        lista.addAll(nowa)
        cofanie.clear()
        listaTekst = tekst
        maListe = true
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 250)
        tKod.text = "Lista: ${lista.size} poz."
        tKod.setTextColor(niebieski)
        tWynik.text = "Idź do magazynu i skanuj kartony"
        tWynik.setTextColor(szary)
        pokazListe()
    }

    private fun klucze(kod: String): List<String> {
        val cyfry = kod.isNotEmpty() && kod.all { it.isDigit() }
        if (cyfry && kod.length == 8 && (kod.startsWith("21") || kod.startsWith("22"))) {
            val id = kod.substring(2, 7).toInt()
            return listOf((if (kod.startsWith("21")) "r" else "w") + id)
        }
        val k = if (cyfry && kod.length == 12) "0$kod" else kod
        val l = mutableListOf("e$k")
        if (k.length == 13 && k.startsWith("0")) l.add("e" + k.substring(1))
        return l
    }

    private fun sprawdzNaLiscie(kod: String, nrSkanu: Int) {
        if (lista.isEmpty()) return
        val kl = klucze(kod)
        var nr = -1
        var wpis: Wpis? = null
        for ((i, p) in lista.withIndex()) {
            for (k in kl) {
                val w = p.wpisy[k]
                if (w != null) {
                    nr = i
                    wpis = w
                    break
                }
            }
            if (wpis != null) break
        }
        if (wpis == null || nr < 0) {
            if (komputerWidziany()) {
                tWynik.text = "Nie z listy (inny rozmiar?) - czekam na komputer"
                tWynik.setTextColor(pomaranczowy)
            }
            return
        }
        val p = lista[nr]
        p.skany.add(Sztuka(wpis, nrSkanu, kod))
        cofanie.addLast(nrSkanu)
        p.uwaga = przelicUwage(p)
        pokazListe()
    }

    private fun pokazListe() {
        listaWidok.removeAllViews()
        if (lista.isEmpty()) {
            listaWidok.addView(tekst("Lista do wydania: w Programie BHP (Wydanie) wybierz pracownika i kliknij \"Lista na telefon\".", 14f, szary))
            return
        }
        var gotowe = 0
        for (p in lista) {
            val komplet = p.skany.size >= p.ilosc
            if (komplet) gotowe++
            val znak = if (komplet) "✔" else "☐"
            val roz = when {
                p.rozmiar == "-" -> ""
                p.rozmiar.isNotBlank() -> "rozm. ${p.rozmiar}"
                else -> "rozm. ?"
            }
            val sb = StringBuilder("$znak ${p.nazwa}  $roz   ${p.skany.size}/${p.ilosc}")
            if (p.skany.isNotEmpty()) {
                sb.append("\n      ")
                sb.append(p.skany.joinToString(", ") { s ->
                    (if (p.warianty.size > 1 && s.wpis.wariant < p.warianty.size) p.warianty[s.wpis.wariant] + " " else "") +
                            s.wpis.rozmiar + (if (s.ok) "" else " ?")
                })
            }
            val t = tekst(sb.toString(), 16f,
                when {
                    p.uwaga -> pomaranczowy
                    komplet -> zielony
                    else -> Color.rgb(38, 50, 56)
                }, komplet)
            t.setPadding(dp(4), dp(5), dp(4), dp(5))
            t.setOnClickListener { cofnijWybrana(p) }
            listaWidok.addView(t)
        }
        val s = tekst("Gotowe: $gotowe z ${lista.size}", 14f, if (gotowe == lista.size) zielony else szary, true)
        s.setPadding(dp(4), dp(6), dp(4), 0)
        listaWidok.addView(s)
        val h = tekst("Dotknij pozycji, żeby cofnąć wybraną sztukę.  \"?\" = komputer jeszcze nie potwierdził.", 12f, szary)
        h.setPadding(dp(4), dp(2), dp(4), 0)
        listaWidok.addView(h)
    }

    // ------------------------------------------------------------------
    //  KATALOG (z komputera):  KAT1|wersja  /  war|rozm|asortyment|wariant|rozmiar|stan|kod1,kod2
    // ------------------------------------------------------------------
    override fun katalog(tekst: String) {
        val nowy = mutableListOf<Kat>()
        var wersja = "0"
        try {
            val linie = tekst.split("\n")
            if (linie.isEmpty() || !linie[0].startsWith("KAT1")) return
            wersja = linie[0].substringAfter("|", "0").trim()
            for (l in linie.drop(1)) {
                val p = l.trimEnd('\r').split("|")
                if (p.size < 7) continue
                val kody = p[6].split(",").map { it.trim() }.filter { it.isNotEmpty() }.toMutableList()
                nowy.add(Kat(p[0].toIntOrNull() ?: continue, p[1].toIntOrNull() ?: 0, polskie(p[2]), polskie(p[3]),
                    polskie(p[4]), p[5].toIntOrNull() ?: 0, kody))
            }
        } catch (e: Exception) {
            return
        }
        runOnUiThread {
            katalog = nowy
            katWersja = wersja
            val w = wybrana
            if (w != null) {
                val nowa = katalog.firstOrNull { it.w == w.w && it.r == w.r }
                if (nowa != null) {
                    wybrana = nowa
                    pokazWybrana()
                }
            }
            pokazStan()
        }
    }

    private fun znajdzWKatalogu(kod: String): Kat? {
        val cyfry = kod.isNotEmpty() && kod.all { it.isDigit() }
        if (cyfry && kod.length == 8 && (kod.startsWith("21") || kod.startsWith("22"))) {
            val id = kod.substring(2, 7).toIntOrNull() ?: return null
            return if (kod.startsWith("21")) katalog.firstOrNull { it.r == id } else katalog.firstOrNull { it.w == id && it.r == 0 }
        }
        val k13 = if (cyfry && kod.length == 12) "0$kod" else kod
        val k12 = if (k13.length == 13 && k13.startsWith("0")) k13.substring(1) else k13
        return katalog.firstOrNull { p -> p.kody.any { it == k13 || it == k12 || it == kod } }
    }

    private fun opisKat(k: Kat): String = if (k.rozm == "-" || k.rozm.isBlank()) k.wariant else "${k.wariant}\nrozm. ${k.rozm}"

    // ------------------------------------------------------------------
    //  EKRAN MAGAZYNU: Dostawa / Inwentura / Kody
    // ------------------------------------------------------------------
    private fun zbudujMagazyn() {
        ekranMag = LinearLayout(this)
        ekranMag.orientation = LinearLayout.VERTICAL
        ekranMag.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranMag.setBackgroundColor(Color.rgb(245, 248, 252))

        val w1 = wiersz()
        w1.addView(przycisk("\u2190 Menu", szary) { pokazStart() })
        tTytulMag = tekst("  Dostawa", 22f, Color.rgb(93, 64, 55), true)
        w1.addView(tTytulMag, lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranMag.addView(w1)

        tKomputerMag = tekst("", 14f, szary, true)
        tKomputerMag.setPadding(0, dp(6), 0, dp(6))
        ekranMag.addView(tKomputerMag)

        podgladMag = PreviewView(this)
        podgladMag.scaleType = PreviewView.ScaleType.FILL_CENTER
        ekranMag.addView(podgladMag, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 0.8f))

        tPozycja = tekst("Zeskanuj kod kartonu / opakowania", 20f, szary, true)
        tPozycja.gravity = Gravity.CENTER
        tPozycja.setPadding(0, dp(8), 0, 0)
        ekranMag.addView(tPozycja)
        tStanProg = tekst("", 15f, szary)
        tStanProg.gravity = Gravity.CENTER
        ekranMag.addView(tStanProg)

        wIlosc = wiersz()
        wIlosc.setPadding(0, dp(6), 0, dp(6))
        wIlosc.addView(przycisk("\u2212", Color.rgb(96, 125, 139), 24f) { zmienIlosc(-1) }, lp(0.6f))
        eIlosc = EditText(this)
        eIlosc.inputType = InputType.TYPE_CLASS_NUMBER
        eIlosc.textSize = 24f
        eIlosc.gravity = Gravity.CENTER
        eIlosc.hint = "ilość"
        wIlosc.addView(eIlosc, lp(1f, 6))
        wIlosc.addView(przycisk("+", Color.rgb(96, 125, 139), 24f) { zmienIlosc(1) }, lp(0.6f, 6))
        bAkcja = przycisk("Dodaj do dostawy", Color.rgb(46, 125, 50), 17f) { akcjaMagazynu() }
        wIlosc.addView(bAkcja, lp(1.6f, 8))
        ekranMag.addView(wIlosc)

        val w3 = wiersz()
        w3.addView(przycisk("Wybierz z listy (bez kodu)", Color.rgb(106, 27, 154)) { wybierzZListy(null) }, lp(1f))
        val bLat = przycisk("Latarka", Color.rgb(96, 125, 139)) { przelaczLatarke() }
        w3.addView(bLat, lp(0.5f, 6))
        ekranMag.addView(w3)

        tWynikMag = tekst("", 15f, szary, true)
        tWynikMag.gravity = Gravity.CENTER
        tWynikMag.setPadding(0, dp(6), 0, dp(4))
        ekranMag.addView(tWynikMag)

        val przew = ScrollView(this)
        historiaMag = LinearLayout(this)
        historiaMag.orientation = LinearLayout.VERTICAL
        przew.addView(historiaMag)
        ekranMag.addView(przew, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 0.7f))
    }

    private fun pokazMagazyn(t: String) {
        zatrzymajKamere()
        tryb = t
        podgladAkt = podgladMag
        wybrana = null
        when (t) {
            "DOSTAWA" -> {
                tTytulMag.text = "  Dostawa"
                tTytulMag.setTextColor(Color.rgb(93, 64, 55))
                bAkcja.text = "Dodaj do dostawy"
            }
            "INWENTURA" -> {
                tTytulMag.text = "  Inwentura"
                tTytulMag.setTextColor(Color.rgb(2, 119, 189))
                bAkcja.text = "Zapisz stan"
            }
            else -> {
                tTytulMag.text = "  Kody producenta"
                tTytulMag.setTextColor(Color.rgb(239, 108, 0))
            }
        }
        wIlosc.visibility = if (t == "KODY") View.GONE else View.VISIBLE
        historiaMag.removeAllViews()
        tWynikMag.text = when (t) {
            "DOSTAWA" -> "Skanuj kartony z dostawy - pozycje dopiszą się w komputerze (Magazyn -> Dostawa)"
            "INWENTURA" -> "Skanuj karton, policz i wpisz ilość - stan zapisze się w komputerze"
            else -> "Skanuj kody z opakowań - nieznany kod przypiszesz z listy"
        }
        tWynikMag.setTextColor(szary)
        pokazWybrana()
        setContentView(ekranMag)
        wlaczKamere()
        pokazStan()
    }

    private fun pokazWybrana() {
        val k = wybrana
        if (k == null) {
            tPozycja.text = "Zeskanuj kod kartonu / opakowania"
            tPozycja.setTextColor(szary)
            tStanProg.text = ""
            eIlosc.setText("")
            bAkcja.isEnabled = false
            return
        }
        tPozycja.text = opisKat(k)
        tPozycja.setTextColor(Color.rgb(38, 50, 56))
        tStanProg.text = "w programie: ${k.stan} szt." + if (k.kody.isNotEmpty()) "   (kod producenta: ${k.kody.size})" else ""
        bAkcja.isEnabled = true
    }

    private fun zmienIlosc(o: Int) {
        val n = (eIlosc.text.toString().toIntOrNull() ?: 0) + o
        eIlosc.setText((if (n < 0) 0 else n).toString())
    }

    private fun kodMagazynu(kod: String) {
        if (katalog.isEmpty()) {
            tWynikMag.text = "Nie ma jeszcze katalogu - w komputerze otwórz Magazyn odzieży"
            tWynikMag.setTextColor(czerwony)
            ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 300)
            return
        }
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
        podgladMag.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
        val k = znajdzWKatalogu(kod)
        if (k == null) {
            tWynikMag.text = "Nieznany kod $kod - wybierz, co to jest"
            tWynikMag.setTextColor(pomaranczowy)
            wybierzZListy(kod)
            return
        }
        ustawWybrana(k, "Kod $kod")
    }

    private fun ustawWybrana(k: Kat, skad: String) {
        wybrana = k
        pokazWybrana()
        when (tryb) {
            "DOSTAWA" -> eIlosc.setText("1")
            "INWENTURA" -> eIlosc.setText("")
        }
        if (tryb == "KODY") {
            tWynikMag.text = "$skad = ${opisKat(k).replace("\n", ", ")}"
            tWynikMag.setTextColor(zielony)
        } else {
            tWynikMag.text = if (tryb == "INWENTURA") "Policz i wpisz ilość, potem \"Zapisz stan\"" else "Popraw ilość, potem \"Dodaj do dostawy\""
            tWynikMag.setTextColor(szary)
            eIlosc.requestFocus()
            eIlosc.selectAll()
        }
    }

    private fun akcjaMagazynu() {
        val k = wybrana ?: return
        val il = eIlosc.text.toString().toIntOrNull()
        if (il == null || (tryb == "DOSTAWA" && il <= 0) || il < 0) {
            tWynikMag.text = "Wpisz ilość"
            tWynikMag.setTextColor(czerwony)
            return
        }
        val polecenie = if (tryb == "DOSTAWA") "@DOST" else "@INW"
        wyslijPolecenie("$polecenie|${k.w}|${k.r}|$il")
        val opis = opisKat(k).replace("\n", ", ")
        dodajHistorieMag(if (tryb == "DOSTAWA") "+$il  $opis" else "stan $il  $opis  (było ${k.stan})")
        if (tryb == "INWENTURA") k.stan = il
        tWynikMag.text = if (komputerWidziany()) "Wysłano - czekam na komputer ..." else "Komputer nie odbiera - wyśle się, gdy otworzysz Magazyn odzieży"
        tWynikMag.setTextColor(if (komputerWidziany()) szary else czerwony)
        wybrana = null
        pokazWybrana()
    }

    private fun wyslijPolecenie(tekst: String) {
        synchronized(skany) {
            skany.add(Skan(nastepnyNr, tekst))
            nastepnyNr++
            while (skany.size > 500) skany.removeAt(0)
        }
    }

    private fun dodajHistorieMag(s: String) {
        val t = tekst(s, 15f, Color.rgb(38, 50, 56))
        t.setPadding(dp(4), dp(4), dp(4), dp(4))
        historiaMag.addView(t, 0)
        while (historiaMag.childCount > 30) historiaMag.removeViewAt(historiaMag.childCount - 1)
    }

    /** wybór pozycji z katalogu: asortyment -> wariant -> rozmiar;  kod != null = przypisanie kodu */
    private fun wybierzZListy(kod: String?) {
        if (katalog.isEmpty()) {
            tWynikMag.text = "Nie ma jeszcze katalogu - w komputerze otwórz Magazyn odzieży"
            tWynikMag.setTextColor(czerwony)
            return
        }
        val uklad = LinearLayout(this)
        uklad.orientation = LinearLayout.VERTICAL
        uklad.setPadding(dp(16), dp(8), dp(16), dp(8))
        val spA = Spinner(this)
        val spW = Spinner(this)
        val spR = Spinner(this)
        uklad.addView(tekst("Asortyment", 13f, szary))
        uklad.addView(spA)
        uklad.addView(tekst("Wariant", 13f, szary))
        uklad.addView(spW)
        uklad.addView(tekst("Rozmiar", 13f, szary))
        uklad.addView(spR)

        val asorty = katalog.map { it.asort }.distinct()
        var warianty: List<String> = emptyList()
        var pozycje: List<Kat> = emptyList()
        spA.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, asorty)
        fun ustawRozmiary() {
            val wn = warianty.getOrNull(spW.selectedItemPosition)
            pozycje = katalog.filter { it.asort == asorty.getOrNull(spA.selectedItemPosition) && it.wariant == wn }
            spR.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item,
                pozycje.map { (if (it.rozm == "-") "bez rozmiaru" else it.rozm) + "   (stan ${it.stan})" })
        }
        fun ustawWarianty() {
            val a = asorty.getOrNull(spA.selectedItemPosition)
            warianty = katalog.filter { it.asort == a }.map { it.wariant }.distinct()
            spW.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, warianty)
            ustawRozmiary()
        }
        spA.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(parent: AdapterView<*>?, view: View?, position: Int, id: Long) = ustawWarianty()
            override fun onNothingSelected(parent: AdapterView<*>?) {}
        }
        spW.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(parent: AdapterView<*>?, view: View?, position: Int, id: Long) = ustawRozmiary()
            override fun onNothingSelected(parent: AdapterView<*>?) {}
        }
        ustawWarianty()

        oknoOtwarte = true
        AlertDialog.Builder(this)
            .setTitle(if (kod != null) "Przypisz kod $kod do:" else "Wybierz pozycję")
            .setView(uklad)
            .setPositiveButton(if (kod != null) "Przypisz" else "Wybierz") { _, _ ->
                val k = pozycje.getOrNull(spR.selectedItemPosition)
                if (k != null) {
                    if (kod != null) {
                        wyslijPolecenie("@KOD|$kod|${k.w}|${k.r}")
                        k.kody.add(if (kod.length == 12 && kod.all { it.isDigit() }) "0$kod" else kod)
                        dodajHistorieMag("kod $kod -> ${opisKat(k).replace("\n", ", ")}")
                        ustawWybrana(k, "Kod $kod")
                    } else {
                        ustawWybrana(k, "Wybrano")
                    }
                }
            }
            .setNegativeButton("Anuluj", null)
            .setOnDismissListener {
                oknoOtwarte = false
                kodWKadrze = null
            }
            .show()
    }

    // ------------------------------------------------------------------
    //  ZAKOŃCZ - całkowicie (nie w tle)
    // ------------------------------------------------------------------
    private fun zakoncz() {
        zatrzymajKamere()
        serwer.stop()
        handler.removeCallbacksAndMessages(null)
        finishAndRemoveTask()
        Handler(Looper.getMainLooper()).postDelayed({ exitProcess(0) }, 300)
    }

    override fun onDestroy() {
        super.onDestroy()
        serwer.stop()
        watekKamery.shutdown()
        skaner?.close()
        ton?.release()
    }
}
