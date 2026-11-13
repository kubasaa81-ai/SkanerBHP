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
import android.widget.ListView
import androidx.activity.result.PickVisualMediaRequest
import java.io.File
import java.io.FileOutputStream
import androidx.camera.core.ImageProxy
import androidx.camera.core.Preview
import androidx.camera.lifecycle.ProcessCameraProvider
import androidx.camera.view.PreviewView
import androidx.core.content.ContextCompat
import androidx.core.content.FileProvider
import com.google.mlkit.vision.barcode.BarcodeScanner
import com.google.mlkit.vision.barcode.BarcodeScannerOptions
import com.google.mlkit.vision.barcode.BarcodeScanning
import com.google.mlkit.vision.barcode.common.Barcode
import com.google.mlkit.vision.common.InputImage
import com.google.mlkit.vision.text.TextRecognition
import com.google.mlkit.vision.text.latin.TextRecognizerOptions
import java.net.Inet4Address
import java.net.NetworkInterface
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import kotlin.system.exitProcess

/**
 * Skaner BHP - telefon jako skaner dla Programu BHP (Excel) przez sieć firmową (GlobalProtect).
 * Ekran startowy: Odzież i ŚOI (-> Wydanie / Dostawa / Inwentura / Kody producenta) / Wypadki / Chemia / Zakończ.
 * Wydanie: komputer wysyła listę "co wydać", aparat czyta kody, komputer pobiera skany i odsyła wynik.
 * Dostawa / Inwentura / Kody: katalog z komputera (warianty, rozmiary, stany, kody producenta) -
 *   znany kod = od razu pozycja, nieznany = wybór z listy i przypisanie kodu; polecenia @DOST / @INW / @KOD.
 * Etykiety chemii: komputer wysyła spis substancji (produkt x wydział), na wydziale robisz zdjęcia etykiet
 *   produktów "do ustalenia" (czy niebezpieczny, czy karta wymagana) - komputer pobiera je do produktów
 *   (Spis substancji -> "Zdjęcia z telefonu").  Lista zostaje w telefonie, gdy na hali nie ma zasięgu.
 * Maszyny - pomiary: komputer wysyła źródła z pomiarów (stary spis) i kartotekę maszyn; na hali przypisujesz
 *   źródłu maszynę z kartoteki (nr inw. z tabliczki albo wybór z listy, kilka maszyn = rozbicie, "nie maszyna");
 *   komputer pobiera przypisania (Pomiary -> Maszyny w pomiarach -> "Połączenia z telefonu").
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
    private lateinit var ekranChem: LinearLayout
    private lateinit var ekranOdziez: LinearLayout
    private lateinit var ekranChemMenu: LinearLayout
    private lateinit var tKomputerChemMenu: TextView
    private lateinit var tTytulChem: TextView
    private lateinit var przewChem: ScrollView
    private lateinit var bRozpoznajChem: Button
    private lateinit var wPrzyciskiChem: LinearLayout
    private var trybChem = 0                                  // 0 do ustalenia, 1 bez kart, 2 zdjęcie substancji
    private lateinit var wWydzChem: LinearLayout
    private lateinit var bKartaChem: Button
    // seria zdjęć: 1 substancje (wydział na końcu), 2 strony karty znanego produktu, 3 strony karty - produkt rozpozna z karty
    private var trybSerii = 0
    private class ZdjSerii(val plik: File) { @Volatile var tekst = ""; @Volatile var nazwa = ""; @Volatile var gotowe = false; var zrobione = false }
    private val seriaChem = mutableListOf<ZdjSerii>()
    private var kartaCel: Triple<Int, String, String>? = null
    private var dalejSerii: (() -> Unit)? = null                     // seria substancji: po wyborze produktu - następne zdjęcie
    private var zapisKarty: ((Triple<Int, String, String>) -> Unit)? = null   // seria karty: wybrany produkt -> zapis stron
    private var nSeriiAuto = 0
    private var nSeriiRecz = 0
    private lateinit var ekranMasz: LinearLayout
    private lateinit var tKomputerOdz: TextView
    @Volatile private var tryb = "MENU"            // MENU / WYDANIE / DOSTAWA / INWENTURA / KODY / ZDJECIA / CHEMIA
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
    // sprawy wypadkowe z komputera (bez nazwisk - RODO): wypadki/sprawy.txt "WSL|wersja" + linie "id|opis"
    private var sprawyWyp: List<Pair<Int, String>> = emptyList()
    @Volatile private var wersjaSprawWyp = ""
    private lateinit var spSprawaZdj: Spinner
    private val aparatZdj = registerForActivityResult(ActivityResultContracts.TakePicture()) { ok ->
        val f = plikAparatu
        if (ok && f != null && f.exists()) {
            val sp = sprawaWybranaZdj()
            watekKamery.execute {
                try {
                    val bmp = wczytajObraz({ f.inputStream() }, 1600)
                    if (bmp != null) {
                        val nr = (plikiZdjec().maxOfOrNull { it.first } ?: 0) + 1
                        FileOutputStream(File(folderZdj, "zdj_$nr.jpg")).use { bmp.compress(Bitmap.CompressFormat.JPEG, 85, it) }
                        File(folderZdj, "zdj_$nr.sp").writeText(sp.toString(), Charsets.UTF_8)
                    }
                } catch (e: Exception) {
                }
                f.delete()
                runOnUiThread {
                    pokazListeZdjec()
                    AlertDialog.Builder(this)
                        .setTitle("Zapisano zdjęcie")
                        .setMessage("Opis możesz dopisać pod zdjęciem. Komputer zabierze zdjęcia sam, gdy Program BHP jest otwarty.")
                        .setPositiveButton("Następne zdjęcie") { _, _ -> zrobZdjecieWyp() }
                        .setNegativeButton("Koniec", null)
                        .show()
                }
            }
        }
    }
    private val prosbaKameraZdj = registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
        if (ok) zrobZdjecieWyp() else Toast.makeText(this, "Bez zgody na aparat - wybierz zdjęcia z galerii", Toast.LENGTH_LONG).show()
    }
    private val folderZdj: File by lazy { File(filesDir, "zdjecia").apply { mkdirs() } }

    // etykiety chemii: lista z komputera (chemia/lista.txt), zdjęcia chemia/ch_<nr>.jpg + ch_<nr>.txt ("id|kod|nazwa")
    private class ProdChem(val id: Int, val kod: String, val doUst: Boolean, val nazwa: String, val producent: String, val miejsce: String, val stan: String = "")
    private var listaChem: List<ProdChem> = emptyList()
    @Volatile private var dataListyChem = ""
    @Volatile private var wersjaListyChem = ""
    @Volatile private var ostatnieTlo = 0L                 // ostatnie odpytanie w tle (GET /stan) - Program BHP otwarty
    private lateinit var tWynikiChem: TextView
    private var filtrChem = 0                               // 0 do ustalenia, 1 brak karty, 2 wszystkie
    private val rozpoznawanie by lazy { TextRecognition.getClient(TextRecognizerOptions.DEFAULT_OPTIONS) }
    private val folderChem: File by lazy { File(filesDir, "chemia").apply { mkdirs() } }
    private lateinit var tKomputerChem: TextView
    private lateinit var tStanChem: TextView
    private lateinit var spWydzChem: Spinner
    private lateinit var bWszystkieChem: Button
    private lateinit var listaChemWidok: LinearLayout
    private var wydzialyChem: List<String> = emptyList()
    private var wszystkieWydzChem: List<Pair<String, String>> = emptyList()     // kod, nazwa - wszystkie wydziały z komputera
    private var celZdjecia: Triple<Int, String, String>? = null      // id produktu (0 = spoza listy, -1 do przypisania, -2 rozpoznaj), kod wydziału, nazwa
    private var typZdjeciaChem = "E"                                  // E etykieta, K karta charakterystyki (papier na wydziale)
    private var plikAparatu: File? = null
    private val aparatChem = registerForActivityResult(ActivityResultContracts.TakePicture()) { ok ->
        val f = plikAparatu
        val cel = celZdjecia
        if (trybSerii != 0) {
            if (ok && f != null && f.exists()) dodajDoSerii(f) else if (seriaChem.isEmpty()) trybSerii = 0 else pytajSerie()
        } else if (ok && f != null && f.exists() && cel != null && cel.first == -2) {
            rozpoznajZdjecieChem(f, cel.second)
        } else if (ok && f != null && f.exists() && cel != null) {
            zapiszZdjecieChem(cel, { f.inputStream() }, typZdjeciaChem) { f.delete() }
            if (cel.first == -1) {
                AlertDialog.Builder(this)
                    .setTitle("Zapisano zdjęcie (wydział ${cel.second})")
                    .setPositiveButton("Następne zdjęcie") { _, _ -> zrobZdjecieChem() }
                    .setNegativeButton("Koniec", null)
                    .show()
            }
        }
    }
    private val galeriaChem = registerForActivityResult(ActivityResultContracts.PickMultipleVisualMedia(10)) { uris ->
        val cel = celZdjecia
        if (cel != null && cel.first != -2) for (u in uris) zapiszZdjecieChem(cel, { contentResolver.openInputStream(u) }, typZdjeciaChem) {}
    }
    private val prosbaKameraChem = registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
        if (ok) zrobZdjecieChem() else Toast.makeText(this, "Bez zgody na aparat - wybierz zdjęcie z galerii", Toast.LENGTH_LONG).show()
    }

    // maszyny - pomiary: lista z komputera maszyny/lista.txt, przypisania maszyny/powiazania.txt ("idZ|P/R/X|id,id")
    private class ZrodloM(val id: Int, val kod: String, val nazwa: String, val typ: String, val nrInw: String, val idM: Int, val opisM: String, val poza: Boolean)
    private class MaszynaK(val id: Int, val kod: String, val nrInw: String, val nrWewn: String, val nazwa: String, val typ: String, val miejsce: String)
    private var zrodlaM: List<ZrodloM> = emptyList()
    private var kartotekaM: List<MaszynaK> = emptyList()
    @Volatile private var dataListyM = ""
    @Volatile private var wersjaListyM = ""
    private val folderMasz: File by lazy { File(filesDir, "maszyny").apply { mkdirs() } }
    private lateinit var tKomputerMasz: TextView
    private lateinit var tStanMasz: TextView
    private lateinit var spWydzMasz: Spinner
    private lateinit var bTylkoMasz: Button
    private lateinit var listaMaszWidok: LinearLayout
    private var wszystkieMasz = false
    private var wydzialyMasz: List<String> = emptyList()

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
    private lateinit var bSkanujMag: Button          // to samo w Dostawie / Inwenturze / Kodach
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
        zbudujOdziez()
        zbudujWydanie()
        zbudujMagazyn()
        zbudujZdjecia()
        zbudujChemie()
        zbudujChemiaMenu()
        zbudujMaszyny()
        pokazStart()
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.SEND_SMS) != PackageManager.PERMISSION_GRANTED) {
            prosbaSms.launch(Manifest.permission.SEND_SMS)
        }
        val blad = serwer.start(8080)
        if (blad != null) Toast.makeText(this, "Serwer: $blad", Toast.LENGTH_LONG).show()
        onBackPressedDispatcher.addCallback(this) {
            when (tryb) {
                "MENU" -> moveTaskToBack(true)
                "WYDANIE", "DOSTAWA", "INWENTURA", "KODY" -> pokazOdziez()
                "CHEMIA" -> pokazChemiaMenu()
                else -> pokazStart()
            }
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

    // przycisk z dwiema liniami tekstu
    private fun lpWysoki(gora: Int): LinearLayout.LayoutParams {
        val p = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(96))
        p.topMargin = dp(gora)
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
        ekranStart.addView(tekst("Program BHP - odzież i ŚOI, wypadki, chemia, maszyny", 15f, szary))

        tSiec = tekst("", 15f, szary, true)
        tSiec.setPadding(0, dp(16), 0, 0)
        ekranStart.addView(tSiec)
        tKomputerStart = tekst("", 14f, szary)
        tKomputerStart.setPadding(0, dp(4), 0, dp(8))
        ekranStart.addView(tKomputerStart)

        bVpn = przycisk("Włącz GlobalProtect", niebieski, 17f) { otworzGlobalProtect() }
        ekranStart.addView(bVpn, lpPelny(4))

        ekranStart.addView(przycisk("Odzież i ŚOI", Color.rgb(46, 125, 50), 24f) { pokazOdziez() }, lpPelny(18))
        ekranStart.addView(przycisk("Wypadki - zdjęcia", Color.rgb(198, 40, 40), 22f) { pokazZdjecia() }, lpPelny(12))
        ekranStart.addView(przycisk("Chemia", Color.rgb(106, 27, 154), 22f) { pokazChemiaMenu() }, lpPelny(12))
        ekranStart.addView(przycisk("Maszyny - pomiary", Color.rgb(69, 90, 100), 22f) { pokazMaszyny() }, lpPelny(12))

        val odstep = View(this)
        ekranStart.addView(odstep, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))
        ekranStart.addView(przycisk("Zakończ", czerwony, 20f) { zakoncz() }, lpPelny(12))
    }

    // podmenu: Odzież i ŚOI
    private fun zbudujOdziez() {
        ekranOdziez = LinearLayout(this)
        ekranOdziez.orientation = LinearLayout.VERTICAL
        ekranOdziez.setPadding(dp(18), dp(18), dp(18), dp(18))
        ekranOdziez.setBackgroundColor(Color.rgb(245, 248, 252))
        val w1 = wiersz()
        w1.addView(przycisk("\u2190 Menu", szary) { pokazStart() })
        w1.addView(tekst("  Odzież i ŚOI", 24f, Color.rgb(46, 125, 50), true), lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranOdziez.addView(w1)
        tKomputerOdz = tekst("", 14f, szary)
        tKomputerOdz.setPadding(0, dp(10), 0, dp(4))
        ekranOdziez.addView(tKomputerOdz)
        ekranOdziez.addView(przycisk("Wydanie", Color.rgb(46, 125, 50), 22f) { pokazWydanie() }, lpPelny(14))
        ekranOdziez.addView(przycisk("Dostawa", Color.rgb(93, 64, 55), 22f) { pokazMagazyn("DOSTAWA") }, lpPelny(12))
        ekranOdziez.addView(przycisk("Inwentura", Color.rgb(2, 119, 189), 22f) { pokazMagazyn("INWENTURA") }, lpPelny(12))
        ekranOdziez.addView(przycisk("Kody producenta", Color.rgb(239, 108, 0), 20f) { pokazMagazyn("KODY") }, lpPelny(12))
    }

    private fun pokazOdziez() {
        tryb = "ODZIEZ"
        zatrzymajKamere()
        ustawSkanuj(false)
        setContentView(ekranOdziez)
        pokazStan()
    }

    private fun zbudujWydanie() {
        ekranWydanie = LinearLayout(this)
        ekranWydanie.orientation = LinearLayout.VERTICAL
        ekranWydanie.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranWydanie.setBackgroundColor(Color.rgb(245, 248, 252))

        val w1 = wiersz()
        w1.addView(przycisk("← Odzież", szary) { pokazOdziez() })
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
    // Program BHP otwarty na komputerze (odpytuje w tle co kilkanaście sekund)
    private fun tloWidziane(): Boolean = ostatnieTlo > 0 && SystemClock.elapsedRealtime() - ostatnieTlo < 75000

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
        // ekran startowy: połączenie w tle (Program BHP otwarty) też się liczy - nie tylko Wydanie odzieży
        tKomputerStart.text = when {
            komputerWidziany() -> k
            tloWidziane() -> "✔ Program BHP otwarty - komputer połączony (wymiana w tle)"
            !vpn -> "Komputer nie widzi telefonu - włącz GlobalProtect"
            else -> "Czekam na komputer - Program BHP połączy się sam w kilka sekund po otwarciu"
        }
        tKomputerStart.setTextColor(if (komputerWidziany() || tloWidziane()) zielony else pomaranczowy)
        if (::tKomputerOdz.isInitialized) {
            tKomputerOdz.text = k
            tKomputerOdz.setTextColor(kolor)
        }
        if (::tKomputer.isInitialized) {
            tKomputer.text = if (vpn) k else "GlobalProtect wyłączony - wróć do Menu i włącz"
            tKomputer.setTextColor(if (vpn) kolor else czerwony)
        }
        if (::tKomputerZdj.isInitialized) {
            tKomputerZdj.text = when {
                !vpn -> "GlobalProtect wyłączony - zdjęcia czekają w telefonie, komputer zabierze je później"
                tloWidziane() || komputerWidziany() -> "\u2714 Program BHP otwarty - zdjęcia same idą do sprawy"
                else -> "Program BHP zamknięty - zdjęcia czekają w telefonie, pójdą same po jego otwarciu"
            }
            tKomputerZdj.setTextColor(if (vpn && (tloWidziane() || komputerWidziany())) zielony else szary)
        }
        if (::tKomputerMasz.isInitialized) {
            tKomputerMasz.text = when {
                zrodlaM.isEmpty() -> "Brak listy - otwórz Program BHP na komputerze (lista przyjdzie sama)"
                !vpn -> "Lista z $dataListyM - przypisania czekają w telefonie, komputer pobierze je później"
                tloWidziane() || komputerWidziany() -> "\u2714 Program BHP otwarty - połączenia idą do bazy same  (lista z $dataListyM)"
                else -> "Lista z $dataListyM - Program BHP zamknięty: połączenia czekają, pójdą same po jego otwarciu"
            }
            tKomputerMasz.setTextColor(if (zrodlaM.isEmpty()) pomaranczowy else if (vpn && (tloWidziane() || komputerWidziany())) zielony else szary)
        }
        if (::tKomputerChemMenu.isInitialized) {
            tKomputerChemMenu.text = if (vpn && (tloWidziane() || komputerWidziany())) "\u2714 Program BHP otwarty - spis i zdjęcia wymieniają się same"
                else if (!vpn) "GlobalProtect wyłączony - zdjęcia czekają w telefonie" else "Program BHP zamknięty - zdjęcia pójdą same po jego otwarciu"
            tKomputerChemMenu.setTextColor(if (vpn && (tloWidziane() || komputerWidziany())) zielony else szary)
        }
        if (::tKomputerChem.isInitialized) {
            tKomputerChem.text = when {
                listaChem.isEmpty() && (tloWidziane() || komputerWidziany()) -> "Program BHP otwarty - spis za chwilę przyjdzie sam"
                listaChem.isEmpty() -> "Brak spisu - otwórz Program BHP na komputerze (spis przyjdzie sam)"
                !vpn -> "Spis z $dataListyChem (${listaChem.size} poz.) - zdjęcia czekają w telefonie, pójdą same po włączeniu GlobalProtect"
                tloWidziane() || komputerWidziany() -> "\u2714 Program BHP otwarty - zdjęcia idą do bazy na bieżąco  (spis z $dataListyChem)"
                else -> "Spis z $dataListyChem - Program BHP zamknięty: zdjęcia czekają, pójdą same po jego otwarciu"
            }
            tKomputerChem.setTextColor(if (listaChem.isEmpty()) pomaranczowy else if (vpn && (tloWidziane() || komputerWidziany())) zielony else szary)
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
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranZdj.addView(w1)

        tSprawaZdj = tekst("", 15f, Color.rgb(173, 20, 87), true)
        tSprawaZdj.setPadding(0, dp(6), 0, 0)
        ekranZdj.addView(tSprawaZdj)
        tKomputerZdj = tekst("", 13f, szary)
        tKomputerZdj.setPadding(0, dp(2), 0, dp(6))
        ekranZdj.addView(tKomputerZdj)

        val ws = wiersz()
        ws.addView(tekst("Sprawa: ", 16f, szary, true))
        spSprawaZdj = Spinner(this)
        ws.addView(spSprawaZdj, lp(1f))
        ekranZdj.addView(ws)

        val wz = wiersz()
        wz.addView(przycisk("\uD83D\uDCF7  Zrób zdjęcie", czerwony, 18f) { zrobZdjecieWyp() }, lp(1f))
        bGaleria = przycisk("Z galerii", Color.rgb(121, 85, 72), 16f) {
            wyborZdjec.launch(PickVisualMediaRequest(ActivityResultContracts.PickVisualMedia.ImageOnly))
        }
        wz.addView(bGaleria, lp(0.6f, 6))
        ekranZdj.addView(wz, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(64)))
        wczytajSprawyWypZPliku()

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
        tSprawaZdj.text = if (sprawaZdj.isNotBlank()) sprawaZdj else ""
        ustawSprawyWyp()
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
        val spr = sprawaWybranaZdj()
        watekKamery.execute {
            var ok = 0
            for (u in uris) {
                try {
                    val bmp = wczytajObraz({ contentResolver.openInputStream(u) }, 1600) ?: continue
                    val nr = (plikiZdjec().maxOfOrNull { it.first } ?: 0) + 1
                    FileOutputStream(File(folderZdj, "zdj_$nr.jpg")).use { bmp.compress(Bitmap.CompressFormat.JPEG, 85, it) }
                    File(folderZdj, "zdj_$nr.sp").writeText(spr.toString(), Charsets.UTF_8)
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
                    .setMessage("Komputer go nie dostanie.")
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
        File(folderZdj, "zdj_$nr.sp").delete()
    }

    private fun sprawaZdjecia(nr: Int): Int {
        val t = File(folderZdj, "zdj_$nr.sp")
        return if (t.exists()) t.readText(Charsets.UTF_8).trim().toIntOrNull() ?: 0 else 0
    }

    private fun sprawaWybranaZdj(): Int {
        if (!::spSprawaZdj.isInitialized) return 0
        val i = spSprawaZdj.selectedItemPosition - 1
        return if (i in sprawyWyp.indices) sprawyWyp[i].first else 0
    }

    private fun wczytajSprawyWypZPliku() {
        val f = File(folderZdj, "sprawy.txt")
        if (f.exists()) try { przetworzSprawyWyp(f.readText(Charsets.UTF_8)) } catch (e: Exception) {}
    }

    private fun przetworzSprawyWyp(tekst: String) {
        val linie = tekst.replace("\r", "").split("\n")
        if (linie.isEmpty() || !linie[0].startsWith("WSL|")) return
        sprawyWyp = linie.drop(1).mapNotNull { l ->
            val p = l.split("|", limit = 2)
            val id = p[0].trim().toIntOrNull() ?: return@mapNotNull null
            Pair(id, polskie(p.getOrElse(1) { "" }.trim()))
        }
        wersjaSprawWyp = linie[0].substringAfter("|").trim()
    }

    private fun ustawSprawyWyp() {
        if (!::spSprawaZdj.isInitialized) return
        val stary = sprawaWybranaZdj()
        val opisy = listOf("(wybiorę na komputerze)") + sprawyWyp.map { it.second }
        spSprawaZdj.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, opisy)
        val i = sprawyWyp.indexOfFirst { it.first == stary }
        spSprawaZdj.setSelection(if (i >= 0) i + 1 else if (sprawyWyp.size == 1) 1 else 0)
    }

    // serwer: POST /zdjecia_sprawy "WSL|wersja" + linie "id|opis"
    override fun zdjeciaSprawy(tekst: String) {
        try { File(folderZdj, "sprawy.txt").writeText(tekst, Charsets.UTF_8) } catch (e: Exception) {}
        przetworzSprawyWyp(tekst)
        runOnUiThread { ustawSprawyWyp() }
    }

    private fun zrobZdjecieWyp() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            prosbaKameraZdj.launch(Manifest.permission.CAMERA)
            return
        }
        try {
            val f = File(cacheDir, "aparat_wypadek.jpg")
            if (f.exists()) f.delete()
            plikAparatu = f
            aparatZdj.launch(FileProvider.getUriForFile(this, "$packageName.pliki", f))
        } catch (e: Exception) {
            Toast.makeText(this, "Nie udało się otworzyć aparatu: ${e.message}", Toast.LENGTH_LONG).show()
        }
    }

    private fun usunWszystkieZdjecia() {
        val n = plikiZdjec().size
        if (n == 0) return
        AlertDialog.Builder(this)
            .setTitle("Usunąć wszystkie zdjęcia z aplikacji ($n)?")
            .setMessage("Komputer ich już nie dostanie.")
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
        return "ZDJ|" + l.size + l.joinToString("") { "\n${it.first}|" + naKomputer(opisZdjecia(it.first)) + "|" + sprawaZdjecia(it.first) }
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
                tStanZdj.text = "\u2714 Komputer zabrał zdjęcia do sprawy - " + tStanZdj.text
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
            // bez zgody (np. "ustawienia z ograniczeniami" dla aplikacji spoza Sklepu Play) -
            // otwiera Wiadomości z gotowym SMS-em, wystarczy nacisnąć Wyślij
            return try {
                val i = Intent(Intent.ACTION_SENDTO, Uri.parse("smsto:$numer")).putExtra("sms_body", tresc)
                i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                runOnUiThread {
                    try {
                        startActivity(i)
                    } catch (e: Exception) {
                        Toast.makeText(this, "Nie udało się otworzyć Wiadomości", Toast.LENGTH_LONG).show()
                    }
                }
                "OTWARTO"
            } catch (e: Exception) {
                "BRAK_UPRAWNIEN"
            }
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
    //  ETYKIETY CHEMII
    //  POST /chemia:  "CHL|data|wersja" + linie "id|kod|1/0 do ustalenia|nazwa|producent|miejsce|stan karty"  (~a = ą ...)
    //                 kod "-" = produkt bez wydziału (tylko do rozpoznawania zdjęć)
    //  GET /chemia_zdjecia -> "CHZ|n" + linie "nr|id|kod|nazwa|typ E/K|odczyt z etykiety";  GET /chemia_zdjecie?nr=N;
    //  POST /chemia_odebrane "nr,nr";  POST /chemia_wyniki - linie "tekst" (co komputer zrobił ze zdjęciami)
    //  Program BHP otwarty odpytuje w tle GET /stan i sam wysyła spis / zabiera zdjęcia.
    // ------------------------------------------------------------------
    private fun zbudujChemie() {
        ekranChem = LinearLayout(this)
        ekranChem.orientation = LinearLayout.VERTICAL
        ekranChem.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranChem.setBackgroundColor(Color.rgb(245, 248, 252))
        val fiolet = Color.rgb(106, 27, 154)

        val w1 = wiersz()
        w1.addView(przycisk("← Chemia", szary) { pokazChemiaMenu() })
        tTytulChem = tekst("  Chemia", 20f, fiolet, true)
        w1.addView(tTytulChem, lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranChem.addView(w1)

        tKomputerChem = tekst("", 13f, szary)
        tKomputerChem.setPadding(0, dp(6), 0, dp(4))
        ekranChem.addView(tKomputerChem)

        val w2 = wiersz()
        wWydzChem = w2
        w2.addView(tekst("Wydział: ", 16f, szary, true))
        spWydzChem = Spinner(this)
        w2.addView(spWydzChem, lp(1f))
        bWszystkieChem = przycisk("Pokaż: do ustalenia", pomaranczowy, 13f) {
            filtrChem = (filtrChem + 1) % 3
            pokazListeChem()
        }
        w2.addView(bWszystkieChem, lp(1f, 6))
        bWszystkieChem.visibility = View.GONE              // rodzaj listy wybierany w menu Chemia
        ekranChem.addView(w2)
        spWydzChem.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(parent: AdapterView<*>?, view: View?, position: Int, id: Long) = pokazListeChem()
            override fun onNothingSelected(parent: AdapterView<*>?) {}
        }

        tStanChem = tekst("", 14f, szary, true)
        tStanChem.gravity = Gravity.CENTER
        tStanChem.setPadding(0, dp(6), 0, dp(2))
        ekranChem.addView(tStanChem)
        tWynikiChem = tekst("", 13f, zielony)
        tWynikiChem.setPadding(0, 0, 0, dp(4))
        tWynikiChem.setOnClickListener { pokazWynikiChem() }
        ekranChem.addView(tWynikiChem)

        przewChem = ScrollView(this)
        listaChemWidok = LinearLayout(this)
        listaChemWidok.orientation = LinearLayout.VERTICAL
        przewChem.addView(listaChemWidok)
        ekranChem.addView(przewChem, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        bRozpoznajChem = przycisk("\uD83D\uDCF7  Zrób zdjęcie\n(potem: kolejne albo koniec, na końcu wybierzesz wydział)", fiolet, 18f) { startSeriiSubstancji() }
        ekranChem.addView(bRozpoznajChem, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(110)))
        bKartaChem = przycisk("\uD83D\uDCC4  Jest karta - zrób zdjęcie\n(strony po kolei, produkt rozpozna z karty)", Color.rgb(198, 40, 40), 17f) { startSeriiKarty(null) }
        val lpK = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(96))
        lpK.topMargin = dp(6)
        ekranChem.addView(bKartaChem, lpK)
        val w3 = wiersz()
        wPrzyciskiChem = w3
        w3.addView(przycisk("+ Spoza spisu (wpiszę nazwę)", Color.rgb(74, 20, 140), 14f) { produktSpozaListy() }, lp(1f))
        w3.addView(przycisk("Zdjęcia wydziału\n(przypiszemy później)", Color.rgb(0, 121, 107), 14f) { zdjeciaWydzialu() }, lp(1f, 6))
        val lpW3 = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(60))
        lpW3.topMargin = dp(6)
        ekranChem.addView(w3, lpW3)
        wczytajListeChemZPliku()
        pokazOstatnieWynikiChem()
    }

    // podmenu Chemia: do ustalenia / bez kart / zdjęcie substancji
    private fun zbudujChemiaMenu() {
        val fiolet = Color.rgb(106, 27, 154)
        ekranChemMenu = LinearLayout(this)
        ekranChemMenu.orientation = LinearLayout.VERTICAL
        ekranChemMenu.setPadding(dp(18), dp(18), dp(18), dp(18))
        ekranChemMenu.setBackgroundColor(Color.rgb(245, 248, 252))
        val w1 = wiersz()
        w1.addView(przycisk("\u2190 Menu", szary) { pokazStart() })
        w1.addView(tekst("  Chemia", 24f, fiolet, true), lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranChemMenu.addView(w1)
        tKomputerChemMenu = tekst("", 14f, szary)
        tKomputerChemMenu.setPadding(0, dp(10), 0, dp(4))
        ekranChemMenu.addView(tKomputerChemMenu)
        ekranChemMenu.addView(przycisk("Substancje do ustalenia\n(zdjęcie etykiety)", pomaranczowy, 20f) { pokazChemie(0) }, lpWysoki(14))
        ekranChemMenu.addView(przycisk("Substancje bez kart charakterystyki\n(jest karta - zrób zdjęcie)", Color.rgb(198, 40, 40), 20f) { pokazChemie(1) }, lpWysoki(12))
        ekranChemMenu.addView(przycisk("Zdjęcie substancji\n(zdjęcia po kolei, na końcu wydział)", fiolet, 20f) { pokazChemie(2) }, lpWysoki(12))
    }

    private fun pokazChemiaMenu() {
        zatrzymajKamere()
        tryb = "CHEMIA_MENU"
        setContentView(ekranChemMenu)
        pokazStan()
    }

    private fun pokazChemie(t: Int = trybChem) {
        zatrzymajKamere()
        trybChem = t
        filtrChem = if (t == 1) 1 else 0
        tTytulChem.text = when (t) { 0 -> "  Do ustalenia"; 1 -> "  Bez kart"; else -> "  Zdjęcie substancji" }
        val lista = t != 2
        przewChem.visibility = if (lista) View.VISIBLE else View.GONE
        wWydzChem.visibility = if (lista) View.VISIBLE else View.GONE
        bRozpoznajChem.visibility = if (lista) View.GONE else View.VISIBLE
        bKartaChem.visibility = if (t == 1) View.VISIBLE else View.GONE
        wPrzyciskiChem.visibility = View.GONE              // wydział wybierany na końcu serii zdjęć
        tryb = "CHEMIA"
        setContentView(ekranChem)
        ustawWydzialyChem()
        pokazStan()
    }

    private fun wczytajListeChemZPliku() {
        val f = File(folderChem, "lista.txt")
        if (f.exists()) try { przetworzListeChem(f.readText(Charsets.UTF_8)) } catch (e: Exception) {}
    }

    private fun przetworzListeChem(tekst: String) {
        val linie = tekst.replace("\r", "").split("\n")
        if (linie.isEmpty() || !linie[0].startsWith("CHL|")) return
        val nowa = mutableListOf<ProdChem>()
        val wydz = mutableListOf<Pair<String, String>>()
        for (l in linie.drop(1)) {
            val p = l.split("|")
            if (p.size == 3 && p[0] == "W") { wydz.add(Pair(polskie(p[1].trim()), polskie(p[2].trim()))); continue }
            if (p.size < 4) continue
            val id = p[0].trim().toIntOrNull() ?: continue
            nowa.add(ProdChem(id, polskie(p[1].trim()), p[2].trim() == "1", polskie(p[3].trim()),
                polskie(p.getOrElse(4) { "" }.trim()), polskie(p.getOrElse(5) { "" }.trim()), polskie(p.getOrElse(6) { "" }.trim())))
        }
        listaChem = nowa
        wszystkieWydzChem = wydz
        val n = linie[0].split("|")
        dataListyChem = n.getOrElse(1) { "" }.trim()
        wersjaListyChem = n.getOrElse(2) { "" }.trim()
    }

    // serwer: POST /chemia
    override fun chemia(tekst: String) {
        try { File(folderChem, "lista.txt").writeText(tekst, Charsets.UTF_8) } catch (e: Exception) {}
        przetworzListeChem(tekst)
        runOnUiThread {
            if (tryb == "CHEMIA") ustawWydzialyChem()
            if (tryb == "CHEMIA") Toast.makeText(this, "Spis substancji z komputera zaktualizowany", Toast.LENGTH_SHORT).show()
        }
    }

    private fun ustawWydzialyChem() {
        val stary = spWydzChem.selectedItem?.toString()
        wydzialyChem = listaChem.map { it.kod }.filter { it != "-" && it.isNotBlank() }.distinct().sorted()
        val opisy = wydzialyChem.map { k ->
            val n = listaChem.count { it.kod == k && it.doUst && liczbaZdjecChem(it.id, k) == 0 }
            val b = listaChem.count { it.kod == k && brakKarty(it) }
            k + (if (n > 0) "  ($n do ustalenia" + (if (b > 0) ", $b bez karty)" else ")") else if (b > 0) "  ($b bez karty)" else "")
        }
        spWydzChem.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, opisy)
        val i = if (stary != null) opisy.indexOfFirst { it.substringBefore(" ") == stary.substringBefore(" ") } else -1
        if (i >= 0) spWydzChem.setSelection(i)
        pokazListeChem()
    }

    private fun wydzialChem(): String {
        val i = spWydzChem.selectedItemPosition
        return if (i in wydzialyChem.indices) wydzialyChem[i] else ""
    }

    private fun zdjeciaChem(): List<Pair<Int, File>> {
        val f = folderChem.listFiles() ?: return emptyList()
        return f.filter { it.name.startsWith("ch_") && it.name.endsWith(".jpg") }
            .mapNotNull { pl -> pl.name.removePrefix("ch_").removeSuffix(".jpg").toIntOrNull()?.let { Pair(it, pl) } }
            .sortedBy { it.first }
    }

    private fun opisZdjeciaChem(nr: Int): List<String> {
        val t = File(folderChem, "ch_$nr.txt")
        return if (t.exists()) t.readText(Charsets.UTF_8).split("|", limit = 5) else listOf("0", "", "", "E", "")
    }

    private fun liczbaZdjecChem(id: Int, kod: String): Int = zdjeciaChem().count {
        val o = opisZdjeciaChem(it.first)
        o.getOrNull(0) == id.toString() && o.getOrNull(1) == kod
    }

    // zdjęcia już pobrane przez komputer: "id|kod" (żeby na hali było widać, co jest zrobione)
    private fun wyslaneChem(): Set<String> {
        val f = File(folderChem, "wyslane.txt")
        return if (f.exists()) f.readLines(Charsets.UTF_8).toSet() else emptySet()
    }

    private fun pokazListeChem() {
        if (!::listaChemWidok.isInitialized) return
        listaChemWidok.removeAllViews()
        if (trybChem == 2) {
            val czeka = zdjeciaChem().size
            tStanChem.text = (if (listaChem.isEmpty()) "Spis przyjdzie sam, gdy na komputerze będzie otwarty Program BHP\n" else "") +
                "Rób zdjęcia etykiet po kolei. Na koniec wybierzesz wydział - telefon rozpozna produkty, a nowe komputer dopisze do spisu." +
                if (czeka > 0) "\nZdjęć czeka na komputer: $czeka" else ""
            tStanChem.setTextColor(if (czeka > 0) pomaranczowy else szary)
            return
        }
        bWszystkieChem.text = when (filtrChem) { 0 -> "Pokaż: do ustalenia"; 1 -> "Pokaż: brak karty"; else -> "Pokaż: wszystkie" }
        val kod = wydzialChem()
        val wysl = wyslaneChem()
        val lista = listaChem.filter { it.kod == kod && when (filtrChem) { 0 -> it.doUst; 1 -> brakKarty(it); else -> true } }
            .sortedWith(compareBy({ !it.doUst }, { it.nazwa.lowercase() }))
        val czeka = zdjeciaChem().size
        val wydz = zdjeciaChem().count { val o = opisZdjeciaChem(it.first); o.getOrNull(0) == "-1" && o.getOrNull(1) == kod }
        tStanChem.text = (if (wydz > 0) "Zdjęcia wydziału do przypisania: $wydz\n" else "") + when {
            listaChem.isEmpty() -> "Spis przyjdzie sam, gdy na komputerze będzie otwarty Program BHP"
            lista.isEmpty() && filtrChem == 0 -> "Na tym wydziale nie ma produktów do ustalenia"
            lista.isEmpty() && filtrChem == 1 -> "Na tym wydziale wszystkie karty są w porządku"
            lista.isEmpty() -> "Na tym wydziale nie ma produktów w spisie"
            filtrChem == 1 -> "Brak / nieaktualna karta - dotknij produktu i zrób zdjęcie karty (strony po kolei)"
            else -> "Dotknij produktu = zdjęcie etykiety"
        } + if (czeka > 0) "   |   zdjęć czeka na komputer: $czeka" else ""
        tStanChem.setTextColor(if (czeka > 0) pomaranczowy else szary)
        for (p in lista) {
            val n = liczbaZdjecChem(p.id, p.kod)
            val bylo = wysl.contains("${p.id}|${p.kod}")
            val ramka = LinearLayout(this)
            ramka.orientation = LinearLayout.VERTICAL
            ramka.setPadding(dp(10), dp(8), dp(10), dp(8))
            val tlo = GradientDrawable()
            tlo.cornerRadius = dp(8).toFloat()
            tlo.setColor(Color.WHITE)
            tlo.setStroke(dp(2), when {
                n > 0 -> zielony
                bylo -> niebieski
                p.doUst || brakKarty(p) -> pomaranczowy
                else -> Color.rgb(207, 216, 220)
            })
            ramka.background = tlo
            ramka.addView(tekst(p.nazwa, 16f, Color.rgb(38, 50, 56), true))
            val opis = listOf(p.producent, p.miejsce, if (brakKarty(p)) "karta: " + p.stan.lowercase() else "").filter { it.isNotBlank() }.joinToString("  |  ")
            if (opis.isNotBlank()) ramka.addView(tekst(opis, 13f, szary))
            val stan = when {
                n > 0 -> "📷 zdjęć: $n - czekają na komputer"
                bylo -> "✔ zdjęcie wysłane do komputera"
                p.doUst -> "DO USTALENIA - zrób zdjęcie etykiety (piktogramy, hasło, zwroty H)"
                brakKarty(p) -> "BEZ KARTY w BHP - jeśli karta jest na wydziale, zrób jej zdjęcie"
                else -> "klasyfikacja ustalona"
            }
            ramka.addView(tekst(stan, 13f, if (n > 0) zielony else if (bylo) niebieski else if (p.doUst || brakKarty(p)) pomaranczowy else szary, true))
            ramka.setOnClickListener {
                if (trybChem == 1 && n == 0) startSeriiKarty(Triple(p.id, p.kod, p.nazwa)) else menuProduktuChem(p.id, p.kod, p.nazwa)
            }
            val lpR = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            lpR.topMargin = dp(6)
            listaChemWidok.addView(ramka, lpR)
        }
    }

    private fun menuProduktuChem(id: Int, kod: String, nazwa: String) {
        celZdjecia = Triple(id, kod, nazwa)
        val n = liczbaZdjecChem(id, kod)
        val opcje = if (trybChem == 1) mutableListOf("Zdjęcie karty charakterystyki (strony po kolei)")
            else mutableListOf("Zrób zdjęcie etykiety", "Zdjęcie karty charakterystyki (strony po kolei)", "Wybierz z galerii")
        if (n > 0) {
            opcje.add("Podgląd zdjęć ($n)")
            opcje.add("Usuń zdjęcia tego produktu ($n)")
        }
        AlertDialog.Builder(this)
            .setTitle(nazwa)
            .setItems(opcje.toTypedArray()) { _, k ->
                when (opcje[k]) {
                    "Zrób zdjęcie etykiety" -> { typZdjeciaChem = "E"; zrobZdjecieChem() }
                    "Zdjęcie karty charakterystyki (strony po kolei)" -> startSeriiKarty(Triple(id, kod, nazwa))
                    "Wybierz z galerii" -> { typZdjeciaChem = "E"; galeriaChem.launch(PickVisualMediaRequest(ActivityResultContracts.PickVisualMedia.ImageOnly)) }
                    else -> if (opcje[k].startsWith("Podgląd")) podgladZdjecChem(id, kod) else {
                        zdjeciaChem().filter { val o = opisZdjeciaChem(it.first); o.getOrNull(0) == id.toString() && o.getOrNull(1) == kod }
                            .forEach { usunZdjecieChem(it.first) }
                        pokazListeChem()
                    }
                }
            }
            .setNegativeButton("Zamknij", null)
            .show()
    }

    private fun produktSpozaListy() {
        val kod = wydzialChem()
        val e = EditText(this)
        e.hint = "Nazwa z etykiety (np. WD-40)"
        e.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_SENTENCES
        AlertDialog.Builder(this)
            .setTitle("Produkt spoza spisu" + if (kod.isNotEmpty()) " - wydział $kod" else "")
            .setMessage("Komputer dopisze go od razu do spisu tego wydziału.")
            .setView(e)
            .setPositiveButton("Zdjęcie") { _, _ ->
                val n = e.text.toString().trim()
                if (n.isEmpty()) {
                    Toast.makeText(this, "Wpisz nazwę produktu", Toast.LENGTH_LONG).show()
                } else {
                    celZdjecia = Triple(0, kod, n)
                    typZdjeciaChem = "E"
                    zrobZdjecieChem()
                }
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    // zdjęcia chemii na wydziale bez wskazania produktu (id -1) - komputer zbiera je "do przypisania"
    private fun zdjeciaWydzialu() {
        val kod = wydzialChem()
        if (kod.isEmpty()) {
            Toast.makeText(this, "Najpierw wybierz wydział (lista z komputera)", Toast.LENGTH_LONG).show()
            return
        }
        val e = EditText(this)
        e.hint = "Gdzie / co to jest (nieobowiązkowo), np. regał przy magazynie"
        e.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_SENTENCES
        AlertDialog.Builder(this)
            .setTitle("Zdjęcia chemii - wydział $kod")
            .setMessage("Rób zdjęcia etykiet po kolei (po każdym zapyta o następne). Na komputerze razem przypiszemy je do produktów ze spisu albo dopiszemy nowe.")
            .setView(e)
            .setPositiveButton("Aparat") { _, _ ->
                celZdjecia = Triple(-1, kod, e.text.toString().trim())
                typZdjeciaChem = "E"
                zrobZdjecieChem()
            }
            .setNeutralButton("Z galerii") { _, _ ->
                celZdjecia = Triple(-1, kod, e.text.toString().trim())
                typZdjeciaChem = "E"
                galeriaChem.launch(PickVisualMediaRequest(ActivityResultContracts.PickVisualMedia.ImageOnly))
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    // karta do zdobycia (stan z komputera)
    private fun brakKarty(p: ProdChem): Boolean =
        p.stan in setOf("BRAK KARTY", "BRAK KOPII", "NIE PO POLSKU", "STARY WZÓR", "DO WERYFIKACJI", "SPRAWDŹ KARTĘ")

    // ------------------------------------------------------------------
    //  ROZPOZNAWANIE ETYKIETY (napis z etykiety -> produkt ze spisu)
    // ------------------------------------------------------------------
    private fun zdjecieRozpoznaj() {
        val kod = wydzialChem()
        if (kod.isEmpty()) {
            Toast.makeText(this, "Najpierw wybierz wydział (spis przychodzi z komputera sam)", Toast.LENGTH_LONG).show()
            return
        }
        celZdjecia = Triple(-2, kod, "")
        typZdjeciaChem = "E"
        zrobZdjecieChem()
    }

    private fun normCh(t: String): String {
        val z = "ąćęłńóśźżäöüéè"
        val na = "acelnoszzaouee"
        val b = StringBuilder(" ")
        for (c0 in t.lowercase()) {
            val k = z.indexOf(c0)
            val c = if (k >= 0) na[k] else c0
            b.append(if (c in 'a'..'z' || c in '0'..'9') c else ' ')
        }
        b.append(' ')
        return b.toString().replace(Regex(" +"), " ")
    }

    private val slowaPomijaneCh = setOf("karta", "preparat", "srodek", "plyn", "spray", "aerozol", "rozpylacz", "czysty", "czysta",
        "olej", "farba", "nowy", "plus", "extra", "super", "color", "liquid", "conc", "pod", "nad", "przy", "oraz", "dla")

    // [id, nazwa, wynik] najlepiej pasujących produktów ze spisu
    private fun dopasujChem(tekst: String, kod: String): List<Triple<Int, String, Double>> {
        val hay = normCh(tekst)
        val wyn = mutableListOf<Triple<Int, String, Double>>()
        for (p in listaChem.distinctBy { it.id }) {
            var nm = p.nazwa
            var opis = ""
            val i = nm.indexOf(" - ")
            if (i > 3) { opis = normCh(nm.substring(i + 3)); nm = nm.substring(0, i) }
            val j = nm.indexOf(" (")
            if (j > 3) nm = nm.substring(0, j)
            val n = normCh(nm)
            var w = 0.0
            if (n.trim().length > 4 && hay.contains(n)) {
                w = 1.0 + n.length / 1000.0
            } else {
                val sl = n.trim().split(" ").filter { it.length >= 4 && it !in slowaPomijaneCh }
                if (sl.isNotEmpty()) {
                    val t = sl.count { hay.contains(" $it ") }
                    w = t.toDouble() / sl.size
                    if (sl.size == 1 && w > 0) w = 0.7
                }
            }
            if (w < 0.95 && opis.trim().length > 12 && hay.contains(opis)) w = 0.95
            if (w > 0 && listaChem.any { it.id == p.id && it.kod == kod }) w += 0.1
            if (w >= 0.5) wyn.add(Triple(p.id, p.nazwa, w))
        }
        return wyn.sortedByDescending { it.third }.take(4)
    }

    // zwroty H z kodów i z polskich zdań na etykiecie, hasło ostrzegawcze
    private fun odczytEtykiety(tekst: String): String {
        val kody = linkedSetOf<String>()
        Regex("\\b(EUH\\s?\\d{3}|H\\s?[2-4]\\d{2})\\b").findAll(tekst.uppercase()).forEach { kody.add(it.value.replace(" ", "")) }
        val n = normCh(tekst)
        val zdania = listOf(
            "skrajnie latwopalny aerozol" to "H222", "latwopalny aerozol" to "H223", "pojemnik pod cisnieniem" to "H229",
            "skrajnie latwopalna ciecz" to "H224", "wysoce latwopalna ciecz" to "H225", "latwopalna ciecz i pary" to "H226",
            "dzialaja szkodliwie po polknieciu" to "H302", "dziala szkodliwie po polknieciu" to "H302",
            "moze grozic smiercia" to "H304", "dziala drazniaco na skore" to "H315", "reakcje alergiczna skory" to "H317",
            "powoduje powazne uszkodzenie oczu" to "H318", "dziala drazniaco na oczy" to "H319",
            "powoduje powazne oparzenia skory" to "H314", "podraznienie drog oddechowych" to "H335",
            "uczucie sennosci" to "H336", "bardzo toksycznie na organizmy wodne powodujac dlugotrwale" to "H410",
            "toksycznie na organizmy wodne powodujac dlugotrwale" to "H411", "szkodliwie na organizmy wodne powodujac dlugotrwale" to "H412",
            "wysuszanie lub pekanie skory" to "EUH066", "moze wywolac reakcje alergiczna" to "EUH208")
        for ((z, k) in zdania) if (n.contains(z)) {
            if (k == "H411" && kody.contains("H410")) continue
            if (k == "H412" && (kody.contains("H410") || kody.contains("H411"))) continue
            if (k == "H226" && (kody.contains("H225") || kody.contains("H224"))) continue
            kody.add(k)
        }
        val haslo = when {
            n.contains(" niebezpieczenstwo ") || n.contains(" danger ") || n.contains(" gefahr ") -> "Niebezpieczeństwo"
            n.contains(" uwaga ") || n.contains(" warning ") || n.contains(" achtung ") -> "Uwaga"
            else -> ""
        }
        return listOf(kody.sorted().joinToString(", "), haslo).filter { it.isNotBlank() }.joinToString("; ")
    }

    private fun rozpoznajZdjecieChem(f: File, kod: String) {
        val kopia = File(cacheDir, "rozpoznaj_${System.currentTimeMillis()}.jpg")
        if (!f.renameTo(kopia)) { f.copyTo(kopia, true); f.delete() }
        Toast.makeText(this, "Czytam etykietę...", Toast.LENGTH_SHORT).show()
        watekKamery.execute {
            val bmp = try { wczytajObraz({ kopia.inputStream() }, 2000) } catch (e: Exception) { null }
            if (bmp == null) {
                runOnUiThread { wyborProduktuChem(kopia, kod, "", "") }
                return@execute
            }
            rozpoznawanie.process(InputImage.fromBitmap(bmp, 0))
                .addOnSuccessListener { wynik ->
                    // nazwa: linia pisana największą czcionką (min. 3 litery)
                    val linie = wynik.textBlocks.flatMap { it.lines }
                    val nazwa = linie.filter { l -> l.text.count { it.isLetter() } >= 3 }
                        .maxByOrNull { it.boundingBox?.height() ?: 0 }?.text?.trim() ?: ""
                    wyborProduktuChem(kopia, kod, wynik.text, nazwa)
                }
                .addOnFailureListener { wyborProduktuChem(kopia, kod, "", "") }
        }
    }

    private fun wyborProduktuChem(plik: File, kod: String, tekst: String, nazwa: String) {
        val odczyt = if (tekst.isNotBlank()) odczytEtykiety(tekst) else ""
        val kand = if (tekst.isNotBlank()) dopasujChem(tekst, kod) else emptyList()
        val opcje = mutableListOf<String>()
        val akcje = mutableListOf<() -> Unit>()
        for (k in kand) {
            val jest = listaChem.any { it.id == k.first && it.kod == kod }
            opcje.add(if (kod == "-") "✔ " + k.second else (if (jest) "✔ " else "+ ") + k.second + (if (jest) "  (jest na $kod)" else "  (dopisz do $kod)"))
            akcje.add { zapiszRozpoznaneChem(plik, Triple(k.first, kod, k.second), odczyt) }
        }
        opcje.add("🔎 Wybierz z całego spisu")
        akcje.add { wybierzZeSpisuChem(plik, kod, odczyt) }
        opcje.add("✎ Nowy produkt (nie ma go w spisie)")
        akcje.add { nowyProduktChem(plik, kod, nazwa, odczyt) }
        if (zapisKarty == null) {
            opcje.add("⏳ Do przypisania na komputerze")
            akcje.add { zapiszRozpoznaneChem(plik, Triple(-1, kod, nazwa), odczyt) }
        }
        val karta = zapisKarty != null
        val tyt = when {
            tekst.isBlank() -> "Nie udało się odczytać napisu - wybierz produkt"
            kand.isEmpty() -> "Nie ma go w spisie? Odczytano: ${nazwa.take(40)}"
            else -> "Rozpoznano - wybierz produkt"
        }
        val nrSerii = if (dalejSerii != null && zapisKarty == null) seriaChem.indexOfFirst { it.plik == plik } else -1
        runOnUiThread {
            val b = AlertDialog.Builder(this)
                .setTitle((if (karta) "Karta charakterystyki: " else if (nrSerii >= 0) "Zdjęcie ${nrSerii + 1} z ${seriaChem.size}: " else "") +
                    tyt + if (odczyt.isNotBlank() && !karta) "\n$odczyt" else "")
                .setItems(opcje.toTypedArray()) { _, i -> akcje[i]() }
                .setNegativeButton(if (karta) "Usuń zdjęcia karty" else "Usuń zdjęcie") { _, _ ->
                    if (karta) { zakonczSerie(); Toast.makeText(this, "Zdjęcia karty usunięte", Toast.LENGTH_SHORT).show() }
                    else { plik.delete(); dalejSerii?.invoke() }
                }
                .setCancelable(false)
            if (nrSerii >= 0) {
                val iv = ImageView(this)
                iv.adjustViewBounds = true
                iv.maxHeight = dp(220)
                try { iv.setImageBitmap(wczytajObraz({ plik.inputStream() }, 700)) } catch (e: Exception) {}
                b.setView(iv)
            }
            b.show()
        }
    }

    private fun wybierzZeSpisuChem(plik: File, kod: String, odczyt: String) {
        val wszystkie = listaChem.distinctBy { it.id }.sortedBy { it.nazwa.lowercase() }
        val e = EditText(this)
        e.hint = "Szukaj (fragment nazwy)"
        val lv = ListView(this)
        fun filtruj() {
            val f = normCh(e.text.toString()).trim()
            val l = wszystkie.filter { f.isEmpty() || normCh(it.nazwa).contains(f) }
            lv.adapter = ArrayAdapter(this, android.R.layout.simple_list_item_1, l.map { it.nazwa })
            lv.tag = l
        }
        e.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
            override fun onTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
            override fun afterTextChanged(x: Editable?) = filtruj()
        })
        filtruj()
        val kol = LinearLayout(this)
        kol.orientation = LinearLayout.VERTICAL
        kol.setPadding(dp(12), dp(8), dp(12), 0)
        kol.addView(e)
        kol.addView(lv, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(380)))
        val d = AlertDialog.Builder(this)
            .setTitle("Produkt ze spisu")
            .setView(kol)
            .setNegativeButton("Wróć") { _, _ -> wyborProduktuChem(plik, kod, "", "") }
            .setCancelable(false)
            .create()
        lv.setOnItemClickListener { _, _, i, _ ->
            @Suppress("UNCHECKED_CAST")
            val p = (lv.tag as List<ProdChem>)[i]
            d.dismiss()
            zapiszRozpoznaneChem(plik, Triple(p.id, kod, p.nazwa), odczyt)
        }
        d.show()
    }

    private fun nowyProduktChem(plik: File, kod: String, nazwa: String, odczyt: String) {
        val e = EditText(this)
        e.setText(nazwa)
        e.hint = "Nazwa z etykiety"
        e.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_SENTENCES
        AlertDialog.Builder(this)
            .setTitle("Nowy produkt - wydział $kod")
            .setMessage("Komputer dopisze go od razu do spisu tego wydziału" + if (odczyt.isNotBlank()) " (z etykiety: $odczyt - sprawdzisz w Programie BHP)." else ".")
            .setView(e)
            .setPositiveButton("Zapisz") { _, _ ->
                val n = e.text.toString().trim()
                zapiszRozpoznaneChem(plik, Triple(if (n.isEmpty()) -1 else 0, kod, n), odczyt)
            }
            .setNegativeButton("Wróć") { _, _ -> wyborProduktuChem(plik, kod, "", nazwa) }
            .setCancelable(false)
            .show()
    }

    private fun zapiszRozpoznaneChem(plik: File, cel: Triple<Int, String, String>, odczyt: String) {
        zapisKarty?.let { it(cel); return }
        zapiszZdjecieChem(cel, { plik.inputStream() }, "E", odczyt) { plik.delete() }
        dalejSerii?.let { nSeriiRecz++; it(); return }
        AlertDialog.Builder(this)
            .setTitle("Zapisano: " + cel.third.ifBlank { "do przypisania" })
            .setPositiveButton("Następne zdjęcie") { _, _ -> zdjecieRozpoznaj() }
            .setNegativeButton("Koniec", null)
            .show()
    }

    // ------------------------------------------------------------------
    //  SERIE ZDJĘĆ: substancje (wydział na końcu) i strony karty charakterystyki
    // ------------------------------------------------------------------
    private fun startSeriiSubstancji() {
        zakonczSerie()
        trybSerii = 1
        typZdjeciaChem = "E"
        zrobZdjecieChem()
    }

    // cel = produkt z listy "bez kart"; null = produkt rozpozna z karty
    private fun startSeriiKarty(cel: Triple<Int, String, String>?) {
        zakonczSerie()
        trybSerii = if (cel != null) 2 else 3
        kartaCel = cel
        typZdjeciaChem = "K"
        if (cel != null) Toast.makeText(this, "Karta: ${cel.third} - zrób zdjęcie 1. strony", Toast.LENGTH_LONG).show()
        else Toast.makeText(this, "Zrób zdjęcie 1. strony karty (z nazwą produktu)", Toast.LENGTH_LONG).show()
        zrobZdjecieChem()
    }

    private fun zakonczSerie() {
        for (z in seriaChem) if (!z.zrobione) z.plik.delete()      // zrobione - zapisywane w tle, plik kasuje zapis
        seriaChem.clear()
        trybSerii = 0
        kartaCel = null
        dalejSerii = null
        zapisKarty = null
    }

    private fun dodajDoSerii(f: File) {
        val kopia = File(cacheDir, "seria_${System.currentTimeMillis()}.jpg")
        if (!f.renameTo(kopia)) { f.copyTo(kopia, true); f.delete() }
        val z = ZdjSerii(kopia)
        seriaChem.add(z)
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
        // napis czytany od razu w tle (substancje - każde zdjęcie, karta - pierwsze 2 strony)
        if (trybSerii == 1 || (trybSerii == 3 && seriaChem.size <= 2)) czytajNapis(z) else z.gotowe = true
        pytajSerie()
    }

    private fun czytajNapis(z: ZdjSerii) {
        watekKamery.execute {
            val bmp = try { wczytajObraz({ z.plik.inputStream() }, 2000) } catch (e: Exception) { null }
            if (bmp == null) { z.gotowe = true; return@execute }
            rozpoznawanie.process(InputImage.fromBitmap(bmp, 0))
                .addOnSuccessListener { w ->
                    z.tekst = w.text
                    z.nazwa = w.textBlocks.flatMap { it.lines }.filter { l -> l.text.count { it.isLetter() } >= 3 }
                        .maxByOrNull { it.boundingBox?.height() ?: 0 }?.text?.trim() ?: ""
                    z.gotowe = true
                }
                .addOnFailureListener { z.gotowe = true }
        }
    }

    private fun pytajSerie() {
        val n = seriaChem.size
        val karta = trybSerii != 1
        AlertDialog.Builder(this)
            .setTitle(if (karta) "Karta: zapisano stron $n" else "Zapisano zdjęć: $n")
            .setMessage(if (karta) "Zrób zdjęcie następnej strony albo zakończ." else "Zrób kolejne zdjęcie albo zakończ - wtedy wybierzesz wydział.")
            .setPositiveButton(if (karta) "Następna strona" else "Kolejne zdjęcie") { _, _ -> zrobZdjecieChem() }
            .setNegativeButton("Koniec") { _, _ -> koniecSerii() }
            .setNeutralButton("Usuń ostatnie") { _, _ ->
                seriaChem.removeLastOrNull()?.plik?.delete()
                if (seriaChem.isEmpty()) zakonczSerie() else pytajSerie()
            }
            .setCancelable(false)
            .show()
    }

    private fun koniecSerii() {
        if (seriaChem.isEmpty()) { zakonczSerie(); return }
        when (trybSerii) {
            1 -> wybierzWydzialSerii()
            2 -> kartaCel?.let { zapiszStronyKarty(it) } ?: zakonczSerie()
            else -> rozpoznajKarte()
        }
    }

    private fun wybierzWydzialSerii() {
        // wszystkie wydziały (z komputera); stary spis bez nich - te ze spisu
        val wsz = wszystkieWydzChem.ifEmpty { wydzialyChem.map { Pair(it, "") } }
        val kody = wsz.map { it.first }
        val opisy = wsz.map { if (it.second.isNotBlank()) it.first + "  -  " + it.second else it.first } +
            "✎ inny wydział - wpiszę kod" + "— nie wiem / bez wydziału —"
        AlertDialog.Builder(this)
            .setTitle("Zdjęć: ${seriaChem.size} - z jakiego wydziału?")
            .setItems(opisy.toTypedArray()) { _, i ->
                nSeriiAuto = 0
                nSeriiRecz = 0
                if (i == kody.size) {
                    val e = EditText(this)
                    e.hint = "Kod wydziału, np. DH"
                    e.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_CHARACTERS
                    AlertDialog.Builder(this)
                        .setTitle("Kod wydziału")
                        .setView(e)
                        .setPositiveButton("OK") { _, _ ->
                            val k = e.text.toString().trim()
                            if (k.isEmpty()) wybierzWydzialSerii() else przetworzSerie(k)
                        }
                        .setNegativeButton("Wróć") { _, _ -> wybierzWydzialSerii() }
                        .setCancelable(false)
                        .show()
                } else przetworzSerie(if (i < kody.size) kody[i] else "-")
            }
            .setNegativeButton("Wróć") { _, _ -> pytajSerie() }
            .setCancelable(false)
            .show()
    }

    // po kolei: pewne rozpoznanie zapisuje samo, niepewne - pyta (ze zdjęciem)
    private fun przetworzSerie(kod: String) {
        val z = seriaChem.firstOrNull { !it.zrobione }
        if (z == null) {
            val razem = nSeriiAuto + nSeriiRecz
            zakonczSerie()
            AlertDialog.Builder(this)
                .setTitle("Zapisano: $razem" + if (kod != "-") " (wydział $kod)" else "")
                .setMessage((if (nSeriiAuto > 0) "Rozpoznane same: $nSeriiAuto\n" else "") + (if (nSeriiRecz > 0) "Wybrane ręcznie: $nSeriiRecz\n" else "") +
                    "Komputer zabierze zdjęcia sam, gdy będzie otwarty Program BHP.")
                .setPositiveButton("OK", null)
                .show()
            if (tryb == "CHEMIA") ustawWydzialyChem()
            return
        }
        if (!z.gotowe) {
            Toast.makeText(this, "Czytam etykietę...", Toast.LENGTH_SHORT).show()
            Handler(Looper.getMainLooper()).postDelayed({ przetworzSerie(kod) }, 600)
            return
        }
        val kand = if (z.tekst.isNotBlank()) dopasujChem(z.tekst, kod) else emptyList()
        val odczyt = if (z.tekst.isNotBlank()) odczytEtykiety(z.tekst) else ""
        z.zrobione = true
        val pewny = kand.isNotEmpty() && kand[0].third >= 1.0 && (kand.size < 2 || kand[1].third < 1.0)
        if (pewny) {
            val k = kand[0]
            val f = z.plik
            zapiszZdjecieChem(Triple(k.first, kod, k.second), { f.inputStream() }, "E", odczyt) { f.delete() }
            nSeriiAuto++
            Toast.makeText(this, "✔ " + k.second, Toast.LENGTH_SHORT).show()
            Handler(Looper.getMainLooper()).postDelayed({ przetworzSerie(kod) }, 400)
            return
        }
        dalejSerii = { Handler(Looper.getMainLooper()).postDelayed({ przetworzSerie(kod) }, 300) }
        wyborProduktuChem(z.plik, kod, z.tekst, z.nazwa)
    }

    // karta znanego produktu - wszystkie strony jako jedna seria (komputer złoży je w PDF karty)
    private fun zapiszStronyKarty(cel: Triple<Int, String, String>) {
        val pliki = seriaChem.map { it.plik }.filter { it.exists() }
        val seria = System.currentTimeMillis().toString()
        val n = pliki.size
        seriaChem.clear()
        trybSerii = 0
        zapisKarty = null
        pliki.forEachIndexed { i, f ->
            zapiszZdjecieChem(cel, { f.inputStream() }, "K", "SERIA:$seria STRONA:${i + 1}/$n") { f.delete() }
        }
        AlertDialog.Builder(this)
            .setTitle("Karta zapisana: " + cel.third.ifBlank { "nowy produkt" })
            .setMessage("Stron: $n. Komputer złoży je w jeden plik karty charakterystyki i zapisze w bazie, gdy będzie otwarty Program BHP.")
            .setPositiveButton("OK", null)
            .show()
    }

    // karta bez wskazanego produktu - nazwa z 1. strony karty
    private fun rozpoznajKarte() {
        val gotowe = seriaChem.take(2).all { it.gotowe }
        if (!gotowe) {
            Toast.makeText(this, "Czytam kartę...", Toast.LENGTH_SHORT).show()
            Handler(Looper.getMainLooper()).postDelayed({ rozpoznajKarte() }, 600)
            return
        }
        val tekst = seriaChem.take(2).joinToString("\n") { it.tekst }
        // nazwa produktu: wiersz po "nazwa handlowa" / "identyfikator produktu", inaczej największy napis
        val m = Regex("""(?i)(nazwa handlowa|nazwa produktu|identyfikator produktu|product name)[^\n]*\n?\s*[:.-]?\s*([^\n]{3,60})""").find(tekst)
        val nazwa = m?.groupValues?.get(2)?.trim()?.trimStart(':', '-', ' ') ?: seriaChem.first().nazwa
        val kod = if (trybChem == 1) wydzialChem() else ""
        zapisKarty = { cel -> zapiszStronyKarty(Triple(cel.first, cel.second.ifBlank { "-" }, cel.third)) }
        wyborProduktuChem(seriaChem.first().plik, kod.ifBlank { "-" }, tekst, nazwa)
    }

    // ------------------------------------------------------------------
    //  WYNIKI Z KOMPUTERA (co zrobił ze zdjęciami)
    // ------------------------------------------------------------------
    private fun wynikiChem(): List<String> {
        val f = File(folderChem, "wyniki.txt")
        return if (f.exists()) f.readLines(Charsets.UTF_8).filter { it.isNotBlank() } else emptyList()
    }

    private fun pokazOstatnieWynikiChem() {
        if (!::tWynikiChem.isInitialized) return
        val w = wynikiChem().take(2)
        tWynikiChem.text = if (w.isEmpty()) "" else w.joinToString("\n") + "   (dotknij - więcej)"
        tWynikiChem.visibility = if (w.isEmpty()) View.GONE else View.VISIBLE
    }

    private fun pokazWynikiChem() {
        val w = wynikiChem()
        if (w.isEmpty()) return
        AlertDialog.Builder(this).setTitle("Zapisane w bazie").setMessage(w.take(40).joinToString("\n"))
            .setPositiveButton("Zamknij", null).show()
    }

    // serwer: POST /chemia_wyniki - linie tekstu, najnowsze na górze (zostaje 60)
    override fun chemiaWyniki(tekst: String) {
        val godz = java.text.SimpleDateFormat("HH:mm", java.util.Locale.getDefault()).format(java.util.Date())
        val nowe = tekst.replace("\r", "").split("\n").filter { it.isNotBlank() }.map { "$godz  " + polskie(it.trim()) }
        if (nowe.isEmpty()) return
        val wsz = (nowe + wynikiChem()).take(60)
        try { File(folderChem, "wyniki.txt").writeText(wsz.joinToString("\n"), Charsets.UTF_8) } catch (e: Exception) {}
        runOnUiThread {
            pokazOstatnieWynikiChem()
            if (tryb == "CHEMIA") {
                Toast.makeText(this, "✔ W bazie: " + nowe.first().substringAfter("  "), Toast.LENGTH_LONG).show()
                ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 200)
            }
        }
    }

    // serwer: GET /stan - Program BHP odpytuje w tle i decyduje, co wysłać / zabrać
    //  "STAN|tryb|wersja spisu chemii|zdjęć chemii|wersja listy maszyn|połączeń maszyn|wersja spraw wypadkowych|zdjęć wypadków"
    override fun stan(): String {
        ostatnieTlo = SystemClock.elapsedRealtime()
        runOnUiThread { pokazStan() }
        return "STAN|$tryb|$wersjaListyChem|${zdjeciaChem().size}|$wersjaListyM|${powiazaniaMasz().size}|$wersjaSprawWyp|${plikiZdjec().size}"
    }

    private fun zrobZdjecieChem() {
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            prosbaKameraChem.launch(Manifest.permission.CAMERA)
            return
        }
        try {
            val f = File(cacheDir, "aparat_chemia.jpg")
            if (f.exists()) f.delete()
            plikAparatu = f
            val uri = FileProvider.getUriForFile(this, "$packageName.pliki", f)
            aparatChem.launch(uri)
        } catch (e: Exception) {
            Toast.makeText(this, "Nie udało się otworzyć aparatu: ${e.message}", Toast.LENGTH_LONG).show()
        }
    }

    private fun zapiszZdjecieChem(cel: Triple<Int, String, String>, otworz: () -> java.io.InputStream?, typ: String = "E", odczyt: String = "", potem: () -> Unit) {
        watekKamery.execute {
            var ok = false
            try {
                val bmp = wczytajObraz(otworz, 1800)
                if (bmp != null) {
                    val nr = (zdjeciaChem().maxOfOrNull { it.first } ?: 0) + 1
                    FileOutputStream(File(folderChem, "ch_$nr.jpg")).use { bmp.compress(Bitmap.CompressFormat.JPEG, 85, it) }
                    File(folderChem, "ch_$nr.txt").writeText("${cel.first}|${cel.second}|${cel.third.replace("|", " ")}|$typ|${odczyt.replace("|", " ").replace("\n", " ")}", Charsets.UTF_8)
                    ok = true
                }
            } catch (e: Exception) {
            }
            potem()
            runOnUiThread {
                if (ok) ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
                else Toast.makeText(this, "Nie udało się zapisać zdjęcia", Toast.LENGTH_LONG).show()
                if (tryb == "CHEMIA") ustawWydzialyChem()
            }
        }
    }

    private fun podgladZdjecChem(id: Int, kod: String) {
        val pliki = zdjeciaChem().filter { val o = opisZdjeciaChem(it.first); o.getOrNull(0) == id.toString() && o.getOrNull(1) == kod }
        if (pliki.isEmpty()) return
        val kol = LinearLayout(this)
        kol.orientation = LinearLayout.VERTICAL
        for ((_, f) in pliki) {
            val iv = ImageView(this)
            iv.adjustViewBounds = true
            iv.scaleType = ImageView.ScaleType.FIT_CENTER
            try { iv.setImageBitmap(wczytajObraz({ f.inputStream() }, 1200)) } catch (e: Exception) {}
            val p = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            p.bottomMargin = dp(8)
            kol.addView(iv, p)
        }
        val sv = ScrollView(this)
        sv.addView(kol)
        AlertDialog.Builder(this).setView(sv).setPositiveButton("Zamknij", null).show()
    }

    private fun usunZdjecieChem(nr: Int) {
        File(folderChem, "ch_$nr.jpg").delete()
        File(folderChem, "ch_$nr.txt").delete()
    }

    // serwer: GET /chemia_zdjecia
    override fun chemiaZdjecia(): String {
        val l = zdjeciaChem()
        return "CHZ|" + l.size + l.joinToString("") {
            val o = opisZdjeciaChem(it.first)
            "\n${it.first}|${o.getOrElse(0) { "0" }}|${naKomputer(o.getOrElse(1) { "" })}|${naKomputer(o.getOrElse(2) { "" })}|${o.getOrElse(3) { "E" }}|${naKomputer(o.getOrElse(4) { "" })}"
        }
    }

    // serwer: GET /chemia_zdjecie?nr=N
    override fun chemiaZdjecie(nr: Int): ByteArray? {
        val f = File(folderChem, "ch_$nr.jpg")
        return if (f.exists()) f.readBytes() else null
    }

    // serwer: POST /chemia_odebrane "nr,nr" - komputer zapisał zdjęcia
    override fun chemiaOdebrane(tekst: String) {
        val wysl = wyslaneChem().toMutableSet()
        for (t in tekst.split(",")) {
            val nr = t.trim().toIntOrNull() ?: continue
            val o = opisZdjeciaChem(nr)
            if ((o.getOrNull(0)?.toIntOrNull() ?: 0) > 0) wysl.add("${o[0]}|${o.getOrElse(1) { "" }}")
            usunZdjecieChem(nr)
        }
        try { File(folderChem, "wyslane.txt").writeText(wysl.joinToString("\n"), Charsets.UTF_8) } catch (e: Exception) {}
        runOnUiThread {
            if (tryb == "CHEMIA") {
                ustawWydzialyChem()
                Toast.makeText(this, "✔ Komputer pobrał zdjęcia etykiet", Toast.LENGTH_LONG).show()
                ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 300)
            }
        }
    }

    // ------------------------------------------------------------------
    //  MASZYNY - POMIARY
    //  POST /maszyny: "MSL|data" + linie "Z|idZ|kod|nazwa|typ|nr inw|idM|opis maszyny|poza"
    //                                 i "M|idM|kod|nr inw|nr wewn|nazwa|typ|miejsce"
    //  GET /maszyny_powiazania -> "MSP|n" + linie "idZ|P|idM" / "idZ|R|idM,idM" / "idZ|X|"
    //  POST /maszyny_odebrane "idZ,idZ" - komputer zapisał
    // ------------------------------------------------------------------
    private fun zbudujMaszyny() {
        ekranMasz = LinearLayout(this)
        ekranMasz.orientation = LinearLayout.VERTICAL
        ekranMasz.setPadding(dp(12), dp(12), dp(12), dp(12))
        ekranMasz.setBackgroundColor(Color.rgb(245, 248, 252))
        val grafit = Color.rgb(69, 90, 100)

        val w1 = wiersz()
        w1.addView(przycisk("← Menu", szary) { pokazStart() })
        w1.addView(tekst("  Maszyny - pomiary", 22f, grafit, true), lp(1f))
        w1.addView(przycisk("Zakończ", czerwony) { zakoncz() })
        ekranMasz.addView(w1)
        tKomputerMasz = tekst("", 13f, szary)
        tKomputerMasz.setPadding(0, dp(6), 0, dp(4))
        ekranMasz.addView(tKomputerMasz)

        val w2 = wiersz()
        w2.addView(tekst("Wydział: ", 16f, szary, true))
        spWydzMasz = Spinner(this)
        w2.addView(spWydzMasz, lp(1f))
        bTylkoMasz = przycisk("Do połączenia", pomaranczowy, 13f) {
            wszystkieMasz = !wszystkieMasz
            pokazListeMasz()
        }
        w2.addView(bTylkoMasz, lp(1f, 6))
        ekranMasz.addView(w2)
        spWydzMasz.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(parent: AdapterView<*>?, view: View?, position: Int, id: Long) = pokazListeMasz()
            override fun onNothingSelected(parent: AdapterView<*>?) {}
        }
        tStanMasz = tekst("", 14f, szary, true)
        tStanMasz.gravity = Gravity.CENTER
        tStanMasz.setPadding(0, dp(6), 0, dp(6))
        ekranMasz.addView(tStanMasz)
        val przew = ScrollView(this)
        listaMaszWidok = LinearLayout(this)
        listaMaszWidok.orientation = LinearLayout.VERTICAL
        przew.addView(listaMaszWidok)
        ekranMasz.addView(przew, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))
        wczytajListeMaszZPliku()
    }

    private fun pokazMaszyny() {
        zatrzymajKamere()
        tryb = "MASZYNY"
        setContentView(ekranMasz)
        ustawWydzialyMasz()
        pokazStan()
    }

    private fun wczytajListeMaszZPliku() {
        val f = File(folderMasz, "lista.txt")
        if (f.exists()) try { przetworzListeMasz(f.readText(Charsets.UTF_8)) } catch (e: Exception) {}
    }

    private fun przetworzListeMasz(tekst: String) {
        val linie = tekst.replace("\r", "").split("\n")
        if (linie.isEmpty() || !linie[0].startsWith("MSL|")) return
        val z = mutableListOf<ZrodloM>()
        val m = mutableListOf<MaszynaK>()
        for (l in linie.drop(1)) {
            val p = l.split("|").map { polskie(it.trim()) }
            if (p.size >= 9 && p[0] == "Z") {
                val id = p[1].toIntOrNull() ?: continue
                z.add(ZrodloM(id, p[2], p[3], p[4], p[5], p[6].toIntOrNull() ?: 0, p[7], p[8] == "1"))
            } else if (p.size >= 8 && p[0] == "M") {
                val id = p[1].toIntOrNull() ?: continue
                m.add(MaszynaK(id, p[2], p[3], p[4], p[5], p[6], p[7]))
            }
        }
        zrodlaM = z
        kartotekaM = m
        val nag = linie[0].split("|")
        dataListyM = nag.getOrElse(1) { "" }.trim()
        wersjaListyM = nag.getOrElse(2) { "" }.trim()
    }

    // serwer: POST /maszyny
    override fun maszyny(tekst: String) {
        try { File(folderMasz, "lista.txt").writeText(tekst, Charsets.UTF_8) } catch (e: Exception) {}
        przetworzListeMasz(tekst)
        try { File(folderMasz, "wyslane.txt").delete() } catch (e: Exception) {}
        runOnUiThread {
            if (tryb == "MASZYNY") ustawWydzialyMasz()
            if (tryb == "MASZYNY") Toast.makeText(this, "Lista maszyn z komputera zaktualizowana", Toast.LENGTH_SHORT).show()
        }
    }

    private fun powiazaniaMasz(): MutableMap<Int, Pair<String, String>> {
        val wyn = linkedMapOf<Int, Pair<String, String>>()
        val f = File(folderMasz, "powiazania.txt")
        if (f.exists()) for (l in f.readLines(Charsets.UTF_8)) {
            val p = l.split("|")
            val id = p.getOrNull(0)?.toIntOrNull() ?: continue
            wyn[id] = Pair(p.getOrElse(1) { "" }, p.getOrElse(2) { "" })
        }
        return wyn
    }

    private fun zapiszPowiazaniaMasz(m: Map<Int, Pair<String, String>>) {
        try {
            File(folderMasz, "powiazania.txt").writeText(m.entries.joinToString("\n") { "${it.key}|${it.value.first}|${it.value.second}" }, Charsets.UTF_8)
        } catch (e: Exception) {
        }
    }

    private fun wyslaneMasz(): Set<Int> {
        val f = File(folderMasz, "wyslane.txt")
        return if (f.exists()) f.readLines(Charsets.UTF_8).mapNotNull { it.trim().toIntOrNull() }.toSet() else emptySet()
    }

    private fun ustawWydzialyMasz() {
        val stary = spWydzMasz.selectedItem?.toString()
        val pow = powiazaniaMasz()
        val wysl = wyslaneMasz()
        wydzialyMasz = zrodlaM.map { it.kod }.distinct().sorted()
        val opisy = wydzialyMasz.map { k ->
            val n = zrodlaM.count { it.kod == k && it.idM == 0 && !it.poza && !pow.containsKey(it.id) && !wysl.contains(it.id) }
            if (n > 0) "$k  ($n do połączenia)" else k
        }
        spWydzMasz.adapter = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, opisy)
        val i = if (stary != null) opisy.indexOfFirst { it.substringBefore(" ") == stary.substringBefore(" ") } else -1
        if (i >= 0) spWydzMasz.setSelection(i)
        pokazListeMasz()
    }

    private fun wydzialMasz(): String {
        val i = spWydzMasz.selectedItemPosition
        return if (i in wydzialyMasz.indices) wydzialyMasz[i] else ""
    }

    private fun opisMaszyny(m: MaszynaK): String =
        listOf(m.nrInw, if (m.nrWewn.isNotBlank()) "nr ${m.nrWewn}" else "", m.nazwa, m.typ).filter { it.isNotBlank() }.joinToString("  ·  ")

    private fun pokazListeMasz() {
        if (!::listaMaszWidok.isInitialized) return
        listaMaszWidok.removeAllViews()
        bTylkoMasz.text = if (wszystkieMasz) "Pokaż: wszystkie" else "Pokaż: do połączenia"
        val kod = wydzialMasz()
        val pow = powiazaniaMasz()
        val wysl = wyslaneMasz()
        val lista = zrodlaM.filter { it.kod == kod && (wszystkieMasz || (it.idM == 0 && !it.poza && !wysl.contains(it.id))) }
            .sortedWith(compareBy({ it.idM != 0 || it.poza }, { it.nazwa.lowercase() }, { it.typ.lowercase() }))
        tStanMasz.text = when {
            zrodlaM.isEmpty() -> "Najpierw w komputerze: Maszyny w pomiarach -> \"Lista na telefon\""
            lista.isEmpty() -> "Na tym wydziale wszystko połączone" + if (pow.isNotEmpty()) "   |   przypisań do wysłania: ${pow.size}" else ""
            else -> "Dotknij maszyny z pomiarów = wskaż ją w kartotece" + if (pow.isNotEmpty()) "   |   do wysłania: ${pow.size}" else ""
        }
        tStanMasz.setTextColor(if (pow.isNotEmpty()) pomaranczowy else szary)
        for (z in lista) {
            val p = pow[z.id]
            val ramka = LinearLayout(this)
            ramka.orientation = LinearLayout.VERTICAL
            ramka.setPadding(dp(10), dp(8), dp(10), dp(8))
            val tlo = GradientDrawable()
            tlo.cornerRadius = dp(8).toFloat()
            tlo.setColor(Color.WHITE)
            tlo.setStroke(dp(2), when {
                p != null -> zielony
                wysl.contains(z.id) -> niebieski
                z.idM == 0 && !z.poza -> pomaranczowy
                else -> Color.rgb(207, 216, 220)
            })
            ramka.background = tlo
            ramka.addView(tekst(listOf(z.nazwa, z.typ).filter { it.isNotBlank() }.joinToString("  "), 16f, Color.rgb(38, 50, 56), true))
            if (z.nrInw.isNotBlank()) ramka.addView(tekst("nr inw. ze starego spisu: ${z.nrInw}", 13f, szary))
            val stan = when {
                p != null -> when (p.first) {
                    "X" -> "→ to nie maszyna z kartoteki (czeka na komputer)"
                    else -> "→ " + p.second.split(",").mapNotNull { s -> kartotekaM.firstOrNull { it.id == s.toIntOrNull() } }
                        .joinToString("; ") { opisMaszyny(it) } + "  (czeka na komputer)"
                }
                wysl.contains(z.id) -> "✔ wysłane do komputera"
                z.poza -> "nie maszyna z kartoteki"
                z.idM != 0 -> "✔ w kartotece: ${z.opisM}"
                else -> "DO POŁĄCZENIA - wskaż maszynę (nr inw. z tabliczki albo z listy)"
            }
            ramka.addView(tekst(stan, 13f, if (p != null) zielony else if (z.idM == 0 && !z.poza && !wysl.contains(z.id)) pomaranczowy else szary, true))
            ramka.setOnClickListener { menuZrodlaMasz(z) }
            val lpR = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            lpR.topMargin = dp(6)
            listaMaszWidok.addView(ramka, lpR)
        }
    }

    private fun menuZrodlaMasz(z: ZrodloM) {
        val pow = powiazaniaMasz()
        val opcje = mutableListOf("Wpisz nr inwentarzowy z tabliczki", "Wybierz z listy maszyn (jedną albo kilka)", "To nie maszyna z kartoteki")
        if (pow.containsKey(z.id)) opcje.add("Usuń przypisanie z telefonu")
        AlertDialog.Builder(this)
            .setTitle(listOf(z.nazwa, z.typ).filter { it.isNotBlank() }.joinToString("  "))
            .setItems(opcje.toTypedArray()) { _, k ->
                when (k) {
                    0 -> wpiszNrMasz(z)
                    1 -> wybierzZListyMasz(z, "")
                    2 -> przypiszMasz(z, "X", "")
                    else -> {
                        pow.remove(z.id)
                        zapiszPowiazaniaMasz(pow)
                        ustawWydzialyMasz()
                    }
                }
            }
            .setNegativeButton("Zamknij", null)
            .show()
    }

    // 517104 (stary nr) -> 5017104 (kartoteka);  porównanie bez spacji, kresek i kropek
    private fun normNr(s: String): String {
        var n = s.filter { it.isLetterOrDigit() }.uppercase()
        if (n.length == 6 && n.startsWith("51")) n = "50" + n.substring(1)
        return n
    }

    private fun wpiszNrMasz(z: ZrodloM) {
        val e = EditText(this)
        e.hint = "np. 5017104 albo 517104"
        e.inputType = InputType.TYPE_CLASS_TEXT or InputType.TYPE_TEXT_FLAG_CAP_CHARACTERS
        AlertDialog.Builder(this)
            .setTitle("Nr inwentarzowy z tabliczki")
            .setMessage("Szuka w numerach inwentarzowych i wewnętrznych całej kartoteki.")
            .setView(e)
            .setPositiveButton("Szukaj") { _, _ ->
                val nr = normNr(e.text.toString())
                if (nr.isEmpty()) return@setPositiveButton
                val trafione = kartotekaM.filter { normNr(it.nrInw) == nr || normNr(it.nrWewn) == nr }
                when (trafione.size) {
                    0 -> {
                        Toast.makeText(this, "Nie ma maszyny o numerze $nr - wybierz z listy", Toast.LENGTH_LONG).show()
                        wybierzZListyMasz(z, e.text.toString().trim())
                    }
                    1 -> {
                        val m = trafione[0]
                        AlertDialog.Builder(this)
                            .setTitle("Przypisać tę maszynę?")
                            .setMessage(opisMaszyny(m) + (if (m.kod.isNotBlank()) "\nwydział: ${m.kod}" else "") + (if (m.miejsce.isNotBlank()) "\n${m.miejsce}" else ""))
                            .setPositiveButton("Tak") { _, _ -> przypiszMasz(z, "P", m.id.toString()) }
                            .setNegativeButton("Nie", null)
                            .show()
                    }
                    else -> wybierzZListyMasz(z, e.text.toString().trim())
                }
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    // lista kartoteki: najpierw wydział maszyny z pomiarów; szukanie po nazwie / numerach (wtedy cała kartoteka)
    private fun wybierzZListyMasz(z: ZrodloM, szukaj: String) {
        val kol = LinearLayout(this)
        kol.orientation = LinearLayout.VERTICAL
        kol.setPadding(dp(12), dp(6), dp(12), 0)
        val e = EditText(this)
        e.hint = "Szukaj: nazwa, nr inw., nr wewn."
        e.setText(szukaj)
        kol.addView(e)
        val lv = ListView(this)
        lv.choiceMode = ListView.CHOICE_MODE_MULTIPLE
        kol.addView(lv, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(420)))
        var widoczne: List<MaszynaK> = emptyList()
        val zaznaczone = mutableSetOf<Int>()
        fun odswiez() {
            val s = e.text.toString().trim().lowercase()
            val sn = normNr(s)
            widoczne = (if (s.isEmpty()) kartotekaM.filter { it.kod == z.kod } else kartotekaM.filter {
                it.nazwa.lowercase().contains(s) || it.typ.lowercase().contains(s) ||
                        (sn.isNotEmpty() && (normNr(it.nrInw).contains(sn) || normNr(it.nrWewn) == sn))
            }).sortedWith(compareBy({ it.kod != z.kod }, { it.nazwa.lowercase() }, { it.nrWewn }))
            lv.adapter = ArrayAdapter(this, android.R.layout.simple_list_item_multiple_choice,
                widoczne.map { opisMaszyny(it) + if (it.kod != z.kod && it.kod.isNotBlank()) "  [${it.kod}]" else "" })
            for (i in widoczne.indices) lv.setItemChecked(i, zaznaczone.contains(widoczne[i].id))
        }
        lv.setOnItemClickListener { _, _, pos, _ ->
            val id = widoczne[pos].id
            if (lv.isItemChecked(pos)) zaznaczone.add(id) else zaznaczone.remove(id)
        }
        e.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
            override fun onTextChanged(a: CharSequence?, b: Int, c: Int, d: Int) {}
            override fun afterTextChanged(x: Editable?) = odswiez()
        })
        odswiez()
        AlertDialog.Builder(this)
            .setTitle("Maszyna z kartoteki dla: " + listOf(z.nazwa, z.typ).filter { it.isNotBlank() }.joinToString(" "))
            .setView(kol)
            .setPositiveButton("Przypisz zaznaczone") { _, _ ->
                when (zaznaczone.size) {
                    0 -> Toast.makeText(this, "Nic nie zaznaczono", Toast.LENGTH_SHORT).show()
                    1 -> przypiszMasz(z, "P", zaznaczone.first().toString())
                    else -> AlertDialog.Builder(this)
                        .setTitle("Rozbić na ${zaznaczone.size} maszyn?")
                        .setMessage("To jedno źródło z pomiarów (np. \"Plecionkarka nr 51-60\") zostanie zastąpione ${zaznaczone.size} maszynami z kartoteki w tych samych grupach pomiarowych.")
                        .setPositiveButton("Tak") { _, _ -> przypiszMasz(z, "R", zaznaczone.joinToString(",")) }
                        .setNegativeButton("Nie", null)
                        .show()
                }
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    private fun przypiszMasz(z: ZrodloM, akcja: String, ids: String) {
        val pow = powiazaniaMasz()
        pow[z.id] = Pair(akcja, ids)
        zapiszPowiazaniaMasz(pow)
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
        ustawWydzialyMasz()
    }

    // serwer: GET /maszyny_powiazania
    override fun maszynyPowiazania(): String {
        val pow = powiazaniaMasz()
        return "MSP|" + pow.size + pow.entries.joinToString("") { "\n${it.key}|${it.value.first}|${it.value.second}" }
    }

    // serwer: POST /maszyny_odebrane "idZ,idZ"
    override fun maszynyOdebrane(tekst: String) {
        val pow = powiazaniaMasz()
        val wysl = wyslaneMasz().toMutableSet()
        for (t in tekst.split(",")) {
            val id = t.trim().toIntOrNull() ?: continue
            pow.remove(id)
            wysl.add(id)
        }
        zapiszPowiazaniaMasz(pow)
        try { File(folderMasz, "wyslane.txt").writeText(wysl.joinToString("\n"), Charsets.UTF_8) } catch (e: Exception) {}
        runOnUiThread {
            if (tryb == "MASZYNY") {
                ustawWydzialyMasz()
                Toast.makeText(this, "✔ Komputer zapisał połączenia maszyn", Toast.LENGTH_LONG).show()
                ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 300)
            }
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
            if (!uzbrojony) return                   // jak w Wydaniu: kod tylko po naciśnięciu SKANUJ
            val kod = kody.firstOrNull { it.format != Barcode.FORMAT_QR_CODE && !it.rawValue.isNullOrEmpty() }?.rawValue ?: return
            ustawSkanuj(false)                        // jeden kod na jedno naciśnięcie
            kodWKadrze = kod
            ostatnioWidziany = SystemClock.elapsedRealtime()
            ostatnioWyslany = ostatnioWidziany
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
        for (b in listOfNotNull(if (::bSkanuj.isInitialized) bSkanuj else null, if (::bSkanujMag.isInitialized) bSkanujMag else null)) {
            val tlo = GradientDrawable()
            tlo.cornerRadius = dp(10).toFloat()
            tlo.setColor(if (tak) pomaranczowy else niebieski)
            b.background = tlo
            b.text = if (tak) "SKANUJĘ... (dotknij = stop)" else "SKANUJ"
        }
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
        w1.addView(przycisk("\u2190 Odzież", szary) { pokazOdziez() })
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

        tPozycja = tekst("Naciśnij SKANUJ i skieruj aparat na kod kartonu", 20f, szary, true)
        tPozycja.gravity = Gravity.CENTER
        tPozycja.setPadding(0, dp(8), 0, 0)
        ekranMag.addView(tPozycja)
        tStanProg = tekst("", 15f, szary)
        tStanProg.gravity = Gravity.CENTER
        ekranMag.addView(tStanProg)

        bSkanujMag = przycisk("SKANUJ", niebieski, 22f) { ustawSkanuj(!uzbrojony) }
        val lpSk = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(60))
        lpSk.topMargin = dp(6)
        ekranMag.addView(bSkanujMag, lpSk)

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
        ustawSkanuj(false)
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
            tPozycja.text = "Naciśnij SKANUJ i skieruj aparat na kod kartonu"
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
