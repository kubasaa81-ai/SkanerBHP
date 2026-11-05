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
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.text.InputType
import android.util.TypedValue
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.View
import android.view.WindowManager
import android.widget.Button
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
 * Ekran startowy: Wydanie / Dostawa / Inwentura / Zakończ.
 * Wydanie: komputer wysyła listę "co wydać", aparat czyta kody, komputer pobiera skany i odsyła wynik.
 */
class MainActivity : AppCompatActivity(), Serwer.Obsluga {

    private val zielony = Color.rgb(46, 125, 50)
    private val czerwony = Color.rgb(198, 40, 40)
    private val pomaranczowy = Color.rgb(230, 81, 0)
    private val szary = Color.rgb(96, 125, 139)
    private val niebieski = Color.rgb(21, 101, 192)

    private lateinit var ekranStart: LinearLayout
    private lateinit var ekranWydanie: LinearLayout
    private var naWydaniu = false

    // start
    private lateinit var tSiec: TextView
    private lateinit var tKomputerStart: TextView
    private lateinit var bVpn: Button

    // wydanie
    private lateinit var tKomputer: TextView
    private lateinit var podglad: PreviewView
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

    // ten sam kod nie wysyła się drugi raz, dopóki nie zniknie z kadru
    private var kodWKadrze: String? = null
    private var ostatnioWidziany = 0L
    private var ostatnioWyslany = 0L
    private var ostatniWyslanyKod: String? = null

    // lista do wydania
    private class Wpis(val rozmiar: String, val wariant: Int)
    private class Pozycja(
        val nazwa: String, val ilosc: Int, val rozmiar: String,
        val warianty: List<String>, val wpisy: Map<String, Wpis>
    ) {
        val skany = mutableListOf<Wpis>()
        var uwaga = false
    }
    private val lista = mutableListOf<Pozycja>()
    private var listaTekst: String? = null
    private val cofanie = ArrayDeque<Int>()

    private val prosbaKamera = registerForActivityResult(ActivityResultContracts.RequestPermission()) { ok ->
        if (ok) uruchomKamere() else {
            tKod.text = "Brak zgody na aparat"
            tKod.setTextColor(czerwony)
        }
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
        pokazStart()
        val blad = serwer.start(8080)
        if (blad != null) Toast.makeText(this, "Serwer: $blad", Toast.LENGTH_LONG).show()
        onBackPressedDispatcher.addCallback(this) {
            if (naWydaniu) pokazStart() else moveTaskToBack(true)
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
        ekranStart.addView(tekst("Odzież i ŚOI - Program BHP", 15f, szary))

        tSiec = tekst("", 15f, szary, true)
        tSiec.setPadding(0, dp(16), 0, 0)
        ekranStart.addView(tSiec)
        tKomputerStart = tekst("", 14f, szary)
        tKomputerStart.setPadding(0, dp(4), 0, dp(8))
        ekranStart.addView(tKomputerStart)

        bVpn = przycisk("Włącz GlobalProtect", niebieski, 17f) { otworzGlobalProtect() }
        ekranStart.addView(bVpn, lpPelny(4))

        ekranStart.addView(przycisk("Wydanie", Color.rgb(46, 125, 50), 22f) { pokazWydanie() }, lpPelny(18))
        ekranStart.addView(przycisk("Dostawa", Color.rgb(93, 64, 55), 22f) {
            Toast.makeText(this, "Dostawa - w następnym kroku", Toast.LENGTH_SHORT).show()
        }, lpPelny(12))
        ekranStart.addView(przycisk("Inwentura", Color.rgb(2, 119, 189), 22f) {
            Toast.makeText(this, "Inwentura - w następnym kroku", Toast.LENGTH_SHORT).show()
        }, lpPelny(12))

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

        podglad = PreviewView(this)
        podglad.scaleType = PreviewView.ScaleType.FILL_CENTER
        ekranWydanie.addView(podglad, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        tKod = tekst("Skieruj aparat na kod kreskowy", 24f, szary, true)
        tKod.gravity = Gravity.CENTER
        tKod.setPadding(0, dp(6), 0, dp(2))
        ekranWydanie.addView(tKod)

        tWynik = tekst("", 15f, szary, true)
        tWynik.gravity = Gravity.CENTER
        tWynik.setPadding(0, 0, 0, dp(4))
        ekranWydanie.addView(tWynik)

        val w3 = wiersz()
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
        naWydaniu = false
        zatrzymajKamere()
        setContentView(ekranStart)
        pokazStan()
    }

    private fun pokazWydanie() {
        naWydaniu = true
        setContentView(ekranWydanie)
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            uruchomKamere()
        } else {
            prosbaKamera.launch(Manifest.permission.CAMERA)
        }
        pokazStan()
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
    override fun ping(): String = "SKANER_BHP|" + (if (naWydaniu) "WYDANIE" else "MENU")

    override fun komputer(adres: String) {
        ostatniKontakt = SystemClock.elapsedRealtime()
        adresKomputera = adres
    }

    override fun lista(tekst: String) {
        synchronized(skany) {
            skany.clear()
            nastepnyNr = 1
        }
        runOnUiThread {
            if (!naWydaniu) pokazWydanie()
            wczytajListe(tekst)
        }
    }

    override fun skany(od: Int): String {
        synchronized(skany) {
            return skany.filter { it.nr >= od }.joinToString("\n") { "${it.nr}|${it.kod}" }
        }
    }

    override fun wynik(tekst: String) {
        val p = tekst.split("|", limit = 3)
        if (p.size < 3) return
        val kolor = when (p[1]) {
            "1" -> zielony
            "2" -> czerwony
            "3" -> pomaranczowy
            else -> szary
        }
        runOnUiThread {
            tWynik.text = "Komputer: " + p[2]
            tWynik.setTextColor(kolor)
            if (p[1] == "2" || p[1] == "3") ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 300)
        }
    }

    override fun koniec(tekst: String) {
        runOnUiThread {
            lista.clear()
            cofanie.clear()
            listaTekst = null
            pokazListe()
            tKod.text = "Wydano ✔"
            tKod.setTextColor(zielony)
            tWynik.text = if (tekst.isNotBlank()) tekst else "Wydanie zapisane w komputerze"
            tWynik.setTextColor(zielony)
            ton?.startTone(ToneGenerator.TONE_PROP_BEEP2, 300)
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
                if (!naWydaniu) return@addListener
                val preview = Preview.Builder().build()
                preview.setSurfaceProvider(podglad.surfaceProvider)
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
        if (!naWydaniu) return
        // QR z listą (zapasowo, gdy nie ma sieci)
        val qr = kody.firstOrNull { it.format == Barcode.FORMAT_QR_CODE && (it.rawValue ?: "").startsWith("BHP1") }
        if (qr != null) {
            val t = qr.rawValue ?: return
            if (t != listaTekst) wczytajListe(t)
            return
        }
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
        wyslij(kod)
    }

    private fun wyslij(kod: String) {
        ostatnioWyslany = SystemClock.elapsedRealtime()
        if (kod != "-") ostatniWyslanyKod = kod
        synchronized(skany) {
            skany.add(Skan(nastepnyNr, kod))
            nastepnyNr++
            while (skany.size > 500) skany.removeAt(0)
        }
        if (kod == "-") return
        tKod.text = kod
        tKod.setTextColor(niebieski)
        ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 120)
        podglad.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
        if (!komputerWidziany()) {
            tWynik.text = "Komputer nie odbiera - kod czeka. Otwórz Wydanie i kliknij \"Lista na telefon\"."
            tWynik.setTextColor(czerwony)
        }
        sprawdzNaLiscie(kod)
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
        if (nr != null && nr >= 0 && nr < lista.size) {
            val p = lista[nr]
            if (p.skany.isNotEmpty()) p.skany.removeAt(p.skany.size - 1)
            p.uwaga = false
        }
        tWynik.text = "Cofnięto ostatni skan (też w komputerze)"
        tWynik.setTextColor(szary)
        pokazListe()
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

    private fun sprawdzNaLiscie(kod: String) {
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
            cofanie.addLast(-1)
            if (komputerWidziany()) {
                tWynik.text = "Nie z listy (inny rozmiar?) - czekam na komputer"
                tWynik.setTextColor(pomaranczowy)
            }
            return
        }
        val p = lista[nr]
        p.skany.add(wpis)
        cofanie.addLast(nr)
        val innyRozmiar = p.rozmiar.isNotBlank() && p.rozmiar != "-" && wpis.rozmiar != "-" &&
                !wpis.rozmiar.equals(p.rozmiar, ignoreCase = true)
        if (innyRozmiar || p.skany.size > p.ilosc) p.uwaga = true
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
                sb.append(p.skany.joinToString(", ") { w ->
                    (if (p.warianty.size > 1 && w.wariant < p.warianty.size) p.warianty[w.wariant] + " " else "") + w.rozmiar
                })
            }
            val t = tekst(sb.toString(), 16f,
                when {
                    p.uwaga -> pomaranczowy
                    komplet -> zielony
                    else -> Color.rgb(38, 50, 56)
                }, komplet)
            t.setPadding(dp(4), dp(5), dp(4), dp(5))
            listaWidok.addView(t)
        }
        val s = tekst("Gotowe: $gotowe z ${lista.size}", 14f, if (gotowe == lista.size) zielony else szary, true)
        s.setPadding(dp(4), dp(6), dp(4), 0)
        listaWidok.addView(s)
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
