package pl.kubasaa.skanerbhp

import android.Manifest
import android.annotation.SuppressLint
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothDevice
import android.content.Intent
import android.content.pm.PackageManager
import android.graphics.Color
import android.graphics.Typeface
import android.graphics.drawable.GradientDrawable
import android.media.AudioManager
import android.media.ToneGenerator
import android.os.Build
import android.os.Bundle
import android.os.SystemClock
import android.text.InputType
import android.util.TypedValue
import android.view.Gravity
import android.view.HapticFeedbackConstants
import android.view.View
import android.view.WindowManager
import android.widget.AdapterView
import android.widget.ArrayAdapter
import android.widget.Button
import android.widget.CheckBox
import android.widget.EditText
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.Spinner
import android.widget.TextView
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
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors

/**
 * Skaner BHP - aparat czyta kod kreskowy, telefon wpisuje go w komputerze jak klawiatura Bluetooth (+ Enter).
 * Kod trafia do okna, które ma kursor: w Programie BHP pole "Skan kodu" (Wydanie / Magazyn).
 * Lista "co wydać": kod QR z okna Wydanie (przycisk "Lista na telefon") - aparat sam ją wczytuje,
 * a każdy skan odhacza pozycję i od razu ostrzega (inny rozmiar, nie z listy, ponad listę).
 */
class MainActivity : AppCompatActivity() {

    private val zielony = Color.rgb(46, 125, 50)
    private val czerwony = Color.rgb(198, 40, 40)
    private val pomaranczowy = Color.rgb(230, 81, 0)
    private val szary = Color.rgb(96, 125, 139)

    private lateinit var tStatus: TextView
    private lateinit var spKomputer: Spinner
    private lateinit var podglad: PreviewView
    private lateinit var tKod: TextView
    private lateinit var tHistoria: TextView
    private lateinit var tWynik: TextView
    private lateinit var listaWidok: LinearLayout
    private lateinit var listaPrzewijanie: ScrollView
    private lateinit var eReczny: EditText
    private lateinit var cbEnter: CheckBox
    private lateinit var bLatarka: Button

    private var klawiatura: HidKlawiatura? = null
    private var urzadzenia: List<BluetoothDevice> = emptyList()
    private val historia = ArrayDeque<String>()
    private var kamera: Camera? = null
    private var latarka = false
    private lateinit var watekKamery: ExecutorService
    private var skaner: BarcodeScanner? = null
    private var ton: ToneGenerator? = null
    private var wypelniaListe = false

    // ten sam kod nie wysyła się drugi raz, dopóki nie zniknie z kadru
    private var kodWKadrze: String? = null
    private var ostatnioWidziany = 0L
    private var ostatnioWyslany = 0L
    private var ostatniWyslanyKod: String? = null

    // lista do wydania (z kodu QR)
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
    private val cofanie = ArrayDeque<Int>()          // numer pozycji (-1 = spoza listy) dla każdego skanu

    private val prosba = registerForActivityResult(ActivityResultContracts.RequestMultiplePermissions()) {
        uruchom()
    }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        watekKamery = Executors.newSingleThreadExecutor()
        zbudujWidok()
        ton = try {
            ToneGenerator(AudioManager.STREAM_NOTIFICATION, 90)
        } catch (e: Exception) {
            null
        }
        prosba.launch(potrzebneUprawnienia())
    }

    private fun potrzebneUprawnienia(): Array<String> {
        val l = mutableListOf(Manifest.permission.CAMERA)
        if (Build.VERSION.SDK_INT >= 31) {
            l.add(Manifest.permission.BLUETOOTH_CONNECT)
            l.add(Manifest.permission.BLUETOOTH_ADVERTISE)
        }
        return l.toTypedArray()
    }

    private fun ma(p: String) = ContextCompat.checkSelfPermission(this, p) == PackageManager.PERMISSION_GRANTED

    private fun maBluetooth() = Build.VERSION.SDK_INT < 31 || ma(Manifest.permission.BLUETOOTH_CONNECT)

    private fun uruchom() {
        if (ma(Manifest.permission.CAMERA)) {
            uruchomKamere()
        } else {
            tKod.text = "Brak zgody na aparat"
            tKod.setTextColor(czerwony)
        }
        if (!maBluetooth()) {
            status("Brak zgody na Bluetooth (Urządzenia w pobliżu) - nadaj w ustawieniach aplikacji", czerwony)
            return
        }
        if (klawiatura == null) {
            val k = HidKlawiatura(this) { runOnUiThread { pokazStatus() } }
            klawiatura = k
            wczytajUrzadzenia()
            k.start()
        }
        pokazStatus()
    }

    // ------------------------------------------------------------------
    //  WIDOK (budowany w kodzie)
    // ------------------------------------------------------------------
    private fun dp(v: Int) = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, v.toFloat(), resources.displayMetrics).toInt()

    private fun przycisk(tekst: String, kolor: Int, akcja: () -> Unit): Button {
        val b = Button(this)
        b.text = tekst
        b.isAllCaps = false
        b.setTextColor(Color.WHITE)
        b.textSize = 15f
        val tlo = GradientDrawable()
        tlo.cornerRadius = dp(8).toFloat()
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

    private fun zbudujWidok() {
        val glowny = LinearLayout(this)
        glowny.orientation = LinearLayout.VERTICAL
        glowny.setPadding(dp(12), dp(12), dp(12), dp(12))
        glowny.setBackgroundColor(Color.rgb(245, 248, 252))

        val tytul = TextView(this)
        tytul.text = "Skaner BHP"
        tytul.textSize = 22f
        tytul.setTypeface(null, Typeface.BOLD)
        tytul.setTextColor(Color.rgb(0, 105, 92))
        glowny.addView(tytul)

        tStatus = TextView(this)
        tStatus.textSize = 15f
        tStatus.setTypeface(null, Typeface.BOLD)
        tStatus.setPadding(0, dp(4), 0, dp(6))
        glowny.addView(tStatus)

        val w1 = wiersz()
        val etykieta = TextView(this)
        etykieta.text = "Komputer:"
        etykieta.textSize = 15f
        w1.addView(etykieta)
        spKomputer = Spinner(this)
        w1.addView(spKomputer, lp(1f, 6))
        w1.addView(przycisk("Połącz", Color.rgb(21, 101, 192)) { polacz() }, lp(0.5f, 6))
        glowny.addView(w1)

        val w2 = wiersz()
        w2.setPadding(0, dp(6), 0, dp(6))
        w2.addView(przycisk("Parowanie", Color.rgb(0, 131, 143)) { widocznyDoParowania() }, lp(1f))
        bLatarka = przycisk("Latarka", Color.rgb(121, 85, 72)) { przelaczLatarke() }
        w2.addView(bLatarka, lp(1f, 6))
        glowny.addView(w2)

        podglad = PreviewView(this)
        podglad.scaleType = PreviewView.ScaleType.FILL_CENTER
        val pp = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f)
        glowny.addView(podglad, pp)

        tKod = TextView(this)
        tKod.text = "Skieruj aparat na kod kreskowy"
        tKod.textSize = 26f
        tKod.setTypeface(null, Typeface.BOLD)
        tKod.gravity = Gravity.CENTER
        tKod.setTextColor(szary)
        tKod.setPadding(0, dp(8), 0, dp(4))
        glowny.addView(tKod)

        tWynik = TextView(this)
        tWynik.textSize = 15f
        tWynik.setTypeface(null, Typeface.BOLD)
        tWynik.gravity = Gravity.CENTER
        tWynik.setPadding(0, 0, 0, dp(4))
        glowny.addView(tWynik)

        val w3 = wiersz()
        w3.addView(przycisk("+1 ten sam", Color.rgb(46, 125, 50)) { ponowTenSam() }, lp(1f))
        w3.addView(przycisk("Cofnij", Color.rgb(121, 85, 72)) { cofnij() }, lp(1f, 6))
        w3.addView(przycisk("Wyczyść listę", Color.rgb(96, 125, 139)) { wyczyscListe() }, lp(1.2f, 6))
        glowny.addView(w3)

        listaPrzewijanie = ScrollView(this)
        listaWidok = LinearLayout(this)
        listaWidok.orientation = LinearLayout.VERTICAL
        listaWidok.setPadding(0, dp(6), 0, dp(6))
        listaPrzewijanie.addView(listaWidok)
        glowny.addView(listaPrzewijanie, LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, 0, 1f))

        val w4 = wiersz()
        w4.setPadding(0, dp(6), 0, dp(4))
        cbEnter = CheckBox(this)
        cbEnter.text = "Enter"
        cbEnter.isChecked = true
        w4.addView(cbEnter)
        eReczny = EditText(this)
        eReczny.hint = "kod ręcznie"
        eReczny.inputType = InputType.TYPE_CLASS_NUMBER
        w4.addView(eReczny, lp(1f))
        w4.addView(przycisk("Wyślij", Color.rgb(106, 27, 154)) { wyslijRecznie() }, lp(0.6f, 6))
        glowny.addView(w4)

        tHistoria = TextView(this)
        tHistoria.textSize = 13f
        tHistoria.setTextColor(Color.rgb(55, 71, 79))
        tHistoria.maxLines = 3
        glowny.addView(tHistoria)

        setContentView(glowny)
        pokazListe()
        status("Uruchamianie ...", szary)
    }

    private fun status(tekst: String, kolor: Int) {
        tStatus.text = tekst
        tStatus.setTextColor(kolor)
    }

    @SuppressLint("MissingPermission")
    private fun nazwa(d: BluetoothDevice?): String {
        if (d == null) return "-"
        return try {
            d.name ?: d.address
        } catch (e: SecurityException) {
            d.address
        }
    }

    private fun pokazStatus() {
        val k = klawiatura
        when {
            k == null -> status("Bluetooth nieaktywny", czerwony)
            k.polaczony != null -> status("Połączono z: ${nazwa(k.polaczony)} - gotowy do skanowania", zielony)
            k.blad != null -> status(k.blad ?: "", czerwony)
            !k.zarejestrowany -> status("Włączanie trybu klawiatury ...", pomaranczowy)
            k.cel == null -> status("Wybierz komputer z listy i kliknij Połącz", pomaranczowy)
            else -> status("Nie połączono - komputer włączony i Bluetooth włączony? Kliknij Połącz.", czerwony)
        }
    }

    // ------------------------------------------------------------------
    //  BLUETOOTH
    // ------------------------------------------------------------------
    private fun wczytajUrzadzenia() {
        val k = klawiatura ?: return
        urzadzenia = k.sparowane()
        val nazwy = urzadzenia.map { nazwa(it) }.ifEmpty { listOf("(brak sparowanych - kliknij Parowanie)") }
        val ad = ArrayAdapter(this, android.R.layout.simple_spinner_dropdown_item, nazwy)
        wypelniaListe = true
        spKomputer.adapter = ad
        val zapisany = getSharedPreferences("skaner", MODE_PRIVATE).getString("komputer", null)
        val idx = urzadzenia.indexOfFirst { it.address == zapisany }
        if (idx >= 0) {
            spKomputer.setSelection(idx)
            k.cel = urzadzenia[idx]
        }
        spKomputer.onItemSelectedListener = object : AdapterView.OnItemSelectedListener {
            override fun onItemSelected(parent: AdapterView<*>?, view: View?, position: Int, id: Long) {
                if (wypelniaListe) {
                    wypelniaListe = false
                    return
                }
                if (position < urzadzenia.size) {
                    val d = urzadzenia[position]
                    getSharedPreferences("skaner", MODE_PRIVATE).edit().putString("komputer", d.address).apply()
                    klawiatura?.cel = d
                    klawiatura?.polacz()
                    pokazStatus()
                }
            }

            override fun onNothingSelected(parent: AdapterView<*>?) {}
        }
    }

    private fun polacz() {
        val k = klawiatura ?: return
        wczytajUrzadzenia()
        val pos = spKomputer.selectedItemPosition
        if (pos >= 0 && pos < urzadzenia.size) {
            val d = urzadzenia[pos]
            getSharedPreferences("skaner", MODE_PRIVATE).edit().putString("komputer", d.address).apply()
            k.cel = d
        }
        k.polacz()
        status("Łączenie z ${nazwa(k.cel)} ...", pomaranczowy)
    }

    @SuppressLint("MissingPermission")
    private fun widocznyDoParowania() {
        if (Build.VERSION.SDK_INT >= 31 && !ma(Manifest.permission.BLUETOOTH_ADVERTISE)) {
            prosba.launch(potrzebneUprawnienia())
            return
        }
        val i = Intent(BluetoothAdapter.ACTION_REQUEST_DISCOVERABLE)
        i.putExtra(BluetoothAdapter.EXTRA_DISCOVERABLE_DURATION, 120)
        try {
            startActivity(i)
            status("Telefon widoczny 2 min - na komputerze: Ustawienia > Bluetooth > Dodaj urządzenie", pomaranczowy)
        } catch (e: Exception) {
            status("Nie udało się włączyć widoczności: ${e.message}", czerwony)
        }
    }

    // ------------------------------------------------------------------
    //  APARAT + ODCZYT KODÓW
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
        // kod QR z listą z komputera - wczytaj, nie wysyłaj
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
        if (kod == kodWKadrze) return               // ten sam karton dalej w kadrze
        if (teraz - ostatnioWyslany < 800) return
        kodWKadrze = kod
        wyslij(kod)
    }

    private fun wyslij(kod: String) {
        ostatnioWyslany = SystemClock.elapsedRealtime()
        ostatniWyslanyKod = kod
        val ok = klawiatura?.wyslij(kod, cbEnter.isChecked) == true
        tKod.text = kod
        if (ok) {
            tKod.setTextColor(zielony)
            ton?.startTone(ToneGenerator.TONE_PROP_BEEP, 150)
            dodajHistorie("✔ $kod")
            sprawdzNaLiscie(kod)
        } else {
            tKod.setTextColor(czerwony)
            ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 400)
            dodajHistorie("✖ $kod - NIE wysłano (brak połączenia)")
            status("Brak połączenia z komputerem - kod NIE wysłany. Kliknij Połącz.", czerwony)
        }
        podglad.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
    }

    // ------------------------------------------------------------------
    //  LISTA DO WYDANIA (QR z okna Wydanie)
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
            val linie = tekst.split("\n")
            for (l in linie.drop(1)) {
                if (l.isBlank()) continue
                val p = l.split("|")
                if (p.size < 5) continue
                val warianty = p[3].split(",").map { polskie(it.trim()) }
                val wpisy = HashMap<String, Wpis>()
                for (w in p[4].split(";")) {
                    val r = w.indexOf('=')
                    val kropka = w.lastIndexOf('.')
                    if (r <= 0 || kropka < r) continue
                    val klucz = w.substring(0, r)
                    val rozm = polskie(w.substring(r + 1, kropka))
                    val nrW = w.substring(kropka + 1).toIntOrNull() ?: 0
                    wpisy[klucz] = Wpis(rozm, nrW)
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
        podglad.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
        tKod.text = "Lista: ${lista.size} poz."
        tKod.setTextColor(Color.rgb(21, 101, 192))
        tWynik.text = "Idź do magazynu i skanuj kartony"
        tWynik.setTextColor(szary)
        pokazListe()
    }

    /** klucze, pod jakimi kod może być na liście */
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
        if (lista.isEmpty()) {
            tWynik.text = ""
            return
        }
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
            tWynik.text = "\u2716 Nie z listy (inny rozmiar?) - sprawdź na komputerze"
            tWynik.setTextColor(czerwony)
            ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 400)
            return
        }
        val p = lista[nr]
        p.skany.add(wpis)
        cofanie.addLast(nr)
        val nazwaW = if (p.warianty.size > 1 && wpis.wariant < p.warianty.size) p.warianty[wpis.wariant] + " " else ""
        val innyRozmiar = p.rozmiar.isNotBlank() && wpis.rozmiar != "-" && !wpis.rozmiar.equals(p.rozmiar, ignoreCase = true)
        when {
            innyRozmiar -> {
                p.uwaga = true
                tWynik.text = "UWAGA: ${p.nazwa} rozm. ${wpis.rozmiar} - na liście rozm. ${p.rozmiar}"
                tWynik.setTextColor(pomaranczowy)
                ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 300)
            }
            p.skany.size > p.ilosc -> {
                p.uwaga = true
                tWynik.text = "UWAGA: ${p.nazwa} ponad listę (ma być ${p.ilosc})"
                tWynik.setTextColor(pomaranczowy)
                ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 300)
            }
            else -> {
                tWynik.text = "\u2714 ${p.nazwa}: $nazwaW${wpis.rozmiar}  (${p.skany.size}/${p.ilosc})"
                tWynik.setTextColor(zielony)
            }
        }
        pokazListe()
    }

    private fun pokazListe() {
        listaWidok.removeAllViews()
        if (lista.isEmpty()) {
            val t = TextView(this)
            t.text = "Lista do wydania: w Programie BHP (Wydanie) kliknij \"Lista na telefon\" i skieruj aparat na kod QR."
            t.textSize = 14f
            t.setTextColor(szary)
            listaWidok.addView(t)
            return
        }
        var gotowe = 0
        for (p in lista) {
            val t = TextView(this)
            val komplet = p.skany.size >= p.ilosc
            if (komplet) gotowe++
            val znak = if (komplet) "\u2714" else "\u2610"
            val roz = if (p.rozmiar.isNotBlank() && p.rozmiar != "-") "rozm. ${p.rozmiar}" else if (p.rozmiar == "-") "" else "rozm. ?"
            val sb = StringBuilder("$znak ${p.nazwa}  $roz   ${p.skany.size}/${p.ilosc}")
            if (p.skany.isNotEmpty()) {
                sb.append("\n      ")
                sb.append(p.skany.joinToString(", ") { w ->
                    (if (p.warianty.size > 1 && w.wariant < p.warianty.size) p.warianty[w.wariant] + " " else "") + w.rozmiar
                })
            }
            t.text = sb.toString()
            t.textSize = 16f
            t.setPadding(dp(4), dp(5), dp(4), dp(5))
            t.setTypeface(null, if (komplet) Typeface.BOLD else Typeface.NORMAL)
            t.setTextColor(
                when {
                    p.uwaga -> pomaranczowy
                    komplet -> zielony
                    else -> Color.rgb(38, 50, 56)
                }
            )
            listaWidok.addView(t)
        }
        val s = TextView(this)
        s.text = "Gotowe: $gotowe z ${lista.size}"
        s.textSize = 14f
        s.setTypeface(null, Typeface.BOLD)
        s.setTextColor(if (gotowe == lista.size) zielony else szary)
        s.setPadding(dp(4), dp(6), dp(4), 0)
        listaWidok.addView(s)
    }

    private fun cofnij() {
        val ok = klawiatura?.wyslij("-", true) == true
        if (!ok) {
            status("Brak połączenia z komputerem - nie cofnięto. Kliknij Połącz.", czerwony)
            return
        }
        val nr = cofanie.removeLastOrNull()
        if (nr != null && nr >= 0 && nr < lista.size) {
            val p = lista[nr]
            if (p.skany.isNotEmpty()) p.skany.removeAt(p.skany.size - 1)
            p.uwaga = false
        }
        tWynik.text = "Cofnięto ostatni skan (też w komputerze)"
        tWynik.setTextColor(szary)
        dodajHistorie("\u21B6 cofnięto")
        pokazListe()
    }

    private fun wyczyscListe() {
        lista.clear()
        cofanie.clear()
        listaTekst = null
        tWynik.text = ""
        pokazListe()
    }

    private fun ponowTenSam() {
        val k = ostatniWyslanyKod
        if (k == null) {
            status("Najpierw zeskanuj kod", pomaranczowy)
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

    private fun dodajHistorie(s: String) {
        historia.addFirst(s)
        while (historia.size > 5) historia.removeLast()
        tHistoria.text = historia.joinToString("\n")
    }

    private fun przelaczLatarke() {
        val k = kamera ?: return
        latarka = !latarka
        k.cameraControl.enableTorch(latarka)
        bLatarka.text = if (latarka) "Latarka: wł." else "Latarka"
    }

    override fun onResume() {
        super.onResume()
        if (klawiatura != null) pokazStatus()
    }

    override fun onDestroy() {
        super.onDestroy()
        klawiatura?.stop()
        klawiatura = null
        watekKamery.shutdown()
        skaner?.close()
        ton?.release()
    }
}
