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

        val w3 = wiersz()
        w3.addView(przycisk("+1 ten sam kod", Color.rgb(46, 125, 50)) { ponowTenSam() }, lp(1f))
        cbEnter = CheckBox(this)
        cbEnter.text = "Enter po kodzie"
        cbEnter.isChecked = true
        w3.addView(cbEnter, lp(1f, 10))
        glowny.addView(w3)

        val w4 = wiersz()
        w4.setPadding(0, dp(6), 0, dp(4))
        eReczny = EditText(this)
        eReczny.hint = "kod ręcznie"
        eReczny.inputType = InputType.TYPE_CLASS_NUMBER
        w4.addView(eReczny, lp(1f))
        w4.addView(przycisk("Wyślij", Color.rgb(106, 27, 154)) { wyslijRecznie() }, lp(0.6f, 6))
        glowny.addView(w4)

        tHistoria = TextView(this)
        tHistoria.textSize = 13f
        tHistoria.setTextColor(Color.rgb(55, 71, 79))
        tHistoria.maxLines = 5
        glowny.addView(tHistoria)

        setContentView(glowny)
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
                    Barcode.FORMAT_UPC_E, Barcode.FORMAT_CODE_128, Barcode.FORMAT_CODE_39
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
        val teraz = SystemClock.elapsedRealtime()
        val kod = kody.firstOrNull { !it.rawValue.isNullOrEmpty() }?.rawValue
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
        } else {
            tKod.setTextColor(czerwony)
            ton?.startTone(ToneGenerator.TONE_SUP_ERROR, 400)
            dodajHistorie("✖ $kod - NIE wysłano (brak połączenia)")
            status("Brak połączenia z komputerem - kod NIE wysłany. Kliknij Połącz.", czerwony)
        }
        podglad.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
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
