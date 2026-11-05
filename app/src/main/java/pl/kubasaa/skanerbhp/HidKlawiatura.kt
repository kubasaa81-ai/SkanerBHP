package pl.kubasaa.skanerbhp

import android.annotation.SuppressLint
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothDevice
import android.bluetooth.BluetoothHidDevice
import android.bluetooth.BluetoothHidDeviceAppSdpSettings
import android.bluetooth.BluetoothManager
import android.bluetooth.BluetoothProfile
import android.content.Context
import java.util.concurrent.Executors

/**
 * Telefon jako klawiatura Bluetooth (profil HID).
 * Komputer widzi zwykłą klawiaturę - nic nie trzeba na nim instalować.
 * Wysyła cyfry / litery kodu i Enter do okna, które ma kursor (pole "Skan kodu" w Programie BHP).
 */
@SuppressLint("MissingPermission")
class HidKlawiatura(private val ctx: Context, private val zmiana: () -> Unit) {

    private val adapter: BluetoothAdapter? =
        (ctx.getSystemService(Context.BLUETOOTH_SERVICE) as BluetoothManager).adapter
    private var hid: BluetoothHidDevice? = null
    private val watekBt = Executors.newSingleThreadExecutor()
    private val watekWysylki = Executors.newSingleThreadExecutor()

    @Volatile var zarejestrowany = false
        private set
    @Volatile var polaczony: BluetoothDevice? = null
        private set
    @Volatile var blad: String? = null
        private set

    /** komputer, z którym ma się łączyć (wybrany na liście sparowanych) */
    var cel: BluetoothDevice? = null

    private val callback = object : BluetoothHidDevice.Callback() {
        override fun onAppStatusChanged(pluggedDevice: BluetoothDevice?, registered: Boolean) {
            zarejestrowany = registered
            if (registered) {
                blad = null
                polacz()
            } else {
                polaczony = null
                blad = "Tryb klawiatury wyłączony - otwórz aplikację jeszcze raz"
            }
            zmiana()
        }

        override fun onConnectionStateChanged(device: BluetoothDevice, state: Int) {
            if (state == BluetoothProfile.STATE_CONNECTED) {
                polaczony = device
            } else if (state == BluetoothProfile.STATE_DISCONNECTED && device == polaczony) {
                polaczony = null
            }
            zmiana()
        }
    }

    private val sluchacz = object : BluetoothProfile.ServiceListener {
        override fun onServiceConnected(profile: Int, proxy: BluetoothProfile) {
            if (profile != BluetoothProfile.HID_DEVICE) return
            val h = proxy as BluetoothHidDevice
            hid = h
            val sdp = BluetoothHidDeviceAppSdpSettings(
                "Skaner BHP", "Skaner kodów - Program BHP", "Program BHP",
                BluetoothHidDevice.SUBCLASS1_KEYBOARD, DESKRYPTOR
            )
            val ok = try {
                h.registerApp(sdp, null, null, watekBt, callback)
            } catch (e: Exception) {
                false
            }
            if (!ok) {
                blad = "Nie mogę włączyć trybu klawiatury. Zamknij inne aplikacje klawiatury Bluetooth " +
                        "(np. Bluetooth Keyboard & Mouse) i otwórz Skaner jeszcze raz."
                zmiana()
            }
        }

        override fun onServiceDisconnected(profile: Int) {
            hid = null
            zarejestrowany = false
            polaczony = null
            zmiana()
        }
    }

    fun start() {
        val a = adapter
        if (a == null) {
            blad = "Ten telefon nie ma Bluetooth"
            zmiana()
            return
        }
        if (!a.isEnabled) {
            blad = "Włącz Bluetooth w telefonie i otwórz aplikację jeszcze raz"
            zmiana()
            return
        }
        val ok = a.getProfileProxy(ctx.applicationContext, sluchacz, BluetoothProfile.HID_DEVICE)
        if (!ok) {
            blad = "Ten telefon nie obsługuje trybu klawiatury Bluetooth"
            zmiana()
        }
    }

    fun sparowane(): List<BluetoothDevice> {
        val a = adapter ?: return emptyList()
        return try {
            a.bondedDevices?.sortedBy { it.name ?: it.address } ?: emptyList()
        } catch (e: SecurityException) {
            emptyList()
        }
    }

    fun polacz() {
        val h = hid ?: return
        val d = cel ?: return
        if (!zarejestrowany) return
        try {
            val stary = polaczony
            if (stary != null && stary != d) h.disconnect(stary)
            if (polaczony != d) h.connect(d)
        } catch (e: Exception) {
            blad = "Błąd łączenia: ${e.message}"
            zmiana()
        }
    }

    /** wysyła tekst jako naciśnięcia klawiszy; false = brak połączenia z komputerem */
    fun wyslij(tekst: String, enter: Boolean): Boolean {
        val h = hid ?: return false
        val d = polaczony ?: return false
        watekWysylki.execute {
            try {
                for (c in tekst) {
                    val k = klawisz(c) ?: continue
                    nacisnij(h, d, k.first, k.second)
                }
                if (enter) nacisnij(h, d, 0, 0x28)
            } catch (e: Exception) {
                blad = "Błąd wysyłania: ${e.message}"
                zmiana()
            }
        }
        return true
    }

    private fun nacisnij(h: BluetoothHidDevice, d: BluetoothDevice, mod: Int, kod: Int) {
        val r = ByteArray(8)
        r[0] = mod.toByte()
        r[2] = kod.toByte()
        h.sendReport(d, 1, r)
        Thread.sleep(15)
        h.sendReport(d, 1, ByteArray(8))
        Thread.sleep(15)
    }

    /** znak -> (modyfikator, kod klawisza USB HID) */
    private fun klawisz(c: Char): Pair<Int, Int>? = when (c) {
        in '1'..'9' -> Pair(0, 0x1E + (c - '1'))
        '0' -> Pair(0, 0x27)
        in 'a'..'z' -> Pair(0, 0x04 + (c - 'a'))
        in 'A'..'Z' -> Pair(0x02, 0x04 + (c - 'A'))
        '-' -> Pair(0, 0x2D)
        '.' -> Pair(0, 0x37)
        ' ' -> Pair(0, 0x2C)
        else -> null
    }

    fun stop() {
        try {
            hid?.unregisterApp()
        } catch (e: Exception) {
        }
        try {
            adapter?.closeProfileProxy(BluetoothProfile.HID_DEVICE, hid)
        } catch (e: Exception) {
        }
        watekWysylki.shutdown()
        watekBt.shutdown()
    }

    companion object {
        /** deskryptor zwykłej klawiatury (raport nr 1: modyfikatory, zarezerwowany, 6 klawiszy) */
        private val DESKRYPTOR: ByteArray = intArrayOf(
            0x05, 0x01,       // Usage Page (Generic Desktop)
            0x09, 0x06,       // Usage (Keyboard)
            0xA1, 0x01,       // Collection (Application)
            0x85, 0x01,       //   Report ID (1)
            0x05, 0x07,       //   Usage Page (Key Codes)
            0x19, 0xE0,       //   Usage Minimum (224)
            0x29, 0xE7,       //   Usage Maximum (231)
            0x15, 0x00,       //   Logical Minimum (0)
            0x25, 0x01,       //   Logical Maximum (1)
            0x75, 0x01,       //   Report Size (1)
            0x95, 0x08,       //   Report Count (8)
            0x81, 0x02,       //   Input (Data, Variable, Absolute) - modyfikatory
            0x95, 0x01,       //   Report Count (1)
            0x75, 0x08,       //   Report Size (8)
            0x81, 0x01,       //   Input (Constant) - bajt zarezerwowany
            0x95, 0x05,       //   Report Count (5)
            0x75, 0x01,       //   Report Size (1)
            0x05, 0x08,       //   Usage Page (LEDs)
            0x19, 0x01,       //   Usage Minimum (1)
            0x29, 0x05,       //   Usage Maximum (5)
            0x91, 0x02,       //   Output (Data, Variable, Absolute) - diody
            0x95, 0x01,       //   Report Count (1)
            0x75, 0x03,       //   Report Size (3)
            0x91, 0x01,       //   Output (Constant)
            0x95, 0x06,       //   Report Count (6)
            0x75, 0x08,       //   Report Size (8)
            0x15, 0x00,       //   Logical Minimum (0)
            0x25, 0x65,       //   Logical Maximum (101)
            0x05, 0x07,       //   Usage Page (Key Codes)
            0x19, 0x00,       //   Usage Minimum (0)
            0x29, 0x65,       //   Usage Maximum (101)
            0x81, 0x00,       //   Input (Data, Array) - klawisze
            0xC0              // End Collection
        ).map { it.toByte() }.toByteArray()
    }
}
