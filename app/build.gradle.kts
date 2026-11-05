plugins {
    id("com.android.application")
    id("org.jetbrains.kotlin.android")
}

val numer = (System.getenv("GITHUB_RUN_NUMBER") ?: "1").toInt()

android {
    namespace = "pl.kubasaa.skanerbhp"
    compileSdk = 34

    defaultConfig {
        applicationId = "pl.kubasaa.skanerbhp"
        minSdk = 28
        targetSdk = 34
        versionCode = numer
        versionName = "1.$numer"
    }

    // stały klucz - każda nowa wersja instaluje się na starą (bez odinstalowania)
    signingConfigs {
        create("wlasny") {
            storeFile = file("klucz.jks")
            storePassword = "skanerbhp"
            keyAlias = "skaner"
            keyPassword = "skanerbhp"
        }
    }

    buildTypes {
        getByName("debug") {
            signingConfig = signingConfigs.getByName("wlasny")
        }
        getByName("release") {
            isMinifyEnabled = false
            signingConfig = signingConfigs.getByName("wlasny")
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_17
        targetCompatibility = JavaVersion.VERSION_17
    }
    kotlinOptions {
        jvmTarget = "17"
    }
}

dependencies {
    implementation("androidx.core:core-ktx:1.13.1")
    implementation("androidx.appcompat:appcompat:1.7.0")
    implementation("androidx.camera:camera-camera2:1.3.4")
    implementation("androidx.camera:camera-lifecycle:1.3.4")
    implementation("androidx.camera:camera-view:1.3.4")
    implementation("com.google.mlkit:barcode-scanning:17.3.0")
}
