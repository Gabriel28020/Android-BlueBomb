# Android BlueBomb
Recently, I noticed that the Wii exploit "BlueBomb" had a minor inconvenience. Anyone who wanted to use it needed to install Linux on a PC. That is a huge pain. Setting up virtual machines, Bluetooth drivers, creating a bootable USB drive, etc.

While daydreaming, I thought: "Android is Linux. Could I make BlueBomb work on Android?" I decided to create a native solution and, with some help from ChatGPT to accelerate the development, I successfully ported the BlueBomb logic from Linux to Android. (It worked VERY well.)

## Attention
Android, although open, has a strict restriction regarding Bluetooth. The operating system fully controls the internal Bluetooth of your phone, which consequently restricts what Bluetooth can and cannot do. Because of this, it cannot natively connect to the Wii or send the required payload packets.

### Solution and Requirements
You will need:

1- An OTG Cable / Adapter (An adapter that connects to your phone's charging port and provides a USB port);

2- A USB Bluetooth Adapter.

The reason is that Android does not have control over these external USB adapters.

## How to use?
First, install the APK normally. (There is no secret: download, install, run.)

Connect your adapter and open the app.

Inside, you will see a large Start button. Click it.

This first launch only serves to identify the adapter and request permission to use it.

Once it says "USB permission granted.", close the app completely and open it again.

Now, configure your Wii's information above and press the button again.

A window will appear telling you to press the sync button on your Nintendo Wii, and then tap "`START SYNC`".

Do exactly that. If everything goes well, it will display "`Wii connected.`" (If it says "`Still waiting for the Wii.`", press the Wii's `SYNC` button one more time.)

Just wait.

The button will turn green and BlueBomb will execute.

## FAQ & Troubleshooting

### **"Every time I start, the same message appears: "`No compatible USB Bluetooth dongle was found`". Why?"**
Usually, there are two main causes:
* 1- Your OTG cable is of poor quality / weak.
* 2- Your Bluetooth adapter is of poor quality / too old.
*(I own one Bluetooth adapter and two OTG cables. My adapter's LED lit up on both cables, but on one of them (the older one), it refused to be detected. Therefore, just because the adapter lights up does not mean it is fully working.)*


### **"My adapter couldn't connect to the Wii. (`Connection failed.`) What could it be?"**
It could be a lot of things.
What you can do:
* Disconnect and reconnect the adapter;
* Move closer to the Wii;
* Swap the OTG cable or the adapter;
* Check if Bluetooth is actually working properly (both on the Wii and on your adapter).

## Compile

### Prerequisites
* Java Development Kit (JDK) 17 (The path to Java 17 must be defined under "JAVA_HOME" in your Environment Variables);
* Android SDK (API 35 and Build-Tools) (Can be found and installed via Android Studio).

**Compile Debug**
*(The debug version is completely in Portuguese, as it was built solely for diagnostics (and it is my native language)):*

```Windows
.\gradlew.bat clean
.\gradlew.bat --no-daemon assembleDebug
```

**Compile Release**
*(The APK must be signed later)*

```Windows
.\gradlew.bat clean
.\gradlew.bat --no-daemon assembleRelease
```

## 🏆 Credits & Special Thanks

* **[Fullmetal5](https://github.com/Fullmetal5/bluebomb/)** - Creator of Linux BlueBomb
* **[Gabriel28020](https://github.com/Gabriel28020)** - Tool Developer (Me)
* (ChatGPT 5.5)

---
☕ **Support my work:** If this tool helped you, consider buying me a coffee on **[Ko-fi](https://ko-fi.com/gab280)**!
