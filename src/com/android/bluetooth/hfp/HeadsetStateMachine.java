/*
 * Copyright (C) 2012 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * Bluetooth Handset StateMachine
 *                      (Disconnected)
 *                           |    ^
 *                   CONNECT |    | DISCONNECTED
 *                           V    |
 *                         (Pending)
 *                           |    ^
 *                 CONNECTED |    | CONNECT
 *                           V    |
 *                        (Connected)
 *                           |    ^
 *             CONNECT_AUDIO |    | DISCONNECT_AUDIO
 *                           V    |
 *                         (AudioOn)
 */
package com.android.bluetooth.hfp;

import android.bluetooth.BluetoothA2dp;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothAssignedNumbers;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothHeadset;
import android.bluetooth.BluetoothProfile;
import android.bluetooth.BluetoothUuid;
import android.bluetooth.IBluetoothHeadsetPhone;
import android.content.ComponentName;
import android.content.Context;
import android.content.Intent;
import android.content.ServiceConnection;
import android.content.ActivityNotFoundException;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.media.AudioManager;
import android.net.Uri;
import android.os.IBinder;
import android.os.IDeviceIdleController;
import android.os.Message;
import android.os.ParcelUuid;
import android.os.RemoteException;
import android.os.ServiceManager;
import android.os.SystemProperties;
import android.os.PowerManager;
import android.os.UserHandle;
import android.os.PowerManager.WakeLock;
import android.telephony.PhoneNumberUtils;
import android.util.Log;
import com.android.bluetooth.Utils;
import com.android.bluetooth.btservice.AdapterService;
import com.android.bluetooth.btservice.ProfileService;
import com.android.internal.util.IState;
import com.android.internal.util.State;
import com.android.internal.util.StateMachine;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import android.os.SystemProperties;
import java.util.concurrent.ConcurrentLinkedQueue;
import android.telecom.TelecomManager;

import android.media.AudioFormat;
import android.media.AudioManager;
import android.media.AudioTrack;
import android.os.Process;

import java.lang.InterruptedException;
import java.lang.Math;
import java.lang.Runnable;

final class HeadsetStateMachine extends StateMachine {
    private static final String TAG = "HeadsetStateMachine";
    private static final boolean DBG = Log.isLoggable("Handsfree", Log.VERBOSE);
    // For Debugging only
    private static int sRefCount = 0;

    private static final String HEADSET_NAME = "bt_headset_name";
    private static final String HEADSET_NREC = "bt_headset_nrec";
    private static final String HEADSET_WBS = "bt_wbs";

    private static String BT_SOC;

    static final int CONNECT = 1;
    static final int DISCONNECT = 2;
    static final int CONNECT_AUDIO = 3;
    static final int DISCONNECT_AUDIO = 4;
    static final int VOICE_RECOGNITION_START = 5;
    static final int VOICE_RECOGNITION_STOP = 6;

    // message.obj is an intent AudioManager.VOLUME_CHANGED_ACTION
    // EXTRA_VOLUME_STREAM_TYPE is STREAM_BLUETOOTH_SCO
    static final int INTENT_SCO_VOLUME_CHANGED = 7;
    static final int SET_MIC_VOLUME = 8;
    static final int CALL_STATE_CHANGED = 9;
    static final int INTENT_BATTERY_CHANGED = 10;
    static final int DEVICE_STATE_CHANGED = 11;
    static final int SEND_CCLC_RESPONSE = 12;
    static final int SEND_VENDOR_SPECIFIC_RESULT_CODE = 13;

    static final int VIRTUAL_CALL_START = 14;
    static final int VIRTUAL_CALL_STOP = 15;

    static final int ENABLE_WBS = 16;
    static final int DISABLE_WBS = 17;

    static final int BIND_RESPONSE = 18;
    static final int UPDATE_A2DP_PLAY_STATE = 19;
    static final int UPDATE_A2DP_CONN_STATE = 20;
    static final int QUERY_PHONE_STATE_AT_SLC = 21;
    static final int UPDATE_CALL_TYPE = 22;
    static final int SEND_INCOMING_CALL_IND = 23;
    static final int AUDIO_SERVER_RESTARTED = 24;

    static final int VOIP_CALL_STATE_CHANGED_ALERTING = 51;
    static final int VOIP_CALL_STATE_CHANGED_ACTIVE = 52;

    static final int CS_CALL_STATE_CHANGED_ALERTING = 61;
    static final int CS_CALL_STATE_CHANGED_ACTIVE = 62;

    private static final int CS_CALL_ALERTING_DELAY_TIME_MSEC = 800;
    private static final int CS_CALL_ACTIVE_DELAY_TIME_MSEC = 10;


    private static final int STACK_EVENT = 101;
    private static final int DIALING_OUT_TIMEOUT = 102;
    private static final int START_VR_TIMEOUT = 103;
    private static final int CLCC_RSP_TIMEOUT = 104;
    private static final int PROCESS_CPBR = 105;

    private static final int CONNECT_TIMEOUT = 201;
    /* Allow time for possible LMP response timeout + Page timeout */
    private static final int CONNECT_TIMEOUT_SEC = 38000;
    /* Retry outgoing connection after this time if the first attempt fails */
    private static final int RETRY_CONNECT_TIME_SEC = 2500;

    /* Delay between call dialling, alerting updates for VOIP call */
    private static final int VOIP_CALL_ALERTING_DELAY_TIME_MSEC = 800;
    /* Delay between call alerting, active updates for VOIP call */
    private static final int VOIP_CALL_ACTIVE_DELAY_TIME_MSEC =
                               VOIP_CALL_ALERTING_DELAY_TIME_MSEC + 50;

    private static final int DIALING_OUT_TIMEOUT_VALUE = 10000;
    private static final int START_VR_TIMEOUT_VALUE = 5000;
    private static final int CLCC_RSP_TIMEOUT_VALUE = 5000;
    private static final int QUERY_PHONE_STATE_CHANGED_DELAYED = 100;
    private static final int INCOMING_CALL_IND_DELAY = 200;
    // Blacklist remote device addresses to send incoimg call indicators with delay of 200ms
    private static final String [] BlacklistDeviceAddrToDelayCallInd =
                                                               {"00:15:83", /* Beiqi CK */
                                                                "2a:eb:00", /* BIAC CK */
                                                                "30:53:00", /* BIAC series */
                                                                "00:17:53", /* ADAYO CK */
                                                                "40:ef:4c", /* Road Rover CK */
                                                               };
    // Blacklist remote device addresses going into bad state if we retry
    private static final String [] BlacklistDeviceAddrForNotRetrying =
                                                              {"A0:14:3D"};  /* Honda HFT */
    private static final int CONNECT_TIMEOUT_MILLIS = 30000;

    // Max number of HF connections at any time
    private int max_hf_connections = 1;

    private static final int NBS_CODEC = 1;
    private static final int WBS_CODEC = 2;

    private static final String VOIP_CALL_NUMBER = "10000000";

    // Keys are AT commands, and values are the company IDs.
    private static final Map<String, Integer> VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID;
    // Hash for storing the Audio Parameters like NREC for connected headsets
    private HashMap<BluetoothDevice, HashMap> mHeadsetAudioParam =
            new HashMap<BluetoothDevice, HashMap>();
    // Hash for storing the Remotedevice BRSF
    private HashMap<BluetoothDevice, Integer> mHeadsetBrsf =
            new HashMap<BluetoothDevice, Integer>();

    // Hash for storing the connection retry attempts from application
    private HashMap<BluetoothDevice, Integer> mRetryConnect =
                                            new HashMap<BluetoothDevice, Integer>();
    // Hash for storing the A2DP connection states
    private HashMap<BluetoothDevice, Integer> mA2dpConnState =
                                          new HashMap<BluetoothDevice, Integer>();
    // Hash for storing the A2DP play states
    private HashMap<BluetoothDevice, Integer> mA2dpPlayState =
                                          new HashMap<BluetoothDevice, Integer>();

    private static final ParcelUuid[] HEADSET_UUIDS = {
            BluetoothUuid.HSP, BluetoothUuid.Handsfree,
    };

    private Disconnected mDisconnected;
    private Pending mPending;
    private Connected mConnected;
    private AudioOn mAudioOn;
    // Multi HFP: add new class object
    private MultiHFPending mMultiHFPending;

    private HeadsetService mService;
    private PowerManager mPowerManager;
    private boolean mVirtualCallStarted = false;
    private boolean mVoiceRecognitionStarted = false;
    private boolean mWaitingForVoiceRecognition = false;
    private WakeLock mStartVoiceRecognitionWakeLock; // held while waiting for voice recognition

    private ConnectivityManager mConnectivityManager;
    private boolean mDialingOut = false;
    private AudioManager mAudioManager;
    private AtPhonebook mPhonebook;

    private static Intent sVoiceCommandIntent;

    private HeadsetPhoneState mPhoneState;
    private int mAudioState;
    private BluetoothAdapter mAdapter;
    private IBluetoothHeadsetPhone mPhoneProxy;
    private boolean mNativeAvailable;

    private boolean mA2dpSuspend;
    private boolean mPendingCiev;
    private boolean mIsCsCall = true;
    private boolean mPendingScoForVR = false;
    //ConcurrentLinkeQueue is used so that it is threadsafe
    private ConcurrentLinkedQueue<HeadsetCallState> mPendingCallStates = new ConcurrentLinkedQueue<HeadsetCallState>();

    private ConcurrentLinkedQueue<HeadsetCallState> mDelayedCSCallStates =
                             new ConcurrentLinkedQueue<HeadsetCallState>();

    // Indicates whether audio can be routed to the device.
    private boolean mAudioRouteAllowed = true;

    // Indicates whether SCO audio needs to be forced to open regardless ANY OTHER restrictions
    private boolean mForceScoAudio = false;

    private boolean mIsCallIndDelay = false;

    private boolean mIsBlacklistedDevice = false;

    private AudioPlayer mAudioPlayer = null;

    private boolean mPlaybackForVR = false;

    private boolean mPlaybackForVOIP = false;

    // mCurrentDevice is the device connected before the state changes
    // mTargetDevice is the device to be connected
    // mIncomingDevice is the device connecting to us, valid only in Pending state
    //                when mIncomingDevice is not null, both mCurrentDevice
    //                  and mTargetDevice are null
    //                when either mCurrentDevice or mTargetDevice is not null,
    //                  mIncomingDevice is null
    // Stable states
    //   No connection, Disconnected state
    //                  both mCurrentDevice and mTargetDevice are null
    //   Connected, Connected state
    //              mCurrentDevice is not null, mTargetDevice is null
    // Interim states
    //   Connecting to a device, Pending
    //                           mCurrentDevice is null, mTargetDevice is not null
    //   Disconnecting device, Connecting to new device
    //     Pending
    //     Both mCurrentDevice and mTargetDevice are not null
    //   Disconnecting device Pending
    //                        mCurrentDevice is not null, mTargetDevice is null
    //   Incoming connections Pending
    //                        Both mCurrentDevice and mTargetDevice are null
    private BluetoothDevice mCurrentDevice = null;
    private BluetoothDevice mTargetDevice = null;
    private BluetoothDevice mIncomingDevice = null;
    private BluetoothDevice mActiveScoDevice = null;
    private BluetoothDevice mScoRequestedDevice = null;
    private BluetoothDevice mLastScoDiscReqDevice = null;
    private BluetoothDevice mMultiDisconnectDevice = null;
    private BluetoothDevice mPendingScoForVRDevice = null;

    // Multi HFP: Connected devices list holds all currently connected headsets
    private ArrayList<BluetoothDevice> mConnectedDevicesList = new ArrayList<BluetoothDevice>();

    static {
        classInitNative();

        VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID = new HashMap<String, Integer>();
        VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID.put(
                BluetoothHeadset.VENDOR_SPECIFIC_HEADSET_EVENT_XEVENT,
                BluetoothAssignedNumbers.PLANTRONICS);
        VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID.put(
                BluetoothHeadset.VENDOR_RESULT_CODE_COMMAND_ANDROID,
                BluetoothAssignedNumbers.GOOGLE);
        VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID.put(
                BluetoothHeadset.VENDOR_SPECIFIC_HEADSET_EVENT_XAPL,
                BluetoothAssignedNumbers.APPLE);
        VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID.put(
                BluetoothHeadset.VENDOR_SPECIFIC_HEADSET_EVENT_IPHONEACCEV,
                BluetoothAssignedNumbers.APPLE);
    }

    private HeadsetStateMachine(HeadsetService context) {
        super(TAG);
        mService = context;
        mVoiceRecognitionStarted = false;
        mWaitingForVoiceRecognition = false;

        mPowerManager = (PowerManager) context.getSystemService(Context.POWER_SERVICE);
        mStartVoiceRecognitionWakeLock = mPowerManager.newWakeLock(
                PowerManager.PARTIAL_WAKE_LOCK, TAG + ":VoiceRecognition");
        mStartVoiceRecognitionWakeLock.setReferenceCounted(false);

        mConnectivityManager = (ConnectivityManager)
                context.getSystemService(Context.CONNECTIVITY_SERVICE);

        mDialingOut = false;
        mAudioManager = (AudioManager) context.getSystemService(Context.AUDIO_SERVICE);
        mPhonebook = new AtPhonebook(mService, this);
        mPhoneState = new HeadsetPhoneState(context, this);
        mAudioState = BluetoothHeadset.STATE_AUDIO_DISCONNECTED;
        mAdapter = BluetoothAdapter.getDefaultAdapter();
        Intent intent = new Intent(IBluetoothHeadsetPhone.class.getName());
        intent.setComponent(intent.resolveSystemService(context.getPackageManager(), 0));
        if (intent.getComponent() == null || !context.bindService(intent, mConnection, 0)) {
            Log.e(TAG, "Could not bind to Bluetooth Headset Phone Service");
        }

        int max_hfp_clients = SystemProperties.getInt("persist.bt.max.hs.connections", 1);
        if (max_hfp_clients >= 2)
            max_hf_connections = 2;
        Log.d(TAG, "max_hf_connections = " + max_hf_connections);
        Log.d(TAG,
                "in-band_ringing_support = " + BluetoothHeadset.isInbandRingingSupported(mService));
        mNativeAvailable = true;

        mDisconnected = new Disconnected();
        mPending = new Pending();
        mConnected = new Connected();
        mAudioOn = new AudioOn();
        // Multi HFP: initialise new class variable
        mMultiHFPending = new MultiHFPending();

        if (sVoiceCommandIntent == null) {
            sVoiceCommandIntent = new Intent(Intent.ACTION_VOICE_COMMAND);
            sVoiceCommandIntent.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
        }

        addState(mDisconnected);
        addState(mPending);
        addState(mConnected);
        addState(mAudioOn);
        // Multi HFP: add State
        addState(mMultiHFPending);

        setInitialState(mDisconnected);

        BT_SOC = SystemProperties.get("qcom.bluetooth.soc");

        if(BT_SOC.equals("cherokee"))
        {
            mPlaybackForVR = SystemProperties.getBoolean("persist.bt.hfp.playbackforvr", true);
            Log.d(TAG, "mPlaybackForVR is " + mPlaybackForVR);

            mPlaybackForVOIP = SystemProperties.getBoolean("persist.bt.hfp.playbackforvoip", true);
            Log.d(TAG, "mPlaybackForVOIP is " + mPlaybackForVOIP);
        }

        if (mPlaybackForVR || mPlaybackForVOIP)
            mAudioPlayer = new AudioPlayer();
    }

    static HeadsetStateMachine make(HeadsetService context) {
        Log.d(TAG, "make");
        HeadsetStateMachine hssm = new HeadsetStateMachine(context);
        hssm.start();
        hssm.initializeNative(hssm.max_hf_connections,
                              BluetoothHeadset.isInbandRingingSupported(hssm.mService));
        return hssm;
    }

    public void doQuit() {
        Log.d(TAG, "Enter doQuit()");
        int size = 0;
        if (mAudioManager != null) {
             mAudioManager.setParameters("BT_SCO=off");
             mAudioManager.setBluetoothScoOn(false);
        }
        if (mActiveScoDevice != null && !mPhoneState.getIsCsCall()) {
            sendVoipConnectivityNetworktype(false);
        }
        if (mActiveScoDevice != null) {
             broadcastAudioState(mActiveScoDevice, BluetoothHeadset.STATE_AUDIO_DISCONNECTED,
                                BluetoothHeadset.STATE_AUDIO_CONNECTED);
        }

        if ((mTargetDevice != null) &&
            (getConnectionState(mTargetDevice) == BluetoothProfile.STATE_CONNECTING)) {
            Log.d(TAG, "doQuit()- Move HFP State to DISCONNECTED");
            broadcastConnectionState(mTargetDevice, BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
        }

        if ((mIncomingDevice!= null) &&
            (getConnectionState(mIncomingDevice) == BluetoothProfile.STATE_CONNECTING)) {
            Log.d(TAG, "doQuit()- Move HFP State to DISCONNECTED");
            broadcastConnectionState(mIncomingDevice, BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
        }

        /* Broadcast disconnected state for connected devices.*/
        size = mConnectedDevicesList.size();
        Log.d(TAG, "cleanup: mConnectedDevicesList size is " + size);
        for(int i = 0; i < size; i++) {
            mCurrentDevice = mConnectedDevicesList.get(i);
            broadcastConnectionState(mCurrentDevice, BluetoothProfile.STATE_DISCONNECTED,
                                     BluetoothProfile.STATE_CONNECTED);
        }

        if ((mPlaybackForVR || mPlaybackForVOIP) &&
            (mAudioPlayer != null) &&
            mAudioPlayer.isPlaying()) {
            Log.d(TAG, "SCO disconnected, stop audio playback");
            mAudioPlayer.stop();
        }

        quitNow();
        Log.d(TAG, "Exit doQuit()");
    }

    public void cleanup() {
        Log.d(TAG, "Enter cleanup()");
        if (mAudioManager != null) {
             mAudioManager.setParameters("BT_SCO=off");
             mAudioManager.setBluetoothScoOn(false);
        }
        if (mPhoneProxy != null) {
            if (DBG) Log.d(TAG, "Unbinding service...");
            synchronized (mConnection) {
                try {
                    mPhoneProxy = null;
                    mService.unbindService(mConnection);
                } catch (Exception re) {
                    Log.e(TAG, "Error unbinding from IBluetoothHeadsetPhone", re);
                }
            }
        }
        if (mPhoneState != null) {
            mPhoneState.listenForPhoneState(false);
            mPhoneState.cleanup();
        }
        if (mPhonebook != null) {
            mPhonebook.cleanup();
        }
        if (mHeadsetAudioParam != null) {
            mHeadsetAudioParam.clear();
        }
        if (mHeadsetBrsf != null) {
            mHeadsetBrsf.clear();
        }
        if (mConnectedDevicesList != null) {
            mConnectedDevicesList.clear();
        }
        if (mActiveScoDevice != null && !mPhoneState.getIsCsCall()) {
            sendVoipConnectivityNetworktype(false);
        }
        if (mNativeAvailable) {
            cleanupNative();
            mNativeAvailable = false;
        }
        Log.d(TAG, "Exit cleanup()");
    }

    public void dump(StringBuilder sb) {
        ProfileService.println(sb, "mCurrentDevice: " + mCurrentDevice);
        ProfileService.println(sb, "mTargetDevice: " + mTargetDevice);
        ProfileService.println(sb, "mIncomingDevice: " + mIncomingDevice);
        ProfileService.println(sb, "mActiveScoDevice: " + mActiveScoDevice);
        ProfileService.println(sb, "mMultiDisconnectDevice: " + mMultiDisconnectDevice);
        ProfileService.println(sb, "mVirtualCallStarted: " + mVirtualCallStarted);
        ProfileService.println(sb, "mVoiceRecognitionStarted: " + mVoiceRecognitionStarted);
        ProfileService.println(sb, "mWaitingForVoiceRecognition: " + mWaitingForVoiceRecognition);
        ProfileService.println(sb, "StateMachine: " + this.toString());
        ProfileService.println(sb, "mPhoneState: " + mPhoneState);
        ProfileService.println(sb, "mAudioState: " + mAudioState);
    }

    private class Disconnected extends State {
        @Override
        public void enter() {
            Log.d(TAG, "Enter Disconnected: " + getCurrentMessage().what + ", size: "
                    + mConnectedDevicesList.size());
            mPhonebook.resetAtState();
            mPhoneState.listenForPhoneState(false);
            mVoiceRecognitionStarted = false;
            mWaitingForVoiceRecognition = false;
            mDialingOut = false;
            mIsBlacklistedDevice = false;
        }

        @Override
        public boolean processMessage(Message message) {
            Log.d(TAG, "Disconnected process message: " + message.what + ", size: "
                    + mConnectedDevicesList.size());
            if (mConnectedDevicesList.size() != 0 || mTargetDevice != null
                    || mIncomingDevice != null) {
                Log.e(TAG, "ERROR: mConnectedDevicesList is not empty,"
                                + "target, or mIncomingDevice not null in Disconnected");
                return NOT_HANDLED;
            }

            switch (message.what) {
                case CONNECT:
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    if (!mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Make conn retry entry for device " + device);
                        mRetryConnect.put(device, 0);
                    }
                    int RetryConn = mRetryConnect.get(device);
                    log("RetryConn = " + RetryConn);

                    if (RetryConn > 1) {
                        if (mRetryConnect.containsKey(device)) {
                            Log.d(TAG, "Removing device " + device +
                                  " conn retry entry since RetryConn = " + RetryConn);
                            mRetryConnect.remove(device);
                        }
                        break;
                    }

                    Log.d(TAG, "Disconnected: connecting to device=" + device);
                    broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                            BluetoothProfile.STATE_DISCONNECTED);
                    if (!connectHfpNative(getByteAddress(device))) {
                        broadcastConnectionState(device,
                                   BluetoothProfile.STATE_DISCONNECTED,
                                   BluetoothProfile.STATE_CONNECTING);
                        break;
                    }

                    RetryConn = RetryConn + 1;
                    mRetryConnect.put(device, RetryConn);
                    if (mPhoneProxy != null) {
                        try {
                            log("Query the phonestates");
                            mPhoneProxy.queryPhoneState();
                        } catch (RemoteException e) {
                            Log.e(TAG, Log.getStackTraceString(new Throwable()));
                        }
                    } else Log.e(TAG, "Phone proxy null for query phone state");

                    synchronized (HeadsetStateMachine.this) {
                        mTargetDevice = device;
                        transitionTo(mPending);
                    }
                    Message m = obtainMessage(CONNECT_TIMEOUT);
                    m.obj = device;
                    sendMessageDelayed(m, CONNECT_TIMEOUT_MILLIS);
                    break;
                case DISCONNECT:
                    // ignore
                    break;
                case INTENT_BATTERY_CHANGED:
                    processIntentBatteryChanged((Intent) message.obj);
                    break;
                case VOIP_CALL_STATE_CHANGED_ALERTING:
                    // intentional fall through
                case VOIP_CALL_STATE_CHANGED_ACTIVE:
                    // intentional fall through
                case CALL_STATE_CHANGED:
                    processCallState((HeadsetCallState) message.obj, message.arg1 == 1);
                    break;
                case UPDATE_A2DP_PLAY_STATE:
                    processIntentA2dpPlayStateChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_CONN_STATE:
                    processIntentA2dpStateChanged((Intent) message.obj);
                    break;
                case UPDATE_CALL_TYPE:
                    processIntentUpdateCallType((Intent) message.obj);
                    break;
                case DEVICE_STATE_CHANGED:
                    log("Disconnected: ignoring DEVICE_STATE_CHANGED event");
                    break;
                case STACK_EVENT:
                    StackEvent event = (StackEvent) message.obj;
                    Log.d(TAG, "Disconnected: event type: " + event.type);
                    switch (event.type) {
                        case EVENT_TYPE_CONNECTION_STATE_CHANGED:
                            processConnectionEvent(event.valueInt, event.device);
                            break;
                        default:
                            Log.e(TAG, "Disconnected: unexpected stack event: " + event.type);
                            break;
                    }
                    break;
                default:
                    Log.e(TAG, "Disconnected: unexpected message " + message.what);
                    return NOT_HANDLED;
            }
            Log.d(TAG, "Exit Disconnected processMessage() ");
            return HANDLED;
        }

        @Override
        public void exit() {
            Log.d(TAG, "Exit Disconnected: " + getCurrentMessage().what);
        }

        // in Disconnected state
        private void processConnectionEvent(int state, BluetoothDevice device) {
            Log.d(TAG,
                    "Disconnected: processConnectionEvent, state=" + state + ", device=" + device);
            switch (state) {
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED:
                    Log.w(TAG, "Disconnected: ignore DISCONNECTED event, device=" + device);
                    break;
                // Both events result in Pending state as SLC establishment is still required
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTED:
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTING:
                    if (okToConnect(device)) {
                        Log.d(TAG,
                                "Disconnected: connected/connecting incoming HF, device=" + device);
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                                BluetoothProfile.STATE_DISCONNECTED);
                        synchronized (HeadsetStateMachine.this) {
                            mIncomingDevice = device;
                            transitionTo(mPending);
                        }
                    } else {
                        Log.d(TAG,
                                "Disconnected: rejected incoming HF, priority="
                                        + mService.getPriority(device) + " bondState="
                                        + device.getBondState() + ", device=" + device);
                        // reject the connection and stay in Disconnected state itself
                        disconnectHfpNative(getByteAddress(device));
                        // the other profile connection should be initiated
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_DISCONNECTED);
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTING:
                    Log.w(TAG, "Disconnected: ignore DISCONNECTING event, device=" + device);
                    break;
                default:
                    Log.e(TAG, "Disconnected: incorrect state: " + state);
                    break;
            }
            Log.d(TAG, "Exit Disconnected processConnectionEvent()");
        }
    }

    // Per HFP 1.7.1 spec page 23/144, Pending state needs to handle
    //      AT+BRSF, AT+CIND, AT+CMER, AT+BIND, +CHLD
    // commands during SLC establishment
    private class Pending extends State {
        @Override
        public void enter() {
            Log.d(TAG, "Enter Pending: " + getCurrentMessage().what);
        }

        @Override
        public boolean processMessage(Message message) {
            log("Pending: processMessage=" + message.what
                    + ", numConnectedDevices=" + mConnectedDevicesList.size());
            switch (message.what) {
                case CONNECT:
                case CONNECT_AUDIO:
                    deferMessage(message);
                    break;
                case CONNECT_TIMEOUT:
                    onConnectionStateChanged(HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED,
                            getByteAddress(mTargetDevice));
                    break;
                case DISCONNECT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "Pending: DISCONNECT, device=" + device);
                    if (mCurrentDevice != null && mTargetDevice != null
                            && mTargetDevice.equals(device)) {
                        // cancel connection to the mTargetDevice
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                        }
                    } else {
                        deferMessage(message);
                    }
                    break;
                }
                case INTENT_BATTERY_CHANGED:
                    processIntentBatteryChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_PLAY_STATE:
                    processIntentA2dpPlayStateChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_CONN_STATE:
                    processIntentA2dpStateChanged((Intent) message.obj);
                    break;
                case VOIP_CALL_STATE_CHANGED_ALERTING:
                    // intentional fall through
                case VOIP_CALL_STATE_CHANGED_ACTIVE:
                    // intentional fall through
                case CALL_STATE_CHANGED:
                    processCallState((HeadsetCallState) message.obj, message.arg1 == 1);
                    break;
                case BIND_RESPONSE: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    bindResponseNative(message.arg1, message.arg2 == 1, getByteAddress(device));
                    break;
                }
                case DEVICE_STATE_CHANGED:
                    log("Pending: ignoring DEVICE_STATE_CHANGED event");
                    break;
                case QUERY_PHONE_STATE_AT_SLC:
                    try {
                       log("Update call states after SLC is up");
                       mPhoneProxy.queryPhoneState();
                    } catch (RemoteException e) {
                       Log.e(TAG, Log.getStackTraceString(new Throwable()));
                    }
                    break;
                case STACK_EVENT:
                    StackEvent event = (StackEvent) message.obj;
                    Log.d(TAG, "Pending: event type: " + event.type);
                    switch (event.type) {
                        case EVENT_TYPE_CONNECTION_STATE_CHANGED:
                            processConnectionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AT_CHLD:
                            processAtChld(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AT_CIND:
                            processAtCind(event.device);
                            break;
                        case EVENT_TYPE_WBS:
                            processWBSEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_BIND:
                            processAtBind(event.valueString, event.device);
                            break;
                        // Unexpected AT commands, we only handle them for comparability reasons
                        case EVENT_TYPE_VR_STATE_CHANGED:
                            Log.w(TAG,
                                    "Pending: Unexpected VR event, device=" + event.device
                                            + ", state=" + event.valueInt);
                            processVrEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_DIAL_CALL:
                            Log.w(TAG, "Pending: Unexpected dial event, device=" + event.device);
                            processDialCall(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST:
                            Log.w(TAG,
                                    "Pending: Unexpected subscriber number event for" + event.device
                                            + ", state=" + event.valueInt);
                            processSubscriberNumberRequest(event.device);
                            break;
                        case EVENT_TYPE_AT_COPS:
                            Log.w(TAG, "Pending: Unexpected COPS event for " + event.device);
                            processAtCops(event.device);
                            break;
                        case EVENT_TYPE_AT_CLCC:
                            Log.w(TAG, "Pending: Unexpected CLCC event for" + event.device);
                            break;
                        case EVENT_TYPE_UNKNOWN_AT:
                            Log.w(TAG,
                                    "Pending: Unexpected unknown AT event for" + event.device
                                            + ", cmd=" + event.valueString);
                            processUnknownAt(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_KEY_PRESSED:
                            Log.w(TAG, "Pending: Unexpected key-press event for " + event.device);
                            processKeyPressed(event.device);
                            break;
                        case EVENT_TYPE_BIEV:
                            Log.w(TAG,
                                    "Pending: Unexpected BIEV event for " + event.device
                                            + ", indId=" + event.valueInt
                                            + ", indVal=" + event.valueInt2);
                            processAtBiev(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_VOLUME_CHANGED:
                            Log.w(TAG, "Pending: Unexpected volume event for " + event.device);
                            processVolumeEvent(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_ANSWER_CALL:
                            Log.w(TAG, "Pending: Unexpected answer event for " + event.device);
                            processAnswerCall(event.device);
                            break;
                        case EVENT_TYPE_HANGUP_CALL:
                            Log.w(TAG, "Pending: Unexpected hangup event for " + event.device);
                            processHangupCall(event.device);
                        default:
                            Log.e(TAG, "Pending: Unexpected event: " + event.type);
                            break;
                    }
                    break;
                default:
                    Log.e(TAG, "Pending: unexpected message " + message.what);
                    return NOT_HANDLED;
            }
            Log.d(TAG, " Exit Pending processMessage() ");
            return HANDLED;
        }

        // in Pending state
        private void processConnectionEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Pending: processConnectionEvent, state=" + state + ", device=" + device);
            BluetoothDevice pendingDevice = getDeviceForMessage(CONNECT_TIMEOUT);
            switch (state) {
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        synchronized (HeadsetStateMachine.this) {
                            processWBSEvent(0, device); /* disable WBS audio parameters */
                            mConnectedDevicesList.remove(device);
                            mHeadsetAudioParam.remove(device);
                            mHeadsetBrsf.remove(device);
                            Log.d(TAG,
                                    "Pending: device " + device.getAddress()
                                            + " is removed in Pending state");
                        }
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_DISCONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mCurrentDevice = null;
                        }

                        if (mTargetDevice != null) {
                            if (!connectHfpNative(getByteAddress(mTargetDevice))) {
                                broadcastConnectionState(mTargetDevice,
                                        BluetoothProfile.STATE_DISCONNECTED,
                                        BluetoothProfile.STATE_CONNECTING);
                                synchronized (HeadsetStateMachine.this) {
                                    mTargetDevice = null;
                                    transitionTo(mDisconnected);
                                }
                            }
                        } else {
                            synchronized (HeadsetStateMachine.this) {
                                mIncomingDevice = null;
                                if (mConnectedDevicesList.size() == 0) {
                                    transitionTo(mDisconnected);
                                } else {
                                    processMultiHFDisconnect(device);
                                }
                            }
                        }
                    } else if (device.equals(mTargetDevice)) {
                        // outgoing connection failed
                        if (mRetryConnect.containsKey(mTargetDevice)) {
                            boolean connectPending = hasDeferredMessages(CONNECT)
                                    && max_hf_connections == 1;
                            Log.d(TAG, "connectPending: " + connectPending);
                            // retry again only if we tried once for non-blacklisted devices
                            if (mRetryConnect.get(device) == 1 &&
                                  !connectPending &&
                                  !isDeviceBlacklistedforConnectionRetry(device)) {
                                Log.d(TAG, "Retry outgoing conn again for device = " + mTargetDevice
                                      + " after " + RETRY_CONNECT_TIME_SEC + "msec");
                                Message m = obtainMessage(CONNECT);
                                m.obj = device;
                                sendMessageDelayed(m, RETRY_CONNECT_TIME_SEC);
                            } else {
                                Log.d(TAG, "Removing conn retry entry for device = " +
                                      mTargetDevice);
                                mRetryConnect.remove(mTargetDevice);
                            }
                        }
                        broadcastConnectionState(mTargetDevice, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                            if (mConnectedDevicesList.size() == 0) {
                                transitionTo(mDisconnected);
                            } else {
                                transitionTo(mConnected);
                            }
                        }
                    } else if (device.equals(mIncomingDevice)) {
                        broadcastConnectionState(mIncomingDevice,
                                BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mIncomingDevice = null;
                            if (mConnectedDevicesList.size() == 0) {
                                transitionTo(mDisconnected);
                            } else {
                                transitionTo(mConnected);
                            }
                        }
                    } else {
                        Log.e(TAG, "Pending: unknown device disconnected: " + device);
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        // Disconnection failure does not go through SLC establishment
                        Log.w(TAG, "Pending: disconnection failed for device " + device);
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                BluetoothProfile.STATE_DISCONNECTING);
                        if (mTargetDevice != null) {
                            broadcastConnectionState(mTargetDevice,
                                    BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                        }
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                            transitionTo(mConnected);
                        }
                    } else if (!device.equals(mTargetDevice) && !device.equals(mIncomingDevice)) {
                        Log.w(TAG,
                                "Pending: unknown incoming HF connected on RFCOMM, device="
                                        + device);
                        if (!okToConnect(device)) {
                            // reject the connection and stay in Pending state itself
                            Log.i(TAG,
                                    "Pending: unknown incoming HF rejected on RFCOMM, priority="
                                            + mService.getPriority(device)
                                            + " bondState=" + device.getBondState());
                            disconnectHfpNative(getByteAddress(device));
                        }
                    } else {
                        // Do nothing in normal case, wait for SLC connected event
                        pendingDevice = null;
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_SLC_CONNECTED:
                    int previousConnectionState = BluetoothProfile.STATE_CONNECTING;
                    synchronized (HeadsetStateMachine.this) {
                        mCurrentDevice = device;
                        mConnectedDevicesList.add(device);
                        if (mRetryConnect.containsKey(device)) {
                            Log.d(TAG,
                                    "Removing device " + device
                                            + " conn retry entry since we got SLC");
                            mRetryConnect.remove(device);
                        }
                        if (device.equals(mTargetDevice)) {
                            Log.d(TAG,
                                    "Pending: added " + device
                                            + " to mConnectedDevicesList, requested by us");
                            mTargetDevice = null;
                            transitionTo(mConnected);
                        } else if (device.equals(mIncomingDevice)) {
                            Log.d(TAG,
                                    "Pending: added " + device
                                            + " to mConnectedDevicesList, requested by remote");
                            mIncomingDevice = null;
                            transitionTo(mConnected);
                        } else {
                            Log.d(TAG,
                                    "Pending: added " + device
                                            + "to mConnectedDevicesList, unknown source");
                            previousConnectionState = BluetoothProfile.STATE_DISCONNECTED;
                        }
                    }
                    configAudioParameters(device);
                    processSlcConnected();
                    broadcastConnectionState(
                            device, BluetoothProfile.STATE_CONNECTED, previousConnectionState);
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTING:
                    if ((mCurrentDevice != null) && mCurrentDevice.equals(device)) {
                        log("current device tries to connect back");
                        // TODO(BT) ignore or reject
                    } else if (mTargetDevice != null && mTargetDevice.equals(device)) {
                        // The stack is connecting to target device or
                        // there is an incoming connection from the target device at the same time
                        // we already broadcasted the intent, doing nothing here
                        log("Stack and target device are connecting");
                    } else if (mIncomingDevice != null && mIncomingDevice.equals(device)) {
                        Log.e(TAG, "Another connecting event on the incoming device");
                    } else {
                        // We get an incoming connecting request while Pending
                        // TODO(BT) is stack handing this case? let's ignore it for now
                        log("Incoming connection while pending, ignore");
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTING:
                    if ((mCurrentDevice != null) && mCurrentDevice.equals(device)) {
                        // we already broadcasted the intent, doing nothing here
                        log("stack is disconnecting mCurrentDevice");
                    } else if (mTargetDevice != null && mTargetDevice.equals(device)) {
                        Log.e(TAG, "TargetDevice is getting disconnected");
                    } else if (mIncomingDevice != null && mIncomingDevice.equals(device)) {
                        Log.e(TAG, "IncomingDevice is getting disconnected");
                    } else {
                        Log.e(TAG, "Disconnecting unknow device: " + device);
                    }
                    break;
                default:
                    Log.e(TAG, "Incorrect state: " + state);
                    break;
            }
            if (pendingDevice != null && pendingDevice.equals(device)) {
                removeMessages(CONNECT_TIMEOUT);
                Log.d(TAG, "Pending: removed CONNECT_TIMEOUT for device=" + pendingDevice);
            }
            Log.d(TAG, "Exit Pending processConnectionEvent()");
        }

        private void processMultiHFDisconnect(BluetoothDevice device) {
            Log.d(TAG, "Enter pending processMultiHFDisconnect()");
            log("Pending state: processMultiHFDisconnect");
            /* Assign the current activedevice again if the disconnected
                         device equals to the current active device*/
            if (mCurrentDevice != null && mCurrentDevice.equals(device)) {
                transitionTo(mConnected);
                int deviceSize = mConnectedDevicesList.size();
                mCurrentDevice = mConnectedDevicesList.get(deviceSize - 1);
            } else {
                // The disconnected device is not current active device
                if (mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED)
                    transitionTo(mAudioOn);
                else
                    transitionTo(mConnected);
            }
            log("processMultiHFDisconnect , the latest mCurrentDevice is:"
                                             + mCurrentDevice);
            log("Pending state: processMultiHFDisconnect ," +
                           "fake broadcasting for mCurrentDevice");
            broadcastConnectionState(mCurrentDevice, BluetoothProfile.STATE_CONNECTED,
                    BluetoothProfile.STATE_DISCONNECTED);
            Log.d(TAG, "Exit pending processMultiHFDisconnect()");
        }

        private void processSlcConnected() {
            Log.d(TAG, "Enter Pending processSlcConnected()");
            if (mPhoneProxy != null) {
                sendMessageDelayed(QUERY_PHONE_STATE_AT_SLC, QUERY_PHONE_STATE_CHANGED_DELAYED);
                mA2dpSuspend = false;/*Reset at SLC*/
                mPendingCiev = false;
                mPendingCallStates.clear();
                if ((isInCall()) && (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED)) {
                    if (DBG) {
                        log("Headset connected while we are in some call state");
                        log("Make A2dpSuspended=true here");
                    }
                    mAudioManager.setParameters("A2dpSuspended=true");
                    mA2dpSuspend = true;
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for query phone state");
            }
            // Checking for the Blacklisted device Addresses
            mIsBlacklistedDevice = isConnectedDeviceBlacklistedforIncomingCall();
            Log.d(TAG, "Exit Pending processSlcConnected()");
        }
    }

    private class Connected extends State {
        @Override
        public void enter() {
            Log.d(TAG, "Enter Connected: " + getCurrentMessage().what +
                           ", size: " + mConnectedDevicesList.size());
            // start phone state listener here so that the CIND response as part of SLC can be
            // responded to, correctly.
            // we may enter Connected from Disconnected/Pending/AudioOn. listenForPhoneState
            // internally handles multiple calls to start listen
            mPhoneState.listenForPhoneState(true);
        }

        @Override
        public boolean processMessage(Message message) {
            Log.d(TAG, "Connected process message=" + message.what
                    + ", numConnectedDevices=" + mConnectedDevicesList.size());
            switch (message.what) {
                case CONNECT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "Connected: CONNECT, device=" + device);
                    if (mConnectedDevicesList.contains(device)) {
                        Log.w(TAG, "Connected: CONNECT, device " + device + " is connected");
                        break;
                    }

                    if (!mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Make conn retry entry for device " + device);
                        mRetryConnect.put(device, 0);
                    }

                    int RetryConn = mRetryConnect.get(device);
                    Log.d(TAG, "RetryConn = " + RetryConn);
                    if (RetryConn > 1) {
                        if (mRetryConnect.containsKey(device)) {
                            Log.d(TAG, "Removing device " + device +
                                  " conn retry entry since RetryConn = " + RetryConn);
                            mRetryConnect.remove(device);
                        }
                        break;
                    }

                    if (mConnectedDevicesList.size() >= max_hf_connections) {
                        BluetoothDevice disconnectDevice = mConnectedDevicesList.get(0);
                        Log.d(TAG, "Connected: Reach to max size, disconnect " + disconnectDevice);
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                                BluetoothProfile.STATE_DISCONNECTED);
                        if (disconnectHfpNative(getByteAddress(disconnectDevice))) {
                            broadcastConnectionState(disconnectDevice,
                                    BluetoothProfile.STATE_DISCONNECTING,
                                    BluetoothProfile.STATE_CONNECTED);
                        } else {
                            Log.w(TAG, "Connected: failed to disconnect " + disconnectDevice);
                            broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                            break;
                        }
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = device;
                            if (max_hf_connections == 1) {
                                transitionTo(mPending);
                            } else {
                                mMultiDisconnectDevice = disconnectDevice;
                                transitionTo(mMultiHFPending);
                            }
                        }
                    } else if (mConnectedDevicesList.size() < max_hf_connections) {
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                            BluetoothProfile.STATE_DISCONNECTED);
                        if (!connectHfpNative(getByteAddress(device))) {
                            broadcastConnectionState(device,
                                    BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                            break;
                        }
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = device;
                            // Transition to MultiHFPending state for Multi HF connection
                            transitionTo(mMultiHFPending);
                        }
                    }
                    RetryConn = RetryConn + 1;
                    mRetryConnect.put(device, RetryConn);
                    Message m = obtainMessage(CONNECT_TIMEOUT);
                    m.obj = device;
                    sendMessageDelayed(m, CONNECT_TIMEOUT_MILLIS);
                } break;
                case DISCONNECT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "Connected: DISCONNECT from device=" + device);
                    if (!mConnectedDevicesList.contains(device)) {
                        Log.w(TAG, "Connected: DISCONNECT, device " + device + " not connected");
                        break;
                    }
                    broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTING,
                            BluetoothProfile.STATE_CONNECTED);
                    if (!disconnectHfpNative(getByteAddress(device))) {
                        // Failed disconnection request
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                BluetoothProfile.STATE_DISCONNECTING);
                        break;
                    }
                    // Pending disconnection confirmation
                    if (mConnectedDevicesList.size() > 1) {
                        mMultiDisconnectDevice = device;
                        transitionTo(mMultiHFPending);
                    } else {
                        transitionTo(mPending);
                    }
                } break;
                case CONNECT_AUDIO: {
                    BluetoothDevice device = mCurrentDevice;
                    Log.d(TAG, "Connected: CONNECT_AUDIO, device=" + device);
                    if (!isScoAcceptable() || mPendingCiev) {
                        Log.w(TAG,"No Active/Held call, no call setup,and no in-band ringing, or A2DP"
                                    + " is playing, not allowing SCO, device=" + device);
                        break;
                    }
                    // TODO(BT) when failure, broadcast audio connecting to disconnected intent
                    //          check if device matches mCurrentDevice
                    if (mActiveScoDevice != null) {
                        Log.w(TAG, "Connected: CONNECT_AUDIO, mActiveScoDevice is not null");
                        device = mActiveScoDevice;
                    }
                    if (mLastScoDiscReqDevice != null) {
                        Log.d(TAG, "Last SCO Discon Requested device is" + mLastScoDiscReqDevice);
                        device = mLastScoDiscReqDevice;
                        mLastScoDiscReqDevice = null;
                    }

                    if (mScoRequestedDevice != null) {
                        Log.d(TAG, "SCO Requested device is" + mScoRequestedDevice);
                        device = mScoRequestedDevice;
                        mScoRequestedDevice = null;
                    }

                    log("connectAudioNative in Connected for device = " + device);
                    connectAudioNative(getByteAddress(device));
                } break;
                case VOICE_RECOGNITION_START:
                    processLocalVrEvent(HeadsetHalConstants.VR_STATE_STARTED);
                    break;
                case VOICE_RECOGNITION_STOP:
                    processLocalVrEvent(HeadsetHalConstants.VR_STATE_STOPPED);
                    break;
                case VOIP_CALL_STATE_CHANGED_ALERTING:
                    // intentional fall through
                case VOIP_CALL_STATE_CHANGED_ACTIVE:
                    processCallState((HeadsetCallState) message.obj, message.arg1 == 1);
                    break;
                case CALL_STATE_CHANGED:
                {
                    boolean isPts = SystemProperties.getBoolean("bt.pts.certification", false);

                    // for PTS, VOIP calls, send the indicators as is
                    if(isPts || isVirtualCallInProgress())
                        processCallState((HeadsetCallState) message.obj,
                                              ((message.arg1==1)?true:false));
                    else
                        processCallStatesDelayed((HeadsetCallState) message.obj, false);
                    break;
                }
                case CS_CALL_STATE_CHANGED_ALERTING:
                {
                    // get the top of the Q
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    // top of the queue is call alerting
                    if(tempCallState != null &&
                        tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
                    {
                        Log.d(TAG, "alerting message timer expired, send alerting update");
                        //dequeue the alerting call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }

                    // top of the queue == call active
                    tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                         tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "alerting message timer expired, send delayed active mesg");
                        //send delayed message for call active;
                        Message msg = obtainMessage(CS_CALL_STATE_CHANGED_ACTIVE);
                        msg.arg1 = 0;
                        sendMessageDelayed(msg, CS_CALL_ACTIVE_DELAY_TIME_MSEC);
                    }
                    break;
                }
                case CS_CALL_STATE_CHANGED_ACTIVE:
                {
                    // get the top of the Q
                    // top of the queue == call active
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                         tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "active message timer expired, send active update");
                        //dequeue the active call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }
                    break;
                }
                case INTENT_BATTERY_CHANGED:
                    processIntentBatteryChanged((Intent) message.obj);
                    break;
                case DEVICE_STATE_CHANGED:
                    processDeviceStateChanged((HeadsetDeviceState) message.obj);
                    break;
                case SEND_CCLC_RESPONSE:
                    processSendClccResponse((HeadsetClccResponse) message.obj);
                    break;
                case CLCC_RSP_TIMEOUT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    if (device != null)
                        clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
                } break;
                case SEND_VENDOR_SPECIFIC_RESULT_CODE:
                    processSendVendorSpecificResultCode(
                            (HeadsetVendorSpecificResultCode) message.obj);
                    break;
                case DIALING_OUT_TIMEOUT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "mDialingOut is " + mDialingOut);
                    if (mDialingOut) {
                        Log.d(TAG, "Timeout waiting for call to be placed, resetting mDialingOut");
                        mDialingOut= false;
                        atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR,
                                                   0, getByteAddress(device));
                    }
                } break;
                case VIRTUAL_CALL_START:
                    initiateScoUsingVirtualVoiceCall();
                    break;
                case VIRTUAL_CALL_STOP:
                    terminateScoUsingVirtualVoiceCall();
                    break;
                case ENABLE_WBS: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device), WBS_CODEC);
                    break;
                }
                case DISABLE_WBS: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device), NBS_CODEC);
                    break;
                }
                case BIND_RESPONSE: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    bindResponseNative(message.arg1, message.arg2 == 1, getByteAddress(device));
                    break;
                }
                case UPDATE_A2DP_PLAY_STATE:
                    processIntentA2dpPlayStateChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_CONN_STATE:
                    processIntentA2dpStateChanged((Intent) message.obj);
                    break;
                case UPDATE_CALL_TYPE:
                    processIntentUpdateCallType((Intent) message.obj);
                    break;
                case START_VR_TIMEOUT: {
                    BluetoothDevice device = (BluetoothDevice) message.obj;
                    if (mWaitingForVoiceRecognition) {
                        device = (BluetoothDevice) message.obj;
                        mWaitingForVoiceRecognition = false;
                        Log.e(TAG, "Timeout waiting for voice recognition to start");
                        atResponseCodeNative(
                                HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                    }
                }
                    break;
                case QUERY_PHONE_STATE_AT_SLC:
                    try {
                       log("Update call states after SLC is up");
                       mPhoneProxy.queryPhoneState();
                    } catch (RemoteException e) {
                       Log.e(TAG, Log.getStackTraceString(new Throwable()));
                    }
                    break;
                case PROCESS_CPBR:
                    Intent intent = (Intent) message.obj;
                    processCpbr(intent);
                    break;
                case SEND_INCOMING_CALL_IND:
                    phoneStateChangeNative(0, 0, HeadsetHalConstants.CALL_STATE_INCOMING,
                                       mPhoneState.getNumber(), mPhoneState.getType());
                    break;
                case STACK_EVENT:
                    StackEvent event = (StackEvent) message.obj;
                    Log.d(TAG, "Connected: event type: " + event.type + "event device : " + event.device);
                    switch (event.type) {
                        case EVENT_TYPE_CONNECTION_STATE_CHANGED:
                            processConnectionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AUDIO_STATE_CHANGED:
                            processAudioEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_VR_STATE_CHANGED:
                            processVrEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_ANSWER_CALL:
                            processAnswerCall(event.device);
                            break;
                        case EVENT_TYPE_HANGUP_CALL:
                            processHangupCall(event.device);
                            break;
                        case EVENT_TYPE_VOLUME_CHANGED:
                            processVolumeEvent(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_DIAL_CALL:
                            processDialCall(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_SEND_DTMF:
                            processSendDtmf(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_NOICE_REDUCTION:
                            processNoiceReductionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_WBS:
                            processWBSEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AT_CHLD:
                            processAtChld(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST:
                            processSubscriberNumberRequest(event.device);
                            break;
                        case EVENT_TYPE_AT_CIND:
                            processAtCind(event.device);
                            break;
                        case EVENT_TYPE_AT_COPS:
                            processAtCops(event.device);
                            break;
                        case EVENT_TYPE_AT_CLCC:
                            processAtClcc(event.device);
                            break;
                        case EVENT_TYPE_UNKNOWN_AT:
                            processUnknownAt(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_KEY_PRESSED:
                            processKeyPressed(event.device);
                            break;
                        case EVENT_TYPE_BIND:
                            processAtBind(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_BIEV:
                            processAtBiev(event.valueInt, event.valueInt2, event.device);
                            break;
                        default:
                            Log.e(TAG, "Connected: Unknown stack event: " + event.type);
                            break;
                    }
                    break;
                default:
                    Log.e(TAG, "Connected: unexpected message " + message.what);
                    return NOT_HANDLED;
            }
            Log.d(TAG, "Exit Connected processMessage() ");
            return HANDLED;
        }

        // in Connected state
        private void processConnectionEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Connected: processConnectionEvent, state=" + state + ", device=" + device);
            switch (state) {
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        processWBSEvent(0, device); /* disable WBS audio parameters */
                        synchronized (HeadsetStateMachine.this) {
                            mConnectedDevicesList.remove(device);
                            mHeadsetAudioParam.remove(device);
                            mHeadsetBrsf.remove(device);
                            Log.d(TAG, "device " + device.getAddress()
                                            + " is removed in Connected state");

                            if (mConnectedDevicesList.size() == 0) {
                                mCurrentDevice = null;
                                transitionTo(mDisconnected);
                            } else {
                                processMultiHFDisconnect(device);
                            }
                        }
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTED);
                    } else {
                        Log.e(TAG, "Disconnected from unknown device: " + device);
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_SLC_CONNECTED:
                    if (mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Removing device " + device +
                                   " conn retry entry since we got SLC");
                        mRetryConnect.remove(device);
                    }
                    // Should have been rejected in CONNECTION_STATE_CONNECTED
                    if (okToConnect(device)
                            && (mConnectedDevicesList.size() < max_hf_connections)) {
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                BluetoothProfile.STATE_DISCONNECTED);
                        synchronized (HeadsetStateMachine.this) {
                            if (!mConnectedDevicesList.contains(device)) {
                                mCurrentDevice = device;
                                mConnectedDevicesList.add(device);
                                Log.d(TAG,
                                        "device " + device.getAddress()
                                                + " is added in Connected state");
                            }
                            transitionTo(mConnected);
                        }
                        configAudioParameters(device);
                    }
                    processSlcConnected();
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        mIncomingDevice = null;
                        mTargetDevice = null;
                        break;
                    }
                    Log.w(TAG, "HFP to be Connected in Connected state");
                    if (!okToConnect(device)
                            || (mConnectedDevicesList.size() >= max_hf_connections)) {
                        // reject the connection and stay in Connected state itself
                        Log.i(TAG, "Incoming Hf rejected. priority=" + mService.getPriority(device)
                                        + " bondState=" + device.getBondState());
                        disconnectHfpNative(getByteAddress(device));
                    }
                    break;
                default:
                    Log.e(TAG, "Connection State Device: " + device + " bad state: " + state);
                    break;
            }
            Log.d(TAG, "Exit Connected processConnectionEvent()");
        }

        // in Connected state
        private void processAudioEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Enter Connected processAudioEvent()");
            if (!mConnectedDevicesList.contains(device)) {
                Log.e(TAG, "Audio changed on disconnected device: " + device);
                return;
            }

            switch (state) {
                case HeadsetHalConstants.AUDIO_STATE_CONNECTED:
                    if (!isScoAcceptable()) {
                        Log.e(TAG, "Audio Connected without any listener");
                        disconnectAudioNative(getByteAddress(device));
                        break;
                    }

                    // TODO(BT) should I save the state for next broadcast as the prevState?
                    mAudioState = BluetoothHeadset.STATE_AUDIO_CONNECTED;
                    setAudioParameters(device); /*Set proper Audio Paramters.*/

                    // Start playing silence if VR or VOIP app is not opening playback session
                    // and selecting device for SCO Rx
                    if (((mVoiceRecognitionStarted && mPlaybackForVR) ||
                         (mVirtualCallStarted && mPlaybackForVOIP)) &&
                        (mAudioPlayer != null) &&
                        !mAudioPlayer.isPlaying()) {
                        Log.d(TAG, "VR or VOIP started, starting audio playback");
                        mAudioPlayer.start();
                    }

                    mAudioManager.setParameters("BT_SCO=on");
                    mAudioManager.setBluetoothScoOn(true);
                    mActiveScoDevice = device;
                    broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_CONNECTED,
                            BluetoothHeadset.STATE_AUDIO_CONNECTING);
                    if (!mPhoneState.getIsCsCall()) {
                        log("Sco connected for call other than CS, check network type");
                        sendVoipConnectivityNetworktype(true);
                    } else {
                        log("Sco connected for CS call, do not check network type");
                    }
                    //Reset SCO requested device
                    mScoRequestedDevice = null;
                    mLastScoDiscReqDevice = null;
                    transitionTo(mAudioOn);
                    break;
                case HeadsetHalConstants.AUDIO_STATE_CONNECTING:
                    mAudioState = BluetoothHeadset.STATE_AUDIO_CONNECTING;
                    broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_CONNECTING,
                            BluetoothHeadset.STATE_AUDIO_DISCONNECTED);
                    break;
                /* When VR is stopped before SCO creation is complete, we need
                   to resume A2DP if we had suspended it */
                case HeadsetHalConstants.AUDIO_STATE_DISCONNECTED:
                    //clear call info for VOIP calls when remote disconnects SCO
                    terminateScoUsingVirtualVoiceCall();

                    if (mA2dpSuspend) {
                        if ((!isInCall()) && (mPhoneState.getNumber().isEmpty())) {
                            log("Audio is closed,Set A2dpSuspended=false");
                            mAudioManager.setParameters("A2dpSuspended=false");
                            mA2dpSuspend = false;
                        }
                    }
                    break;
                    // TODO(BT) process other states
                default:
                    Log.e(TAG, "Audio State Device: " + device + " bad state: " + state);
                    break;
            }
            Log.d(TAG, "Exit Connected processAudioEvent()");
        }

        private void processSlcConnected() {
            Log.d(TAG, "Enter Connected processSlcConnected()");
            if (mPhoneProxy != null) {
                sendMessageDelayed(QUERY_PHONE_STATE_AT_SLC, QUERY_PHONE_STATE_CHANGED_DELAYED);
                mA2dpSuspend = false;/*Reset at SLC*/
                mPendingCiev = false;
                mPendingCallStates.clear();
                if ((isInCall()) && (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED)) {
                    if (DBG) {
                        log("Headset connected while we are in some call state");
                        log("Make A2dpSuspended=true here");
                    }
                    mAudioManager.setParameters("A2dpSuspended=true");
                    mA2dpSuspend = true;
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for query phone state");
            }
            // Checking for the Blacklisted device Addresses
            mIsBlacklistedDevice = isConnectedDeviceBlacklistedforIncomingCall();
            Log.d(TAG, "Exit Connected processSlcConnected()");
        }

        private void processMultiHFDisconnect(BluetoothDevice device) {
            Log.d(TAG, "Enter Connected processMultiHFDisconnect()");
            log("Connect state: processMultiHFDisconnect");
            if (mActiveScoDevice != null && mActiveScoDevice.equals(device)) {
                log("mActiveScoDevice is disconnected, setting it to null");
                mActiveScoDevice = null;
            }
            /* Assign the current activedevice again if the disconnected
                         device equals to the current active device */
            if (mCurrentDevice != null && mCurrentDevice.equals(device)) {
                transitionTo(mConnected);
                int deviceSize = mConnectedDevicesList.size();
                mCurrentDevice = mConnectedDevicesList.get(deviceSize - 1);
            } else {
                // The disconnected device is not current active device
                transitionTo(mConnected);
            }
            log("processMultiHFDisconnect , the latest mCurrentDevice is:" +
                                     mCurrentDevice);
            log("Connect state: processMultiHFDisconnect ," +
                       "fake broadcasting for mCurrentDevice");
            broadcastConnectionState(mCurrentDevice, BluetoothProfile.STATE_CONNECTED,
                    BluetoothProfile.STATE_DISCONNECTED);
            Log.d(TAG, "Exit Connected processMultiHFDisconnect()");
        }

    }

    private class AudioOn extends State {
        @Override
        public void enter() {
            Log.d(TAG, "Enter AudioOn: " + getCurrentMessage().what + ", size: "
                    + mConnectedDevicesList.size());
        }

        @Override
        public boolean processMessage(Message message) {
            Log.d(TAG, "AudioOn process message: " + message.what + ", size: "
                    + mConnectedDevicesList.size());
            BluetoothDevice device = null;
            switch (message.what) {
                case CONNECT: {
                    device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "AudioOn: CONNECT, device=" + device);
                    if (mConnectedDevicesList.contains(device)) {
                        Log.w(TAG, "AudioOn: CONNECT, device " + device + " is connected");
                        break;
                    }

                    if (max_hf_connections == 1) {
                        deferMessage(obtainMessage(DISCONNECT, mCurrentDevice));
                        deferMessage(obtainMessage(CONNECT, device));
                        if (disconnectAudioNative(getByteAddress(mCurrentDevice))) {
                            Log.d(TAG, "AudioOn: disconnecting SCO, device=" + mCurrentDevice);
                        } else {
                            Log.e(TAG, "AudioOn: disconnect SCO failed, device=" + mCurrentDevice);
                        }
                        break;
                    }

                    if (!mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Make conn retry entry for device " + device);
                        mRetryConnect.put(device, 0);
                    }

                    int RetryConn = mRetryConnect.get(device);
                    Log.d(TAG, "RetryConn = " + RetryConn);
                    if (RetryConn > 1) {
                        if (mRetryConnect.containsKey(device)) {
                            Log.d(TAG, "Removing device " + device +
                                  " conn retry entry since RetryConn = " + RetryConn);
                            mRetryConnect.remove(device);
                        }
                        break;
                    }

                    if (mConnectedDevicesList.size() >= max_hf_connections) {
                        BluetoothDevice disconnectDevice = mConnectedDevicesList.get(0);
                        Log.d(TAG, "AudioOn: Reach to max size, disconnect " + disconnectDevice);

                        if (mActiveScoDevice != null && mActiveScoDevice.equals(disconnectDevice)) {
                            disconnectDevice = mConnectedDevicesList.get(1);
                        }

                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                                BluetoothProfile.STATE_DISCONNECTED);

                        if (disconnectHfpNative(getByteAddress(disconnectDevice))) {
                            broadcastConnectionState(disconnectDevice,
                                    BluetoothProfile.STATE_DISCONNECTING,
                                    BluetoothProfile.STATE_CONNECTED);
                        } else {
                            Log.e(TAG, "AudioOn: Failed to disconnect " + disconnectDevice);
                            broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                            break;
                        }

                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = device;
                            mMultiDisconnectDevice = disconnectDevice;
                            transitionTo(mMultiHFPending);
                        }
                    } else if (mConnectedDevicesList.size() < max_hf_connections) {
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTING,
                                BluetoothProfile.STATE_DISCONNECTED);
                        if (!connectHfpNative(getByteAddress(device))) {
                            broadcastConnectionState(device,
                                    BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                            break;
                        }
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = device;
                            // Transtion to MultilHFPending state for Multi handsfree connection
                            transitionTo(mMultiHFPending);
                        }
                    }
                    RetryConn = RetryConn + 1;
                    mRetryConnect.put(device, RetryConn);
                    Message m = obtainMessage(CONNECT_TIMEOUT);
                    m.obj = device;
                    sendMessageDelayed(m, CONNECT_TIMEOUT_MILLIS);
                } break;
                case CONNECT_TIMEOUT:
                    onConnectionStateChanged(HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED,
                            getByteAddress(mTargetDevice));
                    break;
                case DISCONNECT: {
                    device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "AudioOn: DISCONNECT, device=" + device);
                    if (!mConnectedDevicesList.contains(device)) {
                        Log.w(TAG, "AudioOn: DISCONNECT, device " + device + " not connected");
                        break;
                    }
                    if (mActiveScoDevice != null && mActiveScoDevice.equals(device)) {
                        // The disconnected device is active SCO device
                        Log.d(TAG, "AudioOn, DISCONNECT mActiveScoDevice=" + mActiveScoDevice);
                        deferMessage(obtainMessage(DISCONNECT, message.obj));
                        // Disconnect BT SCO first
                        if (disconnectAudioNative(getByteAddress(mActiveScoDevice))) {
                            log("Disconnecting SCO audio");
                        } else {
                            Log.w(TAG, "AudioOn, DISCONNECT failed, device=" + mActiveScoDevice);
                            // if disconnect BT SCO failed, transition to mConnected state
                            transitionTo(mConnected);
                        }
                    } else {
                        /* Do not disconnect BT SCO if the disconnected
                           device is not active SCO device */
                        Log.d(TAG, "AudioOn, DISCONNECT, none active SCO device=" + device);
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTING,
                                BluetoothProfile.STATE_CONNECTED);
                        // Should be still in AudioOn state
                        if (!disconnectHfpNative(getByteAddress(device))) {
                            Log.w(TAG, "AudioOn, DISCONNECT failed, device=" + device);
                            broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                    BluetoothProfile.STATE_DISCONNECTING);
                            break;
                        }
                        /* Transtion to MultiHFPending state for Multi handsfree connection */
                        if (mConnectedDevicesList.size() > 1) {
                            mMultiDisconnectDevice = device;
                            transitionTo(mMultiHFPending);
                        }
                    }
                } break;
                case DISCONNECT_AUDIO:
                    device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "Audioon: Disconnect_audio device " + device +
                       "ActiveScoDevice" + mActiveScoDevice);
                    if (mActiveScoDevice != null) {
                        if (disconnectAudioNative(getByteAddress(mActiveScoDevice))) {
                            Log.d(TAG, "AudioOn: DISCONNECT_AUDIO, device=" + mActiveScoDevice);
                        } else {
                            Log.e(TAG,
                                    "AudioOn: DISCONNECT_AUDIO failed, device=" + mActiveScoDevice);
                        }
                    } else {
                        Log.w(TAG, "AudioOn: DISCONNECT_AUDIO, mActiveScoDevice is null");
                        mLastScoDiscReqDevice = mActiveScoDevice;
                    }
                    break;
                case VOICE_RECOGNITION_START:
                    processLocalVrEvent(HeadsetHalConstants.VR_STATE_STARTED);
                    break;
                case VOICE_RECOGNITION_STOP:
                    processLocalVrEvent(HeadsetHalConstants.VR_STATE_STOPPED);
                    break;
                case INTENT_SCO_VOLUME_CHANGED:
                    if (mActiveScoDevice != null) {
                        processIntentScoVolume((Intent) message.obj, mActiveScoDevice);
                    }
                    break;
                case VOIP_CALL_STATE_CHANGED_ALERTING:
                    // intentional fall through
                case VOIP_CALL_STATE_CHANGED_ACTIVE:
                    processCallState((HeadsetCallState) message.obj, message.arg1 == 1);
                    break;
                case CALL_STATE_CHANGED:
                {
                    boolean isPts = SystemProperties.getBoolean("bt.pts.certification", false);

                    // for PTS, VOIP calls, send the indicators as is
                    if(isPts || isVirtualCallInProgress())
                        processCallState((HeadsetCallState) message.obj,
                                           ((message.arg1==1)?true:false));
                    else
                        processCallStatesDelayed((HeadsetCallState) message.obj, false);
                    break;
                }
                case CS_CALL_STATE_CHANGED_ALERTING:
                {
                    // get the top of the Q
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    // top of the queue == call alerting
                    if( tempCallState != null &&
                            tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
                    {
                        Log.d(TAG, "alerting message timer expired, send alerting update");
                        //dequeue the alerting call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }

                    // top of the queue == call active
                    tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                         tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "alerting message timer expired, send delayed active mesg");
                        //send delayed message for call active;
                        Message msg = obtainMessage(CS_CALL_STATE_CHANGED_ACTIVE);
                        msg.arg1 = 0;
                        sendMessageDelayed(msg, CS_CALL_ACTIVE_DELAY_TIME_MSEC);
                    }
                    break;
                }
                case CS_CALL_STATE_CHANGED_ACTIVE:
                {
                    // get the top of the Q
                    // top of the queue == call active
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                          tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "active message timer expired, send active update");
                        //dequeue the active call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }
                    break;
                }
                case INTENT_BATTERY_CHANGED:
                    processIntentBatteryChanged((Intent) message.obj);
                    break;
                case DEVICE_STATE_CHANGED:
                    processDeviceStateChanged((HeadsetDeviceState) message.obj);
                    break;
                case SEND_CCLC_RESPONSE:
                    processSendClccResponse((HeadsetClccResponse) message.obj);
                    break;
                case CLCC_RSP_TIMEOUT: {
                    device = (BluetoothDevice) message.obj;
                    if (device != null)
                        clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
                    break;
                }
                case SEND_VENDOR_SPECIFIC_RESULT_CODE:
                    processSendVendorSpecificResultCode(
                            (HeadsetVendorSpecificResultCode) message.obj);
                    break;

                case VIRTUAL_CALL_START:
                    initiateScoUsingVirtualVoiceCall();
                    break;
                case VIRTUAL_CALL_STOP:
                    terminateScoUsingVirtualVoiceCall();
                    break;
                case UPDATE_A2DP_PLAY_STATE:
                    processIntentA2dpPlayStateChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_CONN_STATE:
                    processIntentA2dpStateChanged((Intent) message.obj);
                    break;
                case UPDATE_CALL_TYPE:
                    processIntentUpdateCallType((Intent) message.obj);
                    break;
                case DIALING_OUT_TIMEOUT:
                {
                    Log.d(TAG, "mDialingOut is " + mDialingOut);
                    if (mDialingOut) {
                        device = (BluetoothDevice)message.obj;
                        Log.d(TAG, "Timeout waiting for call to be placed, resetting mDialingOut");
                        mDialingOut= false;
                        atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR,
                                               0, getByteAddress(device));
                    }
                    break;
                }
                case ENABLE_WBS:
                {
                    device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device),WBS_CODEC);
                }
                    break;
                case DISABLE_WBS:
                {
                    device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device),NBS_CODEC);
                }
                    break;
                case START_VR_TIMEOUT:
                {
                    if (mWaitingForVoiceRecognition) {
                        device = (BluetoothDevice) message.obj;
                        mWaitingForVoiceRecognition = false;
                        Log.e(TAG, "Timeout waiting for voice recognition"
                                        + "to start");
                        atResponseCodeNative(
                                HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                    }
                    break;
                }
                case PROCESS_CPBR:
                    Intent intent = (Intent) message.obj;
                    processCpbr(intent);
                    break;
                case SEND_INCOMING_CALL_IND:
                    phoneStateChangeNative(0, 0, HeadsetHalConstants.CALL_STATE_INCOMING,
                                       mPhoneState.getNumber(), mPhoneState.getType());
                    break;
                case AUDIO_SERVER_RESTARTED:
                    processAudioServerRestarted();
                    break;
                case QUERY_PHONE_STATE_AT_SLC:
                    try {
                       log("Update call states after SLC is up");
                       mPhoneProxy.queryPhoneState();
                    } catch (RemoteException e) {
                       Log.e(TAG, Log.getStackTraceString(new Throwable()));
                    }
                    break;
                case STACK_EVENT:
                    StackEvent event = (StackEvent) message.obj;
                    Log.d(TAG, "AudioOn: event type: " + event.type);
                    switch (event.type) {
                        case EVENT_TYPE_CONNECTION_STATE_CHANGED:
                            processConnectionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AUDIO_STATE_CHANGED:
                            processAudioEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_VR_STATE_CHANGED:
                            processVrEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_ANSWER_CALL:
                            processAnswerCall(event.device);
                            break;
                        case EVENT_TYPE_HANGUP_CALL:
                            processHangupCall(event.device);
                            break;
                        case EVENT_TYPE_VOLUME_CHANGED:
                            processVolumeEvent(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_DIAL_CALL:
                            processDialCall(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_SEND_DTMF:
                            processSendDtmf(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_NOICE_REDUCTION:
                            processNoiceReductionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_WBS:
                            Log.d(TAG, "EVENT_TYPE_WBS codec is " + event.valueInt);
                            processWBSEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AT_CHLD:
                            processAtChld(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST:
                            processSubscriberNumberRequest(event.device);
                            break;
                        case EVENT_TYPE_AT_CIND:
                            processAtCind(event.device);
                            break;
                        case EVENT_TYPE_AT_COPS:
                            processAtCops(event.device);
                            break;
                        case EVENT_TYPE_AT_CLCC:
                            processAtClcc(event.device);
                            break;
                        case EVENT_TYPE_UNKNOWN_AT:
                            processUnknownAt(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_KEY_PRESSED:
                            processKeyPressed(event.device);
                            break;
                        case EVENT_TYPE_BIND:
                            processAtBind(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_BIEV:
                            processAtBiev(event.valueInt, event.valueInt2, event.device);
                            break;
                        default:
                            Log.e(TAG, "AudioOn: Unknown stack event: " + event.type);
                            break;
                    }
                    break;
                default:
                    Log.e(TAG, "AudioOn: unexpected message " + message.what);
                    return NOT_HANDLED;
            }
            Log.d(TAG, " Exit AudioOn processMessage() ");
            return HANDLED;
        }

        // in AudioOn state. Some headsets disconnect RFCOMM prior to SCO down. Handle this
        private void processConnectionEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "AudioOn: processConnectionEvent, state=" + state + ", device=" + device);
            Log.d(TAG, "mActiveScoDevice state = " + state + ", device = " + mActiveScoDevice);
            BluetoothDevice pendingDevice = getDeviceForMessage(CONNECT_TIMEOUT);
            switch (state) {
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        if (mActiveScoDevice != null && mActiveScoDevice.equals(device)
                                && mAudioState != BluetoothHeadset.STATE_AUDIO_DISCONNECTED) {
                            processAudioEvent(HeadsetHalConstants.AUDIO_STATE_DISCONNECTED, device);
                        }

                        synchronized (HeadsetStateMachine.this) {
                            /* send wbs off to audio manager only when last active
                               sco device is disconnected */
                            if (mConnectedDevicesList.size() == 1) {
                                processWBSEvent(0, device); /* disable WBS audio parameters */
                                Log.d(TAG, "update audiomgr only when last device disconnected");
                            }
                            mConnectedDevicesList.remove(device);
                            mHeadsetAudioParam.remove(device);
                            mHeadsetBrsf.remove(device);
                            Log.d(TAG, "device " + device.getAddress()
                                            + " is removed in AudioOn state");
                            broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                                     BluetoothProfile.STATE_CONNECTED);
                            if (mConnectedDevicesList.size() == 0) {
                                transitionTo(mDisconnected);
                            } else {
                                processMultiHFDisconnect(device);
                            }
                        }
                    } else {
                        Log.e(TAG, "Disconnected from unknown device: " + device);
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_SLC_CONNECTED:
                    if (mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Removing device " + device +
                                   " conn retry entry since we got SLC");
                        mRetryConnect.remove(device);
                    }
                    // Should have been rejected in CONNECTION_STATE_CONNECTED
                    if (okToConnect(device)
                            && (mConnectedDevicesList.size() < max_hf_connections)) {
                        Log.i(TAG, "AudioOn: accepted incoming HF");
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                BluetoothProfile.STATE_DISCONNECTED);
                        synchronized (HeadsetStateMachine.this) {
                            if (!mConnectedDevicesList.contains(device)) {
                                mCurrentDevice = device;
                                mConnectedDevicesList.add(device);
                                Log.d(TAG,
                                        "device " + device.getAddress()
                                                + " is added in AudioOn state");
                            }
                        }
                        configAudioParameters(device);
                    }
                    processSlcConnected();
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        mIncomingDevice = null;
                        mTargetDevice = null;
                        break;
                    }
                    Log.w(TAG, "AudioOn: HFP to be connected device=" + device);
                    if (!okToConnect(device)
                            || (mConnectedDevicesList.size() >= max_hf_connections)) {
                        // reject the connection and stay in Connected state itself
                        Log.i(TAG,
                                "AudioOn: rejected incoming HF, priority="
                                        + mService.getPriority(device)
                                        + " bondState=" + device.getBondState());
                        disconnectHfpNative(getByteAddress(device));
                    } else {
                        // Do nothing in normal case, wait for SLC connected event
                        pendingDevice = null;
                    }
                    break;
                default:
                    Log.e(TAG, "Connection State Device: " + device + " bad state: " + state);
                    break;
            }
            if (pendingDevice != null && pendingDevice.equals(device)) {
                removeMessages(CONNECT_TIMEOUT);
                Log.d(TAG, "AudioOn: removed CONNECT_TIMEOUT for device=" + pendingDevice);
            }
            Log.d(TAG, "Exit AudioOn processConnectionEvent()");
        }

        // in AudioOn state
        private void processAudioEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Enter AudioOn processAudioEvent()");
            if (!mConnectedDevicesList.contains(device)) {
                Log.e(TAG, "Audio changed on disconnected device: " + device);
                return;
            }

            switch (state) {
                case HeadsetHalConstants.AUDIO_STATE_DISCONNECTED:
                    mActiveScoDevice = null;
                    if (mAudioState != BluetoothHeadset.STATE_AUDIO_DISCONNECTED) {
                        mAudioState = BluetoothHeadset.STATE_AUDIO_DISCONNECTED;
                        if (device.equals(mActiveScoDevice)) {
                            mActiveScoDevice = null;
                        }
                        if (mAudioManager.isSpeakerphoneOn()) {
                            // User option might be speaker as sco disconnection
                            // is delayed setting back the speaker option.
                            mAudioManager.setParameters("BT_SCO=off");
                            mAudioManager.setBluetoothScoOn(false);
                            mAudioManager.setSpeakerphoneOn(true);
                        } else {
                            mAudioManager.setParameters("BT_SCO=off");
                            mAudioManager.setBluetoothScoOn(false);
                        }
                        //clear call info for VOIP calls when remote disconnects SCO
                        terminateScoUsingVirtualVoiceCall();

                        if (mA2dpSuspend) {
                            if ((!isInCall()) && (mPhoneState.getNumber().isEmpty())) {
                                log("Audio is closed,Set A2dpSuspended=false");
                                mAudioManager.setParameters("A2dpSuspended=false");
                                mA2dpSuspend = false;
                            }
                        }
                        if (!mPhoneState.getIsCsCall()) {
                            log("Sco disconnected for call other than CS, check network type");
                            sendVoipConnectivityNetworktype(false);
                            mPhoneState.setIsCsCall(true);
                        } else {
                            log("Sco disconnected for CS call, do not check network type");
                        }

                        if ((mPlaybackForVR || mPlaybackForVOIP) &&
                            (mAudioPlayer != null) &&
                            mAudioPlayer.isPlaying()) {
                            Log.d(TAG, "SCO disconnected, stop audio playback");
                            mAudioPlayer.stop();
                        }
                        broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_DISCONNECTED,
                                BluetoothHeadset.STATE_AUDIO_CONNECTED);
                    }
                    transitionTo(mConnected);
                    break;
                case HeadsetHalConstants.AUDIO_STATE_DISCONNECTING:
                    // TODO(BT) adding STATE_AUDIO_DISCONNECTING in BluetoothHeadset?
                    // broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_DISCONNECTING,
                    //                    BluetoothHeadset.STATE_AUDIO_CONNECTED);
                    break;
                default:
                    Log.e(TAG, "Audio State Device: " + device + " bad state: " + state);
                    break;
            }
            Log.d(TAG, "Exit AudioOn processAudioEvent()");
        }

        private void processSlcConnected() {
            Log.d(TAG, "Enter AudioOn processSlcConnected()");
            if (mPhoneProxy != null) {
                try {
                    mPhoneProxy.queryPhoneState();
                } catch (RemoteException e) {
                    Log.e(TAG, Log.getStackTraceString(new Throwable()));
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for query phone state");
            }
            Log.d(TAG, "Exit AudioOn processSlcConnected()");
        }

        private void processIntentScoVolume(Intent intent, BluetoothDevice device) {
            Log.d(TAG, "Enter AudioOn processIntentScoVolume()");
            int volumeValue = intent.getIntExtra(AudioManager.EXTRA_VOLUME_STREAM_VALUE, 0);
            if (mPhoneState.getSpeakerVolume() != volumeValue) {
                mPhoneState.setSpeakerVolume(volumeValue);
            boolean scoVolume =
                    SystemProperties.getBoolean("bt.pts.certification", false);
                if (!scoVolume) {
                    setVolumeNative(HeadsetHalConstants.VOLUME_TYPE_SPK,
                                        volumeValue, getByteAddress(device));
                } else {
                    setVolumeNative(HeadsetHalConstants.VOLUME_TYPE_SPK,
                                        0, getByteAddress(device));
                }
            }
            Log.d(TAG, "Exit AudioOn processIntentScoVolume()");
        }

        private void processMultiHFDisconnect(BluetoothDevice device) {
            Log.d(TAG, "Enter AudioOn processMultiHFDisconnect()");
            log("AudioOn state: processMultiHFDisconnect");
            /* Assign the current activedevice again if the disconnected
                          device equals to the current active device */
            if (mCurrentDevice != null && mCurrentDevice.equals(device)) {
                int deviceSize = mConnectedDevicesList.size();
                mCurrentDevice = mConnectedDevicesList.get(deviceSize - 1);
            }
            if (mAudioState != BluetoothHeadset.STATE_AUDIO_CONNECTED) transitionTo(mConnected);

            log("processMultiHFDisconnect , the latest mCurrentDevice is:"
                                      + mCurrentDevice);
            log("AudioOn state: processMultiHFDisconnect ," +
                       "fake broadcasting for mCurrentDevice");
            broadcastConnectionState(mCurrentDevice, BluetoothProfile.STATE_CONNECTED,
                    BluetoothProfile.STATE_DISCONNECTED);
            Log.d(TAG, "Exit AudioOn processMultiHFDisconnect()");
        }
    }

    /* Add MultiHFPending state when atleast 1 HS is connected
            and disconnect/connect new HS */
    private class MultiHFPending extends State {
        @Override
        public void enter() {
            Log.d(TAG, "Enter MultiHFPending: " + getCurrentMessage().what +
                         ", size: " + mConnectedDevicesList.size());
        }

        @Override
        public boolean processMessage(Message message) {
            Log.d(TAG, " Enter MultiHFPending process message: " + message.what +
                         ", size: " + mConnectedDevicesList.size());
            BluetoothDevice device = null;
            switch (message.what) {
                case CONNECT:
                    deferMessage(message);
                    break;

                case CONNECT_AUDIO:
                    device = mCurrentDevice;
                    if (mLastScoDiscReqDevice != null) {
                        Log.d(TAG, "Last SCO Discon Requested device is" + mLastScoDiscReqDevice);
                        device = mLastScoDiscReqDevice;
                        mLastScoDiscReqDevice = null;
                    }

                    if (mScoRequestedDevice != null) {
                        Log.d(TAG, "MHF: SCO Requested device is" + mScoRequestedDevice);
                        device = mScoRequestedDevice;
                        mScoRequestedDevice = null;
                    }

                    if (device != null) {
                        Log.d(TAG, "Calling ConnectAudioNative with " + device);
                        connectAudioNative(getByteAddress(device));
                    }
                    break;
                case CONNECT_TIMEOUT:
                    onConnectionStateChanged(HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED,
                            getByteAddress(mTargetDevice));
                    break;

                case DISCONNECT_AUDIO:
                    device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "MHF: DISCONNECT_REQ: " + device + " ActiveScoDevice: " + mActiveScoDevice);
                    if (mActiveScoDevice != null) {
                        if (disconnectAudioNative(getByteAddress(mActiveScoDevice))) {
                            Log.d(TAG, "MultiHFPending, Disconnecting SCO audio for "
                                            + mActiveScoDevice);
                        } else {
                            Log.e(TAG, "disconnectAudioNative failed"
                                            + "for device = " + mActiveScoDevice);
                        }
                        //Rememebr the Last Disc req sent Device
                        mLastScoDiscReqDevice = mActiveScoDevice;
                    }
                    break;
                case DISCONNECT:
                    device = (BluetoothDevice) message.obj;
                    Log.d(TAG, "MultiPending: DISCONNECT, device=" + device);
                    if (mConnectedDevicesList.contains(device) && mTargetDevice != null
                            && mTargetDevice.equals(device)) {
                        // cancel connection to the mTargetDevice
                        broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                        }
                    } else {
                        deferMessage(message);
                    }
                    break;
                case VOICE_RECOGNITION_START:
                    device = (BluetoothDevice) message.obj;
                    if (mConnectedDevicesList.contains(device)) {
                        processLocalVrEvent(HeadsetHalConstants.VR_STATE_STARTED);
                    }
                    break;
                case VOICE_RECOGNITION_STOP:
                    device = (BluetoothDevice) message.obj;
                    if (mConnectedDevicesList.contains(device)) {
                        processLocalVrEvent(HeadsetHalConstants.VR_STATE_STOPPED);
                    }
                    break;
                case INTENT_SCO_VOLUME_CHANGED:
                    if (mActiveScoDevice != null) {
                        processIntentScoVolume((Intent) message.obj, mActiveScoDevice);
                    }
                    break;
                case INTENT_BATTERY_CHANGED:
                    processIntentBatteryChanged((Intent) message.obj);
                    break;
                case VOIP_CALL_STATE_CHANGED_ALERTING:
                    // intentional fall through
                case VOIP_CALL_STATE_CHANGED_ACTIVE:
                    processCallState((HeadsetCallState) message.obj, message.arg1 == 1);
                    break;
                case CALL_STATE_CHANGED:
                {
                    boolean isPts = SystemProperties.getBoolean("bt.pts.certification", false);

                    // for PTS, VOIP calls, send the indicators as is
                    if(isPts || isVirtualCallInProgress())
                        processCallState((HeadsetCallState) message.obj,
                                          ((message.arg1==1)?true:false));
                    else
                        processCallStatesDelayed((HeadsetCallState) message.obj, false);
                    break;
                }
                case CS_CALL_STATE_CHANGED_ALERTING:
                {
                    // get the top of the Q
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    // top of the queue == call alerting
                    if( tempCallState != null &&
                         tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
                    {
                        Log.d(TAG, "alerting message timer expired, send alerting update");
                        //dequeue the alerting call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }

                    // top of the queue == call active
                    tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                         tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "alerting message timer expired, send delayed active mesg");
                        //send delayed message for call active;
                        Message msg = obtainMessage(CS_CALL_STATE_CHANGED_ACTIVE);
                        msg.arg1 = 0;
                        sendMessageDelayed(msg, CS_CALL_ACTIVE_DELAY_TIME_MSEC);
                    }
                    break;
                }
                case CS_CALL_STATE_CHANGED_ACTIVE:
                {
                    // get the top of the Q
                    // top of the queue == call active
                    HeadsetCallState tempCallState = mDelayedCSCallStates.peek();
                    if (tempCallState != null &&
                          tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
                    {
                        Log.d(TAG, "active message timer expired, send active update");
                        //dequeue the active call state;
                        mDelayedCSCallStates.poll();
                        processCallState(tempCallState, false);
                    }
                    break;
                }
                case DEVICE_STATE_CHANGED:
                    processDeviceStateChanged((HeadsetDeviceState) message.obj);
                    break;
                case SEND_CCLC_RESPONSE:
                    processSendClccResponse((HeadsetClccResponse) message.obj);
                    break;
                case CLCC_RSP_TIMEOUT: {
                    device = (BluetoothDevice) message.obj;
                    if (device != null)
                        clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
                } break;
                case UPDATE_A2DP_PLAY_STATE:
                    processIntentA2dpPlayStateChanged((Intent) message.obj);
                    break;
                case UPDATE_A2DP_CONN_STATE:
                    processIntentA2dpStateChanged((Intent) message.obj);
                    break;
                case UPDATE_CALL_TYPE:
                    processIntentUpdateCallType((Intent) message.obj);
                    break;
                case DIALING_OUT_TIMEOUT:
                    Log.d(TAG, "mDialingOut is " + mDialingOut);
                    if (mDialingOut) {
                        device = (BluetoothDevice) message.obj;
                        Log.d(TAG, "Timeout waiting for call to be placed, resetting mDialingOut");
                        mDialingOut= false;
                        atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR,
                                             0, getByteAddress(device));
                    }
                    break;
                case VIRTUAL_CALL_START:
                    device = (BluetoothDevice) message.obj;
                    if (mConnectedDevicesList.contains(device)) {
                        initiateScoUsingVirtualVoiceCall();
                    }
                    break;
                case VIRTUAL_CALL_STOP:
                    device = (BluetoothDevice) message.obj;
                    if (mConnectedDevicesList.contains(device)) {
                        terminateScoUsingVirtualVoiceCall();
                    }
                    break;
                case ENABLE_WBS:
                {
                    device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device),WBS_CODEC);
                }
                    break;
                case DISABLE_WBS:
                {
                    device = (BluetoothDevice) message.obj;
                    configureWBSNative(getByteAddress(device),NBS_CODEC);
                }
                    break;
                case START_VR_TIMEOUT:
                    if (mWaitingForVoiceRecognition) {
                        device = (BluetoothDevice) message.obj;
                        mWaitingForVoiceRecognition = false;
                        Log.e(TAG, "Timeout waiting for voice"
                                        + "recognition to start");
                        atResponseCodeNative(
                                HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                    }
                    break;
                case QUERY_PHONE_STATE_AT_SLC:
                    try {
                        log("Update call states after SLC is up");
                        mPhoneProxy.queryPhoneState();
                    } catch (RemoteException e) {
                        Log.e(TAG, Log.getStackTraceString(new Throwable()));
                    }
                    break;
                case PROCESS_CPBR:
                    Intent intent = (Intent) message.obj;
                    processCpbr(intent);
                    break;
                case STACK_EVENT:
                    StackEvent event = (StackEvent) message.obj;
                    log("MultiHFPending: event type: " + event.type);
                    switch (event.type) {
                        case EVENT_TYPE_CONNECTION_STATE_CHANGED:
                            processConnectionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AUDIO_STATE_CHANGED:
                            processAudioEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_VR_STATE_CHANGED:
                            processVrEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_ANSWER_CALL:
                            // TODO(BT) could answer call happen on Connected state?
                            processAnswerCall(event.device);
                            break;
                        case EVENT_TYPE_HANGUP_CALL:
                            // TODO(BT) could hangup call happen on Connected state?
                            processHangupCall(event.device);
                            break;
                        case EVENT_TYPE_VOLUME_CHANGED:
                            processVolumeEvent(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_DIAL_CALL:
                            processDialCall(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_SEND_DTMF:
                            processSendDtmf(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_NOICE_REDUCTION:
                            processNoiceReductionEvent(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST:
                            processSubscriberNumberRequest(event.device);
                            break;
                        case EVENT_TYPE_AT_CIND:
                            processAtCind(event.device);
                            break;
                        case EVENT_TYPE_AT_CHLD:
                            processAtChld(event.valueInt, event.device);
                            break;
                        case EVENT_TYPE_AT_COPS:
                            processAtCops(event.device);
                            break;
                        case EVENT_TYPE_AT_CLCC:
                            processAtClcc(event.device);
                            break;
                        case EVENT_TYPE_UNKNOWN_AT:
                            processUnknownAt(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_KEY_PRESSED:
                            processKeyPressed(event.device);
                            break;
                        case EVENT_TYPE_BIND:
                            processAtBind(event.valueString, event.device);
                            break;
                        case EVENT_TYPE_BIEV:
                            processAtBiev(event.valueInt, event.valueInt2, event.device);
                            break;
                        case EVENT_TYPE_WBS:
                            Log.d(TAG, "MHF: EVENT_TYPE_WBS codec is " + event.valueInt);
                            processWBSEvent(event.valueInt, event.device);
                            break;
                        default:
                            Log.e(TAG, "MultiHFPending: Unexpected event: " + event.type);
                            break;
                    }
                    break;
                default:
                    Log.e(TAG, "MultiHFPending: unexpected message " + message.what);
                    return NOT_HANDLED;
            }
            Log.d(TAG, " Exit MultiHFPending processMessage() ");
            return HANDLED;
        }

        // in MultiHFPending state
        private void processConnectionEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Enter MultiHFPending processConnectionEvent()");
            Log.d(TAG,
                    "MultiPending: processConnectionEvent, state=" + state + ", device=" + device);
            BluetoothDevice pendingDevice = getDeviceForMessage(CONNECT_TIMEOUT);
            switch (state) {
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        if (mMultiDisconnectDevice != null
                                && mMultiDisconnectDevice.equals(device)) {
                            mMultiDisconnectDevice = null;

                            synchronized (HeadsetStateMachine.this) {
                                mConnectedDevicesList.remove(device);
                                mHeadsetAudioParam.remove(device);
                                mHeadsetBrsf.remove(device);
                                Log.d(TAG, "MultiHFPending: removed device=" + device);
                                broadcastConnectionState(device,
                                        BluetoothProfile.STATE_DISCONNECTED,
                                        BluetoothProfile.STATE_DISCONNECTING);
                            }

                            if (mTargetDevice != null) {
                                if (!connectHfpNative(getByteAddress(mTargetDevice))) {
                                    broadcastConnectionState(mTargetDevice,
                                            BluetoothProfile.STATE_DISCONNECTED,
                                            BluetoothProfile.STATE_CONNECTING);
                                    synchronized (HeadsetStateMachine.this) {
                                        mTargetDevice = null;
                                        if (mConnectedDevicesList.size() == 0) {
                                            // Should be not in this state since it has at least
                                            // one HF connected in MultiHFPending state
                                            Log.w(TAG, "MultiHFPending: should not be here");
                                            transitionTo(mDisconnected);
                                        } else {
                                            processMultiHFDisconnect(device);
                                        }
                                    }
                                }
                            } else {
                                synchronized (HeadsetStateMachine.this) {
                                    mIncomingDevice = null;
                                    if (mConnectedDevicesList.size() == 0) {
                                        transitionTo(mDisconnected);
                                    } else {
                                        processMultiHFDisconnect(device);
                                    }
                                }
                            }
                        } else {
                            /* Another HF disconnected when one HF is connecting */
                            synchronized (HeadsetStateMachine.this) {
                                mConnectedDevicesList.remove(device);
                                mHeadsetAudioParam.remove(device);
                                mHeadsetBrsf.remove(device);
                                Log.d(TAG, "device " + device.getAddress()
                                                + " is removed in MultiHFPending state");
                            }
                            broadcastConnectionState(device, BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTED);
                        }
                    } else if (mTargetDevice != null && mTargetDevice.equals(device)) {
                        if (mRetryConnect.containsKey(mTargetDevice)) {
                            // retry again only if we tried once for non-blacklisted devices
                            if (mRetryConnect.get(device) == 1 &&
                                  !isDeviceBlacklistedforConnectionRetry(device)) {
                                Log.d(TAG, "Retry outgoing conn again for device = " + mTargetDevice
                                      + " after " + RETRY_CONNECT_TIME_SEC + "msec");
                                Message m = obtainMessage(CONNECT);
                                m.obj = device;
                                sendMessageDelayed(m, RETRY_CONNECT_TIME_SEC);
                            } else {
                                Log.d(TAG, "Removing conn retry entry for device = " +
                                      mTargetDevice);
                                mRetryConnect.remove(mTargetDevice);
                            }
                        }
                        broadcastConnectionState(mTargetDevice, BluetoothProfile.STATE_DISCONNECTED,
                                BluetoothProfile.STATE_CONNECTING);
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                            if (mConnectedDevicesList.size() == 0) {
                                transitionTo(mDisconnected);
                            } else {
                                if (mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED)
                                    transitionTo(mAudioOn);
                                else
                                    transitionTo(mConnected);
                            }
                        }
                    } else {
                        Log.e(TAG, "Unknown device Disconnected: " + device);
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTED:
                    if (mConnectedDevicesList.contains(device)) {
                        // Disconnection failure does not go through SLC establishment
                        Log.w(TAG, "MultiPending: disconnection failed for device " + device);
                        broadcastConnectionState(device, BluetoothProfile.STATE_CONNECTED,
                                BluetoothProfile.STATE_DISCONNECTING);
                        if (mTargetDevice != null) {
                            broadcastConnectionState(mTargetDevice,
                                    BluetoothProfile.STATE_DISCONNECTED,
                                    BluetoothProfile.STATE_CONNECTING);
                        }
                        synchronized (HeadsetStateMachine.this) {
                            mTargetDevice = null;
                            if (mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED)
                                transitionTo(mAudioOn);
                            else
                                transitionTo(mConnected);
                        }
                    } else if (!device.equals(mTargetDevice)) {
                        Log.w(TAG,
                                "MultiPending: unknown incoming HF connected on RFCOMM"
                                        + ", device=" + device);
                        if (!okToConnect(device)
                                || (mConnectedDevicesList.size() >= max_hf_connections)) {
                            // reject the connection and stay in Pending state itself
                            Log.i(TAG,
                                    "MultiPending: unknown incoming HF rejected on RFCOMM"
                                            + ", priority=" + mService.getPriority(device)
                                            + ", bondState=" + device.getBondState());
                            disconnectHfpNative(getByteAddress(device));
                        } else {
                            // Ok to connect, keep waiting for SLC connected event
                            pendingDevice = null;
                        }
                    } else {
                        // Do nothing in normal case, keep waiting for SLC connected event
                        pendingDevice = null;
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_SLC_CONNECTED:
                    if (mRetryConnect.containsKey(device)) {
                        Log.d(TAG, "Removing device " + device +
                                   " conn retry entry since we got SLC");
                         mRetryConnect.remove(device);
                    }
                    int previousConnectionState = BluetoothProfile.STATE_CONNECTING;
                    synchronized (HeadsetStateMachine.this) {
                        mCurrentDevice = device;
                        mConnectedDevicesList.add(device);
                        if (device.equals(mTargetDevice)) {
                            Log.d(TAG,
                                    "MultiPending: added " + device
                                            + " to mConnectedDevicesList, requested by us");
                            mTargetDevice = null;
                            if (mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED)
                                transitionTo(mAudioOn);
                            else
                                transitionTo(mConnected);
                        } else {
                            Log.d(TAG,
                                    "MultiPending: added " + device
                                            + "to mConnectedDevicesList, unknown source");
                            previousConnectionState = BluetoothProfile.STATE_DISCONNECTED;
                        }
                    }
                    configAudioParameters(device);
                    processSlcConnected();
                    broadcastConnectionState(
                            device, BluetoothProfile.STATE_CONNECTED, previousConnectionState);
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_CONNECTING:
                    if (mConnectedDevicesList.contains(device)) {
                        Log.e(TAG, "MultiPending: current device tries to connect back");
                    } else if (mTargetDevice != null && mTargetDevice.equals(device)) {
                        log("Stack and target device are connecting");
                    } else if (mIncomingDevice != null && mIncomingDevice.equals(device)) {
                        Log.e(TAG, "MultiPending: Another connecting event on the incoming device");
                    }
                    break;
                case HeadsetHalConstants.CONNECTION_STATE_DISCONNECTING:
                    if (mConnectedDevicesList.contains(device)) {
                        log("stack is disconnecting mCurrentDevice");
                    } else if (mTargetDevice != null && mTargetDevice.equals(device)) {
                        Log.e(TAG, "MultiPending: TargetDevice is getting disconnected");
                    } else if (mIncomingDevice != null && mIncomingDevice.equals(device)) {
                        Log.e(TAG, "MultiPending: IncomingDevice is getting disconnected");
                    } else {
                        Log.e(TAG, "MultiPending: Disconnecting unknow device: " + device);
                    }
                    break;
                default:
                    Log.e(TAG, "MultiPending: Incorrect state: " + state);
                    break;
            }
            if (pendingDevice != null && pendingDevice.equals(device)) {
                removeMessages(CONNECT_TIMEOUT);
                Log.d(TAG, "MultiPending: removed CONNECT_TIMEOUT for device=" + pendingDevice);
            }
            Log.d(TAG, "Exit MultiHFPending processConnectionEvent()");
        }

        private void processAudioEvent(int state, BluetoothDevice device) {
            Log.d(TAG, "Enter MultiHFPending processAudioEvent()");
            if (!mConnectedDevicesList.contains(device)) {
                Log.e(TAG, "MultiPending: Audio changed on disconnected device: " + device);
                return;
            }

            switch (state) {
                case HeadsetHalConstants.AUDIO_STATE_CONNECTED:
                    if (!isScoAcceptable()) {
                        Log.e(TAG, "MultiPending: Audio Connected without any listener");
                        disconnectAudioNative(getByteAddress(device));
                        break;
                    }
                    mAudioState = BluetoothHeadset.STATE_AUDIO_CONNECTED;
                    setAudioParameters(device); /* Set proper Audio Parameters. */

                    // Start playing silence if VR or VOIP app is not opening playback session
                    // and selecting device for SCO Rx
                    if (((mVoiceRecognitionStarted && mPlaybackForVR) ||
                        (mVirtualCallStarted && mPlaybackForVOIP)) &&
                        (mAudioPlayer != null) &&
                        !mAudioPlayer.isPlaying()) {
                        Log.d(TAG, "VR or VOIP started, starting audio playback");
                        mAudioPlayer.start();
                    }

                    mAudioManager.setParameters("BT_SCO=on");
                    mAudioManager.setBluetoothScoOn(true);
                    mActiveScoDevice = device;
                    broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_CONNECTED,
                            BluetoothHeadset.STATE_AUDIO_CONNECTING);
                    if (!mPhoneState.getIsCsCall()) {
                        log("Sco connected for call other than CS, check network type");
                        sendVoipConnectivityNetworktype(true);
                    } else {
                        log("Sco connected for CS call, do not check network type");
                    }
                    /* The state should be still in MultiHFPending state when
                       audio connected since other device is still connecting/
                       disconnecting */
                    //Reset SCO requested device
                    mScoRequestedDevice = null;
                    mLastScoDiscReqDevice = null;
                    break;
                case HeadsetHalConstants.AUDIO_STATE_CONNECTING:
                    mAudioState = BluetoothHeadset.STATE_AUDIO_CONNECTING;
                    broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_CONNECTING,
                            BluetoothHeadset.STATE_AUDIO_DISCONNECTED);
                    break;
                case HeadsetHalConstants.AUDIO_STATE_DISCONNECTED:
                    if (mAudioState != BluetoothHeadset.STATE_AUDIO_DISCONNECTED) {
                        mAudioState = BluetoothHeadset.STATE_AUDIO_DISCONNECTED;
                        if (device.equals(mActiveScoDevice)) {
                            mActiveScoDevice = null;
                        }
                        if (mAudioManager.isSpeakerphoneOn()) {
                            // User option might be speaker as sco disconnection
                            // is delayed setting back the speaker option.
                            mAudioManager.setParameters("BT_SCO=off");
                            mAudioManager.setBluetoothScoOn(false);
                            mAudioManager.setSpeakerphoneOn(true);
                        } else {
                            mAudioManager.setParameters("BT_SCO=off");
                            mAudioManager.setBluetoothScoOn(false);
                        }
                        //clear call info for VOIP calls when remote disconnects SCO
                        terminateScoUsingVirtualVoiceCall();

                        if (mA2dpSuspend) {
                            if ((!isInCall()) && (mPhoneState.getNumber().isEmpty())) {
                                log("Audio is closed,Set A2dpSuspended=false");
                                mAudioManager.setParameters("A2dpSuspended=false");
                                mA2dpSuspend = false;
                            }
                        }
                        if (!mPhoneState.getIsCsCall()) {
                            log("Sco disconnected for call other than CS, check network type");
                            sendVoipConnectivityNetworktype(false);
                            mPhoneState.setIsCsCall(true);
                        } else {
                            log("Sco disconnected for CS call, do not check network type");
                        }

                        if ((mPlaybackForVR || mPlaybackForVOIP) &&
                            (mAudioPlayer != null) &&
                            mAudioPlayer.isPlaying()) {
                            Log.d(TAG, "SCO disconnected, stop audio playback");
                            mAudioPlayer.stop();
                        }
                        broadcastAudioState(device, BluetoothHeadset.STATE_AUDIO_DISCONNECTED,
                                BluetoothHeadset.STATE_AUDIO_CONNECTED);
                    }
                    /* The state should be still in MultiHFPending state when audio
                       disconnected since other device is still connecting/
                       disconnecting */
                    break;

                default:
                    Log.e(TAG,
                            "MultiPending: Audio State Device: " + device + " bad state: " + state);
                    break;
            }
            Log.d(TAG, "Exit MultiHFPending processAudioEvent()");
        }

        private void processSlcConnected() {
            Log.d(TAG, "Enter MultiHFPending processSlcConnected()");
            if (mPhoneProxy != null) {
                // start phone state listener here, instead of on disconnected exit()
                // On BT off, exitting SM sends a SM exit() call which incorrectly forces
                // a listenForPhoneState(true).
                // Additionally, no indicator updates should be sent prior to SLC setup
                mPhoneState.listenForPhoneState(true);
                sendMessageDelayed(QUERY_PHONE_STATE_AT_SLC, QUERY_PHONE_STATE_CHANGED_DELAYED);
                mA2dpSuspend = false;/*Reset at SLC*/
                mPendingCiev = false;
                mPendingCallStates.clear();
                if ((isInCall()) && (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED)) {
                    log("Headset connected while we are in some call state");
                    log("Make A2dpSuspended=true here");
                    mAudioManager.setParameters("A2dpSuspended=true");
                    mA2dpSuspend = true;
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for query phone state");
            }
            Log.d(TAG, "Exit MultiHFPending processSlcConnected()");
        }

        private void processMultiHFDisconnect(BluetoothDevice device) {
            Log.d(TAG, "Enter MultiHFPending processMultiHFDisconnect()");
            log("MultiHFPending state: processMultiHFDisconnect");

            if (mActiveScoDevice != null && mActiveScoDevice.equals(device)) {
                log("mActiveScoDevice is disconnected, setting it to null");
                mActiveScoDevice = null;
            }
            /* Assign the current activedevice again if the disconnected
               device equals to the current active device */
            if (mCurrentDevice != null && mCurrentDevice.equals(device)) {
                int deviceSize = mConnectedDevicesList.size();
                mCurrentDevice = mConnectedDevicesList.get(deviceSize - 1);
            }
            // The disconnected device is not current active device
            if (mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED)
                transitionTo(mAudioOn);
            else transitionTo(mConnected);
            log("processMultiHFDisconnect , the latest mCurrentDevice is:"
                                            + mCurrentDevice);
            log("MultiHFPending state: processMultiHFDisconnect ," +
                         "fake broadcasting for mCurrentDevice");
            broadcastConnectionState(mCurrentDevice, BluetoothProfile.STATE_CONNECTED,
                    BluetoothProfile.STATE_DISCONNECTED);
            Log.d(TAG, "Exit MultiHFPending processMultiHFDisconnect()");
        }

        private void processIntentScoVolume(Intent intent, BluetoothDevice device) {
            Log.d(TAG, "Enter MultiHFPending processIntentScoVolume()");
            int volumeValue = intent.getIntExtra(AudioManager.EXTRA_VOLUME_STREAM_VALUE, 0);
            if (mPhoneState.getSpeakerVolume() != volumeValue) {
                mPhoneState.setSpeakerVolume(volumeValue);
            boolean scoVolume =
                    SystemProperties.getBoolean("bt.pts.certification", false);
                if (!scoVolume) {
                    setVolumeNative(HeadsetHalConstants.VOLUME_TYPE_SPK,
                                        volumeValue, getByteAddress(device));
                } else {
                    setVolumeNative(HeadsetHalConstants.VOLUME_TYPE_SPK,
                                        0, getByteAddress(device));
                }
            }
            Log.d(TAG, "Exit MultiHFPending processIntentScoVolume()");
        }
    }

    private final ServiceConnection mConnection = new ServiceConnection() {
        public void onServiceConnected(ComponentName className, IBinder service) {
            log("Proxy object connected");
            mPhoneProxy = IBluetoothHeadsetPhone.Stub.asInterface(service);
        }

        public void onServiceDisconnected(ComponentName className) {
            log("Proxy object disconnected");
            mPhoneProxy = null;
        }
    };

    // HFP Connection state of the device could be changed by the state machine
    // in separate thread while this method is executing.
    int getConnectionState(BluetoothDevice device) {
        Log.d(TAG, "Enter getConnectionState()");
        if (getCurrentState() == mDisconnected) {
            log("currentState is Disconnected");
            return BluetoothProfile.STATE_DISCONNECTED;
        }

        synchronized (this) {
            IState currentState = getCurrentState();
            log("currentState = " + currentState);
            if (currentState == mPending) {
                if ((mTargetDevice != null) && mTargetDevice.equals(device)) {
                    return BluetoothProfile.STATE_CONNECTING;
                }
                if (mConnectedDevicesList.contains(device)) {
                    return BluetoothProfile.STATE_DISCONNECTING;
                }
                if ((mIncomingDevice != null) && mIncomingDevice.equals(device)) {
                    return BluetoothProfile.STATE_CONNECTING; // incoming connection
                }
                return BluetoothProfile.STATE_DISCONNECTED;
            }

            if (currentState == mMultiHFPending) {
                if ((mTargetDevice != null) && mTargetDevice.equals(device)) {
                    return BluetoothProfile.STATE_CONNECTING;
                }
                if ((mIncomingDevice != null) && mIncomingDevice.equals(device)) {
                    return BluetoothProfile.STATE_CONNECTING; // incoming connection
                }
                if (mConnectedDevicesList.contains(device)) {
                    if ((mMultiDisconnectDevice != null)
                            && (!mMultiDisconnectDevice.equals(device))) {
                        // The device is still connected
                        return BluetoothProfile.STATE_CONNECTED;
                    }
                    return BluetoothProfile.STATE_DISCONNECTING;
                }
                return BluetoothProfile.STATE_DISCONNECTED;
            }

            if (currentState == mConnected || currentState == mAudioOn) {
                if (mConnectedDevicesList.contains(device)) {
                    return BluetoothProfile.STATE_CONNECTED;
                }
                return BluetoothProfile.STATE_DISCONNECTED;
            } else {
                Log.e(TAG, "Bad currentState: " + currentState);
                return BluetoothProfile.STATE_DISCONNECTED;
            }
        }
    }

    List<BluetoothDevice> getConnectedDevices() {
        Log.d(TAG, "Enter getConnectedDevices()");
        List<BluetoothDevice> devices = new ArrayList<BluetoothDevice>();
        synchronized (this) {
            devices.addAll(mConnectedDevicesList);
        }

        Log.d(TAG, "Exit getConnectedDevices()");
        return devices;
    }

    boolean isAudioOn() {
        Log.d(TAG, "isAudioOn()");
        return (getCurrentState() == mAudioOn);
    }

    boolean isAudioConnected(BluetoothDevice device) {
        Log.d(TAG, "Enter isAudioConnected()");
        synchronized (this) {
            /*  Additional check for audio state included for the case when PhoneApp queries
            Bluetooth Audio state, before we receive the close event from the stack for the
            sco disconnect issued in AudioOn state. This was causing a mismatch in the
            Incall screen UI. */

            if (mActiveScoDevice != null && mActiveScoDevice.equals(device)
                && mAudioState != BluetoothHeadset.STATE_AUDIO_DISCONNECTED)
            {
                return true;
            }
        }
        Log.d(TAG, "Exit isAudioConnected()");
        return false;
    }

    public void setAudioRouteAllowed(boolean allowed) {
        Log.d(TAG, "Enter setAudioRouteAllowed()");
        mAudioRouteAllowed = allowed;
        setScoAllowedNative(allowed);
        Log.d(TAG, "Exit setAudioRouteAllowed()");
    }

    public boolean getAudioRouteAllowed() {
        Log.d(TAG, "getAudioRouteAllowed()");
        return mAudioRouteAllowed;
    }

    public void setForceScoAudio(boolean forced) {
        mForceScoAudio = forced;
    }

    int getAudioState(BluetoothDevice device) {
        Log.d(TAG, "Enter getAudioState()");
        synchronized (this) {
            if (mConnectedDevicesList.size() == 0) {
                return BluetoothHeadset.STATE_AUDIO_DISCONNECTED;
            }
        }
        Log.d(TAG, "Exit getAudioState()");
        return mAudioState;
    }

    private void processVrEvent(int state, BluetoothDevice device) {
        Log.d(TAG, "Enter processVrEvent()");
        if (device == null) {
            Log.w(TAG, "processVrEvent device is null");
            return;
        }
        Log.d(TAG, "processVrEvent: state=" + state + " mVoiceRecognitionStarted: "
                        + mVoiceRecognitionStarted + " mWaitingforVoiceRecognition: "
                        + mWaitingForVoiceRecognition + " isInCall: " + isInCall());
        if (state == HeadsetHalConstants.VR_STATE_STARTED) {
            if (!isVirtualCallInProgress() && !isInCall()) {
                IDeviceIdleController dic = IDeviceIdleController.Stub.asInterface(
                        ServiceManager.getService(Context.DEVICE_IDLE_CONTROLLER));
                if (dic != null) {
                    try {
                        dic.exitIdle("voice-command");
                    } catch (RemoteException e) {
                    }
                }
                try {
                    mService.startActivity(sVoiceCommandIntent);
                } catch (ActivityNotFoundException e) {
                    atResponseCodeNative(
                            HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                    return;
                }
                expectVoiceRecognition(device);
            } else {
                // send error response if call is ongoing
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                return;
            }
        } else if (state == HeadsetHalConstants.VR_STATE_STOPPED) {
            if (mVoiceRecognitionStarted || mWaitingForVoiceRecognition) {
                atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_OK, 0, getByteAddress(device));
                mVoiceRecognitionStarted = false;
                mWaitingForVoiceRecognition = false;
                if (!isInCall() && (mActiveScoDevice != null)) {
                    disconnectAudioNative(getByteAddress(mActiveScoDevice));
                }
            } else {
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            }
        } else {
            Log.e(TAG, "Bad Voice Recognition state: " + state);
        }
        Log.d(TAG, "Exit processVrEvent()");
    }

    private void processLocalVrEvent(int state) {
        Log.d(TAG, "Enter processLocalVrEvent()");
        BluetoothDevice device = null;
        if (state == HeadsetHalConstants.VR_STATE_STARTED) {
            boolean needAudio = true;
            if (mVoiceRecognitionStarted || isInCall()) {
                Log.e(TAG, "Voice recognition started when call is active. isInCall:" + isInCall()
                                + " mVoiceRecognitionStarted: " + mVoiceRecognitionStarted);
                return;
            }
            mVoiceRecognitionStarted = true;

            if (mWaitingForVoiceRecognition) {
                device = getDeviceForMessage(START_VR_TIMEOUT);
                if (device == null) return;

                Log.d(TAG, "Voice recognition started successfully");
                mWaitingForVoiceRecognition = false;
                atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_OK, 0, getByteAddress(device));
                removeMessages(START_VR_TIMEOUT);
            } else {
                Log.d(TAG, "Voice recognition started locally");
                needAudio = startVoiceRecognitionNative(getByteAddress(mCurrentDevice));
                if (mCurrentDevice != null) device = mCurrentDevice;
            }

            if (needAudio && !isAudioOn()) {
                Log.d(TAG, "Initiating audio connection for Voice Recognition");
                // At this stage, we need to be sure that AVDTP is not streaming. This is needed
                // to be compliant with the AV+HFP Whitepaper as we cannot have A2DP in
                // streaming state while a SCO connection is established.
                // This is needed for VoiceDial scenario alone and not for
                // incoming call/outgoing call scenarios as the phone enters MODE_RINGTONE
                // or MODE_IN_CALL which shall automatically suspend the AVDTP stream if needed.
                // Whereas for VoiceDial we want to activate the SCO connection but we are still
                // in MODE_NORMAL and hence the need to explicitly suspend the A2DP stream
                if (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED) {
                    if (!mA2dpSuspend) {
                        Log.d(TAG, "Suspend A2DP streaming");
                        mA2dpSuspend = true;
                        mAudioManager.setParameters("A2dpSuspended=true");
                    }

                    if (getA2dpPlayState() == BluetoothA2dp.STATE_PLAYING) {
                        mPendingScoForVRDevice = device;
                        mPendingScoForVR = true;
                        if (mStartVoiceRecognitionWakeLock.isHeld()) {
                            mStartVoiceRecognitionWakeLock.release();
                        }
                        return;
                    }
                }

                if (device != null) {
                    connectAudioNative(getByteAddress(device));
                } else {
                    Log.e(TAG, "device not found for VR");
                }
            }

            if (mStartVoiceRecognitionWakeLock.isHeld()) {
                mStartVoiceRecognitionWakeLock.release();
            }
        } else {
            Log.d(TAG, "Voice Recognition stopped. mVoiceRecognitionStarted: "
                            + mVoiceRecognitionStarted + " mWaitingForVoiceRecognition: "
                            + mWaitingForVoiceRecognition);
            if (mVoiceRecognitionStarted || mWaitingForVoiceRecognition) {
                mVoiceRecognitionStarted = false;
                mWaitingForVoiceRecognition = false;

                if (mCurrentDevice != null)
                    stopVoiceRecognitionNative(getByteAddress(mCurrentDevice));

                if (mActiveScoDevice != null &&
                           (!isInCall() || (mPhoneState.getCallState() ==
                           HeadsetHalConstants.CALL_STATE_INCOMING))) {
                    disconnectAudioNative(getByteAddress(mActiveScoDevice));
                }
            }
        }
        Log.d(TAG, "Exit processLocalVrEvent()");
    }

    private synchronized void expectVoiceRecognition(BluetoothDevice device) {
        Log.d(TAG, "Enter expectVoiceRecognition()");
        mWaitingForVoiceRecognition = true;
        Message m = obtainMessage(START_VR_TIMEOUT);
        m.obj = getMatchingDevice(device);
        sendMessageDelayed(m, START_VR_TIMEOUT_VALUE);

        if (!mStartVoiceRecognitionWakeLock.isHeld()) {
            mStartVoiceRecognitionWakeLock.acquire(START_VR_TIMEOUT_VALUE);
        }
        Log.d(TAG, "Exit expectVoiceRecognition()");
    }

    List<BluetoothDevice> getDevicesMatchingConnectionStates(int[] states) {
        Log.d(TAG, "Enter getDevicesMatchingConnectionStates()");
        List<BluetoothDevice> deviceList = new ArrayList<BluetoothDevice>();
        Set<BluetoothDevice> bondedDevices = mAdapter.getBondedDevices();
        int connectionState;
        synchronized (this) {
            for (BluetoothDevice device : bondedDevices) {
                ParcelUuid[] featureUuids = device.getUuids();
                if (!BluetoothUuid.containsAnyUuid(featureUuids, HEADSET_UUIDS)) {
                    continue;
                }
                connectionState = getConnectionState(device);
                for (int i = 0; i < states.length; i++) {
                    if (connectionState == states[i]) {
                        deviceList.add(device);
                    }
                }
            }
        }
        Log.d(TAG, "Exit getDevicesMatchingConnectionStates()");
        return deviceList;
    }

    private BluetoothDevice getDeviceForMessage(int what) {
        Log.d(TAG, "Enter getDeviceForMessage()");
        if (what == CONNECT_TIMEOUT) {
            log("getDeviceForMessage: returning mTargetDevice for what=" + what);
            return mTargetDevice;
        }
        if (mConnectedDevicesList.size() == 0) {
            log("getDeviceForMessage: No connected device. what=" + what);
            return null;
        }
        for (BluetoothDevice device : mConnectedDevicesList) {
            if (getHandler().hasMessages(what, device)) {
                log("getDeviceForMessage: returning " + device);
                return device;
            }
        }
        log("getDeviceForMessage: No matching device for " + what + ". Returning null");
        return null;
    }

    private BluetoothDevice getMatchingDevice(BluetoothDevice device) {
        Log.d(TAG, "Enter getMatchingDevice()");
        for (BluetoothDevice matchingDevice : mConnectedDevicesList) {
            if (matchingDevice.equals(device)) {
                return matchingDevice;
            }
        }
        Log.d(TAG, "Exit getMatchingDevice()");
        return null;
    }

    // This method does not check for error conditon (newState == prevState)
    private void broadcastConnectionState(BluetoothDevice device, int newState, int prevState) {
        Log.d(TAG, "Connection state " + device + ": " + prevState + "->" + newState);
        if (prevState == BluetoothProfile.STATE_CONNECTED) {
            // Headset is disconnecting, stop Virtual call if active.
            terminateScoUsingVirtualVoiceCall();
        }

        Intent intent = new Intent(BluetoothHeadset.ACTION_CONNECTION_STATE_CHANGED);
        intent.putExtra(BluetoothProfile.EXTRA_PREVIOUS_STATE, prevState);
        intent.putExtra(BluetoothProfile.EXTRA_STATE, newState);
        intent.putExtra(BluetoothDevice.EXTRA_DEVICE, device);
        intent.addFlags(Intent.FLAG_RECEIVER_INCLUDE_BACKGROUND);
        mService.sendBroadcastAsUser(intent, UserHandle.ALL,
                HeadsetService.BLUETOOTH_PERM);
        Log.d(TAG, "Exit broadcastConnectionState()");
    }

    private void broadcastAudioState(BluetoothDevice device, int newState, int prevState) {
        Log.d(TAG, "Enter broadcastAudioState()");
        if (prevState == BluetoothHeadset.STATE_AUDIO_CONNECTED) {
            // When SCO gets disconnected during call transfer, Virtual call
            // needs to be cleaned up.So call terminateScoUsingVirtualVoiceCall.
            terminateScoUsingVirtualVoiceCall();
        }
        Intent intent = new Intent(BluetoothHeadset.ACTION_AUDIO_STATE_CHANGED);
        intent.putExtra(BluetoothProfile.EXTRA_PREVIOUS_STATE, prevState);
        intent.putExtra(BluetoothProfile.EXTRA_STATE, newState);
        intent.putExtra(BluetoothDevice.EXTRA_DEVICE, device);
        mService.sendBroadcastAsUser(intent, UserHandle.ALL, HeadsetService.BLUETOOTH_PERM);
        Log.d(TAG, "Audio state " + device + ": " + prevState + "->" + newState);
        Log.d(TAG, "Exit broadcastAudioState()");
    }

    /*
     * Put the AT command, company ID, arguments, and device in an Intent and broadcast it.
     */
    private void broadcastVendorSpecificEventIntent(String command, int companyId, int commandType,
            Object[] arguments, BluetoothDevice device) {
        Log.d(TAG, "Enter broadcastVendorSpecificEventIntent()");
        log("broadcastVendorSpecificEventIntent(" + command + ")");
        Intent intent = new Intent(BluetoothHeadset.ACTION_VENDOR_SPECIFIC_HEADSET_EVENT);
        intent.putExtra(BluetoothHeadset.EXTRA_VENDOR_SPECIFIC_HEADSET_EVENT_CMD, command);
        intent.putExtra(BluetoothHeadset.EXTRA_VENDOR_SPECIFIC_HEADSET_EVENT_CMD_TYPE, commandType);
        // assert: all elements of args are Serializable
        intent.putExtra(BluetoothHeadset.EXTRA_VENDOR_SPECIFIC_HEADSET_EVENT_ARGS, arguments);
        intent.putExtra(BluetoothDevice.EXTRA_DEVICE, device);

        intent.addCategory(BluetoothHeadset.VENDOR_SPECIFIC_HEADSET_EVENT_COMPANY_ID_CATEGORY + "."
                + Integer.toString(companyId));

        mService.sendBroadcastAsUser(intent, UserHandle.ALL, HeadsetService.BLUETOOTH_PERM);
        Log.d(TAG, "Exit broadcastVendorSpecificEventIntent()");
    }

    private void configAudioParameters(BluetoothDevice device) {
        Log.d(TAG, "Enter configAudioParameters()");
        // Reset NREC on connect event. Headset will override later
        HashMap<String, Integer> AudioParamConfig = new HashMap<String, Integer>();
        AudioParamConfig.put("NREC", 1);
        AudioParamConfig.put("codec", NBS_CODEC);
        mHeadsetAudioParam.put(device, AudioParamConfig);
        mAudioManager.setParameters(
                HEADSET_NAME + "=" + getCurrentDeviceName(device) + ";" + HEADSET_NREC + "=on");
        Log.d(TAG, "configAudioParameters for device:" + device + " are: nrec = "
                        + AudioParamConfig.get("NREC"));
        Log.d(TAG, "Exit configAudioParameters()");
    }

    private void setAudioParameters(BluetoothDevice device) {
        Log.d(TAG, "Enter setAudioParameters()");
        // 1. update nrec value
        // 2. update headset name
        int mNrec = 0;
        int mCodec = 0;
        HashMap<String, Integer> AudioParam = mHeadsetAudioParam.get(device);
        if (AudioParam != null && !AudioParam.isEmpty()) {
            if (AudioParam.containsKey("codec"))
                mCodec =  AudioParam.get("codec");
            if (AudioParam.containsKey("NREC"))
                mNrec = AudioParam.get("NREC");
        } else {
            Log.e(TAG, "setAudioParameters: AudioParam not found");
        }

        if (mCodec != WBS_CODEC) {
            Log.d(TAG, "Use NBS PCM samples:" + device);
            mAudioManager.setParameters(HEADSET_WBS + "=off");
        } else {
            Log.d(TAG, "Use WBS PCM samples:" + device);
            mAudioManager.setParameters(HEADSET_WBS + "=on");
        }
        if (mNrec == 1) {
            log("Set NREC: 1 for device:" + device);
            mAudioManager.setParameters(HEADSET_NREC + "=on");
        } else {
            log("Set NREC: 0 for device:" + device);
            mAudioManager.setParameters(HEADSET_NREC + "=off");
        }
        mAudioManager.setParameters(HEADSET_NAME + "=" + getCurrentDeviceName(device));
        Log.d(TAG, "Exit setAudioParameters()");
    }

    private String parseUnknownAt(String atString) {
        Log.d(TAG, "Enter parseUnknownAt()");
        StringBuilder atCommand = new StringBuilder(atString.length());
        String result = null;

        for (int i = 0; i < atString.length(); i++) {
            char c = atString.charAt(i);
            if (c == '"') {
                int j = atString.indexOf('"', i + 1); // search for closing "
                if (j == -1) { // unmatched ", insert one.
                    atCommand.append(atString.substring(i, atString.length()));
                    atCommand.append('"');
                    break;
                }
                atCommand.append(atString.substring(i, j + 1));
                i = j;
            } else if (c != ' ') {
                atCommand.append(Character.toUpperCase(c));
            }
        }
        result = atCommand.toString();
        Log.d(TAG, "Exit parseUnknownAt()");
        return result;
    }

    private int getAtCommandType(String atCommand) {
        Log.d(TAG, "Enter getAtCommandType()");
        int commandType = mPhonebook.TYPE_UNKNOWN;
        String atString = null;
        atCommand = atCommand.trim();
        if (atCommand.length() > 5) {
            atString = atCommand.substring(5);
            if (atString.startsWith("?")) // Read
                commandType = mPhonebook.TYPE_READ;
            else if (atString.startsWith("=?")) // Test
                commandType = mPhonebook.TYPE_TEST;
            else if (atString.startsWith("=")) // Set
                commandType = mPhonebook.TYPE_SET;
            else
                commandType = mPhonebook.TYPE_UNKNOWN;
        }
        Log.d(TAG, "Exit getAtCommandType()");
        return commandType;
    }

    /* Method to check if Virtual Call in Progress */
    private boolean isVirtualCallInProgress() {
        Log.d(TAG, "isVirtualCallInProgress()");
        return mVirtualCallStarted;
    }

    void setVirtualCallInProgress(boolean state) {
        Log.d(TAG, "Enter setVirtualCallInProgress()");
        mVirtualCallStarted = state;
        Log.d(TAG, "Exit setVirtualCallInProgress()");
    }

    /* NOTE: Currently the VirtualCall API does not support handling of
    call transfers. If it is initiated from the handsfree device,
    HeadsetStateMachine will end the virtual call by calling
    terminateScoUsingVirtualVoiceCall() in broadcastAudioState() */
    synchronized boolean initiateScoUsingVirtualVoiceCall() {
        Log.d(TAG, " Enter initiateScoUsingVirtualVoiceCall: Received");
        // 1. Check if the SCO state is idle
        if (isInCall() || mVoiceRecognitionStarted) {
            Log.e(TAG, "initiateScoUsingVirtualVoiceCall: Call in progress.");
            return false;
        }
        setVirtualCallInProgress(true);

        // 2. Update the connectivity network type to controller for CxM optimisation.
        sendVoipConnectivityNetworktype(true);

        if (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED) {
            mAudioManager.setParameters("A2dpSuspended=true");
            mA2dpSuspend = true;
            if (getA2dpPlayState() == BluetoothA2dp.STATE_PLAYING) {
                log("suspending A2DP stream for SCO");
                mPendingCiev = true;
                //This is VOIP call, dont need to remember the states
                return true;
            }
        }

        // 3. Send virtual phone state changed to initialize SCO
        processCallState(new HeadsetCallState(0, 0,
            HeadsetHalConstants.CALL_STATE_DIALING, "", 0), true);

        Message msg = obtainMessage(VOIP_CALL_STATE_CHANGED_ALERTING);
        msg.obj = new HeadsetCallState(0, 0, HeadsetHalConstants.CALL_STATE_ALERTING, "", 0);
        msg.arg1 = 1;
        sendMessageDelayed(msg, VOIP_CALL_ALERTING_DELAY_TIME_MSEC);

        Message m = obtainMessage(VOIP_CALL_STATE_CHANGED_ACTIVE);
        m.obj = new HeadsetCallState(1, 0, HeadsetHalConstants.CALL_STATE_IDLE, "", 0);
        m.arg1 = 1;
        sendMessageDelayed(m, VOIP_CALL_ACTIVE_DELAY_TIME_MSEC);
        // Done
        Log.d(TAG, "Exit initiateScoUsingVirtualVoiceCall()");
        return true;
    }

    synchronized boolean terminateScoUsingVirtualVoiceCall() {
        Log.d(TAG, "Enter terminateScoUsingVirtualVoiceCall()");
        log("terminateScoUsingVirtualVoiceCall: Received");

        if (!isVirtualCallInProgress()) {
            Log.w(TAG, "terminateScoUsingVirtualVoiceCall: No present call to terminate");
            return false;
        }

        /* if there are any delayed call alerting, active messages in the Queue,
           remove them */

        Log.d(TAG, "removing pending alerting, active messages for VOIP");
        removeMessages(VOIP_CALL_STATE_CHANGED_ALERTING);
        removeMessages(VOIP_CALL_STATE_CHANGED_ACTIVE);

        // 2. Send virtual phone state changed to close SCO
        processCallState(
                new HeadsetCallState(0, 0, HeadsetHalConstants.CALL_STATE_IDLE, "", 0), true);
        setVirtualCallInProgress(false);
        sendVoipConnectivityNetworktype(false);

        // Done
        log("terminateScoUsingVirtualVoiceCall: Done");
        Log.d(TAG, "Exit terminateScoUsingVirtualVoiceCall()");
        return true;
    }

    private int getA2dpConnState() {
        /* we are interested only in CONNECTED and DISCONNECTED states.
         * Return CONNECTED only if any device is in CONNECTED state else return DISCONNECTED
         */
        Log.d(TAG, "Enter getA2dpConnState()");
        for(Integer value : mA2dpConnState.values()) {
           if (value == BluetoothProfile.STATE_CONNECTED)
              return BluetoothProfile.STATE_CONNECTED;
        }
        Log.d(TAG, "Exit getA2dpConnState()");
        return BluetoothProfile.STATE_DISCONNECTED;
    }

    private int getA2dpPlayState() {
        Log.d(TAG, "Enter getA2dpPlayState()");
        /* return PLAYING if a2dp is playing on any device */
        for(Integer value : mA2dpPlayState.values()) {
           if (value == BluetoothA2dp.STATE_PLAYING)
              return BluetoothA2dp.STATE_PLAYING;
        }
        Log.d(TAG, "Exit getA2dpPlayState()");
        return BluetoothA2dp.STATE_NOT_PLAYING;
    }

    /* Check for a2dp state change.mA2dpSuspend is set if we had suspended stream and process only in
       that condition A2dp state could be in playing soon after connection if Headset got
       connected while in call and music was played before that (Special case
       to handle RINGER VOLUME zero + music + call) */
    private void processIntentA2dpStateChanged(Intent intent) {
        Log.d(TAG, "Enter processIntentA2dpStateChanged()");

        int state = intent.getIntExtra(BluetoothProfile.EXTRA_STATE,
                           BluetoothProfile.STATE_DISCONNECTED);
        int oldState = intent.getIntExtra(BluetoothProfile.
                       EXTRA_PREVIOUS_STATE,BluetoothProfile.STATE_DISCONNECTED);

        BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);

        Log.d(TAG, "Device " + device + " A2dp State Changed: Current State: " + state +
                  " Prev State: " + oldState + " A2pSuspend: " + mA2dpSuspend);

        if (state == BluetoothProfile.STATE_DISCONNECTED) {
            // remove will remove if the device is present. No need to check for presence of entry
            Log.d(TAG, "A2DP connection for device " + device + " is disconnected. Removing it");
            mA2dpConnState.remove(device);
            mA2dpPlayState.remove(device);
        }
        else
            mA2dpConnState.put(device, state);
        //While in call A2DP connected set A2DP suspend flag to true.
        if((getA2dpConnState() == BluetoothProfile.STATE_CONNECTED) &&
           isInCall() && !mA2dpSuspend) {
            Log.d(TAG, "A2DP connected while is in call suspend A2DP.");
            mAudioManager.setParameters("A2dpSuspended=true");
            mA2dpSuspend = true;
        }
        Log.d(TAG, "Exit processIntentA2dpStateChanged()");
    }

    private void processIntentUpdateCallType(Intent intent) {
        Log.d(TAG, "Enter processIntentUpdateCallType()");

        mIsCsCall = intent.getBooleanExtra(TelecomManager.EXTRA_CALL_TYPE_CS, true);
        Log.d(TAG, "processIntentUpdateCallType " + mIsCsCall);
        mPhoneState.setIsCsCall(mIsCsCall);
        if (mActiveScoDevice != null) {
            if (!mPhoneState.getIsCsCall()) {
                log("processIntentUpdateCallType, Non CS call, check for network type");
                sendVoipConnectivityNetworktype(true);
            } else {
                log("processIntentUpdateCallType, CS call, do not check for network type");
            }
        } else {
            log("processIntentUpdateCallType: Sco not yet connected");
        }
        Log.d(TAG, "Exit processIntentUpdateCallType()");
    }

    private void processIntentA2dpPlayStateChanged(Intent intent) {
        Log.d(TAG, "Enter processIntentA2dpPlayStateChanged()");

        int currState = intent.getIntExtra(BluetoothProfile.EXTRA_STATE,
                                   BluetoothA2dp.STATE_NOT_PLAYING);
        int prevState = intent.getIntExtra(
                                   BluetoothProfile.EXTRA_PREVIOUS_STATE,
                                   BluetoothA2dp.STATE_NOT_PLAYING);

        BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);

        Log.d(TAG, "Device " + device + " A2dp Play State Changed: Current State: " + currState +
                  " Prev State: " + prevState + " A2pSuspend: " + mA2dpSuspend);

        if (!mA2dpConnState.containsKey(device)) {
            Log.w(TAG, "Device " + device + " is not added in the mA2dpConnState map, adding now");
            mA2dpConnState.put(device, BluetoothProfile.STATE_CONNECTED);
        }

        if (prevState == BluetoothA2dp.STATE_PLAYING) {
            if (mA2dpSuspend && mPendingCiev) {
                if (isVirtualCallInProgress()) {
                    //Send virtual phone state changed to initialize SCO
                    processCallState(new HeadsetCallState(0, 0,
                          HeadsetHalConstants.CALL_STATE_DIALING, "", 0),
                          true);

                    Message msg = obtainMessage(VOIP_CALL_STATE_CHANGED_ALERTING);
                    msg.obj = new HeadsetCallState(0, 0, HeadsetHalConstants.CALL_STATE_ALERTING, "", 0);
                    msg.arg1 = 1;
                    sendMessageDelayed(msg, VOIP_CALL_ALERTING_DELAY_TIME_MSEC);

                    Message m = obtainMessage(VOIP_CALL_STATE_CHANGED_ACTIVE);
                    m.obj = new HeadsetCallState(1, 0, HeadsetHalConstants.CALL_STATE_IDLE, "", 0);
                    m.arg1 = 1;
                    sendMessageDelayed(m, VOIP_CALL_ACTIVE_DELAY_TIME_MSEC);
                } else {
                    //send incomming phone status to remote device
                    log("A2dp is suspended, updating phone status if any");
                    Iterator<HeadsetCallState> it = mPendingCallStates.iterator();
                    if (it != null) {
                        while (it.hasNext()) {
                            HeadsetCallState callState = it.next();
                            Log.d(TAG, "mIsCallIndDelay: " + mIsCallIndDelay);
                            phoneStateChangeNative( callState.mNumActive,
                                            callState.mNumHeld,callState.mCallState,
                                            callState.mNumber,callState.mType);
                            it.remove();
                        }
                    } else {
                        Log.d(TAG, "There are no pending call state changes");
                    }
                }
                mPendingCiev = false;
            }
            else if (mA2dpSuspend && mPendingScoForVR) {
                 if (mPendingScoForVRDevice != null)
                     connectAudioNative(getByteAddress(mPendingScoForVRDevice));

                 mPendingScoForVRDevice = null;
                 mPendingScoForVR = false;
            }
        }
        else if (prevState == BluetoothA2dp.STATE_NOT_PLAYING) {
            Log.d(TAG, "A2dp Started " + currState);
            if ((isInCall() || isVirtualCallInProgress()) && isConnected()) {
                if(mA2dpSuspend)
                    Log.e(TAG,"A2dp started while in call, ERROR");
                else {
                    log("Suspend A2dp");
                    mA2dpSuspend = true;
                    mAudioManager.setParameters("A2dpSuspended=true");
                }
            }
        }
        mA2dpPlayState.put(device, currState);
        Log.d(TAG, "Exit processIntentA2dpPlayStateChanged()");
    }

    private void processAnswerCall(BluetoothDevice device) {
        Log.d(TAG, "Enter processAnswerCall()");
        if (device == null) {
            Log.w(TAG, "processAnswerCall device is null");
            return;

        }

        if (mPhoneProxy != null) {
            try {
                mPhoneProxy.answerCall();
                //Store SCO requested device, if telephony trys to trigger
                //SCO connection by calling connectAudio
                mScoRequestedDevice = device;
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for answering call");
        }
        Log.d(TAG, "Exit processAnswerCall()");
    }

    private void processHangupCall(BluetoothDevice device) {
        Log.d(TAG, "Enter processHangupCall()");
        if (device == null) {
            Log.w(TAG, "processHangupCall device is null");
            return;
        }
        // Close the virtual call if active. Virtual call should be
        // terminated for CHUP callback event
        if (isVirtualCallInProgress()) {
            terminateScoUsingVirtualVoiceCall();
        } else {
            if (mPhoneProxy != null) {
                try {
                    mPhoneProxy.hangupCall();
                } catch (RemoteException e) {
                    Log.e(TAG, Log.getStackTraceString(new Throwable()));
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for hanging up call");
            }
        }
        Log.d(TAG, "Exit processHangupCall()");
    }

    private void processDialCall(String number, BluetoothDevice device) {
        Log.d(TAG, "Enter processDialCall()");
        if (device == null) {
            Log.w(TAG, "processDialCall device is null");
            return;
        }

        String dialNumber;
        if (mDialingOut) {
            log("processDialCall, already dialling");
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            return;
        }
        if ((number == null) || (number.length() == 0)) {
            dialNumber = mPhonebook.getLastDialledNumber();
            Log.d(TAG, "dialNumber: " + dialNumber);
            if ((dialNumber == null) || (dialNumber.length() == 0)) {
                Log.d(TAG, "processDialCall, last dial number null");
                atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0,
                                       getByteAddress(device));
                return;
            }
        } else if (number.charAt(0) == '>') {
            // Yuck - memory dialling requested.
            // Just dial last number for now
            if (number.startsWith(">9999")) { // for PTS test
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                return;
            }
            log("processDialCall, memory dial do last dial for now");
            dialNumber = mPhonebook.getLastDialledNumber();
            if (dialNumber == null) {
                log("processDialCall, last dial number null");
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                return;
            }
        } else {
            // Remove trailing ';'
            if (number.charAt(number.length() - 1) == ';') {
                number = number.substring(0, number.length() - 1);
            }

            dialNumber = PhoneNumberUtils.convertPreDial(number);
        }
        // Check for virtual call to terminate before sending Call Intent
        terminateScoUsingVirtualVoiceCall();
        //Store SCO requested device, if telephony trys to trigger
        //SCO connection by calling connectAudio
        mScoRequestedDevice = device;

        Intent intent = new Intent(
                Intent.ACTION_CALL_PRIVILEGED, Uri.fromParts(SCHEME_TEL, dialNumber, null));
        intent.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
        mService.startActivity(intent);
        // TODO(BT) continue send OK reults code after call starts
        //          hold wait lock, start a timer, set wait call flag
        //          Get call started indication from bluetooth phone
        mDialingOut = true;
        Message m = obtainMessage(DIALING_OUT_TIMEOUT);
        m.obj = getMatchingDevice(device);
        sendMessageDelayed(m, DIALING_OUT_TIMEOUT_VALUE);
        Log.d(TAG, "Exit processDialCall()");
    }

    private void processVolumeEvent(int volumeType, int volume, BluetoothDevice device) {
        Log.d(TAG, "Enter processVolumeEvent()");
        if (device != null && !device.equals(mActiveScoDevice) && mPhoneState.isInCall()) {
            Log.w(TAG, "ignore processVolumeEvent");
            return;
        }

        if (volumeType == HeadsetHalConstants.VOLUME_TYPE_SPK) {
            mPhoneState.setSpeakerVolume(volume);
            int flag = (getCurrentState() == mAudioOn) ? AudioManager.FLAG_SHOW_UI : 0;
            mAudioManager.setStreamVolume(AudioManager.STREAM_BLUETOOTH_SCO, volume, flag);
        } else if (volumeType == HeadsetHalConstants.VOLUME_TYPE_MIC) {
            mPhoneState.setMicVolume(volume);
        } else {
            Log.e(TAG, "Bad voluem type: " + volumeType);
        }
        Log.d(TAG, "Exit processVolumeEvent()");
    }

    private void processSendDtmf(int dtmf, BluetoothDevice device) {
        Log.d(TAG, "Enter processSendDtmf()");
        if (device == null) {
            Log.w(TAG, "processSendDtmf device is null");
            return;
        }

        if (mPhoneProxy != null) {
            try {
                mPhoneProxy.sendDtmf(dtmf);
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for sending DTMF");
        }
        Log.d(TAG, "Exit processSendDtmf()");
    }

    private void processCallStatesDelayed(HeadsetCallState callState, boolean isVirtualCall)
    {
        Log.d(TAG, "Enter processCallStatesDelayed");
        if (callState.mCallState == HeadsetHalConstants.CALL_STATE_DIALING)
        {
            // at this point, queue should be empty.
            processCallState(callState, false);
        }
        // update is for call alerting
        else if (callState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING &&
                  mPhoneState.getNumActiveCall() == callState.mNumActive &&
                  mPhoneState.getNumHeldCall() == callState.mNumHeld &&
                  mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_DIALING)
        {
            Log.d(TAG, "Queue alerting update, send alerting delayed mesg");
            //Q the call state;
            mDelayedCSCallStates.add(callState);

            //send delayed message for call alerting;
            Message msg = obtainMessage(CS_CALL_STATE_CHANGED_ALERTING);
            msg.arg1 = 0;
            sendMessageDelayed(msg, CS_CALL_ALERTING_DELAY_TIME_MSEC);
        }
        // call moved to active from alerting state
        else if (mPhoneState.getNumActiveCall() == 0 &&
                 callState.mNumActive == 1 &&
                 mPhoneState.getNumHeldCall() == callState.mNumHeld &&
                 (mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_DIALING ||
                  mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_ALERTING ))
        {
            Log.d(TAG, "Call moved to active state from alerting");
            // get the top of the Q
            HeadsetCallState tempCallState = mDelayedCSCallStates.peek();

            //if (top of the Q == alerting)
            if( tempCallState != null &&
                 tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
            {
                Log.d(TAG, "Call is active, Queue it, top of Queue is alerting");
                //Q active update;
                mDelayedCSCallStates.add(callState);
            }
            else
            // Q is empty
            {
                Log.d(TAG, "is Q empty " + mDelayedCSCallStates.isEmpty());
                Log.d(TAG, "Call is active, Queue it, send delayed active mesg");
                //Q active update;
                mDelayedCSCallStates.add(callState);
                //send delayed message for call active;
                Message msg = obtainMessage(CS_CALL_STATE_CHANGED_ACTIVE);
                msg.arg1 = 0;
                sendMessageDelayed(msg, CS_CALL_ACTIVE_DELAY_TIME_MSEC);
            }
        }
        // call setup or call ended
        else if((mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_DIALING ||
                  mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_ALERTING ) &&
                  callState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE &&
                  mPhoneState.getNumActiveCall() == callState.mNumActive &&
                  mPhoneState.getNumHeldCall() == callState.mNumHeld)
        {
            Log.d(TAG, "call setup or call is ended");
            // get the top of the Q
            HeadsetCallState tempCallState = mDelayedCSCallStates.peek();

            //if (top of the Q == alerting)
            if(tempCallState != null &&
                tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
            {
                Log.d(TAG, "Call is ended, remove delayed alerting mesg");
                removeMessages(CS_CALL_STATE_CHANGED_ALERTING);
                //DeQ(alerting);
                mDelayedCSCallStates.poll();
                // send 2,3 although the call is ended to make sure that we are sending 2,3 always
                processCallState(tempCallState, false);

                // update the top of the Q entry so that we process the active
                // call entry from the Q below
                tempCallState = mDelayedCSCallStates.peek();
            }

            //if (top of the Q == active)
            if (tempCallState != null &&
                 tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
            {
                Log.d(TAG, "Call is ended, remove delayed active mesg");
                removeMessages(CS_CALL_STATE_CHANGED_ACTIVE);
                //DeQ(active);
                mDelayedCSCallStates.poll();
            }
            // send current call state which will take care of sending call end indicator
            processCallState(callState, false);
        } else {
            HeadsetCallState tempCallState;

            // if there are pending call states to be sent, send them now
            if (mDelayedCSCallStates.isEmpty() != true)
            {
                Log.d(TAG, "new call update, removing pending alerting, active messages");
                // remove pending delayed call states
                removeMessages(CS_CALL_STATE_CHANGED_ALERTING);
                removeMessages(CS_CALL_STATE_CHANGED_ACTIVE);
            }

            while (mDelayedCSCallStates.isEmpty() != true)
            {
                tempCallState = mDelayedCSCallStates.poll();
                if (tempCallState != null)
                {
                    processCallState(tempCallState, false);
                }
            }
            // it is incoming call or MO call in non-alerting, non-active state.
            processCallState(callState, isVirtualCall);
        }
        Log.d(TAG, "Exit processCallStatesDelayed");
    }

    private void processCallState(HeadsetCallState callState) {
        Log.d(TAG, "Enter processCallState()");
        processCallState(callState, false);
        Log.d(TAG, "Exit processCallState()");
    }

    private void processCallState(HeadsetCallState callState, boolean isVirtualCall) {
        Log.d(TAG, "Enter processCallState()");

        /* If active call is ended, no held call is present, disconnect SCO
         * and fake the MT Call indicators. */
        boolean isPts =
                SystemProperties.getBoolean("bt.pts.certification", false);
        if (!isPts) {
            Log.d(TAG, "mIsBlacklistedDevice:" + mIsBlacklistedDevice);
            if (mIsBlacklistedDevice &&
                mPhoneState.getNumActiveCall() == 1 &&
                callState.mNumActive == 0 &&
                callState.mNumHeld == 0 &&
                callState.mCallState == HeadsetHalConstants.CALL_STATE_INCOMING) {

                Log.d(TAG, "Disconnect SCO since active call is ended," +
                                    "only waiting call is there");
                Message m = obtainMessage(DISCONNECT_AUDIO);
                m.obj = mCurrentDevice;
                sendMessage(m);

                Log.d(TAG, "Send Idle call indicators once Active call disconnected.");
                mPhoneState.setCallState(HeadsetHalConstants.CALL_STATE_IDLE);
                phoneStateChangeNative(callState.mNumActive, callState.mNumHeld,
                      HeadsetHalConstants.CALL_STATE_IDLE, callState.mNumber, callState.mType);
                mIsCallIndDelay = true;
            }
        }

        mPhoneState.setNumActiveCall(callState.mNumActive);
        mPhoneState.setNumHeldCall(callState.mNumHeld);

        // get the top of the Q
        HeadsetCallState tempCallState = mDelayedCSCallStates.peek();

        if ( !isVirtualCall && tempCallState != null &&
             tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING &&
             callState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING) {
             Log.d(TAG, "update call state as dialing since alerting update is in Q");
             Log.d(TAG, "current call state is " + mPhoneState.getCallState());
             callState.mCallState = HeadsetHalConstants.CALL_STATE_DIALING;
        }

        mPhoneState.setCallState(callState.mCallState);
        mPhoneState.setNumber(callState.mNumber);
        mPhoneState.setType(callState.mType);
        if (mDialingOut && callState.mCallState ==
                HeadsetHalConstants.CALL_STATE_DIALING) {
                BluetoothDevice device = getDeviceForMessage(DIALING_OUT_TIMEOUT);
                removeMessages(DIALING_OUT_TIMEOUT);
                Log.d(TAG, "mDialingOut is " + mDialingOut + ", device " + device);
                mDialingOut = false;
                if (device == null) {
                    return;
                }
                atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_OK,
                                                       0, getByteAddress(device));
        }

        /* Set ActiveScoDevice to null when call ends */
        if ((mActiveScoDevice != null) && !isInCall()
                && callState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE)
            mActiveScoDevice = null;

        log("mNumActive: " + callState.mNumActive + " mNumHeld: " + callState.mNumHeld
                + " mCallState: " + callState.mCallState);
        log("mNumber: " + callState.mNumber + " mType: " + callState.mType);
        if(!isVirtualCall) {
            /* Specific handling when HS connects while in Voip call */
            if (isVirtualCallInProgress() && !isInCall() &&
                callState.mCallState == HeadsetHalConstants.CALL_STATE_IDLE) {
                Log.d(TAG, "update btif for Virtual Call active");
                callState.mNumActive = 1;
                mPhoneState.setNumActiveCall(callState.mNumActive);
            } else {
                /* Not a Virtual call request. End the virtual call, if running,
                before sending phoneStateChangeNative to BTIF */
                terminateScoUsingVirtualVoiceCall();


               /* Specific handling for case of starting MO/MT call while VOIP
               is ongoing, terminateScoUsingVirtualVoiceCall() resets callState
               from INCOMING/DIALING to IDLE. Some HS send AT+CIND? to read call
               indicators and get wrong value of callsetup. This case is hit only
               when SCO for VOIP call is not terminated via SDK API call. */
               if (mPhoneState.getCallState() != callState.mCallState) {
                   mPhoneState.setCallState(callState.mCallState);
               }
            }
        }
        processA2dpState(callState);
        Log.d(TAG, "Exit processCallState()");
    }

    /* This function makes sure that we send a2dp suspend before updating on Incomming call status.
       There may problem with some headsets if send ring and a2dp is not suspended,
       so here we suspend stream if active before updating remote.We resume streaming once
       callstate is idle and there are no active or held calls. */

    private void processA2dpState(HeadsetCallState callState) {
        Log.d(TAG, "Enter processA2dpState()");
        log("mA2dpPlayState " + getA2dpPlayState() + " mA2dpSuspend  " + mA2dpSuspend );
        if ((isInCall()) && (isConnected()) &&
            (getA2dpConnState() == BluetoothProfile.STATE_CONNECTED)) {
            if (!mA2dpSuspend) {
                Log.d(TAG, "Suspend A2DP streaming");
                mAudioManager.setParameters("A2dpSuspended=true");
                mA2dpSuspend = true;
            }
            // Cache the call states for CS calls only
            if (getA2dpPlayState() == BluetoothA2dp.STATE_PLAYING && !isVirtualCallInProgress()) {
                Log.d(TAG, "Cache the call state for future");
                mPendingCiev = true;
                mPendingCallStates.add(callState);
                return ;
            }
        }
        if (getCurrentState() != mDisconnected) {
            log("No A2dp playing to suspend");
            Log.d(TAG, "mIsCallIndDelay: " + mIsCallIndDelay);
            if (mIsCallIndDelay) {
                mIsCallIndDelay = false;
                sendMessageDelayed(SEND_INCOMING_CALL_IND, INCOMING_CALL_IND_DELAY);
            } else {
                phoneStateChangeNative(callState.mNumActive, callState.mNumHeld,
                  callState.mCallState, callState.mNumber, callState.mType);
            }
        }
        if (mA2dpSuspend && (!isAudioOn())) {
            if ((!isInCall()) && (callState.mNumber.isEmpty())) {
                log("Set A2dpSuspended=false to reset the a2dp state to standby");
                mAudioManager.setParameters("A2dpSuspended=false");
                mA2dpSuspend = false;
            }
        }
        Log.d(TAG, "Exit processA2dpState()");
    }

    // 1 enable noice reduction
    // 0 disable noice reduction
    private void processNoiceReductionEvent(int enable, BluetoothDevice device) {
        Log.d(TAG, "Enter processNoiceReductionEvent()");
        HashMap<String, Integer> AudioParamNrec = mHeadsetAudioParam.get(device);
        if (AudioParamNrec != null && !AudioParamNrec.isEmpty()) {
            if (enable == 1)
                AudioParamNrec.put("NREC", 1);
            else
                AudioParamNrec.put("NREC", 0);
            log("NREC value for device :" + device + " is: " + AudioParamNrec.get("NREC"));
        } else {
            Log.e(TAG, "processNoiceReductionEvent: AudioParamNrec is null ");
        }

        if (mActiveScoDevice != null && mActiveScoDevice.equals(device)
                && mAudioState == BluetoothHeadset.STATE_AUDIO_CONNECTED) {
            setAudioParameters(device);
        }
        Log.d(TAG, "Exit processNoiceReductionEvent()");
    }

    // 2 - WBS on
    // 1 - NBS on
    private void processWBSEvent(int enable, BluetoothDevice device) {
        Log.d(TAG, "Enter processWBSEvent()");
        HashMap<String, Integer> AudioParamCodec = mHeadsetAudioParam.get(device);
        if (AudioParamCodec != null && !AudioParamCodec.isEmpty()) {
            AudioParamCodec.put("codec", enable);
        } else {
            Log.e(TAG,"processWBSEvent: AudioParamNrec is null ");
        }

        if (enable == 2) {
            Log.d(TAG,
                    "AudioManager.setParameters: bt_wbs=on, device=" + device.getName() + "["
                            + device.getAddress() + "]");
            mAudioManager.setParameters(HEADSET_WBS + "=on");
        } else {
            Log.d(TAG,
                    "AudioManager.setParameters: bt_wbs=off, enable=" + enable
                            + ", device=" + device.getName() + "[" + device.getAddress() + "]");
            mAudioManager.setParameters(HEADSET_WBS + "=off");
        }
        Log.d(TAG, "Exit processWBSEvent()");
    }

    private void processAtChld(int chld, BluetoothDevice device) {
        Log.d(TAG, "Enter processAtChld()");
        if (device == null) {
            Log.w(TAG, "processAtChld device is null");
            return;
        }

        if (mPhoneProxy != null) {
            try {
                if (mPhoneProxy.processChld(chld)) {
                    atResponseCodeNative(
                            HeadsetHalConstants.AT_RESPONSE_OK, 0, getByteAddress(device));
                } else {
                    atResponseCodeNative(
                            HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                }
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for At+Chld");
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtChld()");
    }

    private void processSubscriberNumberRequest(BluetoothDevice device) {
        Log.d(TAG, "Enter processSubscriberNumberRequest()");
        if (device == null) {
            Log.w(TAG, "processSubscriberNumberRequest device is null");
            return;
        }

        if (mPhoneProxy != null) {
            try {
                String number = mPhoneProxy.getSubscriberNumber();
                if (number != null) {
                    atResponseStringNative("+CNUM: ,\"" + number + "\","
                                    + PhoneNumberUtils.toaFromString(number) + ",,4",
                            getByteAddress(device));
                    atResponseCodeNative(
                            HeadsetHalConstants.AT_RESPONSE_OK, 0, getByteAddress(device));
                } else {
                    Log.e(TAG, "getSubscriberNumber returns null");
                    atResponseCodeNative(
                            HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
                }
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for At+CNUM");
        }
        Log.d(TAG, "Exit processSubscriberNumberRequest()");
    }

    private void processAtCind(BluetoothDevice device) {
        Log.d(TAG, "Enter processAtCind()");
        int call, call_setup, call_state;
        // get the top of the Q
        HeadsetCallState tempCallState = mDelayedCSCallStates.peek();

        if (device == null) {
            Log.w(TAG, "processAtCind device is null");
            return;
        }

        /* Handsfree carkits expect that +CIND is properly responded to
         Hence we ensure that a proper response is sent
         for the virtual call too.*/
        if (isVirtualCallInProgress()) {
            call = mPhoneState.getNumActiveCall();
            call_setup = 0;
        } else {
            // regular phone call
            call = mPhoneState.getNumActiveCall();
            call_setup = mPhoneState.getNumHeldCall();
        }
        if(tempCallState != null &&
            tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING)
              call_state = HeadsetHalConstants.CALL_STATE_DIALING;
        else
              call_state = mPhoneState.getCallState();

        Log.d(TAG, "sending call state in CIND resp as " + call_state);

        cindResponseNative(mPhoneState.getService(), call,
                           call_setup, call_state,
                           mPhoneState.getSignal(), mPhoneState.getRoam(),
                           mPhoneState.getBatteryCharge(), getByteAddress(device));
        Log.d(TAG, "Exit processAtCind()");
    }

    private void processAtCops(BluetoothDevice device) {
        Log.d(TAG, "Enter processAtCops()");
        if (device == null) {
            Log.w(TAG, "processAtCops device is null");
            return;
        }

        if (mPhoneProxy != null) {
            try {
                String operatorName = mPhoneProxy.getNetworkOperator();
                if (operatorName == null || operatorName.equals("")) {
                    operatorName = "No operator";
                }
                copsResponseNative(operatorName, getByteAddress(device));
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
                copsResponseNative("", getByteAddress(device));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for At+COPS");
            copsResponseNative("", getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtCops()");
    }

    private void processAtClcc(BluetoothDevice device) {
        Log.d(TAG, "Enter processAtClcc()");
        if (device == null) {
            Log.w(TAG, "processAtClcc device is null");
            return;
        }

        if (mPhoneProxy != null) {
            try {
                if (isVirtualCallInProgress()) {
                    String phoneNumber = VOIP_CALL_NUMBER;
                    int type = PhoneNumberUtils.TOA_Unknown;
                    Log.d(TAG, "AtClcc response phone number: " + phoneNumber +
                                    " type: " + type);
                    // call still in dialling or alerting state
                    if (mPhoneState.getNumActiveCall() == 0)
                        clccResponseNative(1, 0, mPhoneState.getCallState(), 0, false,
                                            phoneNumber, type, getByteAddress(device));
                    else
                        clccResponseNative(1, 0, 0, 0, false, phoneNumber, type,
                                                       getByteAddress(device));

                    clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
                } else if (!mPhoneProxy.listCurrentCalls()) {
                    clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
                } else {
                    Log.d(TAG, "Starting CLCC response timeout for device: " + device);
                    Message m = obtainMessage(CLCC_RSP_TIMEOUT);
                    m.obj = getMatchingDevice(device);
                    sendMessageDelayed(m, CLCC_RSP_TIMEOUT_VALUE);
                }
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
                clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for At+CLCC");
            clccResponseNative(0, 0, 0, 0, false, "", 0, getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtClcc()");
    }

    private void processAtCscs(String atString, int type, BluetoothDevice device) {
        log("processAtCscs - atString = " + atString);
        if (mPhonebook != null) {
            mPhonebook.handleCscsCommand(atString, type, device);
        } else {
            Log.e(TAG, "Phonebook handle null for At+CSCS");
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtCscs()");
    }

    private void processAtCpbs(String atString, int type, BluetoothDevice device) {
        log("processAtCpbs - atString = " + atString);
        if (mPhonebook != null) {
            mPhonebook.handleCpbsCommand(atString, type, device);
        } else {
            Log.e(TAG, "Phonebook handle null for At+CPBS");
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtCpbs()");
    }

    private void processAtCpbr(String atString, int type, BluetoothDevice device) {
        log("processAtCpbr - atString = " + atString);
        if (mPhonebook != null) {
            mPhonebook.handleCpbrCommand(atString, type, device);
        } else {
            Log.e(TAG, "Phonebook handle null for At+CPBR");
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
        }
        Log.d(TAG, "Exit processAtCpbr()");
    }

    private void queryPhoneState() {
        if (mPhoneProxy != null) {
            try {
                mPhoneProxy.queryPhoneState();
            } catch (RemoteException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
            }
        } else {
            Log.e(TAG, "Handsfree phone proxy null for query phone state");
        }
    }

    /**
     * Find a character ch, ignoring quoted sections.
     * Return input.length() if not found.
     */
    static private int findChar(char ch, String input, int fromIndex) {
        Log.d(TAG, "Enter findChar()");
        for (int i = fromIndex; i < input.length(); i++) {
            char c = input.charAt(i);
            if (c == '"') {
                i = input.indexOf('"', i + 1);
                if (i == -1) {
                    return input.length();
                }
            } else if (c == ch) {
                return i;
            }
        }
        Log.d(TAG, "Exit findChar()");
        return input.length();
    }

    /**
     * Break an argument string into individual arguments (comma delimited).
     * Integer arguments are turned into Integer objects. Otherwise a String
     * object is used.
     */
    static private Object[] generateArgs(String input) {
        Log.d(TAG, "Enter generateArgs()");
        int i = 0;
        int j;
        ArrayList<Object> out = new ArrayList<Object>();
        while (i <= input.length()) {
            j = findChar(',', input, i);

            String arg = input.substring(i, j);
            try {
                out.add(new Integer(arg));
            } catch (NumberFormatException e) {
                out.add(arg);
            }

            i = j + 1; // move past comma
        }
        Log.d(TAG, "Exit generateArgs()");
        return out.toArray();
    }

    /**
     * Process vendor specific AT commands
     * @param atString AT command after the "AT+" prefix
     * @param device Remote device that has sent this command
     */
    private void processVendorSpecificAt(String atString, BluetoothDevice device) {
        Log.d(TAG, "Enter processVendorSpecificAt()");
        log("processVendorSpecificAt - atString = " + atString);

        // Currently we accept only SET type commands.
        int indexOfEqual = atString.indexOf("=");
        if (indexOfEqual == -1) {
            Log.e(TAG, "processVendorSpecificAt: command type error in " + atString);
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            return;
        }

        String command = atString.substring(0, indexOfEqual);
        Integer companyId = VENDOR_SPECIFIC_AT_COMMAND_COMPANY_ID.get(command);
        if (companyId == null) {
            Log.e(TAG, "processVendorSpecificAt: unsupported command: " + atString);
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            return;
        }

        String arg = atString.substring(indexOfEqual + 1);
        if (arg.startsWith("?")) {
            Log.e(TAG, "processVendorSpecificAt: command type error in " + atString);
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            return;
        }

        Object[] args = generateArgs(arg);
        if (command.equals(BluetoothHeadset.VENDOR_SPECIFIC_HEADSET_EVENT_XAPL)) {
            processAtXapl(args, device);
        }
        broadcastVendorSpecificEventIntent(
                command, companyId, BluetoothHeadset.AT_CMD_TYPE_SET, args, device);
        atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_OK, 0, getByteAddress(device));
        Log.d(TAG, "Exit processVendorSpecificAt()");
    }

    /**
     * Process AT+XAPL AT command
     * @param args command arguments after the equal sign
     * @param device Remote device that has sent this command
     */
    private void processAtXapl(Object[] args, BluetoothDevice device) {
        if (args.length != 2) {
            Log.w(TAG, "processAtXapl() args length must be 2: " + String.valueOf(args.length));
            return;
        }
        if (!(args[0] instanceof String) || !(args[1] instanceof Integer)) {
            Log.w(TAG, "processAtXapl() argument types not match");
            return;
        }
        // feature = 2 indicates that we support battery level reporting only
        atResponseStringNative("+XAPL=iPhone," + String.valueOf(2), getByteAddress(device));
    }

    private void processUnknownAt(String atString, BluetoothDevice device) {
        Log.d(TAG, "Enter processUnknownAt()");
        if (device == null) {
            Log.w(TAG, "processUnknownAt device is null");
            return;
        }
        log("processUnknownAt - atString = " + atString);
        String atCommand = parseUnknownAt(atString);
        int commandType = getAtCommandType(atCommand);
        if (atCommand.startsWith("+CSCS")) {
            processAtCscs(atCommand.substring(5), commandType, device);
        } else if (atCommand.startsWith("+CPBS")) {
            processAtCpbs(atCommand.substring(5), commandType, device);
        } else if (atCommand.startsWith("+CPBR")) {
            processAtCpbr(atCommand.substring(5), commandType, device);
        }
        else if (atCommand.startsWith("+CSQ")) {
            atResponseCodeNative(HeadsetHalConstants.AT_RESPONSE_ERROR, 4, getByteAddress(device));
        } else {
            processVendorSpecificAt(atCommand, device);
        }
        Log.d(TAG, "Exit processUnknownAt()");
    }

    private void processKeyPressed(BluetoothDevice device) {
        Log.d(TAG, "Enter processKeyPressed()");
        if (device == null) {
            Log.w(TAG, "processKeyPressed device is null");
            return;
        }

        if (mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_INCOMING) {
            if (mPhoneProxy != null) {
                try {
                    mPhoneProxy.answerCall();
                } catch (RemoteException e) {
                    Log.e(TAG, Log.getStackTraceString(new Throwable()));
                }
            } else {
                Log.e(TAG, "Handsfree phone proxy null for answering call");
            }
        } else if (mPhoneState.getNumActiveCall() > 0) {
            if (!isAudioOn()) {
                connectAudioNative(getByteAddress(mCurrentDevice));
            } else {
                if (mPhoneProxy != null) {
                    try {
                        mPhoneProxy.hangupCall();
                    } catch (RemoteException e) {
                        Log.e(TAG, Log.getStackTraceString(new Throwable()));
                    }
                } else {
                    Log.e(TAG, "Handsfree phone proxy null for hangup call");
                }
            }
        } else {
            String dialNumber = mPhonebook.getLastDialledNumber();
            if (dialNumber == null) {
                log("processKeyPressed, last dial number null");
                return;
            }
            Intent intent = new Intent(
                    Intent.ACTION_CALL_PRIVILEGED, Uri.fromParts(SCHEME_TEL, dialNumber, null));
            intent.setFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            mService.startActivity(intent);
        }
        Log.d(TAG, "Exit processKeyPressed()");
    }

    /**
     * Send HF indicator value changed intent
     * @param device Device whose HF indicator value has changed
     * @param ind_id Indicator ID [0-65535]
     * @param ind_value Indicator Value [0-65535], -1 means invalid but ind_id is supported
     */
    private void sendIndicatorIntent(BluetoothDevice device, int ind_id, int ind_value) {
        Intent intent = new Intent(BluetoothHeadset.ACTION_HF_INDICATORS_VALUE_CHANGED);
        intent.putExtra(BluetoothDevice.EXTRA_DEVICE, device);
        intent.putExtra(BluetoothHeadset.EXTRA_HF_INDICATORS_IND_ID, ind_id);
        intent.putExtra(BluetoothHeadset.EXTRA_HF_INDICATORS_IND_VALUE, ind_value);

        mService.sendBroadcast(intent, HeadsetService.BLUETOOTH_PERM);
    }

    private void processAtBind(String at_string, BluetoothDevice device) {
        log("processAtBind: " + at_string);

        // Parse the AT String to find the Indicator Ids that are supported
        int ind_id = 0;
        int iter = 0;
        int iter1 = 0;

        while (iter < at_string.length()) {
            iter1 = findChar(',', at_string, iter);
            String id = at_string.substring(iter, iter1);

            try {
                ind_id = Integer.valueOf(id);
            } catch (NumberFormatException e) {
                Log.e(TAG, Log.getStackTraceString(new Throwable()));
            }

            switch (ind_id) {
                case HeadsetHalConstants.HF_INDICATOR_ENHANCED_DRIVER_SAFETY:
                    log("Send Broadcast intent for the Enhanced Driver Safety indicator.");
                    sendIndicatorIntent(device, ind_id, -1);
                    break;
                case HeadsetHalConstants.HF_INDICATOR_BATTERY_LEVEL_STATUS:
                    log("Send Broadcast intent for the Battery Level indicator.");
                    sendIndicatorIntent(device, ind_id, -1);
                    break;
                default:
                    log("Invalid HF Indicator Received");
                    break;
            }

            iter = iter1 + 1; // move past comma
        }
        Log.d(TAG, "Exit processAtBind()");
    }

    private void processAtBiev(int indId, int indValue, BluetoothDevice device) {
        log("processAtBiev: ind_id=" + indId + ", ind_value=" + indValue);
        sendIndicatorIntent(device, indId, indValue);
    }

    private void processCpbr(Intent intent)
    {
        int atCommandResult = 0;
        int atCommandErrorCode = 0;
        BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
        Log.d(TAG, "Enter processCpbr()");
        // ASSERT: (headset != null) && headSet.isConnected()
        // REASON: mCheckingAccessPermission is true, otherwise resetAtState
        // has set mCheckingAccessPermission to false
        if (intent.getAction().equals(BluetoothDevice.ACTION_CONNECTION_ACCESS_REPLY)) {
            if (intent.getIntExtra(BluetoothDevice.EXTRA_CONNECTION_ACCESS_RESULT,
                                   BluetoothDevice.CONNECTION_ACCESS_NO)
                    == BluetoothDevice.CONNECTION_ACCESS_YES) {
                if (intent.getBooleanExtra(BluetoothDevice.EXTRA_ALWAYS_ALLOWED, false)) {
                    mCurrentDevice.setPhonebookAccessPermission(BluetoothDevice.ACCESS_ALLOWED);
                }
                atCommandResult = mPhonebook.processCpbrCommand(device);
            } else {
                if (intent.getBooleanExtra(BluetoothDevice.EXTRA_ALWAYS_ALLOWED, false)) {
                    mCurrentDevice.setPhonebookAccessPermission(
                            BluetoothDevice.ACCESS_REJECTED);
                }
            }
        }
        mPhonebook.setCpbrIndex(-1);
        mPhonebook.setCheckingAccessPermission(false);

        if (atCommandResult >= 0) {
            atResponseCodeNative(atCommandResult, atCommandErrorCode, getByteAddress(device));
        } else {
            log("processCpbr - RESULT_NONE");
        }
        Log.d(TAG, "Exit processCpbr()");
    }

    private void onConnectionStateChanged(int state, byte[] address) {
        Log.d(TAG, "Enter onConnectionStateChanged()");
        StackEvent event = new StackEvent(EVENT_TYPE_CONNECTION_STATE_CHANGED);
        event.valueInt = state;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onConnectionStateChanged()");
    }

    private void onAudioStateChanged(int state, byte[] address) {
        Log.d(TAG, "Enter onAudioStateChanged()");
        StackEvent event = new StackEvent(EVENT_TYPE_AUDIO_STATE_CHANGED);
        event.valueInt = state;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAudioStateChanged()");
    }

    private void onVrStateChanged(int state, byte[] address) {
        Log.d(TAG, "Enter onVrStateChanged()");
        StackEvent event = new StackEvent(EVENT_TYPE_VR_STATE_CHANGED);
        event.valueInt = state;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onVrStateChanged()");
    }

    private void onAnswerCall(byte[] address) {
        Log.d(TAG, "Enter onAnswerCall()");
        StackEvent event = new StackEvent(EVENT_TYPE_ANSWER_CALL);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAnswerCall()");
    }

    private void onHangupCall(byte[] address) {
        Log.d(TAG, "Enter onHangupCall()");
        StackEvent event = new StackEvent(EVENT_TYPE_HANGUP_CALL);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onHangupCall()");
    }

    private void onVolumeChanged(int type, int volume, byte[] address) {
        Log.d(TAG, "Enter onVolumeChanged()");
        StackEvent event = new StackEvent(EVENT_TYPE_VOLUME_CHANGED);
        event.valueInt = type;
        event.valueInt2 = volume;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onVolumeChanged()");
    }

    private void onDialCall(String number, byte[] address) {
        Log.d(TAG, "Enter onDialCall()");
        StackEvent event = new StackEvent(EVENT_TYPE_DIAL_CALL);
        event.valueString = number;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onDialCall()");
    }

    private void onSendDtmf(int dtmf, byte[] address) {
        Log.d(TAG, "Enter onSendDtmf()");
        StackEvent event = new StackEvent(EVENT_TYPE_SEND_DTMF);
        event.valueInt = dtmf;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onSendDtmf()");
    }

    private void onNoiceReductionEnable(boolean enable, byte[] address) {
        Log.d(TAG, "Enter onNoiceReductionEnable()");
        StackEvent event = new StackEvent(EVENT_TYPE_NOICE_REDUCTION);
        event.valueInt = enable ? 1 : 0;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onNoiceReductionEnable()");
    }

    private void onWBS(int codec, byte[] address) {
        Log.d(TAG, "Enter onWBS()");
        StackEvent event = new StackEvent(EVENT_TYPE_WBS);
        event.valueInt = codec;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onWBS()");
    }

    private void onAtChld(int chld, byte[] address) {
        Log.d(TAG, "Enter onAtChld()");
        StackEvent event = new StackEvent(EVENT_TYPE_AT_CHLD);
        event.valueInt = chld;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtChld()");
    }

    private void onAtCnum(byte[] address) {
        Log.d(TAG, "Enter onAtCnum()");
        StackEvent event = new StackEvent(EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtCnum()");
    }

    private void onAtCind(byte[] address) {
        Log.d(TAG, "Enter onAtCind()");
        StackEvent event = new StackEvent(EVENT_TYPE_AT_CIND);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtCind()");
    }

    private void onAtCops(byte[] address) {
        Log.d(TAG, "Enter onAtCops()");
        StackEvent event = new StackEvent(EVENT_TYPE_AT_COPS);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtCops()");
    }

    private void onAtClcc(byte[] address) {
        Log.d(TAG, "Enter onAtClcc()");
        StackEvent event = new StackEvent(EVENT_TYPE_AT_CLCC);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtClcc()");
    }

    private void onUnknownAt(String atString, byte[] address) {
        Log.d(TAG, "Enter onUnknownAt()");
        StackEvent event = new StackEvent(EVENT_TYPE_UNKNOWN_AT);
        event.valueString = atString;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onUnknownAt()");
    }

    private void onKeyPressed(byte[] address) {
        Log.d(TAG, "Enter onKeyPressed()");
        StackEvent event = new StackEvent(EVENT_TYPE_KEY_PRESSED);
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onKeyPressed()");
    }

    private void onATBind(String atString, byte[] address) {
        Log.d(TAG, "Enter onAtBind()");
        StackEvent event = new StackEvent(EVENT_TYPE_BIND);
        event.valueString = atString;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtBind()");
    }

    private void onATBiev(int ind_id, int ind_value, byte[] address) {
        Log.d(TAG, "Enter onAtBiev()");
        StackEvent event = new StackEvent(EVENT_TYPE_BIEV);
        event.valueInt = ind_id;
        event.valueInt2 = ind_value;
        event.device = getDevice(address);
        sendMessage(STACK_EVENT, event);
        Log.d(TAG, "Exit onAtBiev()");
    }

    private void processIntentBatteryChanged(Intent intent) {
        Log.d(TAG, "Enter processIntentBatteryChanged()");
        int batteryLevel = intent.getIntExtra("level", -1);
        int scale = intent.getIntExtra("scale", -1);
        if (batteryLevel == -1 || scale == -1 || scale == 0) {
            Log.e(TAG, "Bad Battery Changed intent: " + batteryLevel + "," + scale);
            return;
        }
        batteryLevel = batteryLevel * 5 / scale;
        mPhoneState.setBatteryCharge(batteryLevel);
        Log.d(TAG, "Exit processIntentBatteryChanged()");
    }

    private void processDeviceStateChanged(HeadsetDeviceState deviceState) {
        Log.d(TAG, "Enter processDeviceStateChanged()");
        notifyDeviceStatusNative(deviceState.mService, deviceState.mRoam, deviceState.mSignal,
                deviceState.mBatteryCharge);
        Log.d(TAG, "Exit processDeviceStateChanged()");
    }

    private void processSendClccResponse(HeadsetClccResponse clcc) {
        Log.d(TAG, "Enter processSendClccResponse()");
        BluetoothDevice device = getDeviceForMessage(CLCC_RSP_TIMEOUT);
        if (device == null) {
            Log.w(TAG, "device is null, not sending clcc response");
            return;
        }
        if (clcc.mIndex == 0) {
            getHandler().removeMessages(CLCC_RSP_TIMEOUT, device);
        }

        // get the top of the Q
        HeadsetCallState tempCallState = mDelayedCSCallStates.peek();

        /* Send call state DIALING if call alerting update is still in the Q */
        if (clcc.mStatus == HeadsetHalConstants.CALL_STATE_ALERTING &&
            tempCallState != null &&
            tempCallState.mCallState == HeadsetHalConstants.CALL_STATE_ALERTING) {
            Log.d(TAG, "sending call status as DIALING");
            clccResponseNative(clcc.mIndex, clcc.mDirection, HeadsetHalConstants.CALL_STATE_DIALING,
                    clcc.mMode, clcc.mMpty, clcc.mNumber, clcc.mType, getByteAddress(device));
        } else {
            Log.d(TAG, "sending call status as " + clcc.mStatus);
            clccResponseNative(clcc.mIndex, clcc.mDirection, clcc.mStatus, clcc.mMode, clcc.mMpty,
                           clcc.mNumber, clcc.mType, getByteAddress(device));
        }
        Log.d(TAG, "Exit processSendClccResponse()");
    }

    private void processSendVendorSpecificResultCode(HeadsetVendorSpecificResultCode resultCode) {
        Log.d(TAG, "Enter processSendVendorSpecificResultCode()");
        String stringToSend = resultCode.mCommand + ": ";
        if (resultCode.mArg != null) {
            stringToSend += resultCode.mArg;
        }
        atResponseStringNative(stringToSend, getByteAddress(resultCode.mDevice));
        Log.d(TAG, "Exit processSendVendorSpecificResultCode()");
    }

    private String getCurrentDeviceName(BluetoothDevice device) {
        Log.d(TAG, "Enter getCurrentDeviceName()");
        String defaultName = "<unknown>";

        if (device == null) {
            return defaultName;
        }

        String deviceName = device.getName();
        if (deviceName == null) {
            return defaultName;
        }
        Log.d(TAG, "Exit getCurrentDeviceName()");
        return deviceName;
    }

    private byte[] getByteAddress(BluetoothDevice device) {
        Log.d(TAG, "getByteAddress()");
        return Utils.getBytesFromAddress(device.getAddress());
    }

    private BluetoothDevice getDevice(byte[] address) {
        Log.d(TAG, "getDevice()");
        return mAdapter.getRemoteDevice(Utils.getAddressStringFromByte(address));
    }

    private boolean isRinging() {
        return mPhoneState.getCallState() == HeadsetHalConstants.CALL_STATE_INCOMING;
    }

    boolean isInCall() {
        Log.d(TAG, "isInCall()");
        return ((mPhoneState.getNumActiveCall() > 0) || (mPhoneState.getNumHeldCall() > 0) ||
                ((mPhoneState.getCallState() != HeadsetHalConstants.CALL_STATE_IDLE)));
    }

    // Accept incoming SCO only when there is in-band ringing, incoming call,
    // active call, VR activated, active VOIP call
    private boolean isScoAcceptable() {
        Log.d(TAG, "isScoAcceptable()");
        if (mForceScoAudio) return true;
        return mAudioRouteAllowed && (mVoiceRecognitionStarted ||
               ((mPhoneState.getNumActiveCall() > 0) || (mPhoneState.getNumHeldCall() > 0) ||
                ((mPhoneState.getCallState() != HeadsetHalConstants.CALL_STATE_IDLE) &&
                 (mPhoneState.getCallState() != HeadsetHalConstants.CALL_STATE_INCOMING)))
                           || (BluetoothHeadset.isInbandRingingSupported(mService) && isRinging()));
    }

    boolean isScoOrCallActive() {
        Log.d(TAG, "isScoOrCallActive(): Check for SCO as well as call status.");
        if (isInCall() || (mActiveScoDevice != null)) {
            return true;
        } else {
            return false;
        }
    }

    boolean isConnected() {
        Log.d(TAG, "isConnected()");
        IState currentState = getCurrentState();
        return (currentState == mConnected || currentState == mAudioOn);
    }

    boolean okToConnect(BluetoothDevice device) {
        Log.d(TAG, "Enter okToConnect()");
        AdapterService adapterService = AdapterService.getAdapterService();
        int priority = mService.getPriority(device);
        boolean ret = false;
        // check if this is an incoming connection in Quiet mode.
        if ((adapterService == null)
                || ((adapterService.isQuietModeEnabled() == true) && (mTargetDevice == null))) {
            ret = false;
        }
        // check priority and accept or reject the connection. if priority is undefined
        // it is likely that our SDP has not completed and peer is initiating the
        // connection. Allow this connection, provided the device is bonded
        else if ((BluetoothProfile.PRIORITY_OFF < priority)
                || ((BluetoothProfile.PRIORITY_UNDEFINED == priority)
                           && (device.getBondState() != BluetoothDevice.BOND_NONE))) {
            ret = true;
        }
        Log.d(TAG, "Exit okToConnect()");
        return ret;
    }

    boolean isConnectedDeviceBlacklistedforIncomingCall() {
        // Checking for the Blacklisted device Addresses
        if (max_hf_connections < 2) {
            BluetoothDevice device = mConnectedDevicesList.get(0);
            for (int j = 0; j < BlacklistDeviceAddrToDelayCallInd.length;j++) {
                 String addr = BlacklistDeviceAddrToDelayCallInd[j];
                 if (device.toString().toLowerCase().startsWith(addr.toLowerCase())) {
                     Log.d(TAG,"Remote device address Blacklisted for sending delay");
                     return true;
                 }
            }
        }
        return false;
    }

    boolean isDeviceBlacklistedforConnectionRetry(BluetoothDevice device) {
        for (int j = 0; j < BlacklistDeviceAddrForNotRetrying.length;j++) {
            String addr = BlacklistDeviceAddrForNotRetrying[j];
            if (device.toString().toLowerCase().startsWith(addr.toLowerCase())) {
                Log.d(TAG,"Remote device " + device.toString() + " blacklisted for not retrying");
                return true;
            }
        }
        return false;
    }

    private void sendVoipConnectivityNetworktype(boolean isVoipStarted) {
        Log.d(TAG, "Enter sendVoipConnectivityNetworktype()");
        NetworkInfo networkInfo = mConnectivityManager.getActiveNetworkInfo();
        if (networkInfo == null || !networkInfo.isAvailable() || !networkInfo.isConnected()) {
            Log.e(TAG, "No connected/available connectivity network, don't update soc");
            return;
        }

        if (networkInfo.getType() == ConnectivityManager.TYPE_MOBILE) {
            log("Voip/VoLTE started/stopped on n/w TYPE_MOBILE, don't update to soc");
        } else if (networkInfo.getType() == ConnectivityManager.TYPE_WIFI) {
            log("Voip/VoLTE started/stopped on n/w TYPE_WIFI, update n/w type & start/stop to soc");
            voipNetworkWifiInfoNative(isVoipStarted, true);
        } else {
            log("Voip/VoLTE started/stopped on some other n/w, don't update to soc");
        }
        Log.d(TAG, "Exit sendVoipConnectivityNetworktype()");
    }


    private void processAudioServerRestarted() {
        Log.d(TAG, "Enter processAudioServerRestarted()");
        if (mActiveScoDevice != null) {
            setAudioParameters(mActiveScoDevice);
            mAudioManager.setParameters("BT_SCO=on");
            mAudioManager.setBluetoothScoOn(true);
            log("AudioOn state: processAudioServerRestarted, " +
                           "fake broadcasting for audio state connected");
            broadcastAudioState(mActiveScoDevice, BluetoothHeadset.STATE_AUDIO_CONNECTED,
                    BluetoothHeadset.STATE_AUDIO_DISCONNECTED);
        }
    }

    @Override
    protected void log(String msg) {
        if (DBG) {
            super.log(msg);
        }
    }

    public void handleAccessPermissionResult(Intent intent) {
        Log.d(TAG, "Enter handleAccessPermissionResult()");
        log("handleAccessPermissionResult");
        BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
        if (mPhonebook != null) {
            if (!mPhonebook.getCheckingAccessPermission()) {
                return;
            }

            Message m = obtainMessage(PROCESS_CPBR);
            m.obj = intent;
            sendMessage(m);
        } else {
            Log.e(TAG, "Phonebook handle null");
            if (device != null) {
                atResponseCodeNative(
                        HeadsetHalConstants.AT_RESPONSE_ERROR, 0, getByteAddress(device));
            }
        }
        Log.d(TAG, "Exit handleAccessPermissionResult()");
    }


    public class AudioPlayer implements Runnable {
        AudioTrack mAudioTrack;
        int mBufferSize;

        boolean mPlay;
        boolean mIsPlaying;

        short[] mAudioData;

        Thread mFillerThread = null;

        public AudioPlayer() {
            mBufferSize = 0;
            mBufferSize =
                    AudioTrack.getMinBufferSize(
                        8000,
                        AudioFormat.CHANNEL_OUT_MONO,
                        AudioFormat.ENCODING_PCM_16BIT);
            mPlay = false;
            mIsPlaying = false;
            if (mBufferSize <= 0) {
                Log.e(TAG, "audio track buffer size not valid");
                return;
            }

            // setup audio data (silence will suffice)
            mAudioData = new short[mBufferSize];
            for (int index = 0; index < mBufferSize; index++) {
                 mAudioData[index] = 0;
            }
        }

        public boolean isPlaying() {
            synchronized (this) {
                return mIsPlaying;
            }
        }

        public void start() {
            if (mPlay == true)
                return;

            if (mBufferSize <= 0) {
                mBufferSize =
                        AudioTrack.getMinBufferSize(
                            8000,
                            AudioFormat.CHANNEL_OUT_MONO,
                            AudioFormat.ENCODING_PCM_16BIT);

                if (mBufferSize <= 0) {
                    Log.e(TAG, "In start, audio track buffer size not valid");
                    return;
                }
                // setup audio data (silence will suffice)
                mAudioData = new short[mBufferSize];
                for (int index = 0; index < mBufferSize; index++) {
                     mAudioData[index] = 0;
                }
            }
            mPlay = true;
            mFillerThread = new Thread(this);
            if(mFillerThread != null)
               mFillerThread.start();
        }

        public void stop() {
            mPlay = false;

            try {
                Log.d(TAG, "waiting for audio track thread to exit");
                if(mFillerThread != null)
                   mFillerThread.join();
                Log.d(TAG, "audio track thread exited or timed out");
            } catch (InterruptedException ex) {
            }

            mFillerThread = null;
        }

        @Override
        public void run() {
            try {
                mAudioTrack =
                    new AudioTrack(
                        AudioManager.STREAM_VOICE_CALL,
                        8000,
                        AudioFormat.CHANNEL_OUT_MONO,
                        AudioFormat.ENCODING_PCM_16BIT,
                        mBufferSize,
                        AudioTrack.MODE_STREAM);
            } catch (IllegalArgumentException e) {
                Log.e(TAG, "Illegal arguments exception while creating Audio Track");
            }

            Process.setThreadPriority(Process.THREAD_PRIORITY_URGENT_AUDIO);
             if(mAudioTrack == null){
              Log.e(TAG, "mAudioTrack is null, returning");
              return;
             }
            if(mAudioTrack.getState()==AudioTrack.STATE_UNINITIALIZED){
               Log.e(TAG, "mAudioTrack state is UNINITIALIZED, returning");
               mAudioTrack.release();
               mAudioTrack = null;
               return;
              }
            if (mAudioTrack != null) {
                synchronized (this) {
                    mIsPlaying = true;
                }
                try {
                    mAudioTrack.play();
                } catch (IllegalStateException e) {
                    Log.e(TAG, "Exception while starting playback");
                }
            }
            while (mAudioTrack != null && mPlay) {
                mAudioTrack.write(mAudioData, 0, mBufferSize);
            }

            if (mAudioTrack != null) {
                Log.d(TAG, "stopping audio track");
                try {
                    mAudioTrack.stop();
                } catch (IllegalStateException e) {
                    Log.e(TAG, "Exception while stopping playback");
                }
            }

            synchronized (this) {
                mIsPlaying = false;
            }

            Log.d(TAG, "releasing audio track");
            if (mAudioTrack != null) {
                mAudioTrack.release();
                mAudioTrack = null;
            }
        }
    }


    private static final String SCHEME_TEL = "tel";

    // Event types for STACK_EVENT message
    final private static int EVENT_TYPE_NONE = 0;
    final private static int EVENT_TYPE_CONNECTION_STATE_CHANGED = 1;
    final private static int EVENT_TYPE_AUDIO_STATE_CHANGED = 2;
    final private static int EVENT_TYPE_VR_STATE_CHANGED = 3;
    final private static int EVENT_TYPE_ANSWER_CALL = 4;
    final private static int EVENT_TYPE_HANGUP_CALL = 5;
    final private static int EVENT_TYPE_VOLUME_CHANGED = 6;
    final private static int EVENT_TYPE_DIAL_CALL = 7;
    final private static int EVENT_TYPE_SEND_DTMF = 8;
    final private static int EVENT_TYPE_NOICE_REDUCTION = 9;
    final private static int EVENT_TYPE_AT_CHLD = 10;
    final private static int EVENT_TYPE_SUBSCRIBER_NUMBER_REQUEST = 11;
    final private static int EVENT_TYPE_AT_CIND = 12;
    final private static int EVENT_TYPE_AT_COPS = 13;
    final private static int EVENT_TYPE_AT_CLCC = 14;
    final private static int EVENT_TYPE_UNKNOWN_AT = 15;
    final private static int EVENT_TYPE_KEY_PRESSED = 16;
    final private static int EVENT_TYPE_WBS = 17;
    final private static int EVENT_TYPE_BIND = 18;
    final private static int EVENT_TYPE_BIEV = 19;

    private class StackEvent {
        int type = EVENT_TYPE_NONE;
        int valueInt = 0;
        int valueInt2 = 0;
        String valueString = null;
        BluetoothDevice device = null;

        private StackEvent(int type) {
            this.type = type;
        }
    }

    /*package*/ native boolean atResponseCodeNative(
            int responseCode, int errorCode, byte[] address);
    /*package*/ native boolean atResponseStringNative(String responseString, byte[] address);

    private native static void classInitNative();
    private native void initializeNative(int max_hf_clients, boolean inband_ring_enable);
    private native void cleanupNative();
    private native boolean connectHfpNative(byte[] address);
    private native boolean disconnectHfpNative(byte[] address);
    private native boolean connectAudioNative(byte[] address);
    private native boolean disconnectAudioNative(byte[] address);
    private native boolean startVoiceRecognitionNative(byte[] address);
    private native boolean stopVoiceRecognitionNative(byte[] address);
    private native boolean setVolumeNative(int volumeType, int volume, byte[] address);
    private native boolean cindResponseNative(int service, int numActive, int numHeld,
            int callState, int signal, int roam, int batteryCharge, byte[] address);
    private native boolean bindResponseNative(int ind_id, boolean ind_status, byte[] address);
    private native boolean notifyDeviceStatusNative(
            int networkState, int serviceType, int signal, int batteryCharge);

    private native boolean clccResponseNative(int index, int dir, int status, int mode,
            boolean mpty, String number, int type, byte[] address);
    private native boolean copsResponseNative(String operatorName, byte[] address);

    private native boolean phoneStateChangeNative(
            int numActive, int numHeld, int callState, String number, int type);
    private native boolean configureWBSNative(byte[] address, int condec_config);
    private native boolean voipNetworkWifiInfoNative(boolean isVoipStarted,
                                                     boolean isNetworkWifi);
    private native boolean setScoAllowedNative(boolean value);
}
