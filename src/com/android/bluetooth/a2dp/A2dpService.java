/*
 * Copyright (C) 2017, The Linux Foundation. All rights reserved.
 * Not a Contribution.
 */
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

package com.android.bluetooth.a2dp;

import android.bluetooth.BluetoothA2dp;
import android.bluetooth.BluetoothCodecConfig;
import android.bluetooth.BluetoothCodecStatus;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothProfile;
import android.bluetooth.BluetoothUuid;
import android.bluetooth.IBluetoothA2dp;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.media.AudioManager;
import android.os.ParcelUuid;
import android.provider.Settings;
import android.os.SystemProperties;
import android.util.Log;
import com.android.bluetooth.avrcp.Avrcp;
import com.android.bluetooth.btservice.ProfileService;
import com.android.bluetooth.Utils;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Provides Bluetooth A2DP profile, as a service in the Bluetooth application.
 * @hide
 */
public class A2dpService extends ProfileService {
    private static final boolean DBG = true;
    private static final String TAG="A2dpService";

    private A2dpStateMachine mStateMachine;
    private Avrcp mAvrcp;
    private final Object mBtA2dpLock = new Object();
    private final Object mBtAvrcpLock = new Object();

    private BroadcastReceiver mConnectionStateChangedReceiver = null;

    private class CodecSupportReceiver extends BroadcastReceiver {
        @Override
        public void onReceive(Context context, Intent intent) {
            if (!BluetoothA2dp.ACTION_CONNECTION_STATE_CHANGED.equals(intent.getAction())) {
                return;
            }
            int state = intent.getIntExtra(BluetoothProfile.EXTRA_STATE, -1);
            BluetoothDevice device = intent.getParcelableExtra(BluetoothDevice.EXTRA_DEVICE);
            if (state != BluetoothProfile.STATE_CONNECTED || device == null) {
                return;
            }
            // Each time a device connects, we want to re-check if it supports optional
            // codecs (perhaps it's had a firmware update, etc.) and save that state if
            // it differs from what we had saved before.
            int previousSupport = getSupportsOptionalCodecs(device);
            boolean supportsOptional = false;
            synchronized(mBtA2dpLock) {
                if (mStateMachine != null) {
                    if (mStateMachine.getCodecStatus() != null) {
                        for (BluetoothCodecConfig config :
                                mStateMachine.getCodecStatus().getCodecsSelectableCapabilities()) {
                            if (!config.isMandatoryCodec()) {
                                supportsOptional = true;
                                break;
                            }
                        }
                    } else {
                     Log.i(TAG,"getCodecStatus is NUll, hence aborting");
                    }
                }
            }
            if (previousSupport == BluetoothA2dp.OPTIONAL_CODECS_SUPPORT_UNKNOWN
                    || supportsOptional
                            != (previousSupport == BluetoothA2dp.OPTIONAL_CODECS_SUPPORTED)) {
                setSupportsOptionalCodecs(device, supportsOptional);
            }
            if (supportsOptional) {
                int enabled = getOptionalCodecsEnabled(device);
                if (enabled == BluetoothA2dp.OPTIONAL_CODECS_PREF_ENABLED) {
                    enableOptionalCodecs();
                } else if (enabled == BluetoothA2dp.OPTIONAL_CODECS_PREF_DISABLED) {
                    disableOptionalCodecs();
                }
            }
        }
    };

    private AudioManager mAudioManager;
    private static A2dpService sAd2dpService;
    static final ParcelUuid[] A2DP_SOURCE_UUID = {
        BluetoothUuid.AudioSource
    };
    static final ParcelUuid[] A2DP_SOURCE_SINK_UUIDS = {
        BluetoothUuid.AudioSource,
        BluetoothUuid.AudioSink
    };

    protected String getName() {
        return TAG;
    }

    protected IProfileServiceBinder initBinder() {
        return new BluetoothA2dpBinder(this);
    }

    protected boolean start() {
        int maxConnections = 1;
        int multiCastState = 0;
        boolean isSplitA2dpEnabled = false;
        int maxA2dpConnection =
                SystemProperties.getInt("persist.bt.max.a2dp.connections", 1);
        int a2dpMultiCastState =
                SystemProperties.getInt("persist.bt.enable.multicast", 0);
        String offloadSupported =
                SystemProperties.get("persist.vendor.bt.enable.splita2dp");
        if (DBG) Log.d(TAG, "START of A2dpService");
        // Split A2dp will be enabled by default
        if (offloadSupported.isEmpty() || "true".equals(offloadSupported)) {
            Log.i(TAG,"Split A2dp enabled");
            isSplitA2dpEnabled = true;
        }
        if (DBG) Log.d(TAG, "START of A2dpService");
        if (a2dpMultiCastState == 1)
                multiCastState = a2dpMultiCastState;
        if (maxA2dpConnection == 2)
                maxConnections = maxA2dpConnection;
        // enable soft hands-off also when multicast is enabled.
        if (multiCastState == 1 && maxConnections != 2) {
            Log.i(TAG,"Enable soft handsoff as multicast is enabled");
            maxConnections = 2;
        }
        log( "maxA2dpConnections = " + maxConnections);
        log( "multiCastState = " + multiCastState);
        mStateMachine = A2dpStateMachine.make(this, this,
                maxConnections, multiCastState, isSplitA2dpEnabled);
        setA2dpService(this);
        if (mConnectionStateChangedReceiver == null) {
            IntentFilter filter = new IntentFilter();
            filter.addAction(BluetoothA2dp.ACTION_CONNECTION_STATE_CHANGED);
            mConnectionStateChangedReceiver = new CodecSupportReceiver();
            registerReceiver(mConnectionStateChangedReceiver, filter);
        }
        mAudioManager = (AudioManager) getSystemService(Context.AUDIO_SERVICE);
        mAvrcp = Avrcp.make(this, this, maxConnections);
        if (DBG) Log.d(TAG, "Exit START of A2dpService");
        return true;
    }


    protected boolean stop() {
        if (DBG) Log.d(TAG, "STOP of A2dpService.");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.doQuit();
            }
        }
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.doQuit();
            }
        }
        if (DBG) Log.d(TAG, "Exit STOP of A2dpService");
        return true;
    }

    protected boolean cleanup() {
        if (DBG) Log.d(TAG, "Enter cleanup");
        if (mConnectionStateChangedReceiver != null) {
            unregisterReceiver(mConnectionStateChangedReceiver);
            mConnectionStateChangedReceiver = null;
        }
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.cleanup();
                mStateMachine = null;
            }
        }
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.cleanup();
                mAvrcp = null;
            }
        }
        clearA2dpService();
        if (DBG) Log.d(TAG, "Exit cleanup");
        return true;
    }

    //API Methods

    public static synchronized A2dpService getA2dpService(){
        if (sAd2dpService != null && sAd2dpService.isAvailable()) {
            if (DBG) Log.d(TAG, "getA2DPService(): returning " + sAd2dpService);
            return sAd2dpService;
        }
        if (DBG)  {
            if (sAd2dpService == null) {
                Log.d(TAG, "getA2dpService(): service is NULL");
            } else if (!(sAd2dpService.isAvailable())) {
                Log.d(TAG,"getA2dpService(): service is not available");
            }
        }
        return null;
    }

    private static synchronized void setA2dpService(A2dpService instance) {
        if (instance != null && instance.isAvailable()) {
            if (DBG) Log.d(TAG, "setA2dpService(): set to: " + sAd2dpService);
            sAd2dpService = instance;
        } else {
            if (DBG)  {
                if (sAd2dpService == null) {
                    Log.d(TAG, "setA2dpService(): service not available");
                } else if (!sAd2dpService.isAvailable()) {
                    Log.d(TAG,"setA2dpService(): service is cleaning up");
                }
            }
        }
    }

    private static synchronized void clearA2dpService() {
        sAd2dpService = null;
    }

    public boolean connect(BluetoothDevice device) {
        if (DBG) Log.d(TAG, "Enter connect");
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM,
                                       "Need BLUETOOTH ADMIN permission");

        if (getPriority(device) == BluetoothProfile.PRIORITY_OFF) {
            return false;
        }
        ParcelUuid[] featureUuids = device.getUuids();
        if ((BluetoothUuid.containsAnyUuid(featureUuids, A2DP_SOURCE_UUID)) &&
            !(BluetoothUuid.containsAllUuids(featureUuids ,A2DP_SOURCE_SINK_UUIDS))) {
            Log.e(TAG,"Remote does not have A2dp Sink UUID");
            return false;
        }

        int connectionState = BluetoothProfile.STATE_DISCONNECTED;
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                connectionState = mStateMachine.getConnectionState(device);
            }
        }
        if (connectionState == BluetoothProfile.STATE_CONNECTED ||
            connectionState == BluetoothProfile.STATE_CONNECTING) {
            return false;
        }

        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.sendMessage(A2dpStateMachine.CONNECT, device);
            }
        }
        if (DBG) Log.d(TAG, "Exit connect");
        return true;
    }

    boolean disconnect(BluetoothDevice device) {
        if (DBG) Log.d(TAG, "Enter Disconnect");
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM,
                                       "Need BLUETOOTH ADMIN permission");
        int connectionState = BluetoothProfile.STATE_DISCONNECTED;
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                connectionState = mStateMachine.getConnectionState(device);
            }
        }
        if (connectionState != BluetoothProfile.STATE_CONNECTED &&
            connectionState != BluetoothProfile.STATE_CONNECTING) {
            return false;
        }

        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.sendMessage(A2dpStateMachine.DISCONNECT, device);
            }
        }
        if (DBG) Log.d(TAG, "Exit disconnect");
        return true;
    }

    public List<BluetoothDevice> getConnectedDevices() {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getConnectedDevices();
            } else {
                List<BluetoothDevice> devices = new ArrayList<BluetoothDevice>();
                return devices;
            }
        }
    }

    List<BluetoothDevice> getDevicesMatchingConnectionStates(int[] states) {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getDevicesMatchingConnectionStates(states);
            } else {
                List<BluetoothDevice> deviceList = new ArrayList<BluetoothDevice>();
                return deviceList;
            }
        }
    }

    public int getConnectionState(BluetoothDevice device) {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getConnectionState(device);
            } else {
                Log.e(TAG,"connection state is disconnected:");
                return BluetoothProfile.STATE_DISCONNECTED;
            }
        }
    }

    public boolean setPriority(BluetoothDevice device, int priority) {
        if (DBG) Log.d(TAG, "Enter setPriority");
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM,
                                       "Need BLUETOOTH_ADMIN permission");
        Settings.Global.putInt(getContentResolver(),
            Settings.Global.getBluetoothA2dpSinkPriorityKey(device.getAddress()),
            priority);
        if (DBG) Log.d(TAG,"Saved priority " + device + " = " + priority);
        if (DBG) Log.d(TAG, "Exit setPriority");
        return true;
    }

    public int getPriority(BluetoothDevice device) {
        if (DBG) Log.d(TAG, "Enter getPriority");
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM,
                                       "Need BLUETOOTH_ADMIN permission");
        int priority = Settings.Global.getInt(getContentResolver(),
            Settings.Global.getBluetoothA2dpSinkPriorityKey(device.getAddress()),
            BluetoothProfile.PRIORITY_UNDEFINED);
        if (DBG) Log.d(TAG, "Exit getPriority");
        return priority;
    }

    /* Absolute volume implementation */
    public boolean isAvrcpAbsoluteVolumeSupported() {
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                return mAvrcp.isAbsoluteVolumeSupported();
            } else {
                return false;
            }
        }
    }

    public void adjustAvrcpAbsoluteVolume(int direction) {
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.adjustVolume(direction);
            }
        }
    }

    public void setAvrcpAbsoluteVolume(int volume) {
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.setAbsoluteVolume(volume);
            }
        }
    }

    public void setAvrcpAudioState(int state, BluetoothDevice device) {
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.setA2dpAudioState(state, device);
            }
        }
    }

    public List<BluetoothDevice> getA2dpPlayingDevice() {
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getPlayingDevice();
            } else {
                List<BluetoothDevice> devices = new ArrayList<BluetoothDevice>();
                return devices;
            }
        }
    }

    public boolean isMulticastEnabled() {
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.isMulticastEnabled();
            } else {
                return false;
            }
        }
    }

    public boolean isMulticastFeatureEnabled() {
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.isMulticastFeatureEnabled();
            } else {
                return false;
            }
        }
    }

    // return status of multicast,needed for blocking outgoing connections
    public boolean isMulticastOngoing(BluetoothDevice device) {

        Log.i(TAG,"audio isMusicActive is " + mAudioManager.isMusicActive());
        // we should never land is case where playing device size is bigger
        // than 2 still have safe check.
        if (device == null) {
            if ((getA2dpPlayingDevice().size() >= 2) &&
                    (mAudioManager.isMusicActive())) {
                return true;
            } else {
                return false;
            }
        }
        if ((getA2dpPlayingDevice().size() >= 2) &&
                mAudioManager.isMusicActive() &&
                !(getA2dpPlayingDevice().contains(device))) {
            return true;
        } else {
            return false;
        }
    }

    public void resetAvrcpBlacklist(BluetoothDevice device) {
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.resetBlackList(device.getAddress());
            }
        }
    }

    public boolean isA2dpPlaying(BluetoothDevice device) {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM,
                                       "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "isA2dpPlaying(" + device + ")");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.isPlaying(device);
            } else {
                return false;
            }
        }
    }

    public BluetoothCodecStatus getCodecStatus() {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "getCodecStatus()");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getCodecStatus();
            } else {
                return null;
            }
        }
    }

    public void setCodecConfigPreference(BluetoothCodecConfig codecConfig) {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "setCodecConfigPreference(): " + Objects.toString(codecConfig));
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.setCodecConfigPreference(codecConfig);
            }
        }
    }

    public void enableOptionalCodecs() {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "enableOptionalCodecs()");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.enableOptionalCodecs();
            }
        }
    }

    public void disableOptionalCodecs() {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM, "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "disableOptionalCodecs()");
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.disableOptionalCodecs();
            }
        }
    }

    public int getSupportsOptionalCodecs(BluetoothDevice device) {
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM, "Need BLUETOOTH_ADMIN permission");
        int support = Settings.Global.getInt(getContentResolver(),
                Settings.Global.getBluetoothA2dpSupportsOptionalCodecsKey(device.getAddress()),
                BluetoothA2dp.OPTIONAL_CODECS_SUPPORT_UNKNOWN);
        return support;
    }

    public void setSupportsOptionalCodecs(BluetoothDevice device, boolean doesSupport) {
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM, "Need BLUETOOTH_ADMIN permission");
        int value = doesSupport ? BluetoothA2dp.OPTIONAL_CODECS_SUPPORTED
                                : BluetoothA2dp.OPTIONAL_CODECS_NOT_SUPPORTED;
        Settings.Global.putInt(getContentResolver(),
                Settings.Global.getBluetoothA2dpSupportsOptionalCodecsKey(device.getAddress()),
                value);
    }

    public int getOptionalCodecsEnabled(BluetoothDevice device) {
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM, "Need BLUETOOTH_ADMIN permission");
        return Settings.Global.getInt(getContentResolver(),
                Settings.Global.getBluetoothA2dpOptionalCodecsEnabledKey(device.getAddress()),
                BluetoothA2dp.OPTIONAL_CODECS_PREF_UNKNOWN);
    }

    public void setOptionalCodecsEnabled(BluetoothDevice device, int value) {
        enforceCallingOrSelfPermission(BLUETOOTH_ADMIN_PERM, "Need BLUETOOTH_ADMIN permission");
        if (value != BluetoothA2dp.OPTIONAL_CODECS_PREF_UNKNOWN
                && value != BluetoothA2dp.OPTIONAL_CODECS_PREF_DISABLED
                && value != BluetoothA2dp.OPTIONAL_CODECS_PREF_ENABLED) {
            Log.w(TAG, "Unexpected value passed to setOptionalCodecsEnabled:" + value);
            return;
        }
        Settings.Global.putInt(getContentResolver(),
                Settings.Global.getBluetoothA2dpOptionalCodecsEnabledKey(device.getAddress()),
                value);
    }

    public BluetoothDevice getLatestdevice() {
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                return mStateMachine.getLatestdevice();
            } else {
                return null;
            }
        }
    }

    public boolean selectStream(BluetoothDevice device) {
        enforceCallingOrSelfPermission(BLUETOOTH_PERM,
                                       "Need BLUETOOTH permission");
        if (DBG) Log.d(TAG, "selectStream(" + device + ")");

        mStateMachine.sendMessage(A2dpStateMachine.SELECT_STREAM, device);
        return true;
    }

    //Binder object: Must be static class or memory leak may occur 
    private static class BluetoothA2dpBinder extends IBluetoothA2dp.Stub 
        implements IProfileServiceBinder {
        private A2dpService mService;

        private A2dpService getService() {
            if (!Utils.checkCaller()) {
                Log.w(TAG,"A2dp call not allowed for non-active user");
                return null;
            }

            if (mService != null && mService.isAvailable()) {
                return mService;
            }
            return null;
        }

        BluetoothA2dpBinder(A2dpService svc) {
            mService = svc;
        }

        public boolean cleanup()  {
            mService = null;
            return true;
        }

        public boolean connect(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return false;
            //do not allow new connections with active multicast
            if (service.isMulticastOngoing(device)) {
                Log.i(TAG,"A2dp Multicast is Ongoing, ignore Connection Request");
                return false;
            }
            return service.connect(device);
        }

        public boolean disconnect(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return false;
            return service.disconnect(device);
        }

        public List<BluetoothDevice> getConnectedDevices() {
            A2dpService service = getService();
            if (service == null) return new ArrayList<BluetoothDevice>(0);
            return service.getConnectedDevices();
        }

        public List<BluetoothDevice> getDevicesMatchingConnectionStates(int[] states) {
            A2dpService service = getService();
            if (service == null) return new ArrayList<BluetoothDevice>(0);
            return service.getDevicesMatchingConnectionStates(states);
        }

        public int getConnectionState(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return BluetoothProfile.STATE_DISCONNECTED;
            return service.getConnectionState(device);
        }

        public boolean setPriority(BluetoothDevice device, int priority) {
            A2dpService service = getService();
            if (service == null) return false;
            return service.setPriority(device, priority);
        }

        public int getPriority(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return BluetoothProfile.PRIORITY_UNDEFINED;
            return service.getPriority(device);
        }

        public boolean isAvrcpAbsoluteVolumeSupported() {
            A2dpService service = getService();
            if (service == null) return false;
            return service.isAvrcpAbsoluteVolumeSupported();
        }

        public void adjustAvrcpAbsoluteVolume(int direction) {
            A2dpService service = getService();
            if (service == null) return;
            service.adjustAvrcpAbsoluteVolume(direction);
        }

        public void setAvrcpAbsoluteVolume(int volume) {
            A2dpService service = getService();
            if (service == null) return;
            service.setAvrcpAbsoluteVolume(volume);
        }

        public boolean isA2dpPlaying(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return false;
            return service.isA2dpPlaying(device);
        }

        public BluetoothCodecStatus getCodecStatus() {
            A2dpService service = getService();
            if (service == null) return null;
            return service.getCodecStatus();
        }

        public void setCodecConfigPreference(BluetoothCodecConfig codecConfig) {
            A2dpService service = getService();
            if (service == null) return;
            service.setCodecConfigPreference(codecConfig);
        }

        public void enableOptionalCodecs() {
            A2dpService service = getService();
            if (service == null) return;
            service.enableOptionalCodecs();
        }

        public void disableOptionalCodecs() {
            A2dpService service = getService();
            if (service == null) return;
            service.disableOptionalCodecs();
        }

        public int supportsOptionalCodecs(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return BluetoothA2dp.OPTIONAL_CODECS_SUPPORT_UNKNOWN;
            return service.getSupportsOptionalCodecs(device);
        }

        public int getOptionalCodecsEnabled(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return BluetoothA2dp.OPTIONAL_CODECS_PREF_UNKNOWN;
            return service.getOptionalCodecsEnabled(device);
        }

        public void setOptionalCodecsEnabled(BluetoothDevice device, int value) {
            A2dpService service = getService();
            if (service == null) return;
            service.setOptionalCodecsEnabled(device, value);
        }

        public boolean selectStream(BluetoothDevice device) {
            A2dpService service = getService();
            if (service == null) return false;
            return service.selectStream(device);
        }
    };

    @Override
    public void dump(StringBuilder sb) {
        super.dump(sb);
        synchronized(mBtA2dpLock) {
            if (mStateMachine != null) {
                mStateMachine.dump(sb);
            }
        }
        synchronized(mBtAvrcpLock) {
            if (mAvrcp != null) {
                mAvrcp.dump(sb);
            }
        }
    }
}
