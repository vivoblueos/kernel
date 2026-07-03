// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

pub mod api;
pub mod event;
use super::Medium;
use crate::{
    alloc::string::ToString,
    asynk::channel::Sender,
    net::{
        link::{
            esp32_wlan::event::EventInfo,
            wifi_ops::{
                mark_scan_results_unavailable, try_mark_scan_results_pending,
                update_scan_results_cache, WifiScanConfig, WifiScanResult, WifiSecurity,
            },
            HwAddr, LinkKind, LinkLayer, WifiOps,
        },
        smoltcp::link::SmoltcpDevice,
        NetError,
    },
    scheduler, thread,
    thread::{Entry, SystemThreadStorage, ThreadKind, ThreadNode},
};
use alloc::{string::String, vec, vec::Vec};
use api::*;
use core::{
    mem::MaybeUninit,
    ptr::addr_of,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};
use esp_hal::ram;
use esp_wifi_sys_esp32c3::{
    c_types,
    include::{
        esp_err_t, esp_interface_t_ESP_IF_WIFI_STA, esp_supplicant_init, esp_wifi_connect_internal,
        esp_wifi_deinit_internal, esp_wifi_disconnect_internal, esp_wifi_get_mode,
        esp_wifi_init_internal, esp_wifi_internal_reg_rxcb, esp_wifi_scan_get_ap_num,
        esp_wifi_scan_get_ap_records, esp_wifi_scan_start, esp_wifi_set_config,
        esp_wifi_set_country, esp_wifi_set_mode, esp_wifi_set_protocols, esp_wifi_set_ps,
        esp_wifi_set_tx_done_cb, esp_wifi_start, esp_wifi_stop, g_wifi_default_wpa_crypto_funcs,
        wifi_ap_record_t, wifi_auth_mode_t, wifi_auth_mode_t_WIFI_AUTH_OPEN,
        wifi_auth_mode_t_WIFI_AUTH_WEP, wifi_auth_mode_t_WIFI_AUTH_WPA2_PSK,
        wifi_auth_mode_t_WIFI_AUTH_WPA2_WPA3_PSK, wifi_auth_mode_t_WIFI_AUTH_WPA3_PSK,
        wifi_auth_mode_t_WIFI_AUTH_WPA_PSK, wifi_auth_mode_t_WIFI_AUTH_WPA_WPA2_PSK, wifi_config_t,
        wifi_country_policy_t_WIFI_COUNTRY_POLICY_MANUAL, wifi_country_t, wifi_init_config_t,
        wifi_interface_t_WIFI_IF_STA, wifi_mode_t, wifi_mode_t_WIFI_MODE_NULL,
        wifi_mode_t_WIFI_MODE_STA, wifi_osi_funcs_t, wifi_protocols_t, wifi_ps_type_t_WIFI_PS_NONE,
        wifi_scan_config_t, wifi_scan_type_t_WIFI_SCAN_TYPE_ACTIVE,
        wifi_scan_type_t_WIFI_SCAN_TYPE_PASSIVE, wifi_sort_method_t_WIFI_CONNECT_AP_BY_SIGNAL,
        ESP_OK, ESP_WIFI_OS_ADAPTER_MAGIC, ESP_WIFI_OS_ADAPTER_VERSION, WIFI_INIT_CONFIG_MAGIC,
    },
};
use libc::IW_SCAN_TYPE_ACTIVE;
use smoltcp::{
    iface::{Interface, SocketSet},
    phy::{Device, Medium as SmoltcpMedium, RxToken, TxToken},
    time::Instant,
    wire::{HardwareAddress, IpAddress, IpCidr, Ipv4Address},
};
use spin::Once;

pub const WIFI_PROTOCOL_11B: u32 = 1;
pub const WIFI_PROTOCOL_11G: u32 = 2;
pub const WIFI_PROTOCOL_11N: u32 = 4;
pub const WIFI_PROTOCOL_LR: u32 = 8;
pub const WIFI_PROTOCOL_11A: u32 = 16;
pub const WIFI_PROTOCOL_11AC: u32 = 32;
pub const WIFI_PROTOCOL_11AX: u32 = 64;

const EVENTINFO_CHANNEL_SIZE: usize = 16;

#[repr(transparent)]
pub(super) struct InternalEventSender(Sender<event::EventInfo, EVENTINFO_CHANNEL_SIZE>);

/// Safety: `Sender` is not `Sync`, but `InternalEventSender` is private to this module and
/// only used by `event_post`, which is called from interrupt context. Treating it as `Sync` is
/// safe under that single-producer usage model.
unsafe impl Sync for InternalEventSender {}

/// Safety: initialized in `wifi_inner_init` before being used.
pub(super) static mut EVENT_SENDER: MaybeUninit<InternalEventSender> = MaybeUninit::uninit();

static WIFI_TX_INFLIGHT: AtomicUsize = AtomicUsize::new(0);

fn get_wlan_singleton() -> &'static WifiController {
    static WLAN_SINGLETON: Once<WifiController> = Once::new();
    WLAN_SINGLETON.call_once(|| WifiController {
        init_done: AtomicBool::new(false),
        started: AtomicBool::new(false),
        connected: AtomicBool::new(false),
    })
}

#[ram]
pub(crate) unsafe extern "C" fn esp_wifi_tx_done_cb(
    _ifidx: u8,
    _data: *mut u8,
    _data_len: *mut u16,
    _tx_status: bool,
) {
    WIFI_TX_INFLIGHT
        .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| {
            Some(x.saturating_sub(1))
        })
        .ok();
}

#[ram]
pub(crate) unsafe extern "C" fn recv_cb_sta(
    buffer: *mut c_types::c_void,
    len: u16,
    eb: *mut c_types::c_void,
) -> esp_err_t {
    todo!()
}

struct WifiController {
    init_done: AtomicBool,
    started: AtomicBool,
    connected: AtomicBool,
}

impl WifiController {
    /// Safety: Gated by `init_done` to ensure that the Wi-Fi API adapter is initialized only once.
    pub fn init(&self) -> Result<(), NetError> {
        if self
            .init_done
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            esp_api_adapter_init()?;

            // FIXME: Only support STA mode at now;
            let ret = unsafe {
                esp_wifi_internal_reg_rxcb(esp_interface_t_ESP_IF_WIFI_STA, Some(recv_cb_sta))
            };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_internal_reg_rxcb failed".to_string(),
                ));
            }

            let ret = unsafe { esp_wifi_set_tx_done_cb(Some(esp_wifi_tx_done_cb)) };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_set_tx_done_cb failed".to_string(),
                ));
            }

            let country_info = wifi_country_t {
                cc: [b'C' as i8, b'N' as i8, 0],
                schan: 1,
                nchan: 13,
                max_tx_power: 20,
                policy: wifi_country_policy_t_WIFI_COUNTRY_POLICY_MANUAL,
            };
            let ret = unsafe { esp_wifi_set_country(&country_info as *const wifi_country_t) };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_set_country failed".to_string(),
                ));
            }
        } else {
            log::warn!("Wi-Fi API adapter already initialized");
        }

        Ok(())
    }

    /// Safety: Gated by `started` to ensure that the Wi-Fi is started only once.
    fn start(&self) -> Result<(), NetError> {
        if self
            .started
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            let ret = unsafe { esp_wifi_set_mode(wifi_mode_t_WIFI_MODE_STA) };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_set_mode failed".to_string(),
                ));
            }

            let ret = unsafe { esp_wifi_start() };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_start failed".to_string(),
                ));
            }

            let mut current_mode: wifi_mode_t = wifi_mode_t_WIFI_MODE_NULL;
            let ret = unsafe { esp_wifi_get_mode(&mut current_mode) };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound(
                    "esp_wifi_get_mode failed".to_string(),
                ));
            }

            log::info!("Wi-Fi started successfully in mode {:?}", current_mode);
        } else {
            log::warn!("Wi-Fi already started");
        }

        Ok(())
    }

    fn stop(&self) -> Result<(), NetError> {
        if self
            .started
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            let ret = unsafe { esp_wifi_stop() };
            if ret != (ESP_OK as i32) {
                return Err(NetError::DeviceNotFound("esp_wifi_stop failed".to_string()));
            }
        } else {
            log::warn!("Wi-Fi already stopped");
        }

        Ok(())
    }
}

impl Drop for WifiController {
    fn drop(&mut self) {
        get_wlan_singleton().stop().ok();
    }
}

pub struct Esp32WlanLink {
    controller: &'static WifiController,
}

extern "C" fn wifi_inner_init() {
    if let Err(e) = get_wlan_singleton().init() {
        log::error!("Wi-Fi API adapter initialization failed: {:?}", e);
        return;
    }

    if let Err(e) = get_wlan_singleton().start() {
        log::error!("Wi-Fi start failed: {:?}", e);
        return;
    }
}

impl Esp32WlanLink {
    pub fn new() -> Self {
        static mut WIFI_INIT_STORAGE: SystemThreadStorage =
            SystemThreadStorage::new(ThreadKind::Normal);
        static mut WIFI_INIT: MaybeUninit<ThreadNode> = MaybeUninit::zeroed();

        // Spawn a thread to initialize the Wi-Fi API adapter and start the Wi-Fi.
        // Becasue the Esp32 Wi-Fi adapter must be initialized in a thread context,
        // we create a dedicated thread for this purpose.
        let wifi_init = crate::thread::build_static_thread(
            unsafe { &mut WIFI_INIT },
            unsafe { &mut WIFI_INIT_STORAGE },
            0,
            thread::IDLE,
            Entry::C(wifi_inner_init),
            ThreadKind::Normal,
        );
        let ok = scheduler::queue_ready_thread(thread::IDLE, wifi_init);
        debug_assert_eq!(ok, Ok(()));
        Self {
            controller: get_wlan_singleton(),
        }
    }

    pub fn mac_address(&self) -> [u8; 6] {
        blueos_driver::hwinfo::esp32c3::mac()
    }
}

impl LinkLayer for Esp32WlanLink {
    fn name(&self) -> alloc::string::String {
        String::from("wlan0")
    }

    fn medium(&self) -> super::Medium {
        Medium::Ethernet
    }

    fn mtu(&self) -> usize {
        1500
    }

    fn hw_addr(&self) -> Option<super::HwAddr> {
        Some(HwAddr::from_ethernet(blueos_driver::hwinfo::esp32c3::mac()))
    }

    fn can_send(&self) -> bool {
        false
    }

    fn can_recv(&self) -> bool {
        false
    }

    fn as_wifi(&mut self) -> Option<&mut dyn super::wifi_ops::WifiOps> {
        Some(self)
    }

    fn kind(&self) -> super::LinkKind {
        LinkKind::Wifi
    }
}

pub struct WifiTxToken {}

pub struct WifiRxToken {}

impl RxToken for WifiRxToken {
    fn consume<R, F>(self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        todo!()
    }
}

impl TxToken for WifiTxToken {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        todo!()
    }
}

impl Device for Esp32WlanLink {
    type RxToken<'a>
        = WifiRxToken
    where
        Self: 'a;
    type TxToken<'a>
        = WifiTxToken
    where
        Self: 'a;

    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        None
    }

    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        None
    }

    fn capabilities(&self) -> smoltcp::phy::DeviceCapabilities {
        let mut caps = smoltcp::phy::DeviceCapabilities::default();
        caps.max_transmission_unit = self.mtu();
        caps.max_burst_size = Some(1);
        caps.medium = SmoltcpMedium::Ethernet;
        caps
    }
}

impl SmoltcpDevice for Esp32WlanLink {
    fn create_smoltcp_iface(&mut self) -> (Interface, SocketSet<'static>) {
        use smoltcp::iface::Config;

        let config = Config::new(HardwareAddress::Ethernet(smoltcp::wire::EthernetAddress(
            self.mac_address(),
        )));
        let mut iface = Interface::new(
            config,
            self,
            Instant::from_millis(i64::try_from(crate::time::now().as_millis()).unwrap_or(0)),
        );
        iface.update_ip_addrs(|addrs| {
            let _ = addrs.push(IpCidr::new(IpAddress::v4(10, 232, 39, 110), 24));
        });
        let _ = iface
            .routes_mut()
            .add_default_ipv4_route(Ipv4Address::new(10, 232, 39, 109));
        let sockets = SocketSet::new(vec![]);
        (iface, sockets)
    }

    fn poll_smoltcp(&mut self, timestamp: Instant, iface: &mut Interface, sockets: &mut SocketSet) {
        iface.poll(timestamp, self, sockets);
    }
}

#[allow(non_upper_case_globals)]
fn wifi_security_from_authmode(authmode: wifi_auth_mode_t) -> WifiSecurity {
    match authmode {
        wifi_auth_mode_t_WIFI_AUTH_OPEN => WifiSecurity::Open,
        wifi_auth_mode_t_WIFI_AUTH_WEP => WifiSecurity::Wep,
        wifi_auth_mode_t_WIFI_AUTH_WPA_PSK => WifiSecurity::Wpa,
        wifi_auth_mode_t_WIFI_AUTH_WPA2_PSK | wifi_auth_mode_t_WIFI_AUTH_WPA_WPA2_PSK => {
            WifiSecurity::Wpa2
        }
        wifi_auth_mode_t_WIFI_AUTH_WPA3_PSK | wifi_auth_mode_t_WIFI_AUTH_WPA2_WPA3_PSK => {
            WifiSecurity::Wpa3
        }
        _ => WifiSecurity::Unknown,
    }
}

fn wifi_scan_result_from_record(record: &wifi_ap_record_t) -> WifiScanResult {
    let ssid_len = record
        .ssid
        .iter()
        .position(|&c| c == 0)
        .unwrap_or(record.ssid.len());
    let ssid = String::from(core::str::from_utf8(&record.ssid[..ssid_len]).unwrap_or(""));

    WifiScanResult {
        ssid,
        bssid: record.bssid,
        signal_dbm: record.rssi,
        channel: u16::from(record.primary),
        security: wifi_security_from_authmode(record.authmode),
    }
}

fn update_scan_results_from_driver(context: &str) {
    let mut bss_total = 0u16;
    let ret = unsafe { esp_wifi_scan_get_ap_num(&mut bss_total as *mut u16) };
    if ret != (ESP_OK as i32) || bss_total == 0 {
        log::warn!(
            "{}: no APs found (ret={}, count={})",
            context,
            ret,
            bss_total
        );
        update_scan_results_cache(Vec::new());
        return;
    }

    let mut records: Vec<MaybeUninit<wifi_ap_record_t>> = Vec::with_capacity(bss_total as usize);
    let mut record_count = bss_total;
    let ret = unsafe {
        esp_wifi_scan_get_ap_records(
            &mut record_count as *mut u16,
            records.as_mut_ptr() as *mut wifi_ap_record_t,
        )
    };
    if ret != (ESP_OK as i32) {
        log::warn!(
            "{}: failed to get AP records (ret={}, count={})",
            context,
            ret,
            record_count
        );
        update_scan_results_cache(Vec::new());
        return;
    }

    let records = unsafe {
        records.set_len(record_count as usize);
        core::slice::from_raw_parts(records.as_ptr() as *const wifi_ap_record_t, records.len())
    };
    let results = records.iter().map(wifi_scan_result_from_record).collect();
    log::info!("{}: cache ready ({} networks)", context, record_count);
    update_scan_results_cache(results);
}

impl WifiOps for Esp32WlanLink {
    fn scan(&mut self, config: &WifiScanConfig) -> Result<Vec<WifiScanResult>, NetError> {
        let mut cfg: wifi_scan_config_t = unsafe { core::mem::zeroed() };
        cfg.scan_type = if config.scan_type == IW_SCAN_TYPE_ACTIVE as u8 {
            wifi_scan_type_t_WIFI_SCAN_TYPE_ACTIVE
        } else {
            wifi_scan_type_t_WIFI_SCAN_TYPE_PASSIVE
        };

        if !try_mark_scan_results_pending() {
            log::warn!("WiFi scan already in progress");
            return Err(NetError::WouldBlock);
        }

        let ret = unsafe { esp_wifi_scan_start(&cfg as *const wifi_scan_config_t, false) };
        if ret != (ESP_OK as i32) {
            mark_scan_results_unavailable();
            log::error!("Failed to start WiFi scan: error code {}", ret);
            Err(NetError::NoRoute)
        } else {
            Ok(Vec::new())
        }
    }

    fn connect(&mut self, ssid: &str, passphrase: &str) -> Result<(), NetError> {
        log::info!(
            "WiFi connecting to SSID: {} (passphrase len: {})",
            ssid,
            passphrase.len()
        );

        let ssid_bytes = ssid.as_bytes();
        if ssid_bytes.len() > 32 {
            log::error!("WiFi connect: SSID too long: {}", ssid_bytes.len());
            return Err(NetError::NoRoute);
        }

        let pwd_bytes = passphrase.as_bytes();
        if pwd_bytes.len() > 64 {
            log::error!("WiFi connect: passphrase too long: {}", pwd_bytes.len());
            return Err(NetError::NoRoute);
        }

        unsafe {
            let mut cfg: wifi_config_t = core::mem::zeroed();

            cfg.sta.ssid[..ssid_bytes.len()].copy_from_slice(ssid_bytes);
            cfg.sta.password[..pwd_bytes.len()].copy_from_slice(pwd_bytes);

            cfg.sta.scan_method = 0; // WIFI_FAST_SCAN
            cfg.sta.bssid_set = false;
            cfg.sta.channel = 0;
            cfg.sta.listen_interval = 3;
            cfg.sta.sort_method = wifi_sort_method_t_WIFI_CONNECT_AP_BY_SIGNAL;
            cfg.sta.threshold.rssi = -99;
            cfg.sta.threshold.authmode = if passphrase.is_empty() {
                esp_wifi_sys_esp32c3::include::wifi_auth_mode_t_WIFI_AUTH_OPEN
            } else {
                esp_wifi_sys_esp32c3::include::wifi_auth_mode_t_WIFI_AUTH_WPA2_PSK
            };
            cfg.sta.threshold.rssi_5g_adjustment = 0;
            cfg.sta.pmf_cfg.capable = true;
            cfg.sta.pmf_cfg.required = false;
            cfg.sta.sae_pwe_h2e = 3;
            cfg.sta.failure_retry_cnt = 1;
            cfg.sta.sae_pk_mode = 0;

            // ── Disconnect any stale connection first ──
            // Must disconnect before calling esp_wifi_set_config, otherwise
            // set_config may return ESP_ERR_WIFI_STATE ("still connecting").
            // esp_wifi_disconnect_internal resets STA state from "connecting"
            // or "connected" back to "started" (state 1), allowing set_config
            // to proceed.
            let _ = esp_wifi_disconnect_internal();

            // ── Set STA config while WiFi is running ──
            // Per ESP-IDF documentation, esp_wifi_set_config can be called
            // only when the interface is enabled (i.e., WiFi is started).
            // When WiFi is already started and STA is in state 1 (started,
            // not connecting), wifi_set_config_process detects the config
            // change and triggers wifi_connect_process internally.
            // This is the same approach used by the esp-radio crate:
            // set_config() handles mode+config+start in one step, then
            // connect_impl() just calls esp_wifi_connect_internal().
            //
            // DO NOT use stop→set_config→start here! esp_wifi_stop()
            // deinitializes the WPA supplicant (clears WPA/WPA2 callback
            // registrations done by esp_supplicant_init), but esp_wifi_start()
            // does NOT re-register them. After stop→start, the supplicant
            // is dead and WPA2 authentication cannot trigger.
            let ret = esp_wifi_set_config(
                wifi_interface_t_WIFI_IF_STA,
                &cfg as *const wifi_config_t as *mut wifi_config_t,
            );
            if ret != (ESP_OK as i32) {
                log::error!("WiFi connect: esp_wifi_set_config failed: {}", ret);
                return Err(NetError::NoRoute);
            }

            let p = wifi_protocols_t {
                ghz_2g: (WIFI_PROTOCOL_11B | WIFI_PROTOCOL_11G | WIFI_PROTOCOL_11N) as u16,
                ghz_5g: 0,
            };
            let ret = esp_wifi_set_protocols(
                wifi_interface_t_WIFI_IF_STA,
                &p as *const wifi_protocols_t as *mut wifi_protocols_t,
            );
            if ret != (ESP_OK as i32) {
                log::error!("WiFi connect: esp_wifi_set_protocols failed: {}", ret);
                return Err(NetError::NoRoute);
            }

            // ── Trigger connection ──
            let ret = esp_wifi_connect_internal();
            if ret != (ESP_OK as i32) {
                log::error!("WiFi connect: esp_wifi_connect_internal failed: {}", ret);
                return Err(NetError::NoRoute);
            }
        }
        log::info!("WiFi connect triggered for SSID: {}", ssid);
        Ok(())
    }

    fn disconnect(&mut self) -> Result<(), NetError> {
        todo!()
    }

    fn signal_strength(&self) -> Result<i8, NetError> {
        // TODO: read RSSI from the connected AP
        Ok(-40)
    }
}

fn esp_api_adapter_init() -> Result<(), NetError> {
    debug_assert!(crate::arch::local_irq_enabled());

    let (mut tx, mut rx) = crate::asynk::channel::channel::<EventInfo, EVENTINFO_CHANNEL_SIZE>();
    unsafe {
        EVENT_SENDER.write(InternalEventSender(tx));
    }
    crate::asynk::spawn(async move {
        while let Ok(event) = rx.recv().await {
            match event {
                EventInfo::StationStart => {
                    log::debug!("Wi-Fi StationStart");
                    // set power save mode to none when connected, otherwise the Wi-Fi will not send data after a while.
                    let ret = unsafe { esp_wifi_set_ps(wifi_ps_type_t_WIFI_PS_NONE) };
                    if ret != (ESP_OK as i32) {
                        log::warn!("esp_wifi_set_ps failed: {}", ret);
                        break;
                    }
                    get_wlan_singleton().connected.store(true, Ordering::SeqCst);
                }
                EventInfo::StationStop => {
                    get_wlan_singleton()
                        .connected
                        .store(false, Ordering::SeqCst);
                }
                EventInfo::ScanDone {
                    status,
                    number,
                    scan_id,
                } => {
                    log::info!(
                        "ScanDone: status={} number={} scan_id={}",
                        status,
                        number,
                        scan_id
                    );
                    if status == 0 {
                        update_scan_results_from_driver("ScanDone");
                    } else {
                        log::warn!("ScanDone: scan failed with status {}", status);
                        mark_scan_results_unavailable();
                    }
                }
                EventInfo::StationConnected {
                    ssid,
                    bssid,
                    channel,
                    authmode,
                    aid,
                } => {
                    log::info!(
                        "WiFi StationConnected: ssid={:?} bssid={:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x} ch={} authmode={} aid={}",
                        ssid, bssid[0], bssid[1], bssid[2], bssid[3], bssid[4], bssid[5],
                        channel, authmode, aid
                    );
                }
                EventInfo::StationDisconnected { reason, .. } => {
                    log::info!("WiFi StationDisconnected: reason={}", reason);
                }
                _ => log::debug!("WiFi event: {:?}", event),
            }
        }
    });

    esp_wifi_init()?;

    let ret = unsafe { esp_wifi_set_mode(wifi_mode_t_WIFI_MODE_NULL) };
    if ret != (ESP_OK as i32) {
        return Err(NetError::DeviceNotFound(
            "esp_wifi_set_mode failed".to_string(),
        ));
    }

    Ok(())
}

#[no_mangle]
pub(crate) static __ESP_RADIO_G_WIFI_OSI_FUNCS: wifi_osi_funcs_t = wifi_osi_funcs_t {
    _version: ESP_WIFI_OS_ADAPTER_VERSION as i32,
    _env_is_chip: Some(env_is_chip),
    _set_intr: Some(set_intr),
    _clear_intr: Some(clear_intr),
    _set_isr: Some(set_isr),
    _ints_on: Some(ints_on),
    _ints_off: Some(ints_off),
    _is_from_isr: Some(is_from_isr),
    _spin_lock_create: Some(spin_lock_create),
    _spin_lock_delete: Some(spin_lock_delete),
    _wifi_int_disable: Some(wifi_int_disable),
    _wifi_int_restore: Some(wifi_int_restore),
    _task_yield_from_isr: Some(task_yield_from_isr),
    _semphr_create: Some(semphr_create),
    _semphr_delete: Some(semphr_delete),
    _semphr_take: Some(semphr_take),
    _semphr_give: Some(semphr_give),
    _wifi_thread_semphr_get: Some(wifi_thread_semphr_get),
    _mutex_create: Some(mutex_create),
    _recursive_mutex_create: Some(recursive_mutex_create),
    _mutex_delete: Some(mutex_delete),
    _mutex_lock: Some(mutex_lock),
    _mutex_unlock: Some(mutex_unlock),
    _queue_create: Some(queue_create),
    _queue_delete: Some(queue_delete),
    _queue_send: Some(queue_send),
    _queue_send_from_isr: Some(queue_send_from_isr),
    _queue_send_to_back: Some(queue_send_to_back),
    _queue_send_to_front: Some(queue_send_to_front),
    _queue_recv: Some(queue_recv),
    _queue_msg_waiting: Some(queue_msg_waiting),
    _event_group_create: Some(event_group_create),
    _event_group_delete: Some(event_group_delete),
    _event_group_set_bits: Some(event_group_set_bits),
    _event_group_clear_bits: Some(event_group_clear_bits),
    _event_group_wait_bits: Some(event_group_wait_bits),
    _task_create_pinned_to_core: Some(task_create_pinned_to_core),
    _task_create: Some(task_create),
    _task_delete: Some(task_delete),
    _task_delay: Some(task_delay),
    _task_ms_to_tick: Some(task_ms_to_tick),
    _task_get_current_task: Some(task_get_current_task),
    _task_get_max_priority: Some(task_get_max_priority),
    _malloc: Some(malloc),
    _free: Some(free),
    _event_post: Some(event_post),
    _get_free_heap_size: Some(get_free_heap_size),
    _rand: Some(rand),
    _dport_access_stall_other_cpu_start_wrap: Some(dport_access_stall_other_cpu_start_wrap),
    _dport_access_stall_other_cpu_end_wrap: Some(dport_access_stall_other_cpu_end_wrap),
    _wifi_apb80m_request: Some(wifi_apb80m_request),
    _wifi_apb80m_release: Some(wifi_apb80m_release),
    _phy_disable: Some(phy_disable),
    _phy_enable: Some(phy_enable),
    _phy_update_country_info: Some(phy_update_country_info),
    _read_mac: Some(read_mac),
    _timer_arm: Some(ets_timer_arm),
    _timer_disarm: Some(ets_timer_disarm),
    _timer_done: Some(ets_timer_done),
    _timer_setfn: Some(ets_timer_setfn),
    _timer_arm_us: Some(ets_timer_arm_us),
    _wifi_reset_mac: Some(wifi_reset_mac),
    _wifi_clock_enable: Some(wifi_clock_enable),
    _wifi_clock_disable: Some(wifi_clock_disable),
    _wifi_rtc_enable_iso: Some(wifi_rtc_enable_iso),
    _wifi_rtc_disable_iso: Some(wifi_rtc_disable_iso),
    _esp_timer_get_time: Some(__esp_radio_esp_timer_get_time),
    _nvs_set_i8: Some(nvs_set_i8),
    _nvs_get_i8: Some(nvs_get_i8),
    _nvs_set_u8: Some(nvs_set_u8),
    _nvs_get_u8: Some(nvs_get_u8),
    _nvs_set_u16: Some(nvs_set_u16),
    _nvs_get_u16: Some(nvs_get_u16),
    _nvs_open: Some(nvs_open),
    _nvs_close: Some(nvs_close),
    _nvs_commit: Some(nvs_commit),
    _nvs_set_blob: Some(nvs_set_blob),
    _nvs_get_blob: Some(nvs_get_blob),
    _nvs_erase_key: Some(nvs_erase_key),
    _get_random: Some(get_random),
    _get_time: Some(get_time),
    _random: Some(random),
    _slowclk_cal_get: Some(slowclk_cal_get),
    // FIXME: To be implemented in the future for logging in wifi driver.
    _log_write: None,
    // FIXME: To be implemented in the future for logging in wifi driver.
    _log_writev: None,
    _log_timestamp: Some(log_timestamp),
    _malloc_internal: Some(malloc_internal),
    _realloc_internal: Some(realloc_internal),
    _calloc_internal: Some(calloc_internal_wrapper),
    _zalloc_internal: Some(zalloc_internal),
    _wifi_malloc: Some(wifi_malloc),
    _wifi_realloc: Some(wifi_realloc),
    _wifi_calloc: Some(wifi_calloc),
    _wifi_zalloc: Some(wifi_zalloc),
    _wifi_create_queue: Some(wifi_create_queue),
    _wifi_delete_queue: Some(wifi_delete_queue),
    _coex_init: Some(coex_init),
    _coex_deinit: Some(coex_deinit),
    _coex_enable: Some(coex_enable),
    _coex_disable: Some(coex_disable),
    _coex_status_get: Some(coex_status_get),
    _coex_condition_set: None,
    _coex_wifi_request: Some(coex_wifi_request),
    _coex_wifi_release: Some(coex_wifi_release),
    _coex_wifi_channel_set: Some(coex_wifi_channel_set),
    _coex_event_duration_get: Some(coex_event_duration_get),
    _coex_pti_get: Some(coex_pti_get),
    _coex_schm_status_bit_clear: Some(coex_schm_status_bit_clear),
    _coex_schm_status_bit_set: Some(coex_schm_status_bit_set),
    _coex_schm_interval_set: Some(coex_schm_interval_set),
    _coex_schm_interval_get: Some(coex_schm_interval_get),
    _coex_schm_curr_period_get: Some(coex_schm_curr_period_get),
    _coex_schm_curr_phase_get: Some(coex_schm_curr_phase_get),
    _coex_register_start_cb: Some(coex_register_start_cb),
    _coex_schm_process_restart: Some(coex_schm_process_restart),
    _coex_schm_register_cb: Some(coex_schm_register_cb_wrapper),
    _coex_schm_flexible_period_set: Some(coex_schm_flexible_period_set),
    _coex_schm_flexible_period_get: Some(coex_schm_flexible_period_get),
    _coex_schm_get_phase_by_idx: Some(coex_schm_get_phase_by_idx),

    _magic: ESP_WIFI_OS_ADAPTER_MAGIC as i32,
};

#[no_mangle]
pub(crate) static mut G_WIFI_CONFIG: MaybeUninit<wifi_init_config_t> = MaybeUninit::zeroed();

fn esp_wifi_init() -> Result<(), NetError> {
    unsafe {
        G_WIFI_CONFIG.write(wifi_init_config_t {
            osi_funcs: (&__ESP_RADIO_G_WIFI_OSI_FUNCS) as *const wifi_osi_funcs_t
                as *mut wifi_osi_funcs_t,

            wpa_crypto_funcs: g_wifi_default_wpa_crypto_funcs,
            static_rx_buf_num: 10,
            dynamic_rx_buf_num: 32,
            tx_buf_type: esp_wifi_sys_esp32c3::include::CONFIG_ESP_WIFI_TX_BUFFER_TYPE as i32,
            static_tx_buf_num: 0,
            dynamic_tx_buf_num: 32,
            rx_mgmt_buf_type: esp_wifi_sys_esp32c3::include::CONFIG_ESP_WIFI_DYNAMIC_RX_MGMT_BUF
                as i32,
            rx_mgmt_buf_num: esp_wifi_sys_esp32c3::include::CONFIG_ESP_WIFI_RX_MGMT_BUF_NUM_DEF
                as i32,
            cache_tx_buf_num: esp_wifi_sys_esp32c3::include::WIFI_CACHE_TX_BUFFER_NUM as i32,
            csi_enable: true as i32,
            ampdu_rx_enable: true as i32,
            ampdu_tx_enable: true as i32,
            amsdu_tx_enable: false as i32,
            nvs_enable: 0,
            nano_enable: 0,
            rx_ba_win: 6,
            wifi_task_core_id: 0,
            beacon_max_len: esp_wifi_sys_esp32c3::include::WIFI_SOFTAP_BEACON_MAX_LEN as i32,
            mgmt_sbuf_num: esp_wifi_sys_esp32c3::include::WIFI_MGMT_SBUF_NUM as i32,
            feature_caps: __ESP_RADIO_G_WIFI_FEATURE_CAPS,
            sta_disconnected_pm: false,
            espnow_max_encrypt_num:
                esp_wifi_sys_esp32c3::include::CONFIG_ESP_WIFI_ESPNOW_MAX_ENCRYPT_NUM as i32,

            tx_hetb_queue_num: 3,
            dump_hesigb_enable: false,

            magic: WIFI_INIT_CONFIG_MAGIC as i32,
        });

        let ret = esp_wifi_init_internal(addr_of!(G_WIFI_CONFIG) as *const wifi_init_config_t);
        if ret != (ESP_OK as i32) {
            return Err(NetError::DeviceNotFound("esp_wifi_init failed".to_string()));
        }

        let ret = esp_supplicant_init();
        if ret != (ESP_OK as i32) {
            esp_wifi_deinit_internal();
            return Err(NetError::DeviceNotFound(
                "esp_supplicant_init failed".to_string(),
            ));
        }
    }

    Ok(())
}

const WIFI_ENABLE_WPA3_SAE: u64 = 1 << 0;
const WIFI_ENABLE_ENTERPRISE: u64 = 1 << 7;
const WIFI_FEATURE_CAPS: u64 = WIFI_ENABLE_WPA3_SAE | WIFI_ENABLE_ENTERPRISE;

#[unsafe(no_mangle)]
pub(super) static mut __ESP_RADIO_G_WIFI_FEATURE_CAPS: u64 = WIFI_FEATURE_CAPS;
