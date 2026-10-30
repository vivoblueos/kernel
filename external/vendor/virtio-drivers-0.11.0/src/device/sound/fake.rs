//! Fake VirtIO sound device for tests.

use super::{
    CommandCode, VirtIOSndChmapInfo, VirtIOSndHdr, VirtIOSndJackInfo, VirtIOSndPcmInfo,
    VirtIOSndPcmStatus, VirtIOSndPcmXfer, VirtIOSndQueryInfo, VirtIOSoundConfig, CONTROL_QUEUE_IDX,
    QUEUE_SIZE, TX_QUEUE_IDX,
};
use crate::{
    config::ReadOnly,
    device::sound::{VirtIOSndPcmHdr, VirtIOSndPcmSetParams},
    transport::{
        fake::{FakeTransport, QueueStatus, State},
        DeviceType,
    },
};
use alloc::{sync::Arc, vec};
use core::{
    convert::{TryFrom, TryInto},
    mem::size_of,
    time::Duration,
};
use std::{
    iter::repeat_with,
    sync::{
        atomic::{AtomicBool, Ordering},
        Mutex,
    },
    thread::{self, JoinHandle},
};
use zerocopy::{FromBytes, IntoBytes};

#[derive(Clone, Debug)]
pub struct FakeSoundDevice {
    pub state: Arc<Mutex<State<VirtIOSoundConfig>>>,
    pub terminate: Arc<AtomicBool>,
    /// The paramaters set for each stream, if any.
    pub params: Arc<Mutex<Vec<Option<VirtIOSndPcmSetParams>>>>,
    /// The bytes send on the TX queue for each channel.
    pub played_bytes: Arc<Mutex<Vec<Vec<u8>>>>,
    pub jack_infos: Vec<VirtIOSndJackInfo>,
    pub pcm_infos: Vec<VirtIOSndPcmInfo>,
    pub chmap_infos: Vec<VirtIOSndChmapInfo>,
}

impl FakeSoundDevice {
    pub fn new(
        jack_infos: Vec<VirtIOSndJackInfo>,
        pcm_infos: Vec<VirtIOSndPcmInfo>,
        chmap_infos: Vec<VirtIOSndChmapInfo>,
    ) -> (Self, FakeTransport<VirtIOSoundConfig>) {
        let config_space = VirtIOSoundConfig {
            jacks: ReadOnly::new(jack_infos.len().try_into().unwrap()),
            streams: ReadOnly::new(pcm_infos.len().try_into().unwrap()),
            chmaps: ReadOnly::new(chmap_infos.len().try_into().unwrap()),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
            ],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Socket,
            max_queue_size: 32,
            device_features: 0,
            state: state.clone(),
        };
        let params = repeat_with(|| None).take(pcm_infos.len()).collect();
        let played_bytes = vec![vec![]; pcm_infos.len()];

        (
            Self {
                state,
                terminate: Arc::new(AtomicBool::new(false)),
                params: Arc::new(Mutex::new(params)),
                played_bytes: Arc::new(Mutex::new(played_bytes)),
                jack_infos,
                pcm_infos,
                chmap_infos,
            },
            transport,
        )
    }

    /// Start a background thread simulating the device.
    pub fn spawn(&self) -> JoinHandle<()> {
        let clone = self.clone();
        thread::spawn(move || clone.run())
    }

    /// Terminate the background thread for the device.
    pub fn terminate(&self) {
        self.terminate.store(true, Ordering::Release);
    }

    fn run(&self) {
        while !self.terminate.load(Ordering::Acquire) {
            if State::poll_queue_notified(&self.state, CONTROL_QUEUE_IDX) {
                println!("Control queue was notified.");

                while self
                    .state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(CONTROL_QUEUE_IDX, |request| {
                        self.handle_control_request(&request)
                    })
                {}
            } else if State::poll_queue_notified(&self.state, TX_QUEUE_IDX) {
                println!("TX queue was notified");
                while self
                    .state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(TX_QUEUE_IDX, |request| {
                        self.handle_tx(&request)
                    })
                {}
            } else {
                thread::sleep(Duration::from_millis(10));
            }
        }
    }

    fn handle_tx(&self, request: &[u8]) -> Vec<u8> {
        let header = VirtIOSndPcmXfer::read_from_prefix(&request)
            .expect("TX request too short")
            .0;
        self.played_bytes.lock().unwrap()[usize::try_from(header.stream_id).unwrap()]
            .extend(&request[size_of::<VirtIOSndPcmXfer>()..]);

        VirtIOSndPcmStatus {
            status: CommandCode::SOk.into(),
            latency_bytes: 0,
        }
        .as_bytes()
        .to_owned()
    }

    fn handle_control_request(&self, request: &[u8]) -> Vec<u8> {
        {
            let header = VirtIOSndHdr::read_from_prefix(&request)
                .expect("Control request too short")
                .0;
            let mut response = Vec::new();
            const R_JACK_INFO: u32 = CommandCode::RJackInfo as u32;
            const R_PCM_INFO: u32 = CommandCode::RPcmInfo as u32;
            const R_CHMAP_INFO: u32 = CommandCode::RChmapInfo as u32;
            const R_PCM_SET_PARAMS: u32 = CommandCode::RPcmSetParams as u32;
            const R_PCM_PREPARE: u32 = CommandCode::RPcmPrepare as u32;
            const R_PCM_START: u32 = CommandCode::RPcmStart as u32;
            const R_PCM_STOP: u32 = CommandCode::RPcmStop as u32;
            const R_PCM_RELEASE: u32 = CommandCode::RPcmRelease as u32;
            match header.command_code {
                R_JACK_INFO => {
                    let request = VirtIOSndQueryInfo::read_from_bytes(&request)
                        .expect("R_JACK_INFO control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndJackInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for jack_info in &self.jack_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(jack_info.as_bytes());
                    }
                }
                R_PCM_INFO => {
                    let request = VirtIOSndQueryInfo::read_from_bytes(&request)
                        .expect("R_PCM_INFO control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndPcmInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for pcm_info in &self.pcm_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(pcm_info.as_bytes());
                    }
                }
                R_CHMAP_INFO => {
                    let request = VirtIOSndQueryInfo::read_from_bytes(&request)
                        .expect("R_CHMAP_INFO control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndChmapInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for chmap_info in &self.chmap_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(chmap_info.as_bytes());
                    }
                }
                R_PCM_SET_PARAMS => {
                    let request = VirtIOSndPcmSetParams::read_from_bytes(&request)
                        .expect("R_PCM_SET_PARAMS request wrong length");
                    let stream_id = request.hdr.stream_id;
                    self.params.lock().unwrap()[usize::try_from(stream_id).unwrap()] =
                        Some(request);
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                }
                R_PCM_PREPARE | R_PCM_START | R_PCM_STOP | R_PCM_RELEASE => {
                    let _request =
                        VirtIOSndPcmHdr::read_from_bytes(&request).expect("Request wrong length");
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                }
                _ => {
                    panic!("Unexpected control request, header {:?}", header);
                }
            }
            response
        }
    }
}
