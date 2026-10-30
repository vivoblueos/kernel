// 1xx: Positive Preliminary Reply
pub const INITIATING: u32 = 100;
pub const RESTART_MARKER: u32 = 110;
pub const READY_MINUTE: u32 = 120;
pub const ALREADY_OPEN: u32 = 125;
pub const ABOUT_TO_SEND: u32 = 150;

// 2xx: Positive Completion Reply
pub const COMMAND_OK: u32 = 200;
pub const COMMAND_NOT_IMPLEMENTED: u32 = 202;
pub const SYSTEM: u32 = 211;
pub const DIRECTORY: u32 = 212;
pub const FILE: u32 = 213;
pub const HELP: u32 = 214;
pub const NAME: u32 = 215;
pub const READY: u32 = 220;
pub const CLOSING: u32 = 221;
pub const DATA_CONNECTION_OPEN: u32 = 225;
pub const CLOSING_DATA_CONNECTION: u32 = 226;
pub const PASSIVE_MODE: u32 = 227;
pub const LONG_PASSIVE_MODE: u32 = 228;
pub const EXTENDED_PASSIVE_MODE: u32 = 229;
pub const LOGGED_IN: u32 = 230;
pub const LOGGED_OUT: u32 = 231;
pub const LOGOUT_ACK: u32 = 232;
pub const AUTH_OK: u32 = 234;
pub const REQUESTED_FILE_ACTION_OK: u32 = 250;
pub const PATH_CREATED: u32 = 257;

// 3xx: Positive intermediate Reply
pub const NEED_PASSWORD: u32 = 331;
pub const LOGIN_NEED_ACCOUNT: u32 = 332;
pub const REQUEST_FILE_PENDING: u32 = 350;

// 4xx: Transient Negative Completion Reply
pub const NOT_AVAILABLE: u32 = 421;
pub const CANNOT_OPEN_DATA_CONNECTION: u32 = 425;
pub const TRANSER_ABORTED: u32 = 426;
pub const INVALID_CREDENTIALS: u32 = 430;
pub const HOST_UNAVAILABLE: u32 = 434;
pub const REQUEST_FILE_ACTION_IGNORED: u32 = 450;
pub const ACTION_ABORTED: u32 = 451;
pub const REQUESTED_ACTION_NOT_TAKEN: u32 = 452;

// 5xx: Permanent Negative Completion Reply
pub const BAD_COMMAND: u32 = 500;
pub const BAD_ARGUMENTS: u32 = 501;
pub const NOT_IMPLEMENTED: u32 = 502;
pub const BAD_SEQUENCE: u32 = 503;
pub const NOT_IMPLEMENTED_PARAMETER: u32 = 504;
pub const NOT_LOGGED_IN: u32 = 530;
pub const STORING_NEED_ACCOUNT: u32 = 532;
pub const FILE_UNAVAILABLE: u32 = 550;
pub const PAGE_TYPE_UNKNOWN: u32 = 551;
pub const EXCEEDED_STORAGE: u32 = 552;
pub const BAD_FILENAME: u32 = 553;
