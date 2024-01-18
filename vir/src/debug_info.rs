#[cfg(debug_assertions)]
use lazy_static::lazy_static;

#[cfg(debug_assertions)]
use std::{
    collections::HashMap,
    sync::{atomic::{AtomicUsize, Ordering}, Mutex},
    backtrace::Backtrace
};

#[cfg(debug_assertions)]
lazy_static! {
    static ref DEBUG_DATA: Mutex<HashMap<usize, DebugInfoData>> = Mutex::new(HashMap::new());
    static ref COUNTER: AtomicUsize = AtomicUsize::new(0);
}

#[cfg(debug_assertions)]
pub struct DebugInfoData {
    pub backtrace: Backtrace,
    pub debug_notes: Vec<String>
}

#[cfg(debug_assertions)]
impl DebugInfoData {
    pub fn new() -> DebugInfoData {
        let backtrace = Backtrace::capture();
        DebugInfoData {
            backtrace,
            debug_notes: Vec::new()
        }
    }

    pub fn add_debug_note<S: Into<String>>(&mut self, note: S) {
        self.debug_notes.push(note.into());
    }
}

#[cfg(debug_assertions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DebugInfo(usize);

#[cfg(debug_assertions)]
pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(usize::MAX);

#[cfg(not(debug_assertions))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DebugInfo(());

#[cfg(not(debug_assertions))]
pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(());

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! add_debug_info {
    ($debug_info:expr, $msg: expr) => {
        ()
    };
}

#[cfg(debug_assertions)]
#[macro_export]
macro_rules! add_debug_note {
    ($debug_info:expr, $msg: expr) => {
        $debug_info.add_debug_note($msg)
    };
}

impl DebugInfo {

    pub fn to_debug_comment(&self) -> String {
        format!("/*\n{}\n*/", self.to_debug_string())
    }

    #[cfg(debug_assertions)]
    pub fn new() -> DebugInfo {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let data = DebugInfoData::new();
        DEBUG_DATA.lock().unwrap().insert(id, data);
        DebugInfo(id)
    }

    #[cfg(debug_assertions)]
    pub fn to_debug_string(&self) -> String {
        if self == &DEBUGINFO_NONE {
            return String::from("Entity not created with debug info");
        }
        let map = DEBUG_DATA.lock().unwrap();
        let data = map.get(&self.0).unwrap();
        format!("Notes: {:?}\n\nBacktrace:{}", data.debug_notes, data.backtrace)
    }

    #[cfg(debug_assertions)]
    pub fn add_debug_note(&self, note: String) {
        let mut map = DEBUG_DATA.lock().unwrap();
        let data = map.get_mut(&self.0).unwrap();
        data.add_debug_note(note);
    }

    #[cfg(debug_assertions)]
    pub const fn none() -> DebugInfo {
        DebugInfo(usize::MAX)
    }

    #[cfg(not(debug_assertions))]
    pub fn new() -> DebugInfo {
        DebugInfo(())
    }

    #[cfg(not(debug_assertions))]
    pub fn to_debug_string(&self) -> String {
        String::from("No debug info collected. Rebuild with debug assertions enabled.")
    }

    #[cfg(not(debug_assertions))]
    pub const fn none() -> DebugInfo {
        DebugInfo(())
    }
}
