#[cfg(debug_assertions)]
use lazy_static::lazy_static;

#[cfg(debug_assertions)]
use std::{
    collections::HashMap,
    sync::{atomic::{AtomicUsize, Ordering}, Mutex},
    backtrace::Backtrace
};

#[cfg(debug_assertions)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DebugInfo(usize);

#[cfg(not(debug_assertions))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DebugInfo(());

#[cfg(debug_assertions)]
lazy_static! {
    // TODO: make different CFG flag
    // TODO: put into vir arena
    // TODO: could be a vec
    static ref DEBUG_DATA: Mutex<HashMap<usize, DebugInfoData>> = Mutex::new(HashMap::new());
    static ref COUNTER: AtomicUsize = AtomicUsize::new(0);
}

#[cfg(debug_assertions)]
struct DebugInfoData {
    pub backtrace: Backtrace,
    pub debug_notes: Vec<String>
}

#[cfg(debug_assertions)]
impl DebugInfoData {
    fn new() -> DebugInfoData {
        let backtrace = Backtrace::capture();
        DebugInfoData {
            backtrace,
            debug_notes: Vec::new()
        }
    }

    fn add_debug_note(&mut self, note: String) {
        self.debug_notes.push(note);
    }
}

#[cfg(debug_assertions)]
pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(usize::MAX);

#[cfg(not(debug_assertions))]
pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(());

impl DebugInfo {


    #[cfg(debug_assertions)]
    pub fn new() -> DebugInfo {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        let data = DebugInfoData::new();
        DEBUG_DATA.lock().unwrap().insert(id, data);
        DebugInfo(id)
    }

    #[cfg(not(debug_assertions))]
    pub fn new() -> DebugInfo {
        DebugInfo(())
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

    #[cfg(not(debug_assertions))]
    pub fn to_debug_string(&self) -> String {
        String::from("No debug info collected. Rebuild with debug assertions enabled.")
    }

    pub fn to_debug_comment(&self) -> String {
        format!("/*\n{}\n*/", self.to_debug_string())
    }

    #[cfg(debug_assertions)]
    pub fn add_debug_note_never_call_this_function_directly(&self, note: String) {
        let mut map = DEBUG_DATA.lock().unwrap();
        let data = map.get_mut(&self.0).unwrap();
        data.add_debug_note(note);
    }
}

// TODO: format as part of macro
#[cfg(debug_assertions)]
#[macro_export]
macro_rules! add_debug_note {
    ($debug_info:expr, $msg: expr) => {
        $debug_info.add_debug_note_never_call_this_function_directly($msg)
    };
}

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! add_debug_info {
    ($debug_info:expr, $msg: expr) => {
        ()
    };
}