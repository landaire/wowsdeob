use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::RwLock;
use std::sync::RwLockReadGuard;

// Poisoning only records that another thread panicked while holding the lock. The
// marshal objects behind these locks are never left half-written, so reading them
// stays sound.
pub(crate) fn read_lock<T>(lock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
    lock.read().unwrap_or_else(PoisonError::into_inner)
}

pub(crate) fn lock_mutex<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}
