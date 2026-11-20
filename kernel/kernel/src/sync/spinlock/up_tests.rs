// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::SpinLock;
use crate::arch;
use blueos_test_macro::test;

#[test]
fn test_up_spinlock_shared_reads_and_reacquisition() {
    let lock = SpinLock::new(7);
    let first = lock.try_read().unwrap();
    let second = lock.try_read().unwrap();
    assert_eq!((*first, *second), (7, 7));
    drop(first);
    drop(second);

    let mut writer = lock.try_lock().unwrap();
    *writer = 9;
    drop(writer);
    assert_eq!(*lock.try_read().unwrap(), 9);
}

#[test]
fn test_up_spinlock_writer_excludes_other_access() {
    let lock = SpinLock::new(0);
    let writer = lock.try_lock().unwrap();
    // Only inspect acquisition results. Never dereference a conflicting guard,
    // so a broken backend is reported by assertions without exercising UB.
    let rejects_writer = lock.try_lock().is_none();
    let rejects_reader = lock.try_read().is_none();
    drop(writer);

    assert!(rejects_writer, "UP SpinLock admitted a second writer");
    assert!(
        rejects_reader,
        "UP SpinLock admitted a reader during a write"
    );
    assert!(lock.try_lock().is_some());
}

#[test]
fn test_up_spinlock_readers_exclude_writer_until_last_drop() {
    let lock = SpinLock::new(0);
    let first = lock.try_read().unwrap();
    let second = lock.try_read().unwrap();
    let rejects_with_two = lock.try_lock().is_none();
    drop(first);
    let rejects_with_one = lock.try_lock().is_none();
    drop(second);

    assert!(
        rejects_with_two,
        "UP SpinLock admitted a writer during reads"
    );
    assert!(
        rejects_with_one,
        "UP SpinLock released access before its last reader"
    );
    assert!(lock.try_lock().is_some());
}

#[test]
fn test_up_spinlock_irqsave_writer_excludes_other_access() {
    let lock = SpinLock::new(0);
    let initially_enabled = arch::local_irq_enabled();
    let writer = lock.try_irqsave_lock().unwrap();
    let masked = !arch::local_irq_enabled();
    let rejects_writer = lock.try_irqsave_lock().is_none();
    let rejects_reader = lock.try_irqsave_read().is_none();
    let still_masked = !arch::local_irq_enabled();
    // Restore IRQ state before reporting a failure.
    drop(writer);
    let restored = arch::local_irq_enabled() == initially_enabled;

    assert!(
        masked && still_masked && restored,
        "IRQ state was not preserved"
    );
    assert!(
        rejects_writer,
        "UP IRQ-save SpinLock admitted a second writer"
    );
    assert!(
        rejects_reader,
        "UP IRQ-save SpinLock admitted a reader during a write"
    );
    assert!(lock.try_irqsave_lock().is_some());
}

#[test]
fn test_up_spinlock_irqsave_reader_excludes_writer() {
    let lock = SpinLock::new(0);
    let initially_enabled = arch::local_irq_enabled();
    let reader = lock.try_irqsave_read().unwrap();
    let masked = !arch::local_irq_enabled();
    let rejects_writer = lock.try_irqsave_lock().is_none();
    let still_masked = !arch::local_irq_enabled();
    drop(reader);
    let restored = arch::local_irq_enabled() == initially_enabled;

    assert!(
        masked && still_masked && restored,
        "IRQ state was not preserved"
    );
    assert!(
        rejects_writer,
        "UP IRQ-save SpinLock admitted a writer during a read"
    );
    assert!(lock.try_irqsave_lock().is_some());
}
