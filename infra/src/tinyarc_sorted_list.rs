// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use crate::tinyarc::{TinyArc, TinyArcList};
use crate::intrusive::Adapter;
use core::marker::PhantomData;
use core::cmp::Ordering;
use core::ptr;

/// TinyArcSortedList - Automatically sorted list data structure based on TinyArcList
///
/// # Overview
/// TinyArcSortedList extends TinyArcList functionality, providing automatic maintenance
/// of list ordering state. Through user-provided comparison function, each insert
/// operation places elements in the correct sorted position.
///
/// # Generic Parameters
/// - `T`: Stored data type (must implement Sized)
/// - `C`: Comparison function type (`Fn(&T, &T) -> Ordering`)
/// - `A`: Adapter type (implements Adapter<T> trait)
///
/// # Features
/// - Automatic sorted insertion
/// - Memory safety (based on Arc smart pointers)
/// - Efficient list operations
/// - Flexible comparison functions
/// - Thread-safe reading (write operations need external synchronization)
///
/// # Example
/// ```
/// use tinyarc_sorted_list::TinyArcSortedList;
/// 
/// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
/// list.init();
/// list.insert(TinyArc::new(3));
/// list.insert(TinyArc::new(1));
/// list.insert(TinyArc::new(2));
/// 
/// for item in list.iter() {
///     println!("{}", *item); // Output: 1, 2, 3
/// }
/// ```
#[derive(Debug)]
pub struct TinyArcSortedList<T, C, A>
where
    T: Sized,
    A: Adapter<T>,
{
    /// Base list implementation
    list: TinyArcList<T, A>,
    
    /// Comparison function closure
    compare: C,
    
    /// Adapter type marker
    adapter: PhantomData<A>,
}

impl<T, C, A> TinyArcSortedList<T, C, A>
where
    T: Sized,
    A: Adapter<T>,
    C: for<'a, 'b> Fn(&'a T, &'b T) -> core::cmp::Ordering,
{
    /// Create new empty sorted list
    /// 
    /// # Parameters
    /// * `compare` - Comparison function to determine element ordering
    /// 
    /// # Returns
    /// New TinyArcSortedList instance (uninitialized)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init(); // Requires manual initialization
    /// assert!(list.is_empty());
    /// ```
    pub fn new(compare: C) -> Self {
        Self {
            list: TinyArcList::new(),
            compare,
            adapter: PhantomData,
        }
    }

    /// Initialize the sorted list
    /// 
    /// # Returns
    /// - `true`: Initialization successful
    /// - `false`: Initialization failed
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// assert!(list.init());
    /// assert!(list.is_empty());
    /// ```
    pub fn init(&mut self) -> bool {
        self.list.init()
    }

    /// Check if list is empty
    /// 
    /// # Returns
    /// - `true`: List is empty
    /// - `false`: List contains elements
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// assert!(list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Return number of elements in list
    /// 
    /// # Returns
    /// Number of elements in the list
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// assert_eq!(list.len(), 0);
    /// 
    /// list.insert(TinyArc::new(1));
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        // Manually calculate list length by traversing entire list
        self.list.iter().count()
    }

    /// Insert Arc pointer into correct sorted position
    /// 
    /// # Parameters
    /// * `item` - TinyArc<T> pointer to insert
    /// 
    /// # Returns
    /// - `true`: Insertion successful
    /// - `false`: Insertion failed
    /// 
    /// # Complexity
    /// O(n) - Requires traversal to find insertion position
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// assert!(list.insert(TinyArc::new(3)));
    /// assert!(list.insert(TinyArc::new(1)));
    /// assert!(list.insert(TinyArc::new(2)));
    /// 
    /// assert_eq!(list.len(), 3);
    /// ```
    pub fn insert(&mut self, item: TinyArc<T>) -> bool {
        // Use built-in push_by method for sorted insertion
        // Capture comparison function by reference
        let compare_ref = &self.compare;
        self.list.push_by(|a, b| compare_ref(a, b), item)
    }

    /// Add Arc pointer to list end (without sorting)
    /// 
    /// # Parameters
    /// * `item` - TinyArc<T> pointer to add
    /// 
    /// # Returns
    /// - `true`: Addition successful
    /// - `false`: Addition failed
    /// 
    /// # Complexity
    /// O(1)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// assert!(list.push_back(TinyArc::new(1)));
    /// assert!(list.push_back(TinyArc::new(2)));
    /// ```
    pub fn push_back(&mut self, item: TinyArc<T>) -> bool {
        self.list.push_back(item)
    }

    /// Remove and return Arc pointer from list front
    /// 
    /// # Returns
    /// - `Some(item)`: Successfully removed element
    /// - `None`: List is empty
    /// 
    /// # Complexity
    /// O(1)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(42));
    /// 
    /// if let Some(item) = list.pop_front() {
    ///     assert_eq!(*item, 42);
    /// }
    /// ```
    pub fn pop_front(&mut self) -> Option<TinyArc<T>> {
        self.list.pop_front()
    }

    /// Get Arc pointer from list front (without removal)
    /// 
    /// # Returns
    /// - `Some(item)`: Front element
    /// - `None`: List is empty
    /// 
    /// # Complexity
    /// O(1)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(42));
    /// 
    /// if let Some(front) = list.front() {
    ///     assert_eq!(*front, 42);
    /// }
    /// ```
    pub fn front(&self) -> Option<TinyArc<T>> {
        self.list.front()
    }

    /// Get Arc pointer from list back (without removal)
    /// 
    /// # Returns
    /// - `Some(item)`: Back element
    /// - `None`: List is empty
    /// 
    /// # Complexity
    /// O(1)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(42));
    /// 
    /// if let Some(back) = list.back() {
    ///     assert_eq!(*back, 42);
    /// }
    /// ```
    pub fn back(&self) -> Option<TinyArc<T>> {
        self.list.back()
    }

    /// Get Arc pointer by index (0 is front)
    /// 
    /// # Parameters
    /// * `index` - Element index (0 <= index < len())
    /// 
    /// # Returns
    /// - `Some(item)`: Element at specified position
    /// - `None`: Index out of bounds
    /// 
    /// # Complexity
    /// O(n) - Requires list traversal
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(1));
    /// list.insert(TinyArc::new(2));
    /// list.insert(TinyArc::new(3));
    /// 
    /// if let Some(item) = list.get(1) {
    ///     assert_eq!(*item, 2);
    /// }
    /// ```
    pub fn get(&self, index: usize) -> Option<TinyArc<T>> {
        // Use enumerate() to avoid manual counter
        for (current_index, item) in self.list.iter().enumerate() {
            if current_index == index {
                return Some(item);
            }
        }
        None
    }

    /// Create immutable iterator, traverse elements in sorted order
    /// 
    /// # Returns
    /// `TinyArcSortedListIterator<T, A>`
    /// 
    /// # Traversal Order
    /// From small to large (according to comparison function)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(3));
    /// list.insert(TinyArc::new(1));
    /// list.insert(TinyArc::new(2));
    /// 
    /// let mut values = Vec::new();
    /// for item in list.iter() {
    ///     values.push(*item);
    /// }
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn iter(&self) -> TinyArcSortedListIterator<T, A> {
        TinyArcSortedListIterator {
            inner: self.list.iter(),
        }
    }

    /// Clear all elements from list
    /// 
    /// # Returns
    /// Number of removed elements
    /// 
    /// # Complexity
    /// O(n)
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(1));
    /// list.insert(TinyArc::new(2));
    /// 
    /// let removed_count = list.clear();
    /// assert_eq!(removed_count, 2);
    /// assert!(list.is_empty());
    /// ```
    pub fn clear(&mut self) -> usize {
        self.list.clear()
    }

    /// Find first element satisfying condition
    /// 
    /// # Parameters
    /// * `predicate` - Search condition function
    /// 
    /// # Returns
    /// - `Some(item)`: Found element
    /// - `None`: No matching element found
    /// 
    /// # Complexity
    /// O(n)
    /// 
    /// # Thread Safety
    /// Read operation safe
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(1));
    /// list.insert(TinyArc::new(42));
    /// list.insert(TinyArc::new(3));
    /// 
    /// if let Some(item) = list.find(|x| **x == 42) {
    ///     assert_eq!(*item, 42);
    /// }
    /// ```
    pub fn find<F>(&self, predicate: F) -> Option<TinyArc<T>>
    where
        F: Fn(&TinyArc<T>) -> bool,
    {
        self.iter().find(predicate)
    }

    /// Check if list contains specified Arc pointer
    /// 
    /// # Parameters
    /// * `item` - Arc pointer to search for
    /// 
    /// # Returns
    /// - `true`: List contains the element
    /// - `false`: List does not contain the element
    /// 
    /// # Complexity
    /// O(n)
    /// 
    /// # Thread Safety
    /// Read operation safe
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// let item = TinyArc::new(42);
    /// 
    /// list.insert(item.clone());
    /// assert!(list.contains(&item));
    /// ```
    pub fn contains(&self, item: &TinyArc<T>) -> bool {
        // Use value comparison instead of pointer comparison to avoid memory address issues
        for existing_item in self.iter() {
            if ptr::eq(TinyArc::<T>::as_ptr(&existing_item), TinyArc::<T>::as_ptr(item)) {
                return true;
            }
        }
        false
    }

    /// Remove first element satisfying condition
    /// 
    /// # Parameters
    /// * `predicate` - Condition judgment function
    /// 
    /// # Returns
    /// - `Some(item)`: Removed element
    /// - `None`: No matching element found
    /// 
    /// # Complexity
    /// O(n)
    /// 
    /// # Thread Safety
    /// Requires external synchronization
    /// 
    /// # Example
    /// ```
    /// use tinyarc_sortlist::TinyArcSortedList;
    /// 
    /// let mut list = TinyArcSortedList::new(|a: &i32, b: &i32| a.cmp(b));
    /// list.init();
    /// list.insert(TinyArc::new(1));
    /// list.insert(TinyArc::new(42));
    /// list.insert(TinyArc::new(3));
    /// 
    /// if let Some(removed) = list.remove_if(|x| **x == 42) {
    ///     assert_eq!(*removed, 42);
    /// }
    /// ```
    pub fn remove_if<F>(&mut self, predicate: F) -> Option<TinyArc<T>>
    where
        F: Fn(&TinyArc<T>) -> bool,
    {
        self.list.remove_if(predicate)
    }
}

/// TinyArcSortedList immutable iterator
pub struct TinyArcSortedListIterator<T, A>
where
    T: Sized,
    A: Adapter<T>,
{
    inner: crate::tinyarc::TinyArcListIterator<T, A>,
}

impl<T, A> Iterator for TinyArcSortedListIterator<T, A>
where
    T: Sized,
    A: Adapter<T>,
{
    type Item = TinyArc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{impl_simple_intrusive_adapter, tinyarc::TinyArc, tinyarc::TinyArcList};

    // Create adapter for testing, using same pattern as tinyarc.rs
    impl_simple_intrusive_adapter!(OffsetOfTask, Task, task_node);

    type TaskSortedList = TinyArcSortedList<Task, fn(&Task, &Task) -> core::cmp::Ordering, OffsetOfTask>;
    type TaskArcList = TinyArcList<Task, OffsetOfTask>;

    #[derive(Default, Debug)]
    pub struct Task {
        pub task_node: <TaskArcList as crate::list::GenericList>::Node,
        pub id: usize,
        pub priority: usize,
    }

    impl Task {
        pub fn new(id: usize, priority: usize) -> Self {
            Self {
                id,
                priority,
                ..Default::default()
            }
        }
    }

    #[test]
    fn test_basic_creation() {
        // Test basic creation and initialization
        let mut list = TaskSortedList::new(|a: &Task, b: &Task| a.priority.cmp(&b.priority));
        assert!(list.init());
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test_empty_list_operations() {
        // Test basic operations on empty list
        let mut list = TaskSortedList::new(|a: &Task, b: &Task| a.priority.cmp(&b.priority));
        assert!(list.init());
        
        // Empty list operations should return None or empty
        assert!(list.front().is_none());
        assert!(list.back().is_none());
        assert!(list.get(0).is_none());
        assert!(list.pop_front().is_none());
        assert_eq!(list.clear(), 0);
    }

    #[test]
    fn test_basic_functionality() {
        // Test basic functionality
        let mut list = TaskSortedList::new(|a: &Task, b: &Task| a.priority.cmp(&b.priority));
        assert!(list.init());
        
        // Create some tasks
        let task1 = TinyArc::new(Task::new(1, 5));
        let task2 = TinyArc::new(Task::new(2, 3));
        let task3 = TinyArc::new(Task::new(3, 8));
        
        // Insert tasks (sorted by priority)
        assert!(list.insert(task1.clone()));
        assert!(list.insert(task2.clone()));
        assert!(list.insert(task3.clone()));
        
        // Verify list state
        assert!(!list.is_empty());
        assert_eq!(list.len(), 3);
        
        // Verify sorting (priority: 3 < 5 < 8)
        let mut priorities: Vec<usize> = Vec::new();
        for task in list.iter() {
            priorities.push(task.priority);
        }
        assert_eq!(priorities, vec![3, 5, 8]);
        
        // Verify front and back
        assert_eq!(list.front().map(|t| t.priority), Some(3));
        assert_eq!(list.back().map(|t| t.priority), Some(8));
    }

    #[test]
    fn test_task_operations() {
        // Test operations on task_node (reference Thread test in tinyarc.rs)
        let mut list = TaskSortedList::new(|a: &Task, b: &Task| a.id.cmp(&b.id));
        assert!(list.init());
        
        // Create tasks
        let task1 = TinyArc::new(Task::new(1, 10));
        let task2 = TinyArc::new(Task::new(2, 5));
        let task3 = TinyArc::new(Task::new(3, 15));
        
        // Insert sorted by ID
        assert!(list.insert(task1));
        assert!(list.insert(task2));
        assert!(list.insert(task3));
        
        // Verify sorting by ID (1 < 2 < 3)
        let mut ids: Vec<usize> = Vec::new();
        for task in list.iter() {
            ids.push(task.id);
        }
        assert_eq!(ids, vec![1, 2, 3]);
        
        // Test pop_front
        if let Some(task) = list.pop_front() {
            assert_eq!(task.id, 1);
        }
        assert_eq!(list.len(), 2);
        
        // Test clear
        assert_eq!(list.clear(), 2);
        assert!(list.is_empty());
    }

    #[test]
    fn test_find_and_contains() {
        // Test find functionality
        let mut list = TaskSortedList::new(|a: &Task, b: &Task| a.priority.cmp(&b.priority));
        assert!(list.init());
        
        let task1 = TinyArc::new(Task::new(1, 5));
        let task2 = TinyArc::new(Task::new(2, 10));
        let task3 = TinyArc::new(Task::new(3, 15));
        
        list.insert(task1.clone());
        list.insert(task2.clone());
        list.insert(task3.clone());
        
        // Test contains
        assert!(list.contains(&task1));
        assert!(list.contains(&task2));
        assert!(list.contains(&task3));
        
        // Test find
        if let Some(task) = list.find(|t| t.id == 2) {
            assert_eq!(task.priority, 10);
        } else {
            panic!("Should find task with id 2");
        }
        
        // Test non-existent task
        assert!(list.find(|t| t.id == 99).is_none());
    }
}