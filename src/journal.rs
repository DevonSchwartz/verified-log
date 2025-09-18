use std::collections::VecDeque;

use vstd::{prelude::*, tokens::seq::GhostSeqAuth};

verus!{

pub struct Filesystem<T: Copy, const N: usize> 
{
    filesystem: [T; N]
}

// The view of the filesystem reduces to the view of its internal container
impl<T: Copy, const N: usize> View for Filesystem<T, N>
{

    type V = Seq<T>;

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<T>
    {
        self.filesystem@
    }
}


impl <T: Copy, const N: usize> Filesystem<T, N> {
    pub fn new(default_value : T) -> (out: Self)
        ensures
            out@.len() == N,
            forall|i : int | 0 <= i < out@.len() ==> #[trigger] out@[i] == default_value
        {
            Self 
            {
                filesystem: [default_value; N]
            }
        }

    /**
     * Assign data to a specific index in the filesystsem array
     * Mutates self.filesystem
     */
    pub fn set_block(&mut self, index : usize, data: T) 
        requires
            index < N,
        ensures
            self@[index as int] == data
    {
        self.filesystem[index] = data; 
    }
}

pub struct Journal<T: Copy, const N : usize> 
{
    pub log : VecDeque<(usize, T)>, // keep a tuple of (index, data). Use VecDeque for O(1) removal in checkpointing
    pub last_commit: usize, // exclusive bound of last item commited in log 
    pub filesystem: Filesystem<T, N>,// keep a reference of filesystem to be 
}

impl<T: Copy, const N: usize> View for Journal<T, N>
{
    // We use (usize,T) so that we can produce a sequence of this tuple. V has to match the return type
    type V = Seq<(usize, T)>; 

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<(usize, T)>
    {
        self.log@
    }
}

impl<T:Copy, const N : usize> Journal<T, N> {
    /**
     * Make sure that the bits from the checkpointed sequence have been written to the filsystem
     */
    closed spec fn filesystem_matches_checkpoint(self, checkpointed: Seq<(usize, T)>) -> bool 
    {
        forall | i : int| 0 <= i < checkpointed.len() 
            ==> #[trigger] self.filesystem@[checkpointed[i].0 as int] == checkpointed[i].1 
    }
}

impl <T: Copy, const N : usize> Journal<T, N> 
{
    /**
     * Craete a log for filesystem
     * The log should be empty 
    */
    pub fn new(filesystem : Filesystem<T,N>) -> (out: Self)
        ensures
            out@ == Seq::<(usize, T)>::empty(),
            out.last_commit == out@.len()
        {
            Self
            {
                log: VecDeque::new(), 
                last_commit: 0,
                filesystem,
            }
        }

    /**
     * Write data to the end of the log
     * Index must be in the bounds of the filesystem
     */
    pub fn write(&mut self, index: usize, data : T)
        requires
            forall |i : int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i].0 < N,
            index < N
        ensures
            self@.len() == old(self)@.len() + 1,
            self@.last() == (index, data),
            forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
        {
            self.log.push_back((index, data));
        }

    /**
     * Increase the commit pointer to the length of the log where the last write was made
     * Checkpoint data and truncate each element once written to filesytem
     */
    pub fn commit (&mut self)
        requires
            // all elements in the log are in range of the filesystem before and after call
            forall |i : int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i].0 < N,
        ensures
            self.last_commit == self@.len(),
            self@.len() >= old(self)@.len(), // we are shrinking but never growing, so impossible to add out of range item
            forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
        {
            self.last_commit = self.log.len();
            // self.checkpoint();
        }

    /**
     * Write each block of data from the log to the filesystem
     * each time, teh commit pointer must be decreased by 1
     * The commit pointer may not be caught up with all the writes, but it should be equal to the
     * old commit pointer minus the number of elements removed
     */
    fn checkpoint(&mut self)
        requires
            forall |i : int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i].0 < N,
        ensures
            self@.len() <= old(self)@.len(),
            forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
            self.filesystem_matches_checkpoint(old(self)@.take(old(self)@.len() - self@.len())),
        {
            // loop until all the elements from [0, last_commit) are written to filesytem
            while self.last_commit > 0
                invariant
                    self.last_commit >= 0,
                    forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
                    self@.len() <= old(self)@.len(),
                decreases self.last_commit
                {
                    let old_length = self.log.len();
                    assert(old_length == self@.len()); 
                    match self.log.pop_front() 
                    {
                        Some((index, data)) => self.filesystem.set_block(index, data),
                        None => break // This should never execute because 
                    };
                    assert(self@.len() == (old_length - 1) as int); 
                    // update pointer to ensure consistency 
                    self.last_commit = self.last_commit - 1; 
                }

        }
}
}