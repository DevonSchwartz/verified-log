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
            self@[index as int] == data,
    {
        self.filesystem[index] = data; 
    }
}

pub struct Journal<T: Copy, const N : usize> 
{
    pub log : Vec<(usize, T)>, // keep a tuple of (index, data). Use VecDeque for O(1) removal in checkpointing
    pub last_commit: usize, // exclusive bound of last item commited in log 
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

// impl<T:Copy, const N : usize> Journal<T, N> 
// {
//     /**
//      * Make sure that the bits from the checkpointed sequence have been written to the filsystem
//      */
//     closed spec fn filesystem_matches_checkpoint(self, checkpointed: Seq<(usize, T)>) -> bool 
//     {
//         forall | i : int| 0 <= i < checkpointed.len() 
//             ==> #[trigger] self.filesystem@[checkpointed[i].0 as int] == checkpointed[i].1 
//     }
// }

impl <T: Copy, const N : usize> Journal<T, N> 
{
    /**
     * Craete a log for filesystem
     * The log should be empty 
    */
    pub fn new() -> (out: Self)
        ensures
            out@ == Seq::<(usize, T)>::empty(),
            out.last_commit == out@.len()
        {
            Self
            {
                log: Vec::new(), 
                last_commit: 0,
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
            self.log.push((index, data));
        }

    /**
     * Increase the commit pointer to the length of the log where the last write was made
     * Checkpoint data and truncate each element once written to filesytem
     */
    pub fn commit (&mut self)
        requires
            // all elements in the log are in range of the filesystem before and after call
            forall |i : int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i].0 < N,
            old(self).last_commit <= old(self)@.len(),
        ensures
            self.last_commit == self@.len(),
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
    // fn checkpoint(&mut self)
    //     requires
    //         0 <= old(self).last_commit <= old(self)@.len(),
    //         forall |i : int| 0 <= i < old(self)@.len() ==> #[trigger] old(self)@[i].0 < N,
    //     ensures
    //         0 == self.last_commit <= self@.len(),
    //         old(self)@.len() - old(self).last_commit == old(self)@.skip(old(self).last_commit as int).len(),
    //         self@.len() == old(self)@.len() - old(self).last_commit
    //     {
    //         assert(self.log@.len() == old(self).log@.len()); 
    //         // loop until all the elements from [0, last_commit) are written to filesytem
    //         while self.last_commit > 0
    //             invariant
    //                 forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
    //                 0 <= self.last_commit <= self@.len(),
    //             decreases self.last_commit
    //             {
    //                 let (index, data) = self.log.pop_front().unwrap(); // safe unwrap because last_commit > 0
    //                 self.filesystem.set_block(index, data);
    //                 self.last_commit = self.last_commit - 1;
    //             }
    //     }

    proof fn lemma_decreases_commit_decreases_length(log: Seq<(usize, T)>, commit : nat) 
        requires
            commit <= log.len()
        ensures
            commit <= log.len()
        decreases commit
    {
        if (commit == 0) {
            // do nothing 
        } else {
            let new_log = log.skip(1);
            let new_commit = commit - 1;
            // Add an explicit assertion that new_commit <= new_log.len()
            assert(new_commit <= new_log.len());
            Self::lemma_decreases_commit_decreases_length(new_log, new_commit as nat)
        }
    }

    // fn checkpoint(&mut self)
    //     requires

    //     ensures
    //         old(self).last_commit == self.last_commit, 
    //         old(self)@ == self@, 
    //         forall | i : int| 0 <= i < self.last_commit ==> #[trigger] self.filesystem@[self@[i].0 as int]
    //         == self@[i].1 
    // {
    //     let mut idx = 0; 
    //     while idx < self.last_commit
    //         invariant
    //             forall |i : int| 0 <= i < self@.len() ==> #[trigger] self@[i].0 < N,
    //             self.last_commit == old(self).last_commit,
    //             self@ == old(self)@
    //         decreases self.last_commit - idx
    //         {
    //             let (index, data) = self.log[idx]; 
    //             self.filesystem.set_block(index, data);
    //             assert(self.filesystem@[self@[idx as int].0 as int] == self@[idx as int].1); 
    //             idx += 1;
    //         }
    // }

    // fn checkpoint(&self, idx: usize, filesystem : &mut Filesystem<T,N>)
    //     requires
    //         idx <= self.last_commit <= self@.len(), 
    //         forall |i : int| 0 <= i < self.last_commit ==> #[trigger] self@[i].0 < N,
    //     ensures
    //         idx < self.last_commit ==> 
    //             filesystem@[self@[idx as int].0 as int] == self@[idx as int].1
    //     decreases self.last_commit - idx
    //     {
    //         if idx < self.last_commit
    //         {
    //             filesystem.set_block(self.log[idx].0, self.log[idx].1);
    //             self.checkpoint(idx + 1, filesystem);
    //         }
    //     }

    fn checkpoint(&self, filesystem : &mut Filesystem<T,N>)
        requires
            self.last_commit <= self@.len(),
            forall |i : int| 0 <= i < self.last_commit ==> #[trigger] self@[i].0 < N 
        ensures
            forall | i : int| 0 <= i < self.last_commit ==> 
                #[trigger] filesystem@[self@[i].0 as int] == self@[i].1 
    {
        let mut idx = 0;
        while idx < self.last_commit
            invariant
                idx <= self.last_commit <= self@.len(),
                forall |i : int| 0 <= i < self.last_commit ==> #[trigger] self@[i].0 < N,
                forall | i : int| 0 <= i < idx ==> 
                    #[trigger] filesystem@[self@[i].0 as int] == self@[i].1 
            decreases self.last_commit - idx
            {
                assert(forall | i : int| 0 <= i < idx ==> 
                    #[trigger] filesystem@[self@[i as int].0 as int] == self@[i].1);                
                filesystem.set_block(self.log[idx].0, self.log[idx].1);
                // assert(forall | i : int| 0 <= i < idx ==> 
                //     #[trigger] filesystem@[self@[i as int].0 as int] == self@[i].1);  
                idx += 1; 
            }
        assert(forall | i : int| 0 <= i < idx ==> 
            #[trigger] filesystem@[self@[i].0 as int] == self@[i].1)
    }
}
}