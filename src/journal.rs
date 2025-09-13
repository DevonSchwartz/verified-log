use std::collections::VecDeque;

use vstd::prelude::*;

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
            index < old(self)@.len(),
        ensures
            self@[index as int] == data
    {
        self.filesystem[index] = data; 
    }
}

pub struct Journal<'a, T: Copy, const N : usize> 
{
    log : VecDeque<(usize, T)>, // keep a tuple of (index, data). Use VecDeque for O(1) removal in checkpointing
    last_commit: usize, // index of last item commited in log (inclusive)
    last_checkpoint: usize, // index of last item written to filesystem from log and not truncated (inclusive)
    filesystem: &'a Filesystem<T, N> // keep a reference of filesystem to be 
}

impl<'a, T: Copy, const N: usize> View for Journal<'a, T, N>
{
    // We use (usize,T) so that we can produce a sequence of this tuple. V has to match the return type
    type V = Seq<(usize, T)>; 

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<(usize, T)>
    {
        self.log@
    }
}

impl<'a, T:Copy, const N : usize> Journal<'a, T, N> {
    // the checkpoint pointer must be less than or equal to the commit
    // at all times in the journal
    pub closed spec fn checkpoint_leq_commit(self) -> bool {
        self.last_checkpoint <= self.last_commit
    }
}

impl <'a, T: Copy, const N : usize> Journal<'a, T, N> 
{
    pub fn new(filesystem : &'a Filesystem<T,N>) -> (out: Self)
        ensures
            out@ == Seq::<(usize, T)>::empty(),
            out.checkpoint_leq_commit()
        {
            Self
            {
                log: VecDeque::new(), 
                last_commit: 0,
                last_checkpoint: 0,
                filesystem: filesystem
            }
        }

    pub fn write(&mut self, index: usize, data : T)
        requires
            index < N
        ensures
            self@.len() == old(self)@.len() + 1,
            self@.last() == (index, data)
        {
            self.log.push_back((index, data));
        }

}
}