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

pub struct Journal<T: Copy> 
{
    log : Vec<(usize, T)>, // keep a tuple of (index, data)
    is_transaction: bool // flag to determine whether in transaction or items committed 
}

impl<T: Copy> View for Journal <T>
{
    // We use (usize,T) so that we can produce a sequence of this tuple. V has to match the return type
    type V = Seq<(usize, T)>; 

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<(usize, T)>
    {
        self.log@
    }
}

impl <T: Copy> Journal<T> 
{
    pub fn new() -> (out: Self)
        ensures
            out@ == Seq::<(usize, T)>::empty()
        {
            Self
            {
                log: Vec::new(), 
                is_transaction : false
            }
        }
}
}