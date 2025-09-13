use vstd::prelude::*;

verus!{

pub struct Filesystem<T: Copy, const N: usize> 
{
    filesystem: [T; N]
}

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






// pub struct Journal<T: Copy, const N: usize> {
//     // TODO: Remove data and tx_buffer. Only keep log
//     // TODO: Add a variable for the tail index, which says where the next piece of transaction should be written 
//     // TODO: Use a static array for journal first, initialized to size client wants
//     // TODO: Log is a one-to-one mapping of the data
//     data: [T; N], // this is the main data storage
//     tx_buffer: Vec<(usize, T)>, // this is the transaction buffer, storing the index and the new value
//     log: Vec<Vec<(usize, T)>>, // After a
//     // TODO: Add an enum for state 
// }


// impl<T: Copy, const N: usize> View for Journal<T, N> {

//     type V = Seq<T>;

//     // the view of the journal should be a sequence of its data
//     closed spec fn view(&self) -> Seq<T>
//     {
//         self.data@
//     }
// }

// impl<T: Copy, const N : usize> Journal<T, N> {
//     // We can't use T::default() because it is not supported by Verus, so we need to use a default value
//     pub fn new(&self, default_value:T) -> (out: Self)
//         ensures
//             out@.len() == N,
//             forall|i : int | 0 <= i < out@.len() ==> #[trigger] out@[i] == default_value,            
//         {
//             Self {
//                 data: [default_value; N], // eventually, we want this to be a clone
//                 log: Vec::new(),
//                 tx_buffer: Vec::new()
//             }
//         }

// }
}