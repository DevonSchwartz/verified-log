use vstd::prelude::*;
use std::marker::Copy; 

verus!{

pub struct Journal<T : Clone, const N: usize> {
    data: [T; N], // this is the main data storage
    tx_buffer: Vec<(usize, T)>, // this is the transaction buffer, storing the index and the new value
    log: Vec<Vec<(usize, T)>>
}


impl<T : Clone, const N: usize> View for Journal<T, N> {

    type V = Seq<T>;

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<T>
        decreases self,
    {
        self.data@
    }
}

impl<T : Clone + Copy, const N : usize> Journal<T, N> {
    pub fn new(default_value : T) -> (out: Self)
        ensures
            out@.len() == N,
        {
            Self {
                data: [default_value.clone(); N],
                log: Vec::new(),
                tx_buffer: Vec::new()
            }
        }

}
}