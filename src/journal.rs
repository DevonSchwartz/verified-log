use vstd::prelude::*;

verus!{

pub struct Journal<T : Clone> {
    data: Vec<T>, // this is the main data storage
    tx_buffer: Vec<(usize, T)>, // this is the transaction buffer, storing the index and the new value
    log: Vec<Vec<(usize, T)>>
}

impl 

impl<T : Clone> Journal<T> {
    pub fn new(num_blocks: usize, default_value : T) -> (out: Self)
        ensures
            out.data@.len() == num_blocks,
            forall|i : int | 0 <= i < out.data@.len() ==> #[trigger] out.data@[i] == default_value
            
        {
            Self {
                data: vec![default_value; num_blocks],
                log: Vec::new(),
                tx_buffer: Vec::new()
            }
        }

}
}