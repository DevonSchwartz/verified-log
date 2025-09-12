use vstd::prelude::*;

verus!{

pub struct Journal<T : Clone + Copy, const N: usize> {
    data: [T; N], // this is the main data storage
    tx_buffer: Vec<(usize, T)>, // this is the transaction buffer, storing the index and the new value
    log: Vec<Vec<(usize, T)>>
}


impl<T : Clone + Copy, const N: usize> View for Journal<T, N> {

    type V = Seq<T>;

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<T>
        decreases self,
    {
        self.data@
    }
}

impl<T : Clone + Copy, const N : usize> Journal<T, N> {
    // We can't use T::default() because it is not supported by Verus, so we need to use a default value
    pub fn new(default_value:T) -> (out: Self)
        ensures
            out@.len() == N,
            forall|i : int | 0 <= i < out@.len() ==> #[trigger] out@[i] == default_value
        {
            Self {
                data: [default_value; N], // eventually, we want this to be a clone
                log: Vec::new(),
                tx_buffer: Vec::new()
            }
        }

}
}