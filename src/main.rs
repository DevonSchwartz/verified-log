use vstd::prelude::*;

mod journal;

verus! {

use journal::*;

fn main() {
    let fs : Filesystem<usize, 32> = Filesystem::new(0); 
    let journal : Journal<usize, 32> = Journal::new(fs); 
}

} // verus!
