use vstd::prelude::*;

mod journal;

verus! {

use journal::*;

fn main() {

    let mut fs : Filesystem<usize, 32>  = Filesystem::new(0); 
    let mut log : Journal<usize, 32> = Journal::new(0); 
    log.write(1);
    log.write(2);
    log.commit(&mut fs);
    if 2 == 3
    {
        assert(false)
    }
} 
} // verus!
