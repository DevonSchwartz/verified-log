use vstd::prelude::*;

mod journal;

verus! {

use journal::*;

fn main() {
    let mut log : Journal<usize, 32> = Journal::new(0,  Filesystem::new(0)); 
    log.write(1);
    log.write(3);
    log.commit();
    // Issue with using get-block and saying anything about the filesystem. Report this in presentation 
} 
} // verus!
