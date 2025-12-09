use vstd::prelude::*;

mod journal;

verus! {

use journal::*;
fn main() {
    let mut log : Journal<usize, 32> = Journal::new(0,  Filesystem::new(0)); 
    assert((log.write_ptr as int) == 0);
    log.write(1);
    log.commit(); 
    assert(log@[0] == 1); // only works when we guarentee after checkpoint view is the same 
} 

} // verus!
