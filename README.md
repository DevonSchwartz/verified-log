# verified-log
A verified log written in Rust / Verus with verified multithreaded code


Required Exec functions / Data Structures:

pub struct Journal

impl<T> Journal<T> {
    new() # state = "initialized" 

    begin() # state = "active" 

    write()

    commit()

    abort()

    verify() // replay the log

    truncate_log()

    view_data() // view the current data

    view_log() // view the current log
}


We will have a journal that is a Vec of entries

Journal: state = Tb [(index, a), (index, a), (index, a)] state = Tc 

The journal will then write the entries to the corresponding file system data structure, which is fixed length. The index must be in bounds of the filesystem

We will maintain state for whether we are in a transaction. That determine the validity of a new begin call 

If there is a crash and the transaction flag is false, then we can replay the log to restore the data structure to a consistent state.