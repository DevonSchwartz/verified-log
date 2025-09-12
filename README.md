# verified-log
A verified log written in Rust / Verus with verified multithreaded code


Required Exec functions / Data Structures:

pub struct Journal

impl<T> Journal<T> {
    new()

    begin()

    write()

    commit()

    abort()

    verify() // replay the log

    truncate_log()

    view_data() // view the current data

    view_log() // view the current log
}
