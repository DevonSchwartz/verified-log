use vstd::prelude::*;

verus!
{

pub struct Filesystem<T: Copy, const N: usize> 
{
    filesystem: [T; N]
}

// The view of the filesystem reduces to the view of its internal container
impl<T: Copy, const N: usize> View for Filesystem<T, N>
{

    type V = Seq<T>;

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<T>
    {
        self.filesystem@
    }
}


impl <T: Copy, const N: usize> Filesystem<T, N> 
{
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
            index < N,
        ensures
            self@[index as int] == data,
    {
        self.filesystem[index] = data; 
    }
}

pub struct Journal<T: Copy, const N : usize> 
{
    pub log: [T;N], 
    pub last_commit: usize, // exclusive bound of last item comitted  
    pub last_checkpoint: usize, // 0 <= i < checkpoint items were written to filesystem
    pub write_ptr: usize // where to make next write
}

impl<T: Copy, const N: usize> View for Journal<T, N>
{
    // We use (usize,T) so that we can produce a sequence of this tuple. V has to match the return type
    type V = Seq<T>; 

    // the view of the journal should be a sequence of its data
    closed spec fn view(&self) -> Seq<T>
    {
        self.log@
    }
}

// impl<T:Copy, const N : usize> Journal<T, N> 
// {
//     /**
//      * Make sure that the bits from the checkpointed sequence have been written to the filsystem
//      */
//     closed spec fn filesystem_matches_checkpoint(self, checkpointed: Seq<(usize, T)>) -> bool 
//     {
//         forall | i : int| 0 <= i < checkpointed.len() 
//             ==> #[trigger] self.filesystem@[checkpointed[i].0 as int] == checkpointed[i].1 
//     }
// }

impl <T: Copy, const N : usize> Journal<T, N> 
{
    /**
     * Craete a log for filesystem
     * The log should be empty 
    */
    pub fn new(default_value: T) -> (out: Self)
        ensures
            forall|i : int | 0 <= i < out@.len() ==> #[trigger] out@[i] == default_value,
            out.last_commit == 0,
            out.write_ptr == 0,
            out.last_checkpoint == 0
        {
            Self
            {
                log: [default_value; N], 
                last_commit: 0,
                last_checkpoint: 0,
                write_ptr: 0,
            }
        }

    /**
     * Write data to the end of the log
     * Index must be in the bounds of the filesystem
     */
    pub fn write(&mut self, data : T)
        requires
            0 <= old(self).last_checkpoint <= old(self).last_commit <= old(self).write_ptr < N,
        ensures
            0 <= self.last_checkpoint <= self.last_commit <= self.write_ptr <= N,
            self@[old(self).write_ptr as int] == data
        {
            self.log[self.write_ptr] = data;
            self.write_ptr = self.write_ptr + 1;
        }

    /**
     * Set the commit ptr to be equal to where the write pointer is
     * Checkpoint data up to commit
     */

    pub fn commit(&mut self, _filesystem: &mut Filesystem<T, N>)
        requires
            0 <= old(self).last_checkpoint <= old(self).last_commit <= old(self).write_ptr <= N,
        ensures
            0 <= self.last_checkpoint <= self.last_commit == self.write_ptr <= N,
        {
            self.last_commit = self.write_ptr;
            // self.checkpoint(_filesystem);
        }

    // fn checkpoint(&mut self, _filesystem: &mut Filesystem<T, N>)
    //     requires
    //         0 <= old(self).last_checkpoint <= old(self).last_commit <= old(_filesystem)@.len(),
    //     ensures
    //         0 <= old(self).last_checkpoint <= self.last_checkpoint 
    //             == self.last_commit <= _filesystem@.len(),

    //         self@.subrange(old(self).last_checkpoint as int, self.last_commit as int) 
    //             == _filesystem@.subrange(old(self).last_checkpoint as int, self.last_commit as int)
    //     {
    //         while self.last_checkpoint < self.last_commit
    //             invariant
    //                 0 <= old(self).last_checkpoint <= self.last_checkpoint <= self.last_commit <= _filesystem@.len(),
    //             decreases self.last_commit - self.last_checkpoint
    //             {
    //                 _filesystem.set_block(self.last_checkpoint, self.log[self.last_checkpoint]);
    //                 self.last_checkpoint = self.last_checkpoint + 1; 

    //                 assert(self@.subrange(self.last_checkpoint - 1 as int, self.last_checkpoint as int) 
    //                     == _filesystem@.subrange(self.last_checkpoint - 1 as int, self.last_checkpoint as int)); 
    //             }
    //     }

        fn checkpoint(&mut self, _filesystem: &mut Filesystem<T, N>)
            requires
                0 <= old(self).last_checkpoint <= old(self).last_commit <= old(_filesystem)@.len()
            ensures
                0 <= old(self).last_checkpoint <= self.last_checkpoint 
                    == self.last_commit <= _filesystem@.len(),
                self@ == old(self)@,
                self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int) 
                    == _filesystem@.subrange(old(self).last_checkpoint as int, self.last_checkpoint  as int),

                // old(_filesystem)@.take(old(self).last_checkpoint as int) == _filesystem@.take(old(self).last_checkpoint as int),                
                // _filesystem@ == old(_filesystem)@.take(old(self).last_checkpoint as int) + self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int),  
            decreases old(self).last_commit - old(self).last_checkpoint 
        {
            if self.last_checkpoint < self.last_commit
            {
                _filesystem.set_block(self.last_checkpoint, self.log[self.last_checkpoint]);
                self.last_checkpoint = self.last_checkpoint + 1;

                assert(self.last_checkpoint <= self.last_commit); 
                
                assert(self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int) 
                    == _filesystem@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int));
                assert(self@[old(self).last_checkpoint as int] == _filesystem@[old(self).last_checkpoint as int]); 
                assert(self.last_checkpoint == old(self).last_checkpoint + 1);
                // proof
                // {
                //     Self::lemma_elements_equal(self@, _filesystem@, old(self).last_checkpoint as int, self.last_checkpoint as int); 
                // }; 

                // assert(self.last_checkpoint < self.last_commit ==> _filesystem@[self.last_checkpoint as int]  == old(_filesystem)@[self.last_checkpoint as int]); 


                self.checkpoint(_filesystem);

                // TODO: Assert that the construction from spec is the same as the filesystem construction


                assert(self.last_checkpoint == old(self).last_checkpoint + (self.last_commit - old(self).last_checkpoint));
                assert(self@[old(self).last_checkpoint as int] == old(self)@[old(self).last_checkpoint as int]); 
                assert(self@[old(self).last_checkpoint as int] == _filesystem@[old(self).last_checkpoint as int]); 
                // assert(self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int) 
                //     == _filesystem@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int));
            }
        }


        // proof fn lemma_elements_equal(log : Seq<T>, filesystem: Seq<T>, old_last_checkpoint: int, last_checkpoint: int)
        //     requires
        //         log.len() == filesystem.len(),
        //         0 <= old_last_checkpoint < last_checkpoint <= log.len(),
        //     ensures 
        //         log.subrange(old_last_checkpoint, last_checkpoint) == filesystem.subrange(old_last_checkpoint, last_checkpoint)
        //     {

        //     }


        // TODO: Make a spec function that creates a new filesystem sequence based off of the log
        // It will s
        // spec fn create_filesystem(log: Seq<T>, filesystem: Seq<T>, index: nat, old_last_checkpoint: nat, last_checkpoint: nat) -> Seq<T>
        //     decreases old_last_checkpoint - index
        // {

        //     if index <= old_last_checkpoint <= last_checkpoint <= filesystem.len() && filesystem.len() == log.len()
        //     {
        //         if index < old_last_checkpoint
        //         {
        //             return seq![filesystem[index as int]] + Self::create_filesystem(log, filesystem, index + 1, old_last_checkpoint, last_checkpoint);
        //         }
        //         else if index < last_checkpoint
        //         {
        //             return seq![log[index as int]] + Self::create_filesystem(log, filesystem, index + 1, old_last_checkpoint, last_checkpoint);
        //         }
        //     }
        //     return seq![];
        // }
}
}