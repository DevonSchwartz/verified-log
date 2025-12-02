use vstd::prelude::*;

verus!
{

pub struct Filesystem<T, const N: usize> 
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
            0 <= index < N,
        ensures
            self@ == old(self)@.update(index as int, data) // Use .update() to say rest of sequence same except index
    {
        self.filesystem[index] = data; 
    }

    pub fn get_block(&self, index: usize) -> (out: &T)
        requires
            0 <= (index as int) < N,
        ensures
            self@[index as int] == out
        {
            return &self.filesystem[index]
        }
}

pub struct Journal<T, const N : usize> 
{
    pub log: [T;N], 
    pub last_commit: usize, // exclusive bound of last item comitted  
    pub last_checkpoint: usize, // 0 <= i < checkpoint items were written to filesystem
    pub write_ptr: usize, // where to make next write,
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
            old(self).last_checkpoint == self.last_checkpoint,
            old(self).last_commit == self.last_commit,
            self.write_ptr == old(self).write_ptr + 1,
            0 <= self.last_checkpoint <= self.last_commit <= self.write_ptr <= N,
            self@ == old(self)@.update(old(self).write_ptr as int, data)
        {
            self.log[self.write_ptr] = data;
            self.write_ptr = self.write_ptr + 1;
        }

    /**
     * Set the commit ptr to be equal to where the write pointer is
     * Checkpoint data up to commit
     */

    pub fn commit(&mut self, filesystem : &mut Filesystem<T, N>)
        requires
            0 <= old(self).last_checkpoint <= old(self).last_commit <= old(self).write_ptr <= N,
        ensures
            old(self).write_ptr == self.write_ptr,
            0 <= self.last_checkpoint <= self.last_commit == self.write_ptr <= N,
            self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int)  
                == filesystem@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int)
        {
            self.last_commit = self.write_ptr;
            self.checkpoint(filesystem);
        }

    
    fn checkpoint(&mut self, filesystem : &mut Filesystem<T, N>)
        requires
            0 <= old(self).last_checkpoint <= old(self).last_commit <= old(filesystem)@.len()
        ensures
            old(self).write_ptr == self.write_ptr, // this is still important to guarentee 
            old(self).last_commit == self.last_commit,
            0 <= old(self).last_checkpoint <= self.last_checkpoint == self.last_commit <= filesystem@.len(),
            self@ == old(self)@,
            self@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int)  
                == filesystem@.subrange(old(self).last_checkpoint as int, self.last_checkpoint as int)
    {
        while self.last_checkpoint < self.last_commit
            invariant
                self@ == old(self)@,
                old(self).write_ptr == self.write_ptr, 

                old(self).last_commit == self.last_commit,

                0 <= old(self).last_checkpoint <= self.last_checkpoint <= self.last_commit <= filesystem@.len(),

                forall |i : int| old(self).last_checkpoint as int <= i < self.last_checkpoint ==> #[trigger]
                    self@[i] == filesystem@[i] // WHY DOES FORALL BEHAVE DIFFERENTLY THAN SUBRANGE? 

        decreases self.last_commit - self.last_checkpoint
        { 
            filesystem.set_block(self.last_checkpoint, self.log[self.last_checkpoint]);
            self.last_checkpoint = self.last_checkpoint + 1; 
        }
    }
}
}