use vstd::prelude::*;

verus! {
    fn test1(src: &Vec<u32>, dst: &mut Vec<u32>)
        requires
            src.len() == old(dst).len(),
        ensures
            src@ == dst@,
    {
        for n in 0..src.len()
            invariant
                src.len() == dst.len(),
                forall|i: int| 0 <= i < n ==> src[i] == dst[i],
        {
            dst[n] = src[n];
        }
    }

    broadcast proof fn lemma_seq_subrange_index2<A>(s: Seq<A>, j: int, k: int, i: int)
        requires
            0 <= j <= k <= s.len(),
            0 <= i - j < k - j,
        ensures
            // DANGER: might cause matching loop with axiom_seq_subrange_index
            (#[trigger] s.subrange(j, k))[i - j] == #[trigger] s[i],
    {
    }

    fn test2(src: &Vec<u32>, dst: &mut Vec<u32>)
        requires
            src.len() == old(dst).len(),
        ensures
            src@ == dst@,
    {
        broadcast use lemma_seq_subrange_index2;
        for n in 0..src.len()
            invariant
                src.len() == dst.len(),
                src@.subrange(0, n as int) =~= dst@.subrange(0, n as int),
        {
            broadcast use lemma_seq_subrange_index2;
            dst[n] = src[n];
        }
    }
}