use vstd::prelude::*;
use crate::config::*;
use crate::tokens::*;
use crate::layout::*;
use crate::types::*;
use vstd::set_lib::set_int_range;

verus!{

proof fn lemma_map_distribute<S,T>(s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T)
    ensures s1.union(s2).map(f) == s1.map(f).union(s2.map(f))
{
}

proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
{
}

// used for triggering
spec fn mod64(x: usize) -> usize { x % 64 }
spec fn div64(x: usize) -> usize { x / 64 }

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}

proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
    })
{
}

proof fn lemma_obtain_bit_index_3_aux(a: u64, b: u64, hi: u64) -> (i: u64)
    requires
        a & b != b,
        hi <= 64,
        a >> hi == 0,
        b >> hi == 0,
    ensures
        i < hi,
        !is_bit_set!(a, i),
        is_bit_set!(b, i),
    decreases hi
{
    proof_from_false() // TODO: replace with appropriate return value
}

proof fn lemma_obtain_bit_index_3(a: usize, b: usize) -> (i: usize)
    requires a & b != b
    ensures
        i < 64,
        !is_bit_set(a, i),
        is_bit_set(b, i),
{
    proof_from_false() // TODO: replace with appropriate return value
}

proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    proof_from_false() // TODO: replace with appropriate return value
}

proof fn lemma_obtain_bit_index_1_aux(a: u64, hi: u64) -> (i: u64)
    requires
        a != 0,
        hi <= 64,
        a >> hi == 0,
    ensures
        i < hi,
        is_bit_set!(a, i),
    decreases hi
{
    proof_from_false() // TODO: replace with appropriate return value
}

proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
{
    proof_from_false() // TODO: replace with appropriate return value
}

// I don't think there's a good reason that some of these would need `j < 64` and others don't but
// for some the bitvector assertions without it succeeds and for others it doesn't.
proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        // Implied by previous properties, possibly too aggressive trigger
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
{
}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask {
    pub closed spec fn view(&self) -> Set<int> {
        Set::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    proof fn lemma_view(&self)
        ensures
        // forall|i: int| self@.contains(i) ==> i < 512,
        // TODO: this isn't currently used but probably will need it (-> check later)
        (forall|i: int| self@.contains(i) ==> {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            &&& a * 64 + b == i
            &&& is_bit_set(self.mask[a], b)
        }),
        forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            ==> #[trigger] self@.contains(a * 64 + b),
    {
    }

    #[verifier::opaque]
    pub open spec fn bytes(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr: int|
            self@.contains(
                (addr - segment_start(segment_id)) / COMMIT_SIZE as int
            )
        )
    }

    pub fn empty() -> (cm: CommitMask)
        ensures cm@ == Set::<int>::empty()
    {
        let res = CommitMask { mask: [ 0, 0, 0, 0, 0, 0, 0, 0 ] };
        res
    }

    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == other@.subset_of(self@)
    {
        let mut i = 0;
        while i < 8
        {
            if self.mask[i] & other.mask[i] != other.mask[i] {
                return false;
            }
            i = i + 1;
        }
        return true;
    }

    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == !self@.disjoint(other@)
    {
        let mut i = 0;
        while i < 8
        {
            if self.mask[i] & other.mask[i] != 0 {
                return true;
            }
            i += 1;
        }
        return false;
    }

    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
        ensures res@ == self@.intersect(other@)
    {
        let mut i = 0;
        while i < 8
        {
            res.mask.set(i, self.mask[i] & other.mask[i]);
            i += 1;
        }
    }

    pub fn clear(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.difference(other@)
    {
        let mut i = 0;
        while i < 8
        {
            let m = self.mask[i];
            self.mask.set(i, m & !other.mask[i]);
            i += 1;
        }
    }

    pub fn set(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.union(other@)
    {
        let mut i = 0;
        while i < 8
        {
            let m = self.mask[i];
            self.mask.set(i, m | other.mask[i]);
            i += 1;
        }
    }

    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(Set::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
    {
    }

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == Set::<int>::empty(),
        ensures self@ == Set::new(|i: int| idx <= i < idx + count),
    {
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;

            while bitcount > 0
            {
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    ((1usize << c) - 1) << ofs
                };
                self.mask.set(i, mask);
                bitcount -= c;
                ofs = 0;
                i += 1;
            }
        }
    }

    pub fn create_empty(&mut self)
        ensures self@ == Set::<int>::empty(),
    {
        let mut i = 0;
        while i < 8
        {
            self.mask.set(i, 0);
            i += 1;
        }
    }

    pub fn create_full(&mut self)
        ensures self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS),
    {
        let mut i = 0;
        while i < 8
        {
            self.mask.set(i, !0usize);
            i += 1;
        }
    }

    pub fn committed_size(&self, total: usize) -> usize
    {
        todo(); loop { }
    }

    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
        requires 0 <= idx < COMMIT_MASK_BITS,
        ensures ({ let (next_idx, count) = res;
            next_idx + count <= COMMIT_MASK_BITS
            && (forall |t| next_idx <= t < next_idx + count ==> self@.contains(t))
        }),
        // This should be true, but isn't strictly needed to prove safety:
        //forall |t| idx <= t < next_idx ==> !self@.contains(t),
        // Likewise we could have a condition that `count` is not smaller than necessary
    {
        // Starting at idx, scan to find the first bit.

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        // Changed loop condition to use 8 rather than COMMIT_MASK_FIELD_COUNT due to
        // https://github.com/verus-lang/verus/issues/925
        while i < 8
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                {
                    mask = mask >> 1usize;
                    ofs += 1;
                }
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            // Count 1 bits in this run
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            loop
            {
                loop
                {
                    count += 1;
                    mask = mask >> 1usize;

                    if (mask & 1) != 1 {
                        break;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        break;
                    }
                    mask = self.mask[i];
                    ofs = 0;
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            (next_idx, count)
        }
    }

    pub fn is_empty(&self) -> (b: bool)
    ensures b == (self@ == Set::<int>::empty())
    {
        let mut i = 0;
        while i < 8
        {
            if self.mask[i] != 0 {
                return false;
            }
            i += 1;
        }
        return true;
    }

    pub fn is_full(&self) -> (b: bool)
    ensures b == (self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS))
    {

        let mut i = 0;
        while i < 8
        {
            if self.mask[i] != (!0usize) {
                return false;
            }
            i = i + 1;
        }

        return true;
    }
}

pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
}


}
