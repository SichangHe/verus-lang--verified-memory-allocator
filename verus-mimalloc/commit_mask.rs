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
    assert(s1.union(s2).map(f) =~= s1.map(f).union(s2.map(f))) by {
        assert forall |x: T| s1.union(s2).map(f).contains(x) <==>
            s1.map(f).contains(x) || s2.map(f).contains(x) by {
            // Set::map definition: y in s.map(f) iff exists x in s: f(x) == y
            // s1.union(s2).map(f).contains(y) iff exists x in s1 or s2: f(x) == y
            // (s1.map(f) union s2.map(f)).contains(y) iff y in s1.map(f) or y in s2.map(f)
            // iff exists x in s1: f(x)==y or exists x in s2: f(x)==y
            // These are equal.
        };
    };
}

proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
{
    assert forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T|
        s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f)) by {
        lemma_map_distribute(s1, s2, f);
    };
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
    reveal(is_bit_set);
    let m = sub(1usize << n, 1) << o;
    assert forall |j: usize| j < o implies !is_bit_set(m, j) by {
        assert(!(m & (1usize << j) == (1usize << j))) by (bit_vector)
            requires n < 64, o <= 64 - n, j < o,
                m == sub(1usize << n, 1usize) << o;
    };
    assert forall |j: usize| o <= j < o + n implies is_bit_set(m, j) by {
        assert(m & (1usize << j) == (1usize << j)) by (bit_vector)
            requires n < 64, o <= 64 - n, o <= j, j < o + n,
                m == sub(1usize << n, 1usize) << o;
    };
    assert forall |j: usize| o + n <= j < 64 implies !is_bit_set(m, j) by {
        assert(!(m & (1usize << j) == (1usize << j))) by (bit_vector)
            requires n < 64, o <= 64 - n, o + n <= j, j < 64,
                m == sub(1usize << n, 1usize) << o;
    };
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
    // hi >= 1 since b != 0 and b >> hi == 0 implies hi >= 1
    assert(b != 0u64) by (bit_vector) requires a & b != b;
    assert(hi >= 1) by (bit_vector) requires b != 0u64, b >> hi == 0u64, hi <= 64;
    let hi1 = sub(hi, 1u64);
    if !(a & (1u64 << hi1) == (1u64 << hi1)) && (b & (1u64 << hi1) == (1u64 << hi1)) {
        hi1
    } else {
        let a2: u64 = a & !(1u64 << hi1);
        let b2: u64 = b & !(1u64 << hi1);
        assert(a2 & b2 != b2) by (bit_vector)
            requires a & b != b,
                !(!(a & (1u64 << hi1) == (1u64 << hi1))
                    && (b & (1u64 << hi1) == (1u64 << hi1))),
                a2 == a & !(1u64 << hi1),
                b2 == b & !(1u64 << hi1),
                hi1 == sub(hi, 1u64), hi >= 1;
        assert(a2 >> hi1 == 0u64) by (bit_vector)
            requires a >> hi == 0u64, a2 == a & !(1u64 << hi1), hi >= 1,
                hi1 == sub(hi, 1u64);
        assert(b2 >> hi1 == 0u64) by (bit_vector)
            requires b >> hi == 0u64, b2 == b & !(1u64 << hi1), hi >= 1,
                hi1 == sub(hi, 1u64);
        let result = lemma_obtain_bit_index_3_aux(a2, b2, hi1);
        assert(!(a & (1u64 << result) == (1u64 << result))) by (bit_vector)
            requires !(a2 & (1u64 << result) == (1u64 << result)),
                result < hi1,
                a2 == a & !(1u64 << hi1),
                hi1 == sub(hi, 1u64), hi >= 1;
        assert(b & (1u64 << result) == (1u64 << result)) by (bit_vector)
            requires b2 & (1u64 << result) == (1u64 << result),
                result < hi1,
                b2 == b & !(1u64 << hi1),
                hi1 == sub(hi, 1u64), hi >= 1;
        result
    }
}

proof fn lemma_obtain_bit_index_3(a: usize, b: usize) -> (i: usize)
    requires a & b != b
    ensures
        i < 64,
        !is_bit_set(a, i),
        is_bit_set(b, i),
{
    reveal(is_bit_set);
    assert(a as u64 & b as u64 != b as u64) by (bit_vector)
        requires a & b != b;
    assert((a as u64) >> 64u64 == 0u64) by (bit_vector);
    assert((b as u64) >> 64u64 == 0u64) by (bit_vector);
    let result = lemma_obtain_bit_index_3_aux(a as u64, b as u64, 64);
    // result < 64, !is_bit_set!(a as u64, result), is_bit_set!(b as u64, result)
    assert(!(a & (1usize << (result as usize)) == (1usize << (result as usize)))) by (bit_vector)
        requires !(a as u64 & (1u64 << result) == (1u64 << result)), result < 64;
    assert(b & (1usize << (result as usize)) == (1usize << (result as usize))) by (bit_vector)
        requires b as u64 & (1u64 << result) == (1u64 << result), result < 64;
    result as usize
}

proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    // a & !0 = a != !0, so a & !0 != !0
    assert(a & !0usize != !0usize) by (bit_vector) requires a != !0usize;
    let result = lemma_obtain_bit_index_3(a, !0usize);
    result
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
    assert(hi >= 1) by (bit_vector) requires a != 0u64, a >> hi == 0u64, hi <= 64;
    let hi1 = sub(hi, 1u64);
    if a & (1u64 << hi1) == (1u64 << hi1) {
        hi1
    } else {
        assert(a >> hi1 == 0u64) by (bit_vector)
            requires a >> hi == 0u64,
                !(a & (1u64 << hi1) == (1u64 << hi1)),
                hi >= 1, hi1 == sub(hi, 1u64);
        lemma_obtain_bit_index_1_aux(a, hi1)
    }
}

proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
{
    reveal(is_bit_set);
    assert(a as u64 != 0u64) by (bit_vector) requires a != 0;
    assert((a as u64) >> 64u64 == 0u64) by (bit_vector);
    let result = lemma_obtain_bit_index_1_aux(a as u64, 64);
    assert(a & (1usize << (result as usize)) == (1usize << (result as usize))) by (bit_vector)
        requires a as u64 & (1u64 << result) == (1u64 << result), result < 64;
    result as usize
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
    reveal(is_bit_set);
    assert forall |j: usize| j < 64 implies !(is_bit_set(0usize, j)) by {
        assert(!(0usize & (1usize << j) == (1usize << j))) by (bit_vector) requires j < 64;
    };
    assert forall |j: usize| is_bit_set(!0usize, j) by {
        assert((!0usize) & (1usize << j) == (1usize << j)) by (bit_vector);
    };
    assert forall |a: usize, b: usize, j: usize| is_bit_set(a | b, j) <==> is_bit_set(a, j) || is_bit_set(b, j) by {
        assert((a | b) & (1usize << j) == (1usize << j) <==>
            (a & (1usize << j) == (1usize << j) || b & (1usize << j) == (1usize << j))) by (bit_vector);
    };
    assert forall |a: usize, b: usize, j: usize| j < 64 implies
        (is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)) by {
        assert(((a & !b) & (1usize << j) == (1usize << j)) <==>
            (a & (1usize << j) == (1usize << j) && !(b & (1usize << j) == (1usize << j)))) by (bit_vector)
            requires j < 64;
    };
    assert forall |a: usize, b: usize, j: usize| is_bit_set(a & b, j) <==> is_bit_set(a, j) && is_bit_set(b, j) by {
        assert((a & b) & (1usize << j) == (1usize << j) <==>
            (a & (1usize << j) == (1usize << j) && b & (1usize << j) == (1usize << j))) by (bit_vector);
    };
    assert forall |a: usize, b: usize, j: usize| j < 64 implies
        (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)) by {
        assert(a & b == 0 ==> !(a & (1usize << j) == (1usize << j) && b & (1usize << j) == (1usize << j))) by (bit_vector)
            requires j < 64;
    };
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
        reveal(CommitMask::view);
        assert(usize::BITS == 64) by (compute_only);
        assert forall |i: int| self@.contains(i) implies {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            a * 64 + b == i && is_bit_set(self.mask[a], b)
        } by {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            // i >= 0 because self@ only contains a*64+b with a >= 0, b >= 0
            // b as int == i % 64 from the definition b = (i % 64) as usize
            assert(a * 64 + b as int == i) by (nonlinear_arith)
                requires a == i / 64, b as int == i % 64;
            // is_bit_set(self.mask[a], b) follows from view definition via choose
            let t = choose |t: (int, usize)|
                0 <= t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1) && t.0 * 64 + t.1 as int == i;
            assert(is_bit_set(self.mask[t.0], t.1));
            assert(t.0 * 64 + t.1 as int == i);
            assert(a == t.0 && b == t.1) by (nonlinear_arith) requires
                a * 64 + b as int == i, t.0 * 64 + t.1 as int == i,
                0 <= t.1 < 64, 0 <= b < 64;
            assert(is_bit_set(self.mask[a], b));
        };
        assert forall |a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            implies self@.contains(a * 64 + b) by {
            // Prove existential by providing the tuple witness (a, b)
            assert(Set::<(int, usize)>::new(|t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64 && is_bit_set(self.mask[t.0], t.1)).contains((a, b)));
        };
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
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(usize::BITS == 64) by (compute_only);
            assert(res.mask[0] == 0usize && res.mask[1] == 0usize &&
                res.mask[2] == 0usize && res.mask[3] == 0usize &&
                res.mask[4] == 0usize && res.mask[5] == 0usize &&
                res.mask[6] == 0usize && res.mask[7] == 0usize);
            assert(res@ =~= Set::<int>::empty()) by {
                assert forall |x: int| !res@.contains(x) by { };
            };
        }
        res
    }

    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == other@.subset_of(self@)
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64 && is_bit_set(other.mask[a], b)
                    ==> is_bit_set(self.mask[a], b),
        {
            if self.mask[i] & other.mask[i] != other.mask[i] {
                proof {
                    reveal(CommitMask::view);
                    let ii: int = i as int;
                    let bit_idx = lemma_obtain_bit_index_3(self.mask[ii], other.mask[ii]);
                    lemma_is_bit_set();
                    // bit_idx: is_bit_set(other.mask[ii], bit_idx) && !is_bit_set(self.mask[ii], bit_idx)
                    assert(is_bit_set(other.mask[ii], bit_idx));
                    assert(!is_bit_set(self.mask[ii], bit_idx));
                    assert(0 <= ii < 8);
                    assert(bit_idx < 64);
                    // other@.contains(ii * 64 + bit_idx): by view definition
                    assert(other@.contains(ii * 64 + bit_idx as int));
                    // !self@.contains(ii * 64 + bit_idx): by view definition
                    assert(!self@.contains(ii * 64 + bit_idx as int));
                }
                return false;
            }
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 && is_bit_set(other.mask[i as int], b)
                    implies is_bit_set(self.mask[i as int], b) by {
                    assert(self.mask[i as int] & other.mask[i as int] == other.mask[i as int]);
                    assert(is_bit_set(self.mask[i as int] & other.mask[i as int], b));
                };
            }
            i = i + 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(other@.subset_of(self@)) by {
                assert forall |x: int| other@.contains(x) implies self@.contains(x) by {
                    // other@.contains(x) means exists (a, b) with 0<=a<8, b<64,
                    // is_bit_set(other.mask[a], b), and a*64+b == x
                    let t = choose |t: (int, usize)| 0 <= t.0 < 8 && t.1 < 64
                        && is_bit_set(other.mask[t.0], t.1) && t.0 * 64 + t.1 as int == x;
                    assert(0 <= t.0 < 8 && t.1 < 64);
                    assert(is_bit_set(other.mask[t.0], t.1));
                    // From loop invariant (i==8): is_bit_set(self.mask[t.0], t.1)
                    assert(is_bit_set(self.mask[t.0], t.1));
                    // So self@.contains(x)
                };
            };
        }
        return true;
    }

    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
        ensures res == !self@.disjoint(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64
                    ==> !(is_bit_set(self.mask[a], b) && is_bit_set(other.mask[a], b)),
        {
            if self.mask[i] & other.mask[i] != 0 {
                proof {
                    let ii: int = i as int;
                    let bit_idx = lemma_obtain_bit_index_1(self.mask[ii] & other.mask[ii]);
                    lemma_is_bit_set();
                    reveal(CommitMask::view);
                    assert(is_bit_set(self.mask[ii], bit_idx));
                    assert(is_bit_set(other.mask[ii], bit_idx));
                    assert(self@.contains(ii * 64 + bit_idx as int));
                    assert(other@.contains(ii * 64 + bit_idx as int));
                }
                return true;
            }
            proof {
                lemma_is_bit_set();
                let ii: int = i as int;
                assert forall |b: usize| b < 64 implies
                    !(is_bit_set(self.mask[ii], b) && is_bit_set(other.mask[ii], b)) by {
                    assert(self.mask[ii] & other.mask[ii] == 0usize);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
        }
        return false;
    }

    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
        ensures res@ == self@.intersect(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64
                    ==> (is_bit_set(res.mask[a], b) <==> (is_bit_set(self.mask[a], b) && is_bit_set(other.mask[a], b))),
        {
            res.mask[i] = self.mask[i] & other.mask[i];
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 implies
                    (is_bit_set(res.mask[i as int], b) <==>
                    (is_bit_set(self.mask[i as int], b) && is_bit_set(other.mask[i as int], b))) by {
                    assert(res.mask[i as int] == self.mask[i as int] & other.mask[i as int]);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
        }
    }

    pub fn clear(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.difference(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64
                    ==> (is_bit_set(self.mask[a], b) <==>
                        (is_bit_set(old(self).mask[a], b) && !is_bit_set(other.mask[a], b))),
                forall |a: int, b: usize| i as int <= a < 8 && b < 64
                    ==> is_bit_set(self.mask[a], b) == is_bit_set(old(self).mask[a], b),
        {
            let m = self.mask[i];
            self.mask[i] = m & !other.mask[i];
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 implies
                    (is_bit_set(self.mask[i as int], b) <==>
                    (is_bit_set(old(self).mask[i as int], b) && !is_bit_set(other.mask[i as int], b))) by {
                    assert(self.mask[i as int] == m & !other.mask[i as int]);
                    assert(m == old(self).mask[i as int]);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
        }
    }

    pub fn set(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.union(other@)
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64
                    ==> (is_bit_set(self.mask[a], b) <==>
                        (is_bit_set(old(self).mask[a], b) || is_bit_set(other.mask[a], b))),
                forall |a: int, b: usize| i as int <= a < 8 && b < 64
                    ==> is_bit_set(self.mask[a], b) == is_bit_set(old(self).mask[a], b),
        {
            let m = self.mask[i];
            self.mask[i] = m | other.mask[i];
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 implies
                    (is_bit_set(self.mask[i as int], b) <==>
                    (is_bit_set(old(self).mask[i as int], b) || is_bit_set(other.mask[i as int], b))) by {
                    assert(self.mask[i as int] == m | other.mask[i as int]);
                    assert(m == old(self).mask[i as int]);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
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
        reveal(CommitMask::view);
        lemma_is_bit_set();
    }

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == Set::<int>::empty(),
        ensures self@ == Set::new(|i: int| idx <= i < idx + count),
    {
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
            proof {
                const_facts();
                assert(COMMIT_MASK_BITS == 512) by (compute_only);
                // create_full gives self@ == Set::new(|i| 0 <= i < 512)
                // idx == 0 and count == 512 since idx + count == 512 and idx >= 0
                assert(idx == 0) by (nonlinear_arith)
                    requires idx + count <= 512, count == 512;
                assert(self@ =~= Set::new(|i: int| idx <= i < idx + count)) by {
                    assert forall |i: int| self@.contains(i) <==>
                        (idx as int <= i && i < idx as int + count as int) by { };
                };
            }
        } else if count == 0 {
            proof {
                assert(self@ =~= Set::new(|i: int| idx <= i < idx + count)) by {
                    assert forall |i: int| !self@.contains(i) by {
                        if self@.contains(i) {
                            // old(self)@ == empty and we haven't modified self
                            // But self@ == old(self)@ == empty
                        }
                    };
                };
            }
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;

            while bitcount > 0
                invariant
                    i <= 8,
                    ofs < 64,
                    bitcount <= count,
                    idx + count - bitcount == i as int * 64 + ofs as int,
                    // The bits set so far match Set::new(|j| idx <= j < idx + count - bitcount)
                    forall |a: int, b: usize| 0 <= a < 8 && b < 64
                        ==> is_bit_set(self.mask[a], b) <==>
                            (idx as int <= a * 64 + b && a * 64 + b < idx as int + count as int - bitcount as int),
            {
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    ((1usize << c) - 1) << ofs
                };
                self.mask[i] = mask;
                proof {
                    lemma_is_bit_set();
                    if c < usize::BITS as usize {
                        lemma_bitmask_to_is_bit_set(c, ofs);
                    }
                }
                bitcount -= c;
                ofs = 0;
                i += 1;
            }
            proof {
                reveal(CommitMask::view);
                assert(usize::BITS == 64) by (compute_only);
                assert(COMMIT_MASK_BITS == 512) by (compute_only);
                assert(self@ =~= Set::new(|i: int| idx <= i < idx + count)) by {
                    assert forall |x: int| self@.contains(x) <==>
                        (idx as int <= x && x < idx as int + count as int) by {
                        let a: int = x / 64;
                        let b: usize = (x % 64) as usize;
                        assert(a * 64 + b as int == x) by (nonlinear_arith);
                    };
                };
            }
        }
    }

    pub fn create_empty(&mut self)
        ensures self@ == Set::<int>::empty(),
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64 ==> !is_bit_set(self.mask[a], b),
        {
            self.mask[i] = 0;
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 implies !is_bit_set(self.mask[i as int], b) by {
                    assert(self.mask[i as int] == 0usize);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(self@ =~= Set::<int>::empty()) by {
                assert forall |x: int| !self@.contains(x) by { };
            };
        }
    }

    pub fn create_full(&mut self)
        ensures self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS),
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64 ==> is_bit_set(self.mask[a], b),
        {
            self.mask[i] = !0usize;
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| is_bit_set(self.mask[i as int], b) by {
                    assert(self.mask[i as int] == !0usize);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(COMMIT_MASK_BITS == 512) by (compute_only);
            assert(self@ =~= Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS)) by {
                assert forall |x: int| self@.contains(x) <==> (0 <= x && x < 512) by {
                    let a: int = x / 64;
                    let b: usize = (x % 64) as usize;
                    assert(a * 64 + b as int == x) by (nonlinear_arith);
                };
            };
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
    {
        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        while i < 8
            invariant
                i <= 8,
                ofs < 64,
                mask == self.mask[i as int] >> ofs,
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                    invariant
                        ofs < 64,
                        mask == self.mask[i as int] >> ofs,
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
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            proof {
                assert(usize::BITS == 64) by (compute_only);
                assert(COMMIT_MASK_BITS == 512) by (compute_only);
                assert(next_idx == i * 64usize + ofs);
                assert(next_idx as int == i as int * 64 + ofs as int) by (nonlinear_arith)
                    requires next_idx == i * 64usize + ofs, i < 8, ofs < 64;
                assert(i as int == (next_idx as int) / 64) by (nonlinear_arith)
                    requires next_idx as int == i as int * 64 + ofs as int, ofs < 64;
                assert(next_idx <= 511) by (nonlinear_arith)
                    requires next_idx as int == i as int * 64 + ofs as int, i < 8, ofs < 64;
                assert(mask & 1usize == 1usize) by (bit_vector) requires mask & 1usize != 0usize;
            }
            // ghost_ofs tracks (next_idx + count) % 64, avoiding spec-mode type issues
            let ghost mut ghost_ofs: usize = ofs;
            loop
                invariant
                    mask & 1usize == 1usize,
                    i < 8,
                    i as int == (next_idx as int + count as int) / 64,
                    ghost_ofs < 64usize,
                    ghost_ofs as int == (next_idx as int + count as int) % 64,
                    mask == self.mask[i as int] >> ghost_ofs,
                    forall |t: int| next_idx as int <= t < next_idx as int + count as int ==>
                        #[trigger] is_bit_set(self.mask[t / 64], (t % 64) as usize),
                    next_idx + count <= COMMIT_MASK_BITS as usize,
            {
                loop
                    invariant
                        mask & 1usize == 1usize,
                        i < 8,
                        i as int == (next_idx as int + count as int) / 64,
                        ghost_ofs < 64usize,
                        ghost_ofs as int == (next_idx as int + count as int) % 64,
                        mask == self.mask[i as int] >> ghost_ofs,
                        forall |t: int| next_idx as int <= t < next_idx as int + count as int ==>
                            #[trigger] is_bit_set(self.mask[t / 64], (t % 64) as usize),
                        next_idx + count < COMMIT_MASK_BITS as usize,
                {
                    proof {
                        reveal(is_bit_set);
                        let pos: int = next_idx as int + count as int;
                        // Bind to local to avoid interpreter bug with self.mask[i as int]
                        let mi: usize = self.mask[i as int];
                        // mask = mi >> ghost_ofs, mask & 1 = 1 => is_bit_set(mi, ghost_ofs)
                        assert(mi & (1usize << ghost_ofs) == (1usize << ghost_ofs)) by (bit_vector)
                            requires (mi >> ghost_ofs) & 1usize == 1usize, ghost_ofs < 64usize;
                        assert(is_bit_set(mi, ghost_ofs));
                        assert(is_bit_set(self.mask[i as int], ghost_ofs));
                        assert(ghost_ofs == (pos % 64) as usize) by (nonlinear_arith)
                            requires ghost_ofs as int == pos % 64, ghost_ofs < 64;
                        assert(is_bit_set(self.mask[i as int], (pos % 64) as usize));
                        // i == pos / 64 from invariant
                        assert(is_bit_set(self.mask[pos / 64], (pos % 64) as usize));
                    }
                    count += 1;
                    mask = mask >> 1usize;
                    proof { ghost_ofs = (ghost_ofs + 1) as usize; }

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
                    proof { ghost_ofs = 0usize; }
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            proof {
                reveal(CommitMask::view);
                assert(usize::BITS == 64) by (compute_only);
                assert(COMMIT_MASK_BITS == 512) by (compute_only);
                lemma_is_bit_set();
                assert(forall |t: int| next_idx as int <= t < next_idx as int + count as int ==>
                    self@.contains(t)) by {
                    assert forall |t: int| next_idx as int <= t < next_idx as int + count as int
                        implies self@.contains(t) by {
                        assert(is_bit_set(self.mask[t / 64], (t % 64) as usize));
                    };
                };
            }

            (next_idx, count)
        }
    }

    pub fn is_empty(&self) -> (b: bool)
    ensures b == (self@ == Set::<int>::empty())
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64 ==> !is_bit_set(self.mask[a], b),
        {
            if self.mask[i] != 0 {
                proof {
                    reveal(CommitMask::view);
                    lemma_is_bit_set();
                    let ii: int = i as int;
                    let bit_idx = lemma_obtain_bit_index_1(self.mask[ii]);
                    assert(is_bit_set(self.mask[ii], bit_idx));
                    assert(self@.contains(ii * 64 + bit_idx as int));
                }
                return false;
            }
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| b < 64 implies !is_bit_set(self.mask[i as int], b) by {
                    assert(self.mask[i as int] == 0usize);
                };
            }
            i += 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(self@ =~= Set::<int>::empty()) by {
                assert forall |x: int| !self@.contains(x) by { };
            };
        }
        return true;
    }

    pub fn is_full(&self) -> (b: bool)
    ensures b == (self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS))
    {
        let mut i = 0;
        while i < 8
            invariant
                i <= 8,
                forall |a: int, b: usize| 0 <= a < i as int && b < 64 ==> is_bit_set(self.mask[a], b),
        {
            if self.mask[i] != (!0usize) {
                proof {
                    reveal(CommitMask::view);
                    lemma_is_bit_set();
                    let ii: int = i as int;
                    let bit_idx = lemma_obtain_bit_index_2(self.mask[ii]);
                    let bid: int = bit_idx as int;
                    assert(!is_bit_set(self.mask[ii], bit_idx));
                    assert(COMMIT_MASK_BITS == 512) by (compute_only);
                    assert(0 <= ii * 64 + bid && ii * 64 + bid < 512);
                    assert(!self@.contains(ii * 64 + bid));
                }
                return false;
            }
            proof {
                lemma_is_bit_set();
                assert forall |b: usize| is_bit_set(self.mask[i as int], b) by {
                    assert(self.mask[i as int] == !0usize);
                };
            }
            i = i + 1;
        }
        proof {
            reveal(CommitMask::view);
            lemma_is_bit_set();
            assert(COMMIT_MASK_BITS == 512) by (compute_only);
            assert(self@ =~= Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS)) by {
                assert forall |x: int| self@.contains(x) <==> (0 <= x && x < 512) by {
                    let a: int = x / 64;
                    let b: usize = (x % 64) as usize;
                    assert(a * 64 + b as int == x) by (nonlinear_arith);
                };
            };
        }
        return true;
    }
}

pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
    reveal(CommitMask::bytes);
    const_facts();
    assert(COMMIT_SIZE == SLICE_SIZE);
    assert(COMMIT_SIZE == 65536) by (compute_only);
    assert forall |addr: int| set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE as int).contains(addr)
        implies mask.bytes(sid).contains(addr) by {
        // addr is in [seg_start, seg_start + COMMIT_SIZE)
        // mask.bytes(sid) contains addr iff mask@.contains((addr - seg_start) / COMMIT_SIZE)
        // (addr - seg_start) / COMMIT_SIZE == 0 (since 0 <= addr - seg_start < COMMIT_SIZE)
        let diff: int = addr - segment_start(sid);
        assert(0 <= diff && diff < COMMIT_SIZE as int);
        assert(diff / COMMIT_SIZE as int == 0) by (nonlinear_arith)
            requires 0 <= diff, diff < COMMIT_SIZE as int, COMMIT_SIZE as int > 0;
        assert(mask@.contains(0));
        assert(mask.bytes(sid).contains(addr));
    };
}


}
