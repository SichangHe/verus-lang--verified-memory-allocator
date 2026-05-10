#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

verus!{

// TODO: This belongs in set_lib
proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.finite(),
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b,
{
    assert_by_contradiction!(a == b, {
        let s2 = s.remove(a);
        assert(s2.contains(b));
        assert(s2.finite());
        assert(s2.len() == 0);
        // s2.len() >= 1 since s2 contains b
        assert(s2.len() == s2.remove(b).len() + 1);
    });
}

proof fn set_mismatch(s1:Set<nat>, s2:Set<nat>, missing:nat)
    requires
        s1.finite(),
        s2.finite(),
        s1.len() == s2.len(),
        forall |elt| s2.contains(elt) ==> s1.contains(elt),
        s1.contains(missing),
        !s2.contains(missing),
    ensures
        false,
    decreases s1.len(),
{
    if s1.len() == 0 {
        // s1 has no elements but contains missing - contradiction
        assert(s1.len() == s1.remove(missing).len() + 1);
    } else {
        // s2 is non-empty (same length as s1 > 0)
        // Pick an element from s2
        let x: nat = s2.choose();
        assert(s2.contains(x));
        assert(s1.contains(x));
        let s1p = s1.remove(x);
        let s2p = s2.remove(x);
        assert(s1p.len() == s1.len() - 1);
        assert(s2p.len() == s2.len() - 1);
        assert(s1p.len() == s2p.len());
        assert(forall |elt| s2p.contains(elt) ==> s1p.contains(elt)) by {
            assert forall |elt| s2p.contains(elt) implies s1p.contains(elt) by {
                assert(s2.contains(elt) && elt != x);
                assert(s1.contains(elt));
            };
        };
        // missing is not in s2 but x is, so missing != x
        assert(missing != x);
        assert(s1p.contains(missing));
        assert(!s2p.contains(missing));
        set_mismatch(s1p, s2p, missing);
    }
}

/* TODO: These next two should be derived from the set_int_range and lemma_int_range in
 *       set_lib.rs, but it's surprisingly painful to do so */

/// Creates a finite set of nats in the range [lo, hi).
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::new(|i: nat| lo <= i && i < hi)
}

/// If a set solely contains nats in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).finite(),
        set_nat_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
{
    if lo == hi {
        assert(set_nat_range(lo, hi) =~= Set::<nat>::empty()) by {
            assert forall |i: nat| !set_nat_range(lo, hi).contains(i) by { };
        };
    } else {
        let hi1: nat = (hi - 1) as nat;
        assert(lo <= hi1);
        lemma_nat_range(lo, hi1);
        assert(set_nat_range(lo, hi) =~= set_nat_range(lo, hi1).insert(hi1)) by {
            assert forall |i: nat| set_nat_range(lo, hi).contains(i) <==>
                set_nat_range(lo, hi1).contains(i) || i == hi1 by { };
        };
        assert(!set_nat_range(lo, hi1).contains(hi1));
    }
}


proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.finite(),
        s.len() == bound,
{
    assert(s =~= set_nat_range(0, bound)) by {
        assert forall |i: nat| s.contains(i) <==> set_nat_range(0, bound).contains(i) by { };
    };
    lemma_nat_range(0, bound);
}



pub proof fn pigeonhole_missing_idx_implies_double_helper(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
    prev_vals: Set<nat>,
    k: nat,
) -> (dup2: nat)
    requires
        len >= 2,
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
        0 <= k < len,
        prev_vals.finite(),
        prev_vals.len() == k,
        //forall |j| 0 <= j < k ==> #[trigger] prev_vals.contains(m[j]),
        forall |elt| #[trigger] prev_vals.contains(elt) ==> exists |j| 0 <= j < k && m[j] == elt,
    ensures
        m.dom().contains(dup2),
        exists |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2],
    decreases len - k,
{
    if prev_vals.contains(m[k]) {
        // m[k] is already a value we've seen: found a duplicate
        let val = m[k];
        let dup1 = choose |j: nat| 0 <= j < k && m[j] == val;
        k
    } else {
        // Show k+1 < len: if k == len-1, then prev_vals covers all len-1 possible values
        // but m[k] is a possible value not in prev_vals - contradiction
        assert(k + 1 < len) by {
            if k + 1 >= len {
                // k == len - 1 (since k < len)
                assert(k == len - 1);
                // All values in prev_vals are in {0..len} \ {missing}
                // prev_vals.len() == len - 1 == |{0..len} \ {missing}|
                // So prev_vals == {0..len} \ {missing}
                // But m[k] is in {0..len} \ {missing} and not in prev_vals
                let all_vals = Set::<nat>::new(|v: nat| 0 <= v < len && v != missing);
                // Prove all_vals.finite() and all_vals.len() == len - 1
                let full_range = set_nat_range(0, len);
                lemma_nat_range(0, len);
                assert(full_range.finite() && full_range.len() == len);
                assert(full_range.contains(missing));
                assert(all_vals =~= full_range.remove(missing)) by {
                    assert forall |v: nat| all_vals.contains(v) <==>
                        full_range.remove(missing).contains(v) by { };
                };
                assert(full_range.len() == full_range.remove(missing).len() + 1);
                assert(all_vals.finite());
                assert(all_vals.len() == (len - 1) as nat);
                // prev_vals ⊆ all_vals
                assert(forall |v: nat| #[trigger] prev_vals.contains(v) ==> all_vals.contains(v)) by {
                    assert forall |v: nat| prev_vals.contains(v) implies all_vals.contains(v) by {
                        let j = choose |j: nat| 0 <= j < k && m[j] == v;
                        assert(0 <= j < k && m[j] == v);
                        assert(m.dom().contains(j));
                        assert(m[j] < len && m[j] != missing);
                    };
                };
                assert(m.dom().contains(k));
                assert(0 <= m[k] < len && m[k] != missing);
                assert(all_vals.contains(m[k]));
                assert(!prev_vals.contains(m[k]));
                set_mismatch(all_vals, prev_vals, m[k]);
            }
        };
        let new_prev_vals = prev_vals.insert(m[k]);
        assert(new_prev_vals.len() == k + 1);
        assert(new_prev_vals.finite());
        assert(forall |elt| #[trigger] new_prev_vals.contains(elt) ==>
            exists |j| 0 <= j < k + 1 && m[j] == elt) by {
            assert forall |elt| #[trigger] new_prev_vals.contains(elt) implies
                exists |j: nat| 0 <= j < k + 1 && m[j] == elt by {
                if prev_vals.contains(elt) {
                    let j = choose |j: nat| 0 <= j < k && m[j] == elt;
                    assert(m[j] == elt);
                } else {
                    assert(elt == m[k]);
                    assert(m[k] == elt);
                }
            };
        };
        pigeonhole_missing_idx_implies_double_helper(m, missing, len, new_prev_vals, k + 1)
    }
}

pub proof fn pigeonhole_missing_idx_implies_double(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    if len < 2 {
        // len == 1, missing == 0, but then m[0] must be in {0..1} \ {0} = {} - impossible
        assert(len >= 1);
        assert(m.dom().contains(0nat));
        assert(0nat < len);
        assert(m[0nat] < len && m[0nat] != missing);
        assert(m[0nat] < 1 && m[0nat] != 0nat);
        // m[0] must be in {0..1} \ {0} = {} - impossible
        assert(false);
        (0, 0)
    } else {
        let empty_prev: Set<nat> = Set::empty();
        assert(empty_prev.finite());
        assert(empty_prev.len() == 0);
        assert(forall |elt| #[trigger] empty_prev.contains(elt) ==>
            exists |j: nat| 0 <= j < 0nat && m[j] == elt);
        let dup2 = pigeonhole_missing_idx_implies_double_helper(
            m, missing, len, empty_prev, 0
        );
        let dup1 = choose |j: nat| j != dup2 && m.dom().contains(j) && 0 <= j < len && m[j] == m[dup2];
        (dup1, dup2)
    }
}

pub proof fn pigeonhole_too_many_elements_implies_double(
    m: Map<nat, nat>,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len + 1 <==> m.dom().contains(i)),
        forall |i: nat| #[trigger] m.dom().contains(i) ==> 0 <= m[i] < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    // Domain has len+1 elements, range has len values -> pigeonhole
    // Find a value in {0..len} not in range of first len elements...
    // Actually use missing_idx version: find a "missing" value
    // The domain {0..len+1} maps to {0..len}, so some value in {0..len} is hit twice
    // Equivalently, some value v in {0..len+1} is the "missing" output

    // Build a set of all output values from indices 0..len (not len+1)
    let output_vals = Set::<nat>::new(|v: nat| exists |i: nat| 0 <= i < len && m[i] == v);
    // output_vals ⊆ {0..len} which has len elements
    // output_vals has at most len elements
    // The domain has len+1 elements, so by pigeonhole...

    // Use the missing_idx version: m maps {0..len+1} to {0..len}
    // There must be some missing value in {0..len} that's not achieved
    // ... or we find two indices with the same value

    // Actually, let's just construct the right map and apply pigeonhole_missing_idx
    // Map m' : {0..len} -> {0..len} restricted to first len indices
    // If m' is injective, then m' covers {0..len} and m[len] must duplicate something

    // Simpler: use pigeonhole on the full map with the extra element
    // Find missing value in the range
    let range_vals = Set::<nat>::new(|v: nat| 0 <= v < len && exists |i: nat| 0 <= i < len + 1 && m[i] == v);

    // If range_vals == {0..len}: all values are covered. Then m[len] maps to some value
    // that was already covered by an earlier index. So we have a duplicate.
    // If range_vals != {0..len}: there's a missing value 'miss' in {0..len}.
    // Then all len+1 indices map to the len-1 values in range_vals.
    // Actually let's find the missing value:

    // The range has at most len distinct values (subset of {0..len})
    // But the domain has len+1 elements, so by counting...

    // Let me use a different approach: induct on len
    // Or better: reduce to pigeonhole_missing_idx_implies_double

    // If some value v in {0..len} is not in the range of m:
    //   Then m : {0..len+1} -> {0..len+1} \ {v} and we can apply pigeonhole_missing
    // If all values in {0..len} are in range:
    //   Then m[0..len] covers all of {0..len}, so m[len] duplicates one of them.

    // Let me check if there's a missing value in {0..len}:
    // If for all v in {0..len}, exists i in {0..len+1}: m[i] == v
    // Then the range of m covers {0..len}. In particular, m[0..len] already covers {0..len}
    // (since we have len+1 elements mapping to len values, by pigeonhole some pair in {0..len}
    // must share a value).

    // Let me construct a proof:
    // S1 = set of (i, v) pairs where m[i] = v, i in {0..len+1}
    // Each i appears exactly once. Total len+1 pairs.
    // Each v in {0..len} can appear multiple times.
    // If no v appears multiple times, then there are len+1 distinct v's in {0..len} - impossible.

    // By pigeonhole_missing_idx_implies_double:
    // m : {0..len+1} -> {0..len} -> need len+1 in domain and missing in {0..len+1}
    // Hmm, the domain should be {0..len+1} which has len+1 elements, range {0..len}
    // We need to find a "missing" value in {0..len+1} to use that lemma.

    // Actually let me just use set_mismatch more directly.
    // Map restricted to {0..len}: m' maps {0..len} -> {0..len}
    // If m' is injective, then m' is bijective, and m[len] must duplicate.
    // If m' is not injective, we're done.

    // Simplest: prove by contradiction that m is not injective.
    // If m is injective: m : {0..len+1} -> {0..len} is injective
    // => |range(m)| = |domain(m)| = len+1 > len = |{0..len}|, contradiction.

    // But showing this size argument requires more work...

    // Let's just use pigeonhole_missing_idx_implies_double with a constructed missing value.
    // We need a value in {0..len+1} not in the range of m restricted to {0..len+1}.
    // But the range is in {0..len} ⊆ {0..len+1} \ {len}.
    // So m[i] != len for all i in {0..len+1}.
    // len is a valid "missing" value in {0..len+1}.

    // Build map m2 : {0..len+1} -> {0..len+1} by m2[i] = m[i] (same map, range ⊆ {0..len} ⊆ {0..len+1}\{len})
    // Now apply pigeonhole_missing_idx_implies_double(m2, len, len+1).

    // Check preconditions:
    // forall i: 0 <= i < len+1 <==> m2.dom().contains(i) ✓ (given)
    // forall i: m2.dom().contains(i) ==> 0 <= m2[i] < len+1 && m2[i] != len ✓ (m[i] < len < len+1 and m[i] != len)
    // 0 <= len < len+1 ✓

    let result = pigeonhole_missing_idx_implies_double(m, len, len + 1);
    result
}

}
