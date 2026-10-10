#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11h / X7 -- weak compatibility of split systems: exhaustive small-scale replication.

Reference: H.-J. Bandelt & A. W. M. Dress, "A canonical decomposition theory for metrics
on a finite set", Adv. Math. 92(1) (1992) 47-105.
Line numbers below refer to references/md/BandeltDress1992_CanonicalDecompositionMetrics.md

  * weak compatibility, definition (lines 1663-1679, Fig. 5):
      a collection S of splits of X is weakly compatible if there are no four points
      t,u,v,w in X and three splits S1,S2,S3 in S such that S1 extends {t,u},{v,w},
      S2 extends {t,v},{u,w}, S3 extends {t,w},{v,u}.
  * d-split / isolation index (lines 438-456):
      A|B is a d-split iff  d(a,a')+d(b,b') < max{d(a,b)+d(a',b'), d(a,b')+d(a',b)}
      for all a,a' in A, b,b' in B, iff the isolation index
        alpha_{A,B} = 1/2 * min{ max{d(a,b)+d(a',b'), d(a,b')+d(a',b)} - d(a,a') - d(b,b') }
      is positive.
  * THEOREM 3 (lines 1683-1699): (i) the d-splits of any symmetric d are weakly compatible;
      (ii) conversely, for weakly compatible S and lambda_S > 0, d := sum_S lambda_S delta_S
      has S as its exact set of d-splits, and alpha_S = lambda_S.
  * tree case (lines 539-547): a family is the split set of a four-point-condition metric
      iff it is pairwise compatible;  compatible => weakly compatible (strictly weaker).

Lean counterparts (Phylo/SplitWeak.lean):
    Split.WeaklyCompatible                    Split.HasConflictingQuartet
    Split.weaklyCompatible_of_pairwiseCompatible    (strong => weak)
    Split.weaklyCompatible_of_isDSplit              (Theorem 3 (i))
    Split.not_all_three_deficit_pos                 (pure max inequality)
    Split.weaklyCompatible_pair                     (weak is STRICTLY weaker)
    Cladogram.weaklyCompatible_splits

Pure standard library (fractions.Fraction only) -- exact arithmetic, no floating point,
no Monte Carlo.  Labels 1..n here are `Fin n` indices 0..n-1 in the Lean file.
Exits non-zero if any check fails.
"""

import itertools
import sys
from fractions import Fraction

FAIL = []


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------
# splits of {1..n}
# --------------------------------------------------------------------------
def splits_of(n):
    """All nontrivial splits of {1..n} as frozensets of two blocks (both sides >= 2)."""
    X = frozenset(range(1, n + 1))
    out, uniq = [], []
    for mask in range(1, 1 << n):
        A = frozenset(i for i in range(n) if mask >> i & 1)
        B = X - A
        if len(A) >= 2 and len(B) >= 2:
            out.append(frozenset((A, B)))
    for s in out:
        if s not in uniq:
            uniq.append(s)
    return uniq


def compatible(s, t):
    """One of the four intersections A n A', A n B', B n A', B n B' is empty."""
    A, B = tuple(s)
    C, D = tuple(t)
    return not (A & C) or not (A & D) or not (B & C) or not (B & D)


def pairwise_compatible(S):
    return all(compatible(s, t) for s in S for t in S)


def extends(s, p, q):
    """Split s extends the partial split {p}|{q} (either orientation)."""
    A, B = tuple(s)
    return (p <= A and q <= B) or (p <= B and q <= A)


def conflicting_quartet(S):
    """Witness (t,u,v,w) plus the three splits, or None (brute force, small n only)."""
    pts = sorted(set().union(*[set(b) for s in S for b in s])) if S else []
    for t, u, v, w in itertools.permutations(pts, 4):
        S1 = [s for s in S if extends(s, frozenset((t, u)), frozenset((v, w)))]
        S2 = [s for s in S if extends(s, frozenset((t, v)), frozenset((u, w)))]
        S3 = [s for s in S if extends(s, frozenset((t, w)), frozenset((v, u)))]
        if S1 and S2 and S3:
            return (t, u, v, w, S1[0], S2[0], S3[0])
    return None


def weakly_compatible(S):
    return conflicting_quartet(S) is None


# --- bitmask version (for exhaustive runs over thousands of families) --------
def masks_of(n, S_all):
    """For every 4-subset, the three bitmasks of splits inducing ab|cd, ac|bd, ad|bc."""
    out = []
    for quad in itertools.combinations(range(1, n + 1), 4):
        a, b, c, e = quad
        m1 = m2 = m3 = 0
        for i, s in enumerate(S_all):
            if extends(s, frozenset((a, b)), frozenset((c, e))):
                m1 |= 1 << i
            if extends(s, frozenset((a, c)), frozenset((b, e))):
                m2 |= 1 << i
            if extends(s, frozenset((a, e)), frozenset((b, c))):
                m3 |= 1 << i
        out.append((m1, m2, m3))
    return out


def weak_mask(quadmasks, fam):
    return not any((fam & m1) and (fam & m2) and (fam & m3) for m1, m2, m3 in quadmasks)


def pair_mask(compat_pairs, fam):
    return all(not (fam >> i & 1) or not (fam >> j & 1) or c
               for (i, j), c in compat_pairs.items())


# --------------------------------------------------------------------------
# isolation index of a split w.r.t. a symmetric function d  (exact, Fraction)
# --------------------------------------------------------------------------
def iso_index(d, s):
    """alpha_{A,B} = 1/2 * min over a,a' in A, b,b' in B of
       max{d(a,b)+d(a',b'), d(a,b')+d(a',b)} - d(a,a') - d(b,b')."""
    A, B = tuple(s)
    vals = [max(d(a, b) + d(a1, b1), d(a, b1) + d(a1, b))
            - d(a, a1) - d(b, b1)
            for a in A for a1 in A for b in B for b1 in B]
    return Fraction(1, 2) * min(vals)


def split_metric_sum(S, lam):
    def d(x, y):
        return sum((lam[s] for s in S
                    if extends(s, frozenset((x,)), frozenset((y,)))), Fraction(0))
    return d


def three_deficit(d, a, b, c, e):
    """(deficit for ab|ce, ac|be, ae|bc) = max(cross sums) - within sum."""
    X = d(a, b) + d(c, e)
    Y = d(a, c) + d(b, e)
    Z = d(a, e) + d(b, c)
    return (max(Y, Z) - X, max(X, Z) - Y, max(X, Y) - Z)


# --------------------------------------------------------------------------
def part_one():
    print("=" * 74)
    print("Part I -- exhaustive: pairwise compatible  ==>  weakly compatible")
    print("=" * 74)
    for n in (4, 5, 6):
        S_all = splits_of(n)
        quadmasks = masks_of(n, S_all)
        compat = {}
        for i in range(len(S_all)):
            for j in range(len(S_all)):
                compat[(i, j)] = compatible(S_all[i], S_all[j])
        nweak = npair = total = 0
        bad = 0
        smallest = None
        for r in range(len(S_all) + 1):
            for fam in itertools.combinations(range(len(S_all)), r):
                total += 1
                m = 0
                for i in fam:
                    m |= 1 << i
                w = weak_mask(quadmasks, m)
                p = pair_mask(compat, m)
                if w:
                    nweak += 1
                if p:
                    npair += 1
                if p and not w:
                    bad += 1
                if w and not p and (smallest is None or len(fam) < len(smallest)):
                    smallest = fam
        print("  n=%d : nontrivial splits=%d, split systems=%d" % (n, len(S_all), total))
        check("n=%d : every pairwise compatible family is weakly compatible" % n, bad == 0)
        check("n=%d : weak is STRICTLY weaker (%d weak vs %d pairwise)" % (n, nweak, npair),
              npair < nweak and nweak > 0)
        print("      smallest weak-but-not-pairwise family: %s"
              % sorted(sorted(tuple(sorted(b))) for b in S_all[i]) for i in smallest)


def part_two():
    print()
    print("=" * 74)
    print("Part II -- minimal examples and the 'three splits' obstruction")
    print("=" * 74)
    S4 = splits_of(4)
    print("  nontrivial splits of {1,2,3,4} (exactly the three 2|2 splits): %s"
          % [sorted(tuple(sorted(b)) for b in s) for s in S4])
    check("n=4 has exactly 3 nontrivial splits", len(S4) == 3)
    check("all three together are NOT weakly compatible "
          "[Lean: Split.hasConflictingQuartet_four]", not weakly_compatible(frozenset(S4)))
    for s in S4:
        check("each single 2|2 split is weakly compatible",
              weakly_compatible(frozenset([s])))
    for pair in itertools.combinations(S4, 2):
        check("every PAIR of the three 2|2 splits is weakly compatible "
              "(the two are incompatible; Fig. 5 needs THREE)",
              weakly_compatible(frozenset(pair)) and not compatible(*pair))

    S5 = splits_of(5)
    f5 = [s for s in S5 if frozenset((1, 2)) in s]
    g5 = [s for s in S5 if frozenset((1, 3)) in s]
    check("{1,2} and {1,3} each determine a unique nontrivial split on 5 taxa",
          len(f5) == 1 and len(g5) == 1)
    print("  Fin 5 witness of Split.exists_weaklyCompatible_not_pairwiseCompatible:")
    print("      {12|345, 13|245} = %s" % [sorted(tuple(sorted(b)) for b in s)
                                            for s in (f5[0], g5[0])])
    check("Fin 5 witness: weakly compatible but NOT pairwise compatible",
          weakly_compatible(frozenset((f5[0], g5[0]))) and not compatible(f5[0], g5[0]))

    S6 = splits_of(6)
    quad6 = masks_of(6, S6)
    nb = sum(1 for r in range(len(S6) + 1) for fam in itertools.combinations(range(len(S6)), r)
             if not weak_mask(quad6, sum(1 << i for i in fam)))
    check("anti-vacuity (n=6): non-weakly-compatible families DO exist (%d of 32768)" % nb,
          nb > 0)


def part_three():
    print()
    print("=" * 74)
    print("Part III -- pure max inequality  not_all_three_deficit_pos")
    print("=" * 74)
    bad = [(X, Y, Z) for X in range(-3, 4) for Y in range(-3, 4) for Z in range(-3, 4)
           if max(Y, Z) - X > 0 and max(X, Z) - Y > 0 and max(X, Y) - Z > 0]
    check("exhaustive over X,Y,Z in [-3,3]: never all three 4-point deficits positive "
          "[Lean: Split.not_all_three_deficit_pos]", bad == [])

    pts = [1, 2, 3, 4]
    bad2 = []
    for vals in itertools.product(range(0, 3), repeat=6):
        d = {}
        idx = 0
        for i, x in enumerate(pts):
            for y in pts[i + 1:]:
                d[(x, y)] = d[(y, x)] = Fraction(vals[idx])
                idx += 1
        for a, b, c, e in itertools.permutations(pts, 4):
            if all(v > 0 for v in three_deficit(lambda x, y: d[(x, y)], a, b, c, e)):
                bad2.append((a, b, c, e))
    check("exhaustive over symmetric d on 4 points with entries 0..2 (729 functions "
          "x 24 quadruples): never all three deficits positive", bad2 == [])


def part_four():
    print()
    print("=" * 74)
    print("Part IV -- Bandelt-Dress Theorem 3 (1683-1699), exact rational check")
    print("=" * 74)
    S4 = splits_of(4)

    ok_exact = ok_lambda = True
    ncase = 0
    for r in range(1, len(S4) + 1):
        for fam in itertools.combinations(S4, r):
            S = frozenset(fam)
            if not weakly_compatible(S):
                continue
            ordered = sorted(S, key=lambda s: sorted(tuple(sorted(b)) for b in s))
            for lamvals in itertools.product((1, 2, 3), repeat=len(ordered)):
                ncase += 1
                lam = dict(zip(ordered, [Fraction(v) for v in lamvals]))
                d = split_metric_sum(S, lam)
                if frozenset(s for s in S4 if iso_index(d, s) > 0) != S:
                    ok_exact = False
                for s in S:
                    if iso_index(d, s) != lam[s]:
                        ok_lambda = False
    print("  weakly compatible families on 4 taxa x weight vectors checked: %d" % ncase)
    check("n=4: alpha_{S'} > 0  <=>  S' in S  (Theorem 3, converse)", ok_exact)
    check("n=4: alpha_S == lambda_S on S  (Theorem 3, 'moreover' clause)", ok_lambda)

    ok_weak = True
    for vals in itertools.product(range(0, 4), repeat=6):
        d = {(1, 2): Fraction(vals[0]), (2, 1): Fraction(vals[0]),
             (1, 3): Fraction(vals[1]), (3, 1): Fraction(vals[1]),
             (1, 4): Fraction(vals[2]), (4, 1): Fraction(vals[2]),
             (2, 3): Fraction(vals[3]), (3, 2): Fraction(vals[3]),
             (2, 4): Fraction(vals[4]), (4, 2): Fraction(vals[4]),
             (3, 4): Fraction(vals[5]), (4, 3): Fraction(vals[5])}
        dd = lambda x, y: d[(x, y)]
        if not weakly_compatible(frozenset(s for s in S4 if iso_index(dd, s) > 0)):
            ok_weak = False
    check("n=4, all 4096 symmetric d with integer entries 0..3: the positive-index splits "
          "are weakly compatible  [Lean: weaklyCompatible_of_isDSplit]", ok_weak)

    lam = {s: Fraction(1) for s in S4}
    d = split_metric_sum(frozenset(S4), lam)
    pos = frozenset(s for s in S4 if iso_index(d, s) > 0)
    print("  S = all three 2|2 splits of {1,2,3,4}, lambda = (1,1,1):")
    print("      alpha values = %s" % [str(iso_index(d, s)) for s in S4])
    check("S not weakly compatible  ==>  {S' : alpha_{S'} > 0} is a PROPER subset of S "
          "(a positive coefficient does NOT make a split a d-split)",
          pos < frozenset(S4))

    ordered4 = sorted(S4, key=lambda s: sorted(tuple(sorted(b)) for b in s))
    lam2 = {s: Fraction(i + 1) for i, s in enumerate(ordered4)}
    d2 = split_metric_sum(frozenset(S4), lam2)
    pos2 = frozenset(s for s in S4 if iso_index(d2, s) > 0)
    print("  same S with lambda = (1,2,3): alpha values = %s"
          % [str(iso_index(d2, s)) for s in ordered4])
    check("lambda = (1,2,3): exactly the two splits of largest weight survive, and they "
          "are weakly compatible", len(pos2) == 2 and weakly_compatible(pos2))


def part_five():
    print()
    print("=" * 74)
    print("Part V -- n=5: Theorem 3 with lambda = 1 on every weakly compatible family")
    print("=" * 74)
    S5 = splits_of(5)
    quad5 = masks_of(5, S5)
    ok, cnt = True, 0
    for r in range(1, len(S5) + 1):
        for fam in itertools.combinations(range(len(S5)), r):
            m = sum(1 << i for i in fam)
            if not weak_mask(quad5, m):
                continue
            cnt += 1
            S = frozenset(S5[i] for i in fam)
            lam = {s: Fraction(1) for s in S}
            d = split_metric_sum(S, lam)
            if frozenset(s for s in S5 if iso_index(d, s) > 0) != S:
                ok = False
    print("  weakly compatible nonempty families on 5 taxa: %d of 1023" % cnt)
    check("n=5, lambda = 1: {S' : alpha_{S'} > 0} == S for every weakly compatible S "
          "(exhaustive)", ok and cnt > 0)


def main():
    part_one()
    part_two()
    part_three()
    part_four()
    part_five()
    print()
    if FAIL:
        print("FAILED CHECKS (%d): %s" % (len(FAIL), FAIL))
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
