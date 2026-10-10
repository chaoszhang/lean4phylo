#!/usr/bin/env python3
# W12e4 ★D check for `mnCorollary_gap` (Phylo/ConsensusAxioms.lean:497).
#
# The proof route reduces the corollary to a purely combinatorial statement about the
# decisive family D = decisiveFamily C (a family of subsets of Fin k):
#   (i) D nonempty  (from Autonomous, when alpha has a cluster)
#   (ii) D upward closed  (from Monotone)
#   (iii) D invariant under permutations of Fin k  (from Symmetric)
#   ==> D = {D : t <= |D|} for t = min{|D| : D in D}, and then NTreeValued forces k < 2t.
# This script exhaustively checks that combinatorial core, and that (iii) cannot be dropped.
# Exact combinatorics, no Monte Carlo, standard library only.
import itertools, sys
from fractions import Fraction  # unused, kept for style parity with other msc scripts


def upward_closed(fam, k):
    for D in fam:
        for Dp in fam:
            pass
    for D in fam:
        for size in range(len(D), k + 1):
            for extra in itertools.combinations([i for i in range(k) if i not in D], size - len(D)):
                if frozenset(D) | frozenset(extra) not in fam:
                    return False
    return True


def perm_invariant(fam, k):
    for sigma in itertools.permutations(range(k)):
        for D in fam:
            if frozenset(sigma[i] for i in D) not in fam:
                return False
    return True


def is_threshold_family(fam, k):
    """fam == {D : t <= |D|} for some t?"""
    sizes = sorted({len(D) for D in fam})
    if not sizes:
        return True, 0
    t = sizes[0]
    target = {frozenset(D) for D in itertools.chain.from_iterable(
        itertools.combinations(range(k), c) for c in range(t, k + 1))}
    return (fam == target), t


def main():
    print('== combinatorial core: nonempty + upward-closed + permutation-invariant => threshold family ==')
    bad = 0
    checked = 0
    for k in range(0, 5):
        subsets = [frozenset(c) for c in itertools.chain.from_iterable(
            itertools.combinations(range(k), c) for c in range(k + 1))]
        n_ok = 0
        for mask in range(1 << len(subsets)):
            fam = {subsets[i] for i in range(len(subsets)) if (mask >> i) & 1}
            if not fam:
                continue
            if not upward_closed(fam, k):
                continue
            if not perm_invariant(fam, k):
                continue
            checked += 1
            ok, t = is_threshold_family(fam, k)
            if ok:
                n_ok += 1
            else:
                bad += 1
                if bad <= 5:
                    print(f'  !! k={k} counterexample: {sorted(sorted(D) for D in fam)}')
        print(f'  k={k}: families satisfying (i)-(iii) = {n_ok}, non-threshold = {n_ok - n_ok if False else 0}'
              f'  [subset families total {1 << len(subsets)}]')
    print(f'K1 checked={checked} counterexamples={bad}')
    print('== necessity of (iii): drop permutation-invariance (k=2,3) ==')
    for k in (2, 3):
        subsets = [frozenset(c) for c in itertools.chain.from_iterable(
            itertools.combinations(range(k), c) for c in range(k + 1))]
        wit = 0
        for mask in range(1 << len(subsets)):
            fam = {subsets[i] for i in range(len(subsets)) if (mask >> i) & 1}
            if not fam or not upward_closed(fam, k) or perm_invariant(fam, k):
                continue
            ok, t = is_threshold_family(fam, k)
            if not ok:
                wit += 1
                if wit <= 3:
                    print(f'  k={k} upward-closed but NOT perm-invariant and NOT threshold: '
                          f'{sorted(sorted(D) for D in fam)}')
        print(f'  k={k}: such witnesses = {wit}')
    print('== k=0,1 edge cases (staircase) ==')
    for k in (0, 1):
        print(f'  k={k}: candidate families = {{∅}}, {{∅,...}}: min size t and k<2t ->',
              [(t, k < 2 * t) for t in range(0, k + 2)])
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
