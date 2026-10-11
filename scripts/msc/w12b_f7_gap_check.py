#!/usr/bin/env python3
# -*- coding: ascii -*-
"""W12b / F7 -- exhaustive (exact, no Monte Carlo) counterexample check for the two
explicit gaps left by W11 in `Phylo/RootedTriplet.lean` (lines 1168 / 1184):

  gap 1  rootedTriplet_aho_disconnect_gap :
      forall R T, (forall t in R, T.DisplaysTriplet t) ->
      forall S, (forall t in R, t.leaves subset S) -> 3 <= S.card ->
        not (tripletGraph S R).Preconnected
      (Bryant-Steel 1995 Theorem 2, lines 766-769, the (=>) half)

  gap 2  rootedTriplet_aho_converse_gap :
      forall R, DisplayedByTree R -> AhoOK (systemLeaves R) R
      (Aho et al. 1981 / ONETREE completeness)

Model (faithful to the Lean definitions):
  * a rooted tree on a leaf set Y is modelled by its family F of rooted clades
    (`RootedTree.IsRootedClade`, i.e. far-from-root side leaf sets of edges);
    these are exactly the laminar families F with Y in F and all singletons in F.
  * `T.DisplaysTriplet (ab|c) <-> exists C in F, {a,b} subset C, c not in C`
    (`RootedTree.displaysTriplet_iff_isRootedClade`).
  * `tripletGraph S R`: vertices S, edge {a,b} iff exists t in R with
    t.leaves subset S and a,b in t.pair.
  * `AhoOK S R`: |S| <= 1 success; else blocks (= connected components of
    tripletGraph S R) must number >= 2 and each block recursively succeeds.
  * Preconnected = graph has a single connected component.

Everything is integer/boolean; no floating point, no sampling.
"""

import sys
from itertools import combinations

# ---------------------------------------------------------------- hierarchies


def _laminar(A, B):
    return A <= B or B <= A or not (A & B)


def hierarchies(leaves):
    """All laminar families F on `leaves` with `leaves` in F and each singleton in F."""
    leaves = frozenset(leaves)
    if not leaves:
        return [frozenset()]
    base = frozenset({leaves}) | frozenset(frozenset([x]) for x in leaves)
    rest = [frozenset(c) for r in range(2, len(leaves)) for c in combinations(sorted(leaves), r)]
    out = []

    def rec(i, F):
        if i == len(rest):
            out.append(F)
            return
        C = rest[i]
        if all(_laminar(C, D) for D in F):
            rec(i + 1, F | {C})
        rec(i + 1, F)

    rec(0, base)
    return out


def displayed_triplets(F, X):
    """Set of rooted triplets displayed by the tree with clade family F."""
    tri = set()
    for C in F:
        for a, b in combinations(sorted(C), 2):
            for c in X:
                if c not in C:
                    tri.add((frozenset((a, b)), c))
    return frozenset(tri)


# ---------------------------------------------------------------- graph layer


def t_leaves(t):
    return set(t[0]) | {t[1]}


def components(S, R):
    """Connected components of tripletGraph S R, as frozensets."""
    S = list(S)
    parent = {x: x for x in S}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for t in R:
        if t_leaves(t) <= set(S):
            a, b = sorted(t[0])
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
    comp = {}
    for x in S:
        comp.setdefault(find(x), set()).add(x)
    return [frozenset(v) for v in comp.values()]


def preconnected(S, R):
    if not S:
        return True
    return len(components(S, R)) == 1


def aho_ok(S, R):
    S = frozenset(S)
    if len(S) <= 1:
        return True
    comps = components(S, R)
    if len(comps) < 2:
        return False
    return all(aho_ok(B, R) for B in comps)


def system_leaves(R):
    s = set()
    for t in R:
        s |= t_leaves(t)
    return frozenset(s)


# ---------------------------------------------------------------- main check


def subsets(iterable):
    lst = list(iterable)
    for r in range(len(lst) + 1):
        for c in combinations(lst, r):
            yield frozenset(c)


def main(nmax=5):
    gap1_counter = []          # (X, R, S)
    gap2_counter = []          # (X, R)
    n_trees = 0
    n_R_consistent = 0         # (X, R) pairs: R displayed by some enumerated tree
    n_gap1_pairs = 0           # (R, S) pairs tested in gap 1
    n_gap2_pairs = 0
    n_inconsistent_connected = 0   # anti-vacuity: inconsistent R with a connected [R,S]

    for n in range(3, nmax + 1):
        X = tuple(range(n))
        allR = {}
        for k in range(1, n + 1):
            for Y in combinations(X, k):
                for F in hierarchies(Y):
                    n_trees += 1
                    for t in displayed_triplets(F, frozenset(X)):
                        allR.setdefault(t, None)
        triplets = sorted(allR)          # canonical list of all triplets over X
        tindex = {t: i for i, t in enumerate(triplets)}
        fmask_cache = {}

        # every subset R of the full triplet set that is *some* tree's displayed set
        # (a subset of one) -- and all trees' displayed sets themselves
        consistent = set()
        for k in range(1, n + 1):
            for Y in combinations(X, k):
                for F in hierarchies(Y):
                    D = displayed_triplets(F, frozenset(X))
                    for sub in subsets(sorted(D, key=lambda t: tindex[t])):
                        consistent.add(sub)
        def rkey(R):
            return (len(R), tuple(sorted((tuple(sorted(t[0])), t[1]) for t in R)))

        consistent = sorted(consistent, key=rkey)

        for R in consistent:
            n_R_consistent += 1
            L = system_leaves(R)
            # ---- gap 1 : for every S with leaves(R) subset S, |S| >= 3
            for S in subsets(X):
                if not (L <= set(S)) or len(S) < 3:
                    continue
                n_gap1_pairs += 1
                if preconnected(set(S), R):
                    gap1_counter.append((X, R, S))
            # also test *every* S (not only supersets) for the anti-vacuity count
            # ---- gap 2
            n_gap2_pairs += 1
            if not aho_ok(L, R):
                gap2_counter.append((X, R))

        # anti-vacuity (the check must not be trivial): exhibit *connected* [R,S] instances.
        # n = 4: all 2^12 subsets; n >= 5: all subsets of size <= 3 (exact, bounded, no sampling)
        cand = []
        if n == 4:
            cand = list(subsets(triplets))
        else:
            cand = [frozenset(c) for r in range(0, 4) for c in combinations(triplets, r)]
        for R in cand:
            L = system_leaves(R)
            if len(L) >= 3 and preconnected(set(L), R):
                n_inconsistent_connected += 1
        print("  [n=%d] trees=%d  consistent R=%d  connected-[R,leaves(R)] instances=%d"
              % (n, n_trees, n_R_consistent, n_inconsistent_connected))

    print("nmax                       =", nmax)
    print("trees (hierarchies) counted=", n_trees)
    print("consistent (R) checked     =", n_R_consistent)
    print("gap1 (R,S) pairs tested    =", n_gap1_pairs)
    print("gap2 (R) tested            =", n_gap2_pairs)
    print("candidate R (n=4: all subsets; n=5: size<=3) with connected [R,leaves(R)] =",
          n_inconsistent_connected)
    print("GAP1 COUNTEREXAMPLES       =", len(gap1_counter))
    for c in gap1_counter[:10]:
        print("   ", c)
    print("GAP2 COUNTEREXAMPLES       =", len(gap2_counter))
    for c in gap2_counter[:10]:
        print("   ", c)
    ok = not gap1_counter and not gap2_counter
    print("VERDICT:", "PASS -- both gap statements hold on all instances (no counterexample)"
          if ok else "FAIL -- COUNTEREXAMPLE FOUND -> statement must be rewritten")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(int(sys.argv[1]) if len(sys.argv) > 1 else 5))
