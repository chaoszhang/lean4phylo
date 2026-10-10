#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11c / C7 -- supertree non-existence: exhaustive small-scale replication.

Reference: Steel, Boecker & Dress 2000, "Simple but fundamental limitations on
supertree and consensus tree methods", Syst. Biol. 49(2):363-368.
  Proposition 1 (lines 97-100, proof 101-147): no supertree method satisfies
      P1 (unordered input), P2 (equivariance under taxon renaming), P3 (output
      displays all inputs whenever they are compatible) for UNROOTED trees.
      Witness: taxa 1..6, input quartets (12)(45), (34)(16), (56)(23);
      sigma = (2 6)(3 5) fixes the unordered input but swaps the two parents.
      Lean counterpart:
        Phylo/SupertreeLimits.lean  SBD.no_supertree_method_P2_P3
                                    SBD.no_invariant_tree_displays_two_quartets
  Proposition 3, second half (lines 300-306, "it is easily verified" 312-315):
      no consensus method for ROOTED trees satisfies P7.  Witness: 5 taxa, four
      rooted trees with nontrivial clusters {1,2},{2,3},{3,4},{4,5}; P7 forces
      the output to display (12)5, (23)5, (34)1, (45)1 simultaneously, which no
      rooted tree can do.
      Lean counterpart:
        Phylo/SupertreeLimits.lean  SBD.no_rootedTree_displays_four_triplets

Labels 1..n here correspond to `Fin n` indices 0..n-1 in the Lean file.
Pure standard library.  Exits non-zero if any check fails.
"""

import itertools
import sys

FAIL = []
LABELS = frozenset()


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------
# 1. rooted trees on a finite label set, as nested structures
# --------------------------------------------------------------------------
def _partitions(S):
    """All set partitions of S into non-empty blocks (tuples of frozensets)."""
    S = tuple(sorted(S))
    if not S:
        yield ()
        return
    first, rest = S[0], S[1:]
    for k in range(1, len(S) + 1):
        for extra in itertools.combinations(rest, k - 1):
            block = frozenset((first,) + extra)
            others = [x for x in S if x not in block]
            for sub in _partitions(others):
                yield (block,) + sub


def rooted_trees(S):
    """All rooted trees with leaf set S; every internal node has >= 2 children."""
    S = tuple(sorted(S))
    if len(S) == 1:
        yield ('leaf', S[0])
        return
    first, rest = S[0], S[1:]
    for k in range(1, len(rest) + 1):
        for extra in itertools.combinations(rest, k - 1):
            block = frozenset((first,) + extra)
            others = [x for x in S if x not in block]
            for part in _partitions(others):
                blocks = (block,) + part
                if len(blocks) < 2:
                    continue
                for combo in itertools.product(*[list(rooted_trees(b)) for b in blocks]):
                    yield ('node', combo)


def node_leaves(t):
    if t[0] == 'leaf':
        return frozenset((t[1],))
    out = frozenset()
    for c in t[1]:
        out |= node_leaves(c)
    return out


def clades(t, top=True):
    """Clade family = leaf sets of all non-root nodes."""
    if t[0] == 'leaf':
        return []
    res = []
    if not top:
        res.append(node_leaves(t))
    for c in t[1]:
        res.extend(clades(c, top=False))
    return res


def rooted_signature(t):
    return frozenset(clades(t, top=True))


def all_rooted_trees(X):
    seen = {}
    for t in rooted_trees(X):
        seen.setdefault(rooted_signature(t), t)
    return list(seen.keys())


def splits_of_clades(cl):
    """Unrooted split system (nontrivial splits only) of the unrooted tree."""
    sp = set()
    for C in cl:
        comp = LABELS - C
        if len(C) >= 2 and len(comp) >= 2:
            sp.add(frozenset((C, comp)))
    return frozenset(sp)


def displays_triplet(cl, pair, out):
    return any(pair <= C and out not in C for C in cl)


def displays_quartet(splits, a, b, c, d):
    for s in splits:
        A, B = tuple(s)
        for X, Y in ((A, B), (B, A)):
            if {a, b} <= X and {c, d} <= Y:
                return True
    return False


def main():
    global LABELS

    # ======================= Part I : rooted, Prop. 3 ======================
    print("=" * 74)
    print("Part I -- rooted trees, 5 taxa   (Prop. 3: lines 300-306, 312-315)")
    print("=" * 74)
    X5 = tuple(range(1, 6))
    LABELS = frozenset(X5)
    rooted = all_rooted_trees(X5)
    print("  rooted trees on 5 labelled taxa (every internal node >= 2 children) : %d"
          % len(rooted))
    check("enumeration covers all binary rooted trees (((2n-3)!! = 105))",
          len(rooted) >= 105)

    wanted = [(frozenset((1, 2)), 5), (frozenset((2, 3)), 5),
              (frozenset((3, 4)), 1), (frozenset((4, 5)), 1)]
    names = ["(12)5", "(23)5", "(34)1", "(45)1"]
    inputs = [[pair] + [frozenset((x,)) for x in X5] for pair, _ in wanted]
    print("  the four input trees of Figure 2 (one nontrivial clade each) :",
          [sorted(p) for p, _ in wanted])
    for i, (pair, out) in enumerate(wanted):
        check("input tree %d displays %s" % (i + 1, names[i]),
              displays_triplet(inputs[i], pair, out))

    for i, (pair, out) in enumerate(wanted):
        a, b = sorted(pair)
        bad = []
        for cl in inputs:
            for (p, o) in ((frozenset((a, out)), b), (frozenset((b, out)), a)):
                if displays_triplet(cl, p, o):
                    bad.append((sorted(p), o))
        check("P7 side condition for %s: no input tree displays a competitor %s"
              % (names[i], bad), bad == [])

    survivors = [cl for cl in rooted
                 if all(displays_triplet(cl, p, o) for (p, o) in wanted)]
    print("  rooted trees displaying all four triplets : %d" % len(survivors))
    check("NO rooted tree on 5 taxa displays (12)5,(23)5,(34)1,(45)1 together "
          "[Lean: SBD.no_rootedTree_displays_four_triplets]", len(survivors) == 0)

    print("  non-vacuity -- how many k-subsets of the four triplets ARE realisable:")
    for k in range(1, 5):
        subsets = list(itertools.combinations(range(4), k))
        cnt = sum(1 for combo in subsets
                  if any(all(displays_triplet(cl, *wanted[j]) for j in combo)
                         for cl in rooted))
        print("      k=%d : %d/%d" % (k, cnt, len(subsets)))
    check("every 3-subset of the four forced triplets is realisable "
          "(so the failure is genuinely the 4-fold conjunction)",
          all(any(all(displays_triplet(cl, *wanted[j]) for j in combo) for cl in rooted)
              for combo in itertools.combinations(range(4), 3)))

    # ===================== Part II : unrooted, Prop. 1 =====================
    print()
    print("=" * 74)
    print("Part II -- unrooted trees, 6 taxa  (Prop. 1: lines 97-100, 101-147)")
    print("=" * 74)
    X6 = tuple(range(1, 7))
    LABELS = frozenset(X6)
    trees = {}
    for t in rooted_trees(X6):
        trees.setdefault(splits_of_clades(rooted_signature(t)), t)
    print("  unrooted trees (nontrivial split systems) on 6 labelled taxa : %d"
          % len(trees))

    Q = [((1, 2), (4, 5)), ((3, 4), (1, 6)), ((5, 6), (2, 3))]
    qnames = ["(12)(45)", "(34)(16)", "(56)(23)"]
    parents = [sp for sp in trees
               if all(displays_quartet(sp, a, b, c, d) for (a, b), (c, d) in Q)]
    print("  parent trees of {(12)(45),(34)(16),(56)(23)} : %d" % len(parents))
    for sp in parents:
        print("      splits :", sorted(sorted(tuple(sorted(s))) for s in sp))
    check("exactly two parent trees (Figure 1)", len(parents) == 2)

    sigma = {1: 1, 2: 6, 3: 5, 4: 4, 5: 3, 6: 2}

    def act_split(s):
        return frozenset(frozenset(sigma[x] for x in part) for part in s)

    def act(sps):
        return frozenset(act_split(s) for s in sps)

    def act_q(q):
        return frozenset(frozenset(sigma[x] for x in p) for p in q)

    input_set = frozenset(frozenset((frozenset(p), frozenset(q))) for p, q in Q)
    check("sigma = (2 6)(3 5) fixes the unordered input quartet set "
          "[Lean: SBD.prof_relabel]", frozenset(act_q(q) for q in input_set) == input_set)

    moved = [act(sp) for sp in parents]
    check("sigma swaps the two parent trees",
          len(parents) == 2 and set(moved) == set(parents)
          and all(moved[i] != parents[i] for i in range(len(parents))))

    fixed = [sp for sp in parents if act(sp) == sp]
    check("NO parent tree is sigma-invariant  ==>  every P1+P2+P3 method dies",
          fixed == [])

    # the STRONGER fact actually used in the Lean proof: only TWO of the three
    # quartets are needed.
    q13 = [Q[0], Q[2]]
    inv_q13 = [sp for sp in trees
               if act(sp) == sp
               and all(displays_quartet(sp, a, b, c, d) for (a, b), (c, d) in q13)]
    print("  sigma-invariant trees displaying BOTH (12)(45) and (56)(23) : %d"
          % len(inv_q13))
    check("NO sigma-invariant tree displays (12)(45) and (56)(23) together "
          "[Lean: SBD.no_invariant_tree_displays_two_quartets]", inv_q13 == [])

    def compat(s, t):
        A, B = tuple(s)
        C, D = tuple(t)
        return (A <= C) or (A <= D) or (B <= C) or (B <= D)

    ok = all(compat(s, t) for sp in parents for s in sp for t in sp)
    check("every parent tree has a pairwise-compatible split system", ok)

    # anti-vacuity: a sigma-invariant tree displaying ONE of them does exist,
    # and a parent tree (non-invariant) exists -- so the obstruction is real.
    inv_one = [sp for sp in trees if act(sp) == sp
               and displays_quartet(sp, 1, 2, 4, 5)]
    check("anti-vacuity: sigma-invariant trees displaying (12)(45) alone DO exist "
          "(%d of them)" % len(inv_one), len(inv_one) > 0)
    check("anti-vacuity: parent trees (displaying all three) DO exist (%d)"
          % len(parents), len(parents) > 0)

    # the three input trees are indeed compatible (they have parents)
    print("  parent trees are the witnesses that the input set is COMPATIBLE "
          "==> P3 is not vacuous  [Lean: SBD.prof_compatible]")

    print()
    if FAIL:
        print("FAILED CHECKS (%d): %s" % (len(FAIL), FAIL))
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
