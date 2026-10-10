#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11h / C5 -- n-tree consensus functions: exhaustive small-scale replication.

Reference: F. R. McMorris & D. Neumann, "Consensus functions defined on trees",
Math. Social Sci. 4(2) (1983) 131-136.
Line numbers below refer to references/md/McMorrisNeumann1983_ConsensusFunctionsTrees.md

  * n-tree (lines 294-302): a set T of subsets of S with  S in T,  empty not in T,
      {x} not in T,  and  X n Y in {empty, X, Y};  the trivial n-tree is the empty set.
      Modelled here (and in Lean) by the CLUSTER FAMILY of proper non-singleton subsets,
      i.e. by pairwise laminar families of clusters.
  * consensus function (306): C : T^k -> T.
  * axioms (308-334): (N) neutral, (M) monotone, (P) Pareto, (coP) co-Pareto,
      (S) symmetric, (A) autonomous;  (348-355): (M) and (N)  <=>  (MN), and
      (MN) + (A)  =>  (P).
  * Theorem 2 (362-419): C satisfies (MN) and (A)  <=>  C = M_D for a decisive family D,
      where  X in M_D(P)  <=>  {i : X in T_i} in D.
  * Corollary (429-436): C satisfies (MN), (A) and (S)  <=>  C = M_t (threshold rule);
      "since no two decisive sets can be disjoint, t > k/2".

Lean counterparts (Phylo/ConsensusAxioms.lean, namespace NTreeConsensus):
    IsCluster / IsNTree / Profile / ConsensusFn / support
    Pareto / CoPareto / Monotone / MNSet / MNCard / Symmetric / Autonomous /
        NTreeValued / ClusterValued / ThresholdRule / twoClusterProfile
    thresholdRule_pareto / _coPareto / _monotone / _mnSet / _mnCard / _symmetric /
        _autonomous                      (the rule satisfies the axioms)
    thresholdRule_isNTree                (k < 2t  =>  n-tree valued: MAJORITY works)
    thresholdRule_not_isNTree_of_le      (2t <= k  =>  NOT n-tree valued)
    no_weakmajority_threshold_isNTree    (Fin 4, k = 2, t = 1: impossibility)
    eq_decisiveRule_of_mnSet / mnSet_decisiveRule   (Theorem 2 core)

Pure standard library (itertools only) -- exact, no Monte Carlo, no floating point.
Labels 0..n-1 here are `Fin n` indices in the Lean file.
Exits non-zero if any check fails.
"""

import itertools
import sys

FAIL = []


def check(name, cond):
    print(("  [OK]   " if cond else "  [FAIL] ") + name)
    if not cond:
        FAIL.append(name)


# --------------------------------------------------------------------------
# clusters, n-trees, threshold rule
# --------------------------------------------------------------------------
def clusters(n):
    """Non-trivial clusters of {0..n-1}: size 2..n-1 (the proper non-singletons)."""
    return [frozenset(c) for r in range(2, n) for c in itertools.combinations(range(n), r)]


def laminar(a, b):
    i = a & b
    return i == frozenset() or i == a or i == b


def is_ntree(fam):
    return all(laminar(a, b) for a in fam for b in fam)


def all_ntrees(n):
    """All n-trees on {0..n-1} (DFS with laminarity pruning), including the empty one."""
    cl = sorted(clusters(n), key=lambda c: (len(c), sorted(c)))
    res = []

    def rec(i, cur):
        if i == len(cl):
            res.append(frozenset(cur))
            return
        rec(i + 1, cur)
        if all(laminar(cl[i], x) for x in cur):
            cur.append(cl[i])
            rec(i + 1, cur)
            cur.pop()

    rec(0, [])
    return res


def support(prof, X):
    return frozenset(i for i, T in enumerate(prof) if X in T)


def threshold_rule(prof, t):
    cl = set()
    for T in prof:
        cl |= set(T)
    return frozenset(X for X in cl if len(support(prof, X)) >= t)


def crossing(a, b):
    return not laminar(a, b)


def bounded_profiles(nt, k, cap):
    """All k-tuples of n-trees, or a deterministic prefix if there are more than `cap`."""
    tot = len(nt) ** k
    if tot <= cap:
        return list(itertools.product(nt, repeat=k)), True
    out = []
    for idx, tup in enumerate(itertools.product(nt, repeat=k)):
        out.append(tup)
        if len(out) >= cap:
            break
    return out, False


def part_one():
    print("=" * 74)
    print("Part I -- the domain: n-trees on 4 and 5 leaves")
    print("=" * 74)
    for n in (4, 5):
        cl, nt = clusters(n), all_ntrees(n)
        check("n=%d: %d clusters, %d n-trees (incl. the trivial empty one); all laminar"
              % (n, len(cl), len(nt)), all(is_ntree(T) for T in nt))
    return all_ntrees(4), all_ntrees(5)


def part_two(nt4):
    print()
    print("=" * 74)
    print("Part II -- threshold rule vs the axioms (4 leaves)")
    print("=" * 74)
    for k in (2, 3):
        profs, exact = bounded_profiles(nt4, k, 20000)
        print("  k=%d: %d n-tree profiles (%s)" % (k, len(profs),
                                                   "exhaustive" if exact else "prefix"))
        allcl = set()
        for prof in profs:
            for T in prof:
                allcl |= set(T)
        for t in range(1, k + 1):
            bad_p = bad_cop = bad_m = bad_mn = 0
            supp_mem = {}
            for prof in profs:
                out = threshold_rule(prof, t)
                for X in allcl:
                    s = support(prof, X)
                    mem = X in out
                    # (P) Pareto: full support => member;   (coP): member => nonempty support
                    if len(s) == k and not mem:
                        bad_p += 1
                    if mem and not s:
                        bad_cop += 1
                    # (MN): membership is a function of the support set
                    if s in supp_mem and supp_mem[s] != mem:
                        bad_mn += 1
                    supp_mem.setdefault(s, mem)
                    # (M): monotone in the support set (both directions)
                    if mem and any(s <= s2 and not m2 for s2, m2 in supp_mem.items()):
                        bad_m += 1
                    if not mem and any(s2 <= s and m2 for s2, m2 in supp_mem.items()):
                        bad_m += 1
            # (A) autonomous: every cluster is selected by some n-tree profile
            bad_auto = sum(1 for X in clusters(4)
                           if not any(X in threshold_rule(prof, t) for prof in profs))
            check("k=%d t=%d: (P) Pareto, (coP) co-Pareto, (M) monotone, (MN), (A) "
                  "autonomous all hold" % (k, t),
                  bad_p == bad_cop == bad_m == bad_mn == bad_auto == 0)
        bad_s = 0
        for prof in profs[:150]:
            for t in range(1, k + 1):
                base = threshold_rule(prof, t)
                for perm in itertools.permutations(range(k)):
                    if threshold_rule(tuple(prof[i] for i in perm), t) != base:
                        bad_s += 1
        check("k=%d: (S) symmetric on %d profiles x k! permutations"
              % (k, min(len(profs), 150)), bad_s == 0)


def part_three(nt4):
    print()
    print("=" * 74)
    print("Part III -- n-tree valuedness:  k < 2t works,  2t <= k fails")
    print("=" * 74)
    for k in (2, 3, 4):
        profs, exact = bounded_profiles(nt4, k, 20000)
        for t in range(1, k + 1):
            viol = [prof for prof in profs if not is_ntree(threshold_rule(prof, t))]
            tag = "" if exact else " (prefix of the profile space)"
            if k < 2 * t:
                check("k=%d t=%d (strict majority, k < 2t): output is ALWAYS an n-tree%s "
                      "[Lean: thresholdRule_isNTree]" % (k, t, tag), viol == [])
            else:
                check("k=%d t=%d (2t <= k): output is NOT always an n-tree -- %d "
                      "violating profiles  [Lean: noWeakmajorityThreshold_isNTree]"
                      % (k, t, len(viol)), len(viol) > 0)
                if viol:
                    prof = min(viol, key=lambda p: sum(len(T) for T in p))
                    out = threshold_rule(prof, t)
                    cross = [(a, b) for a in out for b in out if crossing(a, b)]
                    print("      witness profile: %s"
                          % [sorted(sorted(c) for c in T) for T in prof])
                    print("      output %s is NOT laminar (crossing pair %s)"
                          % (sorted(sorted(c) for c in out),
                             [(sorted(a), sorted(b)) for a, b in cross[:1]]))
    # the minimal concrete example of the Lean theorem (Fin 4, k = 2, t = 1)
    X, Y = frozenset((0, 1)), frozenset((0, 2))
    prof = (frozenset([X]), frozenset([Y]))
    out = threshold_rule(prof, 1)
    check("Fin 4 minimal witness: profile ({01}, {02}), k=2, t=1 -> output {%s, %s}, "
          "which is NOT laminar" % (sorted(X), sorted(Y)),
          out == frozenset([X, Y]) and crossing(X, Y))


def part_four(nt4):
    print()
    print("=" * 74)
    print("Part IV -- Theorem 2 / Corollary: decisive family and the threshold shape")
    print("=" * 74)
    k = 3
    profs, exact = bounded_profiles(nt4, k, 20000)
    for t in (1, 2, 3):
        fam = set()
        for prof in profs:
            for X in threshold_rule(prof, t):
                fam.add(support(prof, X))
        expected = set(frozenset(D) for r in range(k + 1)
                       for D in itertools.combinations(range(k), r) if len(D) >= t)
        check("k=%d t=%d: decisive family of the rule is contained in {D : |D| >= t}, and "
              "the full support K is realised (Corollary, lines 429-436)%s"
              % (k, t, "" if exact else " [prefix]"),
              fam <= expected and frozenset(range(k)) in fam)
        disj = [(a, b) for a in fam for b in fam if a & b == frozenset() and a != b]
        if k < 2 * t:
            check("k=%d t=%d: NO two decisive sets are disjoint (this is exactly t > k/2)"
                  % (k, t), disj == [])
        else:
            check("k=%d t=%d: disjoint decisive sets DO exist (2t <= k) -- the source of "
                  "the laminarity obstruction" % (k, t), len(disj) > 0)


def part_five(nt4, nt5):
    print()
    print("=" * 74)
    print("Part V -- 5 leaves: anti-vacuity of the 4-leaf exhaustive results")
    print("=" * 74)
    profs, exact = bounded_profiles(nt5, 2, 20000)
    print("  5 leaves: %d n-trees, %d profiles checked (%s)"
          % (len(nt5), len(profs), "exhaustive" if exact else "prefix"))
    viol = [p for p in profs if not is_ntree(threshold_rule(p, 1))]
    okv = [p for p in profs if is_ntree(threshold_rule(p, 2))]
    check("5 leaves, k=2: t=1 fails on %d profiles while t=2 (strict majority) holds on "
          "all %d checked" % (len(viol), len(profs)),
          len(viol) > 0 and len(okv) == len(profs))
    # n-trees of 5 leaves really do attain crossing clusters (the Fin-4 witness is not an
    # artefact of having only 4 leaves)
    X, Y = frozenset((0, 1)), frozenset((0, 2))
    prof = (frozenset([X]), frozenset([Y]))
    check("5-leaf witness: ({01}, {02}) with k=2, t=1 also fails here",
          not is_ntree(threshold_rule(prof, 1)))


def main():
    nt4, nt5 = part_one()
    part_two(nt4)
    part_three(nt4)
    part_four(nt4)
    part_five(nt4, nt5)
    print()
    if FAIL:
        print("FAILED CHECKS (%d): %s" % (len(FAIL), FAIL))
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
