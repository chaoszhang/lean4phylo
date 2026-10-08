#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/kingman_check.py -- W9 / G5' 的**协调侧独立数值复核**

Purpose: derive the mathematical claims that `Phylo/Stat/MSCKingman.lean` must
implement, by **exhaustive enumeration of 4-leaf Kingman coalescent histories**
(not by trusting the verbal argument, not by Monte Carlo):

  (A1) If NEITHER cherry ({a,b}, {c,d}) coalesces below the root, then 4 lineages
       enter the root population, and the three unrooted topologies are
       **equally likely (1/3 each)**.
  (A2) If AT LEAST ONE cherry coalesces below the root, the unrooted topology is
       forced to be `ab|cd` (point mass).
  (A3) Hence P(concordant) = 1 - (2/3)e^{-t}, agreeing **verbatim** with the
       library's `Coalescent.pConcordant`; each discordant topology gets (1/3)e^{-t}.

Model (coalescent units; the root cuts the internal edge into a ({a,b} side) and
b ({c,d} side), with t = a + b):
  * {a,b} coalesces below the root with prob p_a = 1 - e^{-a};   survives with e^{-a};
  * {c,d} likewise with p_b = 1 - e^{-b};
  * then the root population follows Kingman: each step picks a uniformly random
    pair of extant lineages to merge.

Node ids: a single leaf is its own letter; any cluster is the pair ('N', leafset),
so a node always knows which leaves it carries.

Usage: python kingman_check.py
"""
import itertools
import math
import sys

LEAVES = ('a', 'b', 'c', 'd')
TOPOS = ('ab|cd', 'ac|bd', 'ad|bc')


def node_id(leafset):
    """A single leaf is its own name; a cluster is ('N', leafset)."""
    if len(leafset) == 1:
        return next(iter(leafset))
    return ('N', leafset)


def leaves_of(node):
    """Leaves carried by a node id."""
    if isinstance(node, str):
        return frozenset((node,)) if node in LEAVES else frozenset()
    return node[1]


# ---------------------------------------------------------------- topology
def split_of(history):
    """history = [(node_i, node_j, new_node), ...] -> the unique nontrivial split
    of the induced unrooted 4-leaf tree, as frozenset({frozenset, frozenset})."""
    adj = {}

    def touch(u):
        adj.setdefault(u, set())

    root = None
    for (x, y, z) in history:
        touch(x); touch(y); touch(z)
        adj[x].add(z); adj[z].add(x)
        adj[y].add(z); adj[z].add(y)
    # `merge_sequences` yields the **innermost** (earliest in time) merge first,
    # so the root is history[-1][2].
    root = history[-1][2]

    # root has degree 2 -> suppress it in the unrooted tree
    if len(adj[root]) == 2:
        u, v = tuple(adj[root])
        adj[u].discard(root); adj[v].discard(root)
        adj[u].add(v);        adj[v].add(u)
        del adj[root]

    edges = set()
    for u in adj:
        for v in adj[u]:
            edges.add(frozenset((u, v)))

    # The graph's leaves are exactly the letter nodes (every cluster node is a
    # `('N', leafset)` tuple and always has degree >= 2).  NB: we must NOT use a
    # cluster's own leafset here -- a connected component may cover only part of
    # that cluster.
    # Dedupe: removing an undirected edge is discovered from both endpoints.
    nontrivial = set()
    for e in edges:
        u, v = tuple(e)
        seen = {v}
        stack = [v]
        while stack:
            w = stack.pop()
            for nxt in adj[w]:
                if nxt == u or nxt in seen:
                    continue
                seen.add(nxt)
                stack.append(nxt)
        side = frozenset(x for x in seen if x in LEAVES)
        other = frozenset(LEAVES) - side
        # `edges` is a set, so each undirected edge is visited in ONE arbitrary
        # orientation -> check the complement side as well.
        if len(side) == 2:
            nontrivial.add(frozenset((side, other)))
        elif len(other) == 2:
            nontrivial.add(frozenset((other, side)))
    if len(nontrivial) != 1:
        raise AssertionError("nontrivial split not unique: %r (history=%r)"
                             % (sorted(nontrivial), history))
    return next(iter(nontrivial))


def topo_of_split(sp):
    """Map {i,j}|{k,l} to the Topo name used by the Lean library."""
    sides = sorted(tuple(sorted(s)) for s in sp)
    table = {
        (('a', 'b'), ('c', 'd')): 'ab|cd',
        (('a', 'c'), ('b', 'd')): 'ac|bd',
        (('a', 'd'), ('b', 'c')): 'ad|bc',
    }
    key = tuple(sides)
    if key not in table:
        raise AssertionError("unrecognised split: %r" % (key,))
    return table[key]


# ---------------------------------------------------------------- enumeration
def merge_sequences(items):
    """items = [(leafset, node_id), ...] -> all equally likely merge sequences."""
    if len(items) == 1:
        yield [], items[0][1]
        return
    for i, j in itertools.combinations(range(len(items)), 2):
        rest = [it for k, it in enumerate(items) if k not in (i, j)]
        merged_leaves = items[i][0] | items[j][0]
        newid = node_id(merged_leaves)
        for tail, _top in merge_sequences(rest + [(merged_leaves, newid)]):
            yield [(items[i][1], items[j][1], newid)] + tail, newid


def count_sequences(k):
    n = 1
    while k > 1:
        n *= k * (k - 1) // 2
        k -= 1
    return n


def window_setup(ab_merged, cd_merged):
    """Return (prefix_history, root_items).

    `prefix_history` records the coalescences that happened **below the root**
    (inside the two window populations) as real merge events, so that the leaves
    `a`, `b`, `c`, `d` are genuine nodes of the induced tree.
    `root_items` are the lineages entering the root population.
    """
    prefix = []
    items = []
    for (x, y, merged) in (('a', 'b', ab_merged), ('c', 'd', cd_merged)):
        fs = frozenset((x, y))
        if merged:
            prefix.append((x, y, node_id(fs)))
            items.append((fs, node_id(fs)))
        else:
            items += [(frozenset((x,)), x), (frozenset((y,)), y)]
    return prefix, items


def conditional_probs(ab_merged, cd_merged):
    """Topology distribution **conditioned on** the two window events."""
    prefix, items = window_setup(ab_merged, cd_merged)
    total = count_sequences(len(items))
    acc = {T: 0.0 for T in TOPOS}
    n = 0
    for hist, _ in merge_sequences(items):
        acc[topo_of_split(split_of(prefix + hist))] += 1.0 / total
        n += 1
    assert n == total, (n, total)
    return acc


def topology_probs(a, b):
    """Unconditional exact topology distribution for window lengths a, b."""
    pa = 1.0 - math.exp(-a)
    pb = 1.0 - math.exp(-b)
    acc = {T: 0.0 for T in TOPOS}
    for ab_m, cd_m, w in ((True, True, pa * pb),
                          (True, False, pa * (1 - pb)),
                          (False, True, (1 - pa) * pb),
                          (False, False, (1 - pa) * (1 - pb))):
        if w == 0.0:
            continue
        cond = conditional_probs(ab_m, cd_m)
        for T in TOPOS:
            acc[T] += w * cond[T]
    return acc


# ---------------------------------------------------------------- checks
def main():
    worst = 0.0
    print("cfg                 P(ab|cd)        P(ac|bd)        P(ad|bc)        | residuals")
    for t in (0.0, 0.05, 0.1, 0.3, 0.5, 1.0, 2.0, 5.0, 10.0):
        for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
            a, b = t * frac, t * (1 - frac)
            acc = topology_probs(a, b)
            conc = 1.0 - (2.0 / 3.0) * math.exp(-t)
            disc = (1.0 / 3.0) * math.exp(-t)
            r = (abs(acc['ab|cd'] - conc), abs(acc['ac|bd'] - disc),
                 abs(acc['ad|bc'] - disc), abs(sum(acc.values()) - 1.0))
            worst = max(worst, max(r))
            print("t=%-5.2f a/t=%-4.2f  %.12f  %.12f  %.12f  | %.2e %.2e %.2e  (sum=%.15f)"
                  % (t, frac, acc['ab|cd'], acc['ac|bd'], acc['ad|bc'],
                     r[0], r[1], r[2], sum(acc.values())))
    print()
    print("max residual vs 1-(2/3)e^-t and (1/3)e^-t : %.3e" % worst)

    print()
    print("=== (A1) neither cherry coalesced below root  =>  uniform (1/3, 1/3, 1/3) ===")
    okA1 = True
    for (a, b) in ((0.7, 0.3), (1.3, 2.1), (5.0, 5.0), (0.0, 0.0)):
        cond = conditional_probs(False, False)
        print("  a=%-4.2f b=%-4.2f  conditional P = (%.15f, %.15f, %.15f)"
              % (a, b, cond['ab|cd'], cond['ac|bd'], cond['ad|bc']))
        okA1 = okA1 and all(abs(cond[T] - 1.0 / 3.0) < 1e-15 for T in TOPOS)

    print()
    print("=== (A2) exactly one cherry coalesced below root  =>  ab|cd forced ===")
    okA2 = True
    for (ab_m, cd_m) in ((True, False), (False, True)):
        cond = conditional_probs(ab_m, cd_m)
        print("  (ab_merged=%-5s cd_merged=%-5s) -> %s"
              % (ab_m, cd_m, {k: round(v, 15) for k, v in cond.items()}))
        okA2 = okA2 and abs(cond['ab|cd'] - 1.0) < 1e-15

    print()
    print("=== (A3) 6 first-merge pairs -> 3 classes of exactly 2 ===")
    classes = {}
    for i, j in itertools.combinations(range(4), 2):
        li, lj = LEAVES[i], LEAVES[j]
        items = [(frozenset((x,)), x) for x in LEAVES if x not in (li, lj)]
        first_leafset = frozenset((li, lj))
        first = node_id(first_leafset)
        total = count_sequences(3)
        n = 0
        topos = set()
        for hist, _ in merge_sequences(items + [(first_leafset, first)]):
            full = [(li, lj, first)] + hist
            topos.add(topo_of_split(split_of(full)))
            n += 1
        assert n == total == 3, (n, total)
        # the induced topology does not depend on the later merges -> record the
        # first-merge pair exactly ONCE per topology it can produce (which here
        # is a single topology, since 3 lineages admit only one unrooted shape)
        assert len(topos) == 1, (li, lj, topos)
        classes.setdefault(next(iter(topos)), []).append((li, lj))
    okA3 = True
    for T in TOPOS:
        got = sorted(classes.get(T, []))
        print("  %-6s : %d pairs  %s" % (T, len(got), got))
        okA3 = okA3 and (len(got) == 2)
    print("  every class has exactly 2 pairs =", okA3)

    print()
    print("=== algebraic reconciliation with `Coalescent.pConcordant` ===")
    worst2 = 0.0
    for i in range(0, 201):
        t = i * 0.05
        lhs = (1 - math.exp(-t)) + (1.0 / 3.0) * math.exp(-t)
        rhs = 1 - (2.0 / 3.0) * math.exp(-t)
        worst2 = max(worst2, abs(lhs - rhs))
    print("  max |(1-e^-t)+(1/3)e^-t - (1-(2/3)e^-t)| = %.3e" % worst2)

    verdict = (worst < 1e-12) and okA1 and okA2 and okA3 and (worst2 < 1e-15)
    print()
    print("VERDICT:", "PASS" if verdict else "FAIL")
    return 0 if verdict else 1


if __name__ == '__main__':
    sys.exit(main())
