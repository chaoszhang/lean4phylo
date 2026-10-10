#!/usr/bin/env python3
# W12e2 ★D/★C check: does the "cherry convex-merge" lemma hold?
#   claim:  δ.FourPoint  ∧  δ.IsCherry i j  ==>
#           for a,b,c not in {i,j} and theta in [0,1]:
#             f a + δ b c  ≤  (f b + δ a c)   OR   (f c + δ a b)      (*)
#           where f x = theta*δ x i + (1-theta)*δ x j.
# Part A: exhaustive over 5-leaf tree metrics (all binary topologies with cherry {i,j},
#         plus the star), rational edge weights from a grid, theta from a grid.
# Part B: exhaustive over 5-point integer metrics with entries in {1,2,3} (symmetry + zero
#         diagonal), checking whether FourPoint + IsCherry(i,j) *alone* imply (*).
# Exact rational arithmetic only (fractions.Fraction); no Monte Carlo.
import sys, itertools
from fractions import Fraction as F

N = 5
IDX = list(range(N))  # 0=i, 1=j, 2=a, 3=b, 4=c ; vertices 5,6,7 internal


def check_fp(d):
    """FourPoint: max of the three pair-sums attained twice (disjunction form)."""
    for i, j, k, l in itertools.permutations(range(len(d)), 4):
        s1 = d[i][j] + d[k][l]
        s2 = d[i][k] + d[j][l]
        s3 = d[i][l] + d[j][k]
        if not (s1 <= s2 or s1 <= s3):
            return False
    return True


def is_cherry(d, a, b):
    n = len(d)
    if a == b:
        return False
    for k in range(n):
        if k == a or k == b:
            continue
        for l in range(n):
            if l == a or l == b:
                continue
            if not (d[a][b] + d[k][l] <= d[a][k] + d[b][l]):
                return False
            if not (d[a][b] + d[k][l] <= d[a][l] + d[b][k]):
                return False
    return True


def merged_ok(d, i, j, theta):
    """(*) for all ordered triples (a,b,c) of distinct indices outside {i,j}."""
    n = len(d)
    others = [x for x in range(n) if x != i and x != j]
    f = lambda x: theta * d[x][i] + (1 - theta) * d[x][j]
    for a, b, c in itertools.permutations(others, 3):
        lhs = f(a) + d[b][c]
        if not (lhs <= f(b) + d[a][c] or lhs <= f(c) + d[a][b]):
            return (a, b, c, lhs, f(b) + d[a][c], f(c) + d[a][b])
    return None


# ---------- tree metrics on 5 labelled leaves ----------
# tree 1: cherry (i,j) and cherry (a,b), plus c  -> edges
# tree 2: cherry (i,j), then (c,a) cherry
# tree 3: cherry (i,j), then (b,c) cherry
# tree 4: cherry (i,j) with a,b,c in a caterpillar  ((i,j),a),(.,b)),(.,c)
# tree 5: star with center, cherry (i,j) is then NOT a cherry -> excluded from A2 but kept for A1
TREES = {
    'bal_ij_ab_c': [(0, 5, 'p0'), (1, 5, 'p1'), (2, 6, 'p2'), (3, 6, 'p3'), (4, 7, 'p4'),
                    (5, 7, 'e57'), (6, 7, 'e67')],
    'bal_ij_ca_b': [(0, 5, 'p0'), (1, 5, 'p1'), (2, 6, 'p2'), (4, 6, 'p4'), (3, 7, 'p3'),
                    (5, 7, 'e57'), (6, 7, 'e67')],
    'cater_ij_a_b_c': [(0, 5, 'p0'), (1, 5, 'p1'), (2, 5, 'p2'), (5, 6, 'e56'), (3, 6, 'p3'),
                       (6, 7, 'e67'), (4, 7, 'p4')],
    'star': [(0, 5, 'p0'), (1, 5, 'p1'), (2, 5, 'p2'), (3, 5, 'p3'), (4, 5, 'p4')],
}


def tree_metric(edges, weights, nv=8):
    import collections
    adj = collections.defaultdict(list)
    for (u, v, key) in edges:
        w = weights[key]
        adj[u].append((v, w))
        adj[v].append((u, w))
    out = [[F(0)] * N for _ in range(N)]
    for s in range(N):
        dist = {s: F(0)}
        stack = [s]
        while stack:
            x = stack.pop()
            for (y, w) in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + w
                    stack.append(y)
        for t in range(N):
            out[s][t] = dist[t]
    return out


def part_a():
    grid = [F(1), F(2), F(3), F(1, 2), F(3, 2)]
    thetas = [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]
    bad = 0
    checked = 0
    for name, edges in TREES.items():
        keys = [k for (_, _, k) in edges]
        for combo in itertools.product(grid, repeat=len(keys)):
            w = dict(zip(keys, combo))
            d = tree_metric(edges, w)
            if not check_fp(d):
                print('!! tree metric fails FourPoint (bug):', name, combo); bad += 1; continue
            ch = is_cherry(d, 0, 1)
            for th in thetas:
                r = merged_ok(d, 0, 1, th)
                checked += 1
                if r is not None:
                    print('!! A FAIL', name, combo, 'theta=', th, 'cherry=', ch, r)
                    bad += 1
                    if bad > 5:
                        return checked, bad
    return checked, bad


def part_b(vals=(1, 2, 3)):
    """Abstract search: symmetric, zero diagonal, FourPoint, IsCherry(0,1) => (*)?"""
    pairs = list(itertools.combinations(range(N), 2))
    tested = 0
    cherr = 0
    counter = 0
    thetas = [F(1, 2), F(1, 4), F(3, 4), F(1, 3)]
    for combo in itertools.product(vals, repeat=len(pairs)):
        d = [[F(0)] * N for _ in range(N)]
        for (p, v) in zip(pairs, combo):
            d[p[0]][p[1]] = F(v)
            d[p[1]][p[0]] = F(v)
        tested += 1
        if not check_fp(d):
            continue
        if not is_cherry(d, 0, 1):
            continue
        cherr += 1
        for th in thetas:
            r = merged_ok(d, 0, 1, th)
            if r is not None:
                counter += 1
                if counter <= 10:
                    print('B COUNTEREXAMPLE theta=', th, 'd(0,1)=', d[0][1], 'vals=',
                          {f'{p[0]}{p[1]}': int(d[p[0]][p[1]]) for p in pairs}, 'witness=', r)
                break
    return tested, cherr, counter


if __name__ == '__main__':
    print('== Part A: 5-leaf tree metrics (exhaustive over topologies x weight grid x theta) ==')
    ck, bad = part_a()
    print(f'A: checked={ck} failures={bad}')
    print('== Part B: abstract metrics, entries in {1,2,3}, symmetry+diag+FourPoint+IsCherry(0,1) ==')
    t, c, k = part_b()
    print(f'B: enumerated={t} satisfying FourPoint&IsCherry={c} counterexamples={k}')
    sys.exit(1 if bad else 0)
