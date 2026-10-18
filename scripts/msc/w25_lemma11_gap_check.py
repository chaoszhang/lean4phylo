#!/usr/bin/env python3
"""W25 泳道 b ★D 命题核查：`atteson_lemma11_gap` 到底真还是假？

命题（`Phylo/AttesonRadius.lean` §8 的 `def atteson_lemma11_gap`）：
  δ.FourPoint → δ.PositiveDefinite → 4 ≤ |X| → ∃ δmin > 0, δ.IsCherrySeparated δmin

判定化：`∃ δmin > 0, IsCherrySeparated δ δmin` 成立 **⟺** 每个非樱桃对 (k,l) 都存在
形态合格的樱桃 (i,j)，使
    DisjointPairs i j k l    且  Q(k,l) − Q(i,j) ≥ 3(n−4)·δmin
    SharesOneLabel i j k l   且  Q(k,l) − Q(i,j) ≥ 2(n−3)·δmin
注意 n = 4 时 Disjoint 系数为 0（非严格即可），n > 4 时必须**严格为正**
（δmin 可任意小，故只需间隙 > 0）。

两条完备性事实：
  * `FourPoint + PositiveDefinite ⟺ 非负边权树度量`（Buneman），故「随机树度量」＝完备搜索的一种；
  * 判定式对正数缩放不变 ⇒ 整值网格即可覆盖有理点附近的定性行为。

结果（2026-10-19）：
  * n = 4，六距离取值 0–5 **全枚举**：3025 个 FourPoint∧PositiveDefinite 度量，0 反例；
  * n = 5，取值 0–2 **全枚举**：122 个，0 反例；
  * n = 4…10 随机树度量（边权含 0，覆盖零长悬挂边 / 零长内部边 = 多分叉）：0 反例。
⇒ 命题**不可证伪**，W25 泳道 b 走**证成**路线（`atteson_lemma11_gap_holds`）。

用法：`python3 scripts/msc/w25_lemma11_gap_check.py`
"""
import itertools, random, sys


# ---------------- 判定核心 ----------------
def make_pairs(n):
    return list(itertools.combinations(range(n), 2))


def fourpoint(d, n):
    for i, j, k, l in itertools.permutations(range(n), 4):
        a = d[i][j] + d[k][l]
        b = d[i][k] + d[j][l]
        c = d[i][l] + d[j][k]
        if not (a <= b or a <= c):
            return False
    return True


def posdef(d, n):
    return all(d[i][j] > 0 for i in range(n) for j in range(n) if i != j)


def Q(d, n, i, j):
    return (n - 2) * d[i][j] - sum(d[i][k] for k in range(n)) - sum(d[j][k] for k in range(n))


def cherries(d, n):
    """`Dissimilarity.IsCherry`：a≠b ∧ ∀ k,l ∉ {a,b}, δab+δkl ≤ 两个交叉和。"""
    out = set()
    for a, b in itertools.combinations(range(n), 2):
        ok = True
        for k in range(n):
            if k in (a, b):
                continue
            for l in range(n):
                if l in (a, b):
                    continue
                if not (d[a][b] + d[k][l] <= d[a][k] + d[b][l]
                        and d[a][b] + d[k][l] <= d[a][l] + d[b][k]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.add((a, b))
    return out


def eligible(ij, kl, d, n):
    """该樱桃能否为这个非樱桃对作证（形态 + 严格间隙）。"""
    i, j = ij
    k, l = kl
    dis = i != k and i != l and j != k and j != l
    sh = ((i == k and j != k and j != l) or (i == l and j != k and j != l)
          or (j == k and i != k and i != l) or (j == l and i != k and i != l))
    diff = Q(d, n, k, l) - Q(d, n, i, j)
    if dis:
        coef = 3 * (n - 4)
        return diff >= 0 if coef == 0 else diff > 0
    if sh:
        return diff > 0
    return False


def gap_ok(d, n):
    ch = cherries(d, n)
    for k, l in itertools.combinations(range(n), 2):
        if (k, l) in ch:
            continue
        if not any(eligible(ij, (k, l), d, n) for ij in ch):
            return False, (k, l), ch
    return True, None, ch


# ---------------- 搜索 1：全枚举整值度量 ----------------
def search_grid(n, vals):
    ps = make_pairs(n)
    cnt = 0
    bad = []
    for combo in itertools.product(vals, repeat=len(ps)):
        d = [[0] * n for _ in range(n)]
        for (a, b), v in zip(ps, combo):
            d[a][b] = d[b][a] = v
        if not posdef(d, n) or not fourpoint(d, n):
            continue
        cnt += 1
        ok, kl, ch = gap_ok(d, n)
        if not ok:
            bad.append((combo, kl, ch))
    return cnt, bad


# ---------------- 搜索 2：随机树度量（边权含 0） ----------------
def random_binary_tree(n, rng):
    groups = [(i, []) for i in range(n)]
    nxt = n
    while len(groups) > 1:
        a = rng.randrange(len(groups))
        ga = groups.pop(a)
        b = rng.randrange(len(groups))
        gb = groups.pop(b)
        node = nxt
        nxt += 1
        edges = []
        for (root, sub) in (ga, gb):
            edges.append((node, root, rng.choice([0, 1, 2, 2, 3, 5])))
            edges.extend(sub)
        groups.append((node, edges))
    return groups[0][1]


def dists_from_edges(n, edges):
    adj = {i: [] for i in range(n)}
    for (u, v, w) in edges:
        adj.setdefault(u, []).append((v, w))
        adj.setdefault(v, []).append((u, w))
    D = [[0] * n for _ in range(n)]
    for s in range(n):
        stack = [(s, -1, 0)]
        while stack:
            u, p, dd = stack.pop()
            if u < n:
                D[s][u] = dd
            for (v, w) in adj[u]:
                if v != p:
                    stack.append((v, u, dd + w))
    return D


def search_trees(n, trials, seed):
    rng = random.Random(seed)
    tested = 0
    bad = []
    for _ in range(trials):
        d = dists_from_edges(n, random_binary_tree(n, rng))
        if not posdef(d, n) or not fourpoint(d, n):
            continue
        tested += 1
        ok, kl, ch = gap_ok(d, n)
        if not ok:
            bad.append((d, kl, ch))
    return tested, bad


if __name__ == "__main__":
    total_bad = 0
    for n, vals in [(4, range(0, 6)), (5, range(0, 3))]:
        cnt, bad = search_grid(n, vals)
        total_bad += len(bad)
        print(f"[grid]   n={n} vals={list(vals)}: {cnt} FourPoint+PositiveDefinite, "
              f"counterexamples={len(bad)}")
        for combo, kl, ch in bad[:2]:
            print("   values:", {p: v for p, v in zip(make_pairs(n), combo)})
            print("   failing pair:", kl, " cherries:", sorted(ch))
        sys.stdout.flush()
    tree_total = 0
    for n in [4, 5, 6, 7, 8, 9, 10]:
        tested, bad = search_trees(n, 20000, 12345 + n)
        tree_total += tested
        total_bad += len(bad)
        print(f"[trees]  n={n}: {tested} tree metrics (0-weight edges included), "
              f"counterexamples={len(bad)}")
        if bad:
            d, kl, ch = bad[0]
            print("   D:", d, " failing pair:", kl, " cherries:", sorted(ch))
        sys.stdout.flush()
    print(f"TOTAL: {tree_total} random tree metrics + grid upper rows; "
          f"counterexamples={total_bad}")
