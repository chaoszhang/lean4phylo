#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W10j —— ADR2011 (Allman-Degnan-Rhodes 2011) **Lemma 4** 的精确数值复核.

文献：E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree
from the distribution of unrooted gene trees*, J. Math. Biol. **62** (2011) 833-862.
Lemma 4 原文见 `references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md`
第 **962-970 行**：

> **Lemma 4** If all coalescent events occur above the root (temporally before the MRCA
> of all species) of a 5-taxon species tree, then all 15 of the unrooted topological gene
> trees are equally likely.

本脚本**逐字复刻** `Phylo/Stat/RankedGeneTree.lean` 的编码（`stepMap` / `chainMap` /
`IsStep` / `IsMergeHistory` / `blocksOf` / `cladesOf`），用**整数**穷举核对：

  (A) 合并史（ranked 基因树拓扑）计数 `|RankedTree n| = H_n = prod_{k=2}^{n} C(k,2)`
      （n = 1..6），即 `Phylo.Stat.RankedGeneTree` 的缺口 `rankedTree_card_gap`；
      并核对递推 `|RankedTree n| = C(n,2) * |RankedTree (n-1)|`（组合路线）。
  (B) **无根**拓扑 = **分裂集**（bipartition 集）：由 clade 集去掉单点与根（`univ`）、
      把互补的两个 clade 视为同一个分裂而得到。核对 `n = 5` 时恰有 `15` 个无根拓扑；
      `n = 4` 时恰有 `15` 个（`= (2*4-3)!! = 15`，与 `card_topologies_four` 一致）。
  (C) ★★★ **Lemma 4 的计数核心**：`n = 5` 时每个无根拓扑的**纤维**
      （能产生它的合并史个数）都等于 `12 = H_5/15 = 180/15`。
  (D) 概率：每条合并史的概率都是 `1/H_5 = 1/180`（K82 跳链：第 k 步 C(k,2) 选一），
      故每个无根拓扑的概率 `= 12/180 = 1/15`（精确有理数）。
  (E) 反例边界（论文 Lemma 4 之后的 Note，md 第 973-974 行）：
      `n = 6` 时有两种不同的无根形状，**类似结论不成立** —— 穷举给出 `n = 6` 的
      纤维分布，证明它确实不是常数。

不依赖第三方库，无 Monte Carlo。
"""

from itertools import combinations
from math import factorial, comb
from fractions import Fraction as F
import sys

FAIL = []


def check(name, got, want):
    ok = got == want
    print(("  [ok]   " if ok else "  [FAIL] ") + name + f": got={got} want={want}")
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------------------
# Lean 编码的逐字复刻（`Fin n` 用 `range(n)` 表示，元素是整数 0..n-1）
# ---------------------------------------------------------------------------

def step_map(r, x, y):
    """`RankedGeneTree.stepMap r x y`：把 `y` 所在的块并入 `x` 所在的块。"""
    return tuple(x if r[w] == y else r[w] for w in range(len(r)))


def chain_map(n, f, L):
    """`RankedGeneTree.chainMap n f L`：前 L 次合并之后的块代表映射。"""
    r = tuple(range(n))                      # id
    for k in range(L):
        r = step_map(r, f[k][0], f[k][1])
    return r


def is_step(r, x, y):
    """`RankedGeneTree.IsStep r x y`。"""
    return r[x] == x and r[y] == y and x < y


def is_merge_history(n, f):
    """`RankedGeneTree.IsMergeHistory n f`（`f` 是长度 n-1 的 (x,y) 元组）。"""
    for k in range(n - 1):
        if not is_step(chain_map(n, f, k), f[k][0], f[k][1]):
            return False
    r = chain_map(n, f, n - 1)
    return all(r[w] == r[0] for w in range(n))


def blocks_of(n, r):
    """`RankedGeneTree.blocksOf n r`：以最小元为块代表的划分的**块**集合。"""
    return frozenset(frozenset(w for w in range(n) if r[w] == r[w0]) for w0 in range(n))


def clades_of(n, f):
    """`RankedGeneTree.cladesOf n f`：全部层的块的并（= 有根 clade 集）。"""
    s = set()
    for L in range(n):
        s |= blocks_of(n, chain_map(n, f, L))
    return frozenset(s)


def merge_histories(n):
    """穷举**全部**合并史（`IsMergeHistory n` 的精确解集）。

    `IsMergeHistory n f` 的合法性是**逐步**的（第 `k` 步只依赖 `f[0..k-1]`），
    故按「合法前缀」做 BFS 即可穷尽 —— 等价于对 `Fin (n-1) -> Fin n x Fin n`
    的 `n^(2(n-1))` 个候选逐个筛选，但代价从 `n^(2n-2)` 降到 `H_n * n^2`
    （`n = 6`：`36^5 = 6.0e7` → `56700*36 ≈ 2.0e6`）。

    安全网：`n <= 4` 时同时用**暴力全空间筛选**核对 BFS 结果（见 `main`）。"""
    if n <= 1:
        return [()]
    level = [(tuple(range(n)), ())]
    for _k in range(n - 1):
        nxt = []
        for r, f in level:
            for x in range(n):
                if r[x] != x:
                    continue
                for y in range(x + 1, n):
                    if r[y] != y:
                        continue
                    nxt.append((step_map(r, x, y), f + ((x, y),)))
        level = nxt
    return [f for r, f in level if all(r[w] == r[0] for w in range(n))]


def merge_histories_bruteforce(n):
    """暴力：直接枚举 `Fin (n-1) -> Fin n x Fin n` 的全空间（只用于小 `n` 核对）。"""
    from itertools import product
    if n <= 1:
        return [()]
    out = []
    for f in product([(x, y) for x in range(n) for y in range(n)], repeat=n - 1):
        if is_merge_history(n, f):
            out.append(f)
    return out


def splits_of_clades(n, clades):
    """★ 无根拓扑：把**有根** clade 集转成**无根**分裂（bipartition）集。

    对每个 clade `C` 满足 `2 <= |C| <= n-2`（= 根以下的内部顶点，且**两支都非单点**），
    取分裂 `{C, C^c}`（把互补的两支视为**同一个**分裂）。根的两个孩子的 clade 互补，
    故在这个映射下自动合并成一个分裂 —— 这正是「忘掉根」的代数内容。

    ⚠️ 尺寸上界必须是 `n-2` 而**不是** `n-1`：`|C| = n-1` 的 clade 给出的是
    `C` 与单点 `w` 的二分，即叶 `w` 的**悬垂边**，不是内部边（本脚本第一版用 `n-1`
    得到 90 个伪拓扑，正好说明这一条不能省）。"""
    allset = frozenset(range(n))
    splits = set()
    for C in clades:
        if 2 <= len(C) <= n - 2:
            splits.add(frozenset({C, allset - C}))
    return frozenset(splits)


# ---------------------------------------------------------------------------

def H_prod(n):
    """prod_{k=2}^{n} C(k,2)（= 论文的 H_n）。"""
    r = 1
    for k in range(2, n + 1):
        r *= k * (k - 1) // 2
    return r


def section_A(BY_N):
    print("(A) 合并史计数 |RankedTree n| = H_n = prod_{k=2}^{n} C(k,2)  [Lean: 缺口 rankedTree_card_gap]")
    for n in range(1, 7):
        check(f"|RankedTree {n}|", len(BY_N[n]), H_prod(n))
    print("      H_1..H_6 =", [H_prod(n) for n in range(1, 7)])
    print("      递推 |RankedTree n| = C(n,2)*|RankedTree (n-1)|：")
    for n in range(2, 7):
        check(f"递推 n={n}", len(BY_N[n]), comb(n, 2) * len(BY_N[n - 1]))
    check("H_5", H_prod(5), 180)


def section_B(BY_N):
    print("(B) 无根拓扑 = 分裂集：个数（无根二叉拓扑数 = (2n-5)!!）")
    for n in (3, 4, 5, 6):
        topos = {splits_of_clades(n, clades_of(n, f)) for f in BY_N[n]}
        want = {3: 1, 4: 3, 5: 15, 6: 105}[n]
        check(f"n={n} 无根拓扑数", len(topos), want)
        if n >= 5:
            check(f"n={n} 每个无根拓扑的分裂数（应为 n-3 条内部边）",
                  sorted({len(t) for t in topos}), [n - 3])
    # 交叉核对：有根 clade 集（**不是**无根拓扑）的个数 = (2n-3)!!
    for n in (3, 4):
        rooted = {clades_of(n, f) for f in BY_N[n]}
        check(f"n={n} 有根 clade 集个数 = (2n-3)!!（对照 Lean card_topologies_three/four）",
              len(rooted), {3: 3, 4: 15}[n])


def section_C(BY_N):
    print("(C) ★★★ Lemma 4 的计数核心：n=5 的纤维（=|{f : topoOf f = T}|）")
    n = 5
    fib = {}
    for f in BY_N[n]:
        T = splits_of_clades(n, clades_of(n, f))
        fib[T] = fib.get(T, 0) + 1
    sizes = sorted(set(fib.values()))
    check("纤维大小取值集合", sizes, [12])
    check("纤维数（无根拓扑数）", len(fib), 15)
    check("纤维之和 = 合并史数", sum(fib.values()), 180)
    print("      每个拓扑的纤维 =", sorted(fib.values()))
    print("      样例（按分裂集排序后前 3 个）：")
    for T in sorted(fib, key=lambda t: sorted(map(sorted, t)))[:3]:
        pretty = " | ".join("".join(str(x) for x in C) for C in sorted(map(sorted, T)))
        print(f"        分裂 {pretty:12s} 纤维 = {fib[T]}")
    # n=4 交叉核对：**无根**拓扑 3 个、纤维全 6（对照 Lean 里**有根** clade 集的纤维 1/2）
    fib4 = {}
    for f in BY_N[4]:
        T = splits_of_clades(4, clades_of(4, f))
        fib4[T] = fib4.get(T, 0) + 1
    check("n=4 无根拓扑数", len(fib4), 3)
    check("n=4 无根纤维（= 18/3）", sorted(set(fib4.values())), [6])
    clade4 = {}
    for f in BY_N[4]:
        C = clades_of(4, f)
        clade4[C] = clade4.get(C, 0) + 1
    print("      ⚠️ 对照：n=4 的**有根** clade 集纤维 =",
          sorted(set(clade4.values())), "（Lean: card_rankings_01_23 = 2、card_rankings_012_3 = 1）",
          "—— 有根 ≠ 无根")
    # n=6：证明「5 taxa 的特殊性」
    fib6 = {}
    for f in BY_N[6]:
        T = splits_of_clades(6, clades_of(6, f))
        fib6[T] = fib6.get(T, 0) + 1
    print("(E) 反例边界：n=6 的纤维分布（论文 md 第 973-974 行：「6 taxa 时类似结论不成立」）")
    check("n=6 纤维非均匀（取值集合不是单点）", len(set(fib6.values())) > 1, True)
    print("      n=6 纤维取值分布 =", dict(sorted(__import__("collections").Counter(
        fib6.values()).items())))


def section_D(BY_N):
    print("(D) 概率版：每条合并史概率 1/H_5，每个无根拓扑概率 1/15")
    n = 5
    H5 = H_prod(n)
    p_hist = F(1, H5)
    check("1/H_5", p_hist, F(1, 180))
    # 跳链核：第 k 步在 C(k,2) 个可合并对里均匀选一个
    prod = F(1)
    for k in range(2, n + 1):
        prod *= F(1, comb(k, 2))
    check("prod_{k=2}^{5} 1/C(k,2)", prod, F(1, 180))
    fib = {}
    for f in BY_N[n]:
        T = splits_of_clades(n, clades_of(n, f))
        fib[T] = fib.get(T, 0) + 1
    probs = {F(c) * p_hist for c in fib.values()}
    check("每个无根拓扑的概率取值集合", sorted(probs), [F(1, 15)])
    check("15 个概率之和", sum(F(c) * p_hist for c in fib.values()), F(1))


def section_F(BY_N):
    """(F) 按「第一对」分块的核对 —— 对应 Lean 的 `consPair` / `piece` 分解。"""
    print("(F) 按第一对 k=(x,y) 分块：|piece k|（Lean 的 `consPair`/`piece` 分解用）")
    n = 5
    pieces = {}
    for k in [(x, y) for x in range(n) for y in range(n)]:
        pieces[k] = [g for g in
                     __import__("itertools").product([(x, y) for x in range(n) for y in range(n)],
                                                     repeat=n - 2)
                     if is_merge_history(n, (k,) + g)]
    valid = {x: y for x, y in pieces.items() if x[0] < x[1]}
    invalid = {x: y for x, y in pieces.items() if not x[0] < x[1]}
    check("合法第一对 k 的个数（x<y）", len(valid), 10)
    check("每个合法 k 的 |piece k|（应全 = H_4 = 18）", sorted({len(v) for v in valid.values()}), [18])
    check("非法第一对 k 的 |piece k|（应全 = 0）", sorted({len(v) for v in invalid.values()}), [0])
    check("分块之和 = 合并史数", sum(len(v) for v in pieces.values()), 180)
    # 每块的拓扑多重集：结构是「3 个拓扑 × 每个 6 条」，且 15 个拓扑每个恰被 2 个块覆盖
    per_piece = {}
    for k, gs in valid.items():
        c = {}
        for g in gs:
            T = splits_of_clades(n, clades_of(n, (k,) + g))
            c[T] = c.get(T, 0) + 1
        per_piece[k] = c
    check("每块的**不同**拓扑数（18 = 3 × 6）", sorted({len(c) for c in per_piece.values()}), [3])
    check("每块内每个拓扑的条数", sorted({v for c in per_piece.values() for v in c.values()}), [6])
    cover = {}
    for c in per_piece.values():
        for T in c:
            cover[T] = cover.get(T, 0) + 1
    check("每个无根拓扑被多少个块覆盖（12 = 2 × 6）", sorted(set(cover.values())), [2])
    total = {}
    for c in per_piece.values():
        for T, v in c.items():
            total[T] = total.get(T, 0) + v
    check("Σ_k（块 k 中拓扑 T 的条数）= fiber(T)（应全 = 12）", sorted(set(total.values())), [12])


def section_G(BY_N):
    """(G) 独立路线：论文 Remark 6（有根拓扑的 ranking 数）+「7 个根位置」。

    对每个**有根**拓扑 `R`（= 一个 clade 集）：`#rankings(R) = (n-1)!/prod_{内部顶点 i}(c_i-1)`
    （SD2012 Remark 6）。核对两件事：

      (G1) 穷举出的 `R` 的纤维（产生它的合并史条数）**逐条等于**这个公式；
      (G2) 固定一个**无根**拓扑 `T`，把它的 7 个根位置（2 条内部边 + 5 条悬垂边）
           对应的有根拓扑的 `#rankings` 加起来 = `fiber(T)`（= 12）；
           并核对**这 7 个数的多重集对 15 个 `T` 完全相同** ——
           这正是论文 Lemma 4 证明里「all unrooted gene trees have the same unlabeled shape」
           那句话的代数内容。"""
    print("(G) 独立路线：Remark 6 的 ranking 数 + 无根拓扑的 7 个根位置")
    n = 5
    rooted_fiber = {}
    rooted_topo = {}
    for f in BY_N[n]:
        R = clades_of(n, f)
        rooted_fiber[R] = rooted_fiber.get(R, 0) + 1
        rooted_topo[R] = splits_of_clades(n, R)
    check("有根拓扑（clade 集）个数 = (2n-3)!! = 105", len(rooted_fiber), 105)

    def remark6(R):
        d = 1
        for C in R:
            if len(C) >= 2:
                d *= (len(C) - 1)
        return factorial(n - 1) // d

    bad = [R for R in rooted_fiber if rooted_fiber[R] != remark6(R)]
    check("(G1) 每个有根拓扑：穷举纤维 = Remark 6 公式", bad, [])
    print("      Remark 6 的 ranking 数分布 =",
          dict(sorted(__import__("collections").Counter(remark6(R) for R in rooted_fiber).items())),
          "（Σ = 1*60 + 3*30 + 2*15 = 180）")

    per_T = {}
    for R in rooted_fiber:
        T = rooted_topo[R]
        per_T.setdefault(T, []).append(rooted_fiber[R])
    sigs = {T: tuple(sorted(v)) for T, v in per_T.items()}
    check("(G2) 每个无根拓扑恰好 7 个根位置（有根拓扑）", sorted({len(v) for v in per_T.values()}), [7])
    check("(G2) 7 个根位置的 ranking 多重集：15 个无根拓扑全同", len(set(sigs.values())), 1)
    print("      该多重集 =", list(sigs.values())[0], "→ 和 =", sum(list(sigs.values())[0]))
    check("(G2) 每个无根拓扑的纤维 = Σ 7 个根位置的 ranking 数", sorted(set(sum(v) for v in per_T.values())), [12])
    print("      15 个无根拓扑**形状全同**（内部边构成 A-B-C 链、叶分布 2/1/2），")
    print("      故「7 个根位置的 ranking 多重集」与 T 无关 —— 这就是 Lemma 4 的对称性论证。")


def main():
    print("=" * 78)
    print("W10j —— ADR2011 Lemma 4（5 taxa：全部溯祖在根以上 ⇒ 15 个无根拓扑等概率）")
    print("=" * 78)
    for n in range(1, 5):
        brute = merge_histories_bruteforce(n)
        bfs = merge_histories(n)
        check(f"n={n} BFS 枚举 = 暴力全空间筛选", sorted(bfs), sorted(brute))
    BY_N = {n: merge_histories(n) for n in range(1, 7)}
    section_A(BY_N)
    section_B(BY_N)
    section_C(BY_N)
    section_D(BY_N)
    section_F(BY_N)
    section_G(BY_N)
    print("=" * 78)
    if FAIL:
        print(f"FAILED: {len(FAIL)} -> {FAIL}")
        sys.exit(1)
    print("ALL CHECKS PASSED")
    print("=" * 78)


if __name__ == "__main__":
    main()
