#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
w30c_history_model_check.py -- W30 泳道c：**YHK 律的两个历史空间编码**的精确有理数复核

背景（本脚本是 `Phylo/Stat/ReciprocalMonophyly.lean` §11.3 口径更正的证据）：

`§11.3` 的 `yhkHistorySpace n := (k : Fin (n−3)) → Fin (k+3)`
（第 k 步在 k+3 片叶里选一片、把新叶挂到它的**悬挂边**上）**不是** YHK 律：

  * 它漏了「新叶挂到一条 split 的**另一侧**」的那些树（ZDS 2011 `:1000-1006` 的
    "with a random label" 那一步在编码里没有自由度）⇒ n ≥ 5 时它只覆盖
    `∏_{k=1}^{n−4}(k+3) = (n−1)!/2` 条历史（不同的历史仍可能给出同一棵树），
    而标号无根二叉树共有 `(2n−5)!!` 棵（n=5: 12 ≠ 15）；
  * 于是它的测度不是 YHK 律 ⇒ **不能**填进 `YHKClanLawGap`（`:924`）的 `Ω` 槽
    （在 n = 5 上 `P(A 是 clan)` 会算成 `1/6` 而不是 `clanProb 5 2 = 1/5`）。

本脚本核两件事（全部 `fractions.Fraction` 精确、无浮点、无随机数、可重复）：

  (A) 「选叶」模型 = `yhkHistorySpace`：枚举全部历史 → 建树 → 数「A 是 clan」的频率，
      与 `clanProb n a` 对照。**预期 n = 4 相等、n ≥ 5 不等**（后者是本脚本要*证明*的失配）。
  (B) 「选块对合并」模型 = 库内 `RankedTree n` / `mergeHistories n`
      （`Phylo/Stat/RankedGeneTree.lean:165-169`，基数 `card_mergeHistories_eq_H`
      `Phylo/Stat/CoalescentHistoryCount.lean:578`，已证 `= n!(n−1)!/2^{n−1}`）：
      枚举全部合并历史 → 读出 clade 族 → 数「A 是 clan」的频率，**预期与 `clanProb` 逐点相等**。

口径（与库内一致）：
  * 有根树的 clade = 某内部顶点的后代叶集；**合并历史**每步并出的块就是某个内部顶点的后代叶集；
  * 无根树的 clan = T−ρ 的 split 的一侧 ⇒ 由 ZDS Lemma 6.1（库内 `isClanMinusRoot_iff`）：
    A 是 clan ⟺ A 是 clade 或 X∖A 是 clade（size 1 / n−1 两档恒真，判据同样给对）；
  * `clanProb n a` = ZDS Lemma 6.2 闭式（库内 `clanProb`，`clanProb_eq_inclusionExclusion` 已把代数核过）。

运行：`python3 scripts/msc/w30c_history_model_check.py`（退出码 0 = 全部通过）
"""

from fractions import Fraction
from itertools import combinations, product
from math import comb, factorial


# --------------------------------------------------------------------------
# 1. 闭形式（ZDS Lemma 6.2，库内 `clanProb`）
# --------------------------------------------------------------------------

def clanProb(n, a):
    """`clanProb n a`（`1 ≤ a ≤ n−1`）：无根 YHK 树的 a 元子集是 clan 的概率。"""
    return Fraction(2 * n, 1) * (
        Fraction(1, a * (a + 1))
        + Fraction(1, (n - a) * (n - a + 1))
        - Fraction(1, (n - 1) * n)
    ) / comb(n, a)


# --------------------------------------------------------------------------
# 2. (A) 「选叶」模型（= 库内 `yhkHistorySpace` 的语义）
# --------------------------------------------------------------------------

def _canon(A, B):
    a, b = frozenset(A), frozenset(B)
    return (a, b) if sorted(a) <= sorted(b) else (b, a)


def _attach(splits, leaf, new, current):
    """把新叶 `new` 挂到 `leaf` 的悬挂边上（subdivide 该边），返回新的非平凡 split 集。"""
    out = set()
    for (A, B) in splits:
        out.add(_canon(A | {new}, B) if leaf in A else _canon(A, B | {new}))
    out.add(_canon({leaf, new}, current - {leaf, new}))
    return frozenset(out)


def leaf_model(n):
    """枚举 `(k : Fin (n−3)) → Fin (k+3)` 的全部历史，返回每条的 split 集。"""
    res = []
    for choices in product(*[range(k + 3) for k in range(n - 3)]):
        splits = frozenset()
        for k, chosen in enumerate(choices):
            splits = _attach(splits, chosen, k + 3, set(range(k + 4)))
        res.append(splits)
    return res


def clans_of_splits(splits):
    out = set()
    for (A, B) in splits:
        out.add(A)
        out.add(B)
    return out


def is_clan(A, clades, n):
    """`A` 是 clan ⟺ `A` 或 `X∖A` 是 clade（ZDS Lemma 6.1）；size 1 / n−1 两档恒真。"""
    A = frozenset(A)
    X = frozenset(range(n))
    if len(A) == 1 or len(A) == n - 1:
        return True
    return A in clades or (X - A) in clades


# --------------------------------------------------------------------------
# 3. (B) 「选块对合并」模型（= 库内 `RankedTree n` / `mergeHistories n`）
# --------------------------------------------------------------------------

def merge_model(n):
    """枚举 `mergeHistories n` 的全部元素：每步在 n−k 个块里选一对合并。

    返回每条的 clade 族；块 = 内部顶点的后代叶集 = 有根树的 clade。
    """
    states = [(tuple(frozenset({i}) for i in range(n)), frozenset())]
    for _ in range(n - 1):
        nxt = []
        for blocks, clades in states:
            m = len(blocks)
            for i, j in combinations(range(m), 2):
                merged = blocks[i] | blocks[j]
                nb = tuple(blocks[t] for t in range(m) if t not in (i, j)) + (merged,)
                nxt.append((nb, clades | {merged}))
        states = nxt
    return [clades for _, clades in states]


def odd_double_factorial(n):
    """`(2n−5)!!` = 无根标号二叉树的棵数。"""
    r = 1
    for k in range(1, n - 2):
        r *= 2 * k + 1
    return r


# --------------------------------------------------------------------------
# 4. 主判定
# --------------------------------------------------------------------------

def main():
    ok = True

    print("=" * 78)
    print("(A) 「选叶」模型（库内 `yhkHistorySpace`）：**测度不是 YHK 律**")
    print("=" * 78)
    for n in (4, 5, 6):
        splits_list = leaf_model(n)
        trees = set(splits_list)
        print(f"n = {n}: #hist = {len(splits_list)}, #distinct trees = {len(trees)}, "
              f"(2n-5)!! = {odd_double_factorial(n)}")
        if n >= 5:
            short = len(trees) < odd_double_factorial(n)
            print(f"   覆盖全部标号树？ {'否（缺 %d 棵）' % (odd_double_factorial(n) - len(trees)) if short else '是'}")
            ok &= short
        for a in range(2, n - 1):
            A = frozenset(range(a))
            p = Fraction(sum(1 for t in splits_list if is_clan(A, clans_of_splits(t), n)),
                         len(splits_list))
            ref = clanProb(n, a)
            same = p == ref
            print(f"   a = {a}: P_leaf(A clan) = {p}   clanProb = {ref}   "
                  f"{'相等' if same else '★不等（模型错）'}")
            ok &= (same if n == 4 else (not same))

    print()
    print("=" * 78)
    print("(B) 「选块对合并」模型（库内 `RankedTree n` / `mergeHistories n`）：测度 = YHK 律")
    print("=" * 78)
    for n in (3, 4, 5, 6, 7):
        clades_list = merge_model(n)
        h = 1
        for k in range(2, n + 1):
            h *= comb(k, 2)
        hclosed = Fraction(factorial(n) * factorial(n - 1), 2 ** (n - 1))
        print(f"n = {n}: #hist = {len(clades_list)}, ∏C(k,2) = {h}, "
              f"n!(n-1)!/2^(n-1) = {hclosed}")
        ok &= (len(clades_list) == h == hclosed)
        for a in range(1, n):
            A = frozenset(range(a))
            p = Fraction(sum(1 for cl in clades_list if is_clan(A, cl, n)), len(clades_list))
            ref = clanProb(n, a)
            same = p == ref
            print(f"   a = {a}: P_merge(A clan) = {p}   clanProb = {ref}   "
                  f"{'相等 OK' if same else '★不等'}")
            ok &= same

    print()
    print("=" * 78)
    print("总判定：", "ALL OK" if ok else "存在不一致（见上面 ★ 行）")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
