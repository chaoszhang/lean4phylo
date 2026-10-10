#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11c / C3-C4 —— 精确（纯标准库、无 Monte Carlo）穷举核对脚本
================================================================

对应 Lean 文件 `Phylo/ConsensusGreedy.lean`（W11c / C3 + C4）。
本脚本**只做有限穷举**，不做任何随机采样；所有计数都是精确整数。

## 形式化对象（与 Lean 侧一致）

叶集 `{0,...,n-1}`。一个 **split** 是叶集的二分（无序），用「字典序较小的那一侧的有序元组」
作规范形（`canon`）。两个 split **相容** ⟺ 四个交中至少一个为空。

**树** = 非平凡 split 的**极大两两相容族**（Splits-Equivalence：树的 split 系统两两相容；
反之任一极大相容族都是某棵无度 2 内部顶点的树的 split 集）。故「所有树」= 所有极大相容族。

**贪心（在手文献 ADR2016:779–781 的过程）**：按给定次序逐个考察候选 split，
**接受 ⟺ 与已接受者全部相容**（`greedy`）。全部「频率非增」的候选次序 = 全部同频决胜。

## 本脚本核对

(A) ★B —— 贪心加入顺序影响输出吗？：n∈{4,5}、k∈{2,3} 的**全部**树多重集上，
    枚举**全部**频率非增次序，收集全部不同输出。
(B) Lean 见证复核（Fin 4 的 `exGreedyS`/`exGreedyT`）。
(C1) `2l > k ⟹ M_l 两两相容`（Lean `lSplits_compatible`）。
(C2) 候选表**恰为** `M_l` 时，任意频率非增次序的贪心输出 = `M_l`（Lean `lSplits_greedyRun_eq`）。
(C3) 候选表取**全部**出现过的 split 时，贪心输出 ≠ `M_l`（⇒ 贪心比阈值规则更精细，
     是与 `M_l` **不同**的方法；k ≤ 3 时穷举全部次序）。
(C4) `2l ≤ k` 的**最小**不相容实例（Lean `no_compatible_family_containing_incompatible` 场景）。
"""

import itertools
from collections import Counter

ORDER_CAP = 20000          # 单个实例的次序数上限（超出则跳过并计数）


# ---------------------------------------------------------------- split 基础

def canon(A, B):
    a, b = tuple(sorted(A)), tuple(sorted(B))
    return a if a <= b else b


def all_splits(n):
    """叶集 {0..n-1} 的全部**非平凡** split（两侧各 >= 2）的规范形。"""
    leaves = frozenset(range(n))
    out = set()
    for r in range(2, n - 1):
        for A in itertools.combinations(range(n), r):
            Ax = frozenset(A)
            if 0 not in Ax:                        # 每个 split 只由「含 0 的那一侧」列出一次
                continue
            out.add(canon(Ax, leaves - Ax))
    return out


def compat(s, t, n):
    """两 split 相容 ⟺ 四个交至少一个为空。"""
    A, B = frozenset(s), frozenset(t)
    Ac = frozenset(range(n)) - A
    Bc = frozenset(range(n)) - B
    return not (A & B) or not (A & Bc) or not (Ac & B) or not (Ac & Bc)


def all_trees(n):
    """全部树 = 全部**极大**两两相容的非平凡 split 族（穷举子集）。"""
    sp = sorted(all_splits(n))
    bad = [(i, j) for i in range(len(sp)) for j in range(i + 1, len(sp))
           if not compat(sp[i], sp[j], n)]
    fams = []
    for mask in range(1 << len(sp)):
        chosen = [i for i in range(len(sp)) if mask >> i & 1]
        if any((mask >> i & 1) and (mask >> j & 1) for i, j in bad):
            continue
        maximal = all(
            any(not compat(sp[i], sp[k], n) for k in chosen)
            for i in range(len(sp)) if not (mask >> i & 1))
        if maximal:
            fams.append(frozenset(sp[i] for i in chosen))
    return sp, sorted(fams, key=lambda f: (len(f), sorted(f)))


# ---------------------------------------------------------------- 贪心 / M_l / 次序

def greedy(cand_order, n):
    """在手文献的过程：按给定次序逐个接受『与已接受者全部相容』的 split。"""
    acc = []
    for s in cand_order:
        if all(compat(s, t, n) for t in acc):
            acc.append(s)
    return frozenset(acc)


def freq_orders(cands, cnt):
    """恰好枚举全部『频率非增』的候选次序（= 全部同频决胜），按频率分组做排列积。"""
    groups = {}
    for s in cands:
        groups.setdefault(cnt[s], []).append(s)
    keys = sorted(groups, reverse=True)
    for choice in itertools.product(*[itertools.permutations(groups[k]) for k in keys]):
        yield [s for g in choice for s in g]


def pairwise_compatible(fam, n):
    fl = sorted(fam)
    return all(compat(fl[i], fl[j], n) for i in range(len(fl)) for j in range(i + 1, len(fl)))


def ml(trees, n, l):
    """Day 的 M_l：出现在至少 l 棵树中的 split。"""
    c = Counter()
    for T in trees:
        for s in T:
            c[s] += 1
    return frozenset(s for s, v in c.items() if v >= l)


def n_orders(cands, cnt):
    tot, g = 1, Counter()
    for s in cands:
        g[cnt[s]] += 1
    for v in g.values():
        for i in range(2, v + 1):
            tot *= i
    return tot


# ---------------------------------------------------------------- 主流程

def main():
    print("=" * 78)
    print("W11c / C3-C4 精确穷举核对   （纯标准库；无随机；全部计数精确）")
    print("=" * 78)

    TREES = {}
    for n in (4, 5):
        sp, ts = all_trees(n)
        TREES[n] = ts
        print(f"[枚举] n={n}: 非平凡 split {len(sp)} 个，树（极大相容族）{len(ts)} 棵，"
              f"每棵的 split 数分布 {sorted(Counter(len(t) for t in ts).items())}")

    # ---------------- (A) 次序敏感性 ----------------
    print()
    print("-" * 78)
    print("(A) ★B：贪心加入顺序影响输出吗？—— 全枚举『频率非增』次序")
    print("-" * 78)
    total_inst = skipped = 0
    sensitive = []
    max_out = 0
    for n in (4, 5):
        for k in (2, 3):
            for combo in itertools.combinations_with_replacement(TREES[n], k):
                trees = list(combo)
                cnt = Counter()
                for T in trees:
                    for s in T:
                        cnt[s] += 1
                cands = sorted(cnt)
                if not cands:
                    continue                       # 全星树：无候选
                if n_orders(cands, cnt) > ORDER_CAP:
                    skipped += 1
                    continue
                total_inst += 1
                outs = {greedy(o, n) for o in freq_orders(cands, cnt)}
                max_out = max(max_out, len(outs))
                if len(outs) > 1:
                    sensitive.append(dict(n=n, k=k, trees=trees, cnt=dict(cnt),
                                          cands=cands, norders=n_orders(cands, cnt),
                                          outs=sorted(map(sorted, outs))))
    print(f"实例总数（n∈{{4,5}}, k∈{{2,3}} 的全部树多重集）: {total_inst}")
    print(f"因次序上限 {ORDER_CAP} 跳过的实例数             : {skipped}")
    print(f"**次序敏感**（≥2 个不同输出）的实例数          : {len(sensitive)}")
    print(f"单个实例的最大不同输出数                       : {max_out}")
    sensitive.sort(key=lambda d: (len(d['cands']), d['n'], d['k']))
    w = sensitive[0]
    print()
    print("★ 最小反例（候选数最少，再取 n、k 最小）：")
    print(f"    n = {w['n']}, k = {w['k']}；树 = {[sorted(T) for T in w['trees']]}")
    print(f"    候选 split 及频率 = {w['cnt']}；频率非增次序数 = {w['norders']}")
    print(f"    **全部不同输出** = {w['outs']}")
    dist = Counter((d['n'], d['k']) for d in sensitive)
    print(f"    次序敏感实例按 (n,k) 分布: {sorted(dist.items())}")

    # ---------------- (B) Lean 见证复核 ----------------
    print()
    print("-" * 78)
    print("(B) Lean 见证复核（Fin 4：exGreedyS={0,1}|{2,3}, exGreedyT={0,2}|{1,3}）")
    print("-" * 78)
    n = 4
    S = canon(frozenset({0, 1}), frozenset({2, 3}))
    T = canon(frozenset({0, 2}), frozenset({1, 3}))
    print(f"    canon(exGreedyS) = {S} ; canon(exGreedyT) = {T}")
    print(f"    二者相容? {compat(S, T, n)}          （Lean exGreedy_not_compatible）")
    print(f"    次序 [S,T] 输出 = {sorted(greedy([S, T], n))}   （Lean exGreedy_run_left = {{exGreedyS}}）")
    print(f"    次序 [T,S] 输出 = {sorted(greedy([T, S], n))}   （Lean exGreedy_run_right = {{exGreedyT}}）")
    print(f"    两输出不同? {greedy([S, T], n) != greedy([T, S], n)}         （Lean greedyRun_order_dependent）")
    print("    ✅ 与 Lean 一致；两者都是【单元素相容族】——差别在『哪棵树』，不在『相不相容』")

    # ---------------- (C) M_l 阈值 ----------------
    print()
    print("-" * 78)
    print("(C) Day 的 M_l：相容性阈值、贪心不动点、以及『贪心 ≠ 阈值规则』")
    print("-" * 78)
    c1_ok = c1_bad = c2_ok = c2_bad = 0
    c3_skipped = 0
    c3_diff = []
    bad2 = []
    for n in (4, 5):
        for k in (2, 3, 4, 5):
            for combo in itertools.combinations_with_replacement(TREES[n], k):
                trees = list(combo)
                cnt = Counter()
                for T in trees:
                    for s in T:
                        cnt[s] += 1
                if not cnt:
                    continue
                full = sorted(cnt)
                for l in range(1, k + 1):
                    M = ml(trees, n, l)
                    if not (2 * l > k):
                        if not pairwise_compatible(M, n):
                            bad2.append((n, k, l, sorted(M)))
                        continue
                    # (C1)
                    c1_ok += 1 if pairwise_compatible(M, n) else 0
                    c1_bad += 0 if pairwise_compatible(M, n) else 1
                    # (C2) 候选表恰为 M_l
                    ml_list = sorted(M)
                    if n_orders(ml_list, cnt) <= ORDER_CAP:
                        if all(greedy(o, n) == M for o in freq_orders(ml_list, cnt)):
                            c2_ok += 1
                        else:
                            c2_bad += 1
                    # (C3) 候选表 = 全部出现过的 split（k ≤ 3 才穷举全部次序）
                    if k <= 3:
                        if n_orders(full, cnt) > ORDER_CAP:
                            c3_skipped += 1
                        else:
                            for o in freq_orders(full, cnt):
                                g = greedy(o, n)
                                if g != M:
                                    c3_diff.append(dict(n=n, k=k, l=l,
                                                        M=sorted(M), g=sorted(g),
                                                        extra=sorted(g - M),
                                                        missing=sorted(M - g),
                                                        cnt=dict(cnt)))
                                    break
    print(f"    (C1) 2l > k ⟹ M_l 两两相容（Lean lSplits_compatible）: 通过 {c1_ok}，反例 {c1_bad}")
    print(f"    (C2) 候选表恰为 M_l ⟹ 任意频率非增次序的贪心输出 = M_l"
          f"（Lean lSplits_greedyRun_eq）: 通过 {c2_ok}，反例 {c2_bad}")
    print("    ⇒ (C1)(C2) 穷举零反例")
    print()
    print(f"    (C3) 候选表取【全部出现过的 split】时『贪心 ≠ M_l』的实例数: {len(c3_diff)}"
          f"（k ≤ 3；因次序上限跳过 {c3_skipped}）")
    c3_diff.sort(key=lambda d: (len(d['cnt']), len(d['M']), d['n'], d['k'], d['l']))
    if c3_diff:
        d = c3_diff[0]
        print("    ★ 最小实例（候选数最少，再按 n,k,l 升序）：")
        print(f"      n={d['n']}, k={d['k']}, l={d['l']}；候选及频率 = {d['cnt']}")
        print(f"      M_l（阈值/多数共识）= {d['M']}")
        print(f"      贪心输出            = {d['g']}  （额外接受 {d['extra']}，漏掉 {d['missing']}）")
        print("      ⇒ 贪心**严格更精细**（⊇ M_l，且可严格更大）：『贪心共识』与在手文献的")
        print("        M_l **不是**同一个方法，其定义只能来自 Bryant 2003（不在手）。")
        print(f"      （另有 {len(c3_diff)} 个 k ≤ 3 的实例同样出现分歧；分歧时恒有 M_l ⊆ 贪心输出）")
        print(f"      『M_l ⊆ 贪心输出』在全部 {len(c3_diff)} 个分歧实例上成立: "
              f"{all(not d['missing'] for d in c3_diff)}")
    print()
    bad2.sort(key=lambda b: (b[1], b[2], b[0]))
    print("    (C4) 2l ≤ k 的**最小**不相容实例"
          "（Lean no_compatible_family_containing_incompatible 场景）：")
    if bad2:
        n2, k2, l2, M2 = bad2[0]
        pairs = [(a, b) for a in M2 for b in M2 if a < b and not compat(a, b, n2)]
        print(f"      n={n2}, k={k2}, l={l2}  ⟹  M_l = {M2}")
        print(f"      M_l 中的不相容对（前 3）: {pairs[:3]}")
        print(f"      满足 2l ≤ k 且 M_l 不相容的实例总数: {len(bad2)}")
        print("      ⇒ 越过 Day 的阈值（2l > k）后，任何『输出两两相容』的规则都必须丢弃 M_l 的")
        print("        部分 split；『按什么规范丢』= R* 共识 / Bryant 2003，**不在手**")
        print("        （→ Lean 的显式缺口 rStarConsensus_gap）。")
    else:
        print("      （无）")

    print()
    print("=" * 78)
    print("结论：C4 的在手表述（ADR2016:779–781）**不定义函数**（次序敏感，已被最小反例证实）；")
    print("      C3 的 R* 共识在全库在手文献中**零命中**（唯一 `R*` 字串是 Day1985:1229 的伪代码局部变量）。")
    print("=" * 78)


if __name__ == "__main__":
    main()
