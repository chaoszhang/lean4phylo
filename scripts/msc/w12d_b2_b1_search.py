#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12d/W12k ★C：瓶颈 (B1)/(B2) 与 `Split.FourPoint` 笔误的**精确穷举**核验

纯标准库（`itertools`/`fractions`），**精确有理数**，**无 Monte Carlo**。

核验对象（`δ := Σ_{S∈F} w_S · δ_S`，`δ_S` = `SplitMetric`，`F` **两两相容**、`w_S > 0`）：

1. **(B2)** 非成员 `S ∉ F ± swap` **不是** `δ` 的 d-split（`IsDSplit` 的 `max` 形式）；
   同时给出其**隔离指数** `α_S`（BdD 形式：四元组上平行配对的 `min`），核对 `α_S = 0`。
2. **(B1)** `δ` 是否满足四点条件 —— 分别按**文献形态**（`FourPointStd`：三对和最大者至少两次）
   与**本库 `def FourPoint` 的原文形态**（第三合取项含 `δ a b + δ a' b`）计算。
3. 反空真：至少给出一个 **`F` 非空、`w > 0`、且 `δ` 非常数** 的实例。

跑法：`wsl python3 scripts/msc/w12d_b2_b1_search.py`（有反例即非零退出）。
"""

from fractions import Fraction
from itertools import combinations

FAIL = []


def split_metric(A, comp, x, y):
    return 1 if ((x in A and y in comp) or (x in comp and y in A)) else 0


def canon(n, A):
    A = frozenset(A)
    comp = frozenset(range(n)) - A
    return min(A, comp, key=lambda s: sorted(s))


def all_splits(n):
    out = set()
    for k in range(1, n):
        for A in combinations(range(n), k):
            out.add(canon(n, A))
    return sorted(out, key=lambda s: sorted(s))


def compatible(n, A, B):
    Ac, Bc = frozenset(range(n)) - A, frozenset(range(n)) - B
    return (not (A & B)) or (not (A & Bc)) or (not (Ac & B)) or (not (Ac & Bc))


def delta_of(n, F, w):
    comps = {u: frozenset(range(n)) - u for u in F}
    def d(x, y):
        return sum(Fraction(w[u]) * split_metric(u, comps[u], x, y) for u in F)
    return d


def is_dsplit_max(n, d, S):
    """`IsDSplit δ S (Sᶜ)`（本库 `max` 形式）：所有四元组都严格成立才为真。"""
    A = S
    B = frozenset(range(n)) - S
    for a in A:
        for a2 in A:
            for b in B:
                for b2 in B:
                    lhs = d(a, a2) + d(b, b2)
                    if not (lhs < max(d(a, b) + d(a2, b2), d(a, b2) + d(a2, b))):
                        return False
    return True


def is_dsplit_strong(n, d, S):
    """「两配对都为正」（= 隔离指数 > 0 的逐四元组形式）。"""
    A = S
    B = frozenset(range(n)) - S
    for a in A:
        for a2 in A:
            for b in B:
                for b2 in B:
                    lhs = d(a, a2) + d(b, b2)
                    if not (lhs < d(a, b) + d(a2, b2) and lhs < d(a, b2) + d(a2, b)):
                        return False
    return True


def isolation_index(n, d, S):
    """BdD 隔离指数 α_S = ½·min{ d(a,b)+d(a',b')−d(a,a')−d(b,b') }（含 a=a'、b=b'）。"""
    A, B = S, frozenset(range(n)) - S
    vals = [d(a, b) + d(a2, b2) - d(a, a2) - d(b, b2)
            for a in A for a2 in A for b in B for b2 in B]
    return min(vals) / 2


def four_point(n, d, typo):
    """`typo=False`：文献形态（三对和最大者至少两次）；`typo=True`：本库原文形态。"""
    for a in range(n):
        for a2 in range(n):
            for b in range(n):
                for b2 in range(n):
                    W = d(a, a2) + d(b, b2)
                    P = d(a, b) + d(a2, b2)
                    X = d(a, b2) + d(a2, b)
                    if not (W <= max(P, X) and P <= max(W, X)):
                        return False
                    last = max(W, d(a, b) + d(a2, b)) if typo else max(W, P)
                    if not (X <= last):
                        return False
    return True


def check_families(n, maxsize, weights, label):
    sp = all_splits(n)
    fams = []
    for k in range(1, maxsize + 1):
        for F in combinations(sp, k):
            if all(compatible(n, A, B) for A, B in combinations(F, 2)):
                fams.append(F)
    bad_b2, bad_alpha, bad_b1, bad_b1_typo, nontrivial = [], [], [], [], 0
    for F in fams:
        for combo_w in weights(F):
            w = dict(zip(F, combo_w))
            d = delta_of(n, F, w)
            for S in sp:
                if S in F:
                    continue
                if is_dsplit_max(n, d, S):
                    bad_b2.append((F, combo_w, S))
                if isolation_index(n, d, S) > 0:
                    bad_alpha.append((F, combo_w, S, isolation_index(n, d, S)))
            if not four_point(n, d, typo=False):
                bad_b1.append((F, combo_w))
            if not four_point(n, d, typo=True):
                bad_b1_typo.append((F, combo_w))
            if any(d(0, j) != 0 for j in range(n)):
                nontrivial += 1
    print(f"[{label}] 两两相容族 {len(fams)} 个 × 权重组合 —— 实例数 {nontrivial}")
    print(f"   (B2) 非成员却满足 `IsDSplit`(max)：{len(bad_b2)} 例")
    print(f"   (B2') 非成员隔离指数 > 0（应为 0 例）：{len(bad_alpha)} 例")
    print(f"   (B1_std)      文献四点条件不成立        ：{len(bad_b1)} 例"
          "  ⇒ 0 例意味着 **B1 的 `FourPointStd` 修复形态在这些实例上成立**")
    print(f"   (B1_refuted)  本库 `FourPoint` 原文不成立：{len(bad_b1_typo)} 例"
          "  ⇒ **B1（注册形态，结论用库内 `FourPoint`）为假**")
    if bad_b2[:2]:
        print("   例（B2 反例）：", bad_b2[:2])
    if bad_alpha[:2]:
        print("   例（α ≠ 0）：", bad_alpha[:2])
    if bad_b1_typo[:2]:
        print("   例（FourPoint 原文反例）：", bad_b1_typo[:2])
    if bad_b2:
        FAIL.append(f"{label}: (B2) 反例 {len(bad_b2)}")
    if bad_alpha:
        FAIL.append(f"{label}: α ≠ 0 反例 {len(bad_alpha)}")
    if bad_b1:
        FAIL.append(f"{label}: 文献四点条件反例 {len(bad_b1)}")
    if not bad_b1_typo:
        FAIL.append(f"{label}: 未复现「库内 FourPoint 被树度量违反」")


def unit_weights(F):
    yield tuple([1] * len(F))


def small_weights(F):
    for r in (1, 2):
        yield tuple([r] * len(F))


print("== n = 4：F 大小 ≤ 3，权重 ∈ {1,2} ==")
check_families(4, 3, small_weights, "n=4")
print("== n = 5：F 大小 ≤ 2，权重 = 1 ==")
check_families(5, 2, unit_weights, "n=5")
print("== n = 5：F 大小 ≤ 3，权重 = 1（B2 加压） ==")
check_families(5, 3, unit_weights, "n=5-3")
print("== n = 6：F 大小 ≤ 2，权重 = 1（B2 加压） ==")
check_families(6, 2, unit_weights, "n=6-2")
print("== n = 5：F 大小 ≤ 4，权重 = 1（(★′) 加压） ==")
check_families(5, 4, unit_weights, "n=5-4")
print("== n = 6：F 大小 ≤ 3，权重 = 1（(★′) 加压） ==")
check_families(6, 3, unit_weights, "n=6-3")

print("== 库内 FourPoint 与标准 FourPoint 的方向（对称 δ 小网格）==")


def grid_check(n, vals):
    ks = [c for c in combinations(range(n), 2)]
    only_lib = only_std = both_ = 0
    for combo in __import__("itertools").product(vals, repeat=len(ks)):
        D = {k: Fraction(v) for k, v in zip(ks, combo)}
        def dd(x, y):
            if x == y:
                return Fraction(0)
            return D[(min(x, y), max(x, y))]
        lib = four_point(n, dd, typo=True)
        std = four_point(n, dd, typo=False)
        if lib and std:
            both_ += 1
        elif lib:
            only_lib += 1
        elif std:
            only_std += 1
    print(f"   n={n} 网格 {vals}: 两者皆真 {both_}；仅库内真 {only_lib}；仅标准真 {only_std}")
    if only_lib:
        FAIL.append(f"n={n}: 「仅库内真」{only_lib} 例 ⇒ 方向判定被推翻")


grid_check(3, [0, 1, 2])
grid_check(4, [0, 1])

print()
print("== 结论（两行分开，勿混读）==")
print("1. **注册形态被反驳**：`fourPointOfSplitMetricSum_gap`（结论用库内 `FourPoint`）为**假** ——")
print("   上表 `(B1_refuted)` 例数 > 0 即见证（Lean 侧：`Split.not_fourPointOfSplitMetricSum`，")
print("   最小见证 = 树度量 `δ_{0|123} + δ_{01|23}` 在 `(0,0,1,2)` 处 `3 > 2`）。")
print("2. **修复形态无反例**：`fourPointOfSplitMetricSum_gap_correct_shape`（结论用 `FourPointStd`）")
print("   在上表 `(B1_std)` = 0 例反例 ⇒ 倾向为真（Lean 侧仅登记，未证）。")
print("3. **(B2) 无反例**：非成员在 `max` 形式下都不是 d-split，且隔离指数 `≤ 0`（`> 0` 例数 = 0）。")
if FAIL:
    print("FAILED:", FAIL)
    raise SystemExit(1)
print("ALL OK（精确有理数穷举；注册形态的反例已复现，修复形态与 (B2) 无反例）")
