#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12 · 协调侧核查：库内 `SplitPrime` 与文献的「split-prime」**不是同一回事**（并把范围钉死）。

两个 `IsDSplit` 形态
--------------------
库内 `Phylo/SplitWeak.lean`：
  `IsDSplit δ A B := ∀ a∈A, ∀ a'∈A, ∀ b∈B, ∀ b'∈B,
        δ a a' + δ b b' < max (δ a b + δ a' b') (δ a b' + δ a' b)`        —— **max 形式**
W12d 新增（并由 `bunemanIndex_pos_iff_isDSplitStrong` 与隔离指数 α 挂钩）：
  `IsDSplitStrong δ A B := ∀ a∈A … b'∈B,
        δ a a' + δ b b' < δ a b + δ a' b' ∧ δ a a' + δ b b' < δ a b' + δ a' b`  —— **两配对都为正**
关系：**Strong ⟹ Max** ✓（两配对都正 ⇒ 至少一个为正）；反向不成立 ✗（`a4` 的反例已入库）。

于是两个「split-prime」
----------------------
  · 文献/BdD：`α_S = 0`（隔离指数为零）⟺ **¬Strong**（W12d 已证 `α > 0 ↔ Strong`）；
  · 库内：`SplitPrime δ := ∀ A B, ¬ IsDSplit δ A B` ⟺ **¬Max**。
因 **¬Max ⟹ ¬Strong**（取逆否）而反向不成立 ⇒ **库内 `SplitPrime` 严格强于文献的 split-prime** ✗。

本脚本的判定（穷尽小 `n`，纯标准库、精确整数）
--------------------------------------------
搜「**没有任何 split 是 Strong** 但 **某个 split 是 Max**」的对称 δ：
  · `n = 4`，网格 `{-1,0,1,2}` ⇒ **3** 个（例：`(d01,d02,d03,d12,d13,d23) = (1,1,2,2,1,1)`，
    `(0,1)|(2,3)` 与 `(0,2)|(1,3)` 为 Max 而处处非 Strong）；
  · `n = 5`，网格 `{0,1,2}` ⇒ **1647** 个。

⇒ **后果（只打 `canonicalSplitDecomposition_gap`，不直接打 `weakCompatibilityRealization_gap`）**
`canonicalSplitDecomposition_gap` 要求**残差 `δ₀` 是库内 `SplitPrime`**（= ¬Max），
而 BdD 的典范分解只保证残差**没有 d-split**（= ¬Strong）⇒ **库内的要求比文献强** ✗
⇒ 若某个 `δ` 的典范残差恰是上面的类型（处处 ¬Strong 但某处 Max），
   则**不存在**满足库内 `SplitPrime` 的分解 ⇒ 该缺口**可疑（可能为假）** ✗。
⚠️ 精确范围：上面这些分离实例**都不是** `Σ_S λ_S·SplitMetric S`（`λ > 0`）的形状
（后者对成员必有 Strong ⇒ 必有 Max），故 **`weakCompatibilityRealization_gap` 的陈述未被这些实例直接威胁** ✓；
但那条缺口仍需要「非成员不是 Max」这一条（比「非成员 α = 0」更强），值得单独核 ✗。
"""
import itertools

def quads_of(A, B):
    return ((a, ap, b, bp) for a in A for ap in A for b in B for bp in B)

def is_max(d, A, B):
    for a, ap, b, bp in quads_of(A, B):
        P = d[a][ap] + d[b][bp]
        if not (P < max(d[a][b] + d[ap][bp], d[a][bp] + d[ap][b])):
            return False
    return True

def is_strong(d, A, B):
    for a, ap, b, bp in quads_of(A, B):
        P = d[a][ap] + d[b][bp]
        if not (P < d[a][b] + d[ap][bp] and P < d[a][bp] + d[ap][b]):
            return False
    return True

def splits(n):
    out = []
    for r in range(1, n):
        for A in itertools.combinations(range(n), r):
            B = tuple(sorted(set(range(n)) - set(A)))
            if B: out.append((tuple(sorted(A)), B))
    return out

def mk(n, vals):
    d = [[0] * n for _ in range(n)]; k = 0
    for i in range(n):
        for j in range(i + 1, n):
            d[i][j] = d[j][i] = vals[k]; k += 1
    return d

def search(n, grid):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    S = splits(n)
    cnt, ex = 0, []
    for vals in itertools.product(grid, repeat=len(pairs)):
        d = mk(n, vals)
        if any(is_strong(d, A, B) for A, B in S): continue
        wit = [(A, B) for A, B in S if is_max(d, A, B)]
        if wit:
            cnt += 1
            if len(ex) < 3: ex.append((vals, wit[:2]))
    return cnt, ex

def main():
    # ★ W14b（2026-10-12 协调侧加固）：本脚本原先【没有任何失败路径】（无条件 return 0）✗ ——
    #   于是 `scripts/msc/run_all.sh` 的"绿"对它**不携带信息** ✗。
    #   现按它**自己的结论句**（下面那句"计数 > 0 ⇒ …"）立判据：
    #   若某个网格**找不到**「处处非 Strong 但某处 Max」的见证（计数 ≤ 0），
    #   则本脚本的结论**不成立** ⇒ 必须**非零退出** ✗。
    failures = []
    for n, grid in ((4, (-1, 0, 1, 2)), (5, (0, 1, 2))):
        cnt, ex = search(n, grid)
        print(f"n={n} 穷尽网格{list(grid)}：『处处非 Strong 但某处 Max』的 δ 个数 = {cnt}")
        for vals, wit in ex:
            print(f"    例：独立值 {list(vals)}；Max 成立的 split 例 {wit}")
        if cnt <= 0:
            failures.append((n, grid, cnt))
    print()
    print("⇒ 计数 > 0 ⇒ 库内 `SplitPrime`（¬Max）**严格强于**文献 split-prime（¬Strong）")
    print("   ⇒ `canonicalSplitDecomposition_gap` 的残差条件比文献强 ⇒ 该缺口**可疑（可能为假）** ✗")
    print("   建议：按 ★D 判例 —— 原 `def` 逐字保留 ＋ 另立 `SplitPrimeStd`（¬Strong）")
    print("         ＋ 证 `SplitPrime → SplitPrimeStd` ✓（¬Max ⟹ ¬Strong）＋ 反向给反例 ✗")
    print("         ＋ 把 `canonicalSplitDecomposition_gap` 的正确形态以 `SplitPrimeStd` 重述 ✓")
    if failures:
        print()
        print("VERDICT: FAIL")
        for n, grid, cnt in failures:
            print(f"  ✗ n={n} 网格{list(grid)}：见证计数 = {cnt}（本脚本的结论要求 > 0）")
        return 1
    print("VERDICT: PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
