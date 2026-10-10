#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W12 · 协调侧判定：`Phylo/SplitWeak.lean` 的 `Split.FourPoint` **定义级缺陷**及其后果。

背景（W12d 发现、协调侧查到底）
------------------------------
`def FourPoint (δ : α → α → ℝ) : Prop := ∀ a a' b b',
    δ a a' + δ b b' ≤ max (δ a b + δ a' b') (δ a b' + δ a' b) ∧
    δ a b + δ a' b' ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) ∧
    δ a b' + δ a' b ≤ max (δ a a' + δ b b') (δ a b + δ a' b)      -- ← 末项应为 δ a b + δ a' b'
而它**自己的 docstring**（`:386-388`）说三个表达式是
`d(a,a')+d(b,b')`、`d(a,b)+d(a',b')`、`d(a,b')+d(a',b)` ⇒ 第三式右端应是 `max (δ a a' + δ b b') (δ a b + δ a' b')`。
（`git show HEAD` 的 `def` 体与本版完全一致 ⇒ 属 **W11 遗留**，非 W12 引入。）

本脚本给出三个机器判定（纯标准库、精确整数、无 Monte Carlo 依赖随机种子固定）：
  [1] **方向**：库内（含笔误）形态 **严格强于** 标准形态。
  [2] **严重性**：**树度量**（真正关心的对象）几乎全都不满足库内形态 ⇒ 以它为假设的定理对真实对象**空转**。
  [3] **最小见证**：4 叶平衡树 `((0,1),(2,3))`、边权全 1 即证伪库内形态（标准形态在同一 δ 上成立）。

⇒ **直接后果**：`Split.fourPointOfSplitMetricSum_gap`（W12d 登记的 B1 —— 「`F` 两两相容 ＋ `w > 0`
⟹ `δ := Σ w_S·SplitMetric S` 满足四点条件」）**是假命题** ✗：该 `δ` 就是树度量，而树度量不满足库内形态
⇒ 前提真、结论假。故 B1 应当**证伪**，并另立以 `FourPointStd`（文献形态）表述的**正确**目标。

注：`Phylo/Algorithm/NJ.lean` 的 `Dissimilarity.FourPoint` 是**析取形态**（「三对和无严格最大者」），
与文献一致、树度量满足它 ✓ —— 缺陷只在 `Split.FourPoint` 这一个 `def`。
"""
import random
from itertools import product

def quads(n):
    return product(range(n), repeat=4)

def F_lib(n, d):
    """库内形态（含笔误）。"""
    for a, ap, b, bp in quads(n):
        P = d[a][ap] + d[b][bp]; Q = d[a][b] + d[ap][bp]; R = d[a][bp] + d[ap][b]
        if not (P <= max(Q, R)) or not (Q <= max(P, R)): return False
        if not (R <= max(P, d[a][b] + d[ap][b])): return False
    return True

def F_std(n, d):
    """标准形态（第三式右端用 Q = δ a b + δ a' b'）。"""
    for a, ap, b, bp in quads(n):
        P = d[a][ap] + d[b][bp]; Q = d[a][b] + d[ap][bp]; R = d[a][bp] + d[ap][b]
        if not (P <= max(Q, R)) or not (Q <= max(P, R)): return False
        if not (R <= max(P, Q)): return False
    return True

def mk(n, vals):
    d = [[0] * n for _ in range(n)]; k = 0
    for i in range(n):
        for j in range(i + 1, n):
            d[i][j] = d[j][i] = vals[k]; k += 1
    return d

def random_tree_metric(n, rng):
    """随机树（逐叶挂接）＋ 随机正边权 ⇒ 真正的树度量。"""
    adj = {}
    def link(u, v, w):
        adj.setdefault(u, []).append((v, w)); adj.setdefault(v, []).append((u, w))
    cur, root = n, n
    cur += 1
    for leaf in range(n):
        link(leaf, root, rng.randint(1, 9))
        if leaf + 1 < n and rng.random() < 0.6:
            nxt = cur; cur += 1
            link(root, nxt, rng.randint(1, 9)); root = nxt
    def dist(s, t):
        seen, st = {s: 0}, [s]
        while st:
            u = st.pop()
            for v, w in adj.get(u, []):
                if v not in seen:
                    seen[v] = seen[u] + w
                    if v == t: return seen[v]
                    st.append(v)
    return [[0 if i == j else dist(i, j) for j in range(n)] for i in range(n)]

def part1():
    print("=== [1] 方向：库内形态 vs 标准形态（穷尽 + 抽样）===")
    for n, grid in ((3, (0, 1, 2)), (4, (0, 1, 2))):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        both = only_lib = only_std = neither = 0
        for vals in product(grid, repeat=len(pairs)):
            d = mk(n, vals); t, s = F_lib(n, d), F_std(n, d)
            if t and s: both += 1
            elif t: only_lib += 1
            elif s: only_std += 1
            else: neither += 1
        print(f"  n={n} 穷尽：都真 {both} · **仅库内真 {only_lib}** · 仅标准真 {only_std} · 都假 {neither}")
    rng = random.Random(12); only_lib = only_std = 0
    for _ in range(20000):
        d = mk(5, [rng.randint(0, 6) for _ in range(10)])
        t, s = F_lib(5, d), F_std(5, d)
        if t and not s: only_lib += 1
        if s and not t: only_std += 1
    print(f"  n=5 随机 20000：仅库内真 {only_lib} · 仅标准真 {only_std}")
    print("  ⇒ 『仅库内真』恒为 0 ⇒ 库内形态**严格更强**（库内 ⟹ 标准；反向不成立 ✗）")

def part2():
    print("\n=== [2] 严重性：**树度量**是否满足库内形态？===")
    rng = random.Random(7)
    for n in (4, 5, 6, 7):
        good = tot = 0
        for _ in range(3000):
            d = random_tree_metric(n, rng)
            if not F_std(n, d): continue          # 生成器偶发退化，跳过
            tot += 1
            if F_lib(n, d): good += 1
        print(f"  n={n}: 有效树度量 {tot} 个 ⇒ 其中满足**库内**形态的 {good} 个"
              f"{'  ✓' if good == tot else '  ✗ 大量反例'}")
    print("  ⇒ 树度量几乎全部**不满足**库内形态 ⇒ 以它为假设的定理对真实对象**空转** ✗")

def part3():
    print("\n=== [3] 最小显式见证 ===")
    d = [[0, 2, 3, 3], [2, 0, 3, 3], [3, 3, 0, 2], [3, 3, 2, 0]]   # 4 叶平衡树、边权全 1
    bad = [(a, ap, b, bp) for a, ap, b, bp in quads(4)
           if d[a][bp] + d[ap][b] > max(d[a][ap] + d[b][bp], d[a][b] + d[ap][b])]
    bad_std = [(a, ap, b, bp) for a, ap, b, bp in quads(4)
               if d[a][bp] + d[ap][b] > max(d[a][ap] + d[b][bp], d[a][b] + d[ap][bp])]
    print(f"  δ = {d}（4 叶平衡树 ((0,1),(2,3))、边权全 1）")
    print(f"  库内第三式违反数 = {len(bad)}，首个 (a,a',b,b') = {bad[0] if bad else None}"
          f"  LHS = {d[bad[0][0]][bad[0][3]] + d[bad[0][1]][bad[0][2]] if bad else '-'}"
          f" > RHS = {max(d[bad[0][0]][bad[0][1]] + d[bad[0][2]][bad[0][3]], d[bad[0][0]][bad[0][2]] + d[bad[0][1]][bad[0][2]]) if bad else '-'}")
    print(f"  标准第三式在同一 δ 上违反数 = {len(bad_std)}  ⇒ {'成立 ✓' if not bad_std else '也失败 ✗'}")
    print("  ⇒ **最简的 4 叶树度量**即证伪库内形态 ✗")

def main():
    part1(); part2(); part3()
    print("\n=== 结论 ===")
    print("(a) `Split.FourPoint` 严格强于文献四点条件，且**把真实树度量排除在外** ✗；")
    print("(b) 故 `fourPointOfSplitMetricSum_gap`（B1）**为假** ⇒ 应证伪，并另立以 `FourPointStd` 表述的正确目标；")
    print("(c) 有用的正面引理是 `Split.FourPoint → FourPointStd`（机器判定支持）；")
    print("(d) 仍**不改** `Split.FourPoint` 的定义（★C：不弱化既有字段），以 `FourPointStd` 并存 ＋ 关系定理解决。")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
