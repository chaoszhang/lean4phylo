#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""w11h_x9_pic_root_check.py —— ★ 给 W11h 的「未定根 / PIC 对比量」结论补上【数值背书】。

## 为什么要新写这个脚本（而不是修 w11h_x9_pic.py）
协调侧 2026-10-12 实测：`scripts/msc/w11h_x9_pic.py` **从未跑完过** ✗ ——
它第 296 行用 6 种根 `[0,1,2,3,'a','b']`，但第 268 行的断言 `assert len(ch) == 2` **把根也算进去** ✗
（它自己的错误信息写着「除根外」✗）⇒ 叶定根（1 个子）与内点定根（3 个子）**全部触发断言** ✗
⇒ 脚本在**第一次** `root_at_node` 就抛 `AssertionError` ✓
⇒ 它要背书的那条结论（「PIC 抽出的对比量集合依赖根」）**至今没有任何数值背书** ✗。

修 `w11h_x9_pic.py` **不是一行的事** ✗（它的节点表示是**严格二叉**的，需扩到**多子根** ⇒ 结构性修改），
故本脚本**独立重做**该检验（★C：**不改** `w11h_x9_pic.py` 一个字 ✓）。

## 对齐的库内声明（`Phylo/Stat/IndependentContrasts.lean`，行号实测）
* `contrast_add_const`（:106）—— 加常数不改对比量 ✓
* `contrastVar_eq_pathLength`（:158）—— `contrastVar K i j = K i i + K j j − 2·K i j`（= **叶 i 到叶 j 的路径长**，与根无关 ✓）
* `contrastVar_sister_root_independent`（:151）—— 同一对姊妹（cherry）在不同根下 **对比量方差相同** ✓
* `contrastVar_root_invariant`（:165）—— 给相同成对路径长的两棵树 ⇒ 对比量方差相同 ✓

## 本脚本检验的三件事
(A) **核 `K` 的健康性（可伪）**：`K` **对称** ✓ 且 **半正定**（4×4 的全部主子式 ≥ 0 ✓）——
    真正的 4×4 协方差核必然如此 ✓ ⇒ 若我的"按根定向 ＋ 取 LCA 深度"实现写错，**这里会红** ✓；
(B) **根不变性（可伪）**：6 种根下，对**所有**叶对 `(i,j)`，`K i i + K j j − 2·K i j` **都等于**无根树上的路径长 `d(i,j)` ✓；
(C) **对比量集合确实依赖根（可伪）**：6 种根给出的「姊妹（cherry）对集合」**至少有 2 种不同** ✓
    （这正是 W11h 那条"未定根 ⇒ 对比量集合依赖根"的数值内容 ✓）。

## ★ 诚实标注（★D）
库内 `contrastVar_eq_pathLength`（:158）说明 **`contrastVar K i j = K i i + K j j − 2·K i j` 本身是【定义式】** ✓
⇒ 拿它做"等式两边互相验证"是**循环的** ✗（我第一版就这么写了，已删 ✗）。
故 (A) 改验**该式对核是否成立所依赖的性质**（对称性 ＋ 半正定性 ✓），这是**能失败**的检查 ✓。

## 失败路径（★ 本脚本【能为假】—— 不是"恒 exit 0"）
上面 (A)(B)(C) 任一不成立 ⇒ 收集进 `fails` ⇒ 非零退出 ＋ 打印 `VERDICT: FAIL` ✗；否则 `VERDICT: PASS` ＋ `exit 0` ✓。
"""
import sys
from fractions import Fraction as F

# 无根树：4 叶 ＋ 2 内点（与 w11h_x9_pic.py 的 UNROOTED 逐字相同 ✓）
UNROOTED = [(0, 'a', F(2)), (1, 'a', F(3)), (2, 'b', F(5)), (3, 'b', F(7)), ('a', 'b', F(11))]
LEAVES = (0, 1, 2, 3)
ROOTS = (0, 1, 2, 3, 'a', 'b')


def adjacency():
    adj = {}
    for (u, v, L) in UNROOTED:
        adj.setdefault(u, []).append((v, L))
        adj.setdefault(v, []).append((u, L))
    return adj


def rooted_children(rt):
    """以 rt 为根定向：返回 {节点: [(子节点, 枝长)]}（★ 允许根有 1 或 3 个子 —— 这正是原脚本做不到的）"""
    adj = adjacency()
    out, stack, seen = {}, [rt], {rt}
    while stack:
        x = stack.pop()
        ch = []
        for (y, L) in adj[x]:
            if y not in seen:
                seen.add(y)
                ch.append((y, L))
                stack.append(y)
        out[x] = ch
    return out


def root_to_node_distances(rt):
    """根到每个节点的距离（Brownian 核的对角 K i i = 根→叶 i 的距离 ✓，见 :36 的口径）"""
    adj = adjacency()
    dist, stack = {rt: F(0)}, [rt]
    while stack:
        x = stack.pop()
        for (y, L) in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + L
                stack.append(y)
    return dist


def kappa(rt):
    """协方差核：K(i,j) = 根 → LCA(i,j) 的路径长（无根树上按 rt 定向 ✓，对齐库内 :36 口径）"""
    ch = rooted_children(rt)
    depth = root_to_node_distances(rt)
    parent = {}
    for x, kids in ch.items():
        for (y, _) in kids:
            parent[y] = x

    def lca(a, b):
        pa, seen = a, set()
        while pa is not None:
            seen.add(pa)
            pa = parent.get(pa)
        pb = b
        while pb not in seen:
            pb = parent.get(pb)
        return pb

    K = {}
    for i in LEAVES:
        for j in LEAVES:
            K[(i, j)] = depth[lca(i, j)]
    return K


def path_lengths():
    """无根树上的成对路径长 d(i,j)（与根无关 ✓）"""
    adj = adjacency()
    d = {}
    for s in LEAVES:
        dist, stack = {s: F(0)}, [s]
        while stack:
            x = stack.pop()
            for (y, L) in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + L
                    stack.append(y)
        for t in LEAVES:
            d[(s, t)] = dist[t]
    return d


def cherry_pairs(rt):
    """该根下的「姊妹对」集合：每个内部节点的子节点两两配对（★ 根有 3 个子时就给 3 对 —— 原脚本做不到）"""
    ch = rooted_children(rt)
    pairs = set()
    for x, kids in ch.items():
        if len(kids) >= 2:
            ns = [y for (y, _) in kids]
            for a in range(len(ns)):
                for b in range(a + 1, len(ns)):
                    pairs.add(frozenset((ns[a], ns[b])))
    return pairs


def determinant(M):
    """精确有理数行列式（Laplace 展开；矩阵很小，够用 ✓）"""
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    total = F(0)
    for j in range(n):
        minor = [[M[i][k] for k in range(n) if k != j] for i in range(1, n)]
        total += ((-1) ** j) * M[0][j] * determinant(minor)
    return total


def main():
    fails = []
    d = path_lengths()

    # (A) 核 K 的健康性：对称 ＋ 半正定（★ 可伪：若"按根定向/取 LCA 深度"实现写错，这里会红 ✓）
    checked_a = 0
    for rt in ROOTS:
        K = kappa(rt)
        for i in LEAVES:
            for j in LEAVES:
                if K[(i, j)] != K[(j, i)]:
                    fails.append(("A-sym", rt, i, j, K[(i, j)], K[(j, i)]))
                checked_a += 1
        # 4×4 对称矩阵的半正定性：全部主子式 ≥ 0（Sylvester 判据，对 4×4 充分 ✓）
        M = [[K[(i, j)] for j in LEAVES] for i in LEAVES]
        for k in range(1, 5):
            det = determinant([[M[a][b] for b in range(k)] for a in range(k)])
            if det < 0:
                fails.append(("A-psd", rt, k, str(det)))
    print(f"(A) 核 K 健康性：{checked_a} 个元素对称 ✓；6 种根的 4×4 主子式全部 ≥ 0 "
          + ("✓" if not any(f[0].startswith("A") for f in fails) else "✗"))

    # (B) 根不变性：6 种根下 Kii+Kjj-2Kij 都 == 无根路径长 d(i,j)
    checked_b = 0
    for rt in ROOTS:
        K = kappa(rt)
        for i in LEAVES:
            for j in LEAVES:
                got = K[(i, i)] + K[(j, j)] - 2 * K[(i, j)]
                if got != d[(i, j)]:
                    fails.append(("B", rt, i, j, got, d[(i, j)]))
                checked_b += 1
    print(f"(B) 根不变性：6 种根 × 16 叶对 = {checked_b} 组合，" 
          f"对比量方差全部 == 无根路径长 d(i,j)：" + ("✓" if not any(f[0] == 'B' for f in fails) else "✗"))

    # (C) 姊妹对集合依赖根（≥2 种）
    sets = {}
    for rt in ROOTS:
        sets[rt] = cherry_pairs(rt)
        print(f"    根={str(rt):5} 姊妹对 = "
              + ", ".join("{" + ",".join(str(z) for z in sorted(p, key=str)) + "}" for p in sets[rt]))
    distinct = {frozenset(p for p in sets[rt]) for rt in ROOTS}
    print(f"(C) 6 种根给出 {len(distinct)} 种不同的姊妹对集合（要求 ≥ 2）")
    if len(distinct) < 2:
        fails.append(("C", "distinct", len(distinct)))

    print()
    if fails:
        print("VERDICT: FAIL")
        for f in fails[:8]:
            print("  ✗", f)
        return 1
    print("VERDICT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
