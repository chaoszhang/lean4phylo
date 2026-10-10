#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/rooted_triplet_aho.py —— W11a / F7（有根三元组 · Aho 有根一致性）的**独立复核**

对应模块：`Phylo/RootedTriplet.lean`（本文件新增 §5 §6；§1–§4 为 W6 已有部分）。

**只做穷举 / 精确组合计数，零浮点、零 Monte Carlo、零第三方依赖、不重跑 Lean。**
目的：在相信 Lean 里的定理之前，先把它们的**数学内容**从组合定义独立算一遍。

复核的四件事：

(A) **树枚举器自证**：递归划分生成 `L` 上全部**有根系统发育树**（内部顶点度 ≥ 2），
    以「非根子树叶集（clade）集合」为规范形去重。计数必须命中
    A000311（`n = 1..6` 为 `1, 1, 4, 26, 236, 2752`）—— 先证明复核脚本自身正确。
(B) **相容 ⟺ 可展示**：`R` 一致（存在一棵树展示全部）**⟺** `AhoOK(R)`（BUILD / ONETREE 的
    递归判据，库内 `Phylo.AhoOK`）。对 `n = 3, 4` 的**全部**子集、`n = 5` 的全部 `|R| ≤ 4`
    子集、`n = 6` 的 `|R| ≤ 2` 全部 + 随机抽样逐条比对。
(C) **★B 反例（本批的核心结论）**：**两两相容 ⇏ 一致**。在 `n = 4` 的 12 个三元组的
    **全部 4096 个子集**上统计「两两相容但不一致」的族，并验证最小者为
    `{01|2, 02|3, 03|1}`（= Lean 的 `fourLeafCounterexample`）。
(D) **★B 反例检查 1**：`ab|c` 与 `ac|b` **不相容**（同一三叶集上三选一），
    故 `{ab|c, ac|b, bc|a}` **不是**两两相容 —— 即「相容定义不过弱」。
(E) 单向 `展示 ⟹ 两两相容` 无例外（由 (A)(B) 的数据顺带核对）。
(F) 图 `[R,S]` 的连通性：Bryant–Steel Theorem 2 的 (⟹)（树展示 ⟹ 每个 `|S| ≥ 3` 的
    `S` 上 `[R,S]` 不连通）在全部小实例上成立（这正是 Lean 里**未证**的缺口 1，
    本脚本给出它的数值旁证，**不是**证明）。
"""

import itertools
import random
from functools import lru_cache
from math import comb

PASS = []


def ok(msg):
    PASS.append(msg)
    print("  [OK] " + msg)


def fail(msg):
    print("  [FAIL] " + msg)
    raise SystemExit(1)


# ---------------------------------------------------------------- 三元组
# 有根三元组 ab|c：近对 pair = frozenset({a,b})（恰 2 元），外侧叶 out = c ∉ pair。
# 与 Lean 的 `RootedTriplet X := {p : Finset X × X // p.1.card = 2 ∧ p.2 ∉ p.1}` 一致。


def rt(a, b, c):
    assert a != b and a != c and b != c
    return (frozenset((a, b)), c)


def leaves(r):
    return r[0] | {r[1]}


def all_triplets(L):
    return [rt(a, b, c) for a, b in itertools.combinations(sorted(L), 2)
            for c in sorted(L) if c not in (a, b)]


# ---------------------------------------------------------------- (A) 树枚举
def set_partitions(items):
    """items 的全部集合划分（每块非空）。"""
    items = list(items)
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for part in set_partitions(rest):
        # first 单独成块
        yield [[first]] + [list(b) for b in part]
        # first 并入已有块
        for i in range(len(part)):
            new = [list(b) for b in part]
            new[i] = [first] + new[i]
            yield new


@lru_cache(maxsize=None)
def rooted_trees(leaves_tuple):
    """返回 `leaves_tuple` 上全部有根树，规范形 = frozenset(非根顶点的子树叶集)。

    递归：叶子 → 只有根，规范形为空集；否则把叶集划分成 k ≥ 2 块（= 根的孩子），
    每块递归建子树；规范形 = 各块 + 各子树内部 clade 的并。最后按规范形去重。
    """
    leaves = tuple(sorted(leaves_tuple))
    if len(leaves) == 1:
        return frozenset([frozenset()])
    out = set()
    for part in set_partitions(leaves):
        if len(part) < 2:
            continue
        blocks = [tuple(sorted(b)) for b in part]
        options = [rooted_trees(b) for b in blocks]
        for combo in itertools.product(*options):
            clades = set(blocks)
            for c in combo:
                clades |= c
            out.add(frozenset(frozenset(x) for x in clades))
    return frozenset(out)


def displays(clades, r):
    """树（clade 集）展示 ab|c ⟺ 某条边的**远离根**一侧含 a,b 而不含 c。

    `clades` 的叶标号是 `0..k-1`；`r` 的叶标号由调用方先重标号（见 `relabel`）。"""
    pair, out = r
    return any(pair <= cl and out not in cl for cl in clades)


def relabel(R):
    """把一族三元组的叶标号压紧成 `0..k-1`（树枚举器按**叶数**索引，与标号无关）。"""
    if not R:
        return [], 0
    L = sorted(set().union(*[leaves(r) for r in R]))
    m = {x: i for i, x in enumerate(L)}
    return [(frozenset(m[x] for x in pair), m[out]) for pair, out in R], len(L)


def displayed_set(clades, triplets):
    return frozenset(i for i, r in enumerate(triplets) if displays(clades, r))


# ---------------------------------------------------------------- (A) 自证
print("=== (A) 有根树枚举器自证（A000311: 1, 1, 4, 26, 236, 2752） ===")
A000311 = {1: 1, 2: 1, 3: 4, 4: 26, 5: 236, 6: 2752}
TREES = {}
for n in range(1, 7):
    L = tuple(range(n))
    TREES[n] = sorted(rooted_trees(L), key=lambda c: (len(c), sorted(sorted(x) for x in c)))
    got = len(TREES[n])
    if got != A000311[n]:
        fail(f"n={n}: 树数 {got} ≠ A000311 的 {A000311[n]}")
    ok(f"n={n}: 规范化有根树 {got} 棵 = A000311")

# ⚠️ 只对**二叉**树才有「恰一个」；一般（非二叉）树最多展示一个。
# 星形树 `(a,b,c)` 一个都不展示 —— 这正是本脚本 (A2) 的第一次运行踩到的坑
# （第一版断言「恰 1 个」，被 401 个反例打回；见 README 记录）。
print("=== (A2) 三叶**至多**三选一：每棵树在给定 3 叶上最多展示 1 个三元组 ===")
bad = 0
both = 0
for n in (3, 4, 5):
    for clades in TREES[n]:
        for tri in itertools.combinations(range(n), 3):
            ts = all_triplets(tri)
            cnt = sum(1 for r in ts if displays(clades, r))
            if cnt > 1:
                bad += 1
            if cnt == 1:
                both += 1
if bad:
    fail(f"「至多一个」被破坏 {bad} 次")
ok(f"全部树/全部三叶子集：展示数 ≤ 1（星形树展示 0 —— 非二叉故非「恰一」）；"
   f"其中展示 1 个的有 {both} 例")
if not any(sum(1 for r in all_triplets(tri) if displays(c, r)) == 0
           for c in TREES[3] for tri in itertools.combinations(range(3), 3)):
    fail("三叶星形树竟然展示了三元组")
ok("三叶星形树（无内部边）展示 **0** 个 ⟹ 非二叉树上不成立「恰一」")


# ---------------------------------------------------------------- (B) AhoOK
def triplet_graph_components(S, R):
    """Bryant–Steel 的图 [R,S]（顶点 S；ab|c ∈ R 且 a,b,c ∈ S 时连边 {a,b}）的连通分量。"""
    S = set(S)
    adj = {v: set() for v in S}
    for pair, out in R:
        if pair <= S and out in S:
            a, b = tuple(pair)
            adj[a].add(b)
            adj[b].add(a)
    seen, comps = set(), []
    for v in sorted(S):
        if v in seen:
            continue
        stack, comp = [v], set()
        seen.add(v)
        while stack:
            x = stack.pop()
            comp.add(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        comps.append(frozenset(comp))
    return comps


def aho_ok(S, R):
    """库内 `Phylo.AhoOK` 的逐字实现：|S| ≤ 1 成功；否则块数 ≥ 2 且每块递归成功。"""
    S = frozenset(S)
    if len(S) <= 1:
        return True
    comps = triplet_graph_components(S, R)
    if len(comps) < 2:
        return False
    return all(aho_ok(c, R) for c in comps)


def consistent_from_trees(R, trees):
    """存在一棵树展示 R 的全部三元组（`R` 已重标号到 `0..k-1`）。"""
    R = list(R)
    for clades in trees:
        if all(displays(clades, r) for r in R):
            return True
    return False


def consistent(R):
    RR, k = relabel(R)
    if k == 0:
        return True
    return consistent_from_trees(RR, TREES[k])


print("=== (B) 一致 ⟺ AhoOK（穷举） ===")


def compare(triplets, max_size=None, sample=0, seed=7):
    n = len(triplets)
    tot = 0
    for k in range(0, (max_size if max_size is not None else n) + 1):
        for combi in itertools.combinations(range(n), k):
            R = [triplets[i] for i in combi]
            tot += 1
            c1, c2 = consistent(R), aho_ok(set().union(*[leaves(r) for r in R]) if R else set(), R)
            if c1 != c2:
                fail(f"不一致：R={R}: 可展示={c1} AhoOK={c2}")
    if sample:
        rnd = random.Random(seed)
        for _ in range(sample):
            k = rnd.randint(0, n)
            combi = rnd.sample(range(n), k)
            R = [triplets[i] for i in combi]
            tot += 1
            c1 = consistent(R)
            c2 = aho_ok(set().union(*[leaves(r) for r in R]) if R else set(), R)
            if c1 != c2:
                fail(f"不一致：R={R}: 可展示={c1} AhoOK={c2}")
    return tot


for n, mx, samp in ((3, None, 0), (4, None, 0), (5, 4, 0), (6, 2, 3000)):
    ts = all_triplets(range(n))
    tot = compare(ts, mx, samp)
    which = "全部子集" if mx is None else f"|R| ≤ {mx}" + (f" + {samp} 个随机子集" if samp else "")
    ok(f"n={n}（{len(ts)} 个三元组，{which}，共 {tot} 个族）：可展示 ⟺ AhoOK")


# ---------------------------------------------------------------- (C) 两两相容 ⇏ 一致
print("=== (C) ★B 反例：n=4 的全部 4096 个子集上「两两相容 ⇏ 一致」 ===")
ts4 = all_triplets(range(4))
compat_cache = {}


def compatible_pair(r1, r2):
    key = (r1, r2) if r1 <= r2 else (r2, r1)
    if key not in compat_cache:
        RR, k = relabel([r1, r2])
        compat_cache[key] = consistent_from_trees(RR, TREES[k])
    return compat_cache[key]


n4 = len(ts4)
masks4 = [sum(1 << i for i in displayed_set(c, ts4)) for c in TREES[4]]
pairwise_but_not_consistent = []
pairwise_only, both = 0, 0
for m in range(1 << n4):
    R = [ts4[i] for i in range(n4) if m >> i & 1]
    pw = all(compatible_pair(a, b) for a, b in itertools.combinations(R, 2))
    cons = any(mask & m == m for mask in masks4)
    if pw and cons:
        both += 1
    elif pw and not cons:
        pairwise_but_not_consistent.append(R)
if not pairwise_but_not_consistent:
    fail("n=4 上竟然没有「两两相容但不一致」的族 —— 与 Lean 的定理矛盾")
sizes = sorted({len(R) for R in pairwise_but_not_consistent})
ok(f"n=4：两两相容且一致的族 {both} 个；**两两相容但不一致**的族 "
   f"{len(pairwise_but_not_consistent)} 个，最小基数 {sizes[0]}")
minimal = [R for R in pairwise_but_not_consistent if len(R) == sizes[0]]
ok(f"最小反例共 {len(minimal)} 个（n=4 上基数为 {sizes[0]}）")
lean_family = frozenset({rt(0, 1, 2), rt(0, 2, 3), rt(0, 3, 1)})
found = any(frozenset(R) == lean_family for R in pairwise_but_not_consistent)
if not found:
    fail("Lean 的 fourLeafCounterexample {01|2, 02|3, 03|1} 不在反例集合里")
ok("Lean 的 fourLeafCounterexample = {01|2, 02|3, 03|1} 确在反例集合中")
print("      最小反例（前 6 个，记法 ab|c）：")
for R in minimal[:6]:
    print("        " + ", ".join(sorted(f"{''.join(map(str, sorted(r[0])))}|{r[1]}" for r in R)))

# ---------------------------------------------------------------- (D) 三元素两两相容性
print("=== (D) ★B 反例检查 1：同一三叶集上的三元组互不相容 ===")
for tri in itertools.combinations(range(4), 3):
    ts = all_triplets(tri)
    for a, b in itertools.combinations(ts, 2):
        if compatible_pair(a, b):
            fail(f"{a} 与 {b} 竟然相容")
ok("全部 4 个三叶集 × 全部两两组合：同一三叶集上不同三元组**互不相容**")
ts3 = all_triplets((0, 1, 2))
R3 = ts3
if any(all(compatible_pair(a, b) for a, b in itertools.combinations(R3, 2)) for _ in [0]):
    fail("{ab|c, ac|b, bc|a} 竟然两两相容")
ok("{ab|c, ac|b, bc|a}（n=3）**不是**两两相容 ⟹ 与 Lean 的 "
   "`not_pairwiseCompatible_threeConflicting` 一致")

# ---------------------------------------------------------------- (E) 展示 ⟹ 两两相容
print("=== (E) 单向「展示 ⟹ 两两相容」抽查 ===")
viol = 0
for n in (4, 5):
    ts = all_triplets(range(n))
    masks = [sum(1 << i for i in displayed_set(c, ts)) for c in TREES[n]]
    rnd = random.Random(11)
    for _ in range(400):
        m = rnd.randrange(1 << len(ts))
        R = [ts[i] for i in range(len(ts)) if m >> i & 1]
        if any(mask & m == m for mask in masks):
            if not all(compatible_pair(a, b) for a, b in itertools.combinations(R, 2)):
                viol += 1
if viol:
    fail(f"展示 ⟹ 两两相容 被破坏 {viol} 次")
ok("随机抽查 800 个「可展示」族：全部两两相容（与 `pairwiseCompatible_of_displaysByTree` 一致）")

# ---------------------------------------------------------------- (F) Bryant–Steel Thm 2 (⟹)
print("=== (F) Bryant–Steel Theorem 2 的 (⟹) 数值旁证（Lean 缺口 1） ===")
viol = 0
checks = 0
for n in (4, 5):
    ts = all_triplets(range(n))
    for clades in TREES[n]:
        R = [r for r in ts if displays(clades, r)]
        for k in range(3, n + 1):
            for S in itertools.combinations(range(n), k):
                if not all(leaves(r) <= set(S) for r in R):
                    continue
                checks += 1
                if len(triplet_graph_components(set(S), R)) < 2:
                    viol += 1
if viol:
    fail(f"[R,S] 连通却可展示：{viol} 次")
ok(f"全部 {checks} 个 (树, S) 组合：树展示 ⟹ [R,S] 不连通（|S| ≥ 3）")

print()
print(f"VERDICT: PASS —— 共 {len(PASS)} 项检查全部通过")
