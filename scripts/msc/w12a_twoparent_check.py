#!/usr/bin/env python3
"""W12a · `two_parent_trees_gap` 的**真值机器穷举**（★D：先核命题，再决定证/证伪）。

模型（与 `Phylo/SupertreeLimits.lean` 的定义逐条对应）：
* 无根树 ↔ **两两相容**的非平凡 split 集（`Cladogram` 的 `IsSplitOf` 只看 split 系统；
  平凡 split 每棵树都展示、且 `sig` 把它们映到平凡 split，故对下述判据无影响）；
* `DisplaysQP T q` ↔ 「存在 S 中一条 split，把 q 的两个配对分到两侧」；
* `Split.relabel sig s` ↔ 对 split 的两侧逐点作用 `sig`；
* `sig = Equiv.swap 1 5 * Equiv.swap 2 4`（= 原文的 2↔6、3↔5，0-based）。

纯标准库、精确整数/集合、无 Monte Carlo。运行：python3 w12a_twoparent_check.py

退出码：0 ＝ 下面各项判定（split 数 25 / ★parent 数 = 2 且显式构造核验通过 / 判据一二为真 /
分类定理无反例）全部复现（打印判定词）；1 ＝ 有判定失败并逐条列出。
"""
import sys
from itertools import combinations

N = 6
LAB = tuple(range(N))

# ---------------------------------------------------------------- 基础对象
def all_splits(n):
    """无根 split（两侧都 >= 2），表示为 frozenset({A, B})（无序）。"""
    seen, out = set(), []
    for k in range(2, n - 1):
        for A in combinations(range(n), k):
            A = frozenset(A)
            B = frozenset(range(n)) - A
            if len(B) < 2:
                continue
            key = frozenset({A, B})
            if key not in seen:
                seen.add(key)
                out.append(key)
    return out


SPLITS = all_splits(N)


def sides(s):
    a, b = tuple(s)
    return a, b


def compatible(s, t):
    A, B = sides(s)
    C, D = sides(t)
    return not (A & C and A & D and B & C and B & D)


def all_compatible_families():
    """枚举全部两两相容族（相容图上的全部团）。"""
    res = []

    def dfs(i, cur):
        res.append(frozenset(cur))
        for j in range(i, len(SPLITS)):
            if all(compatible(SPLITS[j], x) for x in cur):
                dfs(j + 1, cur + [SPLITS[j]])

    dfs(0, [])
    return res


# ---------------------------------------------------------------- 树（显式构造，★B 见证）
def build_tree(fam):
    """由相容族显式构造树：返回 (顶点集, 边集, 叶->顶点, 内部顶点集)。

    用 [0] 号 taxon 定根：把每条 split 中**不含 0** 的一侧当作 cluster（这是标准做法，
    无根树由此变成以 0 为「根」的分层结构）。若 0 同时…不可能：0 恰在一侧。
    """
    clusters = []
    for s in fam:
        A, B = sides(s)
        c = A if 0 not in A else B
        if 0 in c:  # 0 在两侧不可能，保险
            continue
        clusters.append(c)
    clusters = sorted(set(clusters), key=lambda c: -len(c))

    edges = []
    internal = []
    # 递归：顶点 u 代表叶集 leafset；其孩子 = 极大真子 cluster；其余叶直接挂在 u 上
    def rec(leafset, parent, name):
        my = name
        internal.append(my)
        if parent is not None:
            edges.append((parent, my))
        inside = [c for c in clusters if c < leafset and c <= leafset]
        maximal = [c for c in inside if not any(c < d and d <= leafset for d in inside)]
        covered = set()
        for c in maximal:
            covered |= rec(c, my, len(internal) + 10000)  # 名字仅用于区分
        direct = leafset - set().union(*maximal) if maximal else leafset
        for x in sorted(direct):
            if x == min(leafset) and x == 0 and parent is not None and len(leafset) > 1:
                pass
            edges.append((my, ('leaf', x)))
        return leafset

    # 顶点命名：内部点用递增编号（0,1,2,…），叶用 ('leaf', x)
    counter = [0]

    def rec2(leafset, parent):
        my = counter[0]
        counter[0] += 1
        internal.append(my)
        if parent is not None:
            edges.append((parent, my))
        inside = [c for c in clusters if c < leafset]
        maximal = [c for c in inside if not any(c < d and d <= leafset for d in inside)]
        for c in maximal:
            rec2(c, my)
        direct = leafset - set().union(*maximal) if maximal else leafset
        for x in sorted(direct):
            edges.append((my, ('leaf', x)))
        return my

    root = rec2(frozenset(range(N)), None)
    return root, edges, counter[0]


def tree_splits_from_edges(edges, nverts):
    """由边集算出每一条边的叶侧 split（返回无序 split 的集合）。"""
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    out = set()
    for u, v in edges:
        # 删去 (u,v) 后从 u 出发能到达的叶集
        seen, stack, leaves = {u}, [u], set()
        while stack:
            x = stack.pop()
            if isinstance(x, tuple):  # 叶
                leaves.add(x[1])
                continue
            for y in adj[x]:
                if (x == u and y == v) or (x == v and y == u):
                    continue
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        A = frozenset(leaves)
        B = frozenset(range(N)) - A
        if len(A) >= 2 and len(B) >= 2:
            out.add(frozenset({A, B}))
    return out


def validate_tree(fam):
    """★B：显式构造该族的树并核验「树合法 + split 系统恰为 fam」。"""
    root, edges, nv = build_tree(fam)
    # 合法树：边数 = 顶点数 - 1（顶点 = nv 内部点 + 6 叶）
    V = nv + N
    if len(edges) != V - 1:
        return False, f"edge count {len(edges)} != V-1 {V-1}"
    # 连通性
    adj = {}
    for u, v in edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    seen, stack = {root}, [root]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                stack.append(y)
    if len(seen) != V:
        return False, "not connected"
    # 度：叶 1、内部 >= 3
    for x in adj:
        if isinstance(x, tuple):
            if len(adj[x]) != 1:
                return False, f"leaf {x} degree {len(adj[x])}"
    for x in adj:
        if not isinstance(x, tuple) and len(adj[x]) < 3:
            return False, f"internal {x} degree {len(adj[x])} < 3"
    got = tree_splits_from_edges(edges, nv)
    if got != set(fam):
        return False, f"split set mismatch: got {sorted(map(str,got))} vs {sorted(map(str,fam))}"
    return True, "ok(V=%d,E=%d)" % (V, len(edges))


# ---------------------------------------------------------------- 判据
Q1 = frozenset({frozenset({0, 1}), frozenset({3, 4})})   # (12)(45)
Q2 = frozenset({frozenset({2, 3}), frozenset({0, 5})})   # (34)(16)
Q3 = frozenset({frozenset({4, 5}), frozenset({1, 2})})   # (56)(23)
PROF = [Q1, Q2, Q3]

# sig = (1 5)(2 4)
SIG = {0: 0, 1: 5, 2: 4, 3: 3, 4: 2, 5: 1}


def displays(fam, q):
    """树 fam 是否展示 quartet q（q 是两个配对的集合）。"""
    p1, p2 = tuple(q)
    for s in fam:
        A, B = sides(s)
        if (p1 <= A and p2 <= B) or (p2 <= A and p1 <= B):
            return True
    return False


def relabel_split(s):
    A, B = sides(s)
    return frozenset({frozenset(SIG[x] for x in A), frozenset(SIG[x] for x in B)})


def relabel_family(fam):
    return frozenset(relabel_split(s) for s in fam)


def subset(fam1, fam2):
    return set(fam1) <= set(fam2)


def show(fam):
    return sorted(sorted(map(sorted, s)) for s in fam)


def main():
    fails = []
    print("=" * 74)
    print("W12a · `two_parent_trees_gap` 真值机器穷举（6 taxa，无根树 ↔ 相容 split 族）")
    print("=" * 74)
    print(f"非平凡 split 数 = {len(SPLITS)}（理论值 2*C(6,2)/2+… = 25 ✓）")
    if len(SPLITS) != 25:
        fails.append(f"非平凡 split 数 = {len(SPLITS)} ≠ 25（6 taxa 的理论值）")
    fams = all_compatible_families()
    print(f"两两相容族总数 = {len(fams)}")
    # 最大尺寸
    mx = max(len(f) for f in fams)
    print(f"最大族大小 = {mx}（= n-3 = 3，即 binary 树）")
    if mx != N - 3:
        fails.append(f"最大族大小 = {mx} ≠ n-3 = {N-3}（Semple–Steel：binary ⟺ |fam| = n-3）")

    parents = [f for f in fams if all(displays(f, q) for q in PROF)]
    print(f"\n★ **parent tree 数 = {len(parents)}**（原文 Figure 1 说 2）")
    if len(parents) != 2:
        fails.append(f"parent tree 数 = {len(parents)} ≠ 2（原文 Figure 1 / 本脚本的核心事实）")
    for i, p in enumerate(parents):
        ok, msg = validate_tree(p)
        print(f"  P{i+1}: {show(p)}   显式构造核验: {'✓' if ok else '✗'} {msg}")
        if not ok:
            fails.append(f"P{i+1}: ★B 显式构造核验失败（{msg}）")
    if len(parents) < 2:
        print()
        print("VERDICT: FAIL")
        for m in fails:
            print("   ✗ " + m)
        print("   ✗ parent tree 数 < 2 ⇒ 后续『判据一/二』无法构造 T₁、T₂")
        return 1

    print("\n" + "=" * 74)
    print("判据一（原 `def two_parent_trees_gap` 第 3 条）：T₂ 的 split 系统 = sig(T₁ 的)")
    print("判据二（原 `def two_parent_trees_gap` 第 4 条）：每个 parent 都含 T₁ 或 T₂ 的 split 系统")
    print("=" * 74)
    ok_any = False
    for i, p in enumerate(parents):
        q = relabel_family(p)
        if q not in parents:
            print(f"  P{i+1}: sig(P{i+1}) 不是 parent ⇒ 该对不满足第 3 条")
            continue
        # 第 4 条
        bad = [T for T in parents if not (subset(p, T) or subset(q, T))]
        print(f"  P{i+1}: sig(P{i+1}) = P{parents.index(q)+1} 是 parent ✓（第 3 条成立）；"
              f"第 4 条 {'✓ 成立' if not bad else '✗ 失败'}")
        if bad:
            for T in bad:
                print(f"       反例：T = {show(T)} 既不含 P{i+1} 也不含 sig(P{i+1})")
        else:
            ok_any = True
    print(f"\n★ 原 `def two_parent_trees_gap` 机器判定：{'**真** ✓' if ok_any else '**假** ✗（可证伪）'}")
    if not ok_any:
        fails.append("原 `def two_parent_trees_gap` 的判据一/二在 6 taxa 上**无**满足对 ⇒ "
                     "与脚本自身打印的『真』不一致（须按 ★D 重新定性）")

    print("\n" + "=" * 74)
    print("另核：`…_correct_shape` 的第 ②（每个 parent 的 split 系统**恰**是 T₁ 或 T₂ 的）")
    print("=" * 74)
    ok_shape = False
    for i, p in enumerate(parents):
        q = relabel_family(p)
        if q not in parents:
            continue
        bad = [T for T in parents if not (set(T) == set(p) or set(T) == set(q))]
        print(f"  P{i+1}/sig(P{i+1}): 第 ② {'✓ 成立' if not bad else '✗ 失败'}"
              + ("" if not bad else f"（反例 {len(bad)} 个，例如 {show(bad[0])}）"))
        if not bad:
            ok_shape = True
    print(f"★ `…_correct_shape` 机器判定：{'**真** ✓' if ok_shape else '**假** ✗'}")
    if not ok_shape:
        fails.append("`…_correct_shape` 第 ② 无满足对 ⇒ 与脚本自身打印的『真』不一致")

    # ------------------------------------------------------------------ ★D-2
    print("\n" + "=" * 74)
    print("★D-2（W12a12）**分类定理**：" + "`SBD.two_parent_trees_classification`")
    print("   每个 parent tree 的每条 split 要么平凡、要么落在 P1 ∪ P2 内")
    print("=" * 74)
    P1, P2 = parents[0], parents[1]
    union = set(P1) | set(P2)
    # 模型层面的精确对应：树 ↔ 相容族；「平凡 split」由任何树的叶边展示，
    # 故非平凡部分只需检查「展示 prof 的族的每条 split ∈ P1 ∪ P2」。
    viol = []
    for f in fams:
        if all(displays(f, q) for q in PROF):
            extra = [s for s in f if s not in union]
            if extra:
                viol.append((f, extra))
    print(f"  检查了 {len(fams)} 个相容族；展示 prof 的族中，含 P1∪P2 之外 split 的：{len(viol)} 个")
    for f, extra in viol:
        print(f"    ✗ 反例 F = {show(f)}，越界 split = {show(frozenset(extra))}")
    print(f"  ⇒ 分类定理（非平凡部分）机器判定：{'**假** ✗（可证伪）' if viol else '**真** ✓'}")
    if viol:
        fails.append(f"分类定理（非平凡部分）有 {len(viol)} 个反例，例如 "
                     f"{show(viol[0][0])}（越界 split {show(frozenset(viol[0][1]))}）")
    # 附：把「任意族 ⊇ 某个 parent」这一更强形式也核一遍（第 4 条的一般形态）
    strong = [f for f in fams if not (subset(P1, f) or subset(P2, f))]
    print(f"  附核（更强形态）：不含 P1 也不含 P2 的相容族 = {len(strong)} 个"
          + ("" if not strong else f"，例如 {show(strong[0])}"))
    # 附：parent 族的规模与「最大族大小」的关系（Semple–Steel：binary ⟺ |fam| = n-3）
    print(f"  附核：两个 parent 族的大小 = {[len(p) for p in parents]}（n-3 = 3 ✓）")
    if any(len(p) != N - 3 for p in parents):
        fails.append(f"parent 族大小 = {[len(p) for p in parents]} ≠ n-3 = {N-3}")
    if fails:
        print()
        print("VERDICT: FAIL")
        for m in fails:
            print("   ✗ " + m)
        return 1
    print()
    print("VERDICT: PASS（非平凡 split 25 / 相容族 236 / ★parent 数 = 2 且两个 parent 的"
          "显式构造核验通过 / 判据一二为真 / 分类定理零反例）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
