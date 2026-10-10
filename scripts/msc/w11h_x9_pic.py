#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W11h / X9 —— 系统发生独立对比（PIC, Felsenstein 1985a）的**精确有理数穷举**核验。

文献：`references/md/Felsenstein1985a_PhylogeniesComparativeMethod.md`（行号指该文件）

    :370-374  相邻（姊妹）叶的对比量独立 —— 因为只涉及**不相交**的枝集合
    :376-385  布朗运动：每条枝增量独立，方差 ∝ 枝长
    :387-391  对比量 X_i - X_j 期望 0、方差 = v_i + v_j；除以标准差 ⇒ 单位方差
    :478-494  ★★ 算法内核步 1-4：取对比量 /（式 (3)）加权平均合并 / 枝长加长 v_k + v_i v_j/(v_i+v_j)
    :496-503  重复步 1-4 ⇒ n 叶抽出 n-1 个对比量；任意树形（含 multifurcation，:501-503）

Lean 对应文件：`Phylo/Stat/IndependentContrasts.lean`（每节注释标出对应定理名）。

**纯标准库**（fractions / itertools），**精确有理数**，**无 Monte Carlo**（全部穷举）。
运行：`python3 scripts/msc/w11h_x9_pic.py`
"""

from fractions import Fraction as F
from itertools import product

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  [FAIL] " + msg)
    return bool(cond)


# ---------------------------------------------------------------------------
# 0. 有根带权二叉树 + 协方差核 + 线性形式的方差/协方差
#    树：('L', label) | ('N', v_left, T_left, v_right, T_right)
#    v_* 是该子节点**下方**的枝长（根没有上方枝长）
#    核：K(i,j) = 根 → LCA(i,j) 的路径长（文献 :387-389）
# ---------------------------------------------------------------------------
def leaves(T):
    if T[0] == 'L':
        return [T[1]]
    return leaves(T[2]) + leaves(T[4])


def paths(T):
    out = {}

    def go(t, acc):
        if t[0] == 'L':
            out[t[1]] = list(acc)
        else:
            go(t[2], acc + [t[1]])
            go(t[4], acc + [t[3]])

    go(T, [])
    return out


def kernel(T):
    P = paths(T)
    ls = list(P)
    K = {}
    for i in ls:
        for j in ls:
            s = F(0)
            for x, y in zip(P[i], P[j]):
                if x != y:
                    break
                s += x
            K[(i, j)] = s
    return ls, K


def cov_of_forms(K, f, g, ls):
    return sum((f.get(i, F(0)) * g.get(j, F(0)) * K[(i, j)] for i in ls for j in ls), F(0))


def contrast_form(i, j):
    return {i: F(1), j: F(-1)}


def cherries(T):
    """所有 (共同祖先节点, i, j, v_i, v_j)：两子女都是叶。"""
    out = []

    def go(t):
        if t[0] == 'L':
            return
        _, vl, tl, vr, tr = t
        if tl[0] == 'L' and tr[0] == 'L':
            out.append((t, tl[1], tr[1], vl, vr))
        go(tl)
        go(tr)

    go(T)
    return out


def clades(T):
    out = []

    def go(t):
        if t[0] == 'L':
            return
        out.append((t, set(leaves(t))))
        go(t[2])
        go(t[4])

    go(T)
    return out


def incomparable_clade_pairs(T):
    ns = clades(T)
    res = []
    for i in range(len(ns)):
        for j in range(i + 1, len(ns)):
            A, B = ns[i][1], ns[j][1]
            if not (A & B) and not (A <= B) and not (B <= A):
                res.append((sorted(A), sorted(B)))
    return res


# --- 形状与枝长赋值的穷举 ---
def shapes(n):
    if n == 1:
        yield ('L', 0)
        return
    for k in range(1, n):
        for L in shapes(k):
            for R in shapes(n - k):
                yield ('N', None, L, None, R)


def relabel(T, ctr):
    if T[0] == 'L':
        return ('L', ctr[0]), (ctr[0] + 1,)
    l, c1 = relabel(T[2], ctr)
    r, c2 = relabel(T[4], c1)
    return ('N', None, l, None, r), c2


def n_slots(T):
    if T[0] == 'L':
        return 0
    return 2 + n_slots(T[2]) + n_slots(T[4])


def fill(T, vals, idx):
    if T[0] == 'L':
        return T
    vl = vals[idx[0]]
    idx[0] += 1
    tl = fill(T[2], vals, idx)
    vr = vals[idx[0]]
    idx[0] += 1
    tr = fill(T[4], vals, idx)
    return ('N', vl, tl, vr, tr)


def iter_trees(n, values):
    """穷举：n 叶的全部形状 × 全部枝长赋值（values 的笛卡尔幂）。"""
    for sh in shapes(n):
        sh, _ = relabel(sh, (0,))
        for vals in product(values, repeat=n_slots(sh)):
            yield fill(sh, list(vals), [0])


# ---------------------------------------------------------------------------
# 1. 姊妹叶对比量（文献 :387-391, :481）
#    Lean: contrastVar_sister / contrastVar_sister_scaled / picStep (1)
# ---------------------------------------------------------------------------
def test_cherry_variance(n, values, tag):
    nt = nc = 0
    for T in iter_trees(n, values):
        nt += 1
        ls, K = kernel(T)
        for (_k, i, j, vi, vj) in cherries(T):
            nc += 1
            var = cov_of_forms(K, contrast_form(i, j), contrast_form(i, j), ls)
            if not check(var == vi + vj, "cherry Var != vi+vj (%s,%s,%s)" % (var, vi, vj)):
                return
            if not check(var / (vi + vj) == 1, "单位方差失败"):
                return
    print("  [1] 姊妹叶：Var(X_i-X_j) = v_i+v_j 且 /(v_i+v_j) = 1 —— %s：%d 棵树 / %d cherry ✓"
          % (tag, nt, nc))


# ---------------------------------------------------------------------------
# 2. ★★ 两两不相关：枝集合不相交的两个 clade 内的对比量协方差 = 0（文献 :370-374）
#    Lean: contrastCov_eq_zero_of_cross_eq / contrastCov_disjoint_cherries
# ---------------------------------------------------------------------------
def test_disjoint_clades(n, values, tag):
    cnt = 0
    for T in iter_trees(n, values):
        ls, K = kernel(T)
        for A, B in incomparable_clade_pairs(T):
            for i, j in product(A, repeat=2):
                if i >= j:
                    continue
                for p, q in product(B, repeat=2):
                    if p >= q:
                        continue
                    c = cov_of_forms(K, contrast_form(i, j), contrast_form(p, q), ls)
                    cnt += 1
                    if not check(c == 0, "不相交 clade 的对比量协方差 != 0：%s" % (c,)):
                        return
    print("  [2] ★★ 不相交 clade 的对比量协方差 = 0 —— %s：%d 组 ✓" % (tag, cnt))


# ---------------------------------------------------------------------------
# 3. ★B 反例检查：「任意两对叶的对比量都独立」是**假**的
#    （文献 :371-374 只覆盖枝集合不相交的两对叶）
#    Lean: contrastCov_nonsister_eq_pendant / contrastCov_nonsister_ne_zero /
#          K6num_nonsister_eq (= 1/2) / K6num_nonsister_ne_zero
# ---------------------------------------------------------------------------
def test_counterexample():
    # 最小反例：三叶树 ((0:1/2, 1:1/3):1, 2:1)，Cov(X0-X1, X0-X2) 应为叶枝长 v0 = 1/2
    ch = ('N', F(1, 2), ('L', 0), F(1, 3), ('L', 1))
    T = ('N', F(1), ch, F(1), ('L', 2))
    ls, K = kernel(T)
    c = cov_of_forms(K, contrast_form(0, 1), contrast_form(0, 2), ls)
    check(c == F(1, 2), "反例数值应为 v0 = 1/2，实得 %s" % c)
    check(c != 0, "反例应非零")
    print("  [3] ★B 反例（最小）：Cov(X0-X1, X0-X2) = %s = 叶枝长 v0 ≠ 0 ⇒ "
          "「任意两对叶都独立」为假 ✓" % c)
    # 穷举 4 叶（枝长 1,2,3）：统计非零协方差，并核对「共享恰一片叶」的情形必非零
    nz = share1 = 0
    examples = []
    for T in iter_trees(4, [F(1), F(2), F(3)]):
        ls, K = kernel(T)
        for i, j in product(ls, repeat=2):
            if i >= j:
                continue
            for p, q in product(ls, repeat=2):
                if p >= q or {i, j} == {p, q}:
                    continue
                cc = cov_of_forms(K, contrast_form(i, j), contrast_form(p, q), ls)
                if cc != 0:
                    nz += 1
                    if len({i, j} & {p, q}) == 1:
                        share1 += 1
                        if len(examples) < 3:
                            examples.append((i, j, p, q, cc))
    check(nz > 0, "4 叶穷举里应存在非零协方差")
    check(share1 > 0, "共享恰一片叶的两对叶必须存在非零协方差")
    print("      4 叶穷举（1,2,3 枝长）：非零协方差 %d 组，其中两对共享恰一片叶的 %d 组，"
          "例 %s" % (nz, share1, examples))


# ---------------------------------------------------------------------------
# 4. ★B 未定根：对比量取值与方差与根无关；但 PIC 抽出的对比量**集合**依赖根
#    Lean: contrast_add_const / contrastVar_sister_root_independent /
#          contrastVar_eq_pathLength / contrastVar_root_invariant
# ---------------------------------------------------------------------------
UNROOTED = [(0, 'a', F(2)), (1, 'a', F(3)), (2, 'b', F(5)), (3, 'b', F(7)), ('a', 'b', F(11))]


def root_at_node(rt):
    adj = {}
    for (u, v, L) in UNROOTED:
        adj.setdefault(u, []).append((v, L))
        adj.setdefault(v, []).append((u, L))

    def go(x, parent):
        ch = [(y, L) for (y, L) in adj[x] if y != parent]
        if not ch:
            return ('L', x)
        assert len(ch) == 2, "除根外内部顶点度应为 3"
        (a, la), (b, lb) = ch
        return ('N', la, go(a, x), lb, go(b, x))

    return go(rt, None)


def unrooted_distances():
    adj = {}
    for (u, v, L) in UNROOTED:
        adj.setdefault(u, []).append((v, L))
        adj.setdefault(v, []).append((u, L))
    d = {}
    for s in (0, 1, 2, 3):
        stack, seen = [(s, F(0))], {s}
        while stack:
            x, acc = stack.pop()
            if x in (0, 1, 2, 3):
                d[(s, x)] = acc
            for (y, L) in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append((y, acc + L))
    return d


def test_root_invariance():
    d = unrooted_distances()
    roots = [0, 1, 2, 3, 'a', 'b']
    for rt in roots:
        T = root_at_node(rt)
        ls, K = kernel(T)
        for i in ls:
            for j in ls:
                var = cov_of_forms(K, contrast_form(i, j), contrast_form(i, j), ls)
                if not check(var == d[(i, j)],
                             "根=%s：Var(X%s-X%s)=%s != 路径长 %s" % (rt, i, j, var, d[(i, j)])):
                    return
    sets = {}
    for rt in roots:
        T = root_at_node(rt)
        sets[rt] = frozenset(frozenset((i, j)) for (_k, i, j, _v, _w) in cherries(T))
    distinct = sorted({tuple(sorted(tuple(sorted(s)) for s in v)) for v in sets.values()})
    check(len(distinct) >= 2, "不同根下姊妹对集合应有差异")
    print("  [4] ★B 未定根：6 种根下 Var(X_i-X_j) 全部 = 路径长 d(i,j)（与根无关）✓；"
          "但「姊妹对/对比量集合」依根而异：%d 种 %s ✓" % (len(distinct), distinct))


# ---------------------------------------------------------------------------
# 5. ★★ PIC 递归（步 1-4）穷举：抽出 n-1 个对比量且**两两不相关**（文献 :478-503）
#    Lean: picMergeValue / picWeightI / picWeightJ / picMergeValue_var /
#          contrast_uncorrelated_picMerge / picStep
# ---------------------------------------------------------------------------
def pic_run(T):
    """PIC 步 1-4（每次取最深的 cherry，确定性）。
    返回 (contrasts, records, merged)；contrasts/merged 是原始叶上的线性形式。"""
    ls0, _K0 = kernel(T)
    forms = {l: {l: F(1)} for l in ls0}
    cur = T
    contrasts, records, merged = [], [], []

    def deepest(t, d=0):
        if t[0] == 'L':
            return None
        best = None
        if t[2][0] == 'L' and t[4][0] == 'L':
            best = (d, t)
        for sub in (t[2], t[4]):
            r = deepest(sub, d + 1)
            if r is not None and (best is None or r[0] > best[0]):
                best = r
        return best

    def replace(t, target, new):
        if t is target:
            return new
        if t[0] == 'L':
            return t
        return ('N', t[1], replace(t[2], target, new), t[3], replace(t[4], target, new))

    def lengthen(t, lab, vi, vj):
        if t[0] == 'L':
            return t
        _, vl, tl, vr, tr = t
        if tl[0] == 'L' and tl[1] == lab:
            vl = vl + vi * vj / (vi + vj)
        elif tr[0] == 'L' and tr[1] == lab:
            vr = vr + vi * vj / (vi + vj)
        return ('N', vl, lengthen(tl, lab, vi, vj), vr, lengthen(tr, lab, vi, vj))

    while len(leaves(cur)) > 1:
        _d, node = deepest(cur)
        _, vl, tl, vr, tr = node
        i, j, vi, vj = tl[1], tr[1], vl, vr
        assert vi + vj > 0, "PIC：被合并两叶的枝长之和必须 > 0"
        # (2) 对比量
        c = {k: forms[i].get(k, F(0)) - forms[j].get(k, F(0)) for k in ls0}
        contrasts.append(c)
        # (3) 式 (3) 加权平均（权 ∝ 方差之逆）
        wi, wj = vj / (vi + vj), vi / (vi + vj)
        m = {k: wi * forms[i].get(k, F(0)) + wj * forms[j].get(k, F(0)) for k in ls0}
        merged.append(m)
        lsC, KC = kernel(cur)
        records.append((i, j, vi, vj, KC[(i, i)] - vi,
                        cov_of_forms(KC, contrast_form(i, j), contrast_form(i, j), lsC),
                        cov_of_forms(KC, {i: wi, j: wj}, {i: wi, j: wj}, lsC)))
        newlab = ('merged', i, j)
        forms[newlab] = m
        cur = lengthen(replace(cur, node, ('L', newlab)), newlab, vi, vj)  # (4) 枝长加长
    return contrasts, records, merged


def test_pic(n, values, tag):
    nt = nc = 0
    for T in iter_trees(n, values):
        nt += 1
        ls, K = kernel(T)
        cs, recs, ms = pic_run(T)
        if not check(len(cs) == n - 1, "对比量个数应为 n-1"):
            return
        nc += len(cs)
        for c, m, (i, j, vi, vj, D, var_now, var_m_now) in zip(cs, ms, recs):
            # (2) 对比量方差 = vi+vj（当前核与原始核一致）
            if not check(var_now == vi + vj, "步(2) 方差 != vi+vj"):
                return
            if not check(cov_of_forms(K, c, c, ls) == vi + vj,
                         "对比量在原始核下方差 != vi+vj"):
                return
            # (3)+(4) 合并值方差 = K_kk + vi vj/(vi+vj)（枝长加长量）
            if not check(var_m_now == D + vi * vj / (vi + vj),
                         "步(3)/(4) 合并值方差 != D + vi vj/(vi+vj)"):
                return
            if not check(cov_of_forms(K, m, m, ls) == var_m_now,
                         "合并值方差在原始核下不一致"):
                return
            # 对比量 ⊥ 合并值（递归不变量）
            if not check(cov_of_forms(K, c, m, ls) == 0, "对比量与合并值不相关失败"):
                return
        # ★★ 抽出的 n-1 个对比量在原始核下两两不相关
        for a in range(len(cs)):
            for b in range(a + 1, len(cs)):
                if not check(cov_of_forms(K, cs[a], cs[b], ls) == 0,
                             "PIC 对比量 #%d,#%d 协方差 != 0" % (a, b)):
                    return
    print("  [5] ★★ PIC 递归（步 1-4）—— %s：%d 棵树 / %d 个对比量，"
          "全部满足「方差=vi+vj」「合并值方差=D+vi vj/(vi+vj)」「对比量⊥合并值」"
          "「两两不相关」✓" % (tag, nt, nc))


# ---------------------------------------------------------------------------
# 6. ★C 最小例（与 Lean 的 K6num 定理逐条对齐：vi=1/2, vj=1/3, Dk=Dl=1, r=0）
#    Lean: K6num_contrastVar(5/6) / K6num_contrastVar_unit / K6num_contrastCov_disjoint(0)
#          K6num_mergeVar(6/5) / K6num_mergedLength(6/5) / K6num_nonsister_eq(1/2)
# ---------------------------------------------------------------------------
def test_k6num():
    Dk, Dl, r, vi, vj, vp, vq = F(1), F(1), F(0), F(1, 2), F(1, 3), F(1), F(1)
    K = {(0, 0): Dk + vi, (0, 1): Dk, (1, 0): Dk, (0, 2): r, (2, 0): r, (0, 3): r, (3, 0): r,
         (0, 4): Dk, (4, 0): Dk, (0, 5): r, (5, 0): r,
         (1, 1): Dk + vj, (1, 2): r, (2, 1): r, (1, 3): r, (3, 1): r,
         (1, 4): Dk, (4, 1): Dk, (1, 5): r, (5, 1): r,
         (2, 2): Dl + vp, (2, 3): Dl, (3, 2): Dl, (2, 4): r, (4, 2): r, (2, 5): Dl, (5, 2): Dl,
         (3, 3): Dl + vq, (3, 4): r, (4, 3): r, (3, 5): Dl, (5, 3): Dl,
         (4, 4): Dk, (4, 5): r, (5, 4): r, (5, 5): Dl}
    ls = [0, 1, 2, 3]
    v01 = cov_of_forms(K, contrast_form(0, 1), contrast_form(0, 1), ls)
    v23 = cov_of_forms(K, contrast_form(2, 3), contrast_form(2, 3), ls)
    c0123 = cov_of_forms(K, contrast_form(0, 1), contrast_form(2, 3), ls)
    c0102 = cov_of_forms(K, contrast_form(0, 1), contrast_form(0, 2), ls)
    wi, wj = vj / (vi + vj), vi / (vi + vj)
    vm = cov_of_forms(K, {0: wi, 1: wj}, {0: wi, 1: wj}, ls)
    check(v01 == F(5, 6), "K6num: Var(X0-X1) 应为 5/6")
    check(v01 / F(5, 6) == 1, "K6num: 单位方差失败")
    check(v23 == F(2), "K6num: Var(X2-X3) 应为 2")
    check(c0123 == 0, "K6num: 分离 cherry 协方差应为 0")
    check(c0102 == F(1, 2), "K6num: 非姊妹对协方差应为 1/2")
    check(vm == Dk + vi * vj / (vi + vj), "K6num: 合并值方差应为 6/5")
    check(vi * vj / (vi + vj) == F(1, 5), "K6num: 枝长加长量应为 1/5")
    print("  [6] ★C K6num：Var(X0-X1)=%s（÷自身=1 ✓）Var(X2-X3)=%s Cov((01),(23))=%s "
          "Cov((01),(02))=%s Var(合并值)=%s（加长量 1/5）✓"
          % (v01, v23, c0123, c0102, vm))


# ---------------------------------------------------------------------------
# 7. 四项式恒等式：Cov(X_i-X_j, X_p-X_q) = K_ip-K_iq-K_jp+K_jq
#    Lean: contrastCov / contrastVar 的定义（contrastCov_self = rfl）
# ---------------------------------------------------------------------------
def test_four_term_identity(n, values, tag):
    cnt = 0
    for T in iter_trees(n, values):
        ls, K = kernel(T)
        for i, j, p, q in product(ls, repeat=4):
            lhs = cov_of_forms(K, contrast_form(i, j), contrast_form(p, q), ls)
            rhs = K[(i, p)] - K[(i, q)] - K[(j, p)] + K[(j, q)]
            cnt += 1
            if not check(lhs == rhs, "四项式恒等式失败"):
                return
    print("  [7] 四项式恒等式 Cov(X_i-X_j,X_p-X_q)=K_ip-K_iq-K_jp+K_jq —— %s：%d 组 ✓"
          % (tag, cnt))


def main():
    print("=" * 78)
    print("W11h / X9 —— PIC（Felsenstein 1985a）精确有理数穷举核验（无 Monte Carlo）")
    print("=" * 78)
    test_cherry_variance(3, [F(1), F(2), F(3), F(1, 2), F(1, 3)], "n=3 全形状×5 枝长")
    test_cherry_variance(4, [F(1), F(2), F(1, 2)], "n=4 全形状×3 枝长")
    test_disjoint_clades(4, [F(1), F(2), F(1, 2)], "n=4 全形状×3 枝长")
    test_disjoint_clades(5, [F(1), F(1, 2)], "n=5 全形状×2 枝长")
    test_counterexample()
    test_root_invariance()
    test_pic(3, [F(1), F(2), F(1, 2), F(1, 3)], "n=3 全形状×4 枝长")
    test_pic(4, [F(1), F(2), F(1, 2), F(1, 3)], "n=4 全形状×4 枝长")
    test_pic(5, [F(1), F(1, 2), F(1, 3)], "n=5 全形状×3 枝长")
    test_pic(6, [F(1), F(1, 2)], "n=6 全形状×2 枝长")
    test_k6num()
    test_four_term_identity(3, [F(1), F(2), F(1, 2)], "n=3 全形状×3 枝长")
    test_four_term_identity(4, [F(1), F(1, 2)], "n=4 全形状×2 枝长")
    # multifurcation：零长枝把 polytomy 写成二叉序列（文献 :501-503）
    star = ('N', F(1, 2), ('L', 0), F(0), ('N', F(1, 3), ('L', 1), F(0),
            ('N', F(1), ('L', 2), F(1), ('L', 3))))
    ls, K = kernel(star)
    cs, _recs, _ms = pic_run(star)
    check(len(cs) == 3, "polytomy（4 叶）应抽出 3 个对比量")
    for a in range(len(cs)):
        for b in range(a + 1, len(cs)):
            check(cov_of_forms(K, cs[a], cs[b], ls) == 0, "polytomy 对比量应两两不相关")
    print("  [8] multifurcation（零长枝二叉化，文献 :501-503）：4 叶星形树抽出 n-1=3 个"
          "对比量，两两不相关 ✓")
    print("-" * 78)
    if FAIL:
        print("结论：**失败 %d 项**" % len(FAIL))
        for m in FAIL[:20]:
            print("   - " + m)
        raise SystemExit(1)
    print("结论：全部检查通过（精确有理数 / 穷举 / 无 Monte Carlo）")


if __name__ == "__main__":
    main()
