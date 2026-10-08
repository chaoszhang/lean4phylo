#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
zds2011_monophyly.py -- Zhu, Degnan & Steel (2011) "Clades, clans and reciprocal
monophyly under neutral evolutionary models" 的**精确有理数**穷举复核。

用途（W10h / Phylo/Stat/ReciprocalMonophyly.lean 的公式来源复核）：
把论文的闭形式（Lemma 4.1/4.2/4.3/4.4、Theorem 4.5、Lemma 6.2、Theorem 6.3、6.4）
与「在 YHK(=Yule=Kingman 拓扑) 分布上**直接穷举**得到的频率」逐条对照。

方法：
  YHK 生成过程 = 从一个叶出发，每步**均匀随机**选一个现有的叶并把它分裂成两个新叶，
  重复 n-1 次。以 Fraction 精确维护 (树, 概率) 的分布。
  （论文 §3、第 193-216 行；与 Kingman 溯祖的拓扑分布相同，第 208-212 行。）

树用嵌套 tuple 表示；叶是 int。clade = 某内部顶点后代叶集（含单点与全集）。
无根树的 clan（第 985-988 行 = 本库 Phylo.Cladogram.IsClade）由 Lemma 6.1
（第 991-992 行）给出：A 是 clan ⟺ A 是 clade 或 X-A 是 clade。

无随机数、无浮点。所有比较用 == 与 Fraction。
"""

from fractions import Fraction
from itertools import combinations
from math import comb, factorial


# --------------------------------------------------------------------------
# 1. YHK 分布（精确）
# --------------------------------------------------------------------------

def _canonical_paths(n):
    """YHK 的「路径」计数：每步选一个现有叶分裂、新叶取下一个标签（标签按 0..n-1 次序）。
    返回 {树: 路径条数}，总路径数 = (n-1)!。"""
    paths = {0: 1}

    def leaves(t):
        if isinstance(t, int):
            return [t]
        return leaves(t[0]) + leaves(t[1])

    def split_leaf(t, target, new_label):
        if isinstance(t, int):
            return (target, new_label) if t == target else None
        a = split_leaf(t[0], target, new_label)
        b = split_leaf(t[1], target, new_label)
        assert not (a is not None and b is not None), "duplicate leaf label"
        if a is not None:
            return (a, t[1])
        if b is not None:
            return (t[0], b)
        return None

    for step in range(1, n):
        nd = {}
        for t, c in paths.items():
            for x in leaves(t):
                t2 = split_leaf(t, x, step)
                assert t2 is not None
                nd[t2] = nd.get(t2, 0) + c
        paths = nd
    return paths


def _relabel(t, perm):
    if isinstance(t, int):
        return perm[t]
    return (_relabel(t[0], perm), _relabel(t[1], perm))


def yhk_distribution(n):
    """{tree: Fraction}——YHK 拓扑律。

    生成过程（论文 §3，第 193-216 行；等价于 Kingman 溯祖的拓扑分布，第 208-212 行）：
    先取一个**均匀随机**的标签次序，再在每一步**均匀随机**选一个现有叶分裂、把下一个标签
    挂上去。故概率 = (该树被 (次序, 选择) 对命中的次数) / (n! · (n-1)!)。"""
    from itertools import permutations

    paths = _canonical_paths(n)
    perms = list(permutations(range(n)))
    total = len(perms) * factorial(n - 1)
    dist = {}
    for t, c in paths.items():
        for s in perms:
            t2 = _relabel(t, s)
            dist[t2] = dist.get(t2, 0) + c
    return {t: Fraction(c, total) for t, c in dist.items()}


def clades(t):
    """根树的 clade 全体（含单点与全集）。"""
    out = set()

    def rec(s):
        if isinstance(s, int):
            out.add(frozenset([s]))
            return frozenset([s])
        a = rec(s[0])
        b = rec(s[1])
        u = a | b
        out.add(u)
        return u

    rec(t)
    return out


# --------------------------------------------------------------------------
# 2. 论文的闭形式（照抄，逐项）
# --------------------------------------------------------------------------

def pn(n, a):
    """Lemma 4.2（第 294-317 行）：A(大小 a) 是 n 叶 YHK 树的 proper clade 的概率。"""
    if not (1 <= a <= n - 1):
        return Fraction(0)
    return Fraction(2 * n, a * (a + 1)) / comb(n, a)


def pn_hat(n, a, b):
    """Lemma 4.4（第 389-396 行）：A,B 是**姐妹** clade 的概率；k = a+b **<** n。

    ⚠️ 脚本复核（n ≤ 6 全穷举）显示：`k = n` 时该表达式**不等于**真值
    （真值为 Lemma 4.3 的值），故此处限定 k < n。"""
    k = a + b
    assert k < n, "Lemma 4.4 只在 k < n 时成立；k = n 用 pn_hat_exh"
    return Fraction(4 * factorial(a) * factorial(b) * factorial(n - k),
                    factorial(n - 1) * k * (k * k - 1))


def pn_hat_exh(n, a):
    """Lemma 4.3（第 369-385 行）：A 与 X-A 是姐妹 clade（= A 是极大真 clade）。"""
    return Fraction(2, n - 1) / comb(n, a)


def R(n, a, b):
    """Theorem 4.5 case 2 的 R_n(a,b)（第 479-503 行）。"""
    return Fraction(4 * n, a * (a + 1) * (b + 1)) / comb(n, b) / comb(b, a)


def G(n, a, b):
    """Theorem 4.5 的 G_n(a,b)（第 511-526 行）。"""
    return (Fraction(n, a * b * (a + 1) * (b + 1))
            - Fraction(a * (a + 1) + b * (b + 1) + a * b,
                       a * b * (a + 1) * (b + 1) * (a + b + 1))
            + Fraction(1, (a + b) * ((a + b) ** 2 - 1)))


def r(n, a, b):
    """Theorem 4.5 case 5 的 r_n(a,b)（第 504-509 行）。"""
    return Fraction(4 * factorial(a) * factorial(b) * factorial(n - a - b),
                    factorial(n - 1)) * G(n, a, b)


def qn_lemma62(n, a):
    """Lemma 6.2（第 1007-1036 行）：A 是**无根** YHK 树的 clan 的概率。"""
    b = n - a
    return (Fraction(2 * n, a * (a + 1)) + Fraction(2 * n, b * (b + 1))
            - Fraction(2, n - 1)) / comb(n, a)


def qn_thm63i(a, b):
    """Theorem 6.3(i)（第 1077-1103 行），n = a+b。"""
    n = a + b
    return (Fraction(2 * factorial(a) * factorial(b), factorial(n - 1))
            * (Fraction(1, a * (a + 1)) + Fraction(1, b * (b + 1))
               - Fraction(1, n * (n - 1))))


def qn_thm63ii(n, a, b):
    """Theorem 6.3(ii)（第 1105-1110 行），a+b < n。"""
    return (r(n, a, b) + R(n, a, n - b) + R(n, b, n - a)
            - pn_hat_exh(n, b) * pn(n - b, a)
            - pn_hat_exh(n, a) * pn(n - a, b))


def q_triple(a1, a2, a3):
    """Theorem 6.4(i)（第 1171-1182 行）。"""
    n = a1 + a2 + a3
    return (Fraction(4 * factorial(a1) * factorial(a2) * factorial(a3),
                     factorial(n - 1))
            * sum(Fraction(1, (n - ai) * ((n - ai) ** 2 - 1))
                  for ai in (a1, a2, a3)))


def q_convex(a1, a2, a3):
    """Theorem 6.4(ii)（第 1190-1191 行）。"""
    n = a1 + a2 + a3
    return (qn_thm63ii(n, a1, a2) + qn_thm63ii(n, a1, a3)
            + qn_thm63ii(n, a2, a3) - 2 * q_triple(a1, a2, a3))


# --------------------------------------------------------------------------
# 3. 穷举真值
# --------------------------------------------------------------------------

def truth_pn(n, a):
    """P(给定 a 元子集是 proper clade)。"""
    dist = yhk_distribution(n)
    target = frozenset(range(a))
    return sum(p for t, p in dist.items()
               if target in clades(t) and a <= n - 1)


def truth_pn_hat(n, a, b):
    """P(A,B 是姐妹 clade)：A,B 及 A∪B 都是 clade，A∩B=∅。"""
    dist = yhk_distribution(n)
    A = frozenset(range(a))
    B = frozenset(range(a, a + b))
    tot = Fraction(0)
    for t, p in dist.items():
        c = clades(t)
        if A in c and B in c and (A | B) in c:
            tot += p
    return tot


def truth_pair_clades(n, a, b):
    """P(A,B 都是 proper clade)（不要求姐妹）—— Theorem 4.5 的 p_n(A,B)。"""
    dist = yhk_distribution(n)
    A = frozenset(range(a))
    B = frozenset(range(a, a + b))
    return sum(p for t, p in dist.items() if A in clades(t) and B in clades(t))


def truth_qn(n, a, b):
    """P(A,B 都是**无根**树 T-ρ 的 clan)（Lemma 6.1：clan ⟺ 自身或补是 clade）。"""
    dist = yhk_distribution(n)
    X = frozenset(range(n))
    A = frozenset(range(a))
    B = frozenset(range(a, a + b))

    def is_clan(c, S):
        return S in c or (X - S) in c

    return sum(p for t, p in dist.items()
               if is_clan(clades(t), A) and is_clan(clades(t), B))


def truth_q_triple(n, sizes):
    """P(A_1,...,A_k 全是无根 clan)，A_i 为按 sizes 切分的连续块。"""
    dist = yhk_distribution(n)
    X = frozenset(range(n))
    blocks, off = [], 0
    for s in sizes:
        blocks.append(frozenset(range(off, off + s)))
        off += s
    assert off == n
    tot = Fraction(0)
    for t, p in dist.items():
        c = clades(t)
        if all((S in c or (X - S) in c) for S in blocks):
            tot += p
    return tot


# --------------------------------------------------------------------------
# 4. 报告
# --------------------------------------------------------------------------

def check(name, lhs, rhs):
    ok = (lhs == rhs)
    print(f"  [{'OK ' if ok else 'XX '}] {name}: {lhs} vs {rhs}")
    return ok


def main():
    allok = True
    print("=" * 78)
    print("A. Lemma 4.2 / 4.3 / 4.4 —— 与穷举真值对照")
    print("=" * 78)
    for n in (4, 5, 6):
        for a in range(1, n):
            allok &= check(f"p_{n}({a})", pn(n, a), truth_pn(n, a))
    for n in (4, 5, 6):
        for a in range(1, n):
            allok &= check(f"pHat_{n}({a},{n-a})  [Lemma 4.3]",
                           pn_hat_exh(n, a), truth_pn_hat(n, a, n - a))
    for (n, a, b) in ((5, 1, 2), (5, 2, 2), (6, 1, 2), (6, 2, 2), (6, 2, 3), (6, 1, 4)):
        allok &= check(f"pHat_{n}({a},{b})  [Lemma 4.4, k<n]",
                       pn_hat(n, a, b), truth_pn_hat(n, a, b))
        allok &= check(f"pHat_{n}({a},{b}) = p_{n}({a+b})*pHat_{a+b}({a},{b})",
                       pn_hat(n, a, b), pn(n, a + b) * pn_hat_exh(a + b, a))

    print()
    print("=" * 78)
    print("B. Theorem 4.5 —— p_n(A,B) 与 r_n / R_n / pHat 的关系")
    print("=" * 78)
    for (n, a, b) in ((6, 2, 2), (6, 1, 3), (5, 1, 2), (6, 2, 3)):
        t = truth_pair_clades(n, a, b)
        allok &= check(f"p_{n}(A,B) = r_{n}({a},{b})", r(n, a, b), t)
    # case 2: A ⊂ B
    for (n, a, b) in ((4, 1, 2), (5, 1, 3), (6, 2, 4), (6, 1, 3)):
        A = frozenset(range(a))
        B = frozenset(range(b))
        dist = yhk_distribution(n)
        t = sum(p for tr, p in dist.items() if A in clades(tr) and B in clades(tr))
        allok &= check(f"p_{n}({a} in {b}) = R_{n}({a},{b})", R(n, a, b), t)

    print()
    print("=" * 78)
    print("C. Lemma 6.2 与 Theorem 6.3(i)（互单系 / reciprocal monophyly）")
    print("=" * 78)
    for n in (4, 5, 6):
        for a in range(1, n):
            allok &= check(f"q_{n}({a})  Lemma6.2 vs 穷举", qn_lemma62(n, a),
                           truth_qn_single(n, a))
    for (a, b) in ((1, 1), (1, 2), (2, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 3)):
        allok &= check(f"q_{a+b}({a},{b})  6.3(i) vs 6.2",
                       qn_thm63i(a, b), qn_lemma62(a + b, a))
        allok &= check(f"q_{a+b}({a},{b})  6.3(i) vs 穷举",
                       qn_thm63i(a, b), truth_qn(a + b, a, b))

    print()
    print("=" * 78)
    print("D. Theorem 6.3(ii)（a+b < n）")
    print("=" * 78)
    for (n, a, b) in ((5, 2, 2), (6, 2, 2), (6, 1, 2), (6, 2, 3), (5, 1, 3)):
        allok &= check(f"q_{n}({a},{b})  6.3(ii) vs 穷举",
                       qn_thm63ii(n, a, b), truth_qn(n, a, b))

    print()
    print("=" * 78)
    print("E. Theorem 6.4（三个 clan）")
    print("=" * 78)
    for sizes in ((1, 1, 1), (2, 2, 2), (1, 2, 3), (1, 1, 2), (1, 2, 2)):
        n = sum(sizes)
        allok &= check(f"q{sizes}  Thm6.4(i) vs 穷举", q_triple(*sizes),
                       truth_q_triple(n, sizes))
    allok &= check("q(2,2,2) = 1/75（论文第 1166 行）", q_triple(2, 2, 2), Fraction(1, 75))
    allok &= check("q'(2,2,2) = 1/15（论文第 1166 行）", q_convex(2, 2, 2), Fraction(1, 15))
    allok &= check("q6(2,2) = 7/225（论文第 1051 行）", qn_thm63ii(6, 2, 2), Fraction(7, 225))

    print()
    print("=" * 78)
    print("F. 锚点恒等式（与具体树无关的算术事实）")
    print("=" * 78)
    for n in range(2, 12):
        allok &= check(f"q_{n}(1) = 1", qn_lemma62(n, 1), Fraction(1))
    for n in range(3, 12):
        allok &= check(f"q_{n}(n-1) = 1", qn_lemma62(n, n - 1), Fraction(1))
    for n in range(2, 12):
        for a in range(1, n):
            allok &= check(f"q_{n}({a}) = p_{n}({a}) + p_{n}({n-a}) - pHat_{n}({a},{n-a})",
                           qn_lemma62(n, a),
                           pn(n, a) + pn(n, n - a) - pn_hat_exh(n, a))
    for (n, a, b) in ((6, 2, 4), (5, 2, 3), (6, 1, 3), (7, 2, 5)):
        allok &= check(f"R_{n}({a},{b}) = p_{n}({b})*p_{b}({a})",
                       R(n, a, b), pn(n, b) * pn(b, a))
    for (a, b) in ((1, 1), (2, 2), (1, 3), (2, 4), (3, 3)):
        allok &= check(f"q_{a+b}({a},{b}) = q_{a+b}({b},{a})",
                       qn_thm63i(a, b), qn_thm63i(b, a))
    print()
    print("=" * 78)
    print("总判定：", "ALL OK" if allok else "存在不一致（见上面 XX 行）")
    print("=" * 78)
    return 0 if allok else 1


def truth_qn_single(n, a):
    """P(给定 a 元子集 A 是无根树的 clan) = p_n(A) + p_n(X-A) - pHat_n(A,X-A)."""
    dist = yhk_distribution(n)
    X = frozenset(range(n))
    A = frozenset(range(a))
    return sum(p for t, p in dist.items()
               if A in clades(t) or (X - A) in clades(t))


if __name__ == "__main__":
    raise SystemExit(main())
