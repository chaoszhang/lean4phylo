#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""yhk_weight_derive.py —— 从 ZDS2011 的生成过程**推出**「一般 n 的 YHK 权重」并穷举核对。

============================================================================
文献：`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md`
  * `:191-221`  §3 The Yule-Harding-Kingman process（「selecting a leaf uniformly at
    random and 'splitting' it into two new leaves」）
  * `:230-232`  (EP) 交换性：「If T′ is obtained from T by permuting its leaves, then
    P(T = T′) = P(T = T)」
  * `:294-317`  Lemma 4.2  pn(a) = 2n/(a(a+1)) · C(n,a)^{-1}
  * `:369-385`  Lemma 4.3  p̂n(a,n−a) = 2/(n−1) · C(n,a)^{-1}
  * `:991-992`  Lemma 6.1  A 是 T−ρ 的 clan ⟺ A 是 T 的 clade 或 X−A 是 T 的 clade
  * `:1007-1035` Lemma 6.2 qn(a) = 2n[1/(a(a+1)) + 1/(b(b+1)) − 1/((n−1)n)]·C(n,a)^{-1}
  * `:1037-1044` 证明（包含-排除 qn(A) = pn(A) + pn(X−A) − pn(A,X−A)）
  * `:1000-1006` 无根版生成过程：「a leaf is selected uniformly at random and a new leaf
    (with a random label) is attached to its incident edge」

================================================================ 推出来的公式
有根（n 叶标号二叉拓扑 T；n_v = v 下方的叶数，**根计入**）：

    P_rooted(T) = 2^{n-1} / ( n! · ∏_{v 内部} (n_v − 1) )          (★)

无根（U = T − ρ，同一 U 有 2n−3 个 rootings，文献 `:996-1006`）：

    P_unrooted(U) = Σ_{e ∈ E(U)} P_rooted(T_e)

推导（本脚本逐条核对，**不照抄任何现成公式**）：
  1. 记 g(T) = ∏_{v}(n_v − 1)。根的两棵子树叶数为 a, n−a 时 g(T) = (n−1)·g(T₁)·g(T₂)。
  2. 「标号有根树 ↦ 形状」的纤维大小 = #hist(T) = (n−1)!/g(T)（下文 (b)）。
  3. 纯生过程在形状层是「以 1/k 均匀选叶再分裂」；按 (EP) 均匀化标号 ⇒ (★)。
  4. 归一化 ⟺ S_n := Σ_T 1/g(T) = n!/2^{n−1}；由
     S_n = (1/(2(n−1)))·Σ_{a=1}^{n−1} C(n,a)·S_a·S_{n−a} 归纳可得（下文 (a) 穷举验证）。

================================================================ 脚本核对的内容
  (a) 有根权重归一：Σ_T P_rooted(T) = 1
  (b) 「均匀选叶分裂」的**精确马尔可夫链**（在形状上）与 (★) 逐形状一致
  (c) 无根律归一：Σ_U P_unrooted(U) = 1；每个 U 恰有 2n−3 个 rootings
  (c') 无根律是否**均匀**（★ 只有 n ≤ 5 均匀；n ≥ 6 不均匀 —— 勿把 n=4 的「三棵等权」外推）
  (d) Lemma 4.2 / 4.3 的概率值
  (e) Lemma 6.2 的 qn(|A|) —— 即缺口 `YHKClanLawGap` 右端的 `clanProb n A.card`
  (f) 形状表（count, g, 权重）：Lean 侧 `yhkRootWeight_four_total` / `_five_total` 的数据来源
  (g) 恒等式 Σ_a C(n,a)·clanProb(n,a) = 4n − 6（＝ 2×(2n−3)，即「proper clan 数的期望」）
  (h) 无根过程的**历史空间**：|Ω_n| = 3·4···(n−1) = (n−1)!/2，每条历史 2/(n−1)!
      （Lean 侧 `two_mul_card_yhkHistorySpace` / `sum_yhkHistoryProb` 的对象）

用法： python3 scripts/msc/yhk_weight_derive.py [nmax]      （默认 nmax = 7）
全部为**精确有理数**（Fraction），无浮点、无随机数。末行 `总判定：ALL OK` 即全通过。
============================================================================
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, factorial
import sys

OK = [True]


def chk(cond, msg):
    if not cond:
        OK[0] = False
        print("    FAIL:", msg)
    return cond


# ---------------------------------------------------------------- 有根拓扑
# 节点 ('N', T1, T2)；叶 ('L', x);  标签是 int
def gen(S):
    """S 上全部有根二叉拓扑（每个 split 取「含 min 的一侧」作左子，唯一）。"""
    S = frozenset(S)
    n = len(S)
    if n == 1:
        return [('L', next(iter(S)))]
    m = min(S)
    rest = sorted(S - {m})
    out = []
    for r in range(0, n - 1):
        for c in combinations(rest, r):
            S1 = frozenset(c) | {m}
            S2 = S - S1
            out.extend(('N', t1, t2) for t1 in gen(S1) for t2 in gen(S2))
    return out


def leaves(T):
    if T[0] == 'L':
        return [T[1]]
    return leaves(T[1]) + leaves(T[2])


def g(T):
    """g(T) = ∏_{v 内部} (n_v − 1)，根计入（n_root − 1 = n − 1）。"""
    if T[0] == 'L':
        return 1
    return (len(leaves(T)) - 1) * g(T[1]) * g(T[2])


def clades(T, S):
    """proper clade = 非根顶点下方的叶集（叶自身⇒单点集也是 clade）。"""
    out = set()

    def rec(t, isroot):
        A = frozenset([t[1]]) if t[0] == 'L' else frozenset(leaves(t))
        if not isroot:
            out.add(A)
        if t[0] != 'L':
            rec(t[1], False)
            rec(t[2], False)
        return A
    X = rec(T, True)
    out.discard(X)
    out.discard(frozenset())
    return out


def canon(A, S):
    """无序 split {A, S\\A} 的规范代表。"""
    a = tuple(sorted(A))
    b = tuple(sorted(frozenset(S) - frozenset(A)))
    return min(a, b, key=lambda t: (len(t), t))


def unrooted_splitset(T, S):
    return frozenset(canon(A, S) for A in clades(T, S))


def P_rooted(T):
    n = len(leaves(T))
    return F(2 ** (n - 1), factorial(n) * g(T))


# ---------------------------------------------------------------- 闭形式
def pn_formula(n, a):
    return F(0) if (a == 0 or a >= n) else F(2 * n, a * (a + 1)) * F(1, comb(n, a))


def phat_exh_formula(n, a):
    return F(2, n - 1) * F(1, comb(n, a))


def clanProb_formula(n, a):
    b = n - a
    return (2 * n * (F(1, a * (a + 1)) + F(1, b * (b + 1)) - F(1, (n - 1) * n))
            * F(1, comb(n, a)))


# ---------------------------------------------------------------- 形状层链
def shape(T):
    if T[0] == 'L':
        return '*'
    a, b = shape(T[1]), shape(T[2])
    return ('N',) + tuple(sorted([a, b], key=repr))


def leaf_positions(s, acc, path=()):
    if s == '*':
        acc.append(path)
        return
    leaf_positions(s[1], acc, path + (1,))
    leaf_positions(s[2], acc, path + (2,))


def split_leaf(s, path):
    if s == '*':
        return ('N', '*', '*')
    i = path[0]
    new = split_leaf(s[i], path[1:])
    other = s[2] if i == 1 else s[1]
    return ('N',) + tuple(sorted([new, other], key=repr))


def nleaves_shape(s):
    return 1 if s == '*' else nleaves_shape(s[1]) + nleaves_shape(s[2])


def shape_dist(n):
    """「以 1/k 均匀选叶、分裂、再均匀重标号」的精确链（形状层）⇒ 形状概率。"""
    dist = {('N', '*', '*'): F(1)}
    for k in range(2, n):
        nd = {}
        for s, p in dist.items():
            pos = []
            leaf_positions(s, pos)
            assert len(pos) == k
            for pth in pos:
                t = split_leaf(s, pth)
                nd[t] = nd.get(t, F(0)) + p * F(1, k)
        dist = nd
    return dist


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    for n in range(3, nmax + 1):
        S = frozenset(range(n))
        Ts = gen(S)
        nb = 1
        for i in range(1, 2 * n - 2, 2):
            nb *= i
        print(f"n={n}: #rooted = {len(Ts)} = (2n-3)!! = {nb}")
        chk(len(Ts) == nb, "rooted count")

        # (a) 有根归一
        tot = sum(P_rooted(T) for T in Ts)
        print(f"  (a) Σ_T P_rooted(T) = {tot}")
        chk(tot == 1, "rooted normalisation")

        # (b) 与分裂链逐形状比对
        dist = shape_dist(n)
        byshape = {}
        for T in Ts:
            byshape.setdefault(shape(T), []).append(T)
        bad = [(s, sum(P_rooted(T) for T in lst), dist.get(s, F(0)))
               for s, lst in byshape.items()
               if sum(P_rooted(T) for T in lst) != dist.get(s, F(0))]
        print(f"  (b) split-chain vs (★): Σ = {sum(dist.values())}, shapes = {len(byshape)}")
        chk(sum(dist.values()) == 1 and not bad, f"chain mismatch {bad[:2]}")

        # (c) 无根律
        U = {}
        for T in Ts:
            k = unrooted_splitset(T, S)
            U[k] = U.get(k, F(0)) + P_rooted(T)
        utot = sum(U.values())
        cnts = {}
        for T in Ts:
            k = unrooted_splitset(T, S)
            cnts[k] = cnts.get(k, 0) + 1
        print(f"  (c) #unrooted = {len(U)} = (2n-5)!!;  Σ_U P_unrooted = {utot};  "
              f"rootings/U ∈ {sorted(set(cnts.values()))} (2n-3 = {2*n-3})")
        chk(utot == 1, "unrooted normalisation")
        chk(set(cnts.values()) == {2 * n - 3}, "rootings per unrooted tree")

        # (c') 无根律是否**均匀**？★ 只有 n ≤ 5 均匀；n = 6 起就不均匀
        #      ⇒ 切勿把 `yhkLawFour` 的「三棵 quartet 等权」外推成「一般 n 均匀」（教训）
        unif = len(set(U.values())) == 1
        print(f"  (c') 无根律 uniform? {unif}   distinct values = "
              f"{sorted(set(U.values()))[:4]}")
        chk(unif == (n <= 5), "uniformity pattern (n<=5 uniform, n>=6 not)")

        # (d)(e) 逐 a 核对 Lemma 4.2 / 4.3 / 6.2
        for a in range(1, n):
            A = frozenset(range(a))
            pr = sum(P_rooted(T) for T in Ts if A in clades(T, S))
            pr2 = sum(P_rooted(T) for T in Ts
                      if A in clades(T, S) and frozenset(S - A) in clades(T, S))
            pu = sum(p for k, p in U.items() if canon(A, S) in k)
            e1, e2, e3 = pn_formula(n, a), phat_exh_formula(n, a), clanProb_formula(n, a)
            print(f"  a={a}: pn={pr} (L4.2 {e1}) {'OK' if pr == e1 else 'FAIL'}"
                  f" | p̂n={pr2} (L4.3 {e2}) {'OK' if pr2 == e2 else 'FAIL'}"
                  f" | q={pu} (L6.2 {e3}) {'OK' if pu == e3 else 'FAIL'}")
            chk(pr == e1 and pr2 == e2 and pu == e3, f"clade prob n={n} a={a}")

        # (f) 形状表
        for s, lst in sorted(byshape.items(), key=lambda kv: -len(kv[1])):
            print(f"  (f) shape count={len(lst):5d} g={g(lst[0]):6d} "
                  f"w=2^(n-1)/(n!g)={P_rooted(lst[0])}  count*w={len(lst)*P_rooted(lst[0])}")
        chk(sum(len(lst) * P_rooted(lst[0]) for lst in byshape.values()) == 1, "shape table")

        # (g) Σ_a C(n,a)·clanProb(n,a) = 4n − 6
        e = sum(comb(n, a) * clanProb_formula(n, a) for a in range(1, n))
        print(f"  (g) Σ_a C(n,a)·clanProb(n,a) = {e}  (4n-6 = {4*n-6})")
        chk(e == 4 * n - 6, "expected #clans")

        if n == 4:
            print(f"  n=4: 无根权重取值集合 = {sorted(set(U.values()))}"
                  f"  → 与 yhkLawFour（三棵 quartet 等权 1/3）一致")
            chk(set(U.values()) == {F(1, 3)}, "n=4 uniform 1/3")

    # (h) 无根过程的历史空间
    print("\n(h) 无根过程历史空间 (leaf attached to a uniformly chosen incident edge):")
    for n in range(3, nmax + 1):
        card = 1
        for k in range(4, n + 1):
            card *= (k - 1)
        p = F(2, factorial(n - 1))
        print(f"  n={n}: |Ω| = 3·4···{n-1} = {card};  (n-1)!/2 = {factorial(n-1)//2};  "
              f"prob = 2/(n-1)! = {p};  |Ω|·prob = {card*p}")
        chk(card == factorial(n - 1) // 2 and card * p == 1, f"history space n={n}")

    print("\n总判定：" + ("ALL OK" if OK[0] else "SOME CHECK FAILED"))
    return 0 if OK[0] else 1


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    sys.exit(main())
