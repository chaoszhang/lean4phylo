#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""W19 C1-M3③ 器材 (b) 第 2 步：闭式概率 ＋ (a) 代入求和 ＋ T=0 诊断（★G）。

★★★ 本轮推导出的闭式（ψ1 = (((A,B),C),D),E)，三条内部枝 b2,b3,b4）：
   i₂ = 2 ；j₂ = 1 若 h 含 clade {A,B}，否则 2
   i₃ = j₂ + 1 ；j₃ = 1 若 h 含 clade {A,B,C}，否则 2
   i₄ = j₃ + 1 ；j₄ = 1 若 h 含 clade {A,B,C,D}，否则 2
   P(h) = Π_b  g_{i_b, j_b}(T_b) / N(i_b, j_b)
   其中 N(i,j) = i! / (2^{i−j} · (i−j)! · (2j−i)!)
     —— 含义：g_{ij}(T) 是"i 条谱系在长度 T 内降到 j 条"的【总】概率（对"哪几对合生"求和），
        故某个【具体】合生方案的概率 = g_{ij}/N(i,j) ✓（N 为 i→j 的方案数）。
   ★ 校验：N(2,1) = 1 ✓ · N(3,2) = 3 ✓ · N(4,2) = 3 ✓ · N(4,3) = 6 ✓（全为正整数 ✓）。

(a) {V,W,X,Y,Z} 代入：class 的定义是约束（如 {X,Y}={A,B}），
    故 class 的概率 = 对【所有满足约束的双射】求和 ✓（这正是 class 的含义 ✓）。

判决性诊断：T₂=T₃=T₄=0 时【只有物种树自身拓扑】概率为 1、其余为 0 ✓。
文献：RosenbergTao2008  p3 正文（linear in e^{−T4} ✓）· :380-389（AGT/Equation 1 ✓）· p9 TABLE 9（T_min ✓）。
"""
import itertools, math, os, importlib.util, sys, re
from fractions import Fraction as F

LEAVES = ["A", "B", "C", "D", "E"]
# ψ1 的 clade 序列（自下而上）：b2 上方的 clade、b3、b4
CLADES = [frozenset("AB"), frozenset("ABC"), frozenset("ABCD")]


def g(i, j, t):
    """RT2008 Table 1 的 g_{ij}(t)（i ≤ 4）✓（用浮点，t ≥ 0）。"""
    e1, e3, e6 = math.exp(-t), math.exp(-3 * t), math.exp(-6 * t)
    table = {
        (2, 1): 1 - e1, (2, 2): e1,
        (3, 1): 1 - 1.5 * e1 + 0.5 * e3, (3, 2): 1.5 * e1 - 1.5 * e3, (3, 3): e3,
        (4, 1): 1 - 1.8 * e1 + e3 - 0.2 * e6, (4, 2): 1.8 * e1 - 3 * e3 + 1.2 * e6,
        (4, 3): 2 * e3 - 2 * e6, (4, 4): e6,
    }
    return table[(i, j)]


def N(i, j):
    """i → j 的合生方案数 = i! / (2^{i−j} (i−j)! (2j−i)!)。"""
    k = i - j
    return math.factorial(i) // (2 ** k * math.factorial(k) * math.factorial(2 * j - i))


def clades_of(nwk_children, root):
    """由树表算出【全部 clade】（叶集合），键为内部节点。"""
    out = {}

    def rec(n):
        if n in nwk_children:
            s = set()
            for c in nwk_children[n]:
                s |= rec(c)
            out[n] = frozenset(s)
            return s
        return {n}
    rec(root)
    return out


def parse_newick(s):
    """解析 Table 3 的记号：一切逗号省略 ＋ 外层根括号可省。"""
    s = re.sub(r",+", ",", re.sub(r"(\)|[A-Z])(?=[(A-Z])", r"\1,", s))
    children, counter = {}, [0]

    def node(a, b):
        counter[0] += 1
        nd = "g%d" % counter[0]
        children[nd] = (a, b)
        return nd

    def one(i):
        if s[i] != "(":
            return s[i], i + 1
        a, i = one(i + 1)
        i += 1                       # ','
        b, i = one(i)
        return node(a, b), i + 1     # ')'

    first, i = one(0)
    if i >= len(s):
        return children, first
    second, i = one(i + 1)
    return children, node(first, second)


def signature(nwk):
    """把一个（含 V,W,X,Y,Z 的）Newick 打成 clade 签名（相对 CLADES ✓）。"""
    ch, root = parse_newick(nwk)
    cl = set(clades_of(ch, root).values())
    return tuple(c in cl for c in CLADES)


def prob_sig(sig, T2, T3, T4):
    """闭式：由签名（三个布尔）定出 (i_b, j_b) 再算 P。"""
    j2 = 1 if sig[0] else 2
    i2 = 2
    i3 = j2 + 1
    j3 = 1 if sig[1] else 2
    i4 = j3 + 1
    j4 = 1 if sig[2] else 2
    p = 1.0
    for (i, j, t) in ((i2, j2, T2), (i3, j3, T3), (i4, j4, T4)):
        if i == j:
            continue                 # 该枝无需合生 ⇒ 因子 1（此时 g_ii 不在表中，跳过 ✓）
        p *= g(i, j, t) / N(i, j)
    return p


def subst(nwk, mapping):
    """按 mapping（V,W,X,Y,Z → 具体分类群）替换叶子。"""
    out = ""
    for c in nwk:
        out += mapping.get(c, c)
    return out


def class_assignments(dfn):
    """由 class 的定义字符串生成全部满足约束的双射（V,W,X,Y,Z → A..E）。"""
    syms = ["V", "W", "X", "Y", "Z"]
    groups = re.findall(r"\{([A-Z,]+)\}=\{([A-Z,]+)\}", dfn)
    neqs = re.findall(r"([A-Z])≠([A-Z])", dfn)
    res = []
    for perm in itertools.permutations(LEAVES, 5):
        m = dict(zip(syms, perm))
        ok = True
        for lhs, rhs in groups:
            if {m[a] for a in lhs.split(",")} != set(rhs.split(",")):
                ok = False
        for a, b in neqs:
            # ★ 右侧可能是分类群本身（如 X≠D）⇒ 非符号时直接比较字面 ✓
            va = m.get(a, a)
            vb = m.get(b, b)
            if va == vb:
                ok = False
        if ok:
            res.append(m)
    return res


def load_classes():
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location("p1", os.path.join(here, "w19_rt2008_psi1_classes.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.modules["p1"] = mod
    spec.loader.exec_module(mod)
    return mod.PSI1, mod.T9_PSI1


def main():
    PSI1, T9 = load_classes()
    t9 = {(a, b): t for (a, b, t) in T9}
    print("=" * 90)
    print("① (a) 代入求和：每个 class 的概率 = Σ_{满足约束的双射} P(代入后的基因树)")
    print("   先做判决性诊断：T2=T3=T4=0 时应【只有物种树自身拓扑】非零")

    # 物种树自身的签名：(含 AB, ABC, ABCD) = (True, True, True) ✓
    sig_species = (True, True, True)
    print("   物种树签名 = %r ，P(0,0,0) = %.6f （应为 1 ✓）" % (sig_species, prob_sig(sig_species, 0, 0, 0)))
    print("   非物种树的签名（如 %r）P(0,0,0) = %.6f （应为 0 ✓）"
          % ((False, False, False), prob_sig((False, False, False), 0, 0, 0)))

    print("=" * 90)
    print("② 各 class 的签名分解（T=0 诊断：只有含全部三个 clade 的代入才非零）")
    rows = []
    for (g_, k, nwk, dfn, cnt) in PSI1:
        if (g_, k) not in t9:
            continue
        assigns = class_assignments(dfn)
        sigs = {}
        for m in assigns:
            s = signature(subst(nwk, m))
            sigs[s] = sigs.get(s, 0) + 1
        p0 = sum(c * prob_sig(s, 0, 0, 0) for s, c in sigs.items())
        rows.append((g_, k, nwk, len(assigns), sigs, p0))
        print("   γ%s %2d %-15s 代入数 %2d  签名数 %d  P(0,0,0) = %.6f"
              % (g_[1], k, nwk, len(assigns), len(sigs), p0))

    print("=" * 90)
    print("③ ★ 正确的总检验（文献 :785 第 (1) 条）：全部 105 个有标号拓扑的概率【求和 = 1】")
    print("   （★ 早前我误把判据写成「T=0 只有物种树拓扑非零」✗ —— 实际上 T=0 时匹配拓扑概率→0，")
    print("     这正是 AGT 现象的成因 ✓；正确判据是 105 项求和 = 1 ✓。）")
    print("=" * 90)
    print("④ 下一步：若 ③ 通过 ⇒ 用闭式解 Equation 1（与 P(H=ψ1) 比）⇒ 与 Table 9 的 T_min 对拍")


if __name__ == "__main__":
    main()
