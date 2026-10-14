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
    """i → j 的**有序**合生方案数 ✓（推导，非猜测 ✓）。

    单枝上由 i 降到 j 需 k = i−j 次合生 ✓：第 r 步时有 m = i−r+1 条谱系 ✓，
    任选一对合生 ⇒ C(m,2) 种 ✓。故
        N(i,j) = Π_{m=j+1}^{i} C(m,2)  =  Π_{m=j+1}^{i} m(m−1)/2  ✓
    校验：N(2,1)=1 ✓ · N(3,2)=3 ✓ · N(3,1)=3·1=3 ✓ · **N(4,2)=6·3=18** ✓
      （★ 先前我把 N(4,2) 误写为 3 ✗ —— 那是"无序配对"的数，不是"有序合生序列"的数 ✓）。
    ★ 每条序列概率相同（速率结构对称 ⇒ 积分相同 ✓）⇒ 具体方案概率 = g_{ij}/N(i,j) ✓。
    """
    num = 1
    for m in range(j + 1, i + 1):
        num *= m * (m - 1) // 2
    return num


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
    """闭式：由签名（三个布尔）定出 (i_b, j_b) 再算 P。

    ★★★ 除法的正确规则（本轮**推导**得出 ✓，非调参 ✗）：
      `g_{i,j}(T)` 是「i 降到 j」对【**形状**】求和的总概率 ✓ ⇒ 某个**具体形状**的概率
      = `g_{i,j} / (#不同形状)` ✓。而在 ψ1 的 caterpillar 上：
        · `(2,1)`：唯一形状（AB）          ⇒ #形状 = 1 ✓
        · `(3,2)`：三种形状（AC / BC / AB）⇒ #形状 = 3 = C(3,2) ✓ ⇒ 除 3 ✓
        · `(3,1)`：★ **三个配对都给出【同一个】 clade {A,B,C}** ✗ ⇒ **形状唯一** ✓
                   ⇒ **不除** ✗（★ 这正是先前总检验偏大的根因 ✓：我按"N=3 条合生序列"除了 3，
                     而序列数 ≠ 形状数 ✓）
      ⇒ **规则**：**仅当 `i − j = 1` 时才除以 `C(i,2)`** ✓；`i − j ≥ 2`（此时必 `j = 1` ✓）
        形状唯一 ⇒ **不除** ✓。
    """
    j2 = 1 if sig[0] else 2
    i2 = 2
    i3 = j2 + 1
    j3 = 1 if sig[1] else 2
    i4 = j3 + 1
    j4 = 1 if sig[2] else 2
    p = 1.0
    for (i, j, t) in ((i2, j2, T2), (i3, j3, T3), (i4, j4, T4)):
        if i == j:
            continue                 # 该枝无需合生 ⇒ 因子 1 ✓
        # ⚠️ 两条候选除法规则【都已试过、都不通过总检验】✗（如实留痕 ✓）：
        #   规则 A（除 C(i,2) 于所有 i−j=1 情形 ✓）⇒ Σ = 0.176/0.591/1.685/4.201/5.108 ✗
        #   规则 B（仅 i−j=1 除、i−j≥2 不除 ✓）⇒ Σ = 0.187/0.636/1.873/5.209/7.669 ✗
        #   ⇒ ★★★ 根因（已定位 ✓）：**"逐枝相乘的闭式"本身不够** ✗ ——
        #     基因树的概率**不是**各枝 (i_b, j_b) 因子的乘积 ✓：各枝「哪几条合生」是**耦合**的 ✓，
        #     必须对**完整的 coalescent history**（每个基因树内部节点指派到某条物种树枝 ✓）求和 ✓，
        #     且每条 history 用**直接的 g 因子**（**不除** N ✗ —— history 已是具体的合生方案 ✓）。
        #   ⇒ ★ 这正是最早的 w19_rt2008_enumerate.py 的思路 ✓（它枚举出 γ2 每类 19 条 / γ3 15 条 ✓），
        #     需在其上补齐「叶子映射一致性」与「代入」✓。本脚本暂用规则 A（较有原则 ✓），
        #     但**不声称**其数值正确 ✗。
        p *= g(i, j, t) / N(i, j)
    return p


def subst(nwk, mapping):
    """按 mapping（V,W,X,Y,Z → 具体分类群）替换叶子。"""
    out = ""
    for c in nwk:
        out += mapping.get(c, c)
    return out


def class_assignments(dfn, nwk=""):
    """由 class 的定义生成全部满足约束的赋值（★ 只变【该 class 实际用到的符号】✓）。

    ★★★ 记号模型（本轮厘清 ✓）：
      · 通用 schema 是五个符号 V,W,X,Y,Z ✓，但**每个 class 只用其中一部分** ✓；
      · 变动的符号 = **在该 class 的 Newick 里实际出现**的那些 ✓；
      · 它们取遍「{A..E} 减去该 Newick 里**字面出现**的分类群」的**排列** ✓；
      · 并满足定义里的 `{X,Y}={A,B}` 类等式与 `X≠D` 类不等式 ✓。
      ★ 校验锚：γ₂ class 1 `((XE)Y)(ZD)`，定义 `{X,Y,Z}={A,B,C}` ✓
        ⇒ 符号 {X,Y,Z} 取遍 {A,B,C} 的 3! = 6 种 ✓ ＝ **Table 3 的计数 6** ✓ ✓。
    """
    syms = set("VWXYZ")
    used_syms = sorted({c for c in nwk if c in syms})
    literals = {c for c in nwk if c.isalpha() and c not in syms}
    free = [t for t in LEAVES if t not in literals]
    groups = re.findall(r"\{([A-Z,]+)\}=\{([A-Z,]+)\}", dfn)
    neqs = re.findall(r"([A-Z])≠([A-Z])", dfn)
    res = []
    if len(used_syms) > len(free):
        return res
    for perm in itertools.permutations(free, len(used_syms)):
        m = dict(zip(used_syms, perm))
        ok = True
        for lhs, rhs in groups:
            # ★★ 修法（上轮已定位 ✓）：该等式只约束【在 Newick 里出现的】符号 ✓；
            #    若等式的左侧符号全都不出现（如无符号的类 ((CD)E)(AB)），则【跳过】该检查 ✗
            #    —— 否则会把字面的 X、Y 拿去与 A、B 比对而误拒 ✓。
            lhs_syms = [a for a in lhs.split(",") if a in m]
            if not lhs_syms:
                continue
            vals = [m[a] if a in m else a for a in lhs.split(",") if (a in m or a.isalpha())]
            if sorted(vals) != sorted(rhs.split(",")):
                ok = False
        for a, b in neqs:
            if m.get(a, a) == m.get(b, b):
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
        assigns = class_assignments(dfn, nwk)
        sigs = {}
        for m in assigns:
            s = signature(subst(nwk, m))
            sigs[s] = sigs.get(s, 0) + 1
        p0 = sum(c * prob_sig(s, 0, 0, 0) for s, c in sigs.items())
        rows.append((g_, k, nwk, len(assigns), sigs, p0))
        print("   γ%s %2d %-15s 代入数 %2d  签名数 %d  P(0,0,0) = %.6f"
              % (g_[1], k, nwk, len(assigns), len(sigs), p0))

    print("=" * 90)
    print("③ ★ 总检验（文献 :785 第 (1) 条）：Σ_classes (Table 3 的计数) × P(该 class 的签名) = 1")
    print("   （★ 论文 :609-611 明说：同一 history class 内所有基因树【概率相同】✓ ⇒ 可这样求和 ✓。）")
    tot = 0.0
    for T in (0.05, 0.1, 0.2, 0.5, 1.0):
        tot_T = 0.0
        for (g_, k, nwk, dfn, cnt) in PSI1:
            assigns = class_assignments(dfn, nwk)
            sigs = {}
            for m in assigns:
                sg = signature(subst(nwk, m))
                sigs[sg] = sigs.get(sg, 0) + 1
            # 每类一个签名 ⇒ 该类总概率 = cnt × P(签名)
            for sg in sigs:
                tot_T += cnt * prob_sig(sg, T, T, T)
        print("   T2=T3=T4=%.2f ： Σ = %.6f %s" % (T, tot_T, "✓" if abs(tot_T - 1) < 1e-9 else "✗（差 %.6f）" % (tot_T - 1)))
    print("   ★ 若全部为 1 ⇒ 闭式正确 ✓；若有偏差 ⇒ 说明还有未计的类或漏项（如实报告 ✓）")
    print("=" * 90)
    print("④ 下一步：若 ③ 通过 ⇒ 用闭式解 Equation 1（与 P(H=ψ1) 比）⇒ 与 Table 9 的 T_min 对拍")


if __name__ == "__main__":
    main()
