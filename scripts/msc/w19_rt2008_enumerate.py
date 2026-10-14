r"""W19 C1-M3③ 器材 (b)：ψ₁ 的 coalescent-history 枚举（★ 进行中，状态如下 ✓）

★★★ 当前状态（2026-10-14，诚实记录 ✓）
  ✅ 已完成：**解析**（Table 3 全部 31 个 class 的记号都能解析成 5 叶 4 内部节点的二叉树 ✓）。
     ★ 记号两处约定（由 PDF 图像逐字读出 ✓）：
       (i)  **一切逗号全省略**（相邻子表达式直接并置：`(((W,E)X)Y)Z` ✓）；
       (ii) **外层根括号省略**（根的两棵子树并置 ✓）。
  ✅ 已完成：**coalescent-history 的候选枚举**（把 4 个基因树内部节点指派到 2/3/4 或
     「物种树根之上的无限长枝」✓；后者容量无限、概率因子 = 1 ✓）——
     得 γ₂ 每类 **19** 条、γ₃ 每类 **15** 条候选 ✓（重数结构对同类一致 ✓）。
  ✗ **未完成、且在修**（两处，缺一概率就不对 ✗）：
     (a) **`{V,W,X,Y,Z}` 代入**：class 的定义（如 `{X,Y}={A,B}` ✓）决定**具体有标号基因树** ✓
         ⇒ class 的概率 = **对允许代入的求和** ✓（这正是"class"的含义 ✓）；
     (b) **拓扑细化检查**：目前只查了「合生发生在其儿子所在枝之上」✓，
         未查「基因树形状能否由物种树上的合生实现」✓ ⇒ 需补"基因树叶子 → 物种树叶子"的映射一致性 ✓。
  ★ **判决性诊断（下一轮用它验证修好没有 ✓）**：`T₂=T₃=T₄=0` 时
     **只有物种树自身的拓扑**应有概率 1 ✓、其余全为 0 ✓；
     而当前脚本对**每个** class 都给出 `P(0,0,0) = 1` ✗ ⇒ 明确说明 (a)(b) 未补 ✓。

★ 文献：RosenbergTao2008_FiveTaxaAnomalyZone.{md,pdf}
  · p3 正文：Equation 1 两端 **linear in e^{−T4}** ✓（branch 4 恒有两条谱系进入 ✓，
    `g₂₁(T₄)=1−e^{−T₄}` ✓ / `g₂₂(T₄)=e^{−T₄}` ✓）；
  · `:380-389`：AGT 定义 —— `h` 是 `σ=(ψ,T)` 的 AGT ⟺ `P_σ(H=h) > P_σ(H=ψ)` ✓（Equation 1 ✓）；
  · p9 TABLE 9：ψ₁ 的 17 个产 AGT 的 (γ, class) 各自的 `T_min` ✓；
  · p3 TABLE 3：ψ₁ 的 31 个 history class（已由 `w19_rt2008_psi1_classes.py` 编码 ✓）。

★ 物种树 ψ1 = `(((A,B),C),D),E)`（内部枝自下而上 b2,b3,b4 ✓，三条各只有 2 条谱系进入 ✓
  ⇒ 每枝因子 ∈ {g21, g22} ✓ ⇒ `P = A(T₂,T₃)·(1−e^{−T₄}) + B(T₂,T₃)·e^{−T₄}` ✓ 与文献一致 ✓）。
"""
import itertools, math, os, importlib.util, sys

# ── 物种树 ψ1 = (((A,B),C),D),E) —— 叶 0..4 = A..E；内部节点 5,6,7,8
SP = {5: (0, 1), 6: (5, 2), 7: (6, 3), 8: (7, 4)}
BRANCH_OF_SPNODE = {5: 2, 6: 3, 7: 4}      # 承载该节点的内部枝
ENTERING = {2: 2, 3: 2, 4: 2}              # 每条内部枝的进入谱系数
ROOT_BRANCH = 5                            # ★ 物种树根之上的"无限长枝"：容量无限，因子 = 1

LEAFNAME = {0: "A", 1: "B", 2: "C", 3: "D", 4: "E"}


def g21(t):   # g21 = 1 − e^{−t}
    return 1 - math.exp(-t)


def g22(t):   # g22 = e^{−t}
    return math.exp(-t)


def parse_newick_rootless(s):
    """解析 Table 3 的记号。

    ★ 两处记号约定（由 PDF 图像逐字读出 ✓）：
      (i)  樱桃写作【并置的两个字母】：`WE` 即 `(W,E)` ⇒ 先插逗号 ✓；
      (ii) 根的两棵子树【并置】、外层根括号可省：`((XE)Y)(ZD)` 即 `(((X,E)Y)(Z,D))` ✓。
    """
    import re
    # ★ 论文记号的通则：**一切逗号全省略**（相邻的两个子表达式直接并置 ✓）。
    #   故在所有"应当是逗号"的位置补上：`)` 或字母 之后紧接 `(` 或字母 ⇒ 插逗号 ✓。
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"(\)|[A-Z])(?=[(A-Z])", r"\1,", s)
    s = re.sub(r",+", ",", s)
    children = {}
    counter = [0]

    def node(a, b):
        counter[0] += 1
        nd = "g%d" % counter[0]
        children[nd] = (a, b)
        return nd

    def parse_one(i):
        """从位置 i 解析【一棵完整的子树】；返回 (节点, 新位置)。"""
        if s[i] != "(":
            # ★ 叶标签一律【单字母】（Table 3 的记号 ✓）；不可贪婪读取，否则 "WE" 会被并成一个叶 ✗
            assert s[i].isalpha(), (s, i)
            return s[i], i + 1
        i += 1                              # 跳过 '('
        a, i = parse_one(i)
        assert s[i] == ",", (s, i)
        i += 1
        b, i = parse_one(i)
        assert s[i] == ")", (s, i)
        return node(a, b), i + 1

    first, i = parse_one(0)
    if i >= len(s):                          # 一棵完整树（有外层根括号）
        return children, first
    assert s[i] == ",", (s, i, s[i:])        # 根的两棵子树之间的分隔（补逗号后必为 ','）
    second, i = parse_one(i + 1)             # 第二棵子树 ⇒ 在外层合并成根
    assert i == len(s), (s, i, s[i:])
    return children, node(first, second)


def enumerate_assignments(children, internal):
    """枚举 基因树内部节点 → 物种树内部枝 (2/3/4) 的合法指派（coalescent histories）。

    合法性（Degnan-Salter 在 caterpillar 物种树上的化用 ✓）：
      ① 每个节点所在枝号 ≥ 其两个儿子所在枝号（叶 = 0）—— 合生必须发生在其儿子之上；
      ② 每条枝上的合生次数 ≤ i_b − 1（须留至少 1 条谱系继续上行）。
    """
    out = []
    for assign in itertools.product((2, 3, 4, ROOT_BRANCH), repeat=len(internal)):
        am = dict(zip(internal, assign))
        ok = True
        for nd in internal:
            for c in children[nd]:
                lb = am[c] if c in am else 0
                if am[nd] < lb:
                    ok = False
        if not ok:
            continue
        pb = {2: 0, 3: 0, 4: 0, ROOT_BRANCH: 0}
        for nd in internal:
            pb[am[nd]] += 1
        if any(pb[b] > ENTERING[b] - 1 for b in (2, 3, 4)):
            continue        # 根上枝容量无限 ✓
        out.append(pb)
    return out


def multiplicity(pb_list):
    """合并同 (k2,k3,k4) 的 history，返回 {(k2,k3,k4): 重数}。"""
    m = {}
    for pb in pb_list:
        key = (pb[2], pb[3], pb[4], pb[ROOT_BRANCH])
        m[key] = m.get(key, 0) + 1
    return m


def prob(merged, T2, T3, T4):
    """P = Σ_history Π_b (k_b==1 ? g21(T_b) : g22(T_b))。"""
    Ts = {2: T2, 3: T3, 4: T4}
    tot = 0.0
    for (k2, k3, k4, k5), mult in merged.items():
        p = 1.0
        for b, k in ((2, k2), (3, k3), (4, k4)):
            p *= g21(Ts[b]) if k == 1 else g22(Ts[b])
        # 根上枝（无限长）因子恒为 1 ✓
        tot += mult * p
    return tot


def load_psi1():
    here = os.path.dirname(os.path.abspath(__file__))
    spec = importlib.util.spec_from_file_location("psi1c", os.path.join(here, "w19_rt2008_psi1_classes.py"))
    mod = importlib.util.module_from_spec(spec)
    sys.modules["psi1c"] = mod
    spec.loader.exec_module(mod)
    return mod.PSI1, mod.T9_PSI1


def main():
    PSI1, T9 = load_psi1()
    t9keys = {(a, b) for (a, b, _) in T9}
    print("=" * 92)
    print("① 解析自检：Table 3 全部 31 个 class 的 Newick 是否都能解析成 5 叶树")
    parsed = {}
    bad = 0
    for (g, k, nwk, dfn, cnt) in PSI1:
        try:
            ch, root = parse_newick_rootless(nwk)
            leaves = set()
            def walk(n):
                if n in ch:
                    for c in ch[n]:
                        walk(c)
                else:
                    leaves.add(n)
            walk(root)
            if len(leaves) != 5 or len(ch) != 4:
                print("   ✗ γ%s %2d %-16s 解析得 %d 叶 / %d 内部节点" % (g[1], k, nwk, len(leaves), len(ch)))
                bad += 1
            parsed[(g, k)] = (ch, root)
        except Exception as e:
            print("   ✗ γ%s %2d %-16s 解析异常：%s" % (g[1], k, nwk, e))
            bad += 1
    print("   31 个 class：解析失败 %d 个 %s" % (bad, "✓ 全部 5 叶 4 内部节点" if bad == 0 else "✗"))

    print("=" * 92)
    print("② 对 Table 9 的 17 个 ψ1 条目，枚举 history 并算 P(0,0,0)（全部 k=0 的重数）")
    print("   γ  cls  Newick            #hist  重数表(k2,k3,k4)               P(0,0,0)")
    for (g, k, nwk, dfn, cnt) in PSI1:
        if (g, k) not in t9keys:
            continue
        ch, root = parsed[(g, k)]
        internal = list(ch.keys())
        hist = enumerate_assignments(ch, internal)
        m = multiplicity(hist)
        p0 = prob(m, 0.0, 0.0, 0.0)
        print("   %-2s %3d  %-16s  %2d   %-30s %.6f"
              % (g, k, nwk, len(hist), str(m), p0))

    print("=" * 92)
    print("③ 下一步（未做，如实登记 ✓）：")
    print("   · 需要每个 class 的【完整】线性式 P = A·(1−e^{−T4}) + B·e^{−T4} 的 A、B 系数")
    print("     （本脚本已给 T2=T3=T4=0 的取值；A、B 需按 e^{−T2}, e^{−T3} 的多项式展开）")
    print("   · 还需 P_σ(H = ψ1)（物种树自身的概率，其 class 在 Table 3 的 γ1 段）")
    print("   · 解 Equation 1 ⇒ T4 < f(T2,T3) ⇒ 与 Table 9 的 T_min 对拍")


if __name__ == "__main__":
    main()
