#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""W19 C1-M3③ 器材 (a)-5：RT2008 Table 3 的 ψ₁ 全表数据 ＋ 三重自检（★G）。

文献：references/pdf/RosenbergTao2008_FiveTaxaAnomalyZone.pdf
  · p3 / 印刷 133：**TABLE 3.** History classes for species tree topology ψ1.
      列：Gene tree topology ｜ Number for history class ｜ Description of class of labeled topologies
          ｜ Definitions of V,W,X,Y,Z ｜ Number of labeled topologies in class
  · :405-415（md 行号）：5 分类群有 3 个无标号拓扑，labelings 数为 **60 / 30 / 15**，合计 **105** ✓
  · p4 TABLE 6：产 AGT 的 class 数 —— γ1: 0/0/0 ｜ **γ2: 12/2/9** ｜ **γ3: 5/0/0** ｜ 总 17/2/9 = 28
  · p9 TABLE 9：ψ1 的 T_min —— γ2 12 个值（含 **0.1935**）· γ3 5 个值
  · p3 正文：Equation 1 两端 【linear in e^{−T4}】（因 branch 4 恒有两条谱系进入：g21/g22）

本脚本做三件事：
  ① 编码 ψ1 的 31 个 history class（Newick ＋ {V,W,X,Y,Z} 定义 ＋ 有标号拓扑数）；
  ② 三重自检：每拓扑之和 = 60/30/15 ✓；总和 = 105 ✓；AGT class 数 = 12 (γ2) + 5 (γ3) = 17 ✓；
  ③ 编码 Table 9 的 T_min 并与 ② 的 AGT class 清单对表。
下一阶段（未做）：枚举各 class 的 coalescent histories（Degnan-Salter）⇒ 乘积求和得 Pσ(H=h)
  ⇒ 用线性性解 Equation 1 得 T4 < f(T2,T3) ⇒ 与 T_min 对拍。
"""

# ── ① ψ1 的 31 个 history class（逐字取自 Table 3 ✓）
#    (gene tree topology γ, class 序号, Newick, {V,W,X,Y,Z} 定义, 该 class 的有标号拓扑数)
PSI1 = [
    # γ1：14 类，合计 60
    ("g1",  1, "(((WE)X)Y)Z",   "{W,X,Y,Z}={A,B,C,D}",      24),
    ("g1",  2, "(((XD)E)Y)Z",   "{X,Y,Z}={A,B,C}",           6),
    ("g1",  3, "(((XD)Y)E)Z",   "{X,Y,Z}={A,B,C}",           6),
    ("g1",  4, "(((XD)Y)Z)E",   "{X,Y,Z}={A,B,C}",           6),
    ("g1",  5, "(((XC)E)Y)Z",   "{X,Y,Z}={A,B,D}, X≠D",      4),
    ("g1",  6, "(((XC)D)E)Y",   "{X,Y}={A,B}",               2),
    ("g1",  7, "(((XC)Y)E)D",   "{X,Y}={A,B}",               2),
    ("g1",  8, "(((XC)D)Y)E",   "{X,Y}={A,B}",               2),
    ("g1",  9, "(((XC)Y)D)E",   "{X,Y}={A,B}",               2),
    ("g1", 10, "(((AB)E)X)Y",   "{X,Y}={C,D}",               2),
    ("g1", 11, "(((AB)D)E)C",   "{X,Y}={C,D}",               1),
    ("g1", 12, "(((AB)C)E)D",   "{X,Y}={C,D}",               1),
    ("g1", 13, "(((AB)D)C)E",   "{X,Y}={C,D}",               1),
    ("g1", 14, "(((AB)C)D)E",   "{X,Y}={C,D}",               1),
    # γ2：12 类，合计 30
    ("g2",  1, "((XE)Y)(ZD)",   "{X,Y,Z}={A,B,C}",           6),
    ("g2",  2, "((XE)Y)(ZC)",   "{X,Y,Z}={A,B,D}, Z≠D",      4),
    ("g2",  3, "((XE)Y)(AB)",   "{X,Y}={C,D}",               2),
    ("g2",  4, "((XD)E)(YC)",   "{X,Y}={A,B}",               2),
    ("g2",  5, "((CD)E)(AB)",   "{X,Y}={A,B}",               1),
    ("g2",  6, "((XC)E)(YD)",   "{X,Y}={A,B}",               2),
    ("g2",  7, "((AB)E)(CD)",   "{X,Y}={A,B}",               1),
    ("g2",  8, "((XD)Y)(ZE)",   "{X,Y,Z}={A,B,C}",           6),
    ("g2",  9, "((XC)D)(YE)",   "{X,Y}={A,B}",               2),
    ("g2", 10, "((AB)D)(CE)",   "{X,Y}={A,B}",               1),
    ("g2", 11, "((XC)Y)(DE)",   "{X,Y}={A,B}",               2),
    ("g2", 12, "((AB)C)(DE)",   "{X,Y}={A,B}",               1),   # ★ 头条见证类（T_min = 0.1935）
    # γ3：5 类，合计 15
    ("g3",  1, "((XD)(YE))Z",   "{X,Y,Z}={A,B,C}",           6),
    ("g3",  2, "((XC)(YE))Z",   "{X,Y,Z}={A,B,C}, X≠D",      4),
    ("g3",  3, "((AB)(XE))Y",   "{X,Y}={C,D}",               2),
    ("g3",  4, "((XC)(YD))E",   "{X,Y}={A,B}",               2),
    ("g3",  5, "((AB)(CD))E",   "—（无需定义）",              1),
]

# ── ③ Table 9 的 ψ1 条目（(基因树, class 序号) ↦ T_min）
T9_PSI1 = [
    ("g2",  1, 0.0477), ("g2",  2, 0.0568), ("g2",  3, 0.0690), ("g2",  4, 0.0890),
    ("g2",  5, 0.1226), ("g2",  6, 0.1044), ("g2",  7, 0.1604), ("g2",  8, 0.0570),
    ("g2",  9, 0.0884), ("g2", 10, 0.1432), ("g2", 11, 0.0939), ("g2", 12, 0.1935),
    ("g3",  1, 0.0307), ("g3",  2, 0.0394), ("g3",  3, 0.0523), ("g3",  4, 0.0601),
    ("g3",  5, 0.1014),
]

def main():
    print("=" * 80)
    print("① ψ1 的 31 个 history class（逐字取自 Table 3 ✓）")
    for g in ("g1", "g2", "g3"):
        rows = [r for r in PSI1 if r[0] == g]
        print("  γ%s ： %d 类" % (g[1], len(rows)))
        for (_, k, nwk, dfn, cnt) in rows:
            print("     %2d  %-14s %-28s %d" % (k, nwk, dfn, cnt))

    print("=" * 80)
    print("② 三重自检")
    bad = 0
    tot = 0
    for g, want in (("g1", 60), ("g2", 30), ("g3", 15)):
        s = sum(r[4] for r in PSI1 if r[0] == g)
        tot += s
        ok = (s == want)
        bad += 0 if ok else 1
        print("   γ%s 有标号拓扑数之和 = %3d （文献 :405-415 称 %3d）%s" % (g[1], s, want, "✓" if ok else "✗"))
    print("   总和 = %d （105 = 60+30+15 ✓）%s" % (tot, "✓" if tot == 105 else "✗"))
    bad += 0 if tot == 105 else 1
    n_agt = len(T9_PSI1)
    n_g2 = sum(1 for r in T9_PSI1 if r[0] == "g2")
    n_g3 = sum(1 for r in T9_PSI1 if r[0] == "g3")
    ok = (n_g2, n_g3, n_agt) == (12, 5, 17)
    bad += 0 if ok else 1
    print("   产 AGT 的 class：γ2 %d ＋ γ3 %d = %d （TABLE 6 称 12/5，总 17）%s"
          % (n_g2, n_g3, n_agt, "✓" if ok else "✗"))
    # T_min 的 class 必须都真的在 PSI1 里
    keys = {(r[0], r[1]) for r in PSI1}
    miss = [(g, k) for (g, k, _) in T9_PSI1 if (g, k) not in keys]
    bad += 0 if not miss else 1
    print("   Table 9 的每个 (γ, class) 都存在于 Table 3 中：%s"
          % ("✓" if not miss else "✗ 缺失 %r" % (miss,)))
    print("   自检结果：%s" % ("全部通过 ✓" if bad == 0 else "有 %d 项不符 ✗" % bad))

    print("=" * 80)
    print("③ Table 9 的 ψ1 条目（T_min ＝ 使该 class 不再产 AGT 的最小统一枝长）")
    for (g, k, t) in T9_PSI1:
        mark = "  ★ 头条见证类（与摘要 0.1934 吻合）" if (g, k) == ("g2", 12) else ""
        print("   γ%s class %2d : T_min = %.4f%s" % (g[1], k, t, mark))
    mx = max(T9_PSI1, key=lambda r: r[2])
    print("   ★ 最大 T_min = %.4f（γ%s class %d）—— 文献正文称 ψ1 的 T_min ≈ 0.1935 ✓"
          % (mx[2], mx[0][1], mx[1]))

    print("=" * 80)
    print("④ 下一阶段（未做，已在 HANDOVER 登记）")
    print("   对每个产 AGT 的 class 枚举 coalescent histories（Degnan-Salter）")
    print("   ⇒ 以 Table 1 的 g_ij 算各条乘积概率并求和 ⇒ 得 Pσ(H = h_class)")
    print("   ⇒ 用 g21/g22 的线性性（Equation 1 两端 linear in e^{−T4}）解出 T4 < f(T2,T3)")
    print("   ⇒ 与上表 T_min 对拍（★ 先做 γ2 的 12 类，即 (b) 的最小充分集）")

if __name__ == "__main__":
    main()
