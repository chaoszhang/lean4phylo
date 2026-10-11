#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W13a 数值对拍脚本 —— 位点权重函数的**概率归一**与**一致有界**（规格缺口 B3）。

对照的 Lean 声明（`Phylo/Stat/SiteWeightMeasurable.lean`）：
  * `sum_patternProb`      : ∑_σ patternProb t σ = 1                （**无条件**）
  * `patternProb_nonneg`   : 0 ≤ patternProb t σ                     （需 t ≥ 0）
  * `abs_patternProb_le_one`: |patternProb t σ| ≤ 1                  （需 t ≥ 0）
  * `abs_wJCR_le_one`      : |wJCR T σ| ≤ 1
  * `abs_geneScore_le_one` : |geneScore S l lx T| ≤ 1                （需 l ≥ 0、lx ≥ 0）

本脚本按 `Phylo/JukesCantor.lean` / `Phylo/Stat/CASTERGeneTree.lean` 的**定义逐字**重写
（不读 `.olean`），并：
  1. 对随机非负枝长**穷举全部 256 个位点模式**核对 ∑ = 1；
  2. 对三个形状 S × 三个拓扑 T × 随机非负枝长核对 |geneScore| ≤ 1；
  3. **阴性对照**：取负枝长，展示 ∑ patternProb = 1 仍成立（行和恒等式不依赖符号），
     但 |patternProb| ≤ 1 与 |geneScore| ≤ 1 **失效** —— 这正是 Lean 侧必须有
     `ht : ∀ i, 0 ≤ t i` 的原因（文件头 §3 的 ★D 判断）。
"""
import itertools
import random

# ---- 字母表 Fin 4：0=A, 1=G, 2=C, 3=T ----
MODES = list(itertools.product(range(4), repeat=4))  # 256 个位点模式


def e(a):
    import math
    return math.exp(-(4.0 / 3.0) * a)


def off(a):
    return 0.25 - 0.25 * e(a)


def lam(a):
    return 0.25 + 0.75 * e(a)


def kernel(t, s, sp):
    return lam(t) if s == sp else off(t)


def patternProb(t, sigma):
    tot = 0.0
    for a in range(4):
        for b in range(4):
            tot += (kernel(t[0], a, sigma[0]) * kernel(t[1], a, sigma[1])
                    * kernel(t[2], a, b)
                    * kernel(t[3], b, sigma[2]) * kernel(t[4], b, sigma[3]))
    return 0.25 * tot


# ---- Topo / perm（逐字对照 CASTERWeights.lean）----
# perm .ab_cd i = i ; perm .ac_bd i = swap 1 2 i ; perm .ad_bc i = swap 1 2 (swap 1 3 i)
PERM = {
    'ab_cd': (0, 1, 2, 3),
    'ac_bd': (0, 2, 1, 3),
    'ad_bc': (0, 3, 1, 2),
}
SIDES_PERM = (2, 3, 0, 1)  # (0 2)(1 3)


def wJCBase(b):
    """+1 / -1/2 / 0（逐字对照 CASTERWeights.wJCBase）。"""
    if b[0] == b[1] and b[2] == b[3] and b[0] != b[2]:
        return 1.0
    if ((b[0] == b[1] and b[2] != b[3] and b[2] != b[0] and b[3] != b[0]) or
            (b[2] == b[3] and b[0] != b[1] and b[0] != b[2] and b[1] != b[2])):
        return -0.5
    return 0.0


def wJC(T, sigma):
    p = PERM[T]
    return wJCBase(tuple(sigma[p[i]] for i in range(4)))


def canonLen(S, l, lx):
    p = PERM[S]
    return [l[p[0]], l[p[1]], lx, l[p[2]], l[p[3]]]


def geneScore(S, l, lx, T):
    p = PERM[S]
    tot = 0.0
    for sigma in MODES:
        comp = tuple(sigma[p[i]] for i in range(4))
        tot += wJC(T, sigma) * patternProb(canonLen(S, l, lx), comp)
    return tot


def main():
    random.seed(20261011)
    worst_sum = 0.0
    worst_pp = 0.0
    worst_gs = 0.0
    n_cases = 0

    # (1)+(2) 非负枝长
    for _ in range(400):
        t = [random.choice([0.0, 1e-9, 0.01, 0.3, 1.0, 5.0, 50.0, random.random() * 20])
             for _ in range(5)]
        s = sum(patternProb(t, sig) for sig in MODES)
        worst_sum = max(worst_sum, abs(s - 1.0))
        worst_pp = max(worst_pp, max(abs(patternProb(t, sig)) for sig in MODES))
        l = [random.random() * 5 for _ in range(4)]
        lx = random.random() * 5
        for S in PERM:
            for T in PERM:
                worst_gs = max(worst_gs, abs(geneScore(S, l, lx, T)))
        n_cases += 1
    # 边界：全零枝长
    t0 = [0.0] * 5
    worst_sum = max(worst_sum, abs(sum(patternProb(t0, sig) for sig in MODES) - 1.0))
    worst_gs = max(worst_gs, max(abs(geneScore(S, [0.0] * 4, 0.0, T))
                                 for S in PERM for T in PERM))
    # 边界：极小/极大
    for t in ([1e-6] * 5, [1e-6, 1e6, 1e-6, 1e6, 1e-6], [100.0] * 5):
        worst_sum = max(worst_sum, abs(sum(patternProb(t, sig) for sig in MODES) - 1.0))
        worst_pp = max(worst_pp, max(abs(patternProb(t, sig)) for sig in MODES))

    print("=== 非负枝长（400 组随机 + 边界） ===")
    print("  cases                       : %d (+3 边界)" % n_cases)
    print("  max |∑_σ patternProb − 1|   : %.3e   [Lean: sum_patternProb]" % worst_sum)
    print("  max |patternProb|           : %.6f   [Lean: abs_patternProb_le_one ⇒ ≤ 1]" % worst_pp)
    print("  max |geneScore| (9 组 S×T)  : %.6f   [Lean: abs_geneScore_le_one ⇒ ≤ 1]" % worst_gs)
    ok1 = worst_sum < 1e-9 and worst_pp <= 1.0 + 1e-12 and worst_gs <= 1.0 + 1e-12
    print("  verdict                     : %s" % ("PASS" if ok1 else "FAIL"))

    # (3) 阴性对照：负枝长
    print("=== 阴性对照：负枝长（Lean 侧必须带 ∀ i, 0 ≤ t i） ===")
    tneg = [-2.0, -2.0, -2.0, -2.0, -2.0]
    sneg = sum(patternProb(tneg, sig) for sig in MODES)
    ppmax = max(abs(patternProb(tneg, sig)) for sig in MODES)
    gsmax = max(abs(geneScore(S, [-2.0] * 4, -2.0, T)) for S in PERM for T in PERM)
    print("  ∑_σ patternProb(−2,…,−2)   : %.10f  (仍 = 1 ⇒ 归一不依赖非负性)" % sneg)
    print("  max |patternProb|           : %.4f   (≫ 1 ⇒ 有界性**失效**)" % ppmax)
    print("  max |geneScore|             : %.4f   (≫ 1 ⇒ 有界性**失效**)" % gsmax)
    print("  verdict                     : %s" % ("PASS（阴性对照如预期）"
                                                 if ppmax > 1.0 and gsmax > 1.0
                                                 else "FAIL（预期负枝长应破坏界）"))


if __name__ == '__main__':
    main()
