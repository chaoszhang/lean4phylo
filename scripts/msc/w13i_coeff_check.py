#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W13i 数值复核脚本 —— `Phylo/Stat/GeneTreeHmeasDischarge.lean` 的两条 ★D 论断

对应文件：`Phylo/Stat/GeneTreeHmeasDischarge.lean`（W13i）
依赖：无（纯标准库，外部依赖原则）

## 本脚本复核什么

### A. `geneScore` **不是**概率表（文件 §1 的 ★D 论断）
从库内 `Phylo/Stat/CASTERWeights.lean` 的**字面定义**复刻：

    wJCBase b = pos      if b0=b1 and b2=b3 and b0≠b2
              = negHalf  if (b0=b1 and b2≠b3 and b2≠b0 and b3≠b0)
                          or (b2=b3 and b0≠b1 and b0≠b2 and b1≠b2)
              = zero     otherwise
    perm  ab_cd = id,  ac_bd = (0,2,1,3),  ad_bc = (0,3,1,2)
    wJC T σ = wJCBase (fun i => σ (perm T i))
    wJCR    = toReal  (pos ↦ 1, negHalf ↦ -1/2, zero ↦ 0)

并复核库内**已有定理**的三个计数（`card_pos` / `card_neg` / `card_zero`）与权重和
（`sum_wJC_rat` 的实数版 `∑_σ wJCR T σ = -12`）。

再复刻 `patternProb` / `canonLen` / `geneScore`（`Phylo/JukesCantor.lean` ·
`Phylo/Stat/CASTERGeneTree.lean`）：

    kernel t s s' = off t + [s = s'] * e t,   off t = 1/4 - 1/4 e t,  e t = exp(-(4/3) t)
    patternProb t σ = (1/4) Σ_a Σ_b kernel(t0,a,σ0) kernel(t1,a,σ1) kernel(t2,a,b)
                                       kernel(t3,b,σ2) kernel(t4,b,σ3)
    canonLen S l lx = ![l (perm S 0), l (perm S 1), lx, l (perm S 2), l (perm S 3)]
    geneScore S l lx T = Σ_σ wJCR T σ * patternProb (canonLen S l lx) (σ ∘ perm S)

并**实测**：(i) 存在让 `geneScore` 取**负值**的枝长；(ii) `Σ_T geneScore S l lx T ≠ 1`。
⇒ 这两条一起说明「把 `freqOf` 的分量**直接取成 `geneScore`**」是不可能的
（`QuartetFreq.p_nonneg` / `p_sum_one` 会失败）——这正是新文件 §1 换用「平方 ＋ 归一化」的理由。

### B. 新文件的 `siteCoeff` 是**单位分解**（文件 §2）
    siteCoeff φ T g = ((geneScore T (φ g).1 (φ g).2 T)^2 + 1) / Σ_{T'} ((geneScore T' ...)^2 + 1)
实测：对任意实数三元组（含负值、零值、极端值）都 `0 ≤ siteCoeff` 且 `Σ_T siteCoeff = 1`。

### C. `variance_empFreq_gap` 去掉 `hmean` 后**为假**（文件 §7）
反例算术：`ind ≡ 1`、`p = 1/2` 时结论要求 `(1-1/2)^2 = p(1-p)/n`，即 `1/4 = 1/(4n)`；
`n = 2` 时 `1/4 ≠ 1/8`。

用法：`python3 scripts/msc/w13i_coeff_check.py`（exit 0 = 全部通过）
"""

import itertools
import math
import random
import sys

# ---------------------------------------------------------------------------
# A1. 从 CASTERWeights.lean 字面复刻的权重表
# ---------------------------------------------------------------------------

POS, NEG, ZERO = "pos", "negHalf", "zero"
TO_REAL = {POS: 1.0, NEG: -0.5, ZERO: 0.0}

PERM = {
    "ab_cd": (0, 1, 2, 3),
    "ac_bd": (0, 2, 1, 3),          # Equiv.swap 1 2
    "ad_bc": (0, 3, 1, 2),          # Equiv.swap 1 2 * Equiv.swap 1 3
}


def wJCBase(b):
    """`Phylo/Stat/CASTERWeights.lean:188` 的逐字复刻。"""
    if b[0] == b[1] and b[2] == b[3] and b[0] != b[2]:
        return POS
    if ((b[0] == b[1] and b[2] != b[3] and b[2] != b[0] and b[3] != b[0])
            or (b[2] == b[3] and b[0] != b[1] and b[0] != b[2] and b[1] != b[2])):
        return NEG
    return ZERO


def wJC(T, sigma):
    p = PERM[T]
    return wJCBase(tuple(sigma[p[i]] for i in range(4)))


def wJCR(T, sigma):
    return TO_REAL[wJC(T, sigma)]


# ---------------------------------------------------------------------------
# A2. JC69 位点模式概率 与 geneScore
# ---------------------------------------------------------------------------

def kernel(t, s, s1):
    off = 0.25 - 0.25 * math.exp(-(4.0 / 3.0) * t)
    e = math.exp(-(4.0 / 3.0) * t)
    return off + (e if s == s1 else 0.0)


def patternProb(t, sigma):
    """`Phylo/JukesCantor.lean:270` 的逐字复刻（Fin 5 → 列表）。"""
    acc = 0.0
    for a in range(4):
        for b in range(4):
            acc += (kernel(t[0], a, sigma[0]) * kernel(t[1], a, sigma[1])
                    * kernel(t[2], a, b) * kernel(t[3], b, sigma[2])
                    * kernel(t[4], b, sigma[3]))
    return acc / 4.0


def canonLen(S, l, lx):
    p = PERM[S]
    return [l[p[0]], l[p[1]], lx, l[p[2]], l[p[3]]]


def geneScore(S, l, lx, T):
    t = canonLen(S, l, lx)
    p = PERM[S]
    tot = 0.0
    for sigma in itertools.product(range(4), repeat=4):
        tot += wJCR(T, sigma) * patternProb(t, tuple(sigma[p[i]] for i in range(4)))
    return tot


# ---------------------------------------------------------------------------
# B. 新文件的 siteCoeff
# ---------------------------------------------------------------------------

def siteCoeff(gs):
    """`Phylo/Stat/GeneTreeHmeasDischarge.lean` 的 `siteCoeff`（`gs` = 三个拓扑上的 geneScore）。"""
    nums = [g * g + 1.0 for g in gs]
    den = sum(nums)
    return [n / den for n in nums]


# ---------------------------------------------------------------------------
# 主检验
# ---------------------------------------------------------------------------

FAIL = []


def check(name, cond, detail=""):
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAIL.append(name)
    print("[%s] %s%s" % (tag, name, ("  -- " + detail) if detail else ""))


def main():
    print("=" * 78)
    print("A. geneScore 不是概率表（文件 §1 的 ★D 论断）")
    print("=" * 78)

    # A-1 库内定理的三个计数 + 权重和
    for T in PERM:
        vals = [wJC(T, s) for s in itertools.product(range(4), repeat=4)]
        c_pos = vals.count(POS)
        c_neg = vals.count(NEG)
        c_zero = vals.count(ZERO)
        tot = sum(TO_REAL[v] for v in vals)
        check("card_pos  (%s) = 12" % T, c_pos == 12, "got %d" % c_pos)
        check("card_neg  (%s) = 48" % T, c_neg == 48, "got %d" % c_neg)
        check("card_zero (%s) = 196" % T, c_zero == 196, "got %d" % c_zero)
        check("sum wJCR  (%s) = -12" % T, abs(tot + 12.0) < 1e-12, "got %.6f" % tot)

    # A-2 patternProb 是概率分布（复刻 `sum_patternProb`）
    rnd = random.Random(20261012)
    for _ in range(5):
        t = [rnd.uniform(0.0, 2.0) for _ in range(5)]
        tot = sum(patternProb(t, s) for s in itertools.product(range(4), repeat=4))
        check("Σ_σ patternProb = 1（随机枝长）", abs(tot - 1.0) < 1e-12, "got %.15f" % tot)

    # A-3 geneScore 可负 + 三个拓扑上的和不等于 1
    worst = None
    sumbad = []
    for S in PERM:
        for _ in range(300):
            l = [rnd.uniform(0.0, 1.5) for _ in range(4)]
            lx = rnd.uniform(0.0, 1.5)
            gs = [geneScore(S, l, lx, T) for T in PERM]
            s = sum(gs)
            if abs(s - 1.0) > 1e-9:
                sumbad.append((S, l, lx, s))
            for T, g in zip(PERM, gs):
                if g < 0.0 and (worst is None or g < worst[0]):
                    worst = (g, S, T, l, lx)

    check("∃ 枝长使 geneScore < 0", worst is not None,
          ("min geneScore = %.6f (S=%s, T=%s)" % (worst[0], worst[1], worst[2])) if worst else "none found")
    check("Σ_T geneScore ≠ 1（不是概率表）", len(sumbad) > 0,
          "%d/%d 组样本满足 Σ_T geneScore ≠ 1；例：S=%s Σ=%.6f"
          % (len(sumbad), 3 * 300, sumbad[0][0], sumbad[0][3]) if sumbad else "none")

    # A-4 退化枝长（l = lx = 0）上 geneScore = 0（可解析核对）
    gs0 = [geneScore("ab_cd", [0.0, 0.0, 0.0, 0.0], 0.0, T) for T in PERM]
    check("退化枝长 l=lx=0 ⇒ geneScore = 0（三个拓扑）",
          all(abs(g) < 1e-12 for g in gs0),
          "got %s" % ["%.3e" % g for g in gs0])

    print()
    print("=" * 78)
    print("B. siteCoeff 是单位分解（文件 §2；含负 geneScore 的情形）")
    print("=" * 78)
    cases = [[0.0, 0.0, 0.0], [-5.0, 3.0, 0.0], [1e6, -1e6, 0.0], [0.25, 0.25, -0.5]]
    for _ in range(200):
        cases.append([rnd.uniform(-10.0, 10.0) for _ in range(3)])
    # 真实的 (geneScore ab_cd, ac_bd, ad_bc) 三元组
    for S in PERM:
        for _ in range(50):
            l = [rnd.uniform(0.0, 1.5) for _ in range(4)]
            lx = rnd.uniform(0.0, 1.5)
            cases.append([geneScore(S, l, lx, T) for T in PERM])
    bad_nn = 0
    bad_sum = 0
    for gs in cases:
        c = siteCoeff(gs)
        if any(x < 0.0 for x in c):
            bad_nn += 1
        if abs(sum(c) - 1.0) > 1e-12:
            bad_sum += 1
    check("∀ 样本：siteCoeff ≥ 0", bad_nn == 0, "%d 违规 / %d 组" % (bad_nn, len(cases)))
    check("∀ 样本：Σ_T siteCoeff = 1", bad_sum == 0, "%d 违规 / %d 组" % (bad_sum, len(cases)))

    print()
    print("=" * 78)
    print("C. variance_empFreq_gap 去掉 hmean 后为假（文件 §7）")
    print("=" * 78)
    p = 0.5
    ok = True
    for n in (1, 2, 3, 10):
        lhs = (1.0 - p) ** 2                 # ∫ (empFreq - p)^2 ，ind ≡ 1 ⇒ empFreq ≡ 1
        rhs = p * (1.0 - p) / n
        if n == 1:
            ok = ok and abs(lhs - rhs) < 1e-12
        else:
            ok = ok and abs(lhs - rhs) > 1e-9
    check("n=1 时 1/4 = p(1-p)/n 成立；n≥2 时不成立（⇒ 命题为假）", ok,
          "n=2: lhs=%.6f rhs=%.6f" % ((1 - p) ** 2, p * (1 - p) / 2))

    print()
    print("=" * 78)
    if FAIL:
        print("RESULT: FAIL（%d 项）：%s" % (len(FAIL), ", ".join(FAIL)))
        return 1
    print("RESULT: ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
