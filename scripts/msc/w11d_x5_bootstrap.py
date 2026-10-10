#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W11d / X5 —— bootstrap 支持度（Felsenstein 1985）的**穷举**数值核对。

文献：J. Felsenstein, "Confidence limits on phylogenies: an approach using the bootstrap",
      Evolution 39(4) (1985) 783-791.
      references/md/Felsenstein1985_ConfidenceLimitsPhylogeniesBootstrap.md
      （md5 e8b363f79343ca89650f9faf82c538c3）

对照的 Lean 模块：`Phylo/Stat/Bootstrap.lean`
（md5 6b01eeae0642e377976be2166c32285c，593 行）

★ 纪律：**不使用随机数**。全部「重抽样」都按 **枚举** `Resample n = Fin n → Fin n`
（共 `n^n` 个等可能结果）完成，概率/期望用 `fractions.Fraction` **精确有理数**算。

对应关系（脚本函数 ↔ Lean 声明）：

    weight_of          ↔ Phylo.Stat.Bootstrap.weightOf
    sum_weightOf       ↔ Phylo.Stat.Bootstrap.sum_weightOf
    sum_weightOf_over  ↔ Phylo.Stat.Bootstrap.sum_weightOf_over_resamples
    expected_linear    ↔ Phylo.Stat.Bootstrap.expected_linear_statistic_eq_original
    sel_majority       ↔ Phylo.Stat.Bootstrap.selMajority
    minimal_example    ↔ Phylo.Stat.Bootstrap.minimal_example_count
    multinomial gap    ↔ Phylo.Stat.Bootstrap.multinomial_weight_count_gap
    incompatibility    ↔ Phylo.Stat.Bootstrap.not_compatible_fourAB_*
"""
from __future__ import annotations

import itertools
import math
import sys
from fractions import Fraction

# ---------------------------------------------------------------- 载体

def resamples(n: int):
    """枚举 `Resample n = Fin n → Fin n`（`n^n` 个；Felsenstein L298-307 的有放回抽样）。"""
    return itertools.product(range(n), repeat=n)


def weight_of(sigma, n: int):
    """`weightOf σ i` = 字符 `i` 被抽中的次数（L1276-1283 的 weights 向量）。"""
    return tuple(sum(1 for s in sigma if s == i) for i in range(n))


# ---------------------------------------------------------------- §1 权重和 = n

def check_sum_weights(nmax: int = 6) -> int:
    """`∑ᵢ weightOf σ i = n` 对**每一个** σ 成立  ↔ Lean `sum_weightOf`。"""
    checked = 0
    for n in range(0, nmax + 1):
        for sigma in resamples(n):
            w = weight_of(sigma, n)
            assert sum(w) == n, (n, sigma, w)
            checked += 1
    print(f"[OK] sum_weightOf          : 枚举 {checked} 个重抽样，恒有 Σᵢ wᵢ = n")
    return checked


# ---------------------------------------------------------------- §4 期望

def check_expectation(nmax: int = 6) -> None:
    """`∑_σ weightOf σ i = n^n`，即 `E[wᵢ] = 1`  ↔ Lean `sum_weightOf_over_resamples`。

    并核对**线性**统计量的均值恒等式 ↔ Lean `expected_linear_statistic_eq_original`。"""
    for n in range(1, nmax + 1):
        total = [0] * n
        for sigma in resamples(n):
            w = weight_of(sigma, n)
            for i in range(n):
                total[i] += w[i]
        assert all(t == n ** n for t in total), (n, total, n ** n)
        # E[w_i] = n^n / n^n = 1  —— 恰为原数据经验频率 1/n 的 n 倍
        for i in range(n):
            assert Fraction(total[i], n ** n) == 1, (n, i)

        # 线性统计量：随机取系数 c（用确定性的伪系数，避免随机数）
        c = [Fraction((i + 1) * 7 % 11 - 5, (i % 3) + 1) for i in range(n)]
        lhs = Fraction(0)
        for sigma in resamples(n):
            w = weight_of(sigma, n)
            lhs += sum(Fraction(w[i]) * c[i] for i in range(n))
        lhs /= n ** n
        assert lhs == sum(c), (n, lhs, sum(c))
    print(f"[OK] expected_linear       : n=1..{nmax}，E[wᵢ] = 1 且 E[Σᵢ wᵢ·cᵢ] = Σᵢ cᵢ（精确有理数）")


def check_nonlinear_fails(n: int = 3) -> None:
    """★B 反例 2：**非线性**统计量下均值恒等式**失效**。

    这里统计量 = `1{规则输出 fourAB}`（Lean 的 `selMajority`）。"""
    cnt = {k: 0 for k in ("AB", "AC", "AD")}
    for sigma in resamples(n):
        cnt[sel_majority(n, weight_of(sigma, n))] += 1
    total = n ** n
    exp_indicator = Fraction(cnt["AB"], total)
    # 原数据（恒等重抽样，权重全 1）报告的是 AB，故「原数据的频率」= 1
    assert exp_indicator != 1, "expected the nonlinear identity to FAIL"
    print(f"[OK] nonlinear fails      : E[1{{rule=AB}}] = {exp_indicator} = {float(exp_indicator):.6f}"
          f"  ≠ 1 = 1{{rule(原数据)=AB}}   ← 反例 2 成立")
    return cnt


# ---------------------------------------------------------------- §5 最小例子

SPLITS = (frozenset({0, 1}), frozenset({0, 2}), frozenset({0, 3}))


def sel_majority(n: int, w):
    """Lean `selMajority n w`：严格多数 `2·wᵢ > n` 的字符所支持的 split；否则下标最小者。

    字符 0/1/2 分别支持 `{0,1}|{2,3}`、`{0,2}|{1,3}`、`{0,3}|{1,2}`。"""
    for idx, name in enumerate(("AB", "AC", "AD")):
        if 2 * w[idx] > n:
            return name
    return "AB"


def check_minimal_example() -> None:
    """4 taxa、3 字符、27 次重抽样  ↔ Lean `minimal_example_count` / `minimal_example_support`。"""
    n = 3
    total = n ** n
    cnt = {k: 0 for k in ("AB", "AC", "AD")}
    histogram = {}
    for sigma in resamples(n):
        w = weight_of(sigma, n)
        histogram[w] = histogram.get(w, 0) + 1
        cnt[sel_majority(n, w)] += 1

    print(f"[..] minimal example      : n = {n}, 重抽样数 = {n}^{n} = {total}")
    print(f"     权重向量直方图（{len(histogram)} 个不同向量，多项式型计数）:")
    for w in sorted(histogram):
        mult = math.factorial(n)
        for x in w:
            mult //= math.factorial(x)
        assert histogram[w] == mult, (w, histogram[w], mult)
        print(f"       w = {w}  ->  count = {histogram[w]:2d}"
              f"   (multinomial {n}!/({'*'.join(str(math.factorial(x)) for x in w)}) = {mult})")
    print(f"     各 split 被报告的次数: AB={cnt['AB']}, AC={cnt['AC']}, AD={cnt['AD']}"
          f"（和 = {sum(cnt.values())}）")

    assert cnt["AB"] == 13, cnt
    assert sum(cnt.values()) == total
    supp = Fraction(cnt["AB"], total)
    assert supp == Fraction(13, 27), supp
    assert supp < Fraction(1, 2), supp
    print(f"[OK] minimal_example_count: 计数 |{{sigma : rule(sigma) = fourAB}}| = 13  (= {total} 中的 13)")
    print(f"[OK] minimal_example_supp : bootstrapSupport(fourAB) = {supp} = {float(supp):.6f} < 1/2")
    print(f"[OK] original split       : 原数据权重 (1,1,1) → 规则报告 AB，"
          f"但其支持度 {supp} < 1/2  ⇒ **它不在多数共识树里**（★B 反例 1）")
    print(f"     诚实性说明：{supp} = {float(supp):.6f}，故 13·2 = 26 < 27 = 2·#{total}。")


# ---------------------------------------------------------------- §6 缺口 M（数值确认）

def check_multinomial_gap(nmax: int = 5) -> None:
    """缺口 M 的命题**在数值上为真**（故它是一个诚实的「未证但正确」的缺口）：

        #{σ | weightOf σ = w} · ∏ᵢ (wᵢ)!  =  n!
    """
    for n in range(0, nmax + 1):
        counts = {}
        for sigma in resamples(n):
            w = weight_of(sigma, n)
            counts[w] = counts.get(w, 0) + 1
        for w in itertools.product(range(n + 1), repeat=n):
            if sum(w) != n:
                continue
            got = counts.get(w, 0)
            prod = 1
            for x in w:
                prod *= math.factorial(x)
            assert got * prod == math.factorial(n), (n, w, got, prod)
    print(f"[OK] multinomial gap (M)   : n=0..{nmax}，计数(w) · ∏ᵢ wᵢ! = n! 恒成立"
          f"（缺口 M 的命题正确但 Lean 侧未证）")

    # 论文 L1288-1292 的 20-字符权重串，每条都是合法的（和 = 20）
    paper_weights = ["21100212120121012010",
                     "01001510031020011211",
                     "01031211201012100121",
                     "12130421030000100101",
                     "20010100211211121211"]
    for s in paper_weights:
        w = tuple(int(ch) for ch in s)
        assert len(w) == 20 and sum(w) == 20, s
    print(f"[OK] paper L1288-1292      : {len(paper_weights)} 条 20-字符权重串全部满足 Σᵢ wᵢ = 20"
          f"（Felsenstein 的 50 次重抽样中给出的 5 条）")


# ---------------------------------------------------------------- §7 4 元 3-split 障碍

def check_incompatibility() -> None:
    """`{0,1}|{2,3}`、`{0,2}|{1,3}`、`{0,3}|{1,2}` 两两**不相容**
    ↔ Lean `not_compatible_fourAB_fourAC` 等。"""
    A = (frozenset({0, 1}), frozenset({2, 3}))
    B = (frozenset({0, 2}), frozenset({1, 3}))
    C = (frozenset({0, 3}), frozenset({1, 2}))

    def compatible(s, t):
        # Split.Compatible：四个交至少一个为空
        return any(not (a & b) for a in s for b in t)

    rep = {}
    for nm, (s, t) in {"AB-AC": (A, B), "AB-AD": (A, C), "AC-AD": (B, C)}.items():
        assert not compatible(s, t), nm
        assert compatible(s, s) and compatible(t, t)
        rep[nm] = "不相容 ✓"
    print(f"[OK] 4-taxon 3-split 障碍  : {rep}")
    print("     推论：一棵树的 split 系统两两相容 ⟹ 它至多含三者之一 ⟹ §5 的 `occ` 层与树层一致")


# ---------------------------------------------------------------- main

def main() -> int:
    print("=" * 78)
    print("W11d / X5  bootstrap 支持度（Felsenstein 1985）—— 穷举核对（无随机数，精确有理数）")
    print("=" * 78)
    check_sum_weights()
    check_expectation()
    check_nonlinear_fails()
    check_minimal_example()
    check_multinomial_gap()
    check_incompatibility()
    print("=" * 78)
    print("全部断言通过：与 Phylo/Stat/Bootstrap.lean 的结论一致。")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
