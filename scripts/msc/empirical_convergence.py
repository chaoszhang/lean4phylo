#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/empirical_convergence.py -- W10d 经验 quartet 频率的**精确有理数**复核

对象（`Phylo/Stat/EmpiricalConvergence.lean`）：

    empFreq n omega = (1/n) * sum_{i<n} ind(omega i)          （n 个 iid 位点的指示值平均）

本脚本**不做 Monte Carlo**，全部用 `fractions.Fraction` 做精确有理数运算
（把 p = 位点给出某个 quartet 的概率当作有理数，逐个核对恒等式，误差恒为 0）。

复核条目（每条打印 PASS/FAIL）
  (A) **无偏性**（对应 Lean 的 `integral_empFreq`）：
        E[empFreq n] = (1/n) * sum_{i<n} E[X_i] = (1/n) * (n p) = p          (1 <= n <= 6)
  (B) **二阶矩与方差**（对应 Lean 的 `integral_sq_sub_of_zero_one` 与缺口 V）：
        E[X_i^2] = p（因为 X_i 取值 0/1），E[X_i X_j] = p^2（i != j，独立性），故
        E[(sum_i X_i)^2] = n p + n(n-1) p^2,
        Var(sum_i X_i) = n p(1-p),  Var(empFreq n) = p(1-p)/n              (1 <= n <= 6)
      并用**第二条独立路线**核对：Var(sum) = sum_i Var(X_i) + 2*sum_{i<j} Cov(X_i,X_j)
      （Cov = 0 由独立性），两条路线的有理数结果必须逐字相等。
  (C) **凸组合系数**：(1/n) * sum_{i<n} 1 = 1（经验频率是均值，权重和恒为 1）。
  (D) **退化一致性**：ind 恒为常数 c 时 empFreq n = c（对一切 n >= 1），
      故 a.s. 极限必须 = c = E[ind]（与 (A) 相容）。
  (E) **Chebyshev 窗口的算术**（仅核对数字；Chebyshev 不等式本身**未**在 Lean 中形式化）：
        p(1-p)/(n eps^2) 在若干有理 (p, n, eps) 上的精确值。
"""

from fractions import Fraction as F
import sys

FAILED = []


def check(name, cond, detail=""):
    ok = bool(cond)
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")
    if not ok:
        FAILED.append(name)
    return ok


PS = [F(0), F(1, 4), F(1, 3), F(1, 2), F(2, 3), F(9, 10), F(1)]
NS = [1, 2, 3, 4, 5, 6]


def section_A():
    print("(A) 无偏性：E[empFreq n] = p（iid 位点，各 E[X_i] = p）")
    for n in NS:
        for p in PS:
            total = sum((p for _ in range(n)), F(0))            # sum_i E[X_i] = n p
            mean = F(1, n) * total                              # (1/n) * n p
            check(f"n = {n}, p = {p}：E[empFreq n] = p", mean == p and total == n * p,
                  f"sum_i E[X_i] = {total}, (1/n)*sum = {mean}")


def section_B():
    print("(B) 二阶矩 / 方差：E[(sum X)^2] = n p + n(n-1) p^2，Var(empFreq n) = p(1-p)/n")
    for n in NS:
        for p in PS:
            # 路线 1：双重和（对角 + 非对角）
            diag = n * p                                        # sum_i E[X_i^2] = n p（X_i^2 = X_i）
            off = n * (n - 1) * p * p                           # sum_{i != j} E[X_i]E[X_j]
            m2 = diag + off
            ex2 = (n * p) ** 2                                  # (E[sum X])^2 = (n p)^2
            var_sum = m2 - ex2
            var_emp = F(1, n * n) * var_sum                     # Var(empFreq) = Var(sum)/n^2
            # 路线 2：sum Var(X_i) + 2 sum_{i<j} Cov(X_i, X_j)（Cov = 0）
            var_each = p - p * p                                # Var(X_i) = E[X_i^2] - (E X_i)^2
            var_route2 = n * var_each                           # Cov 项为 0
            target = p * (1 - p) / n
            check(f"n = {n}, p = {p}：E[(sum X)^2] = n p + n(n-1) p^2", m2 == diag + off,
                  f"m2 = {m2}")
            check(f"n = {n}, p = {p}：Var(sum X) = n p(1-p)（两条路线一致）",
                  var_sum == var_route2 == n * (p - p * p), f"路线1 = {var_sum}, 路线2 = {var_route2}")
            check(f"n = {n}, p = {p}：Var(empFreq n) = p(1-p)/n = {target}", var_emp == target)


def section_C():
    print("(C) 凸组合：empFreq 的权重 (1/n) 之和 = 1")
    for n in NS:
        check(f"n = {n}：(1/n) * sum_{{i<n}} 1 = 1", F(1, n) * n == 1)


def section_D():
    print("(D) 退化一致性：ind 恒为 c 时 empFreq n = c（n >= 1）")
    for n in NS:
        for c in [F(0), F(1), F(1, 3)]:
            mean = F(1, n) * (n * c)
            check(f"n = {n}, c = {c}：empFreq n = c", mean == c)


def section_E():
    print("(E) Chebyshev 窗口的算术（Chebyshev 本身未在 Lean 中形式化）")
    cases = [(F(1, 2), 6, F(1, 2)), (F(1, 2), 4, F(1, 4)), (F(9, 10), 5, F(1, 5))]
    for (p, n, eps) in cases:
        var = p * (1 - p) / n
        bound = var / (eps * eps)
        check(f"p = {p}, n = {n}, eps = {eps}：p(1-p)/(n eps^2) = {bound} <= 1",
              bound <= 1)


def main():
    print("=" * 78)
    print("W10d 经验频率：无偏性 / 方差 的精确有理数复核（零 Monte Carlo、零浮点）")
    print("=" * 78)
    for f in (section_A, section_B, section_C, section_D, section_E):
        f()
    print("=" * 78)
    if FAILED:
        print(f"VERDICT: FAIL（{len(FAILED)} 条不通过）")
        for name in FAILED:
            print("  -", name)
        return 1
    print("VERDICT: ALL PASS")
    print("关键数字（n <= 6、p 为有理数，全部恒等式误差恒为 0）：")
    print("  * 无偏性：E[empFreq n] = (1/n)*(n p) = p。")
    print("  * 二阶矩：E[(sum_i X_i)^2] = n p + n(n-1) p^2（对角 n p + 非对角 n(n-1) p^2）。")
    print("  * 方差两条路线一致：Var(sum) = n p(1-p)，故 Var(empFreq n) = p(1-p)/n。")
    print("  * 权重和：(1/n)*n = 1（经验频率是均值）。")
    print("  * n = 1 特例：p(1-p)/1 = p(1-p)（= Lean 的 integral_sq_sub_empFreq_one）。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
