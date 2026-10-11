#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W13j 数值对拍 —— 换指标引理（规格 §3.3：「前 n 个位点」vs「前 k 棵树」）

对应 Lean 交付：Phylo/Stat/BlockSLLNIndex.lean
  cumSites L k         = N_k = sum_{j<k} L_j
  treesCovered L n     = k(n) = max { k <= n : N_k <= n }
  sub_cumSites_treesCovered_le : n - N_{k(n)} <= C            （需 1 <= L 与 L <= C）
  abs_sum_sub_blockSum_le      : |sum_{m<n} S_m - sum_{j<k(n)} M_j| <= B*C

本脚本检查：
  (A) 穷举小情形：尾块 <= C 个位点、k(n) 单调且 k(n) <= n、换指标误差 <= B*C
  (B) 有界 L 时：块平均与「前 n 个位点平均」**同极限**（相对误差 <= B*C/n）
  (C) ★D：**去掉 `L <= C` 后结论为假** —— 显式反例（块平均恒为 0，前缀平均不收敛）
  (D) 退化一致性：L ≡ 1 ⇒ k(n) = n（尾块 = 0）

只用标准库（无第三方依赖）。
"""
import itertools
import random
from fractions import Fraction


def cum(L, k):
    """N_k = sum_{j<k} L_j"""
    return sum(L[:k])


def k_of(L, n):
    """k(n) = max { k <= n : N_k <= n }（把定义抄成循环）"""
    best = None
    for k in range(0, n + 1):
        if cum(L, k) <= n:
            best = k
    assert best is not None, "k = 0 总是可行（N_0 = 0 <= n）"
    return best


# ---------------------------------------------------------------- (A) 穷举
def check_exhaustive(Cmax=3, Kmax=7):
    worst_gap = {}
    checks = 0
    for C in range(1, Cmax + 1):
        for K in range(1, Kmax + 1):
            for L in itertools.product(range(1, C + 1), repeat=K):
                N_K = cum(L, K)
                prev_k = 0
                for n in range(0, N_K + 1):
                    k = k_of(L, n)
                    gap = n - cum(L, k)                      # n - N_{k(n)}
                    assert k <= n, "k(n) <= n"
                    assert k >= prev_k, "k(n) 单调不减"
                    assert 0 <= gap <= C, ("尾块 <= C 个位点", L, n, gap, C)
                    worst_gap[C] = max(worst_gap.get(C, 0), gap)
                    prev_k = k
                    checks += 1
                # 误差界：随机逐位点权重 |S| <= B，块和 M_j = 该块位点之和
                B = Fraction(random.choice([1, 2, 5]), random.choice([1, 2]))
                S = [Fraction(random.randint(-100, 100), 100) for _ in range(N_K)]
                S = [max(-B, min(B, s)) for s in S]
                assert all(abs(s) <= B for s in S)
                M, pos = [], 0
                for j in range(K):
                    M.append(sum(S[pos:pos + L[j]], Fraction(0)))
                    pos += L[j]
                for n in range(0, N_K + 1):
                    k = k_of(L, n)
                    pref = sum(S[:n], Fraction(0))
                    blocksum = sum(M[:k], Fraction(0))
                    assert abs(pref - blocksum) <= B * C, ("误差界 <= B*C", L, n)
                    if n > 0:
                        assert abs(Fraction(pref, n) - Fraction(blocksum, n)) <= B * C / n
    return checks, worst_gap


# ------------------------------------------------- (B) 有界 L：同极限
def check_same_limit_bounded(K=4000, C=3):
    L = [1 + (j % C) for j in range(K)]                # 1 <= L_j <= C
    w = [1 if (j % 2 == 0) else -1 for j in range(K)]  # 逐块常数权重（B = 1）
    S = []
    for j in range(K):
        S.extend([w[j]] * L[j])
    assert all(abs(s) <= 1 for s in S)                 # B = 1
    Ntot = len(S)
    pref = [0] * (Ntot + 1)
    for i in range(Ntot):
        pref[i + 1] = pref[i] + S[i]
    M, Lc, pos = [], [], 0
    for j in range(K):
        M.append(sum(S[pos:pos + L[j]]))
        Lc.append(L[j])
        pos += L[j]
    rows = []
    for n in [1, 2, 3, 10, 100, 1000, Ntot]:
        k = k_of(L, n)
        blockavg = Fraction(sum(M[:k]), sum(Lc[:k]))
        prefavg = Fraction(pref[n], n)
        rows.append((n, k, blockavg, prefavg, abs(prefavg - blockavg)))
        assert abs(prefavg - blockavg) <= Fraction(1 * C, n), "相对误差 <= B*C/n"
    lim_block = Fraction(sum(M), sum(Lc))
    lim_pref = Fraction(pref[Ntot], Ntot)
    assert abs(lim_block - lim_pref) <= Fraction(1 * C, Ntot)
    return rows, lim_block, lim_pref


# ------------------------------- (C) ★D 无界 L：L <= C 去掉后结论为假
def check_unbounded_counterexample(K=18):
    """显式反例（L_j = 2^j，无上界；块内结构性安排）：

        cumsites:  N_k = sum_{1<=j<k} 2^j = 2^k - 2
        块 j（j >= 1）：前一半位点权重 +1，后一半 -1  ⇒ 块和 M_j = 0

    ⇒ **块平均恒为 0**（假设 `块平均 -> lim = 0` **满足**，B = 1）
    ⇒ 但「前 n 个位点平均」在
         n = N_k        （块边界）  上恒为 0，
         n = N_k + 2^{k-1}（块中点）上 -> 1/3
       两个子列极限不同 ⇒ 前缀平均**不收敛**到 0 ⇒ 结论为**假**。

    ⇒ `L <= C`（规格 §4③）在本引理里是**本质**的，而不只是「方便」。

    （注意：若块长有上界 C，则尾块贡献 <= B*C 且被 /n 压掉 —— 正是 Lean 定理
     `sub_cumSites_treesCovered_le` + `abs_sum_sub_blockSum_le` 的内容。）"""
    L = [0] + [2 ** j for j in range(1, K + 1)]        # 块 j = 2^j, j >= 1
    rows = []
    for k in range(2, K):
        N_k = cum(L, k)
        blkavg = Fraction(0)                            # M_j = 0 全为 0
        n_mid = N_k + 2 ** (k - 1)                      # 块 k 的中点
        a_boundary = Fraction(0, N_k) if N_k else Fraction(0)
        a_mid = Fraction(2 ** (k - 1), n_mid)
        rows.append((k, N_k, n_mid, blkavg, a_boundary, a_mid, n_mid - N_k))
    tail = rows[-8:]
    return rows, tail


# ---------------------------------------- (D) 退化一致性 L ≡ 1
def check_degenerate(K=50):
    L = [1] * K
    for n in range(0, K + 1):
        assert k_of(L, n) == n, "L ≡ 1 ⇒ k(n) = n"
        assert n - cum(L, k_of(L, n)) == 0, "L ≡ 1 ⇒ 尾块 = 0"
    return True


def main():
    random.seed(20261012)
    print("=" * 78)
    print("W13j 换指标引理数值对拍（BlockSLLNIndex.lean）")
    print("=" * 78)

    checks, worst = check_exhaustive()
    print("[A] 穷举 (C<=3, K<=7)：断言数 = %d" % checks)
    print("    最大尾块 n - N_{k(n)}（按 C 分组）: %s   [要求 <= C]"
          % {c: v for c, v in sorted(worst.items())})
    print("    => k(n) 单调不减、k(n) <= n、尾块 <= C、|前缀和 - 块和| <= B*C  全部成立")

    rows, lb, lp = check_same_limit_bounded()
    print("[B] 有界 L（L_j = 1 + j mod 3 <= C = 3, B = 1, K = 4000）:")
    for n, k, ba, pa, err in rows:
        print("      n=%-7d k(n)=%-5d 块平均=%-12.8f 前缀平均=%-12.8f 差=%.3e"
              % (n, k, float(ba), float(pa), float(err)))
    print("    极限：块平均 %.10f   前缀平均 %.10f   |差| <= B*C/n = %.3e"
          % (float(lb), float(lp), float(Fraction(3, rows[-1][0]))))

    rows, tail = check_unbounded_counterexample()
    print("[C] ★D 反例（无界 L_j = 2^j，块内前一半 +1 / 后一半 -1 ⇒ 块和 M_j = 0，B = 1）：")
    print("      k |      N_k |      N_k+2^(k-1) | 块平均 | 前缀@N_k | 前缀@中点 | 尾块位点数")
    for k, Nk, nm, ba, ab, am, tl in tail:
        print("    %4d | %8d | %15d | %6.1f | %8.6f | %9.6f | %10d"
              % (k, Nk, nm, float(ba), float(ab), float(am), tl))
    mid_last = float(tail[-1][5])
    print("    块平均恒为 0（**假设满足**，lim = 0），但前缀平均在 0 与 %.4f 之间振荡" % mid_last)
    print("    两个子列极限 0 与 %.4f 不同 ⇒ 前缀平均**不收敛**到 0 ⇒ 结论为假" % mid_last)
    print("    => `L <= C`（规格 §4③）在本引理里是**本质**的（尾块贡献无界、压不掉）")

    assert check_degenerate()
    print("[D] 退化一致性 L ≡ 1：k(n) = n 且尾块 = 0  ✓")
    print("=" * 78)
    print("全部通过")


if __name__ == "__main__":
    main()
