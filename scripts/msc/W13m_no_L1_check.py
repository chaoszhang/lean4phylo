#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W13m 数值对拍 —— `hL1` 能不能从块级 SLLN 里去掉（W13m 交付件，★G）。

对拍对象（Lean 侧）：

* `Phylo.Stat.BlockSLLNNoL1.div_eq_div_blocks_nohyp`  —— 「取商」恒等式**零假设**版
  `((ΣM)/k)/((ΣL)/k) = (ΣM)/(ΣL)`，在 Lean 的 `x / 0 = 0` 约定下对**每个** `k` 成立
  （含 `ΣL = 0`；`k = 0` 时两边同为 `0/0 = 0`）。第 1 节随机对拍。
* `Phylo.Stat.BlockSLLNNoL1.BlockSLLN_no_L1`         —— `hL1 : 1 ≤ L` 换成 `hL0 : ∫L₀ ≠ 0` 的主定理。
  第 2 节：`L ∈ {0, 2}` 各 1/2、`M ≡ 1`（**故意违反 `1 ≤ L`**，`∫L₀ = 1 ≠ 0`）⇒ 比值仍 → `𝔼M/𝔼L = 1`；
  并展示 `Σ_{j<k} L_j = 0` 的 `k` 只有**有限多个**（`= 前缀 0 的个数`，几何分布、可和 ⇒ Borel–Cantelli）。
* `BlockSLLN_of_L1`（补件）                            —— 旧定理由新定理导出，第 2 节同一条定理覆盖基线 `L ≡ 1`。
* **反例（Lean 侧未形式化，见 `BlockSLLNNoL1Extra.lean` §3.2）**：`M ≡ 1`、`L` iid 均匀 `{−1,+1}`
  ⇒ `∫L₀ = 0`，而 `(ΣM)/(ΣL) = k/S_k` **不收敛**于 `𝔼M/𝔼L = 1/0 = 0`。第 3 节复现
  ⇒ 这是「`hL0` 不能再去掉」的证据（★D）。

只用标准库，全部随机数**带种子**（重跑逐字节一致）。
运行：`python3 scripts/msc/W13m_no_L1_check.py`。
"""

import math
import random
import sys

SEED = 20261012


def ldiv(a, b):
    """Lean/ℝ 的除法约定：`b = 0` 时结果取 `0`。"""
    return 0.0 if b == 0 else a / b


def report(name, ok, detail):
    print("[%-4s] %-26s %s" % ("OK" if ok else "FAIL", name, detail))
    return ok


# ---------------------------------------------------------------- 1. 恒等式
def check_identity(trials=200000, seed=SEED):
    """`div_eq_div_blocks_nohyp`：**零假设**，含 `ΣL = 0` 与 `k = 0`。"""
    rnd = random.Random(seed)
    bad = 0
    n_zero_den = 0
    n_zero_den_gt0 = 0
    for _ in range(trials):
        k = rnd.randrange(0, 6)
        M = [rnd.uniform(-3.0, 3.0) for _ in range(k)]
        if rnd.random() < 0.5:                      # 一半样本强制 ΣL = 0
            if k == 0:
                L = []
            else:
                L = [rnd.uniform(-3.0, 3.0) for _ in range(k - 1)]
                L.append(-sum(L))
        else:
            L = [rnd.uniform(-3.0, 3.0) for _ in range(k)]
        A, B = sum(M), sum(L)
        lhs = ldiv(ldiv(A, float(k)), ldiv(B, float(k)))
        rhs = ldiv(A, B)
        if B == 0:
            n_zero_den += 1
            if k > 0:
                n_zero_den_gt0 += 1
            if not (lhs == 0.0 and rhs == 0.0):     # 退化分支必须**恰好**两边为 0
                bad += 1
        elif abs(lhs - rhs) > 1e-9 * max(1.0, abs(rhs)):
            bad += 1
    return report("identity_nohyp", bad == 0,
                  "trials=%d  ΣL=0 样本=%d（其中 k>0 的 %d） 不符=%d"
                  % (trials, n_zero_den, n_zero_den_gt0, bad))


# ---------------------------------------- 2. hL1 去掉后仍收敛（协调侧指定配置）
def run_path(sample, k, rnd):
    """按块累加，返回 `(ΣM, ΣL, (ΣM)/(ΣL))`（`ΣL = 0` ⇒ 0，Lean 约定）。"""
    M = 0.0
    L = 0.0
    for _ in range(k):
        m, l = sample(rnd)
        M += m
        L += l
    return M, L, ldiv(M, L)


def case_drop_hL1_coord(rnd, ks=(100, 1000, 10000, 50000), paths=300):
    """协调侧指定：`L ∈ {0,2}` 各 1/2、`M ≡ 1`（`hL1` 被违反，`∫L₀ = 1 ≠ 0`）⇒ 极限 1。"""
    def sample(r):
        return 1.0, (2.0 if r.random() < 0.5 else 0.0)
    print("  case_drop_hL1_coord: L∈{0,2} 各 1/2, M≡1 ⇒ ∫L0=1, ∫M0=1, 极限=1.0（hL1 被违反）")
    ok = True
    prev = float("inf")
    for k in ks:
        errs = []
        zeros = 0
        for _ in range(paths):
            M, L, r = run_path(sample, k, rnd)
            if L == 0.0:
                zeros += 1
            errs.append(abs(r - 1.0))
        m = sum(errs) / len(errs)
        # SLLN 收敛速率：误差应 ∼ c/√k ⇒ 以 0.9/√k 为判据，并要求单调下降
        tol = 0.9 / math.sqrt(k)
        print("    k=%-6d 平均|比值-1| = %.6f  (×√k = %.3f, 容忍 0.9/√k = %.6f)   ΣL=0 的路径 = %d/%d"
              % (k, m, m * math.sqrt(k), tol, zeros, paths))
        ok = ok and m < prev and m < tol and (k < 1000 or zeros == 0)
        prev = m
    return report("drop_hL1_coord", ok, "⇒ `1 ≤ L` 不成立时比值仍 → 1.0（误差 ∼ c/√k）✓")


def case_drop_hL1_lsq(rnd, ks=(100, 1000, 10000, 50000), paths=300):
    """另一实例：`L ∈ {0,2}`、`M = L²` ⇒ `∫M₀ = 2`、极限 `2/1 = 2`。"""
    def sample(r):
        l = 2.0 if r.random() < 0.5 else 0.0
        return l * l, l
    errs = {}
    ok = True
    for k in ks:
        e = [abs(run_path(sample, k, rnd)[2] - 2.0) for _ in range(paths)]
        errs[k] = sum(e) / len(e)
        ok = ok and errs[k] < 0.05
    return report("drop_hL1_lsq", ok,
                  "L∈{0,2}, M=L² ⇒ 极限 2.0；平均误差 " +
                  ", ".join("k=%d:%.6f" % (k, errs[k]) for k in ks))


def case_baseline_hL1(rnd, k=20000, paths=300):
    """原版基线：`L ≡ 1`（`hL1` 成立）、`M ∈ {0,2}` ⇒ 极限 1 ⇒ 同一条新定理覆盖原版。"""
    def sample(r):
        return (2.0 if r.random() < 0.5 else 0.0), 1.0
    e = [abs(run_path(sample, k, rnd)[2] - 1.0) for _ in range(paths)]
    m = sum(e) / len(e)
    return report("baseline_hL1", m < 0.05, "L≡1, ∫M0=1 ⇒ k=%d 平均|比值-1| = %.6f" % (k, m))


def case_zero_prefix_finite(rnd, K=200000, paths=200, p=0.5):
    """★ `Σ_{j<k} L_j = 0` 的 `k` **只有有限多个**：`L ≥ 0` ⇒ 等价于「前 k 项全零」，
    其集合恰为 `{0,1,…,m}`（`m` = 前缀 0 的个数）⇒ `P(m ≥ j) = p^j` ⇒ `E[m] = p/(1-p)` 有限、
    `P(m ≥ K) = p^K → 0`（Borel–Cantelli 可用的**前提**）。"""
    last = []
    for _ in range(paths):
        m = 0
        for _ in range(K):
            if rnd.random() < p:
                m += 1
            else:
                break
        last.append(m)
    mx = max(last)
    mean = sum(last) / len(last)
    print("  case_zero_prefix: L∈{0,2} 各 1/2（p=P(L=0)=%.1f）⇒ P(Σ_{j<k} L_j = 0) = p^k" % p)
    print("    「最后一个 ΣL=0 的 k」= 前缀 0 的个数 m：max=%d, 经验均值=%.3f, 理论 E[m]=p/(1-p)=%.3f"
          % (mx, mean, p / (1 - p)))
    print("    P(m ≥ %d) = p^%d = %.3e（双精度下溢为 0）；Σ_{k≥1} p^k = p/(1-p) = %.6f < ∞"
          % (K, K, p ** K, p / (1 - p)))
    ok = mx < K and abs(mean - p / (1 - p)) < 0.5
    return report("zero_prefix_finite", ok, "⇒ 退化点只有有限多个（但零假设恒等式已使其无关紧要）")


# ------------------------------- 3. 反例：∫L₀ = 0 ⇒ 结论为假（hL0 必需）
def case_symmetric(rnd, ks=(100, 1000, 10000, 100000), paths=150):
    """`M ≡ 1`、`L` iid 均匀 `{−1,+1}` ⇒ `∫L₀ = 0`；`(ΣM)/(ΣL) = k/S_k`。

    逐路径统计**运行最大** `max_{k≤K}|k/S_k|` 与**回归 0 的次数** `#{k ≤ K : S_k = 0}`：
    前者随 `K` 无界增长、后者随 `K` 增长（1 维简单随机游走常返）⇒ 序列不收敛 ✓。"""
    print("  case_symmetric: M≡1, L iid 均匀{−1,+1} ⇒ ∫M0=1, ∫L0=0 ⇒ 目标值 1/0 = 0.0")
    ok = True
    for k in ks:
        vals = []
        runmax = []
        zeros = 0
        for _ in range(paths):
            S = 0
            mx = 0
            z = 0
            for i in range(1, k + 1):
                S += 1 if rnd.random() < 0.5 else -1
                if S == 0:
                    z += 1
                    v = 0.0
                else:
                    v = abs(float(i) / S)
                if v > mx:
                    mx = v
            vals.append(ldiv(float(k), float(S)))
            runmax.append(mx)
            zeros += z
        print("    k=%-6d max|k/S_k| = %-9.2f 平均运行最大 = %-10.2f 平均回归 0 次数 = %-8.2f  S_k=0 的路径 = %d/%d"
              % (k, max(abs(v) for v in vals), sum(runmax) / len(runmax),
                 float(zeros) / paths, sum(1 for v in vals if v == 0.0), paths))
        ok = ok and sum(runmax) / len(runmax) > 3.0
    return report("symmetric_counterex", ok,
                  "⇒ 运行最大无界增长（√k 量级）＋ 回归 0 次数增长 ⇒ 不收敛于 0.0（★hL0 必需）")


def case_all_zero_L(rnd, k=20000, paths=50):
    """退化：`L ≡ 0`（`∫L₀ = 0`）⇒ Lean 下比值恒为 `0`、目标 `𝔼M/0 = 0` ⇒ **仍成立**。"""
    vals = []
    for _ in range(paths):
        vals.append(ldiv(float(k), 0.0))
    return report("all_zero_L", all(v == 0.0 for v in vals),
                  "L≡0 ⇒ k=%d 全体路径比值 = 0.0 = 𝔼M/0（退化情形不构成反例）" % k)


# ------------------------------------- 4. Borel–Cantelli 路线（正确但多余）
def check_borel_cantelli():
    """`P(前 k 项全零) = p^k` 可和 —— 协调侧路线的**前提**；本件证明用不到它。"""
    print("  P(Σ_{j<k} L_j = 0) = p^k（L 非负 iid、P(L=0)=p）⇒ Σ_k p^k = p/(1-p) < ∞")
    ok = True
    for p in (0.1, 0.3, 0.5, 0.7, 0.9):
        s = sum(p ** k for k in range(1, 3000))
        print("    p=%.1f  Σ_{k≥1} p^k = %.6f  (= p/(1-p) = %.6f)" % (p, s, p / (1 - p)))
        ok = ok and abs(s - p / (1 - p)) < 1e-6
    return report("borel_cantelli", ok,
                  "⇒ 该路线前提为真；但 `div_eq_div_blocks_nohyp` 已使它对**每个** k 成立 ⇒ 多余")


def main():
    print("W13m 数值对拍（seed=%d, python %s）" % (SEED, sys.version.split()[0]))
    print("[1] 恒等式 `div_eq_div_blocks_nohyp`（零假设；含 ΣL=0 与 k=0）")
    results = [check_identity()]
    print("[2] 主定理 `BlockSLLN_no_L1`（hL1 → hL0）")
    rnd = random.Random(SEED + 1)
    results.append(case_drop_hL1_coord(rnd))
    results.append(case_drop_hL1_lsq(rnd))
    results.append(case_baseline_hL1(rnd))
    print("[2b] `ΣL = 0` 的退化 k 只有有限多个（Borel–Cantelli 路线的前提）")
    results.append(case_zero_prefix_finite(rnd))
    print("[3] 反例：`∫L₀ = 0` 时结论为假（⇒ `hL0` 不可去）")
    rnd = random.Random(SEED + 2)
    results.append(case_symmetric(rnd))
    results.append(case_all_zero_L(rnd))
    print("[4] 协调侧 Borel–Cantelli 路线的前提（正确，但被零假设恒等式取代）")
    results.append(check_borel_cantelli())
    print("汇总：%d/%d 通过" % (sum(1 for r in results if r), len(results)))
    return 0 if all(results) else 1


if __name__ == "__main__":
    sys.exit(main())
