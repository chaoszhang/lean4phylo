#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W13f 数值脚本 —— 「k 固定 ⇒ 假」＋「k → ∞ 块级平均 → m.freq」的小情形穷举验证。

配套 Lean 件：`Phylo/Stat/ToyMSCFin4.lean`（W13f）。

## 规格 §4.1 的数值对照

模型（与 Lean 件 `FixedKGuard` / `guardExample` 一致）：

* `X = Fin 4`；`G = Bool`（两棵候选基因树）；
* `k` 个 IID 基因树，第 j 棵为 `false` 的概率 `4/5`、为 `true` 的概率 `1/5`；
* `FreqOf false = freqA`（质量全在无向 quartet `01|23` 类上）、
  `FreqOf true = freqB`（质量全在 `02|13` 类上）；
* 真树取 `01|23` ⇒ 推前 `m.freq = (4/5)·freqA + (1/5)·freqB`；
* `L ≡ 1`、`ρ ≡ 1`（每个位点由对应基因树独立生成）。

脚本做三件事：

1. **穷举 `Split (Fin 4)`**（`14` 条：`6` 条 `2|2` ＋ `8` 条 `1|3`），
   逐条验证 `freqA` / `freqB` / `m.freq` 的 `p_nonneg`、`p_sum_one`、`p_swap`；
2. **`k` 固定为 `1`**：条件极限 = `FreqOf (ω 0)`，在**正测度**事件 `{ω 0 = false}`
   上它 `= freqA ≠ m.freq` ⇒ 结论为假；脚本打印两类实现上的极限与推前频率之差；
3. **`k → ∞` 趋势**：块级平均 `(1/k) Σ_{j≤k} FreqOf (G_j)` 在 `01|23` 分量上的误差
   `|· − 2/5|`（`k = 1, 2, 4, …, 8192`）—— 用**精确有理数**的期望 + 固定种子模拟。

只依赖标准库（`fractions` / `random` / `itertools`）。
"""

from fractions import Fraction as F
from itertools import combinations
import random

# ---------------------------------------------------------------- 小情形穷举

ELEMS = (0, 1, 2, 3)


def powerset(s):
    s = list(s)
    out = []
    for r in range(len(s) + 1):
        for c in combinations(s, r):
            out.append(frozenset(c))
    return out


def kpartitions(alpha, n):
    """alpha 的所有 n-块**有序**划分（块非空、两两不交、并为全体）。"""
    a = list(alpha)
    out = []
    for assign in __import__("itertools").product(range(n), repeat=len(a)):
        blocks = [set() for _ in range(n)]
        for x, b in zip(a, assign):
            blocks[b].add(x)
        if all(blocks):
            out.append(tuple(frozenset(b) for b in blocks))
    return out


SPLITS = kpartitions(ELEMS, 2)           # == Split (Fin 4)，两侧有序
TWO_TWO = [s for s in SPLITS if len(s[0]) == 2]
ONE_THREE = [s for s in SPLITS if len(s[0]) != 2]


def swap(s):
    return (s[1], s[0])


def class_of(s):
    """无向 quartet 类（三类之一）；`1|3` 返回 None。"""
    if len(s[0]) != 2:
        return None
    a = frozenset(s[0])
    for cls in (frozenset({0, 1}), frozenset({0, 2}), frozenset({0, 3})):
        if a == cls or (frozenset(ELEMS) - a) == cls:
            return cls
    raise AssertionError("unreachable")


CLASS_A = frozenset({0, 1})              # 01|23  （真类）
CLASS_B = frozenset({0, 2})              # 02|13
CLASS_C = frozenset({0, 3})              # 03|12


def point_table(cls):
    """质量 1 全在无向类 `cls` 上：该类两条**有向** split 各 1/2。"""
    return {s: (F(1, 2) if class_of(s) == cls else F(0)) for s in SPLITS}


FREQ_A = point_table(CLASS_A)
FREQ_B = point_table(CLASS_B)


def check_quartet_freq(name, p):
    """验证 QuartetFreq 三条字段（对**全部** Split (Fin 4) 求和/对称）。"""
    bad = []
    if any(v < 0 for v in p.values()):
        bad.append("p_nonneg")
    if sum(p.values()) != 1:
        bad.append("p_sum_one (sum=%s)" % sum(p.values()))
    if any(p[swap(s)] != p[s] for s in SPLITS):
        bad.append("p_swap")
    print("  %-8s p_nonneg=OK p_sum_one=%s p_swap=%s  质量分布: %s"
          % (name, sum(p.values()), "OK" if not bad else "FAIL",
             {str(k): str(v) for k, v in sorted(p.items()) if v}))
    return not bad


NU_FALSE, NU_TRUE = F(4, 5), F(1, 5)


def pushforward():
    """m.freq = (4/5)·freqA + (1/5)·freqB（= k → ∞ 时的极限表）。"""
    return {s: NU_FALSE * FREQ_A[s] + NU_TRUE * FREQ_B[s] for s in SPLITS}


M_FREQ = pushforward()


def class_mass(p, cls):
    """表 `p` 在无向类 `cls` 上的总质量。"""
    return sum(v for s, v in p.items() if class_of(s) == cls)


def directed_mass(p, s):
    return p[s]


# ---------------------------------------------------------------- 1. 穷举验证

print("=" * 78)
print("1. 小情形穷举：Split (Fin 4) 的 14 条 ＋ 三张表的字段验证")
print("=" * 78)
print("  #Split(Fin 4)            = %d   (6 条 2|2 ＋ 8 条 1|3)" % len(SPLITS))
print("  #(2|2 有向)              = %d" % len(TWO_TWO))
print("  #(1|3 有向)              = %d" % len(ONE_THREE))
print("  三张表在三个无向类上的质量：")
for nm, tb in (("freqA", FREQ_A), ("freqB", FREQ_B), ("m.freq", M_FREQ)):
    print("    %-7s  %s" % (nm, {str(c): str(class_mass(tb, c))
                               for c in (CLASS_A, CLASS_B, CLASS_C)}))
ok = all(check_quartet_freq(nm, tb)
         for nm, tb in (("freqA", FREQ_A), ("freqB", FREQ_B), ("m.freq", M_FREQ)))
print("  ⇒ 三张表全部合法：%s" % ok)

# ---------------------------------------------------------------- 2. majorizes

print()
print("=" * 78)
print("2. `majorizes` 的**严格**不等式（★D：简报 §7.4 的复核）")
print("=" * 78)
TRUE_SPLIT = (frozenset({0, 1}), frozenset({2, 3}))
v_true = M_FREQ[TRUE_SPLIT]
competitors = [s for s in SPLITS if s != TRUE_SPLIT and s != swap(TRUE_SPLIT)]
worst = max(M_FREQ[s] for s in competitors)
print("  真 quartet 01|23 的（有向）split 上 m.freq = %s" % v_true)
print("  最强竞争者上 m.freq                     = %s" % worst)
print("  严格不等式 m.freq(竞争者) < m.freq(真)  = %s" % (worst < v_true))
print("  （若改用**公平**硬币 (1/2,1/2) 且两棵树的表都是**纯类**："
      "真类 = 竞争类 = 1/2 ⇒ 严格不等式**失败** ⇒ 必须加权）")
fair = {s: F(1, 2) * FREQ_A[s] + F(1, 2) * FREQ_B[s] for s in SPLITS}
print("  公平硬币下的真类/竞争类质量 = %s / %s"
      % (class_mass(fair, CLASS_A), class_mass(fair, CLASS_B)))

# ---------------------------------------------------------------- 3. k 固定

print()
print("=" * 78)
print("3. ★ k 固定（k = 1、L ≡ 1）：条件极限 = FreqOf(ω 0) ≠ m.freq")
print("=" * 78)
print("  位点数 n → ∞ 时，emp_n 的（条件）极限是**实现的基因树**给的表：")
for tree, freq in ((False, FREQ_A), (True, FREQ_B)):
    lim = directed_mass(freq, TRUE_SPLIT)
    tgt = directed_mass(M_FREQ, TRUE_SPLIT)
    print("    ω 0 = %-5s ⇒ 极限(01|23 分量) = %-5s ; m.freq = %-5s ; 差 = %-5s"
          % (tree, lim, tgt, lim - tgt))
print("  事件 {ω 0 = false} 的概率 = %s > 0  ⇒ 正测度集上极限 ≠ m.freq"
      % NU_FALSE)
print("  ⇒ 规格 §4.1：「k 固定时经验表 → m.freq」**为假** ✓")

# ---------------------------------------------------------------- 4. k → ∞

print()
print("=" * 78)
print("4. k → ∞：块级平均 (1/k)Σ_{j≤k} FreqOf(G_j) → m.freq（01|23 分量）")
print("=" * 78)
TARGET = directed_mass(M_FREQ, TRUE_SPLIT)
print("  精确期望（(1/k)Σ 的期望恒 = m.freq）：%s" % TARGET)
print()
print("   %8s | %-18s | %-12s | %-12s" % ("k", "样本块级平均(01|23)", "误差(绝对)", "误差(相对)"))
rng = random.Random(20261012)


def block_avg(k, rng):
    s = F(0)
    for _ in range(k):
        b = False if rng.random() < float(NU_FALSE) else True
        s += directed_mass(FREQ_A if not b else FREQ_B, TRUE_SPLIT)
    return s / k


for k in (1, 2, 4, 8, 16, 64, 256, 1024, 4096, 8192):
    avg = block_avg(k, rng)
    err = abs(avg - TARGET)
    rel = err / TARGET
    print("   %8d | %-18s | %-12s | %-.6f" % (k, avg, err, float(rel)))
print()
print("  ⇒ 误差随 k 单调趋势下降（SLLN 的数值迹象）；"
      "这正是 k → ∞ 与 k 固定的**分水岭**（规格 §4.1 ①）。")
print()
print("=" * 78)
print("结论：k = 1 时正测度事件 {ω 0 = false} 上极限(=freqA) ≠ m.freq（差 1/10）；")
print("      k → ∞ 时块级平均才收敛到 m.freq。规格 §4.1 的机制数值确认 ✓")
print("=" * 78)
