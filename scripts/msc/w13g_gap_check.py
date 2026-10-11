#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
W13g（ASTRAL 捷径）数值复核 —— ★D「`hpush` ＋ `MSCFreq.majorizes` 可同时满足吗？」

对应 Lean 文件：`Phylo/Stat/GeneTreeSamplingAE.lean`（§5 ★D 反空洞 / §6 退化一致性）。
零第三方依赖（只用标准库）。

## 口径（与 Lean 侧逐字一致）

* `X = Fin 4`，`Split ↥S` 是**有向**二分（`sideA`/`sideB` 均非空）⇒ `2^4 - 2 = 14` 个；
  `QuartetFreq.p_sum_one` 是对**全部 14 个有向 split** 求和为 `1`，
  且 `p_swap : p q.swap = p q` ⇒ 概率质量是「无向类」的 **2 倍记账**。
* 「点质量表」`point(c)`：在 `c` 与 `c.swap` 上各放 `1/2`，其余 `0`（和 = 1 ✓）——
  即「单棵基因树在 `S` 上展示 quartet 类 `c`」的退化频率表。
* `mix(α, β, D, E) := α·D + β·E`（`α, β ≥ 0`、`α + β = 1`）。
* `MSCFreq.majorizes`：真 quartet 类 `q` **严格**最大（`r ≠ q`、`r ≠ q.swap` ⇒ `p r < p q`）。

跑法：`python3 scripts/msc/w13g_gap_check.py`
"""

from itertools import combinations
from fractions import Fraction as F

S = (0, 1, 2, 3)


def directed_splits(items):
    """全部有向二分 (A, B)：A ∪ B = items、A ∩ B = ∅、A ≠ ∅、B ≠ ∅。"""
    out = []
    lst = list(items)
    for k in range(1, len(lst)):
        for A in combinations(lst, k):
            A = frozenset(A)
            B = frozenset(x for x in lst if x not in A)
            out.append((A, B))
    return out


SPLITS = directed_splits(S)
BY_KEY = {s: i for i, s in enumerate(SPLITS)}


def swap(s):
    return (s[1], s[0])


def table_from_point(c):
    """点质量表：c 与 c.swap 上各 1/2。"""
    return {s: (F(1, 2) if s == c or s == swap(c) else F(0)) for s in SPLITS}


def mix(alpha, beta, D, E):
    assert alpha >= 0 and beta >= 0 and alpha + beta == 1
    return {s: alpha * D[s] + beta * E[s] for s in SPLITS}


def is_freq_table(D):
    """非负 + 14 个有向 split 全和 = 1 + swap 不变。"""
    return (all(v >= 0 for v in D.values())
            and sum(D.values()) == 1
            and all(D[swap(s)] == D[s] for s in SPLITS))


def majorizes(D, q):
    """真类 q 严格最大（模 swap）？失败的见证一并返回。"""
    bad = []
    for r in SPLITS:
        if r == q or r == swap(q):
            continue
        if not D[r] < D[q]:
            bad.append((r, D[r], D[q]))
    return bad


Q = frozenset((0, 1))            # 类 01|23
A = frozenset((0, 2))            # 类 02|13
q = (Q, frozenset((2, 3)))       # 真 quartet 的有向代表：{0,1} | {2,3}
a = (A, frozenset((1, 3)))       # 另一个类的有向代表：{0,2} | {1,3}

print("=" * 78)
print("Part I —— 计数复核（简报 §9 提醒：两侧有序、对全部 Split 求和为 1）")
print("=" * 78)
print(f"|Split (Fin 4)|（有向）= {len(SPLITS)}   （期望 14 = 2^4 - 2）")
trivial = [s for s in SPLITS if len(s[0]) == 1 or len(s[1]) == 1]
nontriv = [s for s in SPLITS if len(s[0]) == 2]
print(f"  平凡 1|3 有向 split = {len(trivial)}（期望 8）")
print(f"  非平凡 2|2 有向 split = {len(nontriv)}（期望 6 = 3 类 × 2 向）")
print(f"  无向类数 = {len(SPLITS) // 2}（期望 7）")
assert len(SPLITS) == 14 and len(trivial) == 8 and len(nontriv) == 6

print()
print("=" * 78)
print("Part II —— ★D 结论（1）：本文件的居民【可同时满足 hpush 与 majorizes】 ✓")
print("=" * 78)
T = table_from_point(q)                     # witnessQTable（点质量在真类）
Atab = table_from_point(a)                  # witnessATable（点质量在 02|13 类）
mixT = mix(F(1, 2), F(1, 2), T, Atab)       # witnessMixTable：freqOf true
freq = mix(F(3, 4), F(1, 4), T, Atab)       # witnessFreq：理论表
for name, D in (("witnessQTable", T), ("witnessATable", Atab),
                ("witnessMixTable", mixT), ("witnessFreq", freq)):
    print(f"  {name:18s} 是合法 QuartetFreq = {is_freq_table(D)}")
    assert is_freq_table(D)
hpush = all(F(1, 2) * mixT[s] + F(1, 2) * T[s] == freq[s] for s in SPLITS)
print(f"  hpush（freqOf true/false 各 1/2 的平均 = witnessFreq，逐点）：{hpush}")
assert hpush
print(f"  witnessFreq.p(真类 01|23) = {freq[q]}   （期望 3/8）")
print(f"  witnessFreq.p(类 02|13)   = {freq[a]}   （期望 1/8）")
bad = majorizes(freq, q)
print(f"  majorizes 反例数 = {len(bad)}   （期望 0）")
assert freq[q] == F(3, 8) and freq[a] == F(1, 8) and not bad

print()
print("=" * 78)
print("Part III —— ★D 结论（2）：公平硬币 + 两棵【纯点质量】树 各 1/2  ==> 失败 ✗")
print("=" * 78)
tie = mix(F(1, 2), F(1, 2), T, Atab)
bad = majorizes(tie, q)
print(f"  两棵纯点质量树各 1/2 的平均表 = {tie[q]} (真类) 与 {tie[a]} (竞争类) —— 并列")
print(f"  majorizes 反例：{[(sorted(r[0]), D_r, D_q) for r, D_r, D_q in bad]}")
assert tie[q] == tie[a] == F(1, 4) and bad, "本候选应当失败"
print("  ⇒ 「G = Bool、公平硬币、两棵点质量树各 1/2」**不是** GeneTreeModel 的居民。")

print()
print("  备选（也成立）：**点质量 + 权重不等** w(true)=1/5、w(false)=4/5（简报 §7.4 的原始建议）")
alt = mix(F(4, 5), F(1, 5), T, Atab)
bad_alt = majorizes(alt, q)
print(f"    平均表：真类 {alt[q]}、竞争类 {alt[a]}；majorizes 反例数 = {len(bad_alt)}")
assert not bad_alt

print()
print("=" * 78)
print("Part IV —— k 固定（k = 1）时「经验表 = 理论表」为假（规格 §4.1 的同族反例）")
print("=" * 78)
emp1_true = mixT        # ω 0 = true  ⇒ emp 1 ω = freqOf true
emp1_false = T          # ω 0 = false ⇒ emp 1 ω = freqOf false
print(f"  emp 1 (ω 0 = true ).p(02|13 类) = {emp1_true[a]}  vs 理论表 {freq[a]}  ⇒ 不等")
print(f"  emp 1 (ω 0 = false).p(02|13 类) = {emp1_false[a]}  vs 理论表 {freq[a]}")
assert emp1_true != freq and emp1_false[a] == 0 and freq[a] == F(1, 8)
print("  ⇒ 固定 k 时经验表是**依赖实现**的随机量（不是常数 m.freq）；")
print("    这正是规格 §4.1「k 固定 ⇒ 假」在基因树层的同族反例。")

print()
print("=" * 78)
print("Part V —— ★8④ 退化一致性（ν = Dirac、freqOf 常值 = m.freq）")
print("=" * 78)
print("  freqOf 常值 ⇒ emp k ω = m.freq 对一切 k、ω（Lean: diracModel_emp_eq）")
print(f"  数值：任意常数表 C 上，(1/k)·Σ_(j<k) C = C —— k = 1..5 逐点复核：", end=" ")
assert all(F(1, k) * sum([T[s]] * k) == T[s] for k in range(1, 6) for s in SPLITS)
print("OK")
print("  ⇒ 结论退回 MSCSamplingFixed.converges 的确定性形态（N = 0 即可）。")

print()
print("=" * 78)
print("全部断言通过 ✓")
print("=" * 78)
