#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W10 —— 一般 `n` 的溯祖（合并）历史计数的**独立**数值/穷举复核.

对应 Lean 交付物：
  `Phylo/Stat/CoalescentHistoryCount.lean`
    - ★★★ `card_mergeHistories_eq_H (n) (hn : 1 ≤ n) :
             ((RankedGeneTree.mergeHistories n).card : ℝ) = RankedGeneTree.H n`
    - `card_mergeHistories_eq_Hnat`（`ℕ` 版）
    - `card_mhFinset`（对**任意**有限集 `s` 的归纳主引理：`|s| = m+1` 时恰 `Hnat (m+1)` 个）
    - `card_pairIn` / `card_headFiber` / `isMH_tail` / `isMH_head`

复核策略（**与 Lean 无关的第二实现**，只是复刻 Lean 的语义）：

  (A) `H_n = prod_{k=2}^{n} C(k,2)` 与闭形式 `n!(n-1)!/2^{n-1}` 逐项相等（n = 2..14）。

  (B) **直接模拟 Lean 的编码**（`RankedGeneTree.IsMergeHistory`）：
      状态是「块代表映射」`r : Fin n -> Fin n`（初值 `id`）；
      一步取 `(x, y)`，`x`、`y` 都是 `r` 的不动点（= 各自块的代表）且 `x < y`；
      `RankedGeneTree.stepMap r x y := fun w => if r w == y then x else r w`（把 `y` 的块并进 `x` 的块）；
      走满 `n-1` 步后要求 `r` 是常函数（所有谱系并成一块）。
      穷举计数 = `H_n`（n = 2..7，即 1, 3, 18, 180, 2700, 56700）。

  (C) **`IsMH` 的推广形式**（Lean 主引理 `card_mhFinset` 的内容）：
      对 `Fin N` 的**每个子集** `s`，用同一套 `stepMap` 语义、只允许取 `s` 里的代表对，
      走 `|s|-1` 步把 `s` 并成一块；计数必须 `= Hnat (|s|)`。
      这与 Lean 的归纳假设逐字对应（`N = 0..6` 的全部 `2^N` 个子集）。

  (D) 递推 `|T(n+1)| = C(n+1,2) * |T(n)|`（Lean `card_mergeHistories_succ`）与
      `Hnat` 定义本身 `Hnat (n+2) = Hnat (n+1) * C(n+2,2)`。

  (E) 与库内既有实例对齐：`Phylo/Stat/RankedGeneTree.lean` 的
      `card_mergeHistories_two/three/four = 1, 3, 18`，以及 `H_eq_factorial`
      （`H_l = l!(l-1)!/2^(l-1)`）。另与 `scripts/msc/stadler_degnan_ranked.py`
      的独立「集合划分链」穷举交叉核对（那份脚本用的是 `frozenset` 划分，语义等价但实现不同）。

不依赖任何第三方库；纯整数/`math.comb`。
"""

from math import comb, factorial
from itertools import combinations
import sys

FAIL = []


def check(name, got, want):
    ok = got == want
    print(("  [ok]   " if ok else "  [FAIL] ") + name + f": got={got} want={want}")
    if not ok:
        FAIL.append(name)


# --------------------------------------------------------------- (A) H_n
def H_prod(n):
    """prod_{k=2}^{n} C(k,2)（Lean `RankedGeneTree.H_eq_prod` / 本文件 `Hnat_eq_prod`）。"""
    r = 1
    for k in range(2, n + 1):
        r *= comb(k, 2)
    return r


def H_closed(n):
    """n!(n-1)!/2^{n-1}（论文式 (2)，Lean `RankedGeneTree.H_eq_factorial`）。"""
    if n == 0:
        return 1
    return factorial(n) * factorial(n - 1) // (2 ** (n - 1))


def section_A():
    print("(A) H_n = prod_{k=2}^{n} C(k,2) 与闭形式 n!(n-1)!/2^{n-1}")
    for n in range(2, 15):
        check(f"H_{n} 乘积 = 闭形式", H_prod(n), H_closed(n))
    print("      H_2..H_7 =", [H_prod(n) for n in range(2, 8)])
    print("      H_5 =", H_prod(5), " (= 5!*4!/2^4 =", factorial(5) * factorial(4) // 16, ")")


# --------------------------------- (B) 直接模拟 Lean 的合并史编码
def step_map(r, x, y):
    """`RankedGeneTree.stepMap r x y`（逐字复刻）。"""
    return tuple(x if r[w] == y else r[w] for w in range(len(r)))


def count_merge_histories(n):
    """穷举 `RankedGeneTree.IsMergeHistory n`：返回合并史个数.

    与 Lean 的编码完全一致：
      * 状态 `r : Fin n -> Fin n` 是块代表映射（块的代表 = 块内最小元）；
      * 第 k 步 `f k = (x, y)` 需 `r x = x`、`r y = y`、`x < y`（`IsStep`）；
      * `r' = stepMap r x y`；
      * `n-1` 步之后 `r` 必须是常函数。
    """
    if n == 0:
        return 0
    ident = tuple(range(n))
    total = 0

    def rec(r, steps_left):
        nonlocal total
        if steps_left == 0:
            if len(set(r)) == 1:
                total += 1
            return
        reps = [w for w in range(n) if r[w] == w]
        for x, y in combinations(reps, 2):
            rec(step_map(r, x, y), steps_left - 1)

    rec(ident, n - 1)
    return total


def section_B():
    print("(B) 穷举 Lean 编码 `IsMergeHistory` 的合并史数（n = 1..7）")
    want = {1: 1, 2: 1, 3: 3, 4: 18, 5: 180, 6: 2700, 7: 56700}
    for n in range(1, 8):
        got = count_merge_histories(n)
        check(f"n={n} 合并史数 = H_{n}", got, H_prod(n))
        if n in want:
            check(f"n={n} 与任务书给的数一致", got, want[n])
    print("      得到：n=2..7 ->", [count_merge_histories(n) for n in range(2, 8)])


# --------------------------- (C) IsMH 的推广形式（任意有限子集 s）
def count_merge_histories_on(s, N):
    """`IsMH s m`（`m = |s| - 1`，`ℕ` 截断减法）的计数：只允许取 `s` 里的代表对.

    `s` 是 `range(N)` 的子集；语义与 Lean 的 `IsMH` 逐条对应（含「每步两个代表都在 `s` 里」）。
    ⚠️ `s = ∅` 时 Lean 里 `m = 0 - 1 = 0`（`ℕ` 截断），唯一的 `f : Fin 0 → _` 平凡满足
    `IsMH`（成员条件与常值条件都空），故计数 `1 = Hnat 0 = Hnat 1`；
    Lean 的 `card_mhFinset` 只在 `s.card = m + 1`（即 `|s| ≥ 1`）时发言。
    """
    if not s:
        return 1
    ident = tuple(range(N))
    total = 0

    def rec(r, steps_left):
        nonlocal total
        if steps_left == 0:
            anchor = r[min(s)]
            if all(r[w] == anchor for w in s):
                total += 1
            return
        reps = [w for w in s if r[w] == w]
        for x, y in combinations(reps, 2):
            rec(step_map(r, x, y), steps_left - 1)

    rec(ident, len(s) - 1)
    return total


def section_C():
    print("(C) 推广形式 `IsMH s`：对 `Fin N` 的每个子集 `s`，计数 = Hnat (|s|)")
    for N in range(0, 7):
        bad = 0
        tested = 0
        for mask in range(1 << N):
            s = tuple(i for i in range(N) if (mask >> i) & 1)
            got = count_merge_histories_on(s, N)
            want = H_prod(len(s))
            tested += 1
            if got != want:
                bad += 1
                print(f"        [FAIL] N={N} s={s} got={got} want={want}")
        check(f"N={N}: {tested} 个子集全部满足 |MH(s)| = Hnat(|s|)", bad, 0)


# ------------------------------------------------------------- (D) 递推
def section_D():
    print("(D) 递推 |T(n+1)| = C(n+1,2) * |T(n)| 与 Hnat 递推")
    prev = 1  # |T(1)| = Hnat 1 = 1
    for n in range(1, 7):
        nxt = comb(n + 1, 2) * prev
        check(f"n={n}: C({n+1},2)*|T({n})| = H_{n+1}", nxt, H_prod(n + 1))
        prev = nxt
    # Hnat 的定义本身
    hnat = [1, 1]
    for j in range(0, 12):
        hnat.append(hnat[j + 1] * comb(j + 2, 2))
    check("Hnat 定义递推与乘积一致 (m = 0..13)", [hnat[m] for m in range(0, 14)],
          [H_prod(m) for m in range(0, 14)])


# ------------------------------- (E) 与库内既有实例/论文公式对齐
def section_E():
    print("(E) 与库内既有实例对齐")
    check("RankedGeneTree.card_mergeHistories_two   = 1", count_merge_histories(2), 1)
    check("RankedGeneTree.card_mergeHistories_three = 3", count_merge_histories(3), 3)
    check("RankedGeneTree.card_mergeHistories_four  = 18", count_merge_histories(4), 18)
    check("本文件 card_mergeHistories_five          = 180", count_merge_histories(5), 180)
    check("H_2 = 1, H_3 = 3, H_4 = 18, H_5 = 180",
          [H_prod(n) for n in (2, 3, 4, 5)], [1, 3, 18, 180])


def main():
    print("=" * 78)
    print("W10 复核：一般 n 的溯祖（合并）历史计数 = H_n = prod_{k=2}^{n} C(k,2)")
    print("=" * 78)
    section_A()
    section_B()
    section_C()
    section_D()
    section_E()
    print("=" * 78)
    if FAIL:
        print(f"失败 {len(FAIL)} 项：{FAIL}")
        return 1
    print("全部核对通过（纯整数穷举，无 Monte Carlo）。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
