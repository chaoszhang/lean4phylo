#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/msc/trivial_split_count.py -- W10：缺口 G1（`Split (Fin n)` 上平凡 split 的计数）的
**独立穷举复核**。

对应 Lean 模块：`Phylo/Stat/TrivialSplitCount.lean`
  * `card_sideA_one`      : `n >= 2` 时「sideA 单点」的**有向** split 恰 `n` 个
  * `card_sideB_one`      : `n >= 2` 时「sideB 单点」的**有向** split 恰 `n` 个
  * `card_trivial_splits` : `n >= 3` 时平凡（某一侧 `card = 1`）的有向 split 恰 `2n` 个
  * `card_trivial_splits_gap_holds` : 登记缺口 `SplitProbabilities.card_trivial_splits_gap` 成立

为什么必须要脚本/独立复核：`Split (Fin n)` 的 `Fintype` 来自 `Fintype.ofInjective`
（`Phylo/Split.lean` 第 194-197 行），**非可计算**，`decide` 枚举不了它。
但「**有序** split ↔ 非空真子集 `A`」（`A = sideA`、`B = Aᶜ`）是双射，而子集枚举可计算 ——
本脚本就在这个等价的**可计算代理**上做**精确穷举**（不是 Monte Carlo，不是重跑 Lean）。

模型（与 `Phylo/Split.lean` 第 153-220 行逐条对应）：
  * `Split α = KPartition α 2` 用 `Fin 2` 把两侧**有序化**，故一个**无向** split 对应
    `(A, Aᶜ)` 与 `(Aᶜ, A)` 两个有向值（`r` 与 `r.swap`）；
  * 非退化 split 要求两侧都非空（`KPartition.nonempty`）—— 故 `2^n - 2` 个有向 split；
  * **平凡** = `|A| = 1 ∨ |Aᶜ| = 1`。

复核条目（每条打印 PASS/FAIL）：
  (A) 有向 split 总数 `= 2^n - 2`；
  (B) `|sideA| = 1` 的个数 `= n`、`|sideB| = 1` 的个数 `= n`（`n >= 2`）；
  (C) `n >= 3` 时两支**不交**（`|A| = 1` 与 `|A| = n-1` 不能同时成立），故平凡数 `= 2n`；
      `n = 2` 时两支**重合**（两侧都是单点），平凡数 `= 2 != 2n = 4` —— 这正是 Lean 主定理
      带假设 `3 <= n` 的原因；
  (D) 无向平凡 split（等价类 `{A, Aᶜ}`）`= n`（`n >= 3`），与 ADR2017 第 355-357 行一致；
  (E) 交叉核对 `MSCProof.card_splits_two`：`n = 4` 时 `2|2` 恰 `6`、`1|3` 恰 `8`、总数 `14`。

运行：  python trivial_split_count.py
无第三方依赖（只用标准库 `itertools`）。
"""

from itertools import combinations
import sys

FAILED = []


def check(name, cond, detail=""):
    ok = bool(cond)
    print("  [%s] %s%s" % ("PASS" if ok else "FAIL", name, ("  " + detail) if detail else ""))
    if not ok:
        FAILED.append(name)
    return ok


def ordered_splits(n):
    """全部**有向** split `(A, A^c)`，两侧都非空；`A` 是 `frozenset`。"""
    base = list(range(n))
    out = []
    for r in range(1, n):                       # |A| = r，1 <= r <= n-1（两侧都非空）
        for A in combinations(base, r):
            fa = frozenset(A)
            out.append((fa, frozenset(base) - fa))
    return out


def main():
    print("== (A)(B)(C) 逐 n 穷举：有向 split 的平凡计数 ==")
    print("   n |  总数 2^n-2 | |A|=1 | |A^c|=1 | 支交集 | 平凡(并) | 期望 | 无向平凡")
    for n in range(2, 13):
        splits = ordered_splits(n)
        total = len(splits)
        a1 = [s for s in splits if len(s[0]) == 1]
        b1 = [s for s in splits if len(s[1]) == 1]
        inter = [s for s in splits if len(s[0]) == 1 and len(s[1]) == 1]
        triv = [s for s in splits if len(s[0]) == 1 or len(s[1]) == 1]
        undir = set(frozenset((s[0], s[1])) for s in triv)
        expect = 2 * n if n >= 3 else 2
        print("  %2d | %11d | %5d | %7d | %6d | %8d | %4d | %8d"
              % (n, total, len(a1), len(b1), len(inter), len(triv), expect, len(undir)))

        check("(A) n=%d 有向 split 总数 = 2^n-2" % n, total == 2 ** n - 2,
              "实测 %d" % total)
        check("(B) n=%d |sideA|=1 的个数 = n" % n, len(a1) == n, "实测 %d" % len(a1))
        check("(B) n=%d |sideB|=1 的个数 = n" % n, len(b1) == n, "实测 %d" % len(b1))
        check("(C) n=%d 平凡数 = %d" % (n, expect), len(triv) == expect,
              "实测 %d" % len(triv))
        if n >= 3:
            check("(C) n=%d 两支不交" % n, len(inter) == 0, "交集 %d" % len(inter))
            check("(C) n=%d 两支各自 n 个且不交 => 2n" % n,
                  len(a1) + len(b1) == len(triv) == 2 * n)
            check("(D) n=%d 无向平凡 split = n" % n, len(undir) == n, "实测 %d" % len(undir))
        else:
            check("(C) n=2 两支重合（故 2 != 2n = 4）", len(inter) == 2, "交集 %d" % len(inter))

    print()
    print("== (E) 交叉核对 MSCProof.card_splits_two（n = 4）==")
    s4 = ordered_splits(4)
    two_two = [s for s in s4 if len(s[0]) == 2]
    # ⚠️ `1|3` 是**无向**的类别：`|A|=1`（4 个）与 `|A^c|=1` 即 `|A|=3`（另 4 个）都要算，
    # 故必须写 `len(s[0]) == 1 or len(s[1]) == 1`。本脚本第一版写成只数 `len(s[0]) == 1`，
    # 得 4 —— 被这条自检当场抓住（见 `scripts/msc/README.md` 的「脚本自身踩过的坑」）。
    one_three = [s for s in s4 if len(s[0]) == 1 or len(s[1]) == 1]
    check("(E) |2|2| = 6", len(two_two) == 6, "实测 %d" % len(two_two))
    check("(E) |1|3| = 8", len(one_three) == 8, "实测 %d" % len(one_three))
    check("(E) 总数 14 = 6 + 8", len(s4) == 14 == len(two_two) + len(one_three),
          "实测 %d" % len(s4))
    check("(E) n=4 平凡数 = 8 = 2*4（与 card_trivial_splits_four 一致）",
          len([s for s in s4 if len(s[0]) == 1 or len(s[1]) == 1]) == 8)

    print()
    if FAILED:
        print("VERDICT: FAIL  (%d 条未通过：%s)" % (len(FAILED), ", ".join(FAILED)))
        return 1
    print("VERDICT: PASS  (n = 2..12 全部穷举通过；n >= 3 时平凡有向 split = 2n)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
