/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJ
import Phylo.Stat.MSC

/-!
# `Phylo.Stat.NJst` —— NJst 在多物种下的统计一致性（框架 + 诚实的依赖边界）

**NJst**（Liu–Yu 2011）用**基因树的平均距离**跑 NJ 恢复物种树；不依赖任何度量信息，
只依赖基因树**拓扑**。文献：**Allman–Degnan–Rhodes 2016**（arXiv:1604.05364）
Theorem 4.1 证明了 NJst 在 MSC 下对**任意大**的物种树的统计一致性。

## 本文件做到哪里

* `NJstData` —— 把 ADR 2016 的输入公理化（平均距离 + 真树 + 两条 MSC 引理）；
* ★ `njst_cherry` —— **NJst 的第一步正确**：z 最大的对是真树的 cherry
  （由 `Dissimilarity.nj_cherry` + `MaxZCherryCore` 直接给出）；
* ⬜ **完整一致性**（把「第一步正确」升级为「整棵树正确」）**未形式化** —— 见下。

## 诚实边界（两条，都是已知硬骨头）

1. **`MaxZCherryCore`** —— 「z 最大 ⟺ cherry」在 `Phylo/Algorithm/NJ` 中记为
   **形式化缺口**。⚠️ **注意：这不是学术开放问题** —— NJ 正确性见
   Studier–Keppler (1988)、Weller (2023)；缺口在于本库尚未形式化其前置
   「**实现树 / Buneman 存在性**」。
2. **NJ 的归纳正确性** —— 合并 cherry 后新距离矩阵**仍是树度量**（四点点条件保持），
   从而可归纳。这一步在库里尚未建立。

ADR 2016 之所以能绕开 (1)，是靠把 NJst **归约到 generalized STAR**（clade 共识），
而 STAR 的一致性最终仍需要「**clade 系统决定树**」——与 `Phylo.Stat.QuartetDecides`
同一类定理（即四个算法共享的最后一个缺口）。
-/

universe u v

open NJ

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★ **（公理化）NJst 的 MSC 数据**。

* `δ` —— 由基因树导出的**平均距离**；
* `tree` —— 真物种树；
* `fourPoint` —— ★ MSC 引理（ADR 2016）：平均距离满足**四点点条件**；
* `core` —— ★ NJ 硬核（`MaxZCherryCore`，见模块文档的诚实边界）。 -/
structure NJstData (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 平均距离（无噪极限）。 -/
  δ : Dissimilarity X
  /-- 真物种树。 -/
  tree : Cladogram.{u, v} X
  /-- ★ MSC 引理：平均距离满足四点点条件。 -/
  fourPoint : δ.FourPoint
  /-- ★ NJ 硬核（**形式化缺口，非开放问题**；NJ 正确性见 Studier–Keppler 1988）、 -/
  core : δ.MaxZCherryCore

namespace NJstData

variable (M : NJstData.{u, v} X)

/-- ★ **NJst 的第一步正确**：`Q` 最小的叶对（等价地 `z` 最大）是真树的 cherry。

这正是 NJ 迭代算法的**归纳基**。 -/
theorem njst_cherry (a b : X) (hab : a ≠ b)
    (hmin : ∀ i j : X, i ≠ j → M.δ.Q a b ≤ M.δ.Q i j) : M.δ.IsCherry a b :=
  M.δ.nj_cherry M.core M.fourPoint a b hab hmin

/-- **四点点条件可传**（`NJstData` 的 `fourPoint` 是 `δ` 的性质，便于下游引用）。 -/
theorem four_point (a b c d : X) :
    M.δ.val a b + M.δ.val c d ≤ M.δ.val a c + M.δ.val b d
    ∨ M.δ.val a b + M.δ.val c d ≤ M.δ.val a d + M.δ.val b c :=
  M.fourPoint a b c d

end NJstData
