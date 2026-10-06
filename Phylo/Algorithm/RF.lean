/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Distance
import Phylo.Split

/-!
# `Phylo.Algorithm.RF` —— Robinson–Foulds 距离

`CONCEPTS.md` §5 M5 算法层：**RF 距离**是两个 split 系统的**对称差大小**
`d(S,S') = |S △ S'|`。度量性质由通用骨架 `symmDiffCard`（`Phylo/Distance.lean`）直接继承。

（注：一般还有加权 / 簇版 RF；此处给**无权簇版**，够 M5 起步用。）
-/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Robinson–Foulds 距离**：两个 split 系统的对称差大小。 -/
abbrev rfDistance (S S' : Finset (Split α)) : ℕ := symmDiffCard S S'

theorem rfDistance_def (S S' : Finset (Split α)) :
    rfDistance S S' = ((S \ S') ∪ (S' \ S)).card := rfl

theorem rfDistance_comm (S S' : Finset (Split α)) : rfDistance S S' = rfDistance S' S :=
  symmDiffCard_comm S S'

@[simp] theorem rfDistance_self (S : Finset (Split α)) : rfDistance S S = 0 :=
  symmDiffCard_self S

/-- **分离性**：RF 距离为 0 ⟺ 两个系统相等。 -/
@[simp] theorem rfDistance_eq_zero_iff {S S' : Finset (Split α)} :
    rfDistance S S' = 0 ↔ S = S' :=
  symmDiffCard_eq_zero_iff

/-- **三角不等式**。 -/
theorem rfDistance_triangle (S R T : Finset (Split α)) :
    rfDistance S T ≤ rfDistance S R + rfDistance R T :=
  symmDiffCard_triangle S R T

end Split
