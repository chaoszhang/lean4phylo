/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Phylo.Algorithm.NJ

/-!
# `Phylo.Algorithm.UPGMA` —— 超度量（ultrametric）与 UPGMA 的组合基础

`CONCEPTS.md` §5 的 M5：UPGMA（unweighted pair group method with arithmetic mean）
要求输入是**超度量**（分子钟假设），输出是一棵**超度量树**（所有叶到根等距）。

本文件给**超度量**的定义与组合基础（不依赖建树）：

* `Ultrametric δ`：`δ i k ≤ max (δ i j) (δ j k)` —— 比三角不等式强；
* **★ 球传递性 `ball_trans`**：`δ x y ≤ r ∧ δ y z ≤ r → δ x z ≤ r`
  —— 即「`≤ r` 是**等价关系**」，UPGMA 的分层聚类全靠它；
* `le_of_le`（**等腰性**：`δ x y ≤ δ x z → δ y z ≤ δ x z`）· `triangle`
  （`max ≤ 和`，需非负）。

⚠️ 注意：超度量条件 + 零对角 **不**蕴含非负（例：`δ ≡ -1` 于非对角满足之）。
故 `triangle` 显式带非负假设。
-/

noncomputable section

namespace NJ

variable {X : Type*} [Fintype X] [DecidableEq X]

namespace Dissimilarity

variable (δ : Dissimilarity X)

/-- **超度量（ultrametric）**：`δ i k ≤ max (δ i j) (δ j k)`。

比三角不等式强 —— 分子钟下任意三点构成**等腰三角形**（两腰相等且 ≥ 底）。 -/
def Ultrametric : Prop :=
  ∀ i j k : X, δ.val i k ≤ max (δ.val i j) (δ.val j k)

/-- **★ 球传递性**：`≤ r` 是**等价关系**（UPGMA 分层聚类的核心）。 -/
theorem ball_trans (h : δ.Ultrametric) {r : ℝ} {x y z : X}
    (hxy : δ.val x y ≤ r) (hyz : δ.val y z ≤ r) : δ.val x z ≤ r :=
  le_trans (h x y z) (max_le hxy hyz)

omit [Fintype X] [DecidableEq X] in
/-- **等腰性**：若 `δ x y ≤ δ x z`，则 `δ y z ≤ δ x z`
（`δ x z` 是三点两两距离中的最大者）。 -/
theorem le_of_le (h : δ.Ultrametric) {x y z : X} (hxy : δ.val x y ≤ δ.val x z) :
    δ.val y z ≤ δ.val x z := by
  have h1 := h y x z
  rw [δ.symm y x] at h1
  exact le_trans h1 (max_le hxy (le_refl _))

omit [Fintype X] [DecidableEq X] in
/-- **等腰性的等号形式**：若 `δ y z < δ x y`，则 `δ x z = δ x y`
（严格大于者与第三条边相等）。 -/
theorem eq_of_lt (h : δ.Ultrametric) {x y z : X} (hlt : δ.val y z < δ.val x y) :
    δ.val x z = δ.val x y := by
  refine le_antisymm (le_trans (h x y z) (max_eq_left hlt.le).le) ?_
  by_contra hcon
  rw [not_le] at hcon
  have h1 := h y z x
  rw [δ.symm y x, δ.symm z x] at h1
  have h2 : max (δ.val y z) (δ.val x z) < δ.val x y := max_lt hlt hcon
  linarith

omit [Fintype X] [DecidableEq X] in
/-- 超度量 ⟹ 三角不等式（需非负，使 `max ≤ 和`）。 -/
theorem ultrametric_triangle (h : δ.Ultrametric) (hpos : ∀ i j : X, 0 ≤ δ.val i j)
    (i j k : X) : δ.val i k ≤ δ.val i j + δ.val j k := by
  have h1 := h i j k
  have h2 : max (δ.val i j) (δ.val j k) ≤ δ.val i j + δ.val j k :=
    max_le (le_add_of_nonneg_right (hpos j k)) (le_add_of_nonneg_left (hpos i j))
  linarith

end Dissimilarity

end NJ
