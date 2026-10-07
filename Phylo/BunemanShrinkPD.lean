/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Buneman

/-!
# `Phylo.BunemanShrinkPD` —— **阴性结论**：Buneman 归纳步的收缩**不保持**正定性

`Phylo/Buneman.lean` 的归纳装配（★ `Dissimilarity.exists_realizingPhylogram_of_card_ne_one`）
只需要 `FourPoint`，**不需要** `PositiveDefinite`。原因之一是：**收缩本身会破坏正定性**。
本项目历史上反复尝试过「让正定性沿着归纳步保持」这条错路，本文件把它做成
**机器可查的阴性结论**，以免后人（以及后来的我）再试：

> ★★★ `not_positiveDefinite_shrinkDissimilarity`：
> `¬ ∀ (δ : Dissimilarity (Fin 4)) p q r, δ.PositiveDefinite → δ.FourPoint →
>   (δ.shrinkDissimilarity p q r).PositiveDefinite`

**见证**：星形度量 `ρ = (ρ_0, ρ_1, ρ_2, ρ_3) = (1, 1, 3, 0)`（星心到四片叶的距离），
取极大三元组 `(p,q,r) = (0,1,2)`：
`ρ(p;q,r) = ½(δ(p,q)+δ(p,r)−δ(q,r)) = ½(2+4−4) = 1`，而 `δ(3,p) = ρ_3 + ρ_0 = 1`
⇒ 收缩后 `δ'(inl 3, inr()) = δ(3,p) − ρ(p;q,r) = 0`，但 `inl 3 ≠ inr ()`
⇒ **收缩后的相异度不正定**（`val = 0` 而两点不同）。

⚠️ **与 T0.3 的关系**：这正是「扰动法不能省」的机器可查证据之一 —— 把 `δ` 换成
`Dissimilarity.addConst ε` 后，第 0 层所有 bracket `≥ ε > 0`，于是第 1 层的收缩项
`≥ ε/2 > 0` ⇒ **第 1 层仍正定**；但**更深层**仍可能出现 0 权边（HANDOVER 第 68 批的星形反例
`ρ = (1,1,3,0)`、`ε = 1` 给出 0 权内边 `t—t'`，穷举并列选择都躲不掉），那是**另一件事**，
不要把本文件的结论与那个反例混为一谈。

⚠️ **import 说明**：本文件用到的 `fin_cases` / `norm_num` 经 `Phylo.Buneman` 的 import **传递可用**，
故**刻意不额外 `import Mathlib.Tactic.*`** —— 那些 import 会给全库新增既有的
"module system" 警告（`lake` 打印，见 HANDOVER 纪律），能不加就不加。
-/

noncomputable section

namespace NJ

namespace Dissimilarity

/-- 星形度量的四条腿长：`ρ = (1, 1, 3, 0)`（**最后一条为 0 是关键**）。 -/
def starLeg : Fin 4 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 0

/-- 星形度量：`i ≠ j` 时 `val i j = ρ_i + ρ_j`，对角为 `0`。 -/
def starVal (i j : Fin 4) : ℝ := if i = j then 0 else starLeg i + starLeg j

theorem starVal_symm : ∀ i j, starVal i j = starVal j i := by
  intro i j
  unfold starVal
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬j = i := fun hh => h hh.symm
    simp [h, h', add_comm]

/-- **星形度量**（`ρ = (1,1,3,0)`）—— 后面的见证。 -/
def starWitness : Dissimilarity (Fin 4) where
  val := starVal
  symm := starVal_symm
  diag := by
    intro i
    unfold starVal
    simp

/-- 星形度量**正定**（`i ≠ j` 时 `val i j = ρ_i + ρ_j > 0`）。 -/
theorem starWitness_positiveDefinite : starWitness.PositiveDefinite := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;>
    (simp [starWitness, starVal, starLeg] at hxy ⊢; try norm_num at hxy)

/-- 星形度量满足**四点条件**（星形度量都是树度量：两条腿长的和）。 -/
theorem starWitness_fourPoint : starWitness.FourPoint := by
  intro i j k l
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [starWitness, starVal, starLeg] <;> norm_num

/-- ★★★ **收缩不保持正定**（阴性结论；`ρ = (1,1,3,0)` 星形见证）。

存在**正定**且满足**四点条件**的相异度 `δ`，使得 Buneman 收缩
`δ.shrinkDissimilarity p q r` **不正定**：

* `δ(3, 0) = 1`，`ρ(0;1,2) = ½(δ(0,1)+δ(0,2)−δ(1,2)) = ½(2+4−4) = 1`
  ⇒ `δ'(inl 3, inr()) = 1 − 1 = 0`；
* 而 `inl 3 ≠ inr ()` ⇒ 违反 `PositiveDefinite` 的定义。

⇒ 「正定性沿归纳步保持」是**死路**（`Phylo/Buneman.lean` 的装配因此只能要求 `FourPoint`）。 -/
theorem not_positiveDefinite_shrinkDissimilarity :
    ¬(∀ (δ : Dissimilarity (Fin 4)) (p q r : Fin 4),
        δ.PositiveDefinite → δ.FourPoint → (δ.shrinkDissimilarity p q r).PositiveDefinite) := by
  intro h
  have hbad := h starWitness 0 1 2 starWitness_positiveDefinite starWitness_fourPoint
  have hzero : (starWitness.shrinkDissimilarity 0 1 2).val
      (Sum.inl (⟨3, by decide⟩ : {x : Fin 4 // x ≠ 0 ∧ x ≠ 1})) (Sum.inr ()) = 0 := by
    change starWitness.shrinkVal 0 1 2
      (Sum.inl (⟨3, by decide⟩ : {x : Fin 4 // x ≠ 0 ∧ x ≠ 1})) (Sum.inr ()) = 0
    rw [shrinkVal_inl_inr]
    simp [starWitness, starVal, starLeg, rho]
  exact absurd (hbad _ _ hzero) (by simp)

end Dissimilarity

end NJ
