/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.TreeMetricDistribution

/-!
# `Phylo.Stat.QuartetMeanEquidistributed` —— label-invariant 分布下 quartet 距离的均值与分布无关

本文件把 `Phylo/Stat/TreeMetricDistribution.lean` 的**缺口**
`Phylo.MetricDist.quartetMeanEquidistributed_gap` **证成定理**（`def` 原文未改，缺口保持登记）。

## 结论（逐字对应缺口的陈述）

对任意有限叶集 `X`、任意 `k : ℕ` 与任意 resolution 表族 `𝒯 : Finset (QuartetRes X)`，
若**每个** 4-子集的**每个**小侧在 `𝒯` 中恰出现 `k` 次，则

```text
Σ_{r,r' ∈ 𝒯} quartetDistFull r r' = 48 · k² · C(n,4)        (C(n,4) = #{A : Finset X // A.card = 4})
```

归一化后即 `(2/3)·C(n,4)`（`|𝒯| = 6k`，故 `48k²C / (2·36k²) = (2/3)C`）。

文献：Steel & Penny 1993 第 **486–490** 行 Eq.(11)；Alon–Naves–Sudakov 2016 第 **341–353** 行
Prop 2.2 + Prop 2.3（第 **341–345** 行：随机重标号下每个 4-子集的配对小侧**等可能**）。

## 证明骨架（纯计数，不需要测度层 / 不需要新的 Mathlib 器材）

1. **换序**：`Σ_{r,r'}` 与 `Σ_A`（`A` 遍历 4-子集）交换（`Finset.sum_comm`）；
2. **固定 `A`**：由假设得每条纤维 `= k`，故 `𝒯.card = 6k`（`6 = C(4,2)` 个小侧，
   用 `Finset.card_eq_sum_card_fiberwise` + `Fintype.card_finset_len`）；
3. **固定 `r`**：与之「配对相同」的 `r'` 有 `k` 个、「配对互补」的又有 `k` 个
   （互补的基数仍为 `2`，且 `B ≠ Bᶜ`），故不一致者有 `6k − 2k` 个
   ⇒ 该 `r` 贡献 `2·(6k − 2k) = 8k`；
4. **汇总**：`6k · 8k = 48k²`，再乘 4-子集个数 `C(n,4)`。

⚠️ **退化情形**：`X` 不足 4 个元素时 4-子集类型为空，两边同为 `0`（不是空真：见 §3 的 ★B 见证）。
-/

namespace Phylo.MetricDist

open Finset

section Helpers

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- 4-子集类型（缺口陈述里反复出现的 `{A : Finset X // A.card = 4}`）。 -/
abbrev Quad (X : Type*) [Fintype X] [DecidableEq X] := {A : Finset X // A.card = 4}

/-- 固定 4-子集 `A` 上的「小侧」类型（`{B : Finset ↥A // B.card = 2}`）。 -/
abbrev Side (A : Finset X) := {B : Finset ↥A // B.card = 2}

/-! ## 1. 逐 4-子集分解 -/

/-- 固定 `A` 上的不一致项：配对相同或互补记 `0`，否则记 `2`（未归一化 quartet 距离的逐项分量）。 -/
def quadDiff (A : Quad X) (r r' : QuartetRes X) : ℕ :=
  if (r A).1 = (r' A).1 ∨ (r A).1 = (r' A).1ᶜ then 0 else 2

/-- `quartetDistFull` 就是逐 4-子集分量之和（定义展开，`rfl`）。 -/
theorem quartetDistFull_eq_sum_quadDiff (r r' : QuartetRes X) :
    quartetDistFull r r' = ∑ A : Quad X, quadDiff A r r' := rfl

/-! ## 2. 小侧的基数与互补 -/

/-- 4-元集上 2-元子集的**补集**仍是 2-元子集。 -/
theorem compl_card_two (A : Quad X) {B : Finset ↥A.1} (hB : B.card = 2) : (Bᶜ).card = 2 := by
  have h1 : Fintype.card ↥A.1 = 4 := by
    rw [Fintype.card_coe, A.2]
  rw [Finset.card_compl, h1, hB]

/-- ★ `B ≠ Bᶜ`：否则 `univ = B ∪ Bᶜ = B` 只会有 `2` 个元素，而 `↥A.1` 有 `4` 个。 -/
theorem ne_compl_of_card_two (A : Quad X) {B : Finset ↥A.1} (hB : B.card = 2) : B ≠ Bᶜ := by
  intro h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have hx' : x ∈ Bᶜ := h ▸ hx
  rw [Finset.mem_compl] at hx'
  exact hx' hx

/-- **6 个小侧**：`{B : Finset ↥A // B.card = 2}` 的基数是 `C(4,2) = 6`。 -/
theorem card_side_type (A : Quad X) : Fintype.card (Side A.1) = 6 := by
  have h1 : Fintype.card ↥A.1 = 4 := by
    rw [Fintype.card_coe, A.2]
  rw [Fintype.card_finset_len, h1]
  decide

/-! ## 3. 纤维基数与 `𝒯.card = 6k` -/

/-- 假设的等价形式：纤维按 `r ↦ r A` 计（把 `(r A).1 = B.1` 换成 `r A = B`）。 -/
theorem fiber_card {k : ℕ} {𝒯 : Finset (QuartetRes X)}
    (h : ∀ (A : Quad X) (B : Side A.1), (𝒯.filter fun r => (r A).1 = B.1).card = k)
    (A : Quad X) {B : Finset ↥A.1} (hB : B.card = 2) :
    (𝒯.filter fun r => (r A).1 = B).card = k :=
  h A ⟨B, hB⟩

/-- **`𝒯.card = 6k`**：按固定 4-子集 `A₀` 的 6 个小侧做纤维分解。 -/
theorem card_eq_six_mul {k : ℕ} {𝒯 : Finset (QuartetRes X)}
    (h : ∀ (A : Quad X) (B : Side A.1), (𝒯.filter fun r => (r A).1 = B.1).card = k)
    (A₀ : Quad X) : 𝒯.card = 6 * k := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun r : QuartetRes X => r A₀)
    (t := Finset.univ) (fun r _ => Finset.mem_univ (r A₀))]
  have hB : ∀ b : Side A₀.1, (𝒯.filter fun r => r A₀ = b).card = k := by
    intro b
    have hfil : (𝒯.filter fun r => r A₀ = b) = (𝒯.filter fun r => (r A₀).1 = b.1) :=
      Finset.filter_congr fun r _ => Subtype.ext_iff
    rw [hfil]
    exact fiber_card h A₀ (B := b.1) b.2
  rw [Finset.sum_congr rfl (fun b _ => hB b), Finset.sum_const,
    Finset.card_univ, card_side_type A₀, smul_eq_mul]

/-! ## 4. `Σ (if p then 0 else 2) = 2 · #(¬p 的纤维)` -/

/-- `{0,2}` 值求和的通用引理（`p` 为真的项贡献 `0`）。 -/
theorem sum_ite_zero_two {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (∑ x ∈ s, (if p x then 0 else 2)) = 2 * (s.filter fun x => ¬ p x).card := by
  have h1 : ∀ x, (if p x then (0 : ℕ) else 2) = 2 * (if p x then 0 else 1) := by
    intro x
    by_cases h : p x <;> simp [h]
  have h2 : ∀ x, (if p x then (0 : ℕ) else 1) = (if ¬ p x then 1 else 0) := by
    intro x
    by_cases h : p x <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.card_filter]

/-! ## 5. 固定 `A`：内层和 = `2 · (𝒯.card − 2k)` -/

/-- ★★ 固定 `r` 的内层和：与 `r` 配对相同或互补的 `r'` 各 `k` 个（且互斥），
故不一致者 `𝒯.card − 2k` 个，每个记 `2`。 -/
theorem inner_sum_quadDiff {k : ℕ} {𝒯 : Finset (QuartetRes X)}
    (h : ∀ (A : Quad X) (B : Side A.1), (𝒯.filter fun r => (r A).1 = B.1).card = k)
    (A : Quad X) (r : QuartetRes X) :
    (∑ r' ∈ 𝒯, quadDiff A r r') = 2 * (𝒯.card - 2 * k) := by
  have hc : ((r A).1ᶜ).card = 2 := compl_card_two A (r A).2
  have hp : (𝒯.filter fun r' => (r A).1 = (r' A).1).card = k := by
    have hfil : (𝒯.filter fun r' => (r A).1 = (r' A).1)
        = (𝒯.filter fun r' => (r' A).1 = (r A).1) :=
      Finset.filter_congr fun r' _ => eq_comm
    rw [hfil]
    exact fiber_card h A (r A).2
  have hq : (𝒯.filter fun r' => (r A).1 = (r' A).1ᶜ).card = k := by
    have hfil : (𝒯.filter fun r' => (r A).1 = (r' A).1ᶜ)
        = (𝒯.filter fun r' => (r' A).1 = ((r A).1)ᶜ) :=
      Finset.filter_congr fun r' _ => by
        constructor
        · intro h
          rw [h, compl_compl]
        · intro h
          rw [h, compl_compl]
    rw [hfil]
    exact fiber_card h A hc
  have hdisj : Disjoint (𝒯.filter fun r' => (r A).1 = (r' A).1)
      (𝒯.filter fun r' => (r A).1 = (r' A).1ᶜ) := by
    rw [Finset.disjoint_left]
    intro r' h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact ne_compl_of_card_two A (r' A).2 (h1.2.symm.trans h2.2)
  have hm : (𝒯.filter fun r' => ((r A).1 = (r' A).1 ∨ (r A).1 = (r' A).1ᶜ)).card = 2 * k := by
    rw [Finset.filter_or, Finset.card_union_of_disjoint hdisj, hp, hq]
    ring
  have hmain : (∑ r' ∈ 𝒯, quadDiff A r r')
      = 2 * ((𝒯.filter fun r' => ¬ ((r A).1 = (r' A).1 ∨ (r A).1 = (r' A).1ᶜ)).card) :=
    sum_ite_zero_two 𝒯 _
  rw [hmain]
  have hsplit := Finset.card_filter_add_card_filter_not (s := 𝒯)
    (p := fun r' => ((r A).1 = (r' A).1 ∨ (r A).1 = (r' A).1ᶜ))
  rw [hm] at hsplit
  have : (𝒯.filter fun r' => ¬ ((r A).1 = (r' A).1 ∨ (r A).1 = (r' A).1ᶜ)).card
      = 𝒯.card - 2 * k := by omega
  rw [this]

/-! ## 6. 固定 `A`：贡献 `48k²` -/

/-- ★★★ 固定 4-子集的贡献：`48·k²`（`𝒯.card = 6k` 时，`6k · 8k = 48k²`）。 -/
theorem sum_quadDiff_eq {k : ℕ} {𝒯 : Finset (QuartetRes X)}
    (h : ∀ (A : Quad X) (B : Side A.1), (𝒯.filter fun r => (r A).1 = B.1).card = k)
    (hcard : 𝒯.card = 6 * k) (A : Quad X) :
    (∑ r ∈ 𝒯, ∑ r' ∈ 𝒯, quadDiff A r r') = 48 * k ^ 2 := by
  rw [Finset.sum_congr rfl (fun r _ => inner_sum_quadDiff h A r)]
  rw [Finset.sum_const, hcard, smul_eq_mul]
  have h2 : 6 * k - 2 * k = 4 * k := by omega
  rw [h2]
  ring

end Helpers

/-! ## 7. 主定理（逐字证掉缺口） -/

/-- ★★★ **缺口 `quartetMeanEquidistributed_gap` 成真定理**：

label-invariant（每个 4-子集的每个小侧等可能）的分布下，quartet 距离的**总均值与分布无关**，
等于 `48·k²·C(n,4)`（归一化 `(2/3)·C(n,4)`）。

证明：换序 + 纤维计数（见文件头骨架；`6` 个小侧、`3` 个互补类、每类 `k` 次）。 -/
theorem quartetMeanEquidistributed (X : Type) [Fintype X] [DecidableEq X] (k : ℕ)
    (𝒯 : Finset (QuartetRes X))
    (h : ∀ (A : {A : Finset X // A.card = 4}) (B : {B : Finset ↥A.1 // B.card = 2}),
      (𝒯.filter fun r => (r A).1 = B.1).card = k) :
    (∑ r ∈ 𝒯, ∑ r' ∈ 𝒯, quartetDistFull r r')
      = 48 * k ^ 2 * Fintype.card {A : Finset X // A.card = 4} := by
  by_cases hempty : Fintype.card {A : Finset X // A.card = 4} = 0
  · have huniv : (Finset.univ : Finset {A : Finset X // A.card = 4}) = ∅ :=
      Finset.univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp hempty)
    have hz : ∀ r r' : QuartetRes X, quartetDistFull r r' = 0 := by
      intro r r'
      rw [quartetDistFull_eq_sum_quadDiff, huniv, Finset.sum_empty]
    rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => hz r r')), hempty,
      mul_zero]
    simp
  · obtain ⟨A₀⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hempty)
    have hcard : 𝒯.card = 6 * k := card_eq_six_mul h A₀
    calc (∑ r ∈ 𝒯, ∑ r' ∈ 𝒯, quartetDistFull r r')
        = ∑ A : {A : Finset X // A.card = 4}, ∑ r ∈ 𝒯, ∑ r' ∈ 𝒯, quadDiff A r r' := by
          rw [Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
            (fun r' _ => quartetDistFull_eq_sum_quadDiff r r'))]
          rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm), Finset.sum_comm]
      _ = ∑ _A : {A : Finset X // A.card = 4}, 48 * k ^ 2 :=
          Finset.sum_congr rfl fun A _ => sum_quadDiff_eq h hcard A
      _ = 48 * k ^ 2 * Fintype.card {A : Finset X // A.card = 4} := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring

/-- ★★★ 缺口**收口**：缺口陈述（`def`，原文未改）本身已被证明。 -/
theorem quartetMeanEquidistributed_gap_holds : quartetMeanEquidistributed_gap :=
  quartetMeanEquidistributed

/-! ## 8. ★B 反空真见证 / ★C 最小例子 -/

/-- ★B（i）**退化情形可用**（不是空真）：`X = Fin 3` 时 4-子集类型为空，
主定理给出两边同为 `0`（`C(3,4) = 0`）。 -/
example : (∑ r ∈ (Finset.univ : Finset (QuartetRes (Fin 3))),
    ∑ r' ∈ (Finset.univ : Finset (QuartetRes (Fin 3))), quartetDistFull r r') = 0 := by
  have h := quartetMeanEquidistributed (Fin 3) 7 (Finset.univ : Finset (QuartetRes (Fin 3)))
    (fun A _ => absurd A.2 (by
      have h3 : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
      have hle := Finset.card_le_univ A.1
      omega))
  rw [h, Fintype.card_finset_len]
  decide

/-- ★B（ii）**非退化取值**：`n = 4`、`k = 1` 时结论右边 `= 48`（与
`scripts/msc/w12d_counterexamples.py` §[3] 的精确计数一致：6 张表两两比较，一致 12 对、不同 24 对）。 -/
example : 48 * 1 ^ 2 * Fintype.card {A : Finset (Fin 4) // A.card = 4} = 48 := by
  rw [Fintype.card_finset_len]
  decide

/-! ## 9. 与脚本 `scripts/msc/w12d_counterexamples.py` 的对应

| 量 | 脚本（精确有理数穷举） | 本文件 |
|---|---|---|
| `n = 4`，6 张去重表，`k = 1` | `Σ qd = 48 = 48·1²·1` | ★B（ii）右端 `48` |
| `n = 5`，30 张重标号表，`k = 5` | `Σ qd = 6000 = 48·25·5` | 同一定理（`∀ X`）|
| 每个 4-子集的 6 个小侧各 `k` 次 | 脚本逐一核过 | 缺口假设（定理前提）| -/

end Phylo.MetricDist
