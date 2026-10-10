/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.KingmanCoalescent
import Phylo.Stat.KingmanJumpChain
import Phylo.Stat.KingmanStep

/-!
# `Phylo.Stat.KingmanLaw` —— 把 **跳链律** 与 **逗留时间律** 接成 Theorem 1

W10a（`Phylo/Stat/KingmanJumpChain.lean`，K82 (2.1)/(2.2) 的组合核）与
W10b（`Phylo/Stat/KingmanCoalescent.lean`，K82 (1.7) 与 **Theorem 1**）是**互相解耦**做的：
W10b 把联合律写成对**任意**跳链测度 `μ` 都成立的参数形式
`nCoalescentLaw μ n = μ.prod (sojournJointLaw n)`。
**本文件把参数 `μ` 实例化成 (2.2) 给出的跳链律** —— 于是 Theorem 1 的
「**跳链 ⊗ 独立指数**」在**具体对象**上闭合。

## W10 第二步（2026-10-09）：**一次合并的去向计数** 与 **层间一致性的测度层**

* ★★★ `mergeTargets_gap`（**已证，不再是缺口**）：从 `k+1` 块划分 `Q` 出发，一次合并的
  **去向**恰 `C(k+1,2)` 个 —— 这就是 (2.1) 的**正向**语句（「每步在 `C(k+1,2)` 个去向里
  均匀挑一个」）。证法是**纤维求和**：把 `offDiag Q.1.parts`（有序块对）按
  `p ↦ mergeOf (Q.1,p)` 分纤维，每根纤维恰 `2` 个元素（`card_pairSet`），故
  `2·#{去向} = |offDiag Q.1.parts| = (k+1)k`，再由纯 `Nat` 算术（`Nat.div_eq_of_lt_le` ＋
  `Nat.choose_two_right`）得 `#{去向} = C(k+1,2)`。**全程结构路线，不枚举。**
* ★ `jumpStepLaw`（**已定义**，题目指定的形状）与它的「显式权重」版本 `pairMeasure`；
  以及左边缘的核心算术 `sum_targets_jumpWeight`（每个 `Q` 的 `C(k+1,2)` 个去向各分
  `w(Q)/C(k+1,2)`，加起来恰为 `w(Q)`）。

## K82 的原文（Theorem 1，第 210–215 行）

> In an n-coalescent, the death process `(D_t ; t ≥ 0)` and the jump chain
> `(S_k ; k = n, n−1, …, 1)` are **independent**, and `R_t = S_{D_t}` for all `t ≥ 0`.

## 本文件的形式化口径（**措辞纪律：写清做到了哪一层**）

* **已做**：对**每一个层 `k`**，跳链在 `k` 块上的**边缘律** `jumpMeasure n k`
  （**由 (2.2) 的绝对概率 `jumpWeight` / `partitionProb` 构造**，`IsProbabilityMeasure` **已证**）
  与逗留时间向量 `sojournJointLaw n`（K82 (1.11) 的独立指数乘积）拼成乘积测度，
  并用 **真 `IndepFun`** 证明两者独立（不是「联合律 = 乘积」的代用语）。
* **已做**：**一次合并的去向计数** `mergeTargets_gap`（(2.1) 的正向语句）。
* **部分做**：**层间一致性的测度层形式** —— 一步联合律 `jumpStepLaw` 已定义，
  左边缘的**逐点算术**（`sum_targets_jumpWeight` / `sum_mergeTargets_jumpWeight`）已证；
  但 `jumpStepLaw` 的**两个边缘等式本身**与本文件末尾的 `jumpMeasure_step_gap` **仍未证**
  （如实记为缺口，见诚实边界表）。
* **未做**：把「**整条**跳链 `(S_n, S_{n−1}, …, S_1)`」作为**轨迹空间**上的对象；
  以及 `R_t = S_{D_t}` 这一**过程恒等式**（需要连续时间的 `D_t`，本库没有）。
-/

noncomputable section

open Classical MeasureTheory

namespace Phylo.Stat.KingmanLaw

-- `Measure.pi` / `Measure.prod` 的概率性必须从「因子是概率测度」的实例取，
-- 而 `haveI` 对 `Prop` 会触发 `linter.style.haveILetI`（告警会破坏「0 字节」判据）。
-- 库内已有先例（`PhylogramContract.lean`、`SplitsDetermineTree.lean`）。
set_option linter.style.haveILetI false

open Phylo.Stat.KingmanJumpChain (PartK Part jumpWeight jumpWeight_nonneg jumpWeight_sum_eq_one
  MergeInto mergeOf mergeOf_eq mergePart card_mergePart offDiag mem_offDiag card_offDiag pairSet
  mem_pairSet card_pairSet partitionProb partitionProb_merge_recursion)
open Phylo.Stat.KingmanCoalescent (nCoalescentLaw sojournJointLaw indepFun_fst_snd_nCoalescent
  isProbabilityMeasure_nCoalescentLaw fst_nCoalescentLaw snd_nCoalescentLaw)

/-- `PartK n k`（`k` 块划分）是**有限**类型，取**离散**可测空间 `⊤`。

（`Subtype.instMeasurableSpace` 那条通用路径要求 `MeasurableSpace (Part n)`，而 `Part n` 上
没有可测空间实例，故这里直接给出 —— 它只服务于本文件的测度构造。） -/
instance instMeasurableSpacePartK (n k : ℕ) : MeasurableSpace (PartK n k) := ⊤

/-- ★★★ **跳链在 `k` 层上的概率测度**：把 (2.2) 的绝对概率（= `jumpWeight` = `partitionProb`）
当成点质量权重，在有限类型 `PartK n k` 上求和。 -/
noncomputable def jumpMeasure (n k : ℕ) : Measure (PartK n k) :=
  Measure.sum fun P => ENNReal.ofReal (jumpWeight n k P) • Measure.dirac P

/-- `jumpMeasure` 在任意集合上的取值（有限和）。 -/
theorem jumpMeasure_apply (n k : ℕ) (s : Set (PartK n k)) :
    jumpMeasure n k s
      = ∑ P : PartK n k, ENNReal.ofReal (jumpWeight n k P) * (Measure.dirac P : Measure (PartK n k)) s := by
  rw [jumpMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  exact Finset.sum_congr rfl fun P _ => by rw [Measure.smul_apply, smul_eq_mul]

/-- ★★★ **它是概率测度**（由 (2.2) 的归一化 `jumpWeight_sum_eq_one`）。 -/
theorem isProbabilityMeasure_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    IsProbabilityMeasure (jumpMeasure n k) := by
  refine ⟨?_⟩
  rw [jumpMeasure_apply]
  have h1 : ∀ P : PartK n k, (Measure.dirac P : Measure (PartK n k)) Set.univ = 1 :=
    fun P => Measure.dirac_apply_of_mem (Set.mem_univ P)
  rw [Finset.sum_congr rfl (fun P _ => by rw [h1 P, mul_one])]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun P _ => jumpWeight_nonneg n k P)]
  rw [jumpWeight_sum_eq_one n k hk0 hkn, ENNReal.ofReal_one]

/-- ★★★ **Theorem 1（分层形式）**：跳链在 `k` 层的状态与 `n−1` 个逗留时间**独立**。

K82 Theorem 1 说**整条**跳链与死亡过程独立；本定理是它在**每个层 `k`** 上的实例 ——
两半都是**具体对象**：左边是 (2.2) 给出的跳链律 `jumpMeasure n k`，
右边是 (1.11) 的独立指数乘积 `sojournJointLaw n`。 -/
theorem indepFun_jumpChain_sojourn (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) (hn : 2 ≤ n) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (nCoalescentLaw (jumpMeasure n k) n) := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact indepFun_fst_snd_nCoalescent (jumpMeasure n k) hn

/-- ★★ **联合律的两个边缘**：第一个是跳链律，第二个是独立指数乘积。
（第一边缘**不需要** `IsProbabilityMeasure`，见 `fst_nCoalescentLaw`。） -/
theorem fst_nCoalescentLaw_jumpMeasure (n k : ℕ) (_hk0 : 1 ≤ k) (_hkn : k ≤ n) (hn : 2 ≤ n) :
    (nCoalescentLaw (jumpMeasure n k) n).fst = jumpMeasure n k :=
  fst_nCoalescentLaw (jumpMeasure n k) (n := n) hn

theorem snd_nCoalescentLaw_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) (hn : 2 ≤ n) :
    (nCoalescentLaw (jumpMeasure n k) n).snd = sojournJointLaw n := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact snd_nCoalescentLaw (jumpMeasure n k) (n := n) hn

/-- ★★★ **n-溯祖的联合律是概率测度**（(2.2) 的跳链律 ⊗ (1.11) 的独立指数）。 -/
theorem isProbabilityMeasure_nCoalescentLaw_jumpMeasure (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n)
    (hn : 2 ≤ n) : IsProbabilityMeasure (nCoalescentLaw (jumpMeasure n k) n) := by
  haveI := isProbabilityMeasure_jumpMeasure n k hk0 hkn
  exact isProbabilityMeasure_nCoalescentLaw (jumpMeasure n k) hn

/-! ## 一次合并的**去向计数**（(2.1) 的正向语句）—— **已证**

计数路线（**纤维求和**，全程结构路线、不枚举）：

1. `s := offDiag Q.1.parts`：`Q` 的**有序**块对，`|s| = |Q|(|Q|−1)`（`card_offDiag`）；
2. 按 `p ↦ mergeOf (Q.1,p)` 把 `s` 分纤维，纤维落在
   `t := {P : Part n // P.parts.card = k ∧ MergeInto Q.1 P}` 里
   （块数用 `card_mergePart`，`MergeInto` 用 `mergeOf_eq` 直接构造）；
3. 每根纤维 = `pairSet Q.1 P`，基数恰 `2`（`card_pairSet`）；
4. `Finset.card_eq_sum_card_fiberwise` ⇒ `|s| = Σ_{P∈t} 2 = 2·|t|`；
5. `card_offDiag` ＋ `Q.2` ⇒ `2·|t| = (k+1)k`；纯 `Nat` 算术 ⇒ `|t| = C(k+1,2)`；
6. `PartK` 与 `Part` 的计数一一对应（`Finset.card_bij`）。 -/

/-- 纯 `Nat` 算术：`(m+1)·(m+1−1) = 2t ⟹ t = C(m+1,2)`。 -/
theorem choose_two_of_two_mul {m t : ℕ} (h : (m + 1) * (m + 1 - 1) = t * 2) :
    t = (m + 1).choose 2 := by
  have hm : m + 1 - 1 = m := by omega
  have h2 : m * (m + 1) = t * 2 := by
    rw [mul_comm m (m + 1), ← hm]
    exact h
  have hlt : (m + 1) * m < (t + 1) * 2 := by
    rw [mul_comm (m + 1) m, h2]
    omega
  have hle : t * 2 ≤ (m + 1) * m := by
    rw [mul_comm (m + 1) m, h2]
  have hdiv : (m + 1) * m / 2 = t := Nat.div_eq_of_lt_le (k := t) hle hlt
  rw [Nat.choose_two_right, hm]
  exact hdiv.symm

/-- ★★★ **`mergeTargets_gap`（已证）**：`Q : PartK n (k+1)` 的一步去向恰 `C(k+1,2)` 个。

这是 (2.1) 的**正向**语句，也是「跳链每步均匀挑一个块对」的**计数依据**。 -/
theorem mergeTargets_gap (n k : ℕ) (hk0 : 1 ≤ k) (Q : PartK n (k + 1)) :
    ((Finset.univ.filter (fun P : PartK n k => MergeInto Q.1 P.1)).card) = (k + 1).choose 2 := by
  classical
  have hcard : Q.1.parts.card = k + 1 := Q.2
  set s : Finset (Finset (Fin n) × Finset (Fin n)) := offDiag Q.1.parts with hs
  set t : Finset (Part n) :=
    Finset.univ.filter (fun P : Part n => P.parts.card = k ∧ MergeInto Q.1 P) with ht
  have hmem_t : ∀ p ∈ s, mergeOf (Q.1, p) ∈ t := by
    intro p hp
    have hp' := mem_offDiag.mp (hs ▸ hp)
    have h3 : mergeOf (Q.1, p) = mergePart Q.1 p.1 p.2 hp'.1 hp'.2.1 hp'.2.2 :=
      mergeOf_eq Q.1 p.1 p.2 hp'.1 hp'.2.1 hp'.2.2
    have hcard' : (mergePart Q.1 p.1 p.2 hp'.1 hp'.2.1 hp'.2.2).parts.card = k := by
      rw [card_mergePart Q.1 p.1 p.2 hp'.1 hp'.2.1 hp'.2.2, hcard]
      omega
    have hM : MergeInto Q.1 (mergeOf (Q.1, p)) :=
      ⟨p.1, p.2, hp'.1, hp'.2.1, hp'.2.2, by rw [h3]⟩
    have hcard'' : (mergeOf (Q.1, p)).parts.card = k := by rw [h3]; exact hcard'
    rw [ht, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcard'', hM⟩
  have hmaps : Set.MapsTo (fun p : Finset (Fin n) × Finset (Fin n) => mergeOf (Q.1, p)) ↑s ↑t :=
    fun p hp => hmem_t p hp
  have hkey := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ P ∈ t,
      ({p ∈ s | mergeOf (Q.1, p) = P} : Finset (Finset (Fin n) × Finset (Fin n))).card = 2 := by
    intro P hPt
    have hP := (Finset.mem_filter.mp (ht ▸ hPt)).2.2
    have hset : ({p ∈ s | mergeOf (Q.1, p) = P} : Finset _) = pairSet Q.1 P := by
      ext p
      exact Iff.rfl
    rw [hset, card_pairSet]
    simp only [hP, ↓reduceIte]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, card_offDiag, hcard] at hkey
  rw [nsmul_eq_mul] at hkey
  have htgt : ((Finset.univ.filter (fun P : PartK n k => MergeInto Q.1 P.1)).card) = t.card := by
    refine Finset.card_bij (fun (P : PartK n k) _ => (P.1 : Part n)) ?_ ?_ ?_
    · intro P hP
      have hP' := (Finset.mem_filter.mp hP).2
      rw [ht, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, P.2, hP'⟩
    · intro P _ R _ h
      exact Subtype.ext h
    · intro P hP
      have hP' := Finset.mem_filter.mp (ht ▸ hP)
      exact ⟨⟨P, hP'.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'.2.2⟩, rfl⟩
  have hm : t.card = (k + 1).choose 2 := by
    apply choose_two_of_two_mul
    exact hkey
  rw [htgt, hm]

/-- ★★ **`Q` 的 `C(k+1,2)` 个去向上的均匀权重加起来 = `Q` 的质量**
（一步联合律**左边缘**的核心算术）。 -/
theorem sum_targets_jumpWeight (n k : ℕ) (hk0 : 1 ≤ k) (Q : PartK n (k + 1)) :
    (∑ _P ∈ (Finset.univ.filter (fun P : PartK n k => MergeInto Q.1 P.1)),
        (((k + 1).choose 2 : ℕ) : ℝ)⁻¹ * jumpWeight n (k + 1) Q)
      = jumpWeight n (k + 1) Q := by
  rw [Finset.sum_const, nsmul_eq_mul, mergeTargets_gap n k hk0 Q]
  have hne : (((k + 1).choose 2 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (k + 1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  field_simp

/-! ## 层间一致性的**测度层**：一步联合律

一步联合律的构造：先按 (2.2) 在 `k+1` 层抽 `Q`（权重 `jumpWeight n (k+1) Q`），
再在 `Q` 的 `C(k+1,2)` 个**去向**里**均匀**挑一个（每个权重 `C(k+1,2)⁻¹`），得 `(Q,P)`。 -/

/-- ★★★ **一步联合律的「显式权重」形式**：每个 `(Q,P)` 的质量是
`jumpWeight n (k+1) Q / C(k+1,2)`（**不做** `MergeInto` 判定，判定可另加）。 -/
noncomputable def pairMeasure (n k : ℕ) : Measure (PartK n (k + 1) × PartK n k) :=
  Measure.sum fun x : PartK n (k + 1) × PartK n k =>
    ENNReal.ofReal (jumpWeight n (k + 1) x.1 * (((k + 1).choose 2 : ℕ) : ℝ)⁻¹) •
      Measure.dirac x

/-- ★★★ **一步联合律**（题目指定的形状）：只有 `MergeInto x.1.1 x.2.1` 的点有质量
`jumpWeight n (k+1) x.1 / C(k+1,2)`。 -/
noncomputable def jumpStepLaw (n k : ℕ) : Measure (PartK n (k + 1) × PartK n k) :=
  Measure.sum fun x : PartK n (k + 1) × PartK n k =>
    if MergeInto x.1.1 x.2.1 then
      ENNReal.ofReal (jumpWeight n (k + 1) x.1 * (((k + 1).choose 2 : ℕ) : ℝ)⁻¹) •
        Measure.dirac x
    else 0

/-- `pairMeasure` 在任意集合上的取值（有限和）。 -/
theorem pairMeasure_apply (n k : ℕ) (s : Set (PartK n (k + 1) × PartK n k)) :
    pairMeasure n k s = ∑ x : PartK n (k + 1) × PartK n k,
      ENNReal.ofReal (jumpWeight n (k + 1) x.1 * (((k + 1).choose 2 : ℕ) : ℝ)⁻¹) *
        (Measure.dirac x : Measure (PartK n (k + 1) × PartK n k)) s := by
  rw [pairMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  exact Finset.sum_congr rfl fun x _ => by rw [Measure.smul_apply, smul_eq_mul]

/-- **单点的 `jumpMeasure` 值**。 -/
theorem jumpMeasure_singleton (n k : ℕ) (Q : PartK n k) :
    jumpMeasure n k {Q} = ENNReal.ofReal (jumpWeight n k Q) := by
  rw [jumpMeasure, Measure.sum_apply_of_countable, tsum_fintype]
  rw [Finset.sum_eq_single Q]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_singleton Q), mul_one]
  · intro b _ hb
    rw [Measure.smul_apply, Measure.dirac_apply,
      Set.indicator_of_notMem (by simpa [Set.mem_singleton_iff] using hb), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ Q) h

/-! ## W11g2：把**一步联合律**的两个边缘从「逐点算术」搬成「测度等式」

前人的 `W11g_Probe/W11gIso.lean` 已把**全部逐点算术**打通；本节把簿记补齐：

1. **逐点**：`ite_smul_apply` ＋ `step_term_left` ⇒ `hterm`（`Measure.sum` 的每一项）；
2. **内层**：`inner_merge_filter` ⇒ `inner_sum_left`（固定 `Q`，对去向求和）；
3. **外层**：`Finset.sum_product` ＋ `inner_ite_pull`，最后把
   `∑_{Q ∈ univ.filter (· ∈ S)}` 与 `∑_{Q ∈ S}` **两种记法对齐**（`Finset.sum_filter` ＋ 指标集合相同）
   才能用 `Finset.sum_congr rfl` 收口 —— 这正是前人卡住的那一步。
-/

open Phylo.Stat.KingmanStep (targets card_mergeTargets_cast sum_parents_partitionProb)

/-- `(if p then c • μ else 0) s = if p then c * μ s else 0`（本库**无** `Measure.zero_apply`）。 -/
theorem ite_smul_apply {δ : Type*} [MeasurableSpace δ] (p : Prop) [Decidable p]
    (c : ENNReal) (μ : Measure δ) (s : Set δ) :
    ((if p then c • μ else 0) : Measure δ) s = (if p then c * μ s else 0) := by
  by_cases h : p
  · rw [ite_eq_left h, ite_eq_left h, Measure.smul_apply, smul_eq_mul]
  · rw [ite_eq_right h, ite_eq_right h, Measure.coe_zero, Pi.zero_apply]

/-- 单点质量在 `↑S ×ˢ univ` 上的取值。 -/
theorem dirac_prod_univ_left (n k : ℕ) (S : Finset (PartK n (k+1))) (Q : PartK n (k+1))
    (y : PartK n k) :
    (Measure.dirac (Q, y) : Measure (PartK n (k+1) × PartK n k))
        (↑S ×ˢ (Set.univ : Set (PartK n k))) = if Q ∈ S then 1 else 0 := by
  by_cases hQ : Q ∈ S
  · rw [ite_eq_left hQ, Measure.dirac_apply_of_mem (show (Q, y) ∈ (↑S ×ˢ (Set.univ : Set (PartK n k)))
      from Set.mem_prod.mpr ⟨hQ, Set.mem_univ _⟩)]
  · rw [ite_eq_right hQ, Measure.dirac_apply]
    exact Set.indicator_of_notMem (by
      intro hx
      exact hQ (Set.mem_prod.mp hx).1) (1 : PartK n (k+1) × PartK n k → ENNReal)

/-- 单项 `p` 在 `↑S ×ˢ univ` 上的取值（`smul` ＋ `dirac`）。 -/
theorem step_term_left (n k : ℕ) (S : Finset (PartK n (k+1))) (p : PartK n (k+1) × PartK n k) :
    ((ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) •
        (Measure.dirac p : Measure (PartK n (k+1) × PartK n k))) :
        Measure (PartK n (k+1) × PartK n k)) (↑S ×ˢ (Set.univ : Set (PartK n k)))
      = ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) *
          (if p.1 ∈ S then 1 else 0) := by
  rw [Measure.smul_apply, smul_eq_mul, dirac_prod_univ_left n k S p.1 p.2, mul_comm]

/-- ★ 固定 `Q`：`C(k+1,2)` 个去向各分 `w(Q)/C(k+1,2)`，加起来 = `w(Q)`（**`ENNReal` 口径**）。 -/
theorem sum_targets_jumpWeight_enn (n k : ℕ) (hk0 : 1 ≤ k) (Q : PartK n (k+1)) :
    (∑ _y ∈ targets n k Q,
        ENNReal.ofReal (jumpWeight n (k+1) Q * (((k+1).choose 2 : ℕ) : ℝ)⁻¹))
      = ENNReal.ofReal (jumpWeight n (k+1) Q) := by
  have hne : (((k+1).choose 2 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (k+1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [show (((targets n k Q).card : ℕ) : ENNReal) =
      ENNReal.ofReal (((targets n k Q).card : ℝ)) from (ENNReal.ofReal_natCast _).symm]
  rw [card_mergeTargets_cast (n := n) (k := k) Q]
  rw [← ENNReal.ofReal_mul (Nat.cast_nonneg ((k+1).choose 2))]
  rw [show ((((k+1).choose 2 : ℕ) : ℝ)) * (jumpWeight n (k+1) Q * (((k+1).choose 2 : ℕ) : ℝ)⁻¹)
      = jumpWeight n (k+1) Q from by
    rw [mul_comm (jumpWeight n (k+1) Q)]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]]

/-- ★ 内层：把 `if MergeInto` 换成「对去向集合求和」。 -/
theorem inner_merge_filter (n k : ℕ) (Q : PartK n (k+1)) (a : ENNReal) :
    (∑ y ∈ (Finset.univ : Finset (PartK n k)),
        (if MergeInto Q.1 y.1 then a else 0))
      = ∑ _y ∈ targets n k Q, a := by
  rw [show (∑ y ∈ (Finset.univ : Finset (PartK n k)),
        (if MergeInto Q.1 y.1 then a else 0))
      = (∑ y ∈ (Finset.univ : Finset (PartK n k)).filter (fun y => MergeInto Q.1 y.1), a) from
    (Finset.sum_filter (fun y : PartK n k => MergeInto Q.1 y.1) (fun _ => a)).symm]
  rw [show (Finset.univ.filter (fun y : PartK n k => MergeInto Q.1 y.1)) = targets n k Q
      from rfl]

/-- ★ 内层（固定 `p`）：把 `(if p ∈ S …)` 提出 `∑_y`。 -/
theorem inner_ite_pull (n k : ℕ) (S : Finset (PartK n (k+1))) (p : PartK n (k+1)) :
    (∑ y ∈ (Finset.univ : Finset (PartK n k)),
        (if MergeInto p.1 y.1 then
          ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) *
            (if p ∈ S then 1 else 0) else 0))
      = (if p ∈ S then
          (∑ y ∈ (Finset.univ : Finset (PartK n k)),
            (if MergeInto p.1 y.1 then
              ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) else 0))
        else 0) := by
  by_cases hp : p ∈ S
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact Finset.sum_congr rfl (fun y _ => by
      by_cases hM : MergeInto p.1 y.1
      · rw [ite_eq_left hM, ite_eq_left hM, mul_one]
      · rw [ite_eq_right hM, ite_eq_right hM])
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact Finset.sum_eq_zero (fun y _ => by
      by_cases hM : MergeInto p.1 y.1
      · rw [ite_eq_left hM, mul_zero]
      · rw [ite_eq_right hM])

/-- ★ 内层（固定 `p`）：`∑_y (if MergeInto p y then A else 0) = ofReal (w p)`。 -/
theorem inner_sum_left (n k : ℕ) (hk0 : 1 ≤ k) (p : PartK n (k+1)) :
    (∑ y ∈ (Finset.univ : Finset (PartK n k)),
        (if MergeInto p.1 y.1 then
          ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) else 0))
      = ENNReal.ofReal (jumpWeight n (k+1) p) := by
  rw [inner_merge_filter n k p
    (ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹))]
  exact sum_targets_jumpWeight_enn n k hk0 p

/-- ★★★ **左边缘（有限矩形形式）**：`jumpStepLaw n k (↑S ×ˢ univ) = Σ_{Q ∈ S} w(Q)`。

（这是 `(jumpStepLaw n k).fst = jumpMeasure n (k+1)` 的**唯一**内容：
后者由 `Measure.ext_of_singleton` 把 `S` 取单点集即得。） -/
theorem jumpStepLaw_fst_finset (n k : ℕ) (hk0 : 1 ≤ k)
    (S : Finset (PartK n (k + 1))) :
    jumpStepLaw n k (↑S ×ˢ Set.univ) = ∑ Q ∈ S, ENNReal.ofReal (jumpWeight n (k + 1) Q) := by
  have hfg : (jumpStepLaw n k : Measure (PartK n (k+1) × PartK n k))
      = Measure.sum (fun x : PartK n (k+1) × PartK n k =>
          (if MergeInto x.1.1 x.2.1 then
            ENNReal.ofReal (jumpWeight n (k+1) x.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) •
              (Measure.dirac x : Measure (PartK n (k+1) × PartK n k)) else 0)) := by
    rw [jumpStepLaw]
  have hterm : ∀ p : PartK n (k+1) × PartK n k,
      ((if MergeInto p.1.1 p.2.1 then
          ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) •
            (Measure.dirac p : Measure (PartK n (k+1) × PartK n k)) else 0) :
          Measure (PartK n (k+1) × PartK n k)) (↑S ×ˢ (Set.univ : Set (PartK n k)))
        = (if MergeInto p.1.1 p.2.1 then
            ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) *
              (if p.1 ∈ S then 1 else 0) else 0) := by
    intro p
    rw [ite_smul_apply]
    by_cases hM : MergeInto p.1.1 p.2.1
    · rw [ite_eq_left hM, ite_eq_left hM]
      exact step_term_left n k S p
    · rw [ite_eq_right hM, ite_eq_right hM]
  rw [hfg, Measure.sum_apply_of_countable, tsum_fintype,
    show (Finset.univ : Finset (PartK n (k+1) × PartK n k))
      = (Finset.univ : Finset (PartK n (k+1))) ×ˢ (Finset.univ : Finset (PartK n k)) from
    Finset.univ_product_univ.symm]
  rw [show (∑ p ∈ (Finset.univ : Finset (PartK n (k+1))) ×ˢ (Finset.univ : Finset (PartK n k)),
        ((if MergeInto p.1.1 p.2.1 then
          ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) •
            (Measure.dirac p : Measure (PartK n (k+1) × PartK n k)) else 0) :
          Measure (PartK n (k+1) × PartK n k)) (↑S ×ˢ (Set.univ : Set (PartK n k))))
      = ∑ p ∈ (Finset.univ : Finset (PartK n (k+1))) ×ˢ (Finset.univ : Finset (PartK n k)),
        (if MergeInto p.1.1 p.2.1 then
          ENNReal.ofReal (jumpWeight n (k+1) p.1 * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) *
            (if p.1 ∈ S then 1 else 0) else 0)
      from Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_product]
  rw [show (∑ p ∈ (Finset.univ : Finset (PartK n (k+1))),
        ∑ y ∈ (Finset.univ : Finset (PartK n k)),
          (if MergeInto p.1 y.1 then
            ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) *
              (if p ∈ S then 1 else 0) else 0))
      = ∑ p ∈ (Finset.univ : Finset (PartK n (k+1))),
          (if p ∈ S then
            (∑ y ∈ (Finset.univ : Finset (PartK n k)),
              (if MergeInto p.1 y.1 then
                ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) else 0))
          else 0)
      from Finset.sum_congr rfl (fun p _ => inner_ite_pull n k S p)]
  -- ★ 卡点收口：两侧记法不同（`S` vs `univ.filter (· ∈ S)`），先**统一记法**再 `sum_congr`。
  have hfilter : (Finset.univ.filter (fun Q : PartK n (k+1) => Q ∈ S)) = S := by
    ext Q
    simp
  rw [show (∑ p ∈ (Finset.univ : Finset (PartK n (k+1))),
        (if p ∈ S then
          (∑ y ∈ (Finset.univ : Finset (PartK n k)),
            (if MergeInto p.1 y.1 then
              ENNReal.ofReal (jumpWeight n (k+1) p * (((k+1).choose 2 : ℕ) : ℝ)⁻¹) else 0))
        else 0))
      = ∑ Q ∈ S, ENNReal.ofReal (jumpWeight n (k+1) Q) from by
    rw [← Finset.sum_filter, hfilter]
    exact Finset.sum_congr rfl (fun Q _ => inner_sum_left n k hk0 Q)]

/-! ## 仍是缺口的：一步联合律的**两个边缘等式**（精确记为可检查的 `Prop`）

下面的 `jumpMeasure_step_gap` **未证**。它的**全部算术内容已在本文件证出**：

* 左边缘：`sum_targets_jumpWeight`（每个 `Q` 的 `C(k+1,2)` 个去向各分 `w(Q)/C(k+1,2)`，
  加起来 = `w(Q)`）—— 也就是 `Measure.sum` 在 `Prod.fst` 下的推前；
* 右边缘：`Phylo.Stat.KingmanJumpChain.partitionProb_merge_recursion`（**实数层**递归）
  对 `P` 求和 —— 即 `(1/C)·Σ_{Q : MergeInto Q P} jumpWeight n (k+1) Q = jumpWeight n k P`。

把这两条从「逐点算术」搬成「测度等式」的**簿记**（`Measure.sum_map` 的推前展开、
`Measure.sum_apply_of_countable` 的 `tsum`→`Finset.sum`、`ENNReal.ofReal` 与实数乘法的搬运）
本文件**未完成**，如实记为缺口 —— **不是** `axiom`、**不是** `sorry`。 -/

/-- ❌ **缺口：层间一致性的测度层形式（一步联合律的两个边缘）** ——
存在一步联合律 `step`，以 `jumpMeasure n (k+1)` 为**左边缘**、`jumpMeasure n k` 为**右边缘**。

（`jumpStepLaw n k` 就是候选；本文件证出了它的**逐点权重**与左边缘的核心算术，
但**边缘等式本身未证**，故仍留作 `Prop`。） -/
def jumpMeasure_step_gap : Prop :=
  ∀ (n k : ℕ), 1 ≤ k → k < n →
    ∃ step : Measure (Phylo.Stat.KingmanJumpChain.PartK n (k + 1) ×
        Phylo.Stat.KingmanJumpChain.PartK n k),
      IsProbabilityMeasure step ∧ step.fst = jumpMeasure n (k + 1) ∧ step.snd = jumpMeasure n k

/-! ## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| K82 (2.2) 的跳链**绝对概率** | ✅ 在 W10a（`jumpWeight` = `partitionProb`，`+ partitionProb_sum_eq_one` / `jumpWeight_sum_eq_one`） |
| K82 (1.7) 的逗留时间**律** `Exp(d_k)` | ✅ 在 W10b（`sojournLaw` / `isProbabilityMeasure_sojournLaw` / `sojournLaw_Ioi`） |
| K82 **Theorem 1 的独立性** | ✅ **本文件**：每个层 `k` 上 `IndepFun`（**真 `IndepFun`**，两个边缘也证出） |
| K82 (2.1) 的**正向计数**「一步去向恰 `C(k+1,2)` 个」 | ✅ **本文件**：`mergeTargets_gap`（纤维求和，纯内核） |
| 一步联合律 `jumpStepLaw` 的定义 | ✅ **本文件**（＋显式权重形式 `pairMeasure`） |
| 一步联合律左边缘的**逐点算术** | ✅ **本文件**：`sum_targets_jumpWeight` |
| 一步联合律**两个边缘的测度等式** | ❌ **未做**（簿记未完成）；精确记为 `jumpMeasure_step_gap` |
| 「**整条**跳链 `(S_n,…,S_1)` 作为轨迹空间对象」 | ❌ **未做**：需要链式联合律与转移核，本文件只做**单层**边缘 |
| `R_t = S_{D_t}`（过程恒等式） | ❌ **未做**：需要连续时间的死亡过程 `(D_t)`（本库无 CTMC，见 W10 的路线决策） |
-/

end Phylo.Stat.KingmanLaw
