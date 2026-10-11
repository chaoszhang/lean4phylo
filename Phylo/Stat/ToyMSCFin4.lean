import Phylo.Stat.MSCProof
import Phylo.Stat.EmpiricalConvergence
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Phylo.Stat.ToyMSCFin4

abbrev U : Type := ↥(Finset.univ : Finset (Fin 4))

theorem liftU_mem (T : Finset (Fin 4)) (x : U) :
    x ∈ Phylo.Stat.MSCProof.liftU T ↔ (x : Fin 4) ∈ T := by
  simp [Phylo.Stat.MSCProof.liftU]

theorem liftU_card (T : Finset (Fin 4)) :
    (Phylo.Stat.MSCProof.liftU T).card = T.card :=
  Phylo.Stat.MSCProof.card_liftU T

noncomputable def pairSub (S T : Finset (Fin 4)) : Finset ↥S :=
  Finset.univ.filter fun x => (x : Fin 4) ∈ T

theorem pairSub_univ (T : Finset (Fin 4)) :
    pairSub (Finset.univ : Finset (Fin 4)) T = Phylo.Stat.MSCProof.liftU T := rfl

noncomputable def pointTable (q : (S : Finset (Fin 4)) → S.card = 4 → Split ↥S) :
    QuartetFreq (Fin 4) where
  p := fun S hS r => if r = q S hS ∨ r = (q S hS).swap then 1 / 2 else 0
  p_nonneg := by
    intro S hS r
    by_cases h : r = q S hS ∨ r = (q S hS).swap
    · rw [ite_eq_left h]; norm_num
    · rw [ite_eq_right h]
  p_sum_one := by
    intro S hS
    have hterm : ∀ r : Split ↥S,
        (if r = q S hS ∨ r = (q S hS).swap then (1 / 2 : ℝ) else 0)
          = (if r = q S hS ∨ r = (q S hS).swap then (1 : ℝ) else 0) * (1 / 2) := by
      intro r
      by_cases h : r = q S hS ∨ r = (q S hS).swap <;> simp [h]
    rw [Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.sum_mul, Finset.sum_boole]
    have hcard : ((Finset.univ : Finset (Split ↥S)).filter
        (fun r => r = q S hS ∨ r = (q S hS).swap)).card = 2 := by
      have hset : ((Finset.univ : Finset (Split ↥S)).filter
          (fun r => r = q S hS ∨ r = (q S hS).swap))
          = ({q S hS, (q S hS).swap} : Finset (Split ↥S)) := by
        ext r; simp
      rw [hset, Finset.card_pair (Phylo.Stat.MSCProof.ne_swap_of_split (q S hS))]
    rw [hcard]
    norm_num
  p_swap := by
    intro S hS r
    have hiff : (r.swap = q S hS ∨ r.swap = (q S hS).swap)
        ↔ (r = q S hS ∨ r = (q S hS).swap) := by
      constructor
      · rintro (h | h)
        · exact Or.inr (Split.swap_injective (by rw [Split.swap_swap]; exact h))
        · exact Or.inl (Split.swap_injective h)
      · rintro (h | h)
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h, Split.swap_swap])
    by_cases h : r = q S hS ∨ r = (q S hS).swap
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun hh => h (hiff.mp hh)), ite_eq_right h]

/-- 坐标拉回造出的 split（`sideA = pairSub S T`）。 -/
noncomputable def splitOn (S : Finset (Fin 4)) (hS : S.card = 4) (T : Finset (Fin 4))
    (hT : T.card = 2) : Split ↥S :=
  Phylo.splitOf (pairSub S T)
    (Finset.card_pos.mp (by
      have hS4 : S = (Finset.univ : Finset (Fin 4)) :=
        Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
      subst hS4
      rw [pairSub_univ, liftU_card, hT]; norm_num))
    (Phylo.compl_nonempty_of_ne_univ (by
      have hS4 : S = (Finset.univ : Finset (Fin 4)) :=
        Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
      subst hS4
      intro hh
      have hc := congrArg Finset.card hh
      rw [pairSub_univ, liftU_card, hT, Finset.card_univ, Fintype.card_coe, Finset.card_univ,
        Fintype.card_fin] at hc
      omega))

theorem splitOn_sideA (S : Finset (Fin 4)) (hS : S.card = 4) (T : Finset (Fin 4))
    (hT : T.card = 2) : (splitOn S hS T hT).sideA = pairSub S T :=
  Phylo.splitOf_sideA _ _ _

noncomputable abbrev splitA : Split U := splitOn Finset.univ (by decide) ({0, 1} : Finset (Fin 4)) (by decide)

noncomputable abbrev splitB : Split U := splitOn Finset.univ (by decide) ({0, 2} : Finset (Fin 4)) (by decide)

theorem splitA_sideA : splitA.sideA = Phylo.Stat.MSCProof.liftU ({0, 1} : Finset (Fin 4)) := by
  rw [splitA, splitOn_sideA, pairSub_univ]

theorem splitB_sideA : splitB.sideA = Phylo.Stat.MSCProof.liftU ({0, 2} : Finset (Fin 4)) := by
  rw [splitB, splitOn_sideA, pairSub_univ]

theorem splitA_sideA4 :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4))) splitA
      = ({0, 1} : Finset (Fin 4)) := by
  rw [Phylo.Stat.MSCProof.sideA4, splitA_sideA]
  exact Phylo.Stat.MSCProof.image_liftU _

theorem splitB_sideA4 :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4))) splitB
      = ({0, 2} : Finset (Fin 4)) := by
  rw [Phylo.Stat.MSCProof.sideA4, splitB_sideA]
  exact Phylo.Stat.MSCProof.image_liftU _

theorem splitA_swap_sideA4 :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4))) splitA.swap
      = ({2, 3} : Finset (Fin 4)) := by
  rw [Phylo.Stat.MSCProof.sideA4_swap, splitA_sideA4]
  decide

theorem splitB_swap_sideA4 :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4))) splitB.swap
      = ({1, 3} : Finset (Fin 4)) := by
  rw [Phylo.Stat.MSCProof.sideA4_swap, splitB_sideA4]
  decide

noncomputable def qA (S : Finset (Fin 4)) (hS : S.card = 4) : Split ↥S :=
  splitOn S hS ({0, 1} : Finset (Fin 4)) (by decide)

noncomputable def qB (S : Finset (Fin 4)) (hS : S.card = 4) : Split ↥S :=
  splitOn S hS ({0, 2} : Finset (Fin 4)) (by decide)

theorem qA_card (S : Finset (Fin 4)) (hS : S.card = 4) : (qA S hS).sideA.card = 2 := by
  rw [qA, splitOn_sideA]
  have hS4 : S = (Finset.univ : Finset (Fin 4)) := Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
  subst hS4
  rw [pairSub_univ, liftU_card]; decide

theorem qB_card (S : Finset (Fin 4)) (hS : S.card = 4) : (qB S hS).sideA.card = 2 := by
  rw [qB, splitOn_sideA]
  have hS4 : S = (Finset.univ : Finset (Fin 4)) := Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
  subst hS4
  rw [pairSub_univ, liftU_card]; decide

noncomputable def freqA : QuartetFreq (Fin 4) := pointTable qA

noncomputable def freqB : QuartetFreq (Fin 4) := pointTable qB

theorem freqA_apply (S : Finset (Fin 4)) (hS : S.card = 4) (r : Split ↥S) :
    freqA.p S hS r = (if r = qA S hS ∨ r = (qA S hS).swap then (1 / 2 : ℝ) else 0) := rfl

theorem freqB_apply (S : Finset (Fin 4)) (hS : S.card = 4) (r : Split ↥S) :
    freqB.p S hS r = (if r = qB S hS ∨ r = (qB S hS).swap then (1 / 2 : ℝ) else 0) := rfl

theorem sideA4_qA (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4)))
      (qA Finset.univ hS) = ({0, 1} : Finset (Fin 4)) := by
  rw [show qA Finset.univ hS = splitA from rfl, splitA_sideA4]

theorem sideA4_qA_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4)))
      (qA Finset.univ hS).swap = ({2, 3} : Finset (Fin 4)) := by
  rw [show (qA Finset.univ hS).swap = splitA.swap from rfl, splitA_swap_sideA4]

theorem sideA4_qB (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4)))
      (qB Finset.univ hS) = ({0, 2} : Finset (Fin 4)) := by
  rw [show qB Finset.univ hS = splitB from rfl, splitB_sideA4]

theorem sideA4_qB_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    Phylo.Stat.MSCProof.sideA4 (S := (Finset.univ : Finset (Fin 4)))
      (qB Finset.univ hS).swap = ({1, 3} : Finset (Fin 4)) := by
  rw [show (qB Finset.univ hS).swap = splitB.swap from rfl, splitB_swap_sideA4]

theorem qSplit_univ_eq_qA_univ_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    Phylo.Stat.MSCProof.qSplit Finset.univ hS = (qA Finset.univ hS).swap := by
  refine Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq ?_
  rw [Split.swap_sideA, Phylo.Stat.MSCProof.qSplit_sideA, Split.sideB_eq_sdiff]
  rw [show (qA Finset.univ hS).sideA
      = Phylo.Stat.MSCProof.liftU ({0, 1} : Finset (Fin 4)) from
    (by rw [show qA Finset.univ hS = splitA from rfl, splitA_sideA])]
  ext ⟨v, hv⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, liftU_mem]
  constructor
  · intro hx hc
    fin_cases v <;> simp_all
  · intro hc
    fin_cases v <;> simp_all

theorem freqA_qA_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    freqA.p Finset.univ hS (qA Finset.univ hS).swap = 1 / 2 := by
  rw [freqA_apply]
  exact ite_eq_left (Or.inr rfl)

theorem freqB_qA_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    freqB.p Finset.univ hS (qA Finset.univ hS).swap = 0 := by
  rw [← qSplit_univ_eq_qA_univ_swap hS, freqB_apply]
  exact ite_eq_right (by
    rintro (h | h)
    · have h4 := congrArg (Phylo.Stat.MSCProof.sideA4
        (S := (Finset.univ : Finset (Fin 4)))) h
      rw [Phylo.Stat.MSCProof.sideA4_qSplit, sideA4_qB hS] at h4
      exact absurd h4 (by decide)
    · have h4 := congrArg (Phylo.Stat.MSCProof.sideA4
        (S := (Finset.univ : Finset (Fin 4)))) h
      rw [Phylo.Stat.MSCProof.sideA4_qSplit, sideA4_qB_swap hS] at h4
      exact absurd h4 (by decide))

theorem freqA_majorizes (hS : (Finset.univ : Finset (Fin 4)).card = 4) {r : Split U}
    (hr : r ≠ (qA Finset.univ hS).swap) (hrs : r ≠ qA Finset.univ hS) :
    freqA.p Finset.univ hS r < freqA.p Finset.univ hS (qA Finset.univ hS).swap := by
  have h2 : freqA.p Finset.univ hS r = 0 := by
    rw [freqA_apply]
    exact ite_eq_right (fun hh => hh.elim hrs hr)
  rw [freqA_qA_swap hS, h2]
  norm_num

noncomputable def mscFreqA : MSCFreq (Fin 4) where
  tree := Phylo.Stat.MSCProof.mscQuartetTree.tree
  q := Phylo.Stat.MSCProof.qSplit
  q_card := Phylo.Stat.MSCProof.qSplit_card
  displays := Phylo.Stat.MSCProof.qSplit_displays
  freq := freqA
  majorizes := by
    intro S hS r hr hrs
    obtain rfl : S = (Finset.univ : Finset (Fin 4)) :=
      Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
    rw [qSplit_univ_eq_qA_univ_swap hS] at hr hrs
    rw [Split.swap_swap] at hrs
    exact freqA_majorizes hS hr hrs

theorem mscFreqA_nonempty : Nonempty (MSCFreq.{0, 0} (Fin 4)) := ⟨mscFreqA⟩

/-! ## 3. 推前频率表（`m.freq` = `(4/5)·freqA + (1/5)·freqB`） -/

noncomputable def mFreq : QuartetFreq (Fin 4) where
  p := fun S hS r => (4 / 5) * freqA.p S hS r + (1 / 5) * freqB.p S hS r
  p_nonneg := fun S hS r =>
    add_nonneg (mul_nonneg (by norm_num) (freqA.p_nonneg S hS r))
      (mul_nonneg (by norm_num) (freqB.p_nonneg S hS r))
  p_sum_one := by
    intro S hS
    have h1 : ∑ r : Split ↥S, (4 / 5 : ℝ) * freqA.p S hS r = 4 / 5 := by
      rw [← Finset.mul_sum, freqA.p_sum_one S hS, mul_one]
    have h2 : ∑ r : Split ↥S, (1 / 5 : ℝ) * freqB.p S hS r = 1 / 5 := by
      rw [← Finset.mul_sum, freqB.p_sum_one S hS, mul_one]
    rw [Finset.sum_add_distrib, h1, h2]
    norm_num
  p_swap := by
    intro S hS r
    rw [freqA.p_swap S hS r, freqB.p_swap S hS r]

theorem mFreq_qA_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    mFreq.p Finset.univ hS (qA Finset.univ hS).swap = 2 / 5 := by
  show (4 / 5) * freqA.p Finset.univ hS (qA Finset.univ hS).swap
      + (1 / 5) * freqB.p Finset.univ hS (qA Finset.univ hS).swap = 2 / 5
  rw [freqA_qA_swap hS, freqB_qA_swap hS]
  norm_num

theorem mFreq_splitA (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    mFreq.p Finset.univ hS splitA = 2 / 5 := by
  have hAs : freqA.p Finset.univ hS splitA = 1 / 2 := by
    rw [freqA_apply]
    exact ite_eq_left (Or.inl rfl)
  have hBs : freqB.p Finset.univ hS splitA = 0 := by
    rw [freqB_apply]
    exact ite_eq_right (by
      rintro (h | h)
      · have h4 := congrArg (Phylo.Stat.MSCProof.sideA4
          (S := (Finset.univ : Finset (Fin 4)))) h
        rw [splitA_sideA4, sideA4_qB hS] at h4
        exact absurd h4 (by decide)
      · have h4 := congrArg (Phylo.Stat.MSCProof.sideA4
          (S := (Finset.univ : Finset (Fin 4)))) h
        rw [splitA_sideA4, sideA4_qB_swap hS] at h4
        exact absurd h4 (by decide))
  show (4 / 5) * freqA.p Finset.univ hS splitA + (1 / 5) * freqB.p Finset.univ hS splitA = 2 / 5
  rw [hAs, hBs]
  norm_num

/-- 推前表在竞争者上至多 `1/10`（因为 `freqA` 在真类外给 `0`）。 -/
theorem mFreq_competitor_le (hS : (Finset.univ : Finset (Fin 4)).card = 4) {r : Split U}
    (hr : r ≠ (qA Finset.univ hS).swap) (hrs : r ≠ qA Finset.univ hS) :
    mFreq.p Finset.univ hS r ≤ 1 / 10 := by
  have hA0 : freqA.p Finset.univ hS r = 0 := by
    rw [freqA_apply]
    exact ite_eq_right (fun hh => hh.elim hrs hr)
  have hBle : freqB.p Finset.univ hS r ≤ 1 / 2 := by
    rw [freqB_apply]
    by_cases h : r = qB Finset.univ hS ∨ r = (qB Finset.univ hS).swap
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]; norm_num
  show (4 / 5) * freqA.p Finset.univ hS r + (1 / 5) * freqB.p Finset.univ hS r ≤ 1 / 10
  rw [hA0, mul_zero, zero_add]
  have h := mul_le_mul_of_nonneg_left hBle (by norm_num : (0:ℝ) ≤ 1 / 5)
  linarith

/-- ★★★ **推前表的 `majorizes`**（规格 §7.4 的**严格**不等式，本文件独立复核）。 -/
theorem mFreq_majorizes (hS : (Finset.univ : Finset (Fin 4)).card = 4) {r : Split U}
    (hr : r ≠ (qA Finset.univ hS).swap) (hrs : r ≠ qA Finset.univ hS) :
    mFreq.p Finset.univ hS r < mFreq.p Finset.univ hS (qA Finset.univ hS).swap := by
  rw [mFreq_qA_swap hS]
  linarith [mFreq_competitor_le hS hr hrs]

/-- ★★★ **推前的 `MSCFreq`**（真树 `01|23`、频率表 `mFreq`）。 -/
noncomputable def mGuard : MSCFreq (Fin 4) where
  tree := Phylo.Stat.MSCProof.mscQuartetTree.tree
  q := Phylo.Stat.MSCProof.qSplit
  q_card := Phylo.Stat.MSCProof.qSplit_card
  displays := Phylo.Stat.MSCProof.qSplit_displays
  freq := mFreq
  majorizes := by
    intro S hS r hr hrs
    obtain rfl : S = (Finset.univ : Finset (Fin 4)) :=
      Phylo.Stat.MSCProof.eq_univ_of_card_four S hS
    rw [qSplit_univ_eq_qA_univ_swap hS] at hr hrs
    rw [Split.swap_swap] at hrs
    exact mFreq_majorizes hS hr hrs

theorem mGuard_nonempty : Nonempty (MSCFreq.{0, 0} (Fin 4)) := ⟨mGuard⟩

/-! ## 4. ★★ `k` 固定 ⇒ 假：守卫结构与反例定理 -/

/-- 「经验表最终 `ε`-接近 `target`」。 -/
abbrev EventuallyClose (emp : ℕ → (ℕ → Bool) → ℝ) (target : ℝ) (ε : ℝ) : (ℕ → Bool) → Prop :=
  fun ω => ∃ N : ℕ, ∀ n ≥ N, |emp n ω - target| < ε

/-- **`k` 固定（`k = 1`）的模型**：把「`k` 固定」的**确切内容**写死。 -/
structure FixedKGuard where
  /-- `k = 1` 时的样本空间（`ω 0` 是唯一那棵树的实现）。 -/
  μ : Measure (ℕ → Bool)
  isProb : IsProbabilityMeasure μ
  /-- 基因树 `b` 给出的 quartet 频率表。 -/
  FreqOf : Bool → QuartetFreq (Fin 4)
  /-- 被检验的那个分量（例如 `01|23` 分量）。 -/
  comp : QuartetFreq (Fin 4) → ℝ
  /-- 该分量的经验估计。 -/
  empA : ℕ → (ℕ → Bool) → ℝ
  /-- 条件均值（= 该树给的分量）。 -/
  meanA : (ℕ → Bool) → ℝ
  /-- ★ 强大数定律（`k = 1`：经验平均 a.e. 收敛到条件均值）。 -/
  SLLN : ∀ᵐ ω ∂μ, Tendsto (fun n => empA n ω) atTop (𝓝 (meanA ω))
  /-- 条件均值 = 该基因树给的表在该分量上的值。 -/
  mean_eq : ∀ ω, meanA ω = comp (FreqOf (ω 0))

/-- 守卫的「好集」（收敛成立的那些 `ω`）。 -/
def GuardGood (data : FixedKGuard) : Set (ℕ → Bool) :=
  {ω | Tendsto (fun n => data.empA n ω) atTop (𝓝 (data.meanA ω))}

theorem guardGood_ae (data : FixedKGuard) : ∀ᵐ ω ∂data.μ, ω ∈ GuardGood data :=
  data.SLLN

theorem guardGood_null (data : FixedKGuard) : data.μ {ω | ¬ (ω ∈ GuardGood data)} = 0 :=
  MeasureTheory.ae_iff.mp (guardGood_ae data)

/-- ★★★ **`k` 固定（`k = 1`）⇒ 「经验表 → `m.freq`」为假**（规格 §4.1 的护栏）。

**陈述**：对**任何** `FixedKGuard`，若存在一棵基因树 `b₀` 使
「`b₀` 给的分量」≠「目标值 `target`」（`target` 例中取推前表 `m.freq` 的值），
且 `{ω 0 = b₀}` 有正概率，则**存在正测度集** `s` 与 `ε > 0`，使 `s` 上「经验表最终
`ε`-接近 `target`」**不成立**。

**它替规格 §4.1 论证了什么**：`k` 固定时经验频率的极限是 `comp (FreqOf (ω 0))` ——
一个**依赖实现到的基因树**的随机量（`mean_eq`）；于是只要它在某个**正测度**事件上与常数
`target` 不同，「经验表 → `target`」就**不可能** a.e. 成立（`μ` 为概率测度、`s` 正测度
⇒ `sᶜ ≠ univ`）。`k → ∞` 之所以能救，是因为那时极限变成 `𝔼[FreqOf (ω 0)] = m.freq`
（推前），而不是单个 `FreqOf (ω 0)`。 -/
theorem fixed_k_counterexample (data : FixedKGuard) (target : ℝ) (b₀ : Bool)
    (hpos : 0 < data.μ {ω | ω 0 = b₀}) (hne : data.comp (data.FreqOf b₀) ≠ target) :
    ∃ s : Set (ℕ → Bool), 0 < data.μ s ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ ω ∈ s, ¬ EventuallyClose data.empA target ε ω := by
  have hdpos : 0 < |data.comp (data.FreqOf b₀) - target| / 2 :=
    div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  refine ⟨{ω | ω 0 = b₀} ∩ GuardGood data, ?_, |data.comp (data.FreqOf b₀) - target| / 2,
    hdpos, ?_⟩
  · have hsub : {ω : ℕ → Bool | ω 0 = b₀} ⊆
        ({ω | ω 0 = b₀} ∩ GuardGood data) ∪ {ω | ¬ (ω ∈ GuardGood data)} := by
      intro ω hω
      by_cases h : ω ∈ GuardGood data
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr h
    have h1 : data.μ {ω : ℕ → Bool | ω 0 = b₀} ≤
        data.μ (({ω | ω 0 = b₀} ∩ GuardGood data) ∪ {ω | ¬ (ω ∈ GuardGood data)}) :=
      measure_mono hsub
    have h2 : data.μ (({ω | ω 0 = b₀} ∩ GuardGood data) ∪ {ω | ¬ (ω ∈ GuardGood data)}) ≤
        data.μ ({ω | ω 0 = b₀} ∩ GuardGood data)
          + data.μ {ω | ¬ (ω ∈ GuardGood data)} := measure_union_le _ _
    rw [guardGood_null data, add_zero] at h2
    exact lt_of_lt_of_le hpos (le_trans h1 h2)
  · intro ω hω hclose
    obtain ⟨hωb, hωG⟩ := hω
    have hωG' : Tendsto (fun n => data.empA n ω) atTop (𝓝 (data.meanA ω)) := hωG
    obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hωG' _ hdpos
    obtain ⟨N2, hN2⟩ := hclose
    have h1 := hN1 (max N1 N2) (le_max_left _ _)
    have h2 := hN2 (max N1 N2) (le_max_right _ _)
    rw [Real.dist_eq, abs_sub_comm] at h1
    have hL : data.meanA ω = data.comp (data.FreqOf b₀) := by rw [data.mean_eq ω, hωb]
    rw [hL] at h1
    have htri : |data.comp (data.FreqOf b₀) - target| ≤
        |data.comp (data.FreqOf b₀) - data.empA (max N1 N2) ω|
          + |data.empA (max N1 N2) ω - target| :=
      abs_sub_le _ _ _
    have hlt : |data.comp (data.FreqOf b₀) - target| <
        |data.comp (data.FreqOf b₀) - target| / 2 + |data.comp (data.FreqOf b₀) - target| / 2 :=
      lt_of_le_of_lt htri (add_lt_add h1 h2)
    rw [add_halves] at hlt
    exact lt_irrefl _ hlt

/-! ## 5. ★★ 具体见证（非空真）：`G = Bool`、`(4/5, 1/5)` 加权、`01|23` 真树 -/

/-- 公平硬币（库内 `EmpiricalConvergence.coin`）：`ν = 2⁻¹ • count`。 -/
noncomputable abbrev coinF := Phylo.Stat.EmpiricalConvergence.coin

/-- 位点/树的 iid 概率空间。 -/
noncomputable def muCoin : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => coinF)

theorem muCoin_false : muCoin {ω : ℕ → Bool | ω 0 = false} = 1 / 2 := by
  have hm : Measurable (fun ω : ℕ → Bool => ω 0) := measurable_pi_apply 0
  have hset : (fun ω : ℕ → Bool => ω 0) ⁻¹' ({false} : Set Bool) = {ω | ω 0 = false} := rfl
  rw [← hset, ← Measure.map_apply hm (measurableSet_singleton false)]
  have hmu : muCoin = Measure.infinitePi (fun _ : ℕ => coinF) := rfl
  rw [hmu, Measure.infinitePi_map_eval (fun _ : ℕ => coinF) 0,
    Phylo.Stat.EmpiricalConvergence.coin_false]

/-- 真类分量：`01|23` 分量。 -/
noncomputable def compA (F : QuartetFreq (Fin 4)) : ℝ := F.p Finset.univ (by decide) splitA

/-- ★★ **具体守卫**（本文件的反例模型）：`FreqOf false = freqA`（质量在 `01|23`）、
`FreqOf true = freqB`（质量在 `02|13`）、`ω 0` 是唯一那棵实现到的树。 -/
noncomputable def guardExample : FixedKGuard where
  μ := muCoin
  isProb := by
    unfold muCoin
    infer_instance
  FreqOf := fun b => if b = false then freqA else freqB
  comp := compA
  empA := fun _ ω => compA (if ω 0 = false then freqA else freqB)
  meanA := fun ω => compA (if ω 0 = false then freqA else freqB)
  SLLN := by
    filter_upwards with ω
    exact tendsto_const_nhds
  mean_eq := fun ω => by
    show compA (if ω 0 = false then freqA else freqB) = compA (if ω 0 = false then freqA else freqB)
    rfl

theorem guardExample_hpos : 0 < guardExample.μ {ω | ω 0 = false} := by
  rw [show guardExample.μ = muCoin from rfl, muCoin_false]
  norm_num

theorem guardExample_ne : guardExample.comp (guardExample.FreqOf false) ≠ mFreq.p Finset.univ (by decide) splitA := by
  have h1 : guardExample.comp (guardExample.FreqOf false) = 1 / 2 := by
    show compA (if (false : Bool) = false then freqA else freqB) = 1 / 2
    rw [ite_eq_left rfl]
    show freqA.p Finset.univ (by decide) splitA = 1 / 2
    rw [freqA_apply]
    exact ite_eq_left (Or.inl rfl)
  rw [h1, mFreq_splitA (by decide)]
  norm_num

/-- ★★★ **反例定理的具体实例**（非空真）。 -/
theorem fixed_k_counterexample_concrete :
    ∃ s : Set (ℕ → Bool), 0 < guardExample.μ s ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ ω ∈ s, ¬ EventuallyClose guardExample.empA
        (mFreq.p Finset.univ (by decide) splitA) ε ω :=
  fixed_k_counterexample guardExample _ false guardExample_hpos guardExample_ne

end Phylo.Stat.ToyMSCFin4
