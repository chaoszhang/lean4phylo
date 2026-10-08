/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.CASTERBridge

/-!
# `Phylo.Stat.CASTERTopo` —— 定理 1 / 定理 2 的**无根 quartet 拓扑**版本

## 为什么要再来一个版本

CASTeR 的得分本身就是对**三个无根 quartet 拓扑**定义的：
`W(S) = Σ_{T ∈ topologies(S)} Σ_i w_i(T)`（正文式 (1)）。而各模型的命题 A
（`Phylo.Stat.CASTERJC69` / `CASTERLM1` / `CASTERF84`）与桥接
（`Phylo.Stat.CASTERBridge.expWeight_strict`）产出的期望权重表**正是 `Topo` 索引的**。

库里既有的 `Phylo.Stat.CASTERTheorem1` 用的是 `QuartetChoice X`
（`(S) → S.card = 4 → Split ↥S`）—— 那是与 `QuartetTree` / `QuartetDecidesTree` 配套的
**一般 quartet 选择**框架，但它允许 `1|3` 这类**非 quartet** 的划分，
于是「真拓扑严格最大」这条前提在 `1|3` 划分上没有意义（CASTER 的权重表根本没定义它们）。

⇒ 本文件把同一条定理在 **`Topo`（三选一）** 层面重述一遍：
* 前提与各模型产出**同型**（`TopoIdeal.propB` 直接由 `expWeight_strict` 供给）；
* 结论更强也更干净：**逐 quartet 拓扑完全相等**（不需要模 `swap`）；
* 并且**大数定律作为显式假设**给出（不新增公理）。

两个版本的关系：`1|3` 划分被本文件排除在外，而 `2|2` 划分的三个等价类与 `Topo`
一一对应 —— 这就是「quartet 拓扑」与「quartet split」的常规对应。

## 🔻 诚实边界

* 本文件**不**声称把 `Split ↥S` 与 `Topo` 的对应**形式化**了（那需要给每个 4-元集挑一个
  枚举 `Fin 4 ≃ ↥S`，属于「标号层」工程）。所以本文件的定理与 `Phylo.Stat.CASTERTheorem1`
  是**并列**的两条路：前者对应「每个 quartet 的**拓扑**判对了」，后者对应
  「`QuartetChoice` 判对了（模 `swap`）」。都成立，互不依赖。
* 大数定律以**显式假设**出现（见 `topo_statisticallyConsistent` 的 `hconv`），
  与 `Phylo.Stat.MSC` 的 `MSCSampling.converges` 是同一层的假设。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

namespace Phylo.Stat.CASTERTopo

open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERBridge

open MeasureTheory

/-! ## 1. 无根 quartet 拓扑选择与得分 -/

/-- **无根 quartet 拓扑选择**：每个 4-元集上选三个 quartet 拓扑之一。 -/
abbrev TopoChoice (X : Type u) [Fintype X] [DecidableEq X] :=
  (S : Finset X) → S.card = 4 → Topo

/-- **权重表**（`Topo` 索引）：每个 4-元集上三个拓扑各一个实数权重。 -/
abbrev TopoWeight (X : Type u) [Fintype X] [DecidableEq X] :=
  (S : Finset X) → S.card = 4 → Topo → ℝ

/-- **CASTER 得分**（正文式 (1) 的 `Topo` 版）：所有 4-元集上选定拓扑的权重之和。 -/
noncomputable def topoScore (W : TopoWeight X) (q : TopoChoice X) : ℝ :=
  ∑ S : {S : Finset X // S.card = 4}, W S.1 S.2 (q S.1 S.2)

/-- **真选择**（逐个 quartet 拓扑**完全相等**；`Topo` 版不需要模 `swap`）。 -/
def IsTrueT (qtrue q : TopoChoice X) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4), q S hS = qtrue S hS

/-! ## 2. 理想模型与 gap 引理 -/

/-- **理想模型**：理论期望权重表 + 真选择 + **命题 B**（真拓扑在每个 4-元集上严格最大）。

（命题 B 由 `Phylo.Stat.CASTERBridge.expWeight_strict` 从各模型的命题 A + MSC 对称性供给。） -/
structure TopoIdeal (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 理论期望权重表。 -/
  W : TopoWeight X
  /-- 真树的 quartet 拓扑选择。 -/
  qtrue : TopoChoice X
  /-- ★ **命题 B**。 -/
  propB : ∀ (S : Finset X) (hS : S.card = 4) (T : Topo),
    T ≠ qtrue S hS → W S hS T < W S hS (qtrue S hS)

namespace TopoIdeal

variable (M : TopoIdeal X)

/-- **逐点弱最大**。 -/
theorem W_le (S : Finset X) (hS : S.card = 4) (T : Topo) :
    M.W S hS T ≤ M.W S hS (M.qtrue S hS) := by
  by_cases h : T = M.qtrue S hS
  · rw [h]
  · exact (M.propB S hS T h).le

/-- ★★ **理想情形下真选择得分最大**。 -/
theorem topoScore_le (q : TopoChoice X) :
    topoScore M.W q ≤ topoScore M.W M.qtrue :=
  Finset.sum_le_sum (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    fun S _ => M.W_le S.1 S.2 (q S.1 S.2)

/-- **非真选择必在某处不同**。 -/
theorem exists_ne_of_not_true {q : TopoChoice X} (h : ¬ IsTrueT M.qtrue q) :
    ∃ (S : Finset X) (hS : S.card = 4), q S hS ≠ M.qtrue S hS := by
  by_contra hc
  exact h fun S hS => by by_contra hne; exact hc ⟨S, hS, hne⟩

/-- ★★★ **非真选择的得分严格小于真选择**。 -/
theorem topoScore_lt_of_not_true {q : TopoChoice X} (h : ¬ IsTrueT M.qtrue q) :
    topoScore M.W q < topoScore M.W M.qtrue := by
  obtain ⟨S, hS, hne⟩ := M.exists_ne_of_not_true h
  exact Finset.sum_lt_sum
    (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    (fun S1 _ => M.W_le S1.1 S1.2 (q S1.1 S1.2))
    ⟨⟨S, hS⟩, Finset.mem_univ _, M.propB S hS (q S hS) hne⟩

/-- ★★ **得分 gap**：存在统一 `δ > 0`，非真选择至少低 `δ`（`TopoChoice X` 有限）。 -/
theorem exists_gap (hNE : ∃ q : TopoChoice X, ¬ IsTrueT M.qtrue q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : TopoChoice X, ¬ IsTrueT M.qtrue q →
      topoScore M.W q + δ ≤ topoScore M.W M.qtrue := by
  classical
  obtain ⟨q0, hq0⟩ := hNE
  set S : Finset ℝ := ((Finset.univ : Finset (TopoChoice X)).filter
      (fun q => ¬ IsTrueT M.qtrue q)).image
      (fun q => topoScore M.W M.qtrue - topoScore M.W q) with hSdef
  have hne : S.Nonempty := by
    refine ⟨topoScore M.W M.qtrue - topoScore M.W q0, ?_⟩
    rw [hSdef]
    exact Finset.mem_image.mpr
      ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩, rfl⟩
  refine ⟨S.min' hne, ?_, ?_⟩
  · obtain ⟨q1, hq1, heq⟩ := Finset.mem_image.mp (S.min'_mem hne)
    rw [← heq]
    have := M.topoScore_lt_of_not_true (Finset.mem_filter.mp hq1).2
    linarith
  · intro q hq
    have hmem : topoScore M.W M.qtrue - topoScore M.W q ∈ S := by
      rw [hSdef]
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    have h1 : S.min' hne ≤ topoScore M.W M.qtrue - topoScore M.W q := S.min'_le _ hmem
    linarith

end TopoIdeal

/-! ## 3. 稳定性与定理 1 -/

/-- **权重表的逐点 `ε`-接近**。 -/
def TopoClose (W W' : TopoWeight X) (ε : ℝ) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4) (T : Topo), |W S hS T - W' S hS T| < ε

theorem TopoClose_symm {W W' : TopoWeight X} {ε : ℝ} (h : TopoClose W W' ε) :
    TopoClose W' W ε :=
  fun S hS T => by rw [abs_sub_comm]; exact h S hS T

/-- **扰动下的得分比较上界**。 -/
theorem topoScore_le_add (W W' : TopoWeight X) (q : TopoChoice X) {ε : ℝ}
    (hW : TopoClose W W' ε) :
    topoScore W q ≤ topoScore W' q + ε * (Fintype.card {S : Finset X // S.card = 4}) := by
  have hdiff : topoScore W q - topoScore W' q ≤
      ε * (Fintype.card {S : Finset X // S.card = 4}) := by
    rw [topoScore, topoScore, ← Finset.sum_sub_distrib]
    calc (Finset.univ : Finset {S : Finset X // S.card = 4}).sum
          (fun S => W S.1 S.2 (q S.1 S.2) - W' S.1 S.2 (q S.1 S.2))
        ≤ (Finset.univ : Finset {S : Finset X // S.card = 4}).sum (fun _ => ε) :=
          Finset.sum_le_sum fun S _ => le_trans (le_abs_self _) (hW S.1 S.2 (q S.1 S.2)).le
      _ = ε * (Fintype.card {S : Finset X // S.card = 4}) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  linarith

/-- ★★★ **稳定性**：`ε < δ/(2N+1)` 时，经验权重上不低于真选择的选择必是真选择。 -/
theorem topo_stable_argmax (M : TopoIdeal X) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : TopoChoice X, ¬ IsTrueT M.qtrue q →
      topoScore M.W q + δ ≤ topoScore M.W M.qtrue)
    {W : TopoWeight X}
    (hW : TopoClose W M.W (δ / (2 * (Fintype.card {S : Finset X // S.card = 4}) + 1)))
    {q : TopoChoice X}
    (hmax : topoScore W M.qtrue ≤ topoScore W q) : IsTrueT M.qtrue q := by
  by_contra hnot
  set N : ℝ := (Fintype.card {S : Finset X // S.card = 4} : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * N + 1) with hεdef
  have hN1 : (2 : ℝ) * N + 1 ≠ 0 := by linarith
  have hεN : ε * (2 * N + 1) = δ := by rw [hεdef, div_mul_cancel₀ _ hN1]
  have h1 : topoScore W q ≤ topoScore M.W q + ε * N := topoScore_le_add W M.W q hW
  have h2 : topoScore M.W M.qtrue ≤ topoScore W M.qtrue + ε * N :=
    topoScore_le_add M.W W M.qtrue (TopoClose_symm hW)
  have h3 : topoScore M.W q + δ ≤ topoScore M.W M.qtrue := hgap q hnot
  have h4 : 2 * ε * N < δ := by rw [← hεN]; nlinarith
  linarith

/-- ★★★ **CASTER 定理 1（统计一致性，无根 quartet 拓扑层面）**。

`emp n` 是第 `n` 个样本的经验平均权重表，`hconv` 是**大数定律**（作为显式假设，
不新增公理），`E n` 在 `emp n` 上最大化 CASTER 得分。
则最终 `E n` 与真选择**每个 quartet 拓扑完全相同**。 -/
theorem topo_statisticallyConsistent (M : TopoIdeal X)
    (emp : ℕ → TopoWeight X)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n) M.W ε)
    (hNE : ∃ q : TopoChoice X, ¬ IsTrueT M.qtrue q)
    {E : ℕ → TopoChoice X}
    (hE : ∀ (n : ℕ) (q : TopoChoice X), topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT M.qtrue (E n) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := M.exists_gap hNE
  set K : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := hconv (δ / K) (div_pos hδ hKpos)
  refine ⟨N, fun n hn => ?_⟩
  refine topo_stable_argmax M hδ hgap (W := emp n) ?_ ?_
  · simpa [hKdef] using hN n hn
  · exact hE n M.qtrue

/-- ★★★ **定理 2（贪心放置一致，`Topo` 版）**：候选集含真选择 + 在候选集上最大化 ⇒ 一致。

（附录对定理 2 的归纳证明只用这两条；候选集的形状不影响结论。） -/
theorem topo_greedy_consistent (M : TopoIdeal X)
    (emp : ℕ → TopoWeight X)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n) M.W ε)
    (hNE : ∃ q : TopoChoice X, ¬ IsTrueT M.qtrue q)
    (C : ℕ → Set (TopoChoice X)) (hfeas : ∀ n : ℕ, M.qtrue ∈ C n)
    {E : ℕ → TopoChoice X}
    (hmax : ∀ (n : ℕ) (q : TopoChoice X), q ∈ C n →
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT M.qtrue (E n) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := M.exists_gap hNE
  set K : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := hconv (δ / K) (div_pos hδ hKpos)
  refine ⟨N, fun n hn => ?_⟩
  refine topo_stable_argmax M hδ hgap (W := emp n) ?_ ?_
  · simpa [hKdef] using hN n hn
  · exact hmax n M.qtrue (hfeas n)

/-! ## 4. 与桥接对接：命题 B 由 `expWeight_strict` 供给 -/

/-- ★★★ **`TopoIdeal` 的前提（命题 B）由桥接直接供给**：对**任意** `MSCTopoSym` +
命题 A 数据（`PropAData`）+ 可积性，真拓扑 `ab|cd` 的期望权重严格大于另两个。

这一条就是各模型「插进引擎」的**接口**：
`A`/`f` 由 `Phylo.Stat.CASTERJC69`（或 LM1 / F84）供给，
`S`/`ν` 由 MSC 侧供给，`hint_*` 对应正文的「权重一致有界」。 -/
theorem propB_of_bridge {Θ : Type*} [MeasurableSpace Θ] (S : MSCTopoSym Θ) (ν : Measure Θ)
    [IsProbabilityMeasure ν] (hdeep : MeasurableSet {θ | S.deep θ}) (P : PropAData Θ)
    (hf_int : Integrable P.f ν) (hf_pos : ∀ θ, ¬ S.deep θ → 0 < P.f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint_ab : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ab_cd) ν)
    (hint_ac : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ac_bd) ν)
    (hint_ad : Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' .ad_bc) ν) :
    ∀ T : Topo, T ≠ Topo.ab_cd →
      expWeight ν S.τd P.A T < expWeight ν S.τd P.A Topo.ab_cd := by
  obtain ⟨h1, h2⟩ := expWeight_strict S ν hdeep P hf_int hf_pos hpos hint_ab hint_ac hint_ad
  intro T hT
  rcases T with _ | _ | _
  · exact absurd rfl hT
  · exact h1
  · exact h2

namespace TopoIdeal

variable {Θ : Type*} [MeasurableSpace Θ]

/-- ★★★ **从「单个 MSC 模型 + 命题 A 数据」打包出 `TopoIdeal`**（各模型插进引擎的**入口**）。

所有 4-元集共享同一个基因树模型（`S` / `ν` / `P`）—— 对**单个 quartet**（`X = Fin 4`，
只有一个 4-元集）这是**精确**的；对更多物种，各 quartet 的支长不同，需把 `(ν, P)`
也按 `(S, hS)` 索引（纯记账，模型无关）。

`qtrue` 取每个 4-元集上的 `ab|cd`（= 该 quartet **标号下**的真拓扑；标号是任意约定，
故不失一般性）；`propB` 由 ★★★ `propB_of_bridge` 供给。 -/
noncomputable def ofModel (S : MSCTopoSym Θ) (ν : Measure Θ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (P : PropAData Θ)
    (hf_int : Integrable P.f ν) (hf_pos : ∀ θ, ¬ S.deep θ → 0 < P.f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo, Integrable (fun θ => ∑ T' : Topo, S.τd θ T' * P.A θ T' T) ν) :
    TopoIdeal X where
  W := fun _ _ T => expWeight ν S.τd P.A T
  qtrue := fun _ _ => .ab_cd
  propB := fun _ _ T hT =>
    propB_of_bridge S ν hdeep P hf_int hf_pos hpos
      (hint .ab_cd) (hint .ac_bd) (hint .ad_bc) T hT

/-- ★★★ **从「每个 4-元集各自的 MSC 模型」打包出 `TopoIdeal`**（**一般多物种情形**）。

这是 `ofModel` 的一般化：每个 4-元集 `S` 有自己的时间空间 `Θ S hS`、自己的基因树拓扑分布
`M S hS`、自己的命题 A 数据 `P S hS`。真实物种树上各 quartet 的支长不同，
所以**这才是与正文一致的记账**；`ofModel` 是「所有 quartet 共享同一模型」的特例
（对单个 quartet 精确）。

`qtrue` 一律取 `.ab_cd`：每个 4-元集的标号（谁当 `a,b,c,d`）是该 quartet 模型自带的约定，
换标号只是把三个拓扑的名字置换，故不失一般性。 -/
noncomputable def ofFamily
    (Θ : (S : Finset X) → S.card = 4 → Type*)
    [inst : ∀ (S : Finset X) (hS : S.card = 4), MeasurableSpace (Θ S hS)]
    (M : ∀ (S : Finset X) (hS : S.card = 4), MSCTopoSym (Θ S hS))
    (ν : ∀ (S : Finset X) (hS : S.card = 4), Measure (Θ S hS))
    [inst2 : ∀ (S : Finset X) (hS : S.card = 4), IsProbabilityMeasure (ν S hS)]
    (hdeep : ∀ (S : Finset X) (hS : S.card = 4), MeasurableSet {θ | (M S hS).deep θ})
    (P : ∀ (S : Finset X) (hS : S.card = 4), PropAData (Θ S hS))
    (hf_int : ∀ (S : Finset X) (hS : S.card = 4), Integrable (P S hS).f (ν S hS))
    (hf_pos : ∀ (S : Finset X) (hS : S.card = 4) (θ : Θ S hS),
      ¬ (M S hS).deep θ → 0 < (P S hS).f θ)
    (hpos : ∀ (S : Finset X) (hS : S.card = 4), 0 < ν S hS {θ | ¬ (M S hS).deep θ})
    (hint : ∀ (S : Finset X) (hS : S.card = 4) (T : Topo),
      Integrable (fun θ => ∑ T' : Topo, (M S hS).τd θ T' * (P S hS).A θ T' T) (ν S hS)) :
    TopoIdeal X where
  W := fun S hS T => expWeight (ν S hS) (M S hS).τd (P S hS).A T
  qtrue := fun _ _ => .ab_cd
  propB := fun S hS T hT =>
    propB_of_bridge (M S hS) (ν S hS) (hdeep S hS) (P S hS) (hf_int S hS) (hf_pos S hS)
      (hpos S hS) (hint S hS .ab_cd) (hint S hS .ac_bd) (hint S hS .ad_bc) T hT

end TopoIdeal

end Phylo.Stat.CASTERTopo
