/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.CASTEREngine
import Phylo.Stat.QuartetDecides

/-!
# `Phylo.Stat.CASTERTheorem1` —— CASTER **定理 1（统计一致性）**

文献：Zhang, Nielsen, Mirarab (2025), *Science* **387**(6737) eadk9688，
正文 343–344 行（陈述）、附录 `sm.tex` **1277–1300** 行（证明）。

## 定理 1 说什么

> 在 JC69 / F84 / LM 模型下，用**相应**的位点模式权重，最大化
> `W(S) = Σ_{T ∈ topologies(S)} Σ_{i=1}^k w_i(T)` 的拓扑 `S` 是**统计一致**的。

## 证明链条（本文件补上最后两环）

```
① 命题 B（每个 quartet 上真拓扑的期望权重严格最大）   ← Phylo.Stat.CASTEREngine（已证）
② gap 引理   严格最大 ⟹ 有限选择空间上存在统一的正 gap δ    ← 本文件
③ 稳定性     经验平均权重逐点扰动 < δ/(2N+1) ⟹ argmax 不变  ← 本文件
④ 大数定律   经验平均权重最终收敛到理论期望权重           ← 公理化（见下）
──────────────────────────────────────────────────
⟹ 定理 1：argmax 最终与真树逐 quartet 一致
```
`②③` 与模型无关（只用到选择空间 `QuartetChoice X` **有限**），`①` 由引擎供给，
`④` 是标准大数定律。把 ① 换成 F84 / LM 的版本即得相应模型的定理 1
（本文件写成对任意 `CASTERIdeal` 成立，故换模型不用改一行）。

## 与 ASTRAL 侧的分工

本文件与 `Phylo.Stat.Stability`（ASTRAL 的通用引擎）**结构平行**，但**不能直接复用**：
ASTRAL 的样本是「一个概率分布」（`QuartetFreq`，有 `p_sum_one`），
而 CASTER 的样本是「**位点权重的经验平均**」，它**不是**概率分布（权重可正可负）。
所以这里把样本抽象成 `WeightTable`（每 4-元集、每 split 一个实数）。

## 🔻 诚实边界

* `CASTERSampling.converges` 是**公理化的大数定律**，与 `Phylo.Stat.MSC` 的
  `MSCSampling.converges` **同一层**（同样取「最终 ε-接近」的确定性形式）。
  换成真概率陈述需要概率空间 + 强大数定律 —— 与 `Phylo.Stat.MSCProof` 同属一个课题。
* 结论止于 **quartet 选择层**：估计量输出一个 `QuartetChoice`。升级为「树同构」
  由 `QuartetDecidesTree`（`Phylo.Stat.QuartetDecides`）完成 —— 与 ASTRAL 侧的
  `astral_iso` 完全同一条路。
* 正文还要求「权重跨位点一致**有界**」。本文件把有界性**折叠进 `converges`**
  （直接假设经验平均收敛），故不再单列 —— 因为定理 1 的证明只通过收敛性用到有界性。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 权重表、得分与理想模型 -/

/-- **权重表**：每个 4-元集上，每个（有向）split 一个实数权重。

它就是「把所有位点的位点模式权重加起来」得到的量；对无向拓扑我们只关心它模 `swap`。 -/
abbrev WeightTable (X : Type u) [Fintype X] [DecidableEq X] :=
  (S : Finset X) → S.card = 4 → Split ↥S → ℝ

/-- **CASTER 得分**：所有 4-元集上选定 quartet 的权重之和（正文式 (1)）。 -/
noncomputable def casterScore (W : WeightTable X) (q : QuartetChoice X) : ℝ :=
  ∑ S : {S : Finset X // S.card = 4}, W S.1 S.2 (q S.1 S.2)

/-- **真选择**（模 `swap`，即无向意义下与真树一致）。 -/
def IsTrueQ (qtrue q : QuartetChoice X) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4), q S hS = qtrue S hS ∨ q S hS = (qtrue S hS).swap

/-- **理想模型**（= 定理 1 的三条前提里的第三条，由命题 B 供给）：

* `W` —— 理论期望权重表（无向：`W_swap`）；
* `qtrue` —— 真树的 quartet 选择；
* `propB` —— **命题 B**：真拓扑的期望权重在每个 4-元集上**严格**最大。

（前两条前提「独立性」与「有界性」体现在 `CASTERSampling.converges` 里，见文件头。） -/
structure CASTERIdeal (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 理论期望权重表。 -/
  W : WeightTable X
  /-- 权重只看无向拓扑：交换两侧不改权重。 -/
  W_swap : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S), W S hS r.swap = W S hS r
  /-- 真树的 quartet 选择。 -/
  qtrue : QuartetChoice X
  /-- ★ **命题 B**（由 `Phylo.Stat.CASTEREngine` 供给）。 -/
  propB : ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
    r ≠ qtrue S hS → r ≠ (qtrue S hS).swap → W S hS r < W S hS (qtrue S hS)

namespace CASTERIdeal

variable (M : CASTERIdeal X)

/-- **逐点弱最大**（`propB` 的 `≤` 形式，`swap` 那一支取等号）。 -/
theorem W_le (S : Finset X) (hS : S.card = 4) (r : Split ↥S) :
    M.W S hS r ≤ M.W S hS (M.qtrue S hS) := by
  by_cases h1 : r = M.qtrue S hS
  · rw [h1]
  · by_cases h2 : r = (M.qtrue S hS).swap
    · rw [h2, M.W_swap]
    · exact (M.propB S hS r h1 h2).le

/-- ★★ **理想情形下真选择得分最大**（逐点求和）。 -/
theorem casterScore_le (q : QuartetChoice X) :
    casterScore M.W q ≤ casterScore M.W M.qtrue :=
  Finset.sum_le_sum (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    fun S _ => M.W_le S.1 S.2 (q S.1 S.2)

/-- **非真选择必在某处严格小**（`¬IsTrueQ` 的展开式）。 -/
theorem exists_strict_of_not_true {q : QuartetChoice X} (h : ¬ IsTrueQ M.qtrue q) :
    ∃ (S : Finset X) (hS : S.card = 4),
      q S hS ≠ M.qtrue S hS ∧ q S hS ≠ (M.qtrue S hS).swap := by
  by_contra hc
  apply h
  intro S hS
  by_cases h1 : q S hS = M.qtrue S hS
  · exact Or.inl h1
  · refine Or.inr ?_
    by_contra h2
    exact hc ⟨S, hS, h1, h2⟩

/-- ★★★ **非真选择的得分严格小于真选择**。 -/
theorem casterScore_lt_of_not_true {q : QuartetChoice X} (h : ¬ IsTrueQ M.qtrue q) :
    casterScore M.W q < casterScore M.W M.qtrue := by
  obtain ⟨S, hS, h1, h2⟩ := M.exists_strict_of_not_true h
  exact Finset.sum_lt_sum
    (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    (fun S1 _ => M.W_le S1.1 S1.2 (q S1.1 S1.2))
    ⟨⟨S, hS⟩, Finset.mem_univ _, M.propB S hS (q S hS) h1 h2⟩

/-! ## 2. ② gap 引理 -/

/-- ★★ **得分 gap**：存在统一的 `δ > 0`，使任何非真选择的得分至少比真选择低 `δ`。

由**有限性**（`QuartetChoice X` 有限）取「真得分 − 各非真得分」的最小值。 -/
theorem exists_gap (hNE : ∃ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q →
      casterScore M.W q + δ ≤ casterScore M.W M.qtrue := by
  classical
  obtain ⟨q0, hq0⟩ := hNE
  set S : Finset ℝ := ((Finset.univ : Finset (QuartetChoice X)).filter
      (fun q => ¬ IsTrueQ M.qtrue q)).image
      (fun q => casterScore M.W M.qtrue - casterScore M.W q) with hSdef
  have hne : S.Nonempty := by
    refine ⟨casterScore M.W M.qtrue - casterScore M.W q0, ?_⟩
    rw [hSdef]
    exact Finset.mem_image.mpr
      ⟨q0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq0⟩, rfl⟩
  refine ⟨S.min' hne, ?_, ?_⟩
  · obtain ⟨q1, hq1, heq⟩ := Finset.mem_image.mp (S.min'_mem hne)
    rw [← heq]
    have := M.casterScore_lt_of_not_true (Finset.mem_filter.mp hq1).2
    linarith
  · intro q hq
    have hmem : casterScore M.W M.qtrue - casterScore M.W q ∈ S := by
      rw [hSdef]
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    have h1 : S.min' hne ≤ casterScore M.W M.qtrue - casterScore M.W q := S.min'_le _ hmem
    linarith

end CASTERIdeal

/-! ## 3. ③ 稳定性 -/

/-- **频率/权重的 `ε`-接近**（逐点，两个权重表之间）。 -/
def WeightClose (W W' : WeightTable X) (ε : ℝ) : Prop :=
  ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S), |W S hS r - W' S hS r| < ε

theorem WeightClose_symm {W W' : WeightTable X} {ε : ℝ} (h : WeightClose W W' ε) :
    WeightClose W' W ε :=
  fun S hS r => by rw [abs_sub_comm]; exact h S hS r

/-- **扰动下的得分比较上界**：`score_W(q) ≤ score_{W'}(q) + N·ε`（`N` = 4-元集个数）。 -/
theorem casterScore_le_add (W W' : WeightTable X) (q : QuartetChoice X) {ε : ℝ}
    (hW : WeightClose W W' ε) :
    casterScore W q ≤ casterScore W' q + ε * (Fintype.card {S : Finset X // S.card = 4}) := by
  have hdiff : casterScore W q - casterScore W' q ≤
      ε * (Fintype.card {S : Finset X // S.card = 4}) := by
    rw [casterScore, casterScore, ← Finset.sum_sub_distrib]
    calc (Finset.univ : Finset {S : Finset X // S.card = 4}).sum
          (fun S => W S.1 S.2 (q S.1 S.2) - W' S.1 S.2 (q S.1 S.2))
        ≤ (Finset.univ : Finset {S : Finset X // S.card = 4}).sum (fun _ => ε) :=
          Finset.sum_le_sum fun S _ => le_trans (le_abs_self _) (hW S.1 S.2 (q S.1 S.2)).le
      _ = ε * (Fintype.card {S : Finset X // S.card = 4}) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  linarith

/-- ★★★ **稳定性**：若经验权重与理论权重的逐点扰动 `ε < δ/(2N+1)`，
则任何在经验权重上得分不低于真选择的选择，**必是真选择**。 -/
theorem caster_stable_argmax (M : CASTERIdeal X) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q →
      casterScore M.W q + δ ≤ casterScore M.W M.qtrue)
    {W : WeightTable X}
    (hW : WeightClose W M.W (δ / (2 * (Fintype.card {S : Finset X // S.card = 4}) + 1)))
    {q : QuartetChoice X}
    (hmax : casterScore W M.qtrue ≤ casterScore W q) : IsTrueQ M.qtrue q := by
  by_contra hnot
  set N : ℝ := (Fintype.card {S : Finset X // S.card = 4} : ℝ) with hNdef
  have hN0 : (0 : ℝ) ≤ N := by rw [hNdef]; exact Nat.cast_nonneg _
  set ε : ℝ := δ / (2 * N + 1) with hεdef
  have hN1 : (2 : ℝ) * N + 1 ≠ 0 := by linarith
  have hεN : ε * (2 * N + 1) = δ := by rw [hεdef, div_mul_cancel₀ _ hN1]
  have h1 : casterScore W q ≤ casterScore M.W q + ε * N := casterScore_le_add W M.W q hW
  have h2 : casterScore M.W M.qtrue ≤ casterScore W M.qtrue + ε * N :=
    casterScore_le_add M.W W M.qtrue (WeightClose_symm hW)
  have h3 : casterScore M.W q + δ ≤ casterScore M.W M.qtrue := hgap q hnot
  have h4 : 2 * ε * N < δ := by rw [← hεN]; nlinarith
  linarith

/-! ## 4. ④ 大数定律（公理化）与定理 1 -/

/-- **（公理化）CASTER 采样 + 大数定律**。

* `emp W n` —— 在**理论权重表 `W`** 下、`n` 个位点的**经验平均权重表**；
* `converges` —— **大数定律**：经验平均最终逐点 `ε`-接近**该表** `W`。

📌 **形状说明（2026-10-09 修正）**：`emp` **必须依赖理论权重表 `W`**。
早期版本写成 `ℕ → WeightTable X`（不依赖 `W`），而 `converges` 却对**所有**
`W : WeightTable X` 断言 —— **任意两张不同的权重表**就足以矛盾（比 `MSC` 侧更严重，
连「两个模型」都不需要），该结构因此是**空类型**
（历史上由 `Phylo.Stat.SamplingAxiomVacuity` 证明，并有 `Fin 4` 上的**无条件**实例）。
现按「在理论表下采样」的语义修正，并由 `casterSampling_nonempty` 给出显式居民。

⚠️ 与 `Phylo.Stat.MSC` 的 `MSCSampling.converges` 同一层：取「最终 `ε`-接近」的
**确定性**形式，把「几乎必然收敛」抽象掉。**有界性**（正文条件 2）折叠在这里。 -/
structure CASTERSampling (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 在**理论权重表 `W`** 下，`n` 个位点的经验平均权重表。 -/
  emp : WeightTable X → ℕ → WeightTable X
  /-- ★ **大数定律**（公理化）：在 `W` 下，经验平均最终 `ε`-接近 `W`。 -/
  converges : ∀ W : WeightTable X, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, WeightClose (emp W n) W ε

/-- ★★★ **`CASTERSampling` 非空洞**（理想样本 `emp W n := W`）。 -/
theorem casterSampling_nonempty (X : Type u) [Fintype X] [DecidableEq X] :
    Nonempty (CASTERSampling.{u} X) :=
  ⟨{ emp := fun W _ => W
     converges := fun W ε hε =>
       ⟨0, fun _ _ S hS r => by
         show |W S hS r - W S hS r| < ε
         rw [sub_self, abs_zero]
         exact hε⟩ }⟩

/-- ★★★ **CASTER 定理 1（统计一致性，quartet 层面）**。

设真树的 quartet 期望权重表满足**命题 B**（`M`），`sm` 是满足大数定律的采样，
`E n` 是第 `n` 个样本上的**得分最大化者**，则最终 `E n` 与真树**逐 quartet 一致**（模 `swap`）。

**证明**：`exists_gap` 给统一 gap `δ`；取 `ε = δ/(2N+1)` 用大数定律；
`stable_argmax` 把「得分最大化」转成「真选择」。 -/
theorem caster_statisticallyConsistent (M : CASTERIdeal X) (sm : CASTERSampling X)
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueQ M.qtrue q)
    {E : ℕ → QuartetChoice X}
    (hE : ∀ n : ℕ, ∀ q : QuartetChoice X,
      casterScore (sm.emp M.W n) q ≤ casterScore (sm.emp M.W n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueQ M.qtrue (E n) := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := M.exists_gap hNE
  set K : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges M.W (δ / K) (div_pos hδ hKpos)
  refine ⟨N, fun n hn => ?_⟩
  refine caster_stable_argmax M hδ hgap (W := sm.emp M.W n) ?_ ?_
  · simpa [hKdef] using hN n hn
  · exact hE n M.qtrue
