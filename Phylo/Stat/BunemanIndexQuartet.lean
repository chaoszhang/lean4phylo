/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.BunemanIndexBridge

/-!
# `Phylo.Stat.BunemanIndexQuartet` —— W30 泳道 b：(B) ⇒ `isolationIndex = 2·λ`

## 本文件证什么

`Phylo/SplitWeak.lean` §9 证成 **(B)**（`Split.quartetAvoidingND_of_weaklyCompatible`）：
弱相容族里，对两侧都 `≥ 2` 的成员 `s`，存在**非退化**四元组
`a ≠ a' ∈ s.sideA`、`b ≠ b' ∈ s.sideB`，使 `F` 中除 `s`、`s.swap` 外无成员 W-分离它。

本文件把 (B) 接到隔离指数（`weakCompatibilityRealization_gap_weights_v2` 的第二合取项，
在两侧都 `≥ 2` 的成员上）：

```
isolationIndex (sumMetric F w) s.sideA s.sideB = 2 * (w s + [s.swap ∈ F]·w s.swap)
```

并给出 **`α_s` 在非退化四元组上取到**（`exists_nondegenerate_quartet_attaining`）——
这正是 BdD Theorem 1 / Corollary 1 的适用前提。

## 链条（每一步用的都是库内**已有**定理；因子 `2` 已重算）

1. 取 (B) 给的四元组 `(a,a',b,b')`；
2. `isolationIndex_le_pairDeficit`（`BunemanIndexBridge:995`，`inf'` ⇒ ≤ 任一四元组值）给 `α_s ≤ pd`；
3. `pairDeficit_sum_eq`（`:4665`）给 `pd = 2·max (cW − cP) (cW − cX)`；
4. 弱相容 ⇒ `cP = 0 ∨ cX = 0`（`crossWeight_eq_zero_or`，从 `:4733-4745` 抽出）⇒ `pd = 2·cW`；
   ★ 因子 `2`：每个分离成员贡献 `2λ`（两条交叉边各一次），与
   `isolationIndex_weights_singleton`（`:4629`）的 `α_s = 2·w s` 标定一致；
5. (B) ⇒ `F.filter (qPairW · a a' b b') = {s} ∪ ([s.swap ∈ F]·{s.swap})`
   ⇒ `cW = w s + [s.swap ∈ F]·w s.swap`；
6. 与 `isolationIndex_ge_two_mul_weight`（`:4706`）的 `≥` 一夹 ⇒ 等式。

## 诚实边界

* 结论要求 `2 ≤ |s.sideA|` 且 `2 ≤ |s.sideB|`。**单点侧**（`|sideA| = 1` 或 `|sideB| = 1`）
  不在 (B) 的覆盖范围内（那里不存在非退化四元组），其 `α_s = 2λ_s` 另需论证
  —— 见 `.w30/report_b.md` 的「卡点」。`_v2` 的第二合取项因此在**单点侧成员**上尚未收口。
* 库内 `isolationIndex`、`pairDeficit` **均无 `½`**（`isolationIndex = 2·α_BDD`），
  故 (B) ⇒ `α_s = 2λ_s` 不需要任何 `×2 / ÷2` 换算。
-/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- ★★★ **弱相容 ⇒ 两个交叉配对的权重和至少一个为 `0`**（从 `isolationIndex_ge_two_mul_weight`
的证明体（`:4733-4745`）抽出；名字不带 `gap`）。

需要**一个 W-实现者**为前提（弱相容只禁止三种配对**同时**被实现；原证明里由 `s` 提供）。 -/
theorem crossWeight_eq_zero_or (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u) {a a' b b' : α}
    (hW : ∃ u ∈ F, qPairW u a a' b b' = true) :
    ((∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u) = 0 ∨
        (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u) = 0) := by
  by_contra hcon
  have hcon1 : (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u) ≠ 0 :=
    fun h => hcon (Or.inl h)
  have hcon2 : (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u) ≠ 0 :=
    fun h => hcon (Or.inr h)
  set cP : ℝ := ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u with hcP
  set cX : ℝ := ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u with hcX
  have hcP0 : 0 ≤ cP :=
    Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hcX0 : 0 ≤ cX :=
    Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hPpos : 0 < cP := lt_of_le_of_ne hcP0 (Ne.symm hcon1)
  have hXpos : 0 < cX := lt_of_le_of_ne hcX0 (Ne.symm hcon2)
  have hneP : (F.filter (fun u => qPairP u a a' b b' = true)).Nonempty := by
    rw [hcP] at hPpos
    exact Finset.nonempty_of_sum_ne_zero (ne_of_gt hPpos)
  have hneX : (F.filter (fun u => qPairX u a a' b b' = true)).Nonempty := by
    rw [hcX] at hXpos
    exact Finset.nonempty_of_sum_ne_zero (ne_of_gt hXpos)
  obtain ⟨v, hv⟩ := hneP
  obtain ⟨z, hz⟩ := hneX
  obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
  obtain ⟨hzF, hzX⟩ := Finset.mem_filter.mp hz
  obtain ⟨t, htF, htW⟩ := hW
  exact hF ⟨a, a', b, b',
    ⟨t, by simpa using htF, (qPairW_eq_true_iff t a a' b b').mp htW⟩,
    ⟨v, by simpa using hvF, (qPairP_eq_true_iff v a a' b b').mp hvP⟩,
    ⟨z, by simpa using hzF, (qPairX_eq_true_iff z a a' b b').mp hzX⟩⟩

/-- ★★★★ **避让四元组的四点亏损恰为 `2λ`**：`pd = 2·(w s + [s.swap ∈ F]·w s.swap)`。

（这就是派工书 §2.2 里 `pd = 2(λ₀ − min{λ₁,λ₂})` 的**精确**形态：`λ₀ = λ_s`、`min = 0`。） -/
theorem pairDeficit_eq_two_mul_of_quartetAvoiding (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u)
    {s : Split α} (hs : s ∈ F) {a a' b b' : α}
    (ha : a ∈ s.sideA) (ha' : a' ∈ s.sideA) (hb : b ∈ s.sideB) (hb' : b' ∈ s.sideB)
    (havoid : ∀ u ∈ F, u ≠ s → u ≠ s.swap → ¬ u.Separates a a' b b') :
    pairDeficit (sumMetric F w) a a' b b'
      = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
  classical
  have hsepS : s.Separates a a' b b' := Or.inl ⟨ha, ha', hb, hb'⟩
  have hWwit : ∃ u ∈ F, qPairW u a a' b b' = true :=
    ⟨s, hs, (qPairW_eq_true_iff s a a' b b').mpr hsepS⟩
  have hkey : ∀ u ∈ F, u.Separates a a' b b' → u = s ∨ u = s.swap := by
    intro u huF hsep
    by_contra hc
    exact havoid u huF (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h)) hsep
  have hfilter : F.filter (fun u => qPairW u a a' b b' = true)
      = ({s} : Finset (Split α)) ∪ (if s.swap ∈ F then {s.swap} else ∅) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨huF, huW⟩
      rcases hkey u huF ((qPairW_eq_true_iff u a a' b b').mp huW) with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        by_cases hsw : s.swap ∈ F
        · exact Or.inr (by simp [hsw])
        · rw [h] at huF
          exact absurd huF hsw
    · rintro (h | h)
      · rw [h]
        exact ⟨hs, (qPairW_eq_true_iff s a a' b b').mpr hsepS⟩
      · by_cases hsw : s.swap ∈ F
        · have hu : u = s.swap := by simpa [hsw] using h
          rw [hu]
          refine ⟨hsw, (qPairW_eq_true_iff s.swap a a' b b').mpr (Or.inr ⟨?_, ?_, ?_, ?_⟩)⟩
          · rw [Split.swap_sideB]; exact ha
          · rw [Split.swap_sideB]; exact ha'
          · rw [Split.swap_sideA]; exact hb
          · rw [Split.swap_sideA]; exact hb'
        · simp [hsw] at h
  have hcW : (∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
      = w s + (if s.swap ∈ F then w s.swap else 0) := by
    rw [hfilter]
    split_ifs with hsw
    · rw [Finset.sum_union]
      · rw [Finset.sum_singleton, Finset.sum_singleton]
      · rw [Finset.disjoint_singleton_left, Finset.mem_singleton]
        exact (swap_ne s).symm
    · rw [Finset.union_empty, Finset.sum_singleton]
      ring
  have hpd : pairDeficit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) a a' b b'
      = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
    rw [pairDeficit_sum_eq]
    set cW : ℝ := ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u with hCW
    set cP : ℝ := ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u with hCP
    set cX : ℝ := ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u with hCX
    have hcP0 : 0 ≤ cP :=
      Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
    have hcX0 : 0 ≤ cX :=
      Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
    have hzero : cP = 0 ∨ cX = 0 := crossWeight_eq_zero_or F w hF hw hWwit
    have hmax : max (cW - cP) (cW - cX) = cW := by
      rcases hzero with h | h
      · rw [h, sub_zero]; exact max_eq_left (by linarith)
      · rw [h, sub_zero]; exact max_eq_right (by linarith)
    rw [hmax, hcW]
  exact hpd

/-- ★★★★★ **W30 泳道 b 主结论**：弱相容 ＋ 正权重 ⇒ 两侧都 `≥ 2` 的成员 `s` 的隔离指数
恰为 `2·(w s + [s.swap ∈ F]·w s.swap)`（= `_v2` 第二合取项在该情形）。 -/
theorem isolationIndex_eq_two_mul_weight_of_quartetAvoiding
    (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u)
    {s : Split α} (hs : s ∈ F) (hA : 2 ≤ s.sideA.card) (hB : 2 ≤ s.sideB.card) :
    isolationIndex (sumMetric F w) s.sideA s.sideB
      = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
  classical
  obtain ⟨a, ha, a', ha', b, hb, b', hb', hne, hne', havoid⟩ :=
    quartetAvoidingND_of_weaklyCompatible F s hs hF hA hB
  have hpd := pairDeficit_eq_two_mul_of_quartetAvoiding F w hF hw hs ha ha' hb hb' havoid
  have hle : isolationIndex (sumMetric F w) s.sideA s.sideB
      ≤ 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
    calc isolationIndex (sumMetric F w) s.sideA s.sideB
        ≤ pairDeficit (sumMetric F w) a a' b b' :=
          isolationIndex_le_pairDeficit (sumMetric F w) (s.nonempty 0) (s.nonempty 1)
            ha ha' hb hb'
      _ = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := hpd
  have hge : 2 * (w s + (if s.swap ∈ F then w s.swap else 0))
      ≤ isolationIndex (sumMetric F w) s.sideA s.sideB :=
    isolationIndex_ge_two_mul_weight F w hF hw hs
  linarith

/-- ★★★★★ **非退化极值四元组存在**（BdD Theorem 1 / Corollary 1 的**适用前提**）：
两侧都 `≥ 2` 的成员 `s`，`α_s` 在某个**非退化**四元组上**取到**。

由 `isolationIndex_eq_two_mul_weight_of_quartetAvoiding` ＋ 避让四元组的 `pd = 2λ` 立得。 -/
theorem exists_nondegenerate_quartet_attaining (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u)
    {s : Split α} (hs : s ∈ F) (hA : 2 ≤ s.sideA.card) (hB : 2 ≤ s.sideB.card) :
    ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
      a ≠ a' ∧ b ≠ b' ∧
        isolationIndex (sumMetric F w) s.sideA s.sideB
          = pairDeficit (sumMetric F w) a a' b b' := by
  classical
  obtain ⟨a, ha, a', ha', b, hb, b', hb', hne, hne', havoid⟩ :=
    quartetAvoidingND_of_weaklyCompatible F s hs hF hA hB
  refine ⟨a, ha, a', ha', b, hb, b', hb', hne, hne', ?_⟩
  rw [isolationIndex_eq_two_mul_weight_of_quartetAvoiding F w hF hw hs hA hB]
  exact (pairDeficit_eq_two_mul_of_quartetAvoiding F w hF hw hs ha ha' hb hb' havoid).symm

/-- ★★★★★★★ **W30 泳道 b 收官：`_v2` 第二合取项的等式对 `F` 的每个成员成立**。 -/
theorem isolationIndex_eq_two_mul_weight (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u)
    {s : Split α} (hs : s ∈ F) :
    isolationIndex (sumMetric F w) s.sideA s.sideB
      = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
  classical
  have hge : 2 * (w s + (if s.swap ∈ F then w s.swap else 0))
      ≤ isolationIndex (sumMetric F w) s.sideA s.sideB :=
    isolationIndex_ge_two_mul_weight F w hF hw hs
  rcases Nat.lt_or_ge s.sideA.card 2 with hA2 | hA2
  · have hA1 : s.sideA.card = 1 := le_antisymm (by omega) (s.nonempty 0).card_pos
    obtain ⟨a, hAeq⟩ := Finset.card_eq_one.mp hA1
    rcases Nat.lt_or_ge s.sideB.card 2 with hB2 | hB2
    · -- 两侧都单点
      have hB1 : s.sideB.card = 1 := le_antisymm (by omega) (s.nonempty 1).card_pos
      obtain ⟨b, hBeq⟩ := Finset.card_eq_one.mp hB1
      obtain ⟨a', ha', b', hb', havoid⟩ := both_singleton_avoiding hAeq hBeq
      have hpd := pairDeficit_eq_two_mul_of_quartetAvoiding F w hF hw hs ha' ha' hb' hb' havoid
      have hle : isolationIndex (sumMetric F w) s.sideA s.sideB
          ≤ 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
        calc isolationIndex (sumMetric F w) s.sideA s.sideB
            ≤ pairDeficit (sumMetric F w) a' a' b' b' :=
              isolationIndex_le_pairDeficit (sumMetric F w) (s.nonempty 0) (s.nonempty 1)
                ha' ha' hb' hb'
          _ = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := hpd
      linarith
    · -- `sideA` 单点、`sideB` ≥ 2
      have hBpos : 2 ≤ s.sideB.card := hB2
      obtain ⟨a', ha', b', hb', b'', hb'', hne, havoid⟩ :=
        singleSideAvoiding_of_sideA_singleton F s hF ⟨a, hAeq⟩ hBpos
      have hpd := pairDeficit_eq_two_mul_of_quartetAvoiding F w hF hw hs ha' ha' hb' hb'' havoid
      have hle : isolationIndex (sumMetric F w) s.sideA s.sideB
          ≤ 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
        calc isolationIndex (sumMetric F w) s.sideA s.sideB
            ≤ pairDeficit (sumMetric F w) a' a' b' b'' :=
              isolationIndex_le_pairDeficit (sumMetric F w) (s.nonempty 0) (s.nonempty 1)
                ha' ha' hb' hb''
          _ = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := hpd
      linarith
  · rcases Nat.lt_or_ge s.sideB.card 2 with hB2 | hB2
    · -- `sideB` 单点、`sideA` ≥ 2
      have hB1 : s.sideB.card = 1 := le_antisymm (by omega) (s.nonempty 1).card_pos
      obtain ⟨b, hBeq⟩ := Finset.card_eq_one.mp hB1
      obtain ⟨b', hb', a', ha', a'', ha'', hne, havoid⟩ :=
        singleSideAvoidingB_of_sideB_singleton F s hF ⟨b, hBeq⟩ hA2
      have hpd := pairDeficit_eq_two_mul_of_quartetAvoiding F w hF hw hs ha' ha'' hb' hb' havoid
      have hle : isolationIndex (sumMetric F w) s.sideA s.sideB
          ≤ 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := by
        calc isolationIndex (sumMetric F w) s.sideA s.sideB
            ≤ pairDeficit (sumMetric F w) a' a'' b' b' :=
              isolationIndex_le_pairDeficit (sumMetric F w) (s.nonempty 0) (s.nonempty 1)
                ha' ha'' hb' hb'
          _ = 2 * (w s + (if s.swap ∈ F then w s.swap else 0)) := hpd
      linarith
    · exact isolationIndex_eq_two_mul_weight_of_quartetAvoiding F w hF hw hs hA2 hB2

/-! ## W30 泳道 b：`_v2` 第一合取项的装配

`⟸`：成员（及 `swap`）是 d-split —— `Split.isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible`（`SplitWeak:975`）。
`⟹`：非成员（`s ∉ F`、`s.swap ∉ F`）⇒ `¬IsDSplit` —— **`Split.core_holds`**（`SplitWeak:2539`，
即 `weakCompatibilityNonMemberCore` 的收口定理：W27-b 的「按 `|X|` 强归纳 ＋ 三个 `u_b` 冲突」路线）。

★ 这里**没有**用 (B)：非成员半边要的是 `λ₀ = 0`（`core`），与 (B) 的 `λ₀ = λ_s` 互为对偶但**不等价**。 -/

/-- ★★★★★★★ **W30 泳道 b 收口**：`weakCompatibilityRealization_gap_weights_v2` **成立**
（原 `def`（`BunemanIndexBridge:4844`）**逐字未改**）。

* 第一合取项：`⟸` = `SplitWeak:975`；`⟹` = `Split.core_holds`（`:2539`）；
* 第二合取项：`isolationIndex_eq_two_mul_weight`（本文件，`∀ s ∈ F`，含单点侧）。 -/
theorem weakCompatibilityRealization_gap_weights_v2_holds :
    weakCompatibilityRealization_gap_weights_v2 := by
  intro α instF instD F w hF hw
  refine ⟨?_, fun s hs => isolationIndex_eq_two_mul_weight F w hF hw hs⟩
  intro s
  constructor
  · intro hD
    by_contra hcon
    have hs : s ∉ F := fun hh => hcon ⟨s, hh, Or.inl rfl⟩
    have hss : s.swap ∉ F := fun hh => hcon ⟨s.swap, hh, Or.inr (by simp)⟩
    exact core_holds F w hF hw s hs hss hD
  · rintro ⟨t, htF, h | h⟩
    · exact isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible F w hF hw
        (Or.inl (h ▸ htF))
    · exact isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible F w hF hw
        (Or.inr (by rw [show s.swap = t by rw [← h, swap_swap]]; exact htF))
end Split
