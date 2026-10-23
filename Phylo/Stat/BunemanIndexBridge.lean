/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.SplitWeak
import Phylo.BunemanTree

/-!
# `Phylo.Stat.BunemanIndexBridge` —— 隔离指数（`bunemanIndex`）与 d-split 的接口

## ★D 结论（先说结论：字面桥是**假**的）

任务要求证「`Split.IsDSplit δ A B ↔ 0 < bunemanIndex δ …`（Buneman 1971 / BdD 1992 Thm 1 的
『d-split ⟺ 正隔离指数』）」作为解锁 `weakCompatibilityRealization` / `canonicalSplitDecomposition` /
`fourPointCharacterization` 的钥匙。**核命题后该字面命题为假**：

* `Split.IsDSplit`（`Phylo/SplitWeak.lean:259`）用的是 **`max` 形式**：每个四元组只需
  **两个配对中至少一个**为正：`LHS < max (δ a b + δ a' b') (δ a b' + δ a' b)`；
* `bunemanIndex`（`Phylo/BunemanTree.lean:107`）取的是 **`min` 形式**：`inf'` 遍历
  `sideA × sideA` 与 `sideB × sideB` 的**有序**对，故「平行配对」与「交叉配对」**都**在 `inf'` 内
  ⇒ `0 < bunemanIndex` 等价于「**两个配对都为正**」（= BdD p. 51 的措辞）。

⚠️ 顺带更正 `Phi/SplitWeak.lean:259` 的 docstring：它写「隔离指数取 `min`，故「`min > 0`」⟺「逐对全为正」」——
「逐对全为正」若指 `max > 0`（即 `IsDSplit` 本身），则该等价**不成立**（见本文件反例）；
它成立的对象是**两个配对都为正**的强形式（`IsDSplitStrong`）。

★★★ **W25-b ★D 校正（四要素；推翻上面的「`IsDSplit` 不忠实」判断）**

* **旧判断（作废）**：BdD 的 d-split（= 隔离指数 `α_{A,B} > 0`）是 `min` 形 ⇒ `IsDSplit`（`max` 形）
  **不忠实**，`IsDSplitStrong` 才是 `α > 0`；
* **新判断**：BdD 的 `α := min{max{d(a,b)+d(a',b'), d(a,b')+d(a',b), d(a,a')+d(b,b')} − d(a,a') − d(b,b')}`
  的 `max` **含内部项** ⇒ `α_{A,B} = max(min{max{P,Q} − I}, 0)` ⇒
  `α_{A,B} > 0 ⟺ ∀ 四元组 max{P,Q} > I` ⟺ **`IsDSplit`（`max` 形）** ✓ ⇒ **`IsDSplit` 是忠实的**；
  `IsDSplitStrong` ≡ `bunemanIndex` = **Buneman 1971 p. 390 的 `μ_σ`**（两项 `min`），**不是** BdD 的 `α`；
* **文献行号**：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:438-440`（d-split ⟺ 隔离指数为正）
  ＋ `:446-454`（三项 `max` 的 `α` 定义，第三项 `d(a,a')+d(b,b')` **在 `max` 内**）
  ＋ `:673-684`（split-prime = 隔离指数**恰为 `0`**）；
* **理由（真假判据，非措辞）**：两项 `min` 形可取**负值** ⇒ `:673-684` 的「isolation index `0`」
  无法刻画 split-prime；且 `:438-440` 会与 `:446` 的三项 `max` 自相矛盾。
  ⇒ **本节结论不变**（字面桥 `IsDSplit ↔ 0 < bunemanIndex` 仍**为假**，但原因是
  `bunemanIndex` 是 `μ` 而非 `α`，**不是** `IsDSplit` 不忠实）；连带：
  `SplitPrimeStd` 是**弱化**的 split-prime，忠实形态登记为 `§8.1` 的 `SplitPrimeFaithful`。

## 交付（零未证占位符、零新公理）

1. `Split.IsDSplitStrong` —— **Buneman 1971 `μ_σ > 0`** 的等价形式（两项 `min` 形）；
   ★D 校正后：它**不是** BdD 的 `α_{A,B} > 0`（后者 ⟺ `IsDSplit`，见上）；
2. ★★★ `bunemanIndex_pos_iff_isDSplitStrong` —— **真正的桥**：
   `0 < bunemanIndex δ s ↔ IsDSplitStrong δ.val s.sideA s.sideB`；
   单向推论 `isDSplit_of_bunemanIndex_pos`（`α > 0 ⇒ IsDSplit`，`max` 形式）；
3. ★B `not_isDSplit_implies_bunemanIndex_pos` —— **形式化反例**：存在 `δ : Dissimilarity (Fin 4)`
   与 split `{0,1}|{2,3}`，使 `IsDSplit` 成立而 `bunemanIndex < 0`。

文献行：Bandelt–Dress 1992 第 **496–510** 行（p. 51：tree metric 的 d-split 条件是
`d(a,a')+d(b,b') < d(a,b)+d(a',b') = d(a,b')+d(b,a')`，**两边同时**严格 ⇒ `min` 形式）；
第 **1651–1655** 行（Thm 2）、第 **1683–1699** 行（Thm 3）。
-/

open Finset

namespace Split

/-- **强 d-split**（≡ **Buneman 1971 p. 390 的 `μ_σ > 0`**，即「两项 `min` 形」）：对**每个**四元组
`a, a' ∈ A`、`b, b' ∈ B`，**两个配对都**严格为正。

⚠️ ★D 校正（W25-b，见 `§8.1` 与 `IsDSplit` 的 docstring）：这**不是** BdD 1992 的隔离指数 `α_{A,B} > 0`
—— BdD 的 `α` 的 `max{…}` 里**还含内部项** `d(a,a')+d(b,b')`（md `:446-454`），故
`α_{A,B} > 0 ⟺ IsDSplit`（`max` 形）；本 `def`（两项 `min`）**严格强于**它。
与 `Split.IsDSplit` 的差别：后者只要「两者之一」为正。 -/
def IsDSplitStrong {α : Type*} (δ : α → α → ℝ) (A B : Finset α) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B,
    δ a a' + δ b b' < δ a b + δ a' b' ∧ δ a a' + δ b b' < δ a b' + δ a' b

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 1. ★★★ 真正的桥：`bunemanIndex` 就是隔离指数 `α` -/

/-- ★★★ **`0 < bunemanIndex ⟺ IsDSplitStrong`**（「d-split ⟺ 正隔离指数」的**正确**形式）。

`bunemanQuadruples` 遍历**有序**对 `(a,a') ∈ A × A`、`(b,b') ∈ B × B`，
故「平行配对」与「交叉配对」都在 `inf'` 内 —— 这正是 `min` 形式。 -/
theorem bunemanIndex_pos_iff_isDSplitStrong (δ : NJ.Dissimilarity X) (s : Split X) :
    0 < δ.bunemanIndex s ↔ IsDSplitStrong δ.val s.sideA s.sideB := by
  constructor
  · intro h a ha a' ha' b hb b' hb'
    have h' := (δ.bunemanIndex_pos_iff s).mp h
    have hq : ((a, a'), (b, b')) ∈ NJ.Dissimilarity.bunemanQuadruples s := by
      simp only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product]
      exact ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩⟩
    have h1 := h' ((a, a'), (b, b')) hq
    have hq2 : ((a, a'), (b', b)) ∈ NJ.Dissimilarity.bunemanQuadruples s := by
      simp only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product]
      exact ⟨⟨ha, ha'⟩, ⟨hb', hb⟩⟩
    have h2 := h' ((a, a'), (b', b)) hq2
    simp only [NJ.Dissimilarity.bunemanQuad] at h1 h2
    rw [δ.symm b' b] at h2
    exact ⟨by linarith, by linarith⟩
  · intro h
    refine (δ.bunemanIndex_pos_iff s).mpr fun q hq => ?_
    obtain ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩ := by
      simpa only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product] using hq
    have h1 := (h q.1.1 hA q.1.2 hA' q.2.1 hB q.2.2 hB').1
    simp only [NJ.Dissimilarity.bunemanQuad]
    linarith

/-- ★★ **弱结论**：`α > 0 ⟹ IsDSplit`（`max` 形式；因为平行配对 ≤ `max`）。 -/
theorem isDSplit_of_bunemanIndex_pos (δ : NJ.Dissimilarity X) (s : Split X)
    (h : 0 < δ.bunemanIndex s) : IsDSplit δ.val s.sideA s.sideB := by
  intro a ha a' ha' b hb b' hb'
  exact lt_of_lt_of_le
    ((bunemanIndex_pos_iff_isDSplitStrong δ s).mp h a ha a' ha' b hb b' hb').1
    (le_max_left _ _)

/-! ## 2. ★B 反例：`IsDSplit` **推不出** `α > 0`

`X = Fin 4`，`s = {0,1}|{2,3}`，`δ` 取

```text
δ 0 1 = δ 2 3 = 1/2,   δ 0 2 = δ 1 3 = 1,   δ 0 3 = δ 1 2 = 1/10,   对角 = 0
```

`IsDSplit` 成立（16 组四元组全达标：`1/2 < 2`、`1/2 < 11/10`、`0 < 1/5`、`0 < 2`），
但四元组 `q = ((0,1),(3,2))` 给出
`bunemanQuad δ q = δ(0,3) + δ(1,2) − δ(0,1) − δ(3,2) = 1/10 + 1/10 − 1/2 − 1/2 = −4/5 < 0`
⇒ `bunemanIndex δ s ≤ −2/5 < 0`。 -/

/-- 反例用的对称函数（`Fin 4` 上的 4×4 表）。 -/
noncomputable def cexVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0
  | 0, 1 => 1 / 2
  | 0, 2 => 1
  | 0, 3 => 1 / 10
  | 1, 0 => 1 / 2
  | 1, 1 => 0
  | 1, 2 => 1 / 10
  | 1, 3 => 1
  | 2, 0 => 1
  | 2, 1 => 1 / 10
  | 2, 2 => 0
  | 2, 3 => 1 / 2
  | 3, 0 => 1 / 10
  | 3, 1 => 1
  | 3, 2 => 1 / 2
  | 3, 3 => 0

/-- 反例用的相异度（对称 + 零对角；`Dissimilarity` **不**要求三角不等式 ⇒ 合法）。 -/
noncomputable def cexDelta : NJ.Dissimilarity (Fin 4) where
  val := cexVal
  symm := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [cexVal]
  diag := by intro i; fin_cases i <;> norm_num [cexVal]

/-- 反例用的 split `{0,1}|{2,3}`。 -/
def cexSplit : Split (Fin 4) := ofSideA {0, 1} (by decide) (by decide)

/-- ★B 第一步：该 `δ` 对 `{0,1}|{2,3}` **满足 `IsDSplit`（`max` 形式）**。 -/
theorem cex_isDSplit : IsDSplit cexVal cexSplit.sideA cexSplit.sideB := by
  intro a ha a' ha' b hb b' hb'
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    simp_all [cexSplit, ofSideA_sideA, ofSideA_sideB, cexVal, max_def] <;> norm_num

/-- ★B 第二步：但 `bunemanIndex` **为负**（隔离指数取到负值）。 -/
theorem cex_bunemanIndex_neg : cexDelta.bunemanIndex cexSplit < 0 := by
  have hq : (((0, 1) : Fin 4 × Fin 4), ((3, 2) : Fin 4 × Fin 4))
      ∈ NJ.Dissimilarity.bunemanQuadruples cexSplit := by
    simp only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product, cexSplit,
      ofSideA_sideA, ofSideA_sideB, Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl]
    decide
  have h := cexDelta.bunemanIndex_le_quad cexSplit hq
  have hval : cexDelta.bunemanQuad (((0, 1), (3, 2))) = -(4 / 5) := by
    norm_num [NJ.Dissimilarity.bunemanQuad, cexDelta, cexVal]
  rw [hval] at h
  linarith


/-! ## 3. ★★★ 四点条件下 `max` 形式 = 强形式（= 隔离指数为正）

`IsDSplit`（`max`）与 `IsDSplitStrong`（`min`/双配对）一般**不等价**（§2 反例），
但若 `δ` 满足**四点条件**（`δ.FourPoint`），则三对和中最大者至少出现两次，
于是「`S1 < max S2 S3`」自动升级为「`S1 < S2 ∧ S1 < S3`」⇒ 两种形式一致。

⇒ **用途**：`fourPointCharacterization_gap` 的右边带 `FourPoint δ`，故可在那里安全地用
`bunemanIndex`（隔离指数）代替 `IsDSplit`；而 `weakCompatibilityRealization` /
`canonicalSplitDecomposition` 量化的是**任意对称** `δ`，那里必须改用 `IsDSplitStrong`
（或额外证明 `δ` 满足四点条件）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **四点条件下两种 d-split 形式一致**。 -/
theorem isDSplit_iff_isDSplitStrong_of_fourPoint (δ : NJ.Dissimilarity X) {A B : Finset X}
    (hfp : δ.FourPoint) : IsDSplit δ.val A B ↔ IsDSplitStrong δ.val A B := by
  constructor
  · intro h a ha a' ha' b hb b' hb'
    have h1 : δ.val a a' + δ.val b b'
        < max (δ.val a b + δ.val a' b') (δ.val a b' + δ.val a' b) :=
      h a ha a' ha' b hb b' hb'
    have hs2 : δ.val a b + δ.val a' b' ≤ δ.val a a' + δ.val b b' ∨
        δ.val a b + δ.val a' b' ≤ δ.val a b' + δ.val a' b := by
      rcases hfp a b a' b' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [δ.symm b a'] at h'; exact h')
    have hs3 : δ.val a b' + δ.val a' b ≤ δ.val a a' + δ.val b b' ∨
        δ.val a b' + δ.val a' b ≤ δ.val a b + δ.val a' b' := by
      rcases hfp a b' a' b with h' | h'
      · exact Or.inl (by rw [δ.symm b' b] at h'; exact h')
      · exact Or.inr (by rw [δ.symm b' a'] at h'; exact h')
    constructor
    · by_contra hcon
      have hcon2 : δ.val a b + δ.val a' b' ≤ δ.val a a' + δ.val b b' := not_lt.mp hcon
      have hS3 : δ.val a a' + δ.val b b' < δ.val a b' + δ.val a' b := by
        by_contra hc
        have hc2 : δ.val a b' + δ.val a' b ≤ δ.val a a' + δ.val b b' := not_lt.mp hc
        have : max (δ.val a b + δ.val a' b') (δ.val a b' + δ.val a' b)
            ≤ δ.val a a' + δ.val b b' := max_le hcon2 hc2
        linarith
      rcases hs3 with h' | h' <;> linarith
    · by_contra hcon
      have hcon2 : δ.val a b' + δ.val a' b ≤ δ.val a a' + δ.val b b' := not_lt.mp hcon
      have hS2 : δ.val a a' + δ.val b b' < δ.val a b + δ.val a' b' := by
        by_contra hc
        have hc2 : δ.val a b + δ.val a' b' ≤ δ.val a a' + δ.val b b' := not_lt.mp hc
        have : max (δ.val a b + δ.val a' b') (δ.val a b' + δ.val a' b)
            ≤ δ.val a a' + δ.val b b' := max_le hc2 hcon2
        linarith
      rcases hs2 with h' | h' <;> linarith
  · intro h a ha a' ha' b hb b' hb'
    exact lt_of_lt_of_le (h a ha a' ha' b hb b' hb').1 (le_max_left _ _)

/-! ## 4. `weakCompatibilityRealization_gap` 的「正确形态」（协调侧 W12j 要求）

原 `def weakCompatibilityRealization_gap`（`Phylo/SplitWeak.lean:392`）有三处不忠实，**其 `def` 原文未改**：

1. 参数 `w` 只出现在**假设**里、结论里完全不出现 ⇒ 即使证成也拿不到 BdD Thm 3 的
   「隔离指数 `α_S = w S`」（系数那一半）；
2. 结论用的 `IsDSplit` 是 **`max` 形式**，而 BdD 的 d-split 是 **`α > 0`**
   （§2 反例：两者在任意对称 `δ` 上**不等价**）；
3. `δ` 是**裸对称函数**（无 `δ(x,x) = 0`），而隔离指数的 `inf'` 会取到 `a = a'`、`b = b'`
   的项 —— BdD 的 setting 是 `d(x,x) = 0`。

故「正确形态」如下（用库内 `bunemanIndex` 表达隔离指数；`Dissimilarity` = 对称 + 零对角）。 -/

/-- ⬜ **正确形态（W12j 登记）**：`Σ` 弱相容 ⟹ 存在**对称零对角** `δ`，使 `Σ` 恰是
其**正隔离指数**的 split 集，且**隔离指数就是给定权重 `w`**、非成员的隔离指数为 `0`。

⚠️ **W25-a：本形态是假命题** ✗（本 `def` 原文**逐字未改**）—— 形式化反例见 §4.1 的
`weakCompatibilityRealization_gap_correct_shape_refuted`。病根：`bunemanIndex` 是 `μ`（`min` 形），
「`μ_t = 0`（非成员）」强迫 `t` 的**每个**四元组取值 `≥ 0`，与「`μ_s = w_s > 0`（成员）」在
对角四元组上互斥（`Fin 4`：`{0,1}|{2,3}` 与 `{0,2}|{1,3}`）。忠实形态须改用 `max` 形的
隔离指数 `α`（即 `IsDSplit` 一侧），不是 `bunemanIndex`。 -/
def weakCompatibilityRealization_gap_correct_shape : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    WeaklyCompatible (↑F : Set (Split α)) → (∀ s ∈ F, 0 < w s) →
      ∃ δ : NJ.Dissimilarity α,
        (∀ s : Split α, IsDSplitStrong δ.val s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s) ∧
          (∀ s ∈ F, δ.bunemanIndex s = w s) ∧
            (∀ s : Split α, s ∉ F → s.swap ∉ F → δ.bunemanIndex s = 0)

/-- ★B **结论（形式化反例）**：字面上的桥「`IsDSplit` ⇒ `0 < bunemanIndex`」是**假命题**。 -/
theorem not_isDSplit_implies_bunemanIndex_pos :
    ¬ (∀ (δ : NJ.Dissimilarity (Fin 4)) (s : Split (Fin 4)),
        IsDSplit δ.val s.sideA s.sideB → 0 < δ.bunemanIndex s) := by
  intro h
  have h1 := h cexDelta cexSplit cex_isDSplit
  linarith [cex_bunemanIndex_neg]


/-! ## 4.1 ★B **`weakCompatibilityRealization_gap_correct_shape` 是假命题**（W25-a 形式化反例）

§4 的「正确形态」把 BdD 的隔离指数 `α` 换成了库内 `bunemanIndex` —— 而 ★D 校正已认定后者是
**Buneman 1971 的 `μ_σ`（`min` 形）**，与 `α` 的关键差别：`μ` 是 `inf'`。于是

* 「`μ_s = w_s > 0`」（成员）⟹ `s` 的每个四元组取值 `> 0`；
* 「`μ_t = 0`」（非成员）⟹ `t` 的**每个**四元组取值都 `≥ 0`。

取 `s = {0,1}|{2,3}`（成员，权重 `1`）与 `t = {0,2}|{1,3}`（非成员，非其对换），则

```text
quad_s(((0,1),(2,3))) = δ(0,2) + δ(1,3) − δ(0,1) − δ(2,3)     -- 需 ≥ 2·μ_s = 2
quad_t(((0,2),(1,3))) = δ(0,1) + δ(2,3) − δ(0,2) − δ(1,3)     -- 需 ≥ 2·μ_t = 0
```

两者**互为相反数** ⇒ `0 ≥ 2`，矛盾。注意本反例**只用**了 `_correct_shape` 的第 2、3 个合取项，
**完全没碰**第 1 个合取项 ⇒ 把 `IsDSplitStrong` 换成 `IsDSplit`（或任何别的 d-split 谓词）
**同样为假**：病根在 `bunemanIndex`（`μ`）身上的那两条**等式**，不在 d-split 谓词的形态。

（对照：忠实形态应把这两条换成 `max` 形的隔离指数 `α` —— `α_t = 0` 只要求**某个**四元组的
两个交叉配对都 `≤` 内部配对，正是 BdD Thm 3 的取零机制，与成员的 `α_s > 0` 不冲突。） -/

/-- 反例用的第二个 split：`{0,2} | {1,3}`（与 `cexSplit = {0,1}|{2,3}` 及其对换都不同）。 -/
def cexSplit2 : Split (Fin 4) := ofSideA {0, 2} (by decide) (by decide)

/-- `cexSplit2` **不是**成员 `cexSplit`（比 `sideA = {0,2}` 与 `{0,1}`）。 -/
theorem cexSplit2_ne_cexSplit : cexSplit2 ≠ cexSplit := by
  intro h
  have h' := congrArg (fun s : Split (Fin 4) => s.sideA) h
  simp only [cexSplit2, cexSplit, ofSideA_sideA] at h'
  exact absurd h' (by decide)

/-- `cexSplit2.swap` 也**不是**成员 `cexSplit`（3 在 `cexSplit2.swap.sideA` 而 3 ∉ `cexSplit.sideA`）。 -/
theorem cexSplit2_swap_ne_cexSplit : cexSplit2.swap ≠ cexSplit := by
  intro h
  have h3 : (3 : Fin 4) ∈ cexSplit2.swap.sideA := by
    simp only [cexSplit2, swap_sideA, ofSideA_sideB]
    decide
  rw [h] at h3
  simp only [cexSplit, ofSideA_sideA] at h3
  exact absurd h3 (by decide)

/-- 单元族 `{cexSplit}` **弱相容**（冲突四点需要同一 `split` 在同一四点上诱导两个 2|2 split，
被 `Separates.exclusive` 禁止）。 -/
theorem weaklyCompatible_cexSplit :
    WeaklyCompatible (↑({cexSplit} : Finset (Split (Fin 4))) : Set (Split (Fin 4))) := by
  rintro ⟨a, b, c, e, ⟨u, hu, h1⟩, ⟨v, hv, h2⟩, _⟩
  have hu' : u = cexSplit := by simpa using hu
  have hv' : v = cexSplit := by simpa using hv
  rw [hu'] at h1
  rw [hv'] at h2
  exact Separates.exclusive h1 (Or.inl h2)

/-- ★B **核心矛盾**：`Fin 4` 上不存在相异度同时满足「`μ_{01|23} = 1`」与「`μ_{02|13} = 0`」。

两个四元组 `((0,1),(2,3))`、`((0,2),(1,3))` 的 `bunemanQuad` 取值**互为相反数**，而 `inf'` 的
上界性质（`bunemanIndex_le_quad`）把它们分别钉在 `≥ 2` 与 `≥ 0`。 -/
theorem no_bunemanIndex_pair (δ : NJ.Dissimilarity (Fin 4))
    (h1 : δ.bunemanIndex cexSplit = 1) (h2 : δ.bunemanIndex cexSplit2 = 0) : False := by
  have hq1 : (((0, 1) : Fin 4 × Fin 4), ((2, 3) : Fin 4 × Fin 4))
      ∈ NJ.Dissimilarity.bunemanQuadruples cexSplit := by
    simp only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product, cexSplit,
      ofSideA_sideA, ofSideA_sideB, Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl]
    decide
  have hq2 : (((0, 2) : Fin 4 × Fin 4), ((1, 3) : Fin 4 × Fin 4))
      ∈ NJ.Dissimilarity.bunemanQuadruples cexSplit2 := by
    simp only [NJ.Dissimilarity.bunemanQuadruples, Finset.mem_product, cexSplit2,
      ofSideA_sideA, ofSideA_sideB, Finset.mem_insert, Finset.mem_singleton, Finset.mem_compl]
    decide
  have hb1 := δ.bunemanIndex_le_quad cexSplit hq1
  have hb2 := δ.bunemanIndex_le_quad cexSplit2 hq2
  have hv1 : δ.bunemanQuad (((0, 1), (2, 3)))
      = δ.val 0 2 + δ.val 1 3 - δ.val 0 1 - δ.val 2 3 := by
    simp only [NJ.Dissimilarity.bunemanQuad]
  have hv2 : δ.bunemanQuad (((0, 2), (1, 3)))
      = δ.val 0 1 + δ.val 2 3 - δ.val 0 2 - δ.val 1 3 := by
    simp only [NJ.Dissimilarity.bunemanQuad]
  rw [h1, hv1] at hb1
  rw [h2, hv2] at hb2
  linarith

/-- ★B **`weakCompatibilityRealization_gap_correct_shape` 是假命题**（全称闭包为假：
`α = Fin 4`、`F = {{0,1}|{2,3}}`、`w ≡ 1` 处不存在实现的 `δ`）。

`def` 原文**逐字未改**；本定理只新增反例，核心矛盾在 `no_bunemanIndex_pair`。 -/
theorem weakCompatibilityRealization_gap_correct_shape_refuted :
    ¬ weakCompatibilityRealization_gap_correct_shape.{0} := by
  intro h
  obtain ⟨δ, _, hw, hz⟩ :=
    h (F := {cexSplit}) (w := fun _ => 1) weaklyCompatible_cexSplit
      (by intro _ _; norm_num)
  have h1 : δ.bunemanIndex cexSplit = 1 := by
    simpa using hw cexSplit (by simp)
  have h2 : δ.bunemanIndex cexSplit2 = 0 :=
    hz cexSplit2 (by simpa using cexSplit2_ne_cexSplit)
      (by simpa using cexSplit2_swap_ne_cexSplit)
  exact no_bunemanIndex_pair δ h1 h2


/-! ## 5. ★★★ `fourPointCharacterization_gap` 的 **`⟸` 一半**（本轮已证）

缺口（`Phylo/SplitWeak.lean:414`）：

```text
(∀ s ∈ F, ∀ t ∈ F, s.Compatible t) ↔
  ∃ δ, FourPoint δ ∧ ∀ s, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s
```

**`⟸`（本节结论）**：给定**对称** `δ`、`FourPoint δ`，且 `F` 恰为其 d-split 集（商掉 `swap`），
则 `F` **两两相容**。核心是不依赖 `F` 的引理 `compatible_of_fourPoint_isDSplit`
（Buneman 的两 split 版：`δ` 对称 + 四点条件 + 两个 d-split ⟹ 相容）。

### ⚠️ 两处必须记下的**忠实性问题**（★D）

**(i) 缺口右边没要求 `δ` 对称。** BdD 全篇的 `d` 都是**对称**函数（文献 503–509 行的四点条件
本就写在对称函数上），本节的 `⟸` 需要显式带上 `∀ x y, δ x y = δ y x`。
证明中**只有一处**用到对称：把 `IsDSplit s` 结论里的 `δ c b` 换成 `δ b c`。

**(ii) `Split.FourPoint` 的第三个合取项与它自己的 docstring 不符（疑为笔误）。**
docstring 说三个表达式是 `d(a,a')+d(b,b')`、`d(a,b)+d(a',b')`、`d(a,b')+d(a',b)`（最大者至少取两次）；
但 `def` 第 3 项写的是

```text
δ a b' + δ a' b ≤ max (δ a a' + δ b b') (δ a b + δ a' b)     -- 末项应为 δ a b + δ a' b'
```

末项 `δ a b + δ a' b`（两对共享端点 `b`）**不是**三个表达式之一 ⇒ 本库的 `FourPoint`
与文献的四点条件**不等价**。本节的证明**绕开**了这一项：
只需 `FourPoint` 的**第一个**合取项（它是正确的：`δ a a' + δ b b' ≤ max (δ a b + δ a' b') (δ a b' + δ a' b)`），
在 `(a,a',b,b') = (A,C,B,D)` 与 `(A,D,B,C)` 两个取法上使用。故本定理对**本库原文**成立，
`def FourPoint` 与缺口陈述**逐字未改**。

### 证明（取法与 `Phylo/BunemanTree.lean:218` 的 Lemma 8 一致）

若 `s, t` 不相容，则四个交 `A∩A'`、`A∩B'`、`B∩A'`、`B∩B'` 全非空，取
`A ∈ s.sideA ∩ t.sideA`、`C ∈ s.sideA ∩ t.sideB`、`B ∈ s.sideB ∩ t.sideA`、`D ∈ s.sideB ∩ t.sideB`。
记 `S1 := δ A C + δ B D`、`S2 := δ A B + δ C D`、`U := δ A D + δ B C`，则

* `IsDSplit s`（内部对 `(A,C)`、`(B,D)`）给 `S1 < max (S2) (δ A D + δ C B)`，
  **对称**把它变成 `S1 < max S2 U`；
* `IsDSplit t`（内部对 `(A,B)`、`(C,D)`）给 `S2 < max S1 U`；
* `FourPoint δ A D B C` 的第一合取项给 `U ≤ max S2 S1`（`= max S1 S2`）；

三者与「最大者至少两次」矛盾（纯实数引理 `not_two_pos_of_fourPoint`）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **纯实数引理**：若 `U ≤ max S1 S2`（「最大者至少两次」的必要一半），
则不可能同时有 `S1 < max S2 U` 与 `S2 < max S1 U`。 -/
theorem not_two_pos_of_fourPoint {S1 S2 U : ℝ}
    (h3 : U ≤ max S1 S2) (h4 : S1 < max S2 U) (h5 : S2 < max S1 U) : False := by
  rcases lt_or_ge S2 S1 with hlt | hge
  · have hU : S1 < U := by
      by_contra hc
      have hc' : U ≤ S1 := not_lt.mp hc
      have : max S2 U ≤ S1 := max_le (le_of_lt hlt) hc'
      linarith [h4]
    have hmax : max S1 S2 ≤ S1 := max_le le_rfl (le_of_lt hlt)
    linarith [h3, hmax, hU]
  · have hU : S2 < U := by
      by_contra hc
      have hc' : U ≤ S2 := not_lt.mp hc
      have : max S1 U ≤ S2 := max_le hge hc'
      linarith [h5]
    have hmax : max S1 S2 ≤ S2 := max_le hge le_rfl
    linarith [h3, hmax, hU]

/-- ★★★ **四点条件 + 两个 d-split ⟹ 相容**（Buneman 的两 split 版；`⟸` 方向的核心）。

⚠️ 需要 `δ` **对称**（文件头 ★D (i)）；这是文献的 setting（BdD 的 `d` 恒对称）。 -/
theorem compatible_of_fourPoint_isDSplit {δ : X → X → ℝ} (hsym : ∀ x y, δ x y = δ y x)
    (hfp : FourPoint δ) {s t : Split X}
    (hs : IsDSplit δ s.sideA s.sideB) (ht : IsDSplit δ t.sideA t.sideB) : s.Compatible t := by
  by_contra h
  obtain ⟨A, hAs, hAt⟩ : ∃ A : X, A ∈ s.sideA ∧ A ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inl hd)
  obtain ⟨C, hCs, hCt⟩ : ∃ C : X, C ∈ s.sideA ∧ C ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inl hd))
  obtain ⟨B, hBs, hBt⟩ : ∃ B : X, B ∈ s.sideB ∧ B ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inl hd)))
  obtain ⟨D, hDs, hDt⟩ : ∃ D : X, D ∈ s.sideB ∧ D ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inr hd)))
  have hU : δ A D + δ B C ≤ max (δ A C + δ B D) (δ A B + δ C D) := by
    have h0 := (hfp A D B C).1
    rw [hsym D B, hsym D C, max_comm] at h0
    exact h0
  have hs' : δ A C + δ B D < max (δ A B + δ C D) (δ A D + δ B C) := by
    have h0 := hs A hAs C hCs B hBs D hDs
    rwa [hsym C B] at h0
  have ht' : δ A B + δ C D < max (δ A C + δ B D) (δ A D + δ B C) :=
    ht A hAt B hBt C hCt D hDt
  exact not_two_pos_of_fourPoint hU hs' ht'

/-- ★★★ **`fourPointCharacterization_gap` 的 `⟸` 一半**（已证）：

「存在**对称**的 `δ`：`FourPoint δ` 且其 d-split 集**恰为** `F`（商掉 `swap`）」⟹ `F` **两两相容**。 -/
theorem pairwiseCompatible_of_exists_symm_fourPoint_isDSplit {F : Finset (Split X)}
    (h : ∃ δ : X → X → ℝ, (∀ x y, δ x y = δ y x) ∧ FourPoint δ ∧
      ∀ s : Split X, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s) :
    ∀ s ∈ F, ∀ t ∈ F, s.Compatible t := by
  obtain ⟨δ, hsym, hfp, hδ⟩ := h
  intro s hs t ht
  exact compatible_of_fourPoint_isDSplit hsym hfp
    ((hδ s).mpr ⟨s, hs, Or.inl rfl⟩) ((hδ t).mpr ⟨t, ht, Or.inl rfl⟩)

/-! ## 6. ★★★ `FourPointStd` 与库内 `FourPoint` 的关系（W12k；协调侧机器判定 + 本文件复核）

机器判定（协调侧 `/Temp/w10/` 脚本 + 本仓 `scripts/msc/w12d_b2_b1_search.py`，精确穷举）：

* **方向**：库内（笔误）形态 **严格强于** 标准形态 —— 「仅库内真」= `0`（`n = 3, 4` 网格、`n = 5` 随机 20000），
  「仅标准真」= `6 / 65 / 25` ⇒ **`FourPoint ⟹ FourPointStd`**（*对称* `δ` 下可证，见下）；
* **严重性**：真实**树度量几乎全都不满足库内形态** —— 随机树 + 随机正边权，`n = 4` 的 3000 个有效树度量
  里只有 **1** 个满足，`n = 5/6/7` 为 **0/3000**；本文件用**显式见证**把它证成定理
  （`cexTreeVal_not_fourPoint`：树度量 `δ_{0|123} + δ_{01|23}` 在 `(0,0,1,2)` 处库内第三式 `3 ≤ 2` ✗）。

⇒ **后果**：`fourPointOfSplitMetricSum_gap`（B1）**是假命题**（前提真、结论假，见 `§7`）；
凡以库内 `FourPoint` 为**前提**的定理，其前提把真实树度量排除在外 ⇒ 必须在 `FourPointStd` 上重述
（`§6.2` 给出 `⟸` 半的逐字搬运版）。 -/

omit [Fintype X] [DecidableEq X] in
/-- ★★★ **旧形态 `FourPointLegacy` ⟹ 标准 `FourPoint`**（W12k 最有用的那条桥；**W22 改锚**）。

证明只用一次对称性与 `add_comm`：把库内条件的**第二**合取项用在**前两个参数对调**后的元组
`(a',a,b,b')` 上 —— 那里的「平行和」`δ a' b + δ a b'` 恰是标准第三式左端、
「两内和」`δ a' a + δ b b'` 与「交叉和」`δ a' b' + δ a b` 恰是标准第三式的两个 `max` 参数。

⚠️ 需要 `δ` **对称**（库内条件对非对称 `δ` 也定义，但标准形态是给对称函数用的）。 -/
theorem fourPoint_of_fourPointLegacy {δ : X → X → ℝ} (hsym : ∀ x y, δ x y = δ y x)
    (h : FourPointLegacy δ) : FourPoint δ := by
  intro a a' b b'
  refine ⟨(h a a' b b').1, (h a a' b b').2.1, ?_⟩
  have h0 := (h a' a b b').2.1
  rw [hsym a' a] at h0
  calc δ a b' + δ a' b = δ a' b + δ a b' := by ring
    _ ≤ max (δ a a' + δ b b') (δ a' b' + δ a b) := h0
    _ = max (δ a a' + δ b b') (δ a b + δ a' b') := by rw [add_comm (δ a' b') (δ a b)]

/-! ### 6.1 反向**不成立**：真实树度量满足标准形态、违反库内形态 -/

/-- 见证用 split：`{0}|{1,2,3}`。 -/
def cexS0 : Split (Fin 4) := Split.ofSideA {0} (by decide) (by decide)

/-- 见证用 split：`{0,1}|{2,3}`。 -/
def cexS01 : Split (Fin 4) := Split.ofSideA ({0, 1} : Finset (Fin 4)) (by decide) (by decide)

/-- 见证族 `F := { {0}|{1,2,3}, {0,1}|{2,3} }`（**两两相容** ✓）。 -/
def cexF2 : Finset (Split (Fin 4)) := {cexS0, cexS01}

/-- 见证权重 `w ≡ 1`。 -/
noncomputable def cexW : Split (Fin 4) → ℝ := fun _ => 1

/-- 见证 `δ := Σ_{S ∈ F} w_S · δ_S`（= 树（伪）度量）。 -/
noncomputable def cexT : Fin 4 → Fin 4 → ℝ :=
  fun x y => ∑ s ∈ cexF2, cexW s * SplitMetric s x y

/-- `cexT` 的显式矩阵。 -/
noncomputable def cexTreeVal : Fin 4 → Fin 4 → ℝ
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 2
  | 0, 3 => 2
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 1
  | 2, 0 => 2
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, 3 => 0
  | 3, 0 => 2
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0

/-- `cexT` 就是该矩阵（16 个点逐对求值；先把 2 项和写成显式两项以绕开 `sum_boole`）。 -/
theorem cexT_eq_cexTreeVal : cexT = cexTreeVal := by
  funext x y
  have hpair : cexT x y = SplitMetric cexS0 x y + SplitMetric cexS01 x y := by
    simp only [cexT, cexW, cexF2, one_mul]
    rw [Finset.sum_pair (by decide)]
  rw [hpair]
  fin_cases x <;> fin_cases y <;>
    norm_num [cexTreeVal, cexS0, cexS01, SplitMetric, Split.ofSideA_sideA, Split.ofSideA_sideB]

/-- ★★ **标准四点条件成立**（它是树（伪）度量；256 个四元组全过）。 -/
theorem cexTreeVal_fourPointStd : FourPointStd cexTreeVal := by
  intro a a' b b'
  fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;>
    norm_num [cexTreeVal, max_def]

/-- ★★★ **旧形态 `FourPointLegacy` 不成立**（★ **W22 改名**：本条只对**旧形态**成立 ——
对标准形态它**是假的**，见同文件的 `cexTreeVal_fourPointStd`）：
见证四元组 `(a,a',b,b') = (0,0,1,2)`，旧形态第三式给出 `3 ≤ max (1) (2) = 2` ✗。 -/
theorem cexTreeVal_not_fourPointLegacy : ¬ FourPointLegacy cexTreeVal := by
  intro h
  have h3 := (h 0 0 1 2).2.2
  norm_num [cexTreeVal, max_def] at h3

/-- `cexTreeVal` 对称（显式矩阵）。 -/
theorem cexTreeVal_symm : ∀ x y, cexTreeVal x y = cexTreeVal y x := by
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [cexTreeVal]

/-- ★★★ **「标准 ⟹ 旧形态」是假命题**（同一个树度量即反例）⇒ 旧形态**严格更强**。

★ **W22 改名 + 改锚**：旧名 `not_fourPointStd_imp_fourPoint`（当时含义 =「标准 ⟹ 库内错形态」
不成立）；含义不变，只是把右端从 `FourPoint`（错形态）换成 `FourPointLegacy`、左端换成 `FourPoint`。 -/
theorem not_fourPointLegacy_of_fourPoint :
    ¬ (∀ (δ : Fin 4 → Fin 4 → ℝ), (∀ x y, δ x y = δ y x) → FourPoint δ → FourPointLegacy δ) := by
  intro h
  exact cexTreeVal_not_fourPointLegacy (h cexTreeVal cexTreeVal_symm cexTreeVal_fourPointStd)

/-! ### 6.2 `⟸` 半在 `FourPointStd` 上的重述（逐字搬运：证明只用第一合取项 + 对称性） -/

/-- ★★★ **`FourPointStd` + 两个 d-split ⟹ 相容**（`§5` 定理的标准形态版；证明逐字相同）。 -/
theorem compatible_of_fourPointStd_isDSplit {δ : X → X → ℝ} (hsym : ∀ x y, δ x y = δ y x)
    (hfp : FourPointStd δ) {s t : Split X}
    (hs : IsDSplit δ s.sideA s.sideB) (ht : IsDSplit δ t.sideA t.sideB) : s.Compatible t := by
  by_contra h
  obtain ⟨A, hAs, hAt⟩ : ∃ A : X, A ∈ s.sideA ∧ A ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inl hd)
  obtain ⟨C, hCs, hCt⟩ : ∃ C : X, C ∈ s.sideA ∧ C ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inl hd))
  obtain ⟨B, hBs, hBt⟩ : ∃ B : X, B ∈ s.sideB ∧ B ∈ t.sideA :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inl hd)))
  obtain ⟨D, hDs, hDt⟩ : ∃ D : X, D ∈ s.sideB ∧ D ∈ t.sideB :=
    Finset.not_disjoint_iff.mp fun hd => h (Or.inr (Or.inr (Or.inr hd)))
  have hU : δ A D + δ B C ≤ max (δ A C + δ B D) (δ A B + δ C D) := by
    have h0 := (hfp A D B C).1
    rw [hsym D B, hsym D C, max_comm] at h0
    exact h0
  have hs' : δ A C + δ B D < max (δ A B + δ C D) (δ A D + δ B C) := by
    have h0 := hs A hAs C hCs B hBs D hDs
    rwa [hsym C B] at h0
  have ht' : δ A B + δ C D < max (δ A C + δ B D) (δ A D + δ B C) :=
    ht A hAt B hBt C hCt D hDt
  exact not_two_pos_of_fourPoint hU hs' ht'

/-- ★★★ **缺口 `⟸` 一半的 `FourPointStd` 版**（推荐使用的形态；库内形态版见 `§5`）。 -/
theorem pairwiseCompatible_of_exists_symm_fourPointStd_isDSplit {F : Finset (Split X)}
    (h : ∃ δ : X → X → ℝ, (∀ x y, δ x y = δ y x) ∧ FourPointStd δ ∧
      ∀ s : Split X, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s) :
    ∀ s ∈ F, ∀ t ∈ F, s.Compatible t := by
  obtain ⟨δ, hsym, hfp, hδ⟩ := h
  intro s hs t ht
  exact compatible_of_fourPointStd_isDSplit hsym hfp
    ((hδ s).mpr ⟨s, hs, Or.inl rfl⟩) ((hδ t).mpr ⟨t, ht, Or.inl rfl⟩)

/-! ## 7. ★B 瓶颈 (B1) **证伪**：`fourPointOfSplitMetricSum_gap` 是假命题

取 `F := cexF2 = { {0}|{1,2,3}, {0,1}|{2,3} }`（**两两相容** ✓）、`w ≡ 1` ⇒ `δ̂ = cexT`（树度量）⇒
由 `§6.1` 的 `cexTreeVal_not_fourPoint` 得 `¬ FourPoint δ̂` ⇒ **前提真、结论假** ✗。 -/

/-- 见证族**两两相容**（用库内 `Compatible` 构造件，避免 `Disjoint` 的可判定性）。 -/
theorem cexF2_compat : ∀ s ∈ cexF2, ∀ t ∈ cexF2, s.Compatible t := by
  intro s hs t ht
  simp only [cexF2, Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact compatible_self cexS0
  · exact compatible_of_subset_left (by
      intro x hx
      fin_cases x <;> simp_all [cexS0, cexS01, Split.ofSideA_sideA])
  · exact compatible_of_subset_right (by
      intro x hx
      fin_cases x <;> simp_all [cexS0, cexS01, Split.ofSideA_sideA])
  · exact compatible_self cexS01

/-- **旧形态的 (B1) 缺口**（★ **W22 新增**）：把 `Split.fourPointOfSplitMetricSum_gap` 的结论
换成**旧形态** `FourPointLegacy`。★ **只在追溯时用** —— W22 已把 `FourPoint` 本体改对，
故 `Split.fourPointOfSplitMetricSum_gap` 现在是**标准形态、且已可证**（见 `…_gap_proof`）；
**真正为假的是本 `Prop`** ✓。 -/
def fourPointOfSplitMetricSum_gap_legacy : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) → (∀ s ∈ F, 0 < w s) →
      FourPointLegacy (fun x y => ∑ s ∈ F, w s * SplitMetric s x y)

/-- ★B ★★★ **（旧形态的）瓶颈 (B1) 是假命题**。

★ **W22 改名 + 改锚**：原名 `not_fourPointOfSplitMetricSum`（当时反的是
`fourPointOfSplitMetricSum_gap`，因其结论用的是错形态）；改本体后那个 `Prop` 已为**真**，
故本反驳**改锚**到 `fourPointOfSplitMetricSum_gap_legacy` 上（真内容不变）。 -/
theorem not_fourPointOfSplitMetricSum_legacy : ¬ fourPointOfSplitMetricSum_gap_legacy.{0} := by
  intro h
  have hfp : FourPointLegacy (fun x y : Fin 4 => ∑ s ∈ cexF2, cexW s * SplitMetric s x y) :=
    h (α := Fin 4) cexF2 cexW cexF2_compat (by intro s _; norm_num [cexW])
  rw [show (fun x y : Fin 4 => ∑ s ∈ cexF2, cexW s * SplitMetric s x y) = cexT from rfl,
    cexT_eq_cexTreeVal] at hfp
  exact cexTreeVal_not_fourPointLegacy hfp

/-- ⬜ **瓶颈 (B1) 的正确形态（W12k 登记；未证）**：结论换成**标准**四点条件 `FourPointStd`。

这才是这条缺口的真正数学内容：两两相容族 + 正权重之和是**树度量**，而树度量满足标准四点条件
（`§6.1` 已对最小见证验证标准形态 ✓；库内形态则**被树度量排除** ✗）。 -/
def fourPointOfSplitMetricSum_gap_correct_shape : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) → (∀ s ∈ F, 0 < w s) →
      FourPointStd (fun x y => ∑ s ∈ F, w s * SplitMetric s x y)

/-! ## 8. ★D `SplitPrime` 是**不可满足**的 ⇒ `canonicalSplitDecomposition_gap` **平凡为假**

协调侧怀疑「库内 `SplitPrime`（= 处处 `¬ IsDSplit`，`max` 形式）**严格强于**文献形态
（= 处处 `¬ IsDSplitStrong`）」；本文件核出的结论**更强**：

> 库内 `SplitPrime δ := ∀ A B : Finset α, ¬ IsDSplit δ A B` **对任何 `δ` 都不成立** ✗ ——
> 取 `A = ∅`：`IsDSplit δ ∅ B` 是**空真**（`∀ a ∈ ∅, …`）⇒ `¬ IsDSplit δ ∅ B` 为假。

⇒ **`canonicalSplitDecomposition_gap` 平凡为假**（它的结论要求 `∃ δ₀, SplitPrime δ₀`，
而这样的 `δ₀` 不存在）：见 `not_canonicalSplitDecomposition_gap` ✓。
根因：BdD 的「(partial) split」两侧**非空**，库内 `def SplitPrime` 漏了这个侧条件
（文献形态应写 `A.Nonempty → B.Nonempty → ¬ …`）。

⇒ 补齐非空侧后的形态登记为 `SplitPrimeStd` + `canonicalSplitDecomposition_gap_correct_shape`；
★ **W25-b ★D 校正**：`SplitPrimeStd`（`μ` 形）**仍不是**忠实 split-prime，忠实形态 = `SplitPrimeFaithful`
（`§8.1`）；且 `……_correct_shape` 已被**证成**（`canonicalSplitDecomposition_gap_correct_shape_holds`），
但它是**空转**缺口（见该 `def` 的 docstring）；
原 `def` **逐字未改** ✓。 -/

/-- ★★★ **库内 `SplitPrime` 不可满足**（空集使其空真反驳）。 -/
theorem not_splitPrime {α : Type*} (δ : α → α → ℝ) : ¬ SplitPrime δ := by
  intro h
  exact h ∅ ∅ (by intro a ha; exact absurd ha (Finset.notMem_empty a))

/-- **`μ` 形 split-prime**（两侧非空 + `¬ IsDSplitStrong`，即 `bunemanIndex ≤ 0`）。

⚠️ ★D 校正（W25-b）：这**不是** BdD 的忠实 split-prime —— 忠实形态是隔离指数 `α_{A,B} = 0`
（即 `¬ IsDSplit`，`max` 形；md `:673-684`），登记为 `SplitPrimeFaithful`（本文件 `§8.1`）。
本 `def` **弱于**它（`¬IsDSplit ⟹ ¬IsDSplitStrong`，见 `splitPrimeStd_of_splitPrimeNE`）。 -/
def SplitPrimeStd {α : Type*} (δ : α → α → ℝ) : Prop :=
  ∀ A B : Finset α, A.Nonempty → B.Nonempty → ¬ IsDSplitStrong δ A B

/-- 库内形态（**加上非空侧条件**后）⟹ 忠实形态：`¬Max ⟹ ¬Strong`（逐四元组的 `Strong ⟹ Max`）。 -/
theorem splitPrimeStd_of_splitPrimeNE {α : Type*} {δ : α → α → ℝ}
    (h : ∀ A B : Finset α, A.Nonempty → B.Nonempty → ¬ IsDSplit δ A B) : SplitPrimeStd δ := by
  intro A B hA hB hS
  exact h A B hA hB fun a ha a' ha' b hb b' hb' =>
    lt_of_lt_of_le (hS a ha a' ha' b hb b' hb').1 (le_max_left _ _)

/-- ★★★ **`canonicalSplitDecomposition_gap` 是假命题**（`.{0}` 实例；原 `def` 未改）：
其结论要求 `SplitPrime δ₀`，而该谓词**不可满足**。 -/
theorem not_canonicalSplitDecomposition_gap : ¬ canonicalSplitDecomposition_gap.{0} := by
  intro h
  obtain ⟨_F, _c, δ₀, _hpos, hprime, _hdec⟩ :=
    h (α := Fin 4) (fun _ _ => 0) (fun _ _ => rfl)
  exact not_splitPrime δ₀ hprime

/-- ✓ **`canonicalSplitDecomposition_gap` 的正确形态**（W12k 登记；**W25-b：已证成**，但见下「空转」）：
残差改为**非空侧 + 强形式** `SplitPrimeStd`。

★★ **W25-b 判定：本 `Prop` 为真，且证明不需要 `δ` 的对称性**
（`canonicalSplitDecomposition_gap_correct_shape_holds`，主引理 `exists_splitPrimeFaithful_decomposition`）：
取 `F := 全体 split`、系数恒为足够大的 `M`，残差 `δ₀ := δ − M·∑_s δ_s` 的**非对角元**可任意负，
而对角元 `δ₀ x x = δ x x` 不动（`δ_s x x = 0`）⇒ 一对**退化四元组** `a = a'`、`b = b'`
就使每个非空 `A,B` 的隔离指数 `≤ 0` ✓。

⛔ **所以本 `Prop` 仍是「空转缺口」，不是 BdD Theorem 2**。BdD 的残差还要求
**仍在 `M(X)` 里（仍是度量）**：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:673-684`
「the residue `d₀ := d − ∑_{S∈Σ_d} α_S δ_S` of `d` with respect to its splits is always **in M(X)**
and it is **split-prime**」（另见 `:816`、`:825`「a split-prime metric and a sum of nonnegative
multiples of …」），且系数必须**等于隔离指数**（`:1651-1655` Thm 2）、分解**唯一**。
本 `Prop` 缺的恰是这三件：①`δ` 与 `δ₀` 的**度量约束**（`M(X)`：`δ x x = 0`、非负、三角不等式；
松掉它 ⇒ 非对角可任意下压 ⇒ 平凡为真）；②**典范性** `c s = α_s`；③**唯一性**。
⇒ 忠实形态登记为 `canonicalSplitDecomposition_gap_faithful`（`§8.2`；仍为缺口）。 -/
def canonicalSplitDecomposition_gap_correct_shape : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeStd δ₀ ∧
        ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

/-! ## 8.1 ★★★ W25-b：`……_gap_correct_shape` **已证成**，但它是**空转缺口**

### 证明（思路三行）

`F := Finset.univ`、`c ≡ M := 2·(∑_{x,y} |δ x y|) + 1`、`δ₀ := δ − M·∑_s SplitMetric s`。

* **对角**：`SplitMetric s x x = 0`（`sideA` 与 `sideB` 不交）⇒ `δ₀ x x = δ x x` 不动；
* **非对角**（`x ≠ y`）：split `{x} | {x}ᶜ` 分开它们 ⇒ `∑_s SplitMetric s x y ≥ 1` ⇒
  `δ₀ x y ≤ δ x y − M`（可任意负）；
* **split-prime**：任取非空 `A, B` —— 若 `A ∩ B ≠ ∅`，取 `a = a' = b = b' ∈ A ∩ B`（两边**相等**）；
  否则取 `a ∈ A`、`b ∈ B`（`a ≠ b`），用**退化四元组** `a = a'`、`b = b'`：
  `δ₀ a a + δ₀ b b = δ a a + δ b b ≥ 2·δ₀ a b`（`M` 足够大）
  ⇒ `¬ IsDSplitStrong` —— 更强：连 `¬ IsDSplit`（`max` 形）都成立。

### ★D 校正（W25-b 独立复核；**推翻 W12j「忠实性更正 #2」**）

* **旧判断**（W12j；曾写在 `Phylo/SplitWeak.lean` 的 `IsDSplit` docstring 与本文件的
  `IsDSplitStrong` docstring 里，现已按下面的四要素改正）：「BdD 的 d-split（= 隔离指数 `α_{A,B} > 0`）是 **`min` 形**，
  故库内 `IsDSplit`（**`max` 形**）**不忠实**，`IsDSplitStrong` 才是 `α > 0`」；
* **新判断**：`α` 的定义里 `max{…}` **含第三项**（被减的 `d(a,a')+d(b,b')` 自身），故
  `α_{A,B} = min{max{P,Q,I} − I} = max(min{max{P,Q} − I}, 0)` ⇒
  `α_{A,B} > 0 ⟺ ∀ 四元组 max{P,Q} > I` ⟺ **`IsDSplit`（`max` 形）** ✓ ——
  库内 `IsDSplit` **就是** BdD 的 d-split；而 `IsDSplitStrong`（两项 `min` 形）≡
  **Buneman 1971 p. 390 的 `μ_σ`**（= 库内 `bunemanIndex`），**不是** BdD 的 `α`；
* **文献行号**：`BandeltDress1992_CanonicalDecompositionMetrics.md:438-440`（d-split ⟺ 隔离指数为正）
  ＋ `:446-454`（`α := min{max{d(a,b)+d(a',b'), d(a,b')+d(a',b), d(a,a')+d(b,b')} − d(a,a') − d(b,b')}`，
  **第三项在 `max` 内**）＋ `:673-684`（split-prime = **对每个 split 隔离指数 `0`**）；
* **理由（真假判据，非措辞）**：若 `α` 是两项 `min` 形，则 `α` 可取**负值**，`:673-684` 的
  「isolation index `0`」就无法刻画 split-prime；且 `:438-440` 的「`α > 0` ⟺ `max` 形」与 `:446`
  的三项 `max` **自相矛盾**；两项 `min` 形是 Buneman 1971 p. 390 的 `μ_σ`。
  ⇒ `bunemanIndex_pos_iff_isDSplitStrong` **不变**（它说的是 `μ`，不是 `α`），但
  **「`IsDSplit` 不忠实」这个结论作废**。
  ★ 连带后果：`SplitPrimeStd`（`¬ IsDSplitStrong` = `μ ≤ 0`）**弱于**忠实 split-prime
  （`¬ IsDSplit` = `α = 0`）⇒ 忠实形态登记为 `SplitPrimeFaithful`。 -/

/-- **忠实形态的 split-prime**（BdD `:673-684`「对每个 split 的隔离指数为 `0`」）：两侧**非空**、
且 `¬ IsDSplit`（`max` 形，即 `α_{A,B} = 0`）。

⚠️ **严格强于** `SplitPrimeStd`（`¬ IsDSplitStrong` = `μ ≤ 0`）：`IsDSplitStrong ⟹ IsDSplit`
（逐四元组的 `min ≤ max`），故 `¬IsDSplit ⟹ ¬IsDSplitStrong`（见 `splitPrimeStd_of_splitPrimeNE`）；
反向**不成立**（`§3`：`cex_isDSplit` 与 `¬ IsDSplitStrong` 同时成立）。 -/
def SplitPrimeFaithful {α : Type*} (δ : α → α → ℝ) : Prop :=
  ∀ A B : Finset α, A.Nonempty → B.Nonempty → ¬ IsDSplit δ A B

/-- ★★★ **存在性主引理（零假设；连 `δ` 的对称性都不需要）**：`F := 全体 split`、系数恒为
`M := 2S + 1`（`S := ∑_{x,y} |δ x y|`）、残差 `δ₀ := δ − M·∑_s δ_s` 满足
「**每个**非空 `A, B` 都不是 `δ₀` 的 `d`-split」（`max` 形，比 `SplitPrimeStd` 更强）。

见 `§8.1` 的三行思路。★ 注意：这只证明**存在某个**分解，**不是** BdD 的**典范**分解
（残差不是度量、系数不是隔离指数、分解不唯一）。 -/
theorem exists_splitPrimeFaithful_decomposition {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) :
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithful δ₀ ∧
        ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y := by
  classical
  set S : ℝ := ∑ x : α, ∑ y : α, |δ x y| with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => abs_nonneg _
  have hle1 : ∀ x : α, (∑ y : α, |δ x y|) ≤ S := by
    intro x
    rw [hS]
    exact Finset.single_le_sum (f := fun x => ∑ y : α, |δ x y|)
      (fun x _ => Finset.sum_nonneg fun y _ => abs_nonneg _) (Finset.mem_univ x)
  have hle2 : ∀ x y : α, |δ x y| ≤ ∑ y : α, |δ x y| := by
    intro x y
    exact Finset.single_le_sum (f := fun y => |δ x y|) (fun y _ => abs_nonneg _)
      (Finset.mem_univ y)
  have habs : ∀ x y : α, |δ x y| ≤ S := fun x y => (hle2 x y).trans (hle1 x)
  set M : ℝ := 2 * S + 1 with hM
  have hMpos : 0 < M := by rw [hM]; linarith
  -- 单点 split 分开任意一对不同的点
  have hsep : ∀ a b : α, a ≠ b → ∃ s : Split α, a ∈ s.sideA ∧ b ∈ s.sideB := by
    intro a b hab
    have hb : b ∈ ({a} : Finset α)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact Ne.symm hab
    have h1 : ({a} : Finset α).Nonempty := ⟨a, by simp⟩
    have h2 : (({a} : Finset α)ᶜ).Nonempty := ⟨b, hb⟩
    refine ⟨Split.ofSideA ({a} : Finset α) h1 h2, ?_, ?_⟩
    · rw [Split.ofSideA_sideA]
      exact Finset.mem_singleton_self a
    · rw [Split.ofSideA_sideB]
      exact hb
  have hmetric_diag : ∀ (s : Split α) (x : α), SplitMetric s x x = 0 := by
    intro s x
    have hnot : ¬((x ∈ s.sideA ∧ x ∈ s.sideB) ∨ (x ∈ s.sideB ∧ x ∈ s.sideA)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact (Finset.disjoint_left.mp (disjoint_sides s)) h1 h2
      · exact (Finset.disjoint_left.mp (disjoint_sides s)) h2 h1
    simp only [SplitMetric, ite_eq_right hnot]
  have hmetric_nonneg : ∀ (s : Split α) (x y : α), 0 ≤ SplitMetric s x y := by
    intro s x y
    unfold SplitMetric
    split_ifs <;> norm_num
  have hsum_diag : ∀ x : α, (∑ s : Split α, M * SplitMetric s x x) = 0 := by
    intro x
    simp [hmetric_diag]
  refine ⟨Finset.univ, fun _ => M, fun x y => δ x y - ∑ s : Split α, M * SplitMetric s x y,
    ⟨fun s _ => hMpos, ?_, ?_⟩⟩
  · -- 残差的每个非空 `A | B` 都不是 `max` 形 d-split
    intro A B hA hB hDS
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    rcases eq_or_ne a b with hab | hab
    · -- 重叠：`a = b`，退化四元组 `a = a' = b = b'`
      subst hab
      have h := hDS a ha a ha a hb a hb
      dsimp only at h
      rw [hsum_diag a] at h
      rw [max_self] at h
      linarith
    · -- 分离：`a ≠ b`，退化四元组 `a = a'`、`b = b'`
      obtain ⟨s0, hs0a, hs0b⟩ := hsep a b hab
      have h1 : SplitMetric s0 a b = 1 := by
        have hcond : (a ∈ s0.sideA ∧ b ∈ s0.sideB) ∨ (a ∈ s0.sideB ∧ b ∈ s0.sideA) :=
          Or.inl ⟨hs0a, hs0b⟩
        simp only [SplitMetric, ite_eq_left hcond]
      have hsum1 : 1 ≤ ∑ s : Split α, SplitMetric s a b := by
        have hle := Finset.single_le_sum (f := fun s => SplitMetric s a b)
          (fun s _ => hmetric_nonneg s a b) (Finset.mem_univ s0)
        rw [h1] at hle
        linarith
      have hsumM : M ≤ ∑ s : Split α, M * SplitMetric s a b := by
        rw [← Finset.mul_sum]
        calc M = M * 1 := by ring
          _ ≤ M * ∑ s : Split α, SplitMetric s a b :=
              mul_le_mul_of_nonneg_left hsum1 (le_of_lt hMpos)
      have hδab : δ a b ≤ S := le_trans (le_abs_self _) (habs a b)
      have hδaa : -δ a a ≤ S := by
        have h := neg_abs_le (δ a a)
        linarith [habs a a]
      have hδbb : -δ b b ≤ S := by
        have h := neg_abs_le (δ b b)
        linarith [habs b b]
      have h2M : 2 * M = 4 * S + 2 := by rw [hM]; ring
      have hcontra := hDS a ha a ha b hb b hb
      dsimp only at hcontra
      rw [hsum_diag a, hsum_diag b] at hcontra
      rw [max_self] at hcontra
      linarith
  · -- 分解等式（定义即残差）
    intro x y
    dsimp only
    ring

/-- ★★★ **`canonicalSplitDecomposition_gap_correct_shape` 成立**（`_holds` 形态；**零假设**，
连 `δ` 的对称性都不用）。★ 但见该 `def` 的 docstring：这是**空转**结论 —— 真正的 BdD 内容
（残差仍是度量 + 系数 = 隔离指数 + 唯一性）不在本 `Prop` 里。 -/
theorem canonicalSplitDecomposition_gap_correct_shape_holds :
    canonicalSplitDecomposition_gap_correct_shape.{0} := by
  intro α _ _ δ _
  obtain ⟨F, c, δ₀, hpos, hfaith, heq⟩ := exists_splitPrimeFaithful_decomposition δ
  exact ⟨F, c, δ₀, hpos, splitPrimeStd_of_splitPrimeNE hfaith, heq⟩

/-! ## 8.2 ⛔ **BdD Theorem 2 的忠实形态**（W25-b 登记；**W26-c 由 `§8.5` 机器证伪**） -/

/-- ⛔ **`canonicalSplitDecomposition_gap` 的忠实形态（W25-b 登记；★★★ W26-c 已机器证伪）**：

`δ` 是 `X` 上的**度量**（`M(X)`：对称、`x = x ⟹ 0`、非负、三角不等式 —— `:673-684`、
`:816`、`:825` 的框架），且**残差 `δ₀` 仍是度量**、并且 split-prime（隔离指数处处 `0`）。

★ 与 `……_correct_shape` 的**唯一差别**就是「`δ` 与 `δ₀` 仍在 `M(X)` 里」—— 但这一条
**恰好挡住** `§8.1` 的「全体 split 大系数下压」构造（那里 `δ₀` 非对角为负），
故本形态**不是空转**；它等价于 `:1651-1655` Thm 2 的**存在性**一半
（本 `Prop` 未要求 `c s = α_s` 与唯一性，故弱于 Thm 2 全文）。缺的具名器材见报告「卡点」。

★ **W26-c（`§8.4` 的机器结论）**：本 `Prop` 的结论其实**把残差压成 `0`**（`eq_zero_of_splitPrimeFaithful` ✓ 机器证明 —— 注册形态的 `SplitPrimeFaithful` 量化了**非划分对** `{x}|{y}`，其隔离指数含退化项 `2·δ₀ x y`），故本 `Prop` 的结论等价于「`δ` 是正系数 split 度量之和」，**不是** BdD Thm 2 的残差形态。忠实形态见 `§8.4` 的 `canonicalSplitDecomposition_gap_faithful_v2`（四要素在 `§8.4` 头部）。

★★★ **W26-c 追加：本 `Prop` 已被机器证伪** —— `not_canonicalSplitDecomposition_gap_faithful`
（`§8.5`）：`Fin 5` 上的度量 `d₅`（`{0,1,2}` 两两 `2`；`3、4` 到三者 `1`；`d(3,4) = 1`）使结论失败
（超度量泛函 `Φ`：每个 split 度量上 `≤ 0`，而 `Φ(d₅) = 2`）。 -/
def canonicalSplitDecomposition_gap_faithful : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    (∀ x, δ x x = 0) → (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithful δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

/-! ## 8.3 ★★★ BdD 的**隔离指数** `α_{A,B}`（实值）—— 器材落地（W25-d）

### 文献
* `references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:438-440`：`A|B` 是 **d-split**
  ⟺ 隔离指数 `α_{A,B} > 0`；
* `:446-454`：`α_{A,B} := min{ max{d(a,b)+d(a',b'), d(a,b')+d(a',b), d(a,a')+d(b,b')}
  − d(a,a') − d(b,b') }`（`a,a' ∈ A`、`b,b' ∈ B`，`min` 取遍**可退化**四元组）；
* `:673-684`：split-prime ⟺ **每个** `A|B` 的隔离指数为 `0`。

### 形态约定（为何本节能直接用 `pairDeficit`）
被 `min` 的量是 `pairDeficit δ a a' b b' = max{δ a b + δ a' b', δ a b' + δ a' b} − (δ a a' + δ b b')`
（`Phylo/SplitWeak.lean:251`）；把它写成 BdD 的「`max` 里含第三项」只差一个恒等式
`max{max{P,Q}, I} − I = max{max{P,Q} − I, 0}`，故「`max` 里含 `I`」与「取 `pairDeficit` 再截断
到 `0`」是**同一个数**。★ 关键结论（本节的桥）：`0 < α_{A,B} ⟺ IsDSplit δ A B`（`max` 形），
这正是 `IsDSplit` 忠实性的**定义级证明**，也把 `canonicalSplitDecomposition_gap_faithful` 缺的
第 ② 件器材（系数 `c s = α_{s.sideA, s.sideB}`）落成了库内**可命名**的对象。 -/

/-- 隔离指数取 `inf'` 的**四元组集** `A × A × B × B`（含退化四元组：允许 `a = a'`、`b = b'`）。 -/
abbrev isoQuadruples {α : Type*} (A B : Finset α) : Finset ((α × α) × (α × α)) :=
  (A ×ˢ A) ×ˢ (B ×ˢ B)

/-- `A`、`B` 都非空 ⇒ 四元组集非空（`Finset.inf'` 的前提）。 -/
theorem isoQuadruples_nonempty {α : Type*} {A B : Finset α}
    (hA : A.Nonempty) (hB : B.Nonempty) : (isoQuadruples A B).Nonempty :=
  (hA.product hA).product (hB.product hB)

/-- ★★★ **隔离指数** `α_{A,B}`（BdD md `:446-454`，**实值**）：遍历四元组
`(a,a',b,b') ∈ A×A×B×B` 取 `pairDeficit` 的 `min`。空侧情形记为 `0`（与 `IsDSplit` 的空真相容）。 -/
noncomputable def isolationIndex {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (A B : Finset α) : ℝ :=
  if h : (isoQuadruples A B).Nonempty then
    (isoQuadruples A B).inf' h (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
  else 0

/-- 两侧非空时 `isolationIndex` 的展开式（`inf'` 形态）。 -/
theorem isolationIndex_eq_inf' {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    isolationIndex δ A B
      = (isoQuadruples A B).inf' (isoQuadruples_nonempty hA hB)
          (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold isolationIndex
  split_ifs with h
  · rfl
  · exact absurd (isoQuadruples_nonempty hA hB) h

/-- 四元组 `(a,a',b,b')` 属于 `isoQuadruples A B` 的展开。 -/
theorem mem_isoQuadruples {α : Type*} {A B : Finset α} {a a' b b' : α} :
    ((a, a'), (b, b')) ∈ isoQuadruples A B ↔ a ∈ A ∧ a' ∈ A ∧ b ∈ B ∧ b' ∈ B := by
  simp only [isoQuadruples, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨ha, ha', hb, hb'⟩
    exact ⟨⟨ha, ha'⟩, hb, hb'⟩

/-- ★★★ **`0 < α_{A,B} ⟺ IsDSplit δ A B`**（BdD md `:438-440` 的**忠实形式化**）：
「隔离指数为正」恰好是「逐四元组 `max{P,Q} > I`」，即库内 `max` 形的 `IsDSplit`。 -/
theorem isolationIndex_pos_iff_isDSplit {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    0 < isolationIndex δ A B ↔ IsDSplit δ A B := by
  rw [isolationIndex_eq_inf' δ hA hB]
  have key : (0 : ℝ) < (isoQuadruples A B).inf' (isoQuadruples_nonempty hA hB)
        (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
      ↔ ∀ q ∈ isoQuadruples A B, 0 < pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2 :=
    Finset.lt_inf'_iff (isoQuadruples_nonempty hA hB)
  rw [key]
  constructor
  · intro h a ha a' ha' b hb b' hb'
    have hq := (mem_isoQuadruples (A := A) (B := B) (a := a) (a' := a')
      (b := b) (b' := b')).mpr ⟨ha, ha', hb, hb'⟩
    have hpos := h _ hq
    simp only [pairDeficit, sub_pos] at hpos
    exact hpos
  · intro h q hq
    obtain ⟨⟨a, a'⟩, b, b'⟩ := q
    obtain ⟨ha, ha', hb, hb'⟩ := (mem_isoQuadruples (A := A) (B := B)).mp hq
    show 0 < pairDeficit δ a a' b b'
    simp only [pairDeficit, sub_pos]
    exact h a ha a' ha' b hb b' hb'

/-- ★★ **任一四元组给出隔离指数的上界**：`α_{A,B} ≤ pairDeficit δ a a' b b'`。 -/
theorem isolationIndex_le_pairDeficit {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty)
    {a a' b b' : α} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) :
    isolationIndex δ A B ≤ pairDeficit δ a a' b b' := by
  have hq := (mem_isoQuadruples (A := A) (B := B) (a := a) (a' := a')
    (b := b) (b' := b')).mpr ⟨ha, ha', hb, hb'⟩
  have h : (isoQuadruples A B).inf' (isoQuadruples_nonempty hA hB)
        (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
      ≤ pairDeficit δ a a' b b' := by
    by_contra hcon
    rw [not_le] at hcon
    have hlt := (Finset.lt_inf'_iff (H := isoQuadruples_nonempty hA hB)
      (f := fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)).mp hcon
    exact absurd (hlt _ hq) (lt_irrefl _)
  rw [isolationIndex_eq_inf' δ hA hB]
  exact h

/-- ★★★ **split-prime 的隔离指数形态**（BdD md `:673-684`）：`SplitPrimeFaithful δ` ⟺
**每个**非空 `A`、`B` 的隔离指数 `≤ 0`（截断形态下 `α ≥ 0`，故等价于「`= 0`」）。 -/
theorem splitPrimeFaithful_iff_isolationIndex_nonpos {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) :
    SplitPrimeFaithful δ ↔
      ∀ (A B : Finset α), A.Nonempty → B.Nonempty → isolationIndex δ A B ≤ 0 := by
  constructor
  · intro h A B hA hB
    by_contra hcon
    rw [not_le] at hcon
    exact h A B hA hB ((isolationIndex_pos_iff_isDSplit δ hA hB).mp hcon)
  · intro h A B hA hB hds
    exact absurd (h A B hA hB)
      (not_le.mpr ((isolationIndex_pos_iff_isDSplit δ hA hB).mpr hds))

/-- ★★ **为何 `§8.2` 的 ①（残差仍在 `M(X)` 里）不可省**：只要残差非负、系数非负，
就有逐点 `δ₀ ≤ δ`。故 `§8.1` 的「取全体 split、系数 `M := 2S+1` 把非对角压成负数」构造
**在 ① 下不可能**（那里 `δ₀` 非对角元为负，越界于 `M(X)`）—— 这正是
`……_gap_correct_shape`（无 ①，真空转）与 `……_gap_faithful`（有 ①，非空转）的分水岭。

（本定理只用到 `SplitMetric ≥ 0` 与「和的分拆」，不需要 `δ` 的任何度量性质。） -/
theorem residue_le_of_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {δ δ₀ : α → α → ℝ} {F : Finset (Split α)} {c : Split α → ℝ}
    (hc : ∀ s ∈ F, 0 ≤ c s)
    (heq : ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y) :
    ∀ x y, δ₀ x y ≤ δ x y := by
  have hmetric : ∀ (s : Split α) (x y : α), 0 ≤ SplitMetric s x y := by
    intro s x y
    unfold SplitMetric
    split_ifs <;> norm_num
  intro x y
  have hnn : 0 ≤ ∑ s ∈ F, c s * SplitMetric s x y :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hc s hs) (hmetric s x y)
  rw [heq x y]
  linarith

/-! ## 8.4 ★★★ W26-c：注册形态 `SplitPrimeFaithful` 的**退化定理**（机器证明）与四要素校正

### 机器结论

`§8.1` 的 `SplitPrimeFaithful` 量化的是**任意一对**非空 `Finset` `A, B`，**不要求** `A ∪ B = X`。
取**非划分对** `A = {x}`、`B = {y}`（`x ≠ y`）时四元组集 `A×A×B×B` 只有 `(x,x,y,y)` 一点，
隔离指数只剩 `max{2·(δ₀ x y), δ₀ x x + δ₀ y y} − δ₀ x x − δ₀ y y`；对角 `0` 加非负使它等于 `2·δ₀ x y`
⇒ `¬ IsDSplit` 就是 `δ₀ x y ≤ 0` ⇒ 与「非负」合用即得 `δ₀ ≡ 0`（`eq_zero_of_splitPrimeFaithful` ✓）。

⇒ `§8.2` 的 `canonicalSplitDecomposition_gap_faithful` 的结论**退化**成
「`δ` 是一族**正系数** split 度量之和」（`exists_splitMetric_sum_of_faithful` ✓）：
残差没有留下任何「split-prime 但非零」的余地。这不是 BdD Thm 2 的形态。

### 四要素（`§8.1`/`§8.2` 登记形态 ⇒ 忠实形态）

* **旧形态**（**逐字保留**，未改）：`SplitPrimeFaithful δ := ∀ A B, A.Nonempty → B.Nonempty →
  ¬ IsDSplit δ A B`（`§8.1`）；`canonicalSplitDecomposition_gap_faithful`（`§8.2`，同样未改）；
* **新形态**：`SplitPrimeFaithfulPartition δ := ∀ A B, A.Nonempty → B.Nonempty → Disjoint A B →
  A ∪ B = Finset.univ → ¬ IsDSplit δ A B`（只取 `X` 的**划分** `A|B`），配套
  `canonicalSplitDecomposition_gap_faithful_v2`（残差用新形态）＋
  `splitPrimeFaithfulPartition_iff_isolationIndex_nonpos`（与 `§8.3` 隔离指数的桥，形态照抄 `§8.3`）；
* **文献**：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:1245-1253`
  （split 度量 `δ_{A,B}` 定义在 `A ⊔ B` 上 ⇒ split = **不交并覆盖 `X`** 的一对子集）＋ `:1255-1262`
  （**split-prime = 不存在任何 d-split**；`K₂,₃` 的度量是其五点例，「up to a scalar」唯一）＋
  `:1281-1285`（**Thm 2**：残差 `d₀` 是 split-prime 函数）＋ `:3560-3564`
  （`d₀ = 0` ⟺ 无 split-prime 余项；**四点度量总可分解**，而**五点上存在非零 split-prime 度量**）
  ＋ `:673-684`（残差对**每个 split** 的隔离指数为 `0`）；
* **理由（真假判据，非措辞）**：BdD 的 split-prime = 「对每个 **split（划分）** `A|B` 隔离指数为 `0`」，
  且 `:3564` 明言五点上**存在非零 split-prime 度量**（`K₂,₃`）⇒ 忠实形态**不能**逼出残差为零；
  注册形态却对**非划分对** `{x}|{y}` 也要求隔离指数为 `0`，把残差压成 `0`
  ⇒ 注册形态**严格强于**忠实形态（对 `K₂,₃` 这类度量直接为假）⇒ 须换新形态。
  ★ 下一步（未做）：用 `K₂,₃` 五点度量机器验证「严格强于」（旧形态假、新形态真）。

★ **W26-c 追加（`§8.5`）**：由本节的退化定理可**推出** `§8.2` 的 `Prop` 为**假**
（`not_canonicalSplitDecomposition_gap_faithful`）：退化后结论要求「`δ` 是正系数 split 度量之和」，
而 `Fin 5` 上的 `d₅` 不是（超度量泛函 `Φ` 反证）。 -/

/-- ★★★ **注册形态的 `SplitPrimeFaithful` 逼出「残差恒为零」**：取**非划分对** `A = {x}`、`B = {y}`
（`x ≠ y`），四元组集只有 `(x,x,y,y)` 一点，`¬ IsDSplit` 即 `δ₀ x y ≤ 0`；与非负性合并即得 `δ₀ ≡ 0`。

★ 这不是刻意构造的病态条件：`§8.1` 的 `def` 本来就没有「`A ∪ B = X`」这一条
（BdD 的 split 有，见 `§8.4` 头部的四要素）。 -/
theorem eq_zero_of_splitPrimeFaithful {α : Type*} {δ₀ : α → α → ℝ}
    (hsp : SplitPrimeFaithful δ₀) (hdiag : ∀ x, δ₀ x x = 0) (hnn : ∀ x y, 0 ≤ δ₀ x y) :
    ∀ x y, δ₀ x y = 0 := by
  intro x y
  rcases eq_or_ne x y with rfl | hxy
  · exact hdiag x
  · have hA : ({x} : Finset α).Nonempty := ⟨x, Finset.mem_singleton_self x⟩
    have hB : ({y} : Finset α).Nonempty := ⟨y, Finset.mem_singleton_self y⟩
    have hle : δ₀ x y ≤ 0 := by
      by_contra hcon
      rw [not_le] at hcon
      refine hsp {x} {y} hA hB (fun a ha a' ha' b hb b' hb' => ?_)
      rw [Finset.mem_singleton] at ha ha' hb hb'
      rw [ha, ha', hb, hb']
      rw [hdiag x, hdiag y, max_self]
      linarith
    have hge : 0 ≤ δ₀ x y := hnn x y
    linarith

/-- ★★★ **`§8.2` 忠实缺口的结论 ⇒ `δ` 是「正系数 split 度量之和」**：
残差被 `eq_zero_of_splitPrimeFaithful` 压成 `0`，于是分解式里只剩 split 度量的和。
★ 这条把注册形态的**真实内容**暴露出来：它不是「存在 split-prime 残差」，而是「`δ` 在 split 锥里」。 -/
theorem exists_splitMetric_sum_of_faithful {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ}
    (h : ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithful δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧ ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y) :
    ∃ (F : Finset (Split α)) (c : Split α → ℝ), (∀ s ∈ F, 0 < c s) ∧
      ∀ x y, δ x y = ∑ s ∈ F, c s * SplitMetric s x y := by
  obtain ⟨F, c, δ₀, hpos, hsp, hdiag, hnn, heq⟩ := h
  have hzero := eq_zero_of_splitPrimeFaithful hsp hdiag hnn
  exact ⟨F, c, hpos, fun x y => by rw [heq x y, hzero x y, zero_add]⟩

/-- **忠实 split-prime（四要素校正版）**：只对 `X` 的**划分** `A|B`（不交、并 = 全集、两侧非空）
要求隔离指数 `0`（BdD `:1255-1262`、`:673-684`；split 的定义见 `:1245-1253` 的 `A ⊔ B`）。

★ **严格弱于** `§8.1` 的 `SplitPrimeFaithful`（后者量化任意非空对；见 `§8.4` 的退化定理与
`K₂,₃` 例子）。本 `def` 是 `§8.2` 残差应当使用的谓词。 -/
def SplitPrimeFaithfulPartition {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) : Prop :=
  ∀ A B : Finset α, A.Nonempty → B.Nonempty → Disjoint A B → A ∪ B = Finset.univ →
    ¬ IsDSplit δ A B

/-- ★★ **划分版 split-prime 的隔离指数形态**（`§8.3` 的 `splitPrimeFaithful_iff_isolationIndex_nonpos`
限制到 `X` 的划分；证明照抄 `§8.3`）。 -/
theorem splitPrimeFaithfulPartition_iff_isolationIndex_nonpos {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) :
    SplitPrimeFaithfulPartition δ ↔
      ∀ (A B : Finset α), A.Nonempty → B.Nonempty → Disjoint A B → A ∪ B = Finset.univ →
        isolationIndex δ A B ≤ 0 := by
  constructor
  · intro h A B hA hB hd hu
    by_contra hcon
    rw [not_le] at hcon
    exact h A B hA hB hd hu ((isolationIndex_pos_iff_isDSplit δ hA hB).mp hcon)
  · intro h A B hA hB hd hu hds
    exact absurd (h A B hA hB hd hu)
      (not_le.mpr ((isolationIndex_pos_iff_isDSplit δ hA hB).mpr hds))

/-- ⬜ **忠实缺口（四要素校正版；未证）**：与 `§8.2` 的 `canonicalSplitDecomposition_gap_faithful`
**逐字相同**，只把残差的 split-prime 换成**划分版** `SplitPrimeFaithfulPartition`。

★ 这是 BdD Thm 2（`:1281-1285`）的**存在性**一半（不要求 `c s = α_s`、不要求唯一性）；
`§8.2` 的原版因残差被压成 `0` 而**不是** Thm 2（见 `§8.4`）。 -/
def canonicalSplitDecomposition_gap_faithful_v2 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    (∀ x, δ x x = 0) → (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

/-! ## 8.5 ★★★ W26-c：注册形态 `canonicalSplitDecomposition_gap_faithful` **为假**（机器反例）

### 三行思路

1. 由 `§8.4`，该 `Prop` 的结论逼出残差 `δ₀ ≡ 0`，故结论等价于「`δ` 是**正系数** split 度量之和」；
2. 取**超度量（hypermetric）型**线性泛函 `Φ(δ) := Σ_{i,j} w i · w j · δ i j`，`w = (1,1,1,-1,-1)`：
   对**任何** split `s`（`X` 的划分）有 `Φ(δ_s) = 2·(Σ_A w)·(Σ_B w) ≤ 0`
   （`Σ_A w`、`Σ_B w` 是整数且和为 `1`，故其积 ≤ `0`）—— `witnessForm_splitMetric_le`；
3. 见证度量 `d₅`：`{0,1,2}` 两两 `2`；`3、4` 到三者 `1`；`d(3,4) = 1`。它是**度量** ✓
   （`witnessDist_triangle`），但 `Φ(d₅) = 2 > 0` ⇒ 不可能是正系数 split 度量之和 ⇒ 结论假。

★ 与 BdD 一致：「**四点**度量总可分解，**五点**上出现**非零** split-prime 残差」（md `:3560-3564`）；
超度量不等式是 cut cone（split 度量锥）的合法不等式（Deza–Laurent）。 -/

/-- 见证度量 `d₅` 的整数值（见 `§8.5`）：`{0,1,2}` 两两 `2`，`3、4` 到三者 `1`，`d(3,4) = 1`。 -/
def witnessDistInt (x y : Fin 5) : ℤ :=
  match x.val, y.val with
  | 0, 0 => 0
  | 1, 1 => 0
  | 2, 2 => 0
  | 3, 3 => 0
  | 4, 4 => 0
  | 3, 4 => 1
  | 4, 3 => 1
  | 3, _ => 1
  | 4, _ => 1
  | _, 3 => 1
  | _, 4 => 1
  | _, _ => 2

/-- 见证度量 `d₅`（`witnessDistInt` 的 `ℝ` 版本）。 -/
noncomputable def witnessDist (x y : Fin 5) : ℝ := (witnessDistInt x y : ℝ)

/-- 整数值权重 `w = (1,1,1,-1,-1)`（`Σ w = 1`；整数值是 `(Σ_A w)(Σ_B w) ≤ 0` 的关键）。 -/
def witnessWInt : Fin 5 → ℤ := fun i =>
  match i.val with
  | 3 => -1
  | 4 => -1
  | _ => 1

/-- 实值权重 `w`（`witnessWInt` 的 `ℝ` 版本）。 -/
noncomputable def witnessW (i : Fin 5) : ℝ := (witnessWInt i : ℝ)

/-- **超度量型线性泛函** `Φ(δ) = Σ_{i,j} w i · w j · δ i j`（对称 `δ` 上即 cut cone 的合法不等式）。 -/
noncomputable def witnessForm (δ : Fin 5 → Fin 5 → ℝ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, witnessW i * witnessW j * δ i j

theorem witnessDist_symm : ∀ x y, witnessDist x y = witnessDist y x := by
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [witnessDist, witnessDistInt]

theorem witnessDist_diag : ∀ x, witnessDist x x = 0 := by
  intro x
  fin_cases x <;> norm_num [witnessDist, witnessDistInt]

theorem witnessDist_nonneg : ∀ x y, 0 ≤ witnessDist x y := by
  intro x y
  fin_cases x <;> fin_cases y <;> norm_num [witnessDist, witnessDistInt]

theorem witnessDist_triangle : ∀ x y z, witnessDist x z ≤ witnessDist x y + witnessDist y z := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [witnessDist, witnessDistInt]

theorem witnessWInt_sum : (∑ i : Fin 5, witnessWInt i) = 1 := by decide

/-- 权重和取整：`Σ_{i∈C} w i` 是整数（`w` 整数值）。 -/
theorem witnessW_cast (C : Finset (Fin 5)) :
    ((C.sum witnessWInt : ℤ) : ℝ) = C.sum witnessW := by
  push_cast
  rfl

theorem witnessW_sum : (∑ i : Fin 5, witnessW i) = 1 := by
  rw [← witnessW_cast Finset.univ, witnessWInt_sum]
  norm_num

/-- 整数 `k` 满足 `k·(1-k) ≤ 0`（这正是 `w` 必须整数值的原因）。 -/
theorem int_mul_one_sub_nonpos (k : ℤ) : ((k : ℝ) * (1 - (k : ℝ)) ≤ 0) := by
  rcases lt_or_ge (0 : ℤ) k with h | h
  · have h1 : (1 : ℤ) ≤ k := h
    have h2 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
    nlinarith
  · have h2 : (k : ℝ) ≤ 0 := by exact_mod_cast h
    nlinarith

/-- `if i ∈ C then w i else 0` 对 `i` 的无约束求和等于 `C` 上的和。 -/
theorem sum_ite_witnessW (C : Finset (Fin 5)) :
    (∑ i : Fin 5, (if i ∈ C then witnessW i else 0)) = C.sum witnessW := by
  have hf : (Finset.univ.filter (fun i : Fin 5 => i ∈ C)) = C := by
    ext i
    simp
  rw [← Finset.sum_filter, hf]

/-- `if` 乘积的双和 = 两个和之积。 -/
theorem sum_ite_mul_ite (A B : Finset (Fin 5)) :
    (∑ i : Fin 5, ∑ j : Fin 5,
        (if i ∈ A then witnessW i else 0) * (if j ∈ B then witnessW j else 0))
      = A.sum witnessW * B.sum witnessW := by
  have hB : (∑ j : Fin 5, (if j ∈ B then witnessW j else 0)) = B.sum witnessW :=
    sum_ite_witnessW B
  calc (∑ i : Fin 5, ∑ j : Fin 5,
          (if i ∈ A then witnessW i else 0) * (if j ∈ B then witnessW j else 0))
      = ∑ i : Fin 5, (if i ∈ A then witnessW i else 0)
          * (∑ j : Fin 5, (if j ∈ B then witnessW j else 0)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : Fin 5, (if i ∈ A then witnessW i else 0) * B.sum witnessW := by
        rw [hB]
    _ = (∑ i : Fin 5, (if i ∈ A then witnessW i else 0)) * B.sum witnessW := by
        rw [Finset.sum_mul]
    _ = A.sum witnessW * B.sum witnessW := by
        rw [sum_ite_witnessW A]

/-- ★★★ **split 度量上的超度量不等式**：`Φ(δ_s) ≤ 0`（对**任何** split `s`）。
`δ_s` 是 cut：`Φ(δ_s) = (Σ_A w)(Σ_B w) + (Σ_B w)(Σ_A w) = 2·(Σ_A w)(1 - Σ_A w) ≤ 0`。 -/
theorem witnessForm_splitMetric_le (s : Split (Fin 5)) : witnessForm (SplitMetric s) ≤ 0 := by
  have hB : ∀ i : Fin 5, i ∈ s.sideB ↔ i ∉ s.sideA := by
    intro i
    constructor
    · intro h hA
      exact Finset.disjoint_left.mp s.disjoint_sides hA h
    · intro h
      rcases Finset.mem_union.mp (by rw [s.union_sides]; exact Finset.mem_univ i) with h' | h'
      · exact absurd h' h
      · exact h'
  have hpt : ∀ i j : Fin 5, witnessW i * witnessW j * SplitMetric s i j
      = (if i ∈ s.sideA then witnessW i else 0) * (if j ∈ s.sideB then witnessW j else 0)
        + (if i ∈ s.sideB then witnessW i else 0) * (if j ∈ s.sideA then witnessW j else 0) := by
    intro i j
    by_cases hi : i ∈ s.sideA <;> by_cases hj : j ∈ s.sideA <;>
      simp [SplitMetric, hB, hi, hj]
  have hpt2 : ∀ i : Fin 5, witnessW i
      = (if i ∈ s.sideA then witnessW i else 0) + (if i ∈ s.sideB then witnessW i else 0) := by
    intro i
    by_cases hi : i ∈ s.sideA
    · have hib : i ∉ s.sideB := fun h => Finset.disjoint_left.mp s.disjoint_sides hi h
      simp [hi, hib]
    · have hib : i ∈ s.sideB := (hB i).mpr hi
      simp [hi, hib]
  have hsplit : s.sideA.sum witnessW + s.sideB.sum witnessW = 1 := by
    rw [← sum_ite_witnessW s.sideA, ← sum_ite_witnessW s.sideB, ← Finset.sum_add_distrib,
      ← witnessW_sum]
    exact Finset.sum_congr rfl (fun i _ => (hpt2 i).symm)
  have hX : ((s.sideA.sum witnessWInt : ℤ) : ℝ) = s.sideA.sum witnessW := witnessW_cast s.sideA
  have hY : s.sideB.sum witnessW = 1 - s.sideA.sum witnessW := by linarith
  have hprod : s.sideA.sum witnessW * s.sideB.sum witnessW ≤ 0 := by
    rw [hY, ← hX]
    exact int_mul_one_sub_nonpos (s.sideA.sum witnessWInt)
  calc witnessForm (SplitMetric s)
      = ∑ i : Fin 5, ∑ j : Fin 5,
          ((if i ∈ s.sideA then witnessW i else 0) * (if j ∈ s.sideB then witnessW j else 0)
            + (if i ∈ s.sideB then witnessW i else 0) * (if j ∈ s.sideA then witnessW j else 0)) := by
        unfold witnessForm
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))
    _ = (∑ i : Fin 5, ∑ j : Fin 5,
            (if i ∈ s.sideA then witnessW i else 0) * (if j ∈ s.sideB then witnessW j else 0))
          + (∑ i : Fin 5, ∑ j : Fin 5,
            (if i ∈ s.sideB then witnessW i else 0) * (if j ∈ s.sideA then witnessW j else 0)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_add_distrib]
    _ = s.sideA.sum witnessW * s.sideB.sum witnessW
          + s.sideB.sum witnessW * s.sideA.sum witnessW := by
        rw [sum_ite_mul_ite, sum_ite_mul_ite]
    _ = 2 * (s.sideA.sum witnessW * s.sideB.sum witnessW) := by ring
    _ ≤ 0 := by linarith

/-- `Φ` 对「`F` 上的加权和」可加（线性）。 -/
theorem witnessForm_sum {ι : Type*} (F : Finset ι) (c : ι → ℝ) (δs : ι → Fin 5 → Fin 5 → ℝ) :
    witnessForm (fun x y => ∑ s ∈ F, c s * δs s x y)
      = ∑ s ∈ F, c s * witnessForm (δs s) := by
  have step1 : ∀ i j : Fin 5, witnessW i * witnessW j * (∑ s ∈ F, c s * δs s i j)
      = ∑ s ∈ F, c s * (witnessW i * witnessW j * δs s i j) := by
    intro i j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  calc witnessForm (fun x y => ∑ s ∈ F, c s * δs s x y)
      = ∑ i : Fin 5, ∑ j : Fin 5,
          ∑ s ∈ F, c s * (witnessW i * witnessW j * δs s i j) := by
        unfold witnessForm
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => step1 i j))
    _ = ∑ i : Fin 5, ∑ s ∈ F, ∑ j : Fin 5, c s * (witnessW i * witnessW j * δs s i j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact Finset.sum_comm
    _ = ∑ s ∈ F, ∑ i : Fin 5, ∑ j : Fin 5, c s * (witnessW i * witnessW j * δs s i j) := by
        exact Finset.sum_comm
    _ = ∑ s ∈ F, c s * witnessForm (δs s) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        unfold witnessForm
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]

/-- 见证度量上的泛函值：`Φ(d₅) = 2 > 0`（整数值计算，`decide` 收尾）。 -/
theorem witnessForm_witnessDist : witnessForm witnessDist = 2 := by
  have h : witnessForm witnessDist
      = ((∑ i : Fin 5, ∑ j : Fin 5, witnessWInt i * witnessWInt j * witnessDistInt i j : ℤ) : ℝ) := by
    unfold witnessForm
    push_cast
    rfl
  have h2 : (∑ i : Fin 5, ∑ j : Fin 5, witnessWInt i * witnessWInt j * witnessDistInt i j) = 2 := by
    decide
  rw [h, h2]
  norm_num

/-- ★★★ **`canonicalSplitDecomposition_gap_faithful` 是假命题**（`Fin 5` 上的度量反例 `d₅`）：
结论会把 `d₅` 写成**正系数** split 度量之和，从而 `Φ(d₅) ≤ 0`；而 `Φ(d₅) = 2`。 -/
theorem not_canonicalSplitDecomposition_gap_faithful :
    ¬ canonicalSplitDecomposition_gap_faithful.{0} := by
  intro h
  obtain ⟨F, c, δ₀, hpos, hsp, hdiag, hnn, heq⟩ :=
    h (α := Fin 5) witnessDist witnessDist_symm witnessDist_diag witnessDist_nonneg
      witnessDist_triangle
  have hzero : ∀ x y, δ₀ x y = 0 := eq_zero_of_splitPrimeFaithful hsp hdiag hnn
  have hdec : witnessForm witnessDist = ∑ s ∈ F, c s * witnessForm (SplitMetric s) := by
    rw [show witnessDist = (fun x y => ∑ s ∈ F, c s * SplitMetric s x y) from ?_]
    · exact witnessForm_sum F c (fun s => SplitMetric s)
    · funext x y
      rw [heq x y, hzero x y, zero_add]
  have hnonpos : ∑ s ∈ F, c s * witnessForm (SplitMetric s) ≤ 0 :=
    Finset.sum_nonpos fun s hs =>
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hpos s hs)) (witnessForm_splitMetric_le s)
  have hpos2 : 0 < witnessForm witnessDist := by rw [witnessForm_witnessDist]; norm_num
  linarith

/-! ## 8.6 ★★★ W27 泳道 e：BdD **Thm 2** 的**剥离步**器材（存在性 ① 的第一块砖）

文献：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:1281-1326`（**Thm 2** 陈述：
`A,B` 是 `d`-split 时系数 `λ_{A,B} = α_{A,B}`，其余为 `0`；`d' := d - Σ λ_{A,B} δ_{A,B}` 满足
`α'_{A,B} = α_{A,B} - λ_{A,B}`；**且 `d` 是 dissimilarity/metric ⇒ `d'` 也是**）＋ Proof 从 `:1346` 起。

### 本节的机器结论（四要素：旧形态 / 新形态 / 文献 / 理由）

`canonicalSplitDecomposition_gap_faithful_v2`（`:1154`，**未改一字**）的结论要求
`δ = δ₀ + Σ_{s∈F} c_s·δ_s`，`c_s > 0`、`δ₀` 划分版 split-prime、`δ₀` 非负且对角为 `0`。
存在性 ① = 「把正隔离指数的 split 逐个剥离」。**本节只落地剥离单步的全部度量保形结论**
（= Thm 2 末句「`d'` 仍是 dissimilarity/metric」），不声称已证 ①。

记 `A := s.sideA`、`B := s.sideB`、`α := isolationIndex δ A B`、`c := α/2`
（BdD 的 `α` 带 `½`，库内 `pairDeficit` **省去 `½`** ⇒ 系数要除 `2`，见 `§8.3` 头部的形态约定）、
`δ' := peelMetric δ s`（即 `δ' x y = δ x y - c·δ_{A,B}(x,y)`）。

1. `splitMetric_nonneg / _self / _eq_one_* / _eq_zero_*`：`δ_{A,B}` 是 `0/1` 值、对角 `0`、
   两侧之间的取值为 `1`、同侧取值为 `0`（`splitMetric_symm` 已在 `Phylo/SplitWeak.lean:960`）；
2. `peelMetric_symm / _diag / _nonneg / _triangle`：**`δ'` 仍是度量**；
   ★ 非负与三角不等式的**实质输入都是同一条定量界**（本节 `isolationIndex_le_cross_gap_*`）：
   `α_{A,B} ≤ δ x y + δ y z - δ x z`（`x,z` 同侧、`y` 在另一侧）——
   它是 `isolationIndex_le_pairDeficit` 的**退化四元组** `(x,z,y,y)` 的直接推论，
   也正是「剥离不会把距离压到负、也不会破坏三角不等式」的**唯一**障碍；
3. `peelMetric_pairDeficit`：对 `A×A×B×B` 的四元组 `q`，`pd(δ',q) = pd(δ,q) - 2c = pd(δ,q) - α`
   （该四元组相对 `s` 的模式只有 `(2,2,0)` 一种 ⇒ `max` **可以**整体减去常数）；
4. `peelMetric_not_isDSplit`：**`s` 不再是 `δ'` 的 d-split**（即 `α'_s = α_s - 2c = 0`）；
5. `peelCoeff_pos`：`s` 是 `δ` 的 d-split ⇒ `0 < c`；
6. `peelStep`：以上合取成一个「剥离步」包（**BdD Thm 2 Proof `:1346` 起的第一句**的机器版）。

### ⚠️ 仍缺的两件（**具名**缺件；本节不含、也不假装含）

* **(P1) 剥离的「全局」下降**：Thm 2 的 `α'_{A,B} = α_{A,B} - λ_{A,B}` 是对**所有**对 `A,B`
  （本节第 3 条只对上被剥离的那一对 `A,B = s.sideA,s.sideB`）。一般对不是逐点可加的：
  对四元组 `q`，`pd(δ - cδ_s, q)` 与 `pd(δ,q)` 之差取决于 `q` 相对 `s` 的**五种模式**
  （见 `§9` 头部的表）：模式 `(0,0,0)`、`(1,1,1)` 差 `0`，`(2,2,0)` 差 `-2c`，
  而 `(2,0,2)` / `(0,2,2)` 差 `max{P'+2c,Q'} - max{P',Q'} - 2c`，**可正可负**
  ⇒ 需要 BdD Lemma 3–6（md `:5581` / `:6094` / `:6159` / `:6504`）的 `s(S)`-cluster / 弱层级结构
  才能推出「剥离后 d-split 集合严格缩小」。
* **(P2) 终止性**：可取的终止测度是 `dSplits δ`（本节 `:定义`）的基数：
  每剥一步 `card` 严格下降（需 (P1)）⇒ 有限步后残差无 d-split。**目前 (P1) 缺 ⇒ 终止性缺。**
* **② 唯一性（BdD Cor 4，md `:1794-1799`）不是独立上游**：Cor 4 的原文证明用 Thm 3（唯一性），
  而 Thm 3 又依赖「d-split 集合 = 正系数支撑集」⇒ 它在 ① **之后**；先做 ② 拿不到独立成果。
  这是把「先做 ②」的路线**排除**的机器级理由（Cor 4 的 `Y⁺`/`Y⁻` 论证以 Thm 3 为前提）。 -/

/-- `SplitMetric` 非负（`0/1` 值）。 -/
theorem splitMetric_nonneg {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) (x y : α) :
    0 ≤ SplitMetric s x y := by
  unfold SplitMetric
  split_ifs <;> norm_num

/-- `SplitMetric` 对角为零（两侧不交）。 -/
theorem splitMetric_self {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) (x : α) :
    SplitMetric s x x = 0 := by
  unfold SplitMetric
  split_ifs with h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h2 (Finset.disjoint_left.mp s.disjoint_sides h1)
    · exact absurd h1 (Finset.disjoint_left.mp s.disjoint_sides h2)
  · rfl

/-- `x ∈ A`、`y ∈ B` ⇒ `δ_{A,B}(x,y) = 1`。 -/
theorem splitMetric_eq_one_of_mem_sideA_mem_sideB {α : Type*} [Fintype α] [DecidableEq α]
    {s : Split α} {x y : α} (hx : x ∈ s.sideA) (hy : y ∈ s.sideB) :
    SplitMetric s x y = 1 := by
  unfold SplitMetric
  split_ifs with h
  · rfl
  · exact absurd (Or.inl ⟨hx, hy⟩) h

/-- `x ∈ B`、`y ∈ A` ⇒ `δ_{A,B}(x,y) = 1`。 -/
theorem splitMetric_eq_one_of_mem_sideB_mem_sideA {α : Type*} [Fintype α] [DecidableEq α]
    {s : Split α} {x y : α} (hx : x ∈ s.sideB) (hy : y ∈ s.sideA) :
    SplitMetric s x y = 1 := by
  unfold SplitMetric
  split_ifs with h
  · rfl
  · exact absurd (Or.inr ⟨hx, hy⟩) h

/-- 同侧（都在 `A`）⇒ `δ_{A,B}(x,y) = 0`。 -/
theorem splitMetric_eq_zero_of_mem_sideA {α : Type*} [Fintype α] [DecidableEq α]
    {s : Split α} {x y : α} (hx : x ∈ s.sideA) (hy : y ∈ s.sideA) :
    SplitMetric s x y = 0 := by
  have hyB : y ∉ s.sideB := fun h => Finset.disjoint_left.mp s.disjoint_sides hy h
  have hxB : x ∉ s.sideB := fun h => Finset.disjoint_left.mp s.disjoint_sides hx h
  unfold SplitMetric
  split_ifs with h
  · rcases h with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact absurd h2 hyB
    · exact absurd h2 hxB
  · rfl

/-- 同侧（都在 `B`）⇒ `δ_{A,B}(x,y) = 0`。 -/
theorem splitMetric_eq_zero_of_mem_sideB {α : Type*} [Fintype α] [DecidableEq α]
    {s : Split α} {x y : α} (hx : x ∈ s.sideB) (hy : y ∈ s.sideB) :
    SplitMetric s x y = 0 := by
  have hyA : y ∉ s.sideA := fun h => Finset.disjoint_left.mp s.disjoint_sides h hy
  have hxA : x ∉ s.sideA := fun h => Finset.disjoint_left.mp s.disjoint_sides h hx
  unfold SplitMetric
  split_ifs with h
  · rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hxA
    · exact absurd h2 hyA
  · rfl

/-- ★ 剥离系数 `c := α_{A,B}/2`（BdD 的 `α` 含 `½`，库内 `pairDeficit` 省去 `½`）。 -/
noncomputable def peelCoeff {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (s : Split α) : ℝ := isolationIndex δ s.sideA s.sideB / 2

/-- ★ 剥离一步：`δ' x y := δ x y - c·δ_{A,B}(x,y)`（BdD Thm 2 的 `d' := d - λ_{A,B}δ_{A,B}`）。 -/
noncomputable def peelMetric {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (s : Split α) : α → α → ℝ :=
  fun x y => δ x y - peelCoeff δ s * SplitMetric s x y

/-- `peelMetric` 的展开式（`def` 级，`rfl`）。 -/
theorem peelMetric_apply {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (s : Split α) (x y : α) :
    peelMetric δ s x y = δ x y - peelCoeff δ s * SplitMetric s x y := rfl

/-- `δ` 的 d-split 全体（**终止测度的载体**：`card` 是要在 (P1) 之后证严格下降的量）。 -/
noncomputable def dSplits {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) : Finset (Split α) :=
  letI := Classical.decPred (fun s : Split α => IsDSplit δ s.sideA s.sideB)
  Finset.univ.filter (fun s => IsDSplit δ s.sideA s.sideB)

/-- `dSplits` 的成员判据（`s ∈ dSplits δ ↔ s` 是 `δ` 的 d-split）。 -/
theorem mem_dSplits {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} :
    s ∈ dSplits δ ↔ IsDSplit δ s.sideA s.sideB := by
  classical
  simp only [dSplits, Finset.mem_filter, Finset.mem_univ, true_and]

/-- ★★ **同侧跨点的定量界**（`x,z ∈ A`、`y ∈ B`）：`α_{A,B} ≤ δ x y + δ y z - δ x z`。
来自退化四元组 `(x,z,y,y)`；它是「剥离后三角不等式仍成立」的实质输入。 -/
theorem isolationIndex_le_cross_gap_of_mem_sideA {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) {s : Split α} (hδ : ∀ x y, δ x y = δ y x)
    (hdiag : ∀ x, δ x x = 0) (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty)
    {x y z : α} (hx : x ∈ s.sideA) (hz : z ∈ s.sideA) (hy : y ∈ s.sideB) :
    isolationIndex δ s.sideA s.sideB ≤ δ x y + δ y z - δ x z := by
  have hle := isolationIndex_le_pairDeficit δ (A := s.sideA) (B := s.sideB) hA hB
    (a := x) (a' := z) (b := y) (b' := y) hx hz hy hy
  have hpd : pairDeficit δ x z y y = δ x y + δ y z - δ x z := by
    unfold pairDeficit
    rw [hdiag y, max_self, ← hδ z y]
    ring
  linarith

/-- ★★ **同侧跨点的定量界**（`x,z ∈ B`、`y ∈ A`）：`α_{A,B} ≤ δ x y + δ y z - δ x z`
（退化四元组 `(y,y,x,z)`）。 -/
theorem isolationIndex_le_cross_gap_of_mem_sideB {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) {s : Split α} (hδ : ∀ x y, δ x y = δ y x)
    (hdiag : ∀ x, δ x x = 0) (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty)
    {x y z : α} (hx : x ∈ s.sideB) (hz : z ∈ s.sideB) (hy : y ∈ s.sideA) :
    isolationIndex δ s.sideA s.sideB ≤ δ x y + δ y z - δ x z := by
  have hle := isolationIndex_le_pairDeficit δ (A := s.sideA) (B := s.sideB) hA hB
    (a := y) (a' := y) (b := x) (b' := z) hy hy hx hz
  have hpd : pairDeficit δ y y x z = δ x y + δ y z - δ x z := by
    unfold pairDeficit
    rw [hdiag y, add_comm (δ y z) (δ y x), max_self, ← hδ y x]
    ring
  linarith

/-- ★★ `δ'` 对称。 -/
theorem peelMetric_symm {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} (hδ : ∀ x y, δ x y = δ y x) (s : Split α) :
    ∀ x y, peelMetric δ s x y = peelMetric δ s y x := by
  intro x y
  rw [peelMetric_apply, peelMetric_apply, hδ x y, splitMetric_symm s x y]

/-- ★★ `δ'` 对角为零。 -/
theorem peelMetric_diag {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} (hdiag : ∀ x, δ x x = 0) (s : Split α) :
    ∀ x, peelMetric δ s x x = 0 := by
  intro x
  rw [peelMetric_apply, hdiag x, splitMetric_self, mul_zero, sub_zero]

/-- ★★★ **`δ'` 非负**（Thm 2 末句「`d` 是 dissimilarity ⇒ `d'` 也是」的第一半）。
两侧被分开时用退化四元组的定量界 `α ≤ 2δ x y`；同侧时 `δ' = δ`。 -/
theorem peelMetric_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α}
    (hδ : ∀ x y, δ x y = δ y x) (hdiag : ∀ x, δ x x = 0) (hnn : ∀ x y, 0 ≤ δ x y)
    (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty) :
    ∀ x y, 0 ≤ peelMetric δ s x y := by
  intro x y
  rw [peelMetric_apply]
  have hc : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  by_cases hxy : (x ∈ s.sideA ∧ y ∈ s.sideB) ∨ (x ∈ s.sideB ∧ y ∈ s.sideA)
  · have hS : SplitMetric s x y = 1 := by
      unfold SplitMetric
      exact ite_eq_left hxy
    rw [hS, mul_one]
    have hbound : isolationIndex δ s.sideA s.sideB ≤ 2 * δ x y := by
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · have hle := isolationIndex_le_pairDeficit δ (A := s.sideA) (B := s.sideB) hA hB
          (a := x) (a' := x) (b := y) (b' := y) hx hx hy hy
        have hpd : pairDeficit δ x x y y = 2 * δ x y := by
          unfold pairDeficit
          rw [hdiag x, hdiag y, max_self]
          ring
        linarith
      · have hle := isolationIndex_le_pairDeficit δ (A := s.sideA) (B := s.sideB) hA hB
          (a := y) (a' := y) (b := x) (b' := x) hy hy hx hx
        have hpd : pairDeficit δ y y x x = 2 * δ x y := by
          unfold pairDeficit
          rw [hdiag y, hdiag x, ← hδ x y, max_self]
          ring
        linarith
    linarith
  · have hS : SplitMetric s x y = 0 := by
      unfold SplitMetric
      exact ite_eq_right hxy
    rw [hS, mul_zero, sub_zero]
    exact hnn x y

/-- ★★★ **`δ'` 满足三角不等式**（Thm 2 末句「`d` 是 metric ⇒ `d'` 也是」的第二半）。
八种「`x,y,z` 相对两侧的位置」情形：同侧同情形给 `0`，跨侧给 `1`；
只有「`x,z` 同侧、`y` 在另一侧」两情形需要定量界 `α ≤ δ x y + δ y z - δ x z`，其余只用 `δ` 的三角不等式。 -/
theorem peelMetric_triangle {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α}
    (hδ : ∀ x y, δ x y = δ y x) (hdiag : ∀ x, δ x x = 0)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty) :
    ∀ x y z, peelMetric δ s x z ≤ peelMetric δ s x y + peelMetric δ s y z := by
  intro x y z
  rw [peelMetric_apply, peelMetric_apply, peelMetric_apply]
  have hc : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  by_cases hx : x ∈ s.sideA <;> by_cases hy : y ∈ s.sideA <;> by_cases hz : z ∈ s.sideA
  · rw [splitMetric_eq_zero_of_mem_sideA hx hz, splitMetric_eq_zero_of_mem_sideA hx hy,
      splitMetric_eq_zero_of_mem_sideA hy hz]
    simp only [mul_zero, sub_zero]
    exact htri x y z
  · have hzB : z ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s z).mpr hz
    rw [splitMetric_eq_one_of_mem_sideA_mem_sideB hx hzB,
      splitMetric_eq_zero_of_mem_sideA hx hy,
      splitMetric_eq_one_of_mem_sideA_mem_sideB hy hzB]
    simp only [mul_one, mul_zero, sub_zero]
    linarith [htri x y z]
  · have hyB : y ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s y).mpr hy
    rw [splitMetric_eq_zero_of_mem_sideA hx hz,
      splitMetric_eq_one_of_mem_sideA_mem_sideB hx hyB,
      splitMetric_eq_one_of_mem_sideB_mem_sideA hyB hz]
    simp only [mul_one, mul_zero, sub_zero]
    have hgap := isolationIndex_le_cross_gap_of_mem_sideA δ hδ hdiag hA hB hx hz hyB
    linarith
  · have hzB : z ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s z).mpr hz
    have hyB : y ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s y).mpr hy
    rw [splitMetric_eq_one_of_mem_sideA_mem_sideB hx hzB,
      splitMetric_eq_one_of_mem_sideA_mem_sideB hx hyB,
      splitMetric_eq_zero_of_mem_sideB hyB hzB]
    simp only [mul_one, mul_zero, sub_zero]
    linarith [htri x y z]
  · have hxB : x ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s x).mpr hx
    rw [splitMetric_eq_one_of_mem_sideB_mem_sideA hxB hz,
      splitMetric_eq_one_of_mem_sideB_mem_sideA hxB hy,
      splitMetric_eq_zero_of_mem_sideA hy hz]
    simp only [mul_one, mul_zero, sub_zero]
    linarith [htri x y z]
  · have hxB : x ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s x).mpr hx
    have hzB : z ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s z).mpr hz
    rw [splitMetric_eq_zero_of_mem_sideB hxB hzB,
      splitMetric_eq_one_of_mem_sideB_mem_sideA hxB hy,
      splitMetric_eq_one_of_mem_sideA_mem_sideB hy hzB]
    simp only [mul_one, mul_zero, sub_zero]
    have hgap := isolationIndex_le_cross_gap_of_mem_sideB δ hδ hdiag hA hB hxB hzB hy
    linarith
  · have hxB : x ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s x).mpr hx
    have hyB : y ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s y).mpr hy
    rw [splitMetric_eq_one_of_mem_sideB_mem_sideA hxB hz,
      splitMetric_eq_zero_of_mem_sideB hxB hyB,
      splitMetric_eq_one_of_mem_sideB_mem_sideA hyB hz]
    simp only [mul_one, mul_zero, sub_zero]
    linarith [htri x y z]
  · have hxB : x ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s x).mpr hx
    have hyB : y ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s y).mpr hy
    have hzB : z ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s z).mpr hz
    rw [splitMetric_eq_zero_of_mem_sideB hxB hzB, splitMetric_eq_zero_of_mem_sideB hxB hyB,
      splitMetric_eq_zero_of_mem_sideB hyB hzB]
    simp only [mul_zero, sub_zero]
    exact htri x y z

/-- ★★★ **被剥离四元组的 `pairDeficit` 精确下降**：`q ∈ A×A×B×B` 时
`pd(δ',q) = pd(δ,q) - 2c = pd(δ,q) - α`（该模式只有 `(2,2,0)` 一种 ⇒ `max` 可整体平移）。 -/
theorem peelMetric_pairDeficit {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a a' b b' : α}
    (ha : a ∈ s.sideA) (ha' : a' ∈ s.sideA) (hb : b ∈ s.sideB) (hb' : b' ∈ s.sideB) :
    pairDeficit (peelMetric δ s) a a' b b' = pairDeficit δ a a' b b' - 2 * peelCoeff δ s := by
  have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha hb
  have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha' hb'
  have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha hb'
  have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha' hb
  have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA ha ha'
  have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB hb hb'
  have e1 : (δ a b - peelCoeff δ s * 1) + (δ a' b' - peelCoeff δ s * 1)
      = (δ a b + δ a' b') - 2 * peelCoeff δ s := by ring
  have e2 : (δ a b' - peelCoeff δ s * 1) + (δ a' b - peelCoeff δ s * 1)
      = (δ a b' + δ a' b) - 2 * peelCoeff δ s := by ring
  have e3 : (δ a a' - peelCoeff δ s * 0) + (δ b b' - peelCoeff δ s * 0)
      = δ a a' + δ b b' := by ring
  simp only [pairDeficit, peelMetric_apply, h1, h2, h3, h4, h5, h6, e1, e2, e3,
    max_sub_sub_right]
  ring

/-- ★★★ **`s` 不再是 `δ'` 的 d-split**（Thm 2 的 `α'_s = α_s - 2c = 0`）。
反证：若 `δ'` 仍在 `A×A×B×B` 上处处正亏损，则由 `lt_inf'_iff` 得 `α < α`。 -/
theorem peelMetric_not_isDSplit {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty) :
    ¬ IsDSplit (peelMetric δ s) s.sideA s.sideB := by
  intro hcon
  have hc : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  have hlt : isolationIndex δ s.sideA s.sideB < isolationIndex δ s.sideA s.sideB := by
    have hkey : isolationIndex δ s.sideA s.sideB
        < (isoQuadruples s.sideA s.sideB).inf' (isoQuadruples_nonempty hA hB)
            (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2) := by
      refine (Finset.lt_inf'_iff (H := isoQuadruples_nonempty hA hB)
        (f := fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)).mpr ?_
      intro q hq
      obtain ⟨⟨a, a'⟩, b, b'⟩ := q
      obtain ⟨ha, ha', hb, hb'⟩ := mem_isoQuadruples.mp hq
      have hp : 0 < pairDeficit (peelMetric δ s) a a' b b' := by
        simp only [pairDeficit, sub_pos]
        exact hcon a ha a' ha' b hb b' hb'
      rw [peelMetric_pairDeficit ha ha' hb hb'] at hp
      linarith
    rwa [← isolationIndex_eq_inf' δ hA hB] at hkey
  exact lt_irrefl _ hlt

/-- ★★ **d-split 的剥离系数为正**（`α_s > 0`）。 -/
theorem peelCoeff_pos {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α}
    (hA : s.sideA.Nonempty) (hB : s.sideB.Nonempty) (hds : IsDSplit δ s.sideA s.sideB) :
    0 < peelCoeff δ s := by
  have hpos : 0 < isolationIndex δ s.sideA s.sideB :=
    (isolationIndex_pos_iff_isDSplit δ hA hB).mpr hds
  unfold peelCoeff
  linarith

/-- ★★★ **剥离步包**（BdD Thm 2 Proof `:1346` 起：「if `d` is a dissimilarity function
(or a metric), then `d′` is also」＋ `α'_s = 0` 的机器版）。

`δ` 是度量（对称 / 对角 `0` / 非负 / 三角不等式）、`s` 是 `δ` 的 d-split ⇒
`c = α_s/2 > 0`，`δ' := δ - c·δ_s` **仍是度量**，且 `s` **不再是** `δ'` 的 d-split。

⚠️ 这**不是** `canonicalSplitDecomposition_gap_faithful_v2`（`:1154`）：还缺 (P1)「剥离后
d-split 集合严格缩小」（BdD Lemma 3–6）与 (P2) 终止性 —— 见本节头部。 -/
theorem peelStep {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α}
    (hδ : ∀ x y, δ x y = δ y x) (hdiag : ∀ x, δ x x = 0) (hnn : ∀ x y, 0 ≤ δ x y)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) (hds : IsDSplit δ s.sideA s.sideB) :
    0 < peelCoeff δ s ∧ (∀ x y, peelMetric δ s x y = peelMetric δ s y x) ∧
      (∀ x, peelMetric δ s x x = 0) ∧ (∀ x y, 0 ≤ peelMetric δ s x y) ∧
      (∀ x y z, peelMetric δ s x z ≤ peelMetric δ s x y + peelMetric δ s y z) ∧
      ¬ IsDSplit (peelMetric δ s) s.sideA s.sideB :=
  ⟨peelCoeff_pos (s.nonempty 0) (s.nonempty 1) hds,
   peelMetric_symm hδ s,
   peelMetric_diag hdiag s,
   peelMetric_nonneg hδ hdiag hnn (s.nonempty 0) (s.nonempty 1),
   peelMetric_triangle hδ hdiag htri (s.nonempty 0) (s.nonempty 1),
   peelMetric_not_isDSplit (s.nonempty 0) (s.nonempty 1)⟩


/-! ## 8.7 ★★★ W27 泳道 e：`_v2` 结论的**两整类非空真实例** ＋ 归纳步的封闭性

`§8.6` 给的是**剥离一步**的度量保形（存在性 ① 的器材）。本节给 `canonicalSplitDecomposition_gap_faithful_v2`
（`:1154`，**def 未改**）的**结论**（`∃ F c δ₀, …`）的两整类真实例，用来排除「`_v2` 也像 v1 一样为假」的可能
（v1 已被 `not_canonicalSplitDecomposition_gap_faithful`（`:1368`）机器证伪）：

1. `splitPrimeFaithfulPartition_zero`：残差取 `0` 时划分版 split-prime 成立；
2. `…_v2_conclusion_of_splitMetricSum`：**`δ` = 正系数 split 度量之和**（= 树度量类，含全部树度量）
   取 `F` = 支撑、`c` = 系数、`δ₀ = 0` 即满足结论；
3. `…_v2_conclusion_of_splitPrime`：**`δ` 本身划分版 split-prime**（非负、对角 `0`）取
   `F = ∅`、`c = 0`、`δ₀ = δ` 即满足结论（= 剥离到 `F = ∅` 的终止态）。

★ 这四条合起来把 ① 的缺口**精确定位**成一条：剥离链的**终止性**（(P1) 的全局下降 ＋ (P2) 的测度）。
不带任何数学假设，也不碰 `def`。 -/

/-- 残差为 `0` 时划分版 split-prime 成立（`0` 的每个四元组亏损都是 `0`，不可能严格为正）。 -/
theorem splitPrimeFaithfulPartition_zero {α : Type*} [Fintype α] [DecidableEq α] :
    SplitPrimeFaithfulPartition (fun _ _ : α => (0 : ℝ)) := by
  intro A B hA hB _ _ hds
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have h := hds a ha a ha b hb b hb
  simp at h

/-- ★★★ **`_v2` 结论的一整类非空真实例**：`δ` 是**正系数 split 度量之和**时，
取 `F` = 支撑、`c` = 系数、`δ₀ = 0` 即满足 `canonicalSplitDecomposition_gap_faithful_v2` 的结论。

（含**全部树度量**：BdD md `:1245-1253` 的 split 度量正是树的边权展开。） -/
theorem canonicalSplitDecomposition_gap_faithful_v2_conclusion_of_splitMetricSum
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ} {F : Finset (Split α)}
    {c : Split α → ℝ} (hpos : ∀ s ∈ F, 0 < c s)
    (hδ : ∀ x y, δ x y = ∑ s ∈ F, c s * SplitMetric s x y) :
    ∃ (F' : Finset (Split α)) (c' : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F', 0 < c' s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F', c' s * SplitMetric s x y :=
  ⟨F, c, fun _ _ : α => (0 : ℝ), hpos, splitPrimeFaithfulPartition_zero,
   fun _ => rfl, fun _ _ => le_refl 0, by
     intro x y
     rw [hδ x y]
     simp⟩

/-- ★★★ **`_v2` 结论的另一整类非空真实例**：`δ` 本身**划分版 split-prime**（非负、对角 `0`）时，
取 `F = ∅`、`c = 0`、`δ₀ = δ` 即满足结论（= 剥离到 `F = ∅` 的终止态）。 -/
theorem canonicalSplitDecomposition_gap_faithful_v2_conclusion_of_splitPrime
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ}
    (hsp : SplitPrimeFaithfulPartition δ) (hdiag : ∀ x, δ x x = 0) (hnn : ∀ x y, 0 ≤ δ x y) :
    ∃ (F' : Finset (Split α)) (c' : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F', 0 < c' s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F', c' s * SplitMetric s x y :=
  ⟨∅, fun _ => 0, δ,
   (fun s hs => by simp at hs),
   hsp, hdiag, hnn, by
     intro x y
     simp⟩

/-! ## 8.8 ★★★ W27 泳道 e：`_v2` 结论的**归纳步封闭性**（存在性 ① 的骨架）

`§8.7` 给了两端：split 锥内（`F` = 支撑、`δ₀ = 0`）与 split-prime 端（`F = ∅`、`δ₀ = δ`）。
本节补上中间的**归纳步**：结论对「再加一条正系数 split 度量」封闭 ⇒

> 存在性 ① ＝ 基例（split-prime 端，已证）＋ 归纳步（本节，已证）＋ **剥离链的终止性**（缺，即 §8.6 的 (P1)+(P2)）。

这就是把 `_v2` 的缺口**收缩到唯一一件**：终止性。 -/

/-- ★★ 系数并合的展开（`s₀ ∈ F` 情形用的 `c'`）：
`(if s = s₀ then c s₀ + c₀ else c s) = c s + (if s = s₀ then c₀ else 0)`。 -/
theorem coeff_merge_mem {α : Type*} [Fintype α] [DecidableEq α] (c : Split α → ℝ) (c₀ : ℝ)
    {s₀ s : Split α} :
    (if s = s₀ then c s₀ + c₀ else c s) = c s + (if s = s₀ then c₀ else 0) := by
  by_cases h : s = s₀
  · rw [h, ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right h, add_zero]

/-- ★★ `s₀ ∈ F` 情形的正性：并合后的系数仍为正。 -/
theorem coeff_merge_mem_pos {α : Type*} [Fintype α] [DecidableEq α] {F : Finset (Split α)}
    {s₀ : Split α} (hmem : s₀ ∈ F) {c : Split α → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpos : ∀ s ∈ F, 0 < c s) {s : Split α} (hs : s ∈ F) :
    0 < (if s = s₀ then c s₀ + c₀ else c s) := by
  by_cases h : s = s₀
  · rw [ite_eq_left h]
    linarith [hpos s₀ hmem, hc₀]
  · rw [ite_eq_right h]
    exact hpos s hs

/-- ★★ `s₀ ∉ F` 情形的正性：新并进来的 `s₀` 系数为 `c₀ > 0`，其余不变。 -/
theorem coeff_insert_pos {α : Type*} [Fintype α] [DecidableEq α] {F : Finset (Split α)}
    {s₀ : Split α} (hnot : s₀ ∉ F) {c : Split α → ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hpos : ∀ s ∈ F, 0 < c s) {s : Split α} (hs : s ∈ insert s₀ F) :
    0 < (if s = s₀ then c₀ else c s) := by
  rcases Finset.mem_insert.mp hs with rfl | hs'
  · rw [ite_eq_left rfl]
    exact hc₀
  · have hne : s ≠ s₀ := fun hh => hnot (hh ▸ hs')
    rw [ite_eq_right hne]
    exact hpos s hs'

/-- ★★ 系数合并（`s₀ ∈ F` 情形）：`Σ_{s∈F} c s·δ_s + c₀·δ_{s₀} = Σ_{s∈F} c'_s·δ_s`，
其中 `c'_s := if s = s₀ then c s₀ + c₀ else c s`。 -/
theorem sum_splitMetric_add_mem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Split α)} {s₀ : Split α} (hmem : s₀ ∈ F) (c : Split α → ℝ) (c₀ : ℝ)
    (x y : α) :
    (∑ s ∈ F, c s * SplitMetric s x y) + c₀ * SplitMetric s₀ x y
      = ∑ s ∈ F, (if s = s₀ then c s₀ + c₀ else c s) * SplitMetric s x y := by
  have hpt : ∀ s ∈ F, (if s = s₀ then c s₀ + c₀ else c s) * SplitMetric s x y
      = c s * SplitMetric s x y + (if s = s₀ then c₀ * SplitMetric s₀ x y else 0) := by
    intro s _
    rw [coeff_merge_mem c c₀ (s₀ := s₀) (s := s), add_mul]
    by_cases h : s = s₀
    · rw [h, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right h, zero_mul, add_zero]
  have hsingle : (∑ s ∈ F, (if s = s₀ then c₀ * SplitMetric s₀ x y else 0))
      = c₀ * SplitMetric s₀ x y := by
    have h := Finset.sum_eq_single (s := F) (a := s₀)
      (f := fun s => if s = s₀ then c₀ * SplitMetric s₀ x y else 0) (by
        intro b _ hb
        exact ite_eq_right hb) (by
        intro h
        exact absurd hmem h)
    simpa using h
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hsingle]

/-- ★★ 系数合并（`s₀ ∉ F` 情形）：`Σ_{s∈F} c s·δ_s + c₀·δ_{s₀} = Σ_{s∈insert s₀ F} c'_s·δ_s`，
其中 `c'_s := if s = s₀ then c₀ else c s`。 -/
theorem sum_splitMetric_add_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    {F : Finset (Split α)} {s₀ : Split α} (hnot : s₀ ∉ F) (c : Split α → ℝ) (c₀ : ℝ)
    (x y : α) :
    (∑ s ∈ F, c s * SplitMetric s x y) + c₀ * SplitMetric s₀ x y
      = ∑ s ∈ insert s₀ F, (if s = s₀ then c₀ else c s) * SplitMetric s x y := by
  have hrest : (∑ s ∈ F, (if s = s₀ then c₀ else c s) * SplitMetric s x y)
      = ∑ s ∈ F, c s * SplitMetric s x y := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hne : s ≠ s₀ := fun h => hnot (h ▸ hs)
    rw [ite_eq_right hne]
  rw [Finset.sum_insert hnot, hrest]
  have hv : (if s₀ = s₀ then c₀ else c s₀) * SplitMetric s₀ x y = c₀ * SplitMetric s₀ x y := by
    rw [ite_eq_left rfl]
  rw [hv]
  ring

/-- ★★★ **`_v2` 结论的归纳步**：若 `δ` 有分解，则 `δ + c₀·δ_{s₀}`（`c₀ > 0`）也有分解 ——
残差 `δ₀` 与 split-prime 性**逐字不动**，只把 `s₀` 并进 `F`（已在则系数相加）。

⇒ 存在性 ① 只剩「剥离链终止」这一件（见 §8.6 的 (P1)+(P2)）。 -/
theorem canonicalSplitDecomposition_gap_faithful_v2_conclusion_add_split
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ} {s₀ : Split α} {c₀ : ℝ}
    (hc₀ : 0 < c₀)
    (h : ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧ ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y) :
    ∃ (F' : Finset (Split α)) (c' : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F', 0 < c' s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y + c₀ * SplitMetric s₀ x y
            = δ₀ x y + ∑ s ∈ F', c' s * SplitMetric s x y := by
  obtain ⟨F, c, δ₀, hpos, hsp, hdiag, hnn, heq⟩ := h
  by_cases hmem : s₀ ∈ F
  · refine ⟨F, fun s => if s = s₀ then c s₀ + c₀ else c s, δ₀,
      fun s hs => coeff_merge_mem_pos (F := F) (s₀ := s₀) hmem hc₀ hpos hs, hsp, hdiag, hnn, ?_⟩
    intro x y
    rw [heq x y]
    linarith [sum_splitMetric_add_mem hmem c c₀ x y]
  · refine ⟨insert s₀ F, fun s => if s = s₀ then c₀ else c s, δ₀,
      fun s hs => coeff_insert_pos (F := F) (s₀ := s₀) hmem hc₀ hpos hs, hsp, hdiag, hnn, ?_⟩
    intro x y
    rw [heq x y]
    linarith [sum_splitMetric_add_not_mem hmem c c₀ x y]

/-! ## 8.9 ★★★ W27 泳道 e：(P1) 的**相容部分** —— 剥离只毁掉与 `s` 不相容的 d-split

`§8.6` 的 (P1)（Thm 2 的 `α'_{A,B} = α_{A,B} - λ_{A,B}`，对**所有**对）在一般情况下不可逐点加，
因为 `pd` 的差按四元组相对 `s` 的**五种模式**取 `0 / 0 / -2c / 可正可负`。本节证明：
**「可正可负」的两模式恰是 `s` 与 `t` 不相容的情形** ⇒ 只要 `t` 与 `s` 相容，`pd` 就单调不减。

### 机器结论

1. `splitMetric_le_one`：`δ_{s} ≤ 1`；
2. `splitMetric_compat_sum_le_one`：★★ `s` 与 `t` 相容、`a,a' ∈ t.sideA`、`b,b' ∈ t.sideB` ⇒
   `δ_s(a,a') + δ_s(b,b') ≤ 1`（四个交必有一个空 ⇒ `t` 的某一段整体落在 `s` 的同一侧）；
3. `splitMetric_pairing_eq` / `splitMetric_self_sum_le_pair`：在同一条 `≤ 1` 下，
   两种配对的交叉数相等（`u = v`）且 `w ≤ u`（16 情形逐个核对）；
4. `eq_peelMetric_add`：`δ = δ' + c·δ_s`（`δ' = peelMetric δ s` 的反向展开）；
5. ★★★ `isDSplit_of_isDSplit_peelMetric`：**相容的 d-split 在剥离下存活** ——
   `0 ≤ c`、`s` 与 `t` 相容、`t` 是 `δ'` 的 d-split ⇒ `t` 是 `δ` 的 d-split。

### 缺的那一半（(P1) 剩余的**具名**缺件）

`t` 与 `s` **不相容**时 `u ≠ v`（模式 `(2,0,2)` / `(0,2,2)`），`pd` 之差可正可负 ⇒ 需要 BdD 的
**弱相容 / `s(S)`-cluster 结构**（Lemma 3–6，md `:5581/:6094/:6159/:6504`）才能推出
「`δ'` 的 d-split 集合 ⊆ `δ` 的 d-split 集合」。★ 注意 `weaklyCompatible_of_isDSplit`
（`Phylo/SplitWeak.lean`）已给出「全体 d-split 弱相容」，所以这部分不是无从下手，而是**需要 cluster 层**。 -/

/-- `SplitMetric ≤ 1`（`0/1` 值）。 -/
theorem splitMetric_le_one {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) (x y : α) :
    SplitMetric s x y ≤ 1 := by
  unfold SplitMetric
  split_ifs <;> norm_num

/-- ★★ **相容性禁止 `w = 2`**：`s` 与 `t` 相容、`a,a' ∈ t.sideA`、`b,b' ∈ t.sideB` ⇒
`δ_s(a,a') + δ_s(b,b') ≤ 1`。

四个交（`A_s∩A_t`、`A_s∩B_t`、`B_s∩A_t`、`B_s∩B_t`）必有一个空；每个空交都强制
「`t` 的 `A` 段整体在 `s` 同侧」或「`t` 的 `B` 段整体在 `s` 同侧」⇒ 对应 `δ_s = 0`。 -/
theorem splitMetric_compat_sum_le_one {α : Type*} [Fintype α] [DecidableEq α] {s t : Split α}
    (hst : s.Compatible t) {a a' b b' : α}
    (ha : a ∈ t.sideA) (ha' : a' ∈ t.sideA) (hb : b ∈ t.sideB) (hb' : b' ∈ t.sideB) :
    SplitMetric s a a' + SplitMetric s b b' ≤ 1 := by
  have h1 := splitMetric_le_one s a a'
  have h2 := splitMetric_le_one s b b'
  rcases hst with h | h | h | h
  · have haB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr (Finset.disjoint_right.mp h ha)
    have ha'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr (Finset.disjoint_right.mp h ha')
    have hz : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideB haB ha'B
    linarith
  · have hbB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr (Finset.disjoint_right.mp h hb)
    have hb'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr (Finset.disjoint_right.mp h hb')
    have hz : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB hbB hb'B
    linarith
  · have haA : a ∈ s.sideA := by
      by_contra hc
      exact Finset.disjoint_left.mp h ((mem_sideB_iff_not_mem_sideA s a).mpr hc) ha
    have ha'A : a' ∈ s.sideA := by
      by_contra hc
      exact Finset.disjoint_left.mp h ((mem_sideB_iff_not_mem_sideA s a').mpr hc) ha'
    have hz : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA haA ha'A
    linarith
  · have hbA : b ∈ s.sideA := by
      by_contra hc
      exact Finset.disjoint_left.mp h ((mem_sideB_iff_not_mem_sideA s b).mpr hc) hb
    have hb'A : b' ∈ s.sideA := by
      by_contra hc
      exact Finset.disjoint_left.mp h ((mem_sideB_iff_not_mem_sideA s b').mpr hc) hb'
    have hz : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideA hbA hb'A
    linarith

/-- ★★ 在 `w ≤ 1` 下两种配对的交叉数相等：`u = v`（16 情形逐个核对）。 -/
theorem splitMetric_pairing_eq {α : Type*} [Fintype α] [DecidableEq α] {s : Split α}
    {a a' b b' : α} (hw : SplitMetric s a a' + SplitMetric s b b' ≤ 1) :
    SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a b' + SplitMetric s a' b := by
  by_cases h1 : a ∈ s.sideA <;> by_cases h2 : a' ∈ s.sideA <;>
    by_cases h3 : b ∈ s.sideA <;> by_cases h4 : b' ∈ s.sideA <;>
    simp only [SplitMetric, mem_sideB_iff_not_mem_sideA, h1, h2, h3, h4] at * <;>
    norm_num at *

/-- ★★ 在 `w ≤ 1` 下 `w ≤ u`（16 情形逐个核对）。 -/
theorem splitMetric_self_sum_le_pair {α : Type*} [Fintype α] [DecidableEq α] {s : Split α}
    {a a' b b' : α} (hw : SplitMetric s a a' + SplitMetric s b b' ≤ 1) :
    SplitMetric s a a' + SplitMetric s b b' ≤ SplitMetric s a b + SplitMetric s a' b' := by
  by_cases h1 : a ∈ s.sideA <;> by_cases h2 : a' ∈ s.sideA <;>
    by_cases h3 : b ∈ s.sideA <;> by_cases h4 : b' ∈ s.sideA <;>
    simp only [SplitMetric, mem_sideB_iff_not_mem_sideA, h1, h2, h3, h4] at * <;>
    norm_num at *

/-- `δ = δ' + c·δ_s`（`peelMetric` 的**反向**展开，逐点）。 -/
theorem eq_peelMetric_add {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (s : Split α) (x y : α) :
    δ x y = peelMetric δ s x y + peelCoeff δ s * SplitMetric s x y := by
  rw [peelMetric_apply]
  ring

/-- ★★★ **(P1) 的相容部分：相容的 d-split 在剥离下存活**。

`0 ≤ c`（`s` 是 d-split 时 `c > 0` 由 `peelCoeff_pos` 给）、`s` 与 `t` 相容、
`t` 是 `δ' := δ - c·δ_s` 的 d-split ⇒ `t` 也是 `δ` 的 d-split。

★ 证明要点：相容 ⇒ `w = δ_s(a,a') + δ_s(b,b') ≤ 1` ⇒ `u = v` 且 `w ≤ u` ⇒
`pd(δ,q) = pd(δ',q) + c·(u-w) ≥ pd(δ',q)`。 -/
theorem isDSplit_of_isDSplit_peelMetric {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s t : Split α} (hc : 0 ≤ peelCoeff δ s) (hst : s.Compatible t)
    (h : IsDSplit (peelMetric δ s) t.sideA t.sideB) :
    IsDSplit δ t.sideA t.sideB := by
  intro a ha a' ha' b hb b' hb'
  have hp : 0 < pairDeficit (peelMetric δ s) a a' b b' := by
    simp only [pairDeficit, sub_pos]
    exact h a ha a' ha' b hb b' hb'
  have hw1 : SplitMetric s a a' + SplitMetric s b b' ≤ 1 :=
    splitMetric_compat_sum_le_one hst ha ha' hb hb'
  have huv := splitMetric_pairing_eq hw1
  have hwu := splitMetric_self_sum_le_pair hw1
  have key : pairDeficit δ a a' b b' = pairDeficit (peelMetric δ s) a a' b b'
      + peelCoeff δ s * ((SplitMetric s a b + SplitMetric s a' b')
          - (SplitMetric s a a' + SplitMetric s b b')) := by
    unfold pairDeficit
    rw [peelMetric_apply, peelMetric_apply, peelMetric_apply, peelMetric_apply,
      peelMetric_apply, peelMetric_apply]
    have e1 : (δ a b - peelCoeff δ s * SplitMetric s a b)
          + (δ a' b' - peelCoeff δ s * SplitMetric s a' b')
        = (δ a b + δ a' b')
          - peelCoeff δ s * (SplitMetric s a b + SplitMetric s a' b') := by ring
    have e2 : (δ a b' - peelCoeff δ s * SplitMetric s a b')
          + (δ a' b - peelCoeff δ s * SplitMetric s a' b)
        = (δ a b' + δ a' b)
          - peelCoeff δ s * (SplitMetric s a b + SplitMetric s a' b') := by
      rw [huv]
      ring
    have e3 : (δ a a' - peelCoeff δ s * SplitMetric s a a')
          + (δ b b' - peelCoeff δ s * SplitMetric s b b')
        = (δ a a' + δ b b')
          - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by ring
    rw [e1, e2, e3, max_sub_sub_right]
    ring
  have hpd : 0 < pairDeficit δ a a' b b' := by
    rw [key]
    have hnn : 0 ≤ peelCoeff δ s * ((SplitMetric s a b + SplitMetric s a' b')
        - (SplitMetric s a a' + SplitMetric s b b')) := mul_nonneg hc (by linarith)
    linarith
  simp only [pairDeficit, sub_pos] at hpd
  exact hpd
/-! ## 9. ★★★ 修复形态的关键引理：三种「配对」两两不相容（W12l）

**目标**（`fourPointOfSplitMetricSum_gap_correct_shape`）：正权 ＋ 两两相容的 split 度量之和
满足**文献**四点条件 `FourPointStd`（数学内容 = 树度量满足四点条件）。
本节把它**唯一的结构性障碍**证掉，并记录**完整的收尾算法**。

### 已完成：三种配对两两不相容

对固定四元组 `(a,a',b,b')` 定义三种**配对**
（`PairW = {a,a'}|{b,b'}`、`PairP = {a,b}|{a',b'}`、`PairX = {a,b'}|{a',b}`），则**任意两种**的
实现者都**不兼容**（库内 `not_compatible_of_separates` 直接给出）⇒ **两两相容的 `F` 中至多一种配对可被实现** ✓。

### 收尾算法（已推完；本轮未形式化，见报告「诚实边界」）

记 `δ̂ := Σ_{u∈F} w_u·δ_u`（`w_u > 0`），对四元组 `(a,a',b,b')` 记
`W := δ̂aa' + δ̂bb'`、`P := δ̂ab + δ̂a'b'`、`X := δ̂ab' + δ̂a'b`；并令
`c_W := Σ_{u ∈ F, u 实现 W-配对} w_u`，`c_P`、`c_X` 同理（本节结论：三者**至多一个非零**）。逐 `u` 的取值只有五种
（`σ` = 该点在 `u` 的哪一侧，`4` 点分布）：

| 分布 | `(W_u,P_u,X_u)` |
|---|---|
| 全在同一侧 | `(0,0,0)` |
| `1|3` 分布 | `(1,1,1)` |
| `{a,a'} | {b,b'}` | `(0,2,2)` |
| `{a,b} | {a',b'}` | `(2,0,2)` |
| `{a,b'} | {a',b}` | `(2,2,0)` |

⇒ `X − W = 2(c_W − c_X)`、`X − P = 2(c_P − c_X)`；由「至多一种配对被实现」：
若 `c_X > 0`（唯一非零）则 `X − W < 0` ⇒ `X < W` ✓；若 `c_W > 0` 则 `X = P` ✓；若 `c_P > 0` 则 `X = W` ✓；
三者皆零则 `X = W = P` ✓ —— 四种情形都给出 **`X ≤ max W P`**。
对 `W`、`P` 各自重复同一论证（把三种配对轮换）即得 `FourPointStd` 的三个合取项 ✓。
退化情形（四点有重合，例如 `a = a'`）自动成立：此时 `P = X` 精确相等 ⇒ 「最大者至少取两次」✓。 -/

/-- 四元组上的 **W-配对**：`u` 把 `{a,a'}` 与 `{b,b'}` 分开。 -/
abbrev PairW (u : Split X) (a a' b b' : X) : Prop := u.Separates a a' b b'

/-- 四元组上的 **P-配对**：`u` 把 `{a,b}` 与 `{a',b'}` 分开。 -/
abbrev PairP (u : Split X) (a a' b b' : X) : Prop := u.Separates a b a' b'

/-- 四元组上的 **X-配对**：`u` 把 `{a,b'}` 与 `{a',b}` 分开。 -/
abbrev PairX (u : Split X) (a a' b b' : X) : Prop := u.Separates a b' a' b

/-- ★★ **W-配对与 P-配对不相容**。 -/
theorem not_compatible_of_PairW_PairP {u v : Split X} {a a' b b' : X}
    (hu : PairW u a a' b b') (hv : PairP v a a' b b') : ¬ u.Compatible v :=
  not_compatible_of_separates (s := u) (t := v) (a := a) (b := a') (c := b) (e := b') hu hv

/-- ★★ **W-配对与 X-配对不相容**。 -/
theorem not_compatible_of_PairW_PairX {u v : Split X} {a a' b b' : X}
    (hu : PairW u a a' b b') (hv : PairX v a a' b b') : ¬ u.Compatible v :=
  not_compatible_of_separates (s := u) (t := v) (a := a) (b := a') (c := b') (e := b)
    ((separates_comm_last u a a' b b').mp hu) hv

/-- ★★ **P-配对与 X-配对不相容**。 -/
theorem not_compatible_of_PairP_PairX {u v : Split X} {a a' b b' : X}
    (hu : PairP u a a' b b') (hv : PairX v a a' b b') : ¬ u.Compatible v :=
  not_compatible_of_separates (s := u) (t := v) (a := a) (b := b) (c := b') (e := a')
    ((separates_comm_last u a b a' b').mp hu) ((separates_comm_last v a b' a' b).mp hv)

/-- ★★★ **两两相容的 `F` 中至多一种配对可被实现**（W/P 版）。 -/
theorem not_PairW_and_PairP {F : Finset (Split X)}
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) {a a' b b' : X} :
    ¬ ((∃ u ∈ F, PairW u a a' b b') ∧ (∃ v ∈ F, PairP v a a' b b')) := by
  rintro ⟨⟨u, huF, hu⟩, ⟨v, hvF, hv⟩⟩
  exact not_compatible_of_PairW_PairP hu hv (hF u huF v hvF)

/-- ★★★ **两两相容的 `F` 中至多一种配对可被实现**（W/X 版）。 -/
theorem not_PairW_and_PairX {F : Finset (Split X)}
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) {a a' b b' : X} :
    ¬ ((∃ u ∈ F, PairW u a a' b b') ∧ (∃ v ∈ F, PairX v a a' b b')) := by
  rintro ⟨⟨u, huF, hu⟩, ⟨v, hvF, hv⟩⟩
  exact not_compatible_of_PairW_PairX hu hv (hF u huF v hvF)

/-- ★★★ **两两相容的 `F` 中至多一种配对可被实现**（P/X 版）。 -/
theorem not_PairP_and_PairX {F : Finset (Split X)}
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) {a a' b b' : X} :
    ¬ ((∃ u ∈ F, PairP u a a' b b') ∧ (∃ v ∈ F, PairX v a a' b b')) := by
  rintro ⟨⟨u, huF, hu⟩, ⟨v, hvF, hv⟩⟩
  exact not_compatible_of_PairP_PairX hu hv (hF u huF v hvF)

/-! ## 10. 修复形态的**计算核心**（W12m/W12n：`bSep` 方案）

按 §9 的收尾算法与「两个工具链坑」的结论，本节把逐 split 求值改为 **`Bool` 谓词** 驱动
（`Bool` 等式的可判定实例现成 ⇒ `if … = true then … else …` 恒可判定 ⇒ 坑 1 消解；
不再写析取 ⇒ 坑 2 消解）：

* `bSep u x y : Bool` —— `x,y` 是否被 `u` 分到两侧（`decide (x ∈ sideA) != decide (y ∈ sideA)`）；
* `SplitMetric u x y = if bSep u x y = true then 1 else 0`；
* `bPairW/bPairP/bPairX : Bool` —— 三种配对的**布尔**判据，与 §9 的 `PairW/PairP/PairX` 等价。 -/

/-- `x ∈ u.sideB ↔ x ∉ u.sideA`（两侧互补；逐 split 求值的基础砖）。 -/
theorem mem_sideB_iff (u : Split X) (x : X) : x ∈ u.sideB ↔ x ∉ u.sideA := by
  constructor
  · intro hb ha
    exact (Finset.disjoint_left.mp (disjoint_sides u)) ha hb
  · intro ha
    have h : x ∈ u.sideA ∪ u.sideB := by
      rw [union_sides]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp h with h' | h'
    · exact absurd h' ha
    · exact h'

/-- `Bool` 型分离谓词：`x`、`y` 是否被 `u` 分到两侧。 -/
def bSep (u : Split X) (x y : X) : Bool :=
  decide (x ∈ u.sideA) != decide (y ∈ u.sideA)

/-- ★ **`SplitMetric` 的 `Bool` 形式**（条件是可判定的 `Bool` 等式）。 -/
theorem splitMetric_eq_bSep (u : Split X) (x y : X) :
    SplitMetric u x y = if bSep u x y = true then 1 else 0 := by
  by_cases hx : x ∈ u.sideA <;> by_cases hy : y ∈ u.sideA <;>
    simp only [SplitMetric, bSep, mem_sideB_iff, hx, hy] <;> norm_num

/-- **W-配对的布尔判据**（`{a,a'}` 同侧、`{b,b'}` 同侧、`a,b` 异侧）。 -/
abbrev bPairW (u : Split X) (a a' b b' : X) : Bool :=
  (bSep u a a' == false) && (bSep u b b' == false) && (bSep u a b == true)

/-- **P-配对的布尔判据**（`{a,b}` 同侧、`{a',b'}` 同侧、`a,a'` 异侧）。 -/
abbrev bPairP (u : Split X) (a a' b b' : X) : Bool :=
  (bSep u a b == false) && (bSep u a' b' == false) && (bSep u a a' == true)

/-- **X-配对的布尔判据**（`{a,b'}` 同侧、`{a',b}` 同侧、`a,a'` 异侧）。 -/
abbrev bPairX (u : Split X) (a a' b b' : X) : Bool :=
  (bSep u a b' == false) && (bSep u a' b == false) && (bSep u a a' == true)

/-! ### 10.1 布尔判据与 §9 的 Prop 判据等价（**至多一个非零**因此可用于布尔筛选） -/

/-- `bPairW = true ↔ PairW`。 -/
theorem bPairW_eq_true_iff (u : Split X) (a a' b b' : X) :
    bPairW u a a' b b' = true ↔ PairW u a a' b b' := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [bPairW, bSep, PairW, Separates, mem_sideB_iff, ha, ha', hb, hb'] <;> decide

/-- `bPairP = true ↔ PairP`。 -/
theorem bPairP_eq_true_iff (u : Split X) (a a' b b' : X) :
    bPairP u a a' b b' = true ↔ PairP u a a' b b' := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [bPairP, bSep, PairP, Separates, mem_sideB_iff, ha, ha', hb, hb'] <;> decide

/-- `bPairX = true ↔ PairX`。 -/
theorem bPairX_eq_true_iff (u : Split X) (a a' b b' : X) :
    bPairX u a a' b b' = true ↔ PairX u a a' b b' := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [bPairX, bSep, PairX, Separates, mem_sideB_iff, ha, ha', hb, hb'] <;> decide

/-! ### 10.2 逐 split 差分恒等式（收尾算法的计算核心） -/

/-- ★★★ **逐 split：`X_u − W_u = 2·[W-配对] − 2·[X-配对]`**（五个取值情形逐项核对）。 -/
theorem splitMetric_diff_W (u : Split X) (a a' b b' : X) :
    (SplitMetric u a b' + SplitMetric u a' b) - (SplitMetric u a a' + SplitMetric u b b')
      = (if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairX u a a' b b' = true then (2 : ℝ) else 0) := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [SplitMetric, bPairW, bPairX, bSep, mem_sideB_iff, ha, ha', hb, hb'] <;>
    norm_num

/-- ★★★ **逐 split：`X_u − P_u = 2·[P-配对] − 2·[X-配对]`**。 -/
theorem splitMetric_diff_P (u : Split X) (a a' b b' : X) :
    (SplitMetric u a b' + SplitMetric u a' b) - (SplitMetric u a b + SplitMetric u a' b')
      = (if bPairP u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairX u a a' b b' = true then (2 : ℝ) else 0) := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [SplitMetric, bPairP, bPairX, bSep, mem_sideB_iff, ha, ha', hb, hb'] <;>
    norm_num

/-! ### 10.3 拆和：`X − W = 2c_W − 2c_X`、`X − P = 2c_P − 2c_X`（施工图第 2 步） -/

/-- 指标和：`∑ w u · (if p u then c else 0) = c · ∑_{u ∈ F.filter p} w u`。 -/
theorem sum_mul_ite_eq {ι : Type*} (F : Finset ι) (w : ι → ℝ) (p : ι → Prop) [DecidablePred p]
    (c : ℝ) : (∑ u ∈ F, w u * (if p u then c else 0)) = c * ∑ u ∈ F.filter p, w u := by
  rw [Finset.mul_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun u _ => by by_cases h : p u <;> simp [h, mul_comm]

/-- ★★★ **拆和（W 分量）**：`X − W = 2c_W − 2c_X`。 -/
theorem splitMetricSum_diff_W (F : Finset (Split X)) (w : Split X → ℝ) (a a' b b' : X) :
    (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
        - ((∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b'))
      = 2 * (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u)
        - 2 * (∑ u ∈ F.filter (fun u => bPairX u a a' b b' = true), w u) := by
  have h1 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      = ∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b) :=
    Finset.sum_add_distrib.symm
  have h2 : (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
      = ∑ u ∈ F, (w u * SplitMetric u a a' + w u * SplitMetric u b b') :=
    Finset.sum_add_distrib.symm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [show (∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b
        - (w u * SplitMetric u a a' + w u * SplitMetric u b b')))
      = ∑ u ∈ F, w u * ((if bPairW u a a' b b' = true then (2 : ℝ) else 0)
          - (if bPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by
      rw [show w u * SplitMetric u a b' + w u * SplitMetric u a' b
            - (w u * SplitMetric u a a' + w u * SplitMetric u b b')
          = w u * ((SplitMetric u a b' + SplitMetric u a' b)
            - (SplitMetric u a a' + SplitMetric u b b')) from by ring,
        splitMetric_diff_W u a a' b b']]
  rw [show (∑ u ∈ F, w u * ((if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairX u a a' b b' = true then (2 : ℝ) else 0)))
      = ∑ u ∈ F, (w u * (if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - w u * (if bPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by ring]
  rw [Finset.sum_sub_distrib,
    sum_mul_ite_eq F w (fun u => bPairW u a a' b b' = true) 2,
    sum_mul_ite_eq F w (fun u => bPairX u a a' b b' = true) 2]

/-- ★★★ **拆和（P 分量）**：`X − P = 2c_P − 2c_X`。 -/
theorem splitMetricSum_diff_P (F : Finset (Split X)) (w : Split X → ℝ) (a a' b b' : X) :
    (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
        - ((∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b'))
      = 2 * (∑ u ∈ F.filter (fun u => bPairP u a a' b b' = true), w u)
        - 2 * (∑ u ∈ F.filter (fun u => bPairX u a a' b b' = true), w u) := by
  have h1 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      = ∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b) :=
    Finset.sum_add_distrib.symm
  have h2 : (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
      = ∑ u ∈ F, (w u * SplitMetric u a b + w u * SplitMetric u a' b') :=
    Finset.sum_add_distrib.symm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [show (∑ u ∈ F, (w u * SplitMetric u a b' + w u * SplitMetric u a' b
        - (w u * SplitMetric u a b + w u * SplitMetric u a' b')))
      = ∑ u ∈ F, w u * ((if bPairP u a a' b b' = true then (2 : ℝ) else 0)
          - (if bPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by
      rw [show w u * SplitMetric u a b' + w u * SplitMetric u a' b
            - (w u * SplitMetric u a b + w u * SplitMetric u a' b')
          = w u * ((SplitMetric u a b' + SplitMetric u a' b)
            - (SplitMetric u a b + SplitMetric u a' b')) from by ring,
        splitMetric_diff_P u a a' b b']]
  rw [show (∑ u ∈ F, w u * ((if bPairP u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairX u a a' b b' = true then (2 : ℝ) else 0)))
      = ∑ u ∈ F, (w u * (if bPairP u a a' b b' = true then (2 : ℝ) else 0)
        - w u * (if bPairX u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by ring]
  rw [Finset.sum_sub_distrib,
    sum_mul_ite_eq F w (fun u => bPairP u a a' b b' = true) 2,
    sum_mul_ite_eq F w (fun u => bPairX u a a' b b' = true) 2]

/-! ### 10.4 主不等式与收口（施工图第 3–4 步） -/

/-- `SplitMetric` 对两个自变量对称。 -/
theorem splitMetric_comm (u : Split X) (x y : X) : SplitMetric u x y = SplitMetric u y x := by
  by_cases hx : x ∈ u.sideA <;> by_cases hy : y ∈ u.sideA <;>
    simp only [SplitMetric, mem_sideB_iff, hx, hy] <;> norm_num

/-- 加权和也对称。 -/
theorem splitMetricSum_comm (F : Finset (Split X)) (w : Split X → ℝ) (x y : X) :
    (∑ u ∈ F, w u * SplitMetric u x y) = ∑ u ∈ F, w u * SplitMetric u y x :=
  Finset.sum_congr rfl fun u _ => by rw [splitMetric_comm u x y]

/-- ★★★ **主不等式**：`X ≤ max W P`。四情形都归结为「三种配对至多一种被实现」。 -/
theorem splitMetricSum_X_le_max (F : Finset (Split X)) (w : Split X → ℝ)
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) (hw : ∀ s ∈ F, 0 < w s) (a a' b b' : X) :
    (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      ≤ max ((∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b'))
            ((∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')) := by
  classical
  have hXW := splitMetricSum_diff_W F w a a' b b'
  have hXP := splitMetricSum_diff_P F w a a' b b'
  by_cases hXn : (F.filter (fun u => bPairX u a a' b b' = true)).Nonempty
  · obtain ⟨u, hu⟩ := hXn
    obtain ⟨huF, huX⟩ := Finset.mem_filter.mp hu
    have hPairX : PairX u a a' b b' := (bPairX_eq_true_iff u a a' b b').mp huX
    have hWne : ¬ (F.filter (fun v => bPairW v a a' b b' = true)).Nonempty := fun h => by
      obtain ⟨v, hv⟩ := h
      obtain ⟨hvF, hvW⟩ := Finset.mem_filter.mp hv
      exact (not_PairW_and_PairX hF) ⟨⟨v, hvF, (bPairW_eq_true_iff v a a' b b').mp hvW⟩,
        ⟨u, huF, hPairX⟩⟩
    have hPne : ¬ (F.filter (fun v => bPairP v a a' b b' = true)).Nonempty := fun h => by
      obtain ⟨v, hv⟩ := h
      obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
      exact (not_PairP_and_PairX hF) ⟨⟨v, hvF, (bPairP_eq_true_iff v a a' b b').mp hvP⟩,
        ⟨u, huF, hPairX⟩⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hWne hPne
    rw [hWne, Finset.sum_empty] at hXW
    rw [hPne, Finset.sum_empty] at hXP
    have hXnn : 0 ≤ ∑ v ∈ F.filter (fun v => bPairX v a a' b b' = true), w v :=
      Finset.sum_nonneg fun v hv => le_of_lt (hw v (Finset.mem_filter.mp hv).1)
    have h1 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
        ≤ (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b') := by
      linarith
    exact le_trans h1 (le_max_left _ _)
  · have hXe : F.filter (fun v => bPairX v a a' b b' = true) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hXn
    have hX0 : (∑ v ∈ F.filter (fun v => bPairX v a a' b b' = true), w v) = 0 := by
      rw [hXe, Finset.sum_empty]
    rw [hX0] at hXW hXP
    by_cases hWn : (F.filter (fun u => bPairW u a a' b b' = true)).Nonempty
    · obtain ⟨u, hu⟩ := hWn
      obtain ⟨huF, huW⟩ := Finset.mem_filter.mp hu
      have hPairW : PairW u a a' b b' := (bPairW_eq_true_iff u a a' b b').mp huW
      have hPne : ¬ (F.filter (fun v => bPairP v a a' b b' = true)).Nonempty := fun h => by
        obtain ⟨v, hv⟩ := h
        obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
        exact (not_PairW_and_PairP hF) ⟨⟨u, huF, hPairW⟩,
          ⟨v, hvF, (bPairP_eq_true_iff v a a' b b').mp hvP⟩⟩
      rw [Finset.not_nonempty_iff_eq_empty] at hPne
      rw [hPne, Finset.sum_empty] at hXP
      have h2 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
          = (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b') := by
        linarith
      exact le_trans (le_of_eq h2) (le_max_right _ _)
    · have hWe : F.filter (fun v => bPairW v a a' b b' = true) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hWn
      have hW0 : (∑ v ∈ F.filter (fun v => bPairW v a a' b b' = true), w v) = 0 := by
        rw [hWe, Finset.sum_empty]
      rw [hW0] at hXW
      have h3 : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
          = (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b') := by
        linarith
      exact le_trans (le_of_eq h3) (le_max_left _ _)

/-- ★★★ **收口**：修复形态（结论用 `FourPointStd`）**已成定理**（原 `def` 逐字保留）。
三个合取项由主不等式 `splitMetricSum_X_le_max` 在三个**重标号**下给出（`max` 次序用 `max_comm` 对齐，
`D x y = D y x` 用 `splitMetricSum_comm` 对齐）：

* `(a, b, b', a')` ⇒ `W ≤ max P X`；
* `(a, b', a', b)` ⇒ `P ≤ max X W`（再用 `max_comm`）；
* `(a, a', b, b')` ⇒ `X ≤ max W P`。 -/
theorem fourPointOfSplitMetricSum_gap_correct_shape_proof :
    fourPointOfSplitMetricSum_gap_correct_shape := by
  intro α _ _ F w hF hw a a' b b'
  refine ⟨?_, ?_, ?_⟩
  · have h := splitMetricSum_X_le_max F w hF hw a b b' a'
    rw [splitMetricSum_comm F w b' a', splitMetricSum_comm F w b a'] at h
    exact h
  · rw [max_comm]
    have h := splitMetricSum_X_le_max F w hF hw a b' a' b
    rw [splitMetricSum_comm F w b' a', splitMetricSum_comm F w b' b] at h
    exact h
  · have h := splitMetricSum_X_le_max F w hF hw a a' b b'
    exact h

/-! ### 10.5 ★B 对照见证 -/

/-- ★B **对照见证**：在 §7 中**注册形态被反驳**的那个 `F := cexF2`（两两相容、`w ≡ 1`）上，
**修复形态成立** ⇒ 一真一假并列可见 ✓。 -/
example : FourPointStd (fun x y : Fin 4 => ∑ s ∈ cexF2, (1 : ℝ) * SplitMetric s x y) :=
  fourPointOfSplitMetricSum_gap_correct_shape_proof cexF2 (fun _ => (1 : ℝ)) cexF2_compat
    (by intro s _; norm_num)

/-! ## 11. (B2) 的**加法核心**与**归约**（W12p）

`notIsDSplit_of_splitMetricSum_gap`（非成员不是 `max`-d-split）经本节的机械部分归约为
**一条纯组合命题**（见 §11.3 的 `noWRealizer_exists_gap`）：

* 逐 split 的五情形表已由差分恒等式给出（§10.2）：`X_u − W_u = 2[bPairW] − 2[bPairX]`、`X_u − P_u = 2[bPairP] − 2[bPairX]`；
  本节补齐**第三条**：`P_u − W_u = 2[bPairW] − 2[bPairP]`（此处 `W_u = LHS_u` 为「同侧内和」）；
* 求和 ⇒ `X − LHS = 2c_W − 2c_X`、`P − LHS = 2c_W − 2c_P`（`c_W/c_P/c_X` = 相应筛选和）；
* ⇒ **若某四元组的 `c_W = 0`，则该四元组使 `IsDSplit` 失败** ⇒ `¬ IsDSplit` ✓（一个反例四元组即够）；
* ⇒ 只剩「**存在四元组使 `c_W = 0`**」（`noWRealizer_exists_gap`，穷举无反例，见脚本）。 -/

/-- ★★★ **逐 split 第三条差分恒等式**：`P_u − W_u = 2·[bPairW] − 2·[bPairP]`。 -/
theorem splitMetric_diff_PW (u : Split X) (a a' b b' : X) :
    (SplitMetric u a b + SplitMetric u a' b') - (SplitMetric u a a' + SplitMetric u b b')
      = (if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairP u a a' b b' = true then (2 : ℝ) else 0) := by
  by_cases ha : a ∈ u.sideA <;> by_cases ha' : a' ∈ u.sideA <;>
    by_cases hb : b ∈ u.sideA <;> by_cases hb' : b' ∈ u.sideA <;>
    simp only [SplitMetric, bPairW, bPairP, bSep, mem_sideB_iff, ha, ha', hb, hb'] <;>
    norm_num

/-- ★★★ **拆和（P − W）**：`P − W = 2c_W − 2c_P`。 -/
theorem splitMetricSum_diff_PW (F : Finset (Split X)) (w : Split X → ℝ) (a a' b b' : X) :
    (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
        - ((∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b'))
      = 2 * (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u)
        - 2 * (∑ u ∈ F.filter (fun u => bPairP u a a' b b' = true), w u) := by
  have h1 : (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
      = ∑ u ∈ F, (w u * SplitMetric u a b + w u * SplitMetric u a' b') :=
    Finset.sum_add_distrib.symm
  have h2 : (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
      = ∑ u ∈ F, (w u * SplitMetric u a a' + w u * SplitMetric u b b') :=
    Finset.sum_add_distrib.symm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  rw [show (∑ u ∈ F, (w u * SplitMetric u a b + w u * SplitMetric u a' b'
        - (w u * SplitMetric u a a' + w u * SplitMetric u b b')))
      = ∑ u ∈ F, w u * ((if bPairW u a a' b b' = true then (2 : ℝ) else 0)
          - (if bPairP u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by
      rw [show w u * SplitMetric u a b + w u * SplitMetric u a' b'
            - (w u * SplitMetric u a a' + w u * SplitMetric u b b')
          = w u * ((SplitMetric u a b + SplitMetric u a' b')
            - (SplitMetric u a a' + SplitMetric u b b')) from by ring,
        splitMetric_diff_PW u a a' b b']]
  rw [show (∑ u ∈ F, w u * ((if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - (if bPairP u a a' b b' = true then (2 : ℝ) else 0)))
      = ∑ u ∈ F, (w u * (if bPairW u a a' b b' = true then (2 : ℝ) else 0)
        - w u * (if bPairP u a a' b b' = true then (2 : ℝ) else 0)) from
    Finset.sum_congr rfl fun u _ => by ring]
  rw [Finset.sum_sub_distrib,
    sum_mul_ite_eq F w (fun u => bPairW u a a' b b' = true) 2,
    sum_mul_ite_eq F w (fun u => bPairP u a a' b b' = true) 2]

/-! ### 11.1 归约：`c_W = 0` 的四元组 ⇒ `¬ IsDSplit`（一个反例四元组即够） -/

/-- ★★★ **归约**：若某四元组（`a,a' ∈ S.sideA`、`b,b' ∈ S.sideB`）**没有 `W`-实现者**
（即 `c_W = 0`），则 `S` **不是** `δ̂ := Σ w·δ_u` 的 `d`-split（`IsDSplit` 的 `max` 形式）。 -/
theorem not_isDSplit_of_no_W_realizer (F : Finset (Split X)) (w : Split X → ℝ)
    (hw : ∀ s ∈ F, 0 < w s) (S : Split X) {a a' b b' : X} (ha : a ∈ S.sideA) (ha' : a' ∈ S.sideA)
    (hb : b ∈ S.sideB) (hb' : b' ∈ S.sideB)
    (hW0 : (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u) = 0) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) S.sideA S.sideB := by
  intro hDS
  have h1 := hDS a ha a' ha' b hb b' hb'
  have hXW := splitMetricSum_diff_W F w a a' b b'
  have hPW := splitMetricSum_diff_PW F w a a' b b'
  rw [hW0] at hXW hPW
  have hXnn : 0 ≤ ∑ u ∈ F.filter (fun u => bPairX u a a' b b' = true), w u :=
    Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hPnn : 0 ≤ ∑ u ∈ F.filter (fun u => bPairP u a a' b b' = true), w u :=
    Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hXle : (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
      ≤ (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b') := by
    linarith
  have hPle : (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
      ≤ (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b') := by
    linarith
  exact not_lt_of_ge (max_le hXle hPle) h1

/-! ### 11.2 (★′) 纯组合命题（登记）与 (B2) 的条件收口 -/

/-- ⬜ **(★′)（W12p 登记；未证）**：两两相容 `F` ＋ 正权重、`S ∉ F ± swap` 时，**存在**四元组
`a, a' ∈ S.sideA`、`b, b' ∈ S.sideB`，使**没有** `u ∈ F` 把 `{a,a'}` 与 `{b,b'}` 分开
（等价说法：该四元组的 `c_W = 0`）。

⇒ 由 §11.1 的 `not_isDSplit_of_no_W_realizer`，(★′) 一成立即得 (B2)（见
`notIsDSplit_of_splitMetricSum_gap_proof`）✓。
**穷举证据**（`scripts/msc/w12d_b2_b1_search.py`，精确有理数、无 Monte Carlo，`exit 0`）：
`n = 4`（`F` ≤ 3，权重 ∈ {1,2}）、`n = 5`（`F` ≤ 2, 3, **4**）、`n = 6`（`F` ≤ 2, **3**）的**全部**两两相容族
（共 **2674** 个族）上，(B2) 与 (★′) 反例均 **0** 例 ✓ ⇒ 命题**倾向为真**（W12q 加压检索后仍无反例）。

### 本轮（W12q）的进展与**精确卡点**（供下一轮直接接续）

**已排除的路线（勿重复）**：
1. **「点对版」不够**：取 `a = a'`、`b = b'`（即只需「某对 `(a,b)` 不被任何 `u ∈ F` 分开」）**不充分** ——
   星形树见证：`F = {四条平凡 split}`、`S = {0,1}|{2,3}` 时每对 `(a,b) ∈ S.sideA × S.sideB` 都被切开，
   但四元组 `(0,1,2,3)` 的 `c_W = 0` ✓（必须用**四元组**，不能用点对）。
2. **「固定 `ρ ∈ S.sideB`、只看 `u` 避开 `ρ` 的一侧 `u*`」**（即要求 `∃ a,a' ∈ S.sideA` 使没有 `u* ⊇ {a,a'}`）
   **不充分**：`F = { {0,1}|{2,3} }`、`S = {0,1}|{2,3}`（`S = u` ✗ 被排除）之外的组合里，
   `u* ⊇ S.sideA` 的情形确实存在（此时 `(a,a',ρ,ρ)` 全部被实现 ✗），必须改用 `b ≠ b'` 的四元组。
   （星形见证的另一面：`F = 四条平凡 split 去掉 {0}|rest`、`S = {0}|{1,2,3}` 时 `(0,0,1,1)` 被实现 ✗
   而 `(0,0,1,2)` 不被实现 ✓ —— 关键在 `{b,b'}` 被某个 `u` **内部切开**。）

**最有希望的两条路线**：
* **(R1) 层析（laminar）路线**：固定 `ρ ∈ S.sideB`，`u* := u` 的**不含 `ρ` 的那一侧**；
  由两两相容 + 库内 `laminar_of_sidesCompatible_of_notMem` 得 `{u*}` **层析** ✓；
  再用 `S ∉ F±swap` 在层析族里找一个「不包含任何 `a,a'` 配对的极小元」⇒ 取该元外的两点给出反例四元组。
  **卡点**：需要把「层析 + `S ∉ F±swap`」翻成「存在一对 `a,a' ∈ S.sideA` 与某个 `b,b'` 的组合不被任何 `u` 实现」——
  这一步的归纳/极小性论证我本轮没做出来（`S` 的两侧与层析族的相互位置分情形较多）。
* **(R2) 「同侧或切开」充分条件（W12r 已**修正**下面的判据，勿用错误版）**：
  固定 `ρ ∈ S.sideB`，记 `u*` 为 `u` 的**不含 `ρ` 的那一侧**（`u⁺` 为含 `ρ` 的一侧）。则
  > `u` 实现 `W`（把 `{a,a'}` 与 `{b,b'}` 分开）**⟺** `({a,a'} ⊆ u* ∧ {b,b'} ⊆ u⁺) ∨ ({a,a'} ⊆ u⁺ ∧ {b,b'} ⊆ u*)`
  （**注意**：`{b,b'} ⊄ u*` **并不**推出 `{b,b'} ⊆ u⁺` —— `{b,b'}` 可能**横跨** `u*`/`u⁺`；
  我 W12q 记的「恰好一对 `⊆ u*`」是**错的** ✗，正确读法是「一对全在 `u*`、另一对全在 `u⁺`」。）
  ⇒ 充分条件：存在 `a,a' ∈ S.sideA`、`b,b' ∈ S.sideB`，使**每个** `u ∈ F` 满足
  「`{a,a'}`、`{b,b'}` **同在 `u` 的同一侧**」或「`u` **横跨**其中至少一对」⇒ 无 `u` 实现 `W` ⇒ `c_W = 0` ✓。
  星形见证正走此路（`F = 四条平凡 split`、`S = {0,1}|{2,3}`、四元组 `(0,1,2,3)`；
  `u = {2}|rest` 横跨 `{2,3}` ✓）。
  **下一轮建议的第一步（已推出的关键子事实 (F1)，纯 `Finset` 推理、不含求和）**：
  > 若 `u ∈ F` 且 `S.sideA ⊆ u*`，则 **`u* ∩ S.sideB ≠ ∅`** ——
  > 否则（`S.sideA ⊆ u*` 且 `u* ∩ S.sideB = ∅`）由 `S.sideA ∪ S.sideB = univ` 得 `u* = S.sideA`，
  > 即 `u ∈ {S, S.swap}` ✗，与 `S ∉ F±swap` 矛盾 ✓。
  ⇒ (F1) 说明「`u*` 吞掉整个 `S.sideA`」时它一定也碰到 `S.sideB`，因此可以取 `b ∈ u* ∩ S.sideB` 让
  `{a,a'}`、`{b,b}` 同在 `u*` 内（同侧 ✓）；**卡点**：这个 `b` 依赖 `u`，而四元组 `(a,a',b,b')`
  必须**同时**对所有 `u ∈ F` 生效 —— 需要层析族上的极小性/归纳把 `b` 选成「对所有 `u` 同时可用」的那个。
  ⇒ 建议下一轮顺序：**(F1) → 层析极小元 → 一次选出 `b,b'`**。
★★★ **2026-10-17 W23：本缺口已证成 ✅**（`def` 本体逐字未动 ✓）。
上面列的两条已作废路线与 (R1)/(R2) 只是当时的探路记录；**真正成功的路线在 §11.10**
（`Split.noWRealizer_core`，零新增公理）。要点：**(i)** `pairW_sideNotMem`（若 `u` 在
`(a,a',ρ,b)` 上实现 `W`，则 `a,a'` 同在 `u* = sideNotMem u ρ` 内、`b` 在外）⇒ 取
`b := b' := ρ` 可先杀掉第二个析取项；**(ii)** `laminar_sideNotMem`（`{u*}` 两两嵌嵌）
⇒ 含定点的 cluster 构成**链**，小心取最小元就够，**不需要**已被证伪的「极小 cluster」
命题 (★″) `minimalCluster_exists_gap` ✗；**(iii)** 分两情形（存在无公共 cluster 的对 / 每对都有），
后者用「含 `a₀` 与 `p` 的 cluster 的**最小基数**」在 `S.sideA` 上取最大者逐步嵌嵌定位
（`S.sideA ⊆ u₁*`、`u₁* ∩ S.sideB ≠ ∅`、最后一步用基数推相等）✓。
⇒ 既得 `theorem noWRealizer_exists_gap_proof : noWRealizer_exists_gap.{0}` ✓（零 `sorry` / 零 `axiom`）。 -/
def noWRealizer_exists_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) → (∀ s ∈ F, 0 < w s) →
      ∀ S : Split α, (∀ t ∈ F, t ≠ S ∧ t.swap ≠ S) →
        ∃ a ∈ S.sideA, ∃ a' ∈ S.sideA, ∃ b ∈ S.sideB, ∃ b' ∈ S.sideB,
          (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u) = 0

/-- ★★★ **(B2) 的收口形态（条件版）**：由 (★′) `noWRealizer_exists_gap` **即得**注册形态
`notIsDSplit_of_splitMetricSum_gap`（原 `def` 逐字保留 ✓）。
即：本轮的机械部分（三条差分恒等式 ＋ 归约）把 (B2) **完全归结**为 (★′) 这条纯组合命题 ✓。 -/
theorem notIsDSplit_of_splitMetricSum_gap_proof (h : noWRealizer_exists_gap.{0}) :
    notIsDSplit_of_splitMetricSum_gap.{0} := by
  intro α _ _ F w hF hw S hS
  obtain ⟨a, ha, a', ha', b, hb, b', hb', hW0⟩ := h F w hF hw S hS
  exact not_isDSplit_of_no_W_realizer F w hw S ha ha' hb hb' hW0

/-! ### 11.3 (F1)：层析极小性路线的第一步 -/

/-- `u` 的**不含 `ρ` 的那一侧**（`ρ` 固定；(R2)/(F1) 里的 `u*`）。 -/
def sideNotMem (u : Split X) (ρ : X) : Finset X := if ρ ∈ u.sideA then u.sideB else u.sideA

/-- `x ∈ u.sideA ↔ x ∉ u.sideB`（`mem_sideB_iff` 的对偶读法）。 -/
theorem mem_sideA_iff_not_mem_sideB (u : Split X) (x : X) : x ∈ u.sideA ↔ x ∉ u.sideB := by
  rw [← not_iff_not, not_not]
  exact (mem_sideB_iff u x).symm

/-- ★★★ **(F1)**：设 `u* := sideNotMem u ρ`（`u` 的不含 `ρ` 的一侧）。若 `S.sideA ⊆ u*`，
且 `u` 的两侧既不是 `S.sideA` 也不是 `S.sideB`（即 `u ∉ {S, S.swap}` 的**侧等价形式**，
以避免依赖结构外延引理），则 `u* ∩ S.sideB ≠ ∅` ✓。

证明（纯集合包含）：反设 `u* ∩ S.sideB = ∅`；由 `S.sideA ⊆ u*` ＋ `S.sideA ∪ S.sideB = univ`
得 `u* = S.sideA`，再用 `u*` 的定义与两侧互补（`mem_sideB_iff`）推出 `u.sideA = S.sideB`
或 `u.sideA = S.sideA`，与两条假设矛盾 ✓。 -/
theorem sideA_subset_sideNotMem_meets (S u : Split X) {ρ : X}
    (hA : u.sideA ≠ S.sideA) (hA' : u.sideA ≠ S.sideB) (h : S.sideA ⊆ sideNotMem u ρ) :
    (sideNotMem u ρ ∩ S.sideB).Nonempty := by
  classical
  have key : ∀ U : Finset X, S.sideA ⊆ U → U ∩ S.sideB = ∅ → U = S.sideA := by
    intro U hsub hemp
    refine Finset.Subset.antisymm (fun x hx => ?_) hsub
    by_contra hxS
    have hxB : x ∈ S.sideB := (mem_sideB_iff S x).mpr hxS
    have hmem : x ∈ U ∩ S.sideB := Finset.mem_inter.mpr ⟨hx, hxB⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty x hmem
  by_cases hu : ρ ∈ u.sideA
  · have hB : sideNotMem u ρ = u.sideB := by simp only [sideNotMem, hu, ite_true]
    rw [hB] at h ⊢
    by_cases hne : (u.sideB ∩ S.sideB).Nonempty
    · exact hne
    · have heqA : u.sideA = S.sideB := by
        refine Finset.ext fun x => ?_
        rw [mem_sideA_iff_not_mem_sideB u x,
          key u.sideB h (Finset.not_nonempty_iff_eq_empty.mp hne)]
        exact (mem_sideB_iff S x).symm
      exact absurd heqA hA'
  · have hAe : sideNotMem u ρ = u.sideA := by simp only [sideNotMem, hu, ite_false]
    rw [hAe] at h ⊢
    by_cases hne : (u.sideA ∩ S.sideB).Nonempty
    · exact hne
    · exact absurd (key u.sideA h (Finset.not_nonempty_iff_eq_empty.mp hne)) hA

/-! ### 11.4 (★′) 极小性用的基建：`u*` 恒避开 `ρ` -/

/-- `u*`（即 `sideNotMem u ρ`，`u` 的不含 `ρ` 的一侧）恒**避开 `ρ`** ✓ ——
层析引理 `laminar_of_sidesCompatible_of_notMem` 的两个 `notMem` 前提由此得到 ✓。

（附注：本仓库 **已有** `Split.sideB_eq_compl : u.sideB = u.sideAᶜ` ✓，无需新增；
又 `Split` 是 `abbrev KPartition α 2` ⇒ **没有** `Split.ext` ✗，外延请走 `KPartition` 或侧等式 ＋ `mem_sideB_iff` ✓。） -/
theorem notMem_sideNotMem (u : Split X) (ρ : X) : ρ ∉ sideNotMem u ρ := by
  by_cases h : ρ ∈ u.sideA
  · simp only [sideNotMem, h, ite_true]
    exact Finset.disjoint_left.mp (disjoint_sides u) h
  · simpa only [sideNotMem, h, ite_false] using h

/-! ### 11.5 ★C 卫生：(F1) 与库内 `cluster` 对齐（**避免重复造轮子**） -/

/-- ★ **`sideNotMem` 与库内 `Split.cluster` 是同一个东西**（两者定义体逐字相同）✓ ——
库内已有 `notMem_cluster`、`cluster_eq_sideA_or_compl`、`sidesCompatible_cluster`、
以及**层析引理 `laminar_of_compatible_clusters`** ✓，故 (★′) 极小性一步应直接用库内 API，
本文件不再重复实现（W18 发现的 ★C 卫生问题 ✓）。 -/
theorem sideNotMem_eq_cluster (u : Split X) (ρ : X) : sideNotMem u ρ = u.cluster ρ := rfl

/-- ★★★ **(F1) 的 `cluster` 形式**：若 `S.sideA ⊆ u.cluster ρ` 且 `u` 的两侧既不是 `S.sideA`
也不是 `S.sideB`，则 `u.cluster ρ ∩ S.sideB ≠ ∅` ✓ —— 与库内 `laminar_of_compatible_clusters`
配套使用（两者都以 `cluster` 为口径）；原 `sideNotMem` 形式的 (F1) **逐字保留** ✓（★C）。 -/
theorem sideA_subset_cluster_meets (S u : Split X) (ρ : X)
    (hA : u.sideA ≠ S.sideA) (hA' : u.sideA ≠ S.sideB) (h : S.sideA ⊆ u.cluster ρ) :
    (u.cluster ρ ∩ S.sideB).Nonempty := by
  rw [← sideNotMem_eq_cluster] at h ⊢
  exact sideA_subset_sideNotMem_meets S u hA hA' h

/-! ### 11.6 (★′) 极小性一步：登记（W19） -/

/-- ❌ **(★″) 极小 cluster 存在性 —— 已证伪（W20）**：本命题**为假** ✗（反例全文见 §11.7：
`α = Fin 5`、`F = { {0,1}|{2,3,4}, {2,3}|{0,1,4} }`（两两相容、**相离**）、`S = {0,2}|{1,3,4}`、`ρ = 4 ∈ S.sideB`；
两个 cluster `{0,1}`、`{2,3}` **都咬** `S.sideA = {0,2}` 却**相离** ⇒ **不存在**被所有咬 `S.sideA` 者包含的 `u₀` ✗）。
⇒ 保留此 `def` 仅为**历史登记**，**不得**用作任何证明步骤 ✗；极小性路线已作废，**(★′)** 需另走路线 ✓。
原登记内容（仅存档）：

`F` 两两相容、`S ∉ F ± swap`、`ρ ∈ S.sideB`，且 `F` 中有 `u` 使 `u.cluster ρ ∩ S.sideA ≠ ∅`
（即 `u*` 真的"咬到" `S.sideA`）时，**存在**这样的 `u₀`，其 `u₀.cluster ρ` 被**所有**这类 `u` 的
`u.cluster ρ` 包含（即 `M := {u ∈ F : u.cluster ρ ∩ S.sideA ≠ ∅}` 的**极小元** ✓）。

**证明路线（下一轮）**：`M` 有限非空 ⇒ 取基数最小者 ✓；层析性 `laminar_of_compatible_clusters`
（`Phylo/Split.lean:910`，⚠️ **真实全名待 `#check laminar_of_compatible_clusters` 确认** —— 无 `Split.` 前缀 ✓）
保证族内两成员"嵌套或相离"，而二者都与 `S.sideA` 相交 ⇒ 相离不可能 ⇒ 必嵌套 ⇒ 取包含关系极小者 ✓。

⇒ 配合**已入库**的 (F1)（`Split.sideA_subset_cluster_meets` ✓：`u*` 吞掉 `S.sideA` 时必咬到 `S.sideB`）
即可**一次**选定 `b, b'`（⚠️ **固定 `ρ`** 不换 ✓）⇒ `c_W = 0` 的四元组 ⇒ **(★′)** `noWRealizer_exists_gap` ✓
⇒ 已入库 `notIsDSplit_of_splitMetricSum_gap_proof` ⇒ **(B2)** ✓。

★ **W25-a 已形式化**（此前只有下面的散文反例）：§11.7.1 的
`minimalCluster_exists_gap_false : ¬ minimalCluster_exists_gap.{0}`（全称闭包为假）
＋ 实例形态 `mce_conclusion_false`（三条前提与见证全部成立，结论本身为假）✓。
本 `def` 原文**逐字未改**，此处仅加登记指针。 -/
def minimalCluster_exists_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (S : Split α) (ρ : α),
    (∀ s ∈ F, ∀ t ∈ F, s.Compatible t) →
      (∀ t ∈ F, t ≠ S ∧ t.swap ≠ S) → ρ ∈ S.sideB →
        (∃ u ∈ F, (u.cluster ρ ∩ S.sideA).Nonempty) →
          ∃ u₀ ∈ F, (u₀.cluster ρ ∩ S.sideA).Nonempty ∧
            ∀ u ∈ F, (u.cluster ρ ∩ S.sideA).Nonempty → u₀.cluster ρ ⊆ u.cluster ρ

/-! ### 11.7 ★D：**(★″)（`minimalCluster_exists_gap`）是假命题** ✗（W20 发现，勿再尝试证明）

**反例（`α = Fin 5`，`ρ = 4`）**：
* `F = { u₁ = {0,1} | {2,3,4},  u₂ = {2,3} | {0,1,4} }`（两条 split **两两相容** ✓：它们相离 ✓）；
* `S = {0,2} | {1,3,4}`（`S ∉ F ± swap` ✓，且 `ρ = 4 ∈ S.sideB` ✓）；
* `u₁.cluster 4 = {0,1}` ✓、`u₂.cluster 4 = {2,3}` ✓（两者都避开 `ρ = 4` ✓）；
* 两者都"咬" `S.sideA = {0,2}`：`{0,1} ∩ {0,2} = {0} ≠ ∅` ✓、`{2,3} ∩ {0,2} = {2} ≠ ∅` ✓；
* 但 **`{0,1}` 与 `{2,3}` 相离** ⇒ 谁也不包含谁 ⇒ **(★″) 的结论（存在被所有咬 `S.sideA` 者包含的 `u₀`）不成立** ✗。

⇒ **W19 我把「相离與两者都咬 `S.sideA` 矛盾」当成了事实 —— 那是错的** ✗
（相离的两个 cluster 完全可以各自咬到 `S.sideA` 的**不同点** ✓）。
⇒ **本文件里的 `def minimalCluster_exists_gap` 是假命题** ✗（仅为历史登记，**不得**用作证明步骤 ✓）；
⇒ **极小性路线需要重做**：（★′）的证明不能再依赖"取唯一极小 cluster" ✗。
**建议的替代路线（W21）**：不做极小元，直接**构造**四元组 —— 例如取
`a, a' ∈ S.sideA` 为**被不同 `u` 咬到**的两点、并用库内 `laminar_of_compatible_clusters`
保证的"嵌套或相离"做二分：若存在同时咬 `S.sideA` 的**嵌套对**则取内层，否则（全相离）直接取
`a = a'` 于某一 `u.cluster ρ`、`b, b' ∈ S.sideB` 用 (F1) `sideA_subset_cluster_meets` 的补集形式 ✓ ——
⚠️ 此路线**尚未验证**，落地前必须先按 ★D 用见证校验 ✗。

★ **W25-a 已把本节散文反例形式化**：见 §11.7.1 的 `minimalCluster_exists_gap_false`
（`¬ minimalCluster_exists_gap.{0}`）与实例形态 `mce_conclusion_false` ✓ —— 零假设、零 `sorry`。 -/

/-! ### 11.7.1 ★D：`minimalCluster_exists_gap` 的**形式化反例**（W25-a 落地）

§11.7 的论证此前**只有散文**（故台账把该缺口记「真开放」而非「已证伪」）。本节把它做成定理
`minimalCluster_exists_gap_false : ¬ minimalCluster_exists_gap.{0}`（**全称闭包为假**），
`def` 原文**逐字未改**。

装置（`α = Fin 5`、`ρ = 4`）：
* `mceU1 = {0,1} | {2,3,4}`、`mceU2 = {2,3} | {0,1,4}` —— 两条 split **相离**（故两两相容 ✓）；
* `mceS = {0,2} | {1,3,4}` —— 与 `mceU1`/`mceU2` **及其对换**都不同，且 `ρ = 4 ∈ mceS.sideB` ✓；
* `mceU1.cluster 4 = {0,1}`、`mceU2.cluster 4 = {2,3}`（都避开 `ρ`），
  两者都咬 `mceS.sideA = {0,2}`（分别咬到 `0` 与 `2`）却**互不包含** ⇒ 结论中的 `u₀` 不存在 ✗。

⇒ 命题为假；极小性路线（(★″) ⇒ (★′)）**不能再依赖"取唯一极小 cluster"** ✗。 -/

/-- 反例的第一个 split：`{0,1} | {2,3,4}`（`α = Fin 5`）。 -/
def mceU1 : Split (Fin 5) := ofSideA {0, 1} (by decide) (by decide)

/-- 反例的第二个 split：`{2,3} | {0,1,4}`（与 `mceU1` **相离**）。 -/
def mceU2 : Split (Fin 5) := ofSideA {2, 3} (by decide) (by decide)

/-- 反例的目标 split：`{0,2} | {1,3,4}`（`ρ = 4 ∈ sideB`）。 -/
def mceS : Split (Fin 5) := ofSideA {0, 2} (by decide) (by decide)

/-- `mceS.sideA = {0,2}`。 -/
theorem mceS_sideA : mceS.sideA = ({0, 2} : Finset (Fin 5)) := by
  simp only [mceS, ofSideA_sideA]

/-- `ρ = 4 ∈ mceS.sideB`。 -/
theorem mceS_mem_sideB : (4 : Fin 5) ∈ mceS.sideB := by
  simp only [mceS, ofSideA_sideB, Finset.mem_compl]
  decide

/-- `mceU1.cluster 4 = {0,1}`（`4 ∉ mceU1.sideA`）。 -/
theorem mceU1_cluster : mceU1.cluster (4 : Fin 5) = ({0, 1} : Finset (Fin 5)) := by
  unfold Split.cluster
  split_ifs with h4
  · exact absurd h4 (by simp only [mceU1, ofSideA_sideA]; decide)
  · simp only [mceU1, ofSideA_sideA]

/-- `mceU2.cluster 4 = {2,3}`（`4 ∉ mceU2.sideA`）。 -/
theorem mceU2_cluster : mceU2.cluster (4 : Fin 5) = ({2, 3} : Finset (Fin 5)) := by
  unfold Split.cluster
  split_ifs with h4
  · exact absurd h4 (by simp only [mceU2, ofSideA_sideA]; decide)
  · simp only [mceU2, ofSideA_sideA]

/-- 反例族 `F = {mceU1, mceU2}` **两两相容**（两者相离，自相容由 `disjoint_sides` 给出）。 -/
theorem mce_compatible : ∀ s ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))),
    ∀ t ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))), s.Compatible t := by
  intro s hs t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact Or.inr (Or.inl (disjoint_sides mceU1))
  · refine Or.inl ?_
    simp only [mceU1, mceU2, ofSideA_sideA]
    decide
  · refine Or.inl ?_
    simp only [mceU1, mceU2, ofSideA_sideA]
    decide
  · exact Or.inr (Or.inl (disjoint_sides mceU2))

/-- `mceS` **既不是** `mceU1`/`mceU2`，**也不是**它们的对换（`(★″)` 的第二条假设）。 -/
theorem mce_ne : ∀ t ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))), t ≠ mceS ∧ t.swap ≠ mceS := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · refine ⟨fun heq => ?_, fun heq => ?_⟩
    · have h' := congrArg (fun s : Split (Fin 5) => s.sideA) heq
      simp only [mceU1, mceS, ofSideA_sideA] at h'
      have h1 : (1 : Fin 5) ∈ ({0, 1} : Finset (Fin 5)) := by decide
      rw [h'] at h1
      exact absurd h1 (by decide)
    · have h' := congrArg (fun s : Split (Fin 5) => s.sideA) heq
      simp only [mceU1, mceS, swap_sideA, ofSideA_sideB, ofSideA_sideA] at h'
      have h4 : (4 : Fin 5) ∈ ({0, 1}ᶜ : Finset (Fin 5)) := by decide
      rw [h'] at h4
      exact absurd h4 (by decide)
  · refine ⟨fun heq => ?_, fun heq => ?_⟩
    · have h' := congrArg (fun s : Split (Fin 5) => s.sideA) heq
      simp only [mceU2, mceS, ofSideA_sideA] at h'
      have h3 : (3 : Fin 5) ∈ ({2, 3} : Finset (Fin 5)) := by decide
      rw [h'] at h3
      exact absurd h3 (by decide)
    · have h' := congrArg (fun s : Split (Fin 5) => s.sideA) heq
      simp only [mceU2, mceS, swap_sideA, ofSideA_sideB, ofSideA_sideA] at h'
      have h4 : (4 : Fin 5) ∈ ({2, 3}ᶜ : Finset (Fin 5)) := by decide
      rw [h'] at h4
      exact absurd h4 (by decide)

/-- 假设里的存在项：`mceU1 ∈ F` 且 `mceU1.cluster 4` **咬到** `mceS.sideA`。 -/
theorem mce_witness : ∃ u ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))),
    (u.cluster (4 : Fin 5) ∩ mceS.sideA).Nonempty := by
  refine ⟨mceU1, by simp, ?_⟩
  rw [mceU1_cluster, mceS_sideA]
  exact ⟨0, Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩

/-- ★D **核心矛盾**：`mceU1.cluster 4 = {0,1}` 与 `mceU2.cluster 4 = {2,3}` **互不包含**。 -/
theorem not_subset_mce_clusters :
    ¬ (mceU1.cluster (4 : Fin 5) ⊆ mceU2.cluster (4 : Fin 5)) ∧
      ¬ (mceU2.cluster (4 : Fin 5) ⊆ mceU1.cluster (4 : Fin 5)) := by
  constructor
  · intro hsub
    rw [mceU1_cluster, mceU2_cluster] at hsub
    have h0 : (0 : Fin 5) ∈ ({0, 1} : Finset (Fin 5)) := by decide
    exact absurd (hsub h0) (by decide)
  · intro hsub
    rw [mceU1_cluster, mceU2_cluster] at hsub
    have h2 : (2 : Fin 5) ∈ ({2, 3} : Finset (Fin 5)) := by decide
    exact absurd (hsub h2) (by decide)

/-- **某实例形态**：`mceU2`（或 `mceU1`）的 cluster 都咬 `mceS.sideA`。 -/
theorem mce_meet (u : Split (Fin 5)) (hu : u ∈ ({mceU1, mceU2} : Finset (Split (Fin 5)))) :
    (u.cluster (4 : Fin 5) ∩ mceS.sideA).Nonempty := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact ⟨0, by
      rw [mceU1_cluster, mceS_sideA]
      exact Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩
  · exact ⟨2, by
      rw [mceU2_cluster, mceS_sideA]
      exact Finset.mem_inter.mpr ⟨by decide, by decide⟩⟩

/-- ★D **实例形态（谓词为假）**：在 `F = {mceU1, mceU2}`、`S = mceS`、`ρ = 4` 处，
`(★″)` 的**结论本身**为假 —— 而三条前提（`mce_compatible`、`mce_ne`、`mceS_mem_sideB`）
与见证 `mce_witness` **全部成立** ✓ ⇒ 反例不是「前提不可满足」的空真 ✗。 -/
theorem mce_conclusion_false :
    ¬ ∃ u₀ ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))),
        (u₀.cluster (4 : Fin 5) ∩ mceS.sideA).Nonempty ∧
          ∀ u ∈ ({mceU1, mceU2} : Finset (Split (Fin 5))),
            (u.cluster (4 : Fin 5) ∩ mceS.sideA).Nonempty →
              u₀.cluster (4 : Fin 5) ⊆ u.cluster (4 : Fin 5) := by
  rintro ⟨u₀, hu₀, -, hmin⟩
  have hsub1 := not_subset_mce_clusters.1
  have hsub2 := not_subset_mce_clusters.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu₀
  rcases hu₀ with rfl | rfl
  · exact hsub1 (hmin mceU2 (by simp) (mce_meet mceU2 (by simp)))
  · exact hsub2 (hmin mceU1 (by simp) (mce_meet mceU1 (by simp)))

/-- ★D **`minimalCluster_exists_gap` 是假命题**（**全称闭包为假**：`α = Fin 5`、
`F = {mceU1, mceU2}`、`S = mceS`、`ρ = 4` 处结论不成立）。

`def` 原文**逐字未改**；§11.7 的散文反例首次形式化（W25-a），
矛盾落在实例形态的 `mce_conclusion_false` 上。 -/
theorem minimalCluster_exists_gap_false : ¬ minimalCluster_exists_gap.{0} :=
  fun h => mce_conclusion_false
    (h ({mceU1, mceU2}) mceS 4 mce_compatible mce_ne mceS_mem_sideB mce_witness)

/-! ### 11.8 (iii)：`c_W = 0` 的**充分条件**（逐 `u`、不依赖极小性/统一性 ✓） -/

/-- ★★★ **(iii) 充分条件（已证）**：若 `a ∈ S.sideA`、`b ∈ S.sideB`，且**每个** `v ∈ F`
都**不把 `a` 与 `b` 分开**，则对**任意** `a' ∈ S.sideA`、`b' ∈ S.sideB` 该四元组的 `c_W = 0` ✓。

理由（**逐 `u`、无统一性** ✓）：`u` 实现 `W` 要求 `{a,a'}` 在一侧、`{b,b'}` 在另一侧
⇒ `a` 与 `b` **必异侧** ⇒ 与假设矛盾 ✓。
⚠️ **W22 发现**：我原先把 `a',b'` 的同侧条件也写进了假设，但**证明只用到了 `a,b` 那一半** ⇒
`a',b'` 的条件是**多余的** ✓（陈述因此**更强** ✓）—— 与 W15 的 `hρ` 同理：**未使用的假设说明陈述可以更强** ✓。 -/
theorem sum_bPairW_eq_zero_of_never_separated (F : Finset (Split X)) (w : Split X → ℝ)
    (a a' b b' : X)
    (h : ∀ v ∈ F, ¬ ((a ∈ v.sideA ∧ b ∈ v.sideB) ∨ (a ∈ v.sideB ∧ b ∈ v.sideA))) :
    (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u) = 0 := by
  have hne : ¬ (F.filter (fun u => bPairW u a a' b b' = true)).Nonempty := by
    rintro ⟨v, hv⟩
    obtain ⟨hvF, hbw⟩ := Finset.mem_filter.mp hv
    have hPW : PairW v a a' b b' := (bPairW_eq_true_iff v a a' b b').mp hbw
    rcases hPW with ⟨ha, ha', hb, hb'⟩ | ⟨ha, ha', hb, hb'⟩
    · exact h v hvF (Or.inl ⟨ha, hb⟩)
    · exact h v hvF (Or.inr ⟨ha, hb⟩)
  rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]

/-- ★★★ **(iii) 与归约合体（已证）**：`a ∈ S.sideA`、`b ∈ S.sideB` 从不被 `F` 分开 ⇒
`S` **不是** `δ̂ = Σ w·δ_u` 的 `d`-split ✓（`not_isDSplit_of_no_W_realizer` 的即用形态 ✓）。 -/
theorem not_isDSplit_of_never_separated (F : Finset (Split X)) (w : Split X → ℝ)
    (hw : ∀ s ∈ F, 0 < w s) (S : Split X) {a a' b b' : X}
    (ha : a ∈ S.sideA) (ha' : a' ∈ S.sideA) (hb : b ∈ S.sideB) (hb' : b' ∈ S.sideB)
    (h : ∀ v ∈ F, ¬ ((a ∈ v.sideA ∧ b ∈ v.sideB) ∨ (a ∈ v.sideB ∧ b ∈ v.sideA))) :
    ¬ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) S.sideA S.sideB :=
  not_isDSplit_of_no_W_realizer F w hw S ha ha' hb hb'
    (sum_bPairW_eq_zero_of_never_separated F w a a' b b' h)

/-! ### 11.9 ★D：W22 提的"分情形 ②（内部切开）"路线**自相矛盾** ✗（W23 校验结论，勿再尝试）

设 `a ~ b :⟺ ∀v ∈ F, v 不把 a 与 b 分开`（同侧关系 ✓）。它是**等价关系** ✓（若干划分的核之交 ✓），
其类即"分量" ✓。分情形 ② 的原话是：
> "否则（每个分量都只与 `S` 的一侧相交）⇒ 取 `a,a'` 在被某个 `v` **内部切开**的 `S.sideA`-分量里、`b,b'` 同理
>  ⇒ 该 `v` 横跨该对 ⇒ 该 `v` 不实现 `W` ✓"

**校验结果：不成立 ✗**，两条独立理由：

1. **"被内部切开的分量"不存在** ✗（**自相矛盾**）：分量是按「**∀v ∈ F** 同侧」定义的 ✓ ⇒
   分量内任两点**不被任何 `v ∈ F` 分开** ✓ ⇒ "某个 `v` **内部切开**该分量"**与分量的定义直接冲突** ✗✗。
   （⇒ ② 想要的"横跨该对"的 `v` **根本不存在** ✓。）
2. **跨分量的 `v` 恰好实现 `W`**（不是横跨 ✗）：若 `a ≁ b`，则**存在** `v ∈ F` 把 `a` 与 `b` 异侧 ✓；
   于是对**任意** `a' ~ a`、`b' ~ b`（即同在各自分量内 ✓）都有 `{a,a'} ⊆ v` 的一侧、`{b,b'} ⊆ v` 的另一侧
   ⇒ **该 `v` 实现 `W`** ✗ ⇒ 这类四元组的 `c_W ≥ w_v > 0` ✗（<(iii)> 的假设也**不成立** ✗）。
   ⇒ ② 的"内部切开"机制把**方向搞反**了 ✓。

**⇒ 结论**：分情形 ② **作废** ✗，**(★′) 不能靠"取同分量内的两点对"来证** ✗。
**(iii)（已入库 ✓）只覆盖 `a ~ b` 的情形** ✓（此时 (iii) 直接给 `c_W = 0` ✓）。
**剩下真正要处理的情形**是 `a ≁ b`（⇒ 存在 `v` 把两侧的**分量**分开 ✓），
此时必须取 `a'` **不**在 `a` 的分量里（或 `b'` 不在 `b` 的分量里）⇒ 让某个 `v` **横跨** `{a,a'}`（或 `{b,b'}`）✓ ——
⚠️ 但**仍需逐 `v`** 检查**所有** `v' ∈ F`（勿重犯 W20「逐 `u` 当全 `F`」✗），
且此方向**尚未校验** ✗ —— 建议 W24 先按 ★D 用见证校验（例如 `F = { {0,1,2}|{3} }`、`S = {0,1}|{2,3}`，
看"取 `a'` 跨分量"能否真的给出 `c_W = 0` 的四元组 ✓/✗）再开证 ✓。 -/

/-! ## 12. ★★★★ W22 任务 A：瓶颈 (B1) **收口**

`Split.fourPointOfSplitMetricSum_gap` 的结论在 W22 改本体后变成**标准**四点条件
⇒ 它与 W12k 早已收口的 `fourPointOfSplitMetricSum_gap_correct_shape` **成为同一条陈述**
⇒ 直接复用其证明即可。★ 真正为假的是**旧形态**的那条（`…_gap_legacy`，见 §7）。 -/

/-- ★★★★ **瓶颈 (B1) 收口**（W22）：`fourPointOfSplitMetricSum_gap` 已成定理。

★ **留证**（HANDOVER【命题改动表】）：**旧形态**（结论用错形态）**为假** ——
形式化反驳 = `not_fourPointOfSplitMetricSum_legacy`；**新形态**（结论用标准形态）**为真** ——
本定理（复用 W12k 的 `fourPointOfSplitMetricSum_gap_correct_shape_proof`，两者改本体后**同陈述**）。
**文献依据** = `Buneman1974` Thm 1（`:33-36`）＋ Thm 2（`:70-74`）；**理由** = ★D 判真假（旧形态把真实
树度量排除在外，见 `def FourPoint` 的 docstring）。 -/
theorem fourPointOfSplitMetricSum_gap_proof : fourPointOfSplitMetricSum_gap :=
  fourPointOfSplitMetricSum_gap_correct_shape_proof

/-! ## 12.1 ★★★ W22 任务 B-③：`fourPointCharacterization_gap` 的 `⟸` 半边**无条件**收口

★ **关键发现**：本库 `def FourPoint` 只写三条 `max` 不等式，**没有**把「对称」写进定义
（文献的 `d` 恒对称 —— BdD 的 setting）。因此本文件此前的
`pairwiseCompatible_of_exists_symm_fourPoint_isDSplit` 只能证明
「**对称** ＋ 四点 ⇒ 两两相容」，`symmetric` 是**额外假设** ✗ —— 而
`fourPointCharacterization_gap` 的右边**只写 `FourPointStd δ`**，
拿不到 `hsym` ✗ ⇒ 该 `⟸` 半边此前只能算「有条件版」✗。

★ 但**对称性其实是被三条不等式强制出来的**（见 `Split.fourPoint_symm`，本批新增）：
两次实例化 `(a,a',b,b') = (x,y,x,x)` 与 `(y,x,y,y)` 的**第一合取项**，
`max` 的两个槽是**同一表达式**（退化）⇒ 直接得 `δ x y ≤ δ y x` 与反向 ⇒ 相等 ✓。
⇒ 「`δ` 对称」**不是**第四要素，`def FourPoint` 的形态**无需再改** ✓。 -/

/-- ★★★ **`fourPointCharacterization_gap` 的 `⟸` 半边（无条件版，W22 B-③）**：

「存在 `δ`：`FourPointStd δ`（= `FourPoint δ`）且其 d-split 集**恰为** `F`（商掉 `swap`）」
⟹ `F` **两两相容**。

★ 与 W12k 的 `pairwiseCompatible_of_exists_symm_fourPoint_isDSplit` 的区别：
**去掉了 `symm` 额外假设**（由 `Split.fourPoint_symm` 从 `FourPoint` 本身得到）⇒
本定理的前提**逐字**就是 `Split.fourPointCharacterization_gap` 的右半句 ✓。

★ 诚实说明：这只是**半边**。另一半（`⟹`：两两相容 ⟹ 存在这样的 `δ`）仍**未证**，
其剩余件 = (B1) ✅（W22 收口，`fourPointOfSplitMetricSum_gap_proof`）
＋「成员是 d-split」（未证）＋「非成员不是 d-split」= (B2)，而 (B2) 已被 §11.2 归约到
纯组合命题 (★′) `noWRealizer_exists_gap`，后者 W12p–W12r 未证成。 -/
theorem fourPointCharacterization_gap_reverse {F : Finset (Split X)}
    (h : ∃ δ : X → X → ℝ, FourPoint δ ∧
      ∀ s : Split X, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s) :
    ∀ s ∈ F, ∀ t ∈ F, s.Compatible t := by
  obtain ⟨δ, hfp, hδ⟩ := h
  exact pairwiseCompatible_of_exists_symm_fourPoint_isDSplit
    ⟨δ, fun x y => fourPoint_symm hfp x y, hfp, hδ⟩

/-! ## 12.2 ★★★ W22 任务 B-③：`⟹` 半边的**第三件** —— 「成员是 `d`-split」

★ **上一轮记的错路线已排除**：想由「每个 `SplitMetric` 逐项满足四条点不等式」推出
`Σ w_u·M_u ≤ max(Σ w_u·X_u, Σ w_u·Y_u)` 是**错的**（反例 `X₁=1,Y₁=0,X₂=0,Y₂=1,w≡1`：
`Σ M = 2 > max(ΣX,ΣY) = 1`）⇒ 必须走库内 `bPair*` **计数**路线（§10.2/§10.4）。

★ **本轮读通的 `bPair*` 语义**（此前按字面猜过一次，猜错）：
| 判据 | 含义 |
|---|---|
| `PairW u a a' b b'` | `u` **分离 `{a,a'} | {b,b'}`**（两对内部同侧、`a` 与 `b` 异侧） |
| `PairP u a a' b b'` | `u` 分离 `{a,b} | {a',b'}` |
| `PairX u a a' b b'` | `u` 分离 `{a,b'} | {a',b}` |

（★ 注意 `PairW` 对应的是 `{a,a'}|{b,b'}`，**不是** `{a,b'}|{a',b}` —— 这就是上一轮算例对不上的原因。） -/

/-- ★★★ **「成员是 `d`-split」（W22 B-③ `⟹` 半的第三件）**：`F` 两两相容、`w` 在 `F` 上正、
`t ∈ F` 时，`t` 的两侧是 `δ := Σ_{u∈F} w_u·δ_u` 的 `d`-split（`IsDSplit`，`max` 形式）。

**证明**（★★ 纯**计数**，不做逐项 `max` 求和）：取 `a,a' ∈ t.sideA`、`b,b' ∈ t.sideB`，记
`X := δaa' + δbb'`、`P := δab + δa'b'`、`W := δab' + δa'b`。§10.2 的两条差分恒等式给出
`W − X = 2c_W − 2c_X` 与 `W − P = 2c_P − 2c_X`（`c_• := Σ_{u∈F.filter bPair•} w_u`）。
由取法，`t` 满足 `bPairW`（两对都在 `t` 内部同侧、`a` 与 `b` 异侧）⇒ `c_W > 0`；
由两两相容的**互斥性**（`not_PairW_and_PairX` / `not_PairW_and_PairP`）⇒ `c_X = c_P = 0`
⇒ `W = P` 且 `W − X = 2c_W > 0` ⇒ `X < P ≤ max P W` ✓ **严格**。 -/
theorem isDSplit_splitMetricSum_of_mem {F : Finset (Split X)} {w : Split X → ℝ}
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t) (hw : ∀ s ∈ F, 0 < w s)
    {t : Split X} (ht : t ∈ F) :
    IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB := by
  intro a ha a' ha' b hb b' hb'
  have hba : b ∉ t.sideA := (mem_sideB_iff t b).mp hb
  have hb'a : b' ∉ t.sideA := (mem_sideB_iff t b').mp hb'
  have hPairW : bPairW t a a' b b' = true := by
    simp [bPairW, bSep, ha, ha', hba, hb'a]
  have hexX : F.filter (fun u => bPairX u a a' b b' = true) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨v, hv⟩
    obtain ⟨hvF, hvX⟩ := Finset.mem_filter.mp hv
    exact not_PairW_and_PairX hF
      ⟨⟨t, ht, (bPairW_eq_true_iff t a a' b b').mp hPairW⟩,
        ⟨v, hvF, (bPairX_eq_true_iff v a a' b b').mp hvX⟩⟩
  have hexP : F.filter (fun u => bPairP u a a' b b' = true) = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨v, hv⟩
    obtain ⟨hvF, hvP⟩ := Finset.mem_filter.mp hv
    exact not_PairW_and_PairP hF
      ⟨⟨t, ht, (bPairW_eq_true_iff t a a' b b').mp hPairW⟩,
        ⟨v, hvF, (bPairP_eq_true_iff v a a' b b').mp hvP⟩⟩
  have hcW : 0 < ∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u := by
    have hle : ∀ u ∈ F.filter (fun u => bPairW u a a' b b' = true), 0 ≤ w u :=
      fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
    have h1 : w t ≤ ∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u :=
      Finset.single_le_sum hle (Finset.mem_filter.mpr ⟨ht, hPairW⟩)
    linarith [hw t ht]
  set Xv : ℝ := (∑ u ∈ F, w u * SplitMetric u a a') + (∑ u ∈ F, w u * SplitMetric u b b')
    with hXv
  set Pv : ℝ := (∑ u ∈ F, w u * SplitMetric u a b) + (∑ u ∈ F, w u * SplitMetric u a' b')
    with hPv
  set Wv : ℝ := (∑ u ∈ F, w u * SplitMetric u a b') + (∑ u ∈ F, w u * SplitMetric u a' b)
    with hWv
  have hXW := splitMetricSum_diff_W F w a a' b b'
  have hXP := splitMetricSum_diff_P F w a a' b b'
  rw [hexX] at hXW hXP
  rw [hexP] at hXP
  simp only [Finset.sum_empty, mul_zero, sub_zero] at hXW hXP
  have hWgt : Xv < Wv := by linarith
  have hPeq : Wv = Pv := by linarith
  calc Xv < Wv := hWgt
    _ = Pv := hPeq
    _ ≤ max Pv Wv := le_max_left _ _

/-! ## 12.3 ★★★★ `fourPointCharacterization_gap` 的**条件收口**（(B2) 以外的件已全部到手） -/

/-- ★★★★ **`fourPointCharacterization_gap` 的收口形态（条件版，W22 B-③）**：
由 (★′) `noWRealizer_exists_gap` **即得**注册形态 `fourPointCharacterization_gap`
（原 `def` **逐字保留** ✓，真值状态由本定理 + (★′) 共同决定）。

* **`⟸` 半**：**无条件**已证 —— `fourPointCharacterization_gap_reverse`（`c71d5fd`）；
* **`⟹` 半**：三件**已全备** ——
  **(B1)** `fourPointOfSplitMetricSum_gap`（W22 收口：结论是四点条件）；
  **成员件** `isDSplit_splitMetricSum_of_mem`（`dc4cd8d`：`t ∈ F` ⇒ `t` 两侧是 d-split）；
  **(B2)** `notIsDSplit_of_splitMetricSum_gap_proof`（由 (★′)：非成员**不是** d-split）。
  取 `w ≡ 1`、`δ := Σ_{u∈F} δ_u`；`swap` 那一支由 `isDSplit_comm`（对称性由
  `splitMetricSum_comm` 提供）＋ `Split.swap_sideA/swap_sideB` 搬过来。

★★ **命名说明（重要）**：本定理**故意不叫** `…_gap_proof` / `…_gap_holds` ——
它带一个**未证**假设 (★′)。若叫 `_proof`，`scripts/list_gaps.sh` **口径 B** 会把它
误记为 `[已收口]`；这正是 `notIsDSplit_of_splitMetricSum_gap` **现在被误记**的原因
（其收口定理 `notIsDSplit_of_splitMetricSum_gap_proof` 带 `(h : noWRealizer_exists_gap)`）。
⇒ 登记为【口径 B 已知漏洞】待修（`HANDOVER.md` 的 W22 块有记）。 -/
theorem fourPointCharacterization_gap_of_noWRealizer (h : noWRealizer_exists_gap.{0}) :
    fourPointCharacterization_gap.{0} := by
  intro α _ _ F
  constructor
  · intro hF
    refine ⟨fun x y => ∑ u ∈ F, (1 : ℝ) * SplitMetric u x y, ?_, ?_⟩
    · exact fourPointOfSplitMetricSum_gap_proof F (fun _ => 1) hF (fun _ _ => one_pos)
    · intro s
      constructor
      · intro hs
        by_contra hne
        have hall : ∀ t ∈ F, t ≠ s ∧ t.swap ≠ s := by
          intro t ht
          exact ⟨fun h1 => hne ⟨t, ht, Or.inl h1⟩, fun h2 => hne ⟨t, ht, Or.inr h2⟩⟩
        exact (notIsDSplit_of_splitMetricSum_gap_proof h F (fun _ => 1) hF
          (fun _ _ => one_pos) s hall) hs
      · rintro ⟨t, ht, hts | hts⟩
        · rw [← hts]
          exact isDSplit_splitMetricSum_of_mem hF (fun _ _ => one_pos) ht
        · rw [← hts, Split.swap_sideA, Split.swap_sideB]
          exact (isDSplit_comm (fun x y => splitMetricSum_comm F (fun _ => 1) x y)).mpr
            (isDSplit_splitMetricSum_of_mem hF (fun _ _ => one_pos) ht)
  · rintro ⟨δ, hfp, hδ⟩
    exact fourPointCharacterization_gap_reverse ⟨δ, hfp, hδ⟩


/-! ### 11.10 ★★★★ W23：**(★′) `noWRealizer_exists_gap` 收口**

★ **命题**（逐字即 `def noWRealizer_exists_gap`）：`F` 两两相容、`w` 在 `F` 上正、
`S ∉ F ± swap` ⇒ 存在 `a,a' ∈ S.sideA`、`b,b' ∈ S.sideB`，使 **没有** `u ∈ F` 在
`(a,a',b,b')` 上实现 `W`（即 `c_W = 0`）。

★★ **证明路线（W23 新路线，与已作废的「极小 cluster」路线无关）**：

固定 `ρ ∈ S.sideB`，对 `u ∈ F` 记 `u* := sideNotMem u ρ`（`u` 的**不含 `ρ`** 那一侧
= `u.cluster ρ`）。两条关键事实：

1. **`W`-配对的读法**（`pairW_sideNotMem`）：若 `u` 在 `(a,a',ρ,b)` 上实现 `W`，
   则 `a,a'` 同在 `u*` 内、`b` 在 `u*` 外 ✓。
   ⇒ **只要 `b' := ρ`（即 `b = b' = ρ`）**，实现 `W` 就**等价于** `{a,a'} ⊆ u*` ✓
   （第二个析取项要求 `ρ ∈ u` 的**另一侧**，而 `ρ ∉ u*` 恒成立 ✓）。
2. **镶嵌性**（`laminar_sideNotMem`，由库内 `laminar_of_compatible_clusters` 立得）：
   `{u* : u ∈ F}` 两两「包含或相离」✓。
   ⇒ 含**给定点**的 cluster 构成**链** ⇒ **最小元存在** ✓（不需要 (★″) 那条已被证伪的
   「被所有咬 `S.sideA` 者包含的极小元」命题 ✗）。

**分情形（对 `ρ` 固定、`b := ρ` 固定）**：

* **情形 ①**：存在 `a,a' ∈ S.sideA`，**没有** `u ∈ F` 使 `a,a'` 同在 `u*` 内。
  取 `b := b' := ρ`：由 (1)，任何实现 `W` 的 `u` 都会给出 `{a,a'} ⊆ u*` ⇒ 没有 ⇒ `c_W = 0` ✓。
* **情形 ②**：每个 `a,a' ∈ S.sideA` 都有公共的 `u*`。取
  `cardMin p :=` 含 `a₀` 与 `p` 的 cluster 的**最小基数**（`p` 取遍 `S.sideA`，`a₀ ∈ S.sideA` 固定），
  在 `S.sideA` 上取**达到最大** `cardMin` 的 `p₁`，`u₁` 为实现 `cardMin p₁` 的 cluster。则
  1. `S.sideA ⊆ u₁*`（否则 `a` 的最小 cluster `w` 与 `u₁*` 镶嵌 ⇒ 要么 `a ∈ u₁*` ✗，要么
     `|w| > |u₁*|` 与 `cardMin` 最大性矛盾 ✗）；
  2. `u₁* ∩ S.sideB ≠ ∅`（否则 `u₁* ⊆ S.sideA` 且 `≠ S.sideA`（否则 `u₁ = S` 或 `S.swap` ✗）
     ⇒ 取 `a₃ ∈ S.sideA \ u₁*`，其最小 cluster `w` 与 `u₁*` 镶嵌 ⇒ 同样两种矛盾 ✗）；
  3. 取 `b₁ ∈ u₁* ∩ S.sideB`。对**任何**含 `a₀` 与 `p₁` 的 `u ∈ F`：`u*` 与 `u₁*` 镶嵌
     ⇒ `u₁* ⊆ u*`（反向用基数推相等）⇒ `b₁ ∈ u*` ✓。
     ⇒ 由 (1)，任何实现 `W` 的 `u`（它必含 `a₀,p₁`）都使 `b₁ ∈ u*`，与 `b₁` 在 `u*` 外矛盾 ✓
     ⇒ `c_W = 0` ✓。

⇒ 两种情形都给出 `∃ a ∈ S.sideA, ∃ a' ∈ S.sideA, ∃ b ∈ S.sideB, ∃ b' ∈ S.sideB, c_W = 0` ✓。 -/

/-- **(11.10-a) `W`-配对在 `ρ`-侧上的读法**：若 `u` 在 `(a,a',ρ,b)` 上实现 `W`，
则 `a, a'` 同在 `u` 的**不含 `ρ`** 的那一侧 `u* = sideNotMem u ρ` 内，而 `b` 在 `u*` 之外 ✓。 -/
theorem pairW_sideNotMem {u : Split X} {ρ a a' b : X} (hW : PairW u a a' ρ b) :
    a ∈ sideNotMem u ρ ∧ a' ∈ sideNotMem u ρ ∧ b ∉ sideNotMem u ρ := by
  have hAB : ∀ x : X, x ∈ u.sideB → x ∉ u.sideA := fun x h => (mem_sideB_iff u x).mp h
  have hBA : ∀ x : X, x ∈ u.sideA → x ∉ u.sideB := fun x h hb => (mem_sideB_iff u x).mp hb h
  by_cases hρ : ρ ∈ u.sideA
  · have hK : sideNotMem u ρ = u.sideB := by simp only [sideNotMem, hρ, ite_true]
    rcases hW with ⟨ha, ha', hρB, hb⟩ | ⟨ha, ha', hρA, hb⟩
    · exact absurd hρ (hAB ρ hρB)
    · exact ⟨by rw [hK]; exact ha, by rw [hK]; exact ha', by rw [hK]; exact hBA b hb⟩
  · have hK : sideNotMem u ρ = u.sideA := by simp only [sideNotMem, hρ, ite_false]
    rcases hW with ⟨ha, ha', hρB, hb⟩ | ⟨ha, ha', hρA, hb⟩
    · exact ⟨by rw [hK]; exact ha, by rw [hK]; exact ha', by rw [hK]; exact hAB b hb⟩
    · exact absurd hρA hρ

/-- **(11.10-b) 相容族里「不含 `ρ` 的那一侧」两两镶嵌** ✓（`laminar_of_compatible_clusters` 的直接实例）。 -/
theorem laminar_sideNotMem {F : Finset (Split X)} {ρ : X}
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t)
    {u v : Split X} (hu : u ∈ F) (hv : v ∈ F) :
    sideNotMem u ρ ⊆ sideNotMem v ρ ∨ sideNotMem v ρ ⊆ sideNotMem u ρ ∨
      Disjoint (sideNotMem u ρ) (sideNotMem v ρ) :=
  laminar_of_compatible_clusters (s := u) (t := v) (ρ := ρ) (hF u hu v hv)
    (sideNotMem_eq_cluster u ρ) (sideNotMem_eq_cluster v ρ)

/-- **(11.10-c) `cluster` 判据下的 `c_W = 0` 充分条件**（情形 ① 与情形 ② 共用的收尾）：
若对每个 `u ∈ F`，`a, a'` 同在 `u*` 内就迫使 `b₁ ∈ u*`，则四元组 `(a,a',ρ,b₁)` 的 `c_W = 0` ✓。 -/
theorem sum_bPairW_eq_zero_of_cluster {F : Finset (Split X)} {w : Split X → ℝ}
    {ρ b₁ a a' : X}
    (h : ∀ u ∈ F, a ∈ sideNotMem u ρ → a' ∈ sideNotMem u ρ → b₁ ∈ sideNotMem u ρ) :
    (∑ u ∈ F.filter (fun u => bPairW u a a' ρ b₁ = true), w u) = 0 := by
  have hne : ¬ (F.filter (fun u => bPairW u a a' ρ b₁ = true)).Nonempty := by
    rintro ⟨v, hv⟩
    obtain ⟨hvF, hbw⟩ := Finset.mem_filter.mp hv
    obtain ⟨h1, h2, h3⟩ := pairW_sideNotMem ((bPairW_eq_true_iff v a a' ρ b₁).mp hbw)
    exact h3 (h v hvF h1 h2)
  rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]

/-- **(11.10-d)**：若 `u` 的 `ρ`-侧恰是 `S.sideA`，则 `u` 就是 `S` 或 `S.swap` ✓。 -/
theorem eq_or_swap_eq_of_sideNotMem_eq_sideA {u S : Split X} {ρ : X}
    (h : sideNotMem u ρ = S.sideA) : u = S ∨ u.swap = S := by
  have key : ∀ v : Split X, v.sideA = S.sideA → v = S := by
    intro v hv
    refine (KPartition.eq_iff_parts v S).mpr ?_
    funext i
    fin_cases i
    · show v.sideA = S.sideA
      exact hv
    · show v.sideB = S.sideB
      rw [v.sideB_eq_compl, S.sideB_eq_compl, hv]
  by_cases hρ : ρ ∈ u.sideA
  · have hK : sideNotMem u ρ = u.sideB := by simp only [sideNotMem, hρ, ite_true]
    right
    refine key u.swap ?_
    rw [swap_sideA]
    rw [hK] at h
    exact h
  · have hK : sideNotMem u ρ = u.sideA := by simp only [sideNotMem, hρ, ite_false]
    left
    rw [hK] at h
    exact key u h

/-- ★★★★ **(11.10-e) (★′) 的核心**：`noWRealizer_exists_gap` 的证明主体。 -/
theorem noWRealizer_core (F : Finset (Split X)) (w : Split X → ℝ) (S : Split X)
    (hF : ∀ s ∈ F, ∀ t ∈ F, s.Compatible t)
    (hS : ∀ t ∈ F, t ≠ S ∧ t.swap ≠ S) :
    ∃ a ∈ S.sideA, ∃ a' ∈ S.sideA, ∃ b ∈ S.sideB, ∃ b' ∈ S.sideB,
      (∑ u ∈ F.filter (fun u => bPairW u a a' b b' = true), w u) = 0 := by
  classical
  obtain ⟨ρ, hρ⟩ := S.nonempty 1
  obtain ⟨a₀, ha₀⟩ := S.nonempty 0
  by_cases hcase1 : ∃ a ∈ S.sideA, ∃ a' ∈ S.sideA,
      ∀ u ∈ F, ¬ (a ∈ sideNotMem u ρ ∧ a' ∈ sideNotMem u ρ)
  · obtain ⟨a, ha, a', ha', hno⟩ := hcase1
    exact ⟨a, ha, a', ha', ρ, hρ, ρ, hρ,
      sum_bPairW_eq_zero_of_cluster (fun u hu h1 h2 => absurd ⟨h1, h2⟩ (hno u hu))⟩
  · have hshare : ∀ a ∈ S.sideA, ∀ a' ∈ S.sideA,
        ∃ u ∈ F, a ∈ sideNotMem u ρ ∧ a' ∈ sideNotMem u ρ := by
      intro a ha a' ha'
      by_contra hcon
      exact hcase1 ⟨a, ha, a', ha', fun u hu h => hcon ⟨u, hu, h⟩⟩
    set T : Finset (Split X) := F.filter (fun u => a₀ ∈ sideNotMem u ρ) with hT
    have hTF : ∀ u ∈ T, u ∈ F := fun u hu => (Finset.mem_filter.mp hu).1
    have hTa₀ : ∀ u ∈ T, a₀ ∈ sideNotMem u ρ := fun u hu => (Finset.mem_filter.mp hu).2
    have hTne : ∀ p : {x // x ∈ S.sideA}, (T.filter (fun u => p.1 ∈ sideNotMem u ρ)).Nonempty := by
      intro p
      obtain ⟨u, huF, hu1, hu2⟩ := hshare a₀ ha₀ p.1 p.2
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨huF, hu1⟩, hu2⟩⟩
    let cardMin : {x // x ∈ S.sideA} → ℕ := fun p =>
      ((T.filter (fun u => p.1 ∈ sideNotMem u ρ)).image (fun u => (sideNotMem u ρ).card)).min'
        ((hTne p).image (fun u => (sideNotMem u ρ).card))
    -- 取含 a₀ 与 a 的最小 cluster（存在性；`cardMin` 的取值者）
    have hmin_wit : ∀ (a : X) (ha : a ∈ S.sideA), ∃ u ∈ T, a ∈ sideNotMem u ρ ∧
        (sideNotMem u ρ).card = cardMin ⟨a, ha⟩ := by
      intro a ha
      have hmem := Finset.min'_mem
        ((T.filter (fun u => a ∈ sideNotMem u ρ)).image (fun u => (sideNotMem u ρ).card))
        ((hTne ⟨a, ha⟩).image (fun u => (sideNotMem u ρ).card))
      obtain ⟨u, humem, hucard⟩ := Finset.mem_image.mp hmem
      exact ⟨u, (Finset.mem_filter.mp humem).1, (Finset.mem_filter.mp humem).2, hucard⟩
    obtain ⟨p₁, -, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset {x // x ∈ S.sideA}) cardMin
      ⟨⟨a₀, ha₀⟩, Finset.mem_univ _⟩
    obtain ⟨u₁, hu₁T, hu₁p₁, hu₁card⟩ := hmin_wit p₁.1 p₁.2
    have hu₁F : u₁ ∈ F := hTF u₁ hu₁T
    -- (1) `S.sideA ⊆ u₁*`
    have hAsub : S.sideA ⊆ sideNotMem u₁ ρ := by
      intro a ha
      by_contra hna
      obtain ⟨w, hwT, hwa, hwcard⟩ := hmin_wit a ha
      have hle : (sideNotMem w ρ).card ≤ (sideNotMem u₁ ρ).card := by
        rw [hu₁card, hwcard]
        exact hmax ⟨a, ha⟩ (Finset.mem_univ _)
      have hl := laminar_sideNotMem (F := F) (ρ := ρ) hF (hTF w hwT) hu₁F
      have ha₀u : a₀ ∈ sideNotMem u₁ ρ := hTa₀ u₁ hu₁T
      have ha₀w : a₀ ∈ sideNotMem w ρ := hTa₀ w hwT
      rcases hl with h1 | h1 | h1
      · exact hna (h1 hwa)
      · have heq : sideNotMem u₁ ρ = sideNotMem w ρ :=
          Finset.eq_of_subset_of_card_le h1 hle
        exact hna (heq.symm ▸ hwa)
      · exact absurd ha₀w (Finset.disjoint_right.mp h1 ha₀u)
    -- (2) `u₁* ∩ S.sideB ≠ ∅`
    have hB : (sideNotMem u₁ ρ ∩ S.sideB).Nonempty := by
      by_contra hemp
      have hemp' : sideNotMem u₁ ρ ∩ S.sideB = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
      have hKsub : sideNotMem u₁ ρ ⊆ S.sideA := by
        intro x hx
        have hxu : x ∈ S.sideA ∪ S.sideB := by rw [S.union_sides]; exact Finset.mem_univ x
        rcases Finset.mem_union.mp hxu with h | h
        · exact h
        · exact absurd (Finset.mem_inter.mpr ⟨hx, h⟩) (by rw [hemp']; exact Finset.notMem_empty x)
      have hKne : sideNotMem u₁ ρ ≠ S.sideA := by
        intro hEq
        rcases eq_or_swap_eq_of_sideNotMem_eq_sideA hEq with h1 | h1
        · exact (hS u₁ hu₁F).1 h1
        · exact (hS u₁ hu₁F).2 h1
      have hex : ∃ x ∈ S.sideA, x ∉ sideNotMem u₁ ρ := by
        by_contra hcon
        refine hKne (Finset.Subset.antisymm hKsub ?_)
        intro x hx
        by_contra hxK
        exact hcon ⟨x, hx, hxK⟩
      obtain ⟨a₃, ha₃A, ha₃K⟩ := hex
      obtain ⟨w, hwT, hwa, hwcard⟩ := hmin_wit a₃ ha₃A
      have hle : (sideNotMem w ρ).card ≤ (sideNotMem u₁ ρ).card := by
        rw [hu₁card, hwcard]
        exact hmax ⟨a₃, ha₃A⟩ (Finset.mem_univ _)
      have hl := laminar_sideNotMem (F := F) (ρ := ρ) hF (hTF w hwT) hu₁F
      have ha₀u : a₀ ∈ sideNotMem u₁ ρ := hTa₀ u₁ hu₁T
      have ha₀w : a₀ ∈ sideNotMem w ρ := hTa₀ w hwT
      rcases hl with h1 | h1 | h1
      · exact ha₃K (h1 hwa)
      · have hlt : (sideNotMem u₁ ρ).card < (sideNotMem w ρ).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h1, fun heq => ha₃K (heq.symm ▸ hwa)⟩)
        omega
      · exact absurd ha₀w (Finset.disjoint_right.mp h1 ha₀u)
    obtain ⟨b₁, hb₁⟩ := hB
    obtain ⟨hb₁K, hb₁B⟩ := Finset.mem_inter.mp hb₁
    -- (3) 收尾：任何含 `a₀` 与 `p₁` 的 `u` 都含 `b₁`
    refine ⟨a₀, ha₀, p₁.1, p₁.2, ρ, hρ, b₁, hb₁B, sum_bPairW_eq_zero_of_cluster ?_⟩
    intro u huF hua₀ hua₁
    have huT : u ∈ T := Finset.mem_filter.mpr ⟨huF, hua₀⟩
    have hle : (sideNotMem u₁ ρ).card ≤ (sideNotMem u ρ).card := by
      rw [hu₁card]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr
        ⟨u, Finset.mem_filter.mpr ⟨huT, hua₁⟩, rfl⟩)
    have hl := laminar_sideNotMem (F := F) (ρ := ρ) hF hu₁F huF
    rcases hl with h1 | h1 | h1
    · exact h1 hb₁K
    · have heq : sideNotMem u ρ = sideNotMem u₁ ρ :=
        Finset.eq_of_subset_of_card_le h1 hle
      exact heq.symm ▸ hb₁K
    · have hmem : a₀ ∈ sideNotMem u₁ ρ ∩ sideNotMem u ρ :=
        Finset.mem_inter.mpr ⟨hTa₀ u₁ hu₁T, hTa₀ u huT⟩
      rw [Finset.disjoint_iff_inter_eq_empty.mp h1] at hmem
      exact absurd hmem (Finset.notMem_empty a₀)

/-- ★★★★ **(★′) `noWRealizer_exists_gap` —— 已证（W23）** ✓

这是 W22 记下的 **B-③ 唯一剩余件**（W12p / W12q / W12r 三轮未证成）。
`#print axioms` 与全库其它定理同一基础（无新增公理）。 -/
theorem noWRealizer_exists_gap_proof : noWRealizer_exists_gap.{0} := by
  intro α _ _ F w hF _hw S hS
  exact noWRealizer_core F w S hF hS

/-- ★★★★ **(B2) 的无条件收口**：`notIsDSplit_of_splitMetricSum_gap` 现为**定理** ✓

（此前只有带 `(h : noWRealizer_exists_gap)` 的条件版 `…_gap_proof`；现在 (★′) 已证，
⇒ 条件收口升为**无条件收口** ⇒ `list_gaps.sh` 口径 B 的「条件收口」漏洞在**这一条**上消除 ✓。） -/
theorem notIsDSplit_of_splitMetricSum_gap_holds : notIsDSplit_of_splitMetricSum_gap.{0} :=
  notIsDSplit_of_splitMetricSum_gap_proof noWRealizer_exists_gap_proof

/-- ★★★★★ **`fourPointCharacterization_gap` —— 已收口（W23）** ✓✓

`⟸` 半：`fourPointCharacterization_gap_reverse`（W22，**无条件**，靠 `fourPoint_symm`）；
`⟹` 半：`fourPointCharacterization_gap_of_noWRealizer` ＋ 本轮的 **(★′)** 证明。
⇒ 两半皆无条件 ⇒ 注册形态 `def fourPointCharacterization_gap` 现为**定理**（`def` 逐字未动 ✓）。 -/
theorem fourPointCharacterization_gap_proof : fourPointCharacterization_gap.{0} :=
  fourPointCharacterization_gap_of_noWRealizer noWRealizer_exists_gap_proof

/-! ## 4.2 ★★★★ W27-b：`weakCompatibilityRealization_gap` 的**忠实形态**（`α_S = w S`）

### 0. 为什么登记在**本文件**而不在 `Phylo/SplitWeak.lean`

忠实形态的结论必须写出**隔离指数**，而隔离指数的落地件 `Split.isolationIndex` 在本文件 §8.3
（`:942`）；本文件 **import** `Phylo.SplitWeak`（`:6`）⇒ 反向写会**循环依赖** ✗。
故 `Phylo/SplitWeak.lean` 的 §7.4 只登记**非成员核心**（`weakCompatibilityNonMemberCore`）与
**归约**（`weakCompatibilityRealization_gap_of_core`），忠实形态登记在此处 ✓。
★ 本节的 `α` 与 `w` 的桥**不需要**新器材：`0 < isolationIndex ⟺ IsDSplit` 已在 §8.3 证成
（`isolationIndex_pos_iff_isDSplit`，`:971`）。

### 1. 形态（四要素）

* **旧形态（派单建议）** ✗：忠实形态的结论追加 `bunemanIndex δ s.sideA s.sideB = w s`。**三重不可行**：
  1. **不合型**：`bunemanIndex (δ : NJ.Dissimilarity X) (s : Split X)` 只吃 `Split`、不吃两侧
     （`Phylo/BunemanTree.lean:107`）⇒ 字面写法**不存在**；
  2. **类型不对**：`bunemanIndex` 是 **Buneman 1971 的 `μ_σ`**（两项 `min` 形 ＝ `IsDSplitStrong`），
     **不是** BdD 的三项 `max` 形 `α` —— 正是 §4.1 **已证伪** `…_correct_shape`（`:249`，反例 `:351`）的病根；
  3. **会重演同一反例**：`μ ≤ α` 且可取严格小值，而结论 (1) 的成员方向要求 `α_S > 0` ＝`IsDSplit`
     ⇒ 在同一 `δ` 上「`μ_S = w_S`」与「`α_S > 0`」可同时不可满足。
* **新形态** ✓：用 §8.3 的 `Split.isolationIndex`（三项 `max` 形 `α`，`0 < α ⟺ IsDSplit`）；
* **文献行号**：`references/md/BandeltDress1992_CanonicalDecompositionMetrics.md:438-440`
  （d-split ⟺ `α > 0`）· `:446-454`（`α` 定义）· `:1683-1699`（Thm 3：`Σ` ＝ d-split 全体 **且**
  `α_S = λ_S`）· `:456-460`（`#X = 4` 时 `d = Σ α_{A,B} δ_{A,B}` —— **定标**系数）；
* **理由（真假判据）**：W25-a 的假命题是「`IsDSplit ⟺ μ > 0`」；W25-b ★D 已改成「`IsDSplit ⟺ α > 0`」
  ⇒ 忠实形态**必须**建在 `α` 上。

### 2. 系数的 `2` 与 `w s + (if s.swap ∈ F then w s.swap else 0)`

* **`2` 的来源（归一化差）**：本库 `isolationIndex` 取 `min pairDeficit`（**无 `½`**，§8.3），
  而 `pairDeficit δ_S = 2`（`a,a' ∈ A`、`b,b' ∈ B` 时 `P = X = 2`、`I = 0`）⇒ 本库口径下
  `isolationIndex = 2·α_BD`；由 `:456-460` 的定标（`d = δ_S` 必须给 `α_S = 1`）知 BdD 的
  `α_S = λ_S` 在本库口径下正是 `isolationIndex = 2λ`。★ 若把 `δ_S` 归一为 `½·indicator`，
  则 `2` 消失 —— 本库 `SplitMetric` 是 `0/1`，故 `2` 在。
  ★ 对**成员** `s`，每个四元组都有 `pairDeficit ≥ 2·w_s > 0`（计数判据
  `splitMetricSum_isDSplit_iff` ＋ 弱相容 ⇒ `min c_P c_X = 0`，`c_W ≥ w_s`）
  ⇒ §8.3 的「`max` 里含 `I`」与「截断到 `0`」两种写法在**成员**上一致 ⇒ 上式两侧同源 ✓
  （截断只可能影响**非成员**，而结论 (2) 不声称非成员）。
* **为何不是 `α_s = w s`**：`Split` 的两侧**有序**、而 `δ_s = δ_{s.swap}` ⇒ 同一 split 以 `s` 与
  `s.swap` **两个**成员出现时**合并**计数。取 `F = {s, s.swap}`、`w s ≠ w s.swap` 即知
  「`α_s = w s`」**为假** ⇒ 必须写和式（这是 `w` 一侧**唯一**需要修的细节，「弱化」一侧不动）。
* ★ 结论 (2) **只**声称成员（及成员的 `swap`）；**不**声称非成员 `α = 0` ——
  那正是 §4.1 被证伪的那一条（`BunemanIndexBridge.lean:245`），且还需 `α ≥ 0`。

### 3. 未证状态

本 `def` 是**未证**形态（⬖）：BD Thm 3 的系数半边需要「`α` 对弱相容族逐成员恰等于权重」的
层析论证，不在 W27-b 时间盒内。本节**只**交「**忠实 ⟹ 弱化**」方向
（`weakCompatibilityRealization_gap_of_weights`，**无条件、零 `sorry`**）。 -/

/-- ★★★★ **忠实形态**（W27-b 新立；BdD Theorem 3 的**两条**断言一起，一般 `α` 的 `_holds` 形态）。

`F` 弱相容、`w > 0` 于 `F` ⇒ 取 `δ := Σ_{u∈F} w_u δ_u`，则
① `IsDSplit δ s.sideA s.sideB ⟺ ∃ t ∈ F, t = s ∨ t.swap = s`（**弱化形态**的全部内容）；
② `α_s(δ) = 2·(w s + (if s.swap ∈ F then w s.swap else 0))` 对每个成员 `s`
（**忠实形态**追加的那半；`2` 是本库 `isolationIndex` 与 BdD `α` 的归一化差，见 §4.2 第 2 条）。

★ 与 `Split.weakCompatibilityRealization_gap`（`Phylo/SplitWeak.lean:562`）的**唯一**差别就是新增的 ②：
`w` 从「只出现在假设里」变成「**进出结论**」⇒ **收口前者的 `_holds` ≠ 形式化 BdD Thm 3**。 -/
def weakCompatibilityRealization_gap_weights : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    WeaklyCompatible (↑F : Set (Split α)) → (∀ s ∈ F, 0 < w s) →
      ∃ δ : α → α → ℝ, (∀ x y, δ x y = δ y x) ∧
        (∀ s : Split α, IsDSplit δ s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s) ∧
          ∀ s : Split α, (s ∈ F ∨ s.swap ∈ F) →
            isolationIndex δ s.sideA s.sideB
              = 2 * (w s + (if s.swap ∈ F then w s.swap else 0))

/-- ★★★★ **忠实 ⟹ 弱化**（W27-b 要求的第二件，**无条件、零 `sorry`**）：结论多一条 `α_S = w S`
的形态蕴含原 `def`（`Phylo/SplitWeak.lean:562`）—— 丢掉第三个合取项即可。

★ 该方向**只是投影**，故它本身**不**声称忠实形态成立（忠实形态本批仍为 ⬖）。 -/
theorem weakCompatibilityRealization_gap_of_weights :
    weakCompatibilityRealization_gap_weights.{0} → Split.weakCompatibilityRealization_gap.{0} := by
  intro h α instF instD F w hF hw
  obtain ⟨δ, hsymm, hiff, _⟩ := h F w hF hw
  exact ⟨δ, hsymm, hiff⟩


/-! ## 8.10 ★★★★ W28 泳道 e：`_v2` 的**收口归约** —— 存在性 ① 只剩 (P1) 一条具名假设

### 本节做了什么

`§8.7` 给了基例（残差取 `δ` 本身、`F = ∅`）、`§8.8` 给了归纳步（再加一条正系数 split 度量）、
`§8.6` 给了单步剥离的全部度量保形。本节把三者**接起来**，并给出 (P1) 的**相容半边**：

1. `splitPrimeFaithfulPartition_iff_forall_not_isDSplit`：`δ` 划分版 split-prime ⟺
   **没有**任何 `Split α` 是 `δ` 的 d-split（「剥离链终止态」与「§8.7 基例」之间的桥）；
2. `dSplits_eq_empty_iff_splitPrimeFaithfulPartition`：`dSplits δ = ∅` ⟺ `δ` 划分版 split-prime；
3. ★★★ `dSplits_peelMetric_card_lt_of_compatible`：**(P1) 的相容半边** —— 若剥离后活下来的
   d-split **都与 `s` 相容**，则 `dSplits` 的基数**严格下降**（终止测度成立）；
4. ★★★★ `canonicalSplitDecomposition_gap_faithful_v2_of_dSplits_card_decrease`：
   **对 `(dSplits δ).card` 作强归纳**，把 `_v2` 的**完整结论（零额外假设）**归约到**唯一**一条
   具名假设 (P1)：「剥离任一 d-split 后 `dSplits` 的基数严格下降」。

### 为什么 (P1) 就是全部（终止性 ＋ 装配都在本节内部完成）

* 归纳步：`s ∈ dSplits δ` ⇒ `c := α_s/2 > 0`（`peelCoeff_pos`）、`δ' := δ - c·δ_s` 仍是度量
  （`§8.6`）、`s ∉ dSplits δ'`（`peelMetric_not_isDSplit`）；由 (P1) 得
  `card(dSplits δ') < card(dSplits δ)` ⇒ 归纳假设给 `δ'` 的分解 ⇒ `§8.8` 的
  `…_conclusion_add_split` 把 `c·δ_s` 并回去（`δ' x y + c·δ_s x y = δ x y` 由 `ring`）；
* 基例：`dSplits δ = ∅` ⇒ `§8.7` 的 `…_conclusion_of_splitPrime`（残差取 `δ`、`F = ∅`）。

### (P1) 的现状（**未证**；两半各说清，★ 不冒充 `_holds`）

* **相容半边（已证，就在本节）**：`§8.9` 的 `isDSplit_of_isDSplit_peelMetric` ＋ 第 3 条 ——
  `dSplits δ' ⊆ dSplits δ` 且 `s ∈ dSplits δ \ dSplits δ'` ⇒ 真子集 ⇒ 基数严格下降；
* **不相容半边（仍缺，BdD Lemma 3–6）**：`t` 与 `s` 不相容时四元组相对 `s` 可呈
  `(2,0,2)`/`(0,2,2)` 模式，`pd(δ,q) = pd(δ',q) + c·pd_s(q)` 中 `pd_s(q) = -2`
  ⇒ `pd(δ',q) > 0` 只给出 `pd(δ,q) > -2c`，**推不出** `pd(δ,q) > 0`。
  直接用 `isolationIndex_le_cross_gap_of_mem_sideA/B` 夹逼会**循环**：取
  `a,b ∈ A_s`、`a',b' ∈ B_s`（此时 `s` 与 `t` 四交全非空，正是**不相容**），
  由 `α_s ≤ δ a a' + δ a b' − δ a' b'` 得 `δ a' b' − δ a a' ≤ δ a b' − α_s`，代入
  `pd(δ,q) = δ a b + δ a' b' − δ a a' − δ b b'` 只得到 `pd(δ,q) ≤ δ a b + δ a b' − α_s − δ b b'`，
  而三角不等式给的是**相反**方向的界 ⇒ 必须引入 BdD 的 convexity / `s(S)`-cluster 弱层级
  （Lemma 3 `md:5581`、Lemma 4 `:6094`、Lemma 5 `:6159`、Lemma 6 `:6504`）。 -/

/-- ★★★ **划分版 split-prime ⟺ 没有任何 `Split` 是 d-split**（「剥离链终止态」的形式化）。

`⇒`：`s.sideA | s.sideB` 本身就是 `X` 的划分（`disjoint_sides` ＋ `union_sides` ＋ 两侧非空）；
`⇐`：给定划分 `A | B`，取 `s := Split.ofSideA A …`，则 `s.sideA = A`、`s.sideB = Aᶜ = B`
（`Aᶜ = B` 由 `A ∪ B = univ` ＋ `A ⊥ B` 立得）。 -/
theorem splitPrimeFaithfulPartition_iff_forall_not_isDSplit
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ} :
    SplitPrimeFaithfulPartition δ ↔ ∀ s : Split α, ¬ IsDSplit δ s.sideA s.sideB := by
  constructor
  · intro hsp s hds
    exact hsp s.sideA s.sideB (s.nonempty 0) (s.nonempty 1) s.disjoint_sides s.union_sides hds
  · intro h A B hA hB hdisj hunion hds
    have hcB : Aᶜ = B := by
      ext x
      simp only [Finset.mem_compl]
      constructor
      · intro hx
        have hmem : x ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ x
        rcases Finset.mem_union.mp hmem with h' | h'
        · exact absurd h' hx
        · exact h'
      · intro hx hxA
        exact Finset.disjoint_left.mp hdisj hxA hx
    have hAc : Aᶜ.Nonempty := by rw [hcB]; exact hB
    have hneg := h (Split.ofSideA A hA hAc)
    rw [Split.ofSideA_sideA, Split.ofSideA_sideB, hcB] at hneg
    exact hneg hds

/-- ★★ **`dSplits δ = ∅` ⟺ `δ` 划分版 split-prime**（（P2）的**基例判据**：
剥离链终止 ⟺ 残差无 d-split ⟺ 残差 split-prime ⇒ `§8.7` 基例可用）。 -/
theorem dSplits_eq_empty_iff_splitPrimeFaithfulPartition
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ} :
    dSplits δ = ∅ ↔ SplitPrimeFaithfulPartition δ := by
  rw [splitPrimeFaithfulPartition_iff_forall_not_isDSplit]
  constructor
  · intro h s hds
    have hmem : s ∈ dSplits δ := mem_dSplits.mpr hds
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty s)
  · intro h
    ext s
    simp only [mem_dSplits, Finset.notMem_empty]
    exact ⟨fun hds => h s hds, fun hf => hf.elim⟩

/-- ★★★ **(P1) 的相容半边**：若剥离后活下来的 d-split **都与 `s` 相容**，则 `dSplits` 的基数**严格下降**。

证明：`dSplits δ' ⊆ dSplits δ`（逐点用 `§8.9` 的 `isDSplit_of_isDSplit_peelMetric`），
且 `s ∈ dSplits δ \ dSplits δ'`（`s` 是 `δ` 的 d-split 而**不再**是 `δ'` 的，`peelMetric_not_isDSplit`）
⇒ 真子集 ⇒ `card_lt_card`。

★ 本定理**把 (P1) 精确压到不相容情形**：剩下的唯一障碍是「存在 `t ∈ dSplits δ'` 与 `s` 不相容」。 -/
theorem dSplits_peelMetric_card_lt_of_compatible
    {α : Type*} [Fintype α] [DecidableEq α] {δ : α → α → ℝ} {s : Split α}
    (hds : IsDSplit δ s.sideA s.sideB)
    (hcompat : ∀ t : Split α, IsDSplit (peelMetric δ s) t.sideA t.sideB → s.Compatible t) :
    (dSplits (peelMetric δ s)).card < (dSplits δ).card := by
  have hc : 0 ≤ peelCoeff δ s := le_of_lt (peelCoeff_pos (s.nonempty 0) (s.nonempty 1) hds)
  have hsub : dSplits (peelMetric δ s) ⊆ dSplits δ := by
    intro t ht
    exact mem_dSplits.mpr
      (isDSplit_of_isDSplit_peelMetric hc (hcompat t (mem_dSplits.mp ht)) (mem_dSplits.mp ht))
  have hne : dSplits (peelMetric δ s) ≠ dSplits δ := by
    intro heq
    have hm : s ∈ dSplits (peelMetric δ s) := by
      rw [heq]
      exact mem_dSplits.mpr hds
    exact peelMetric_not_isDSplit (s.nonempty 0) (s.nonempty 1) (mem_dSplits.mp hm)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- ★★★★ **`_v2` 的收口归约（W28 核心）**：`canonicalSplitDecomposition_gap_faithful_v2`（`:1154`，
**def 未改一字**）的**完整结论**（零额外假设、含存在性 ①）由**唯一一条具名假设 (P1)** 推出：

`hdec`：(P1) —— 对任意度量 `δ` 与 `δ` 的任一 d-split `s`，剥离后 `dSplits` 的基数**严格下降**。

证明：对 `(dSplits δ).card` 作**强归纳**（`Nat.strong_induction_on`）。
* `dSplits δ = ∅`：`§8.7` 基例 `…_conclusion_of_splitPrime`；
* 否则取 `s ∈ dSplits δ`：`§8.6` 给 `0 < c := α_s/2`、`δ' := peelMetric δ s` 仍是度量、
  `s ∉ dSplits δ'`；(P1) 给基数严格下降 ⇒ 归纳假设给 `δ'` 的分解 ⇒ `§8.8` 的
  `…_conclusion_add_split` 并回 `c·δ_s`。

★ 本定理**不叫** `_holds`：前提 `hdec`（(P1) 的不相容半边，BdD Lemma 3–6）**未证**，
半成品不许用 `_holds` 命名（台账只认该后缀为「已证」）。
★ 一旦 (P1) 证成，`_holds` 只需 `canonicalSplitDecomposition_gap_faithful_v2_of_dSplits_card_decrease
  (fun δ hδ hdiag hnn htri s hds => …)` 一行装配。 -/
theorem canonicalSplitDecomposition_gap_faithful_v2_of_dSplits_card_decrease
    {α : Type*} [Fintype α] [DecidableEq α]
    (hdec : ∀ (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) → (∀ x, δ x x = 0) →
      (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) → ∀ s : Split α,
      IsDSplit δ s.sideA s.sideB → (dSplits (peelMetric δ s)).card < (dSplits δ).card) :
    ∀ (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) → (∀ x, δ x x = 0) →
      (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
      ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
        (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
          (∀ x y, 0 ≤ δ₀ x y) ∧
            ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y := by
  classical
  suffices H : ∀ n (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) → (∀ x, δ x x = 0) →
      (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) → (dSplits δ).card ≤ n →
      ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
        (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithfulPartition δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
          (∀ x y, 0 ≤ δ₀ x y) ∧
            ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y from
    fun δ hδ hdiag hnn htri => H (dSplits δ).card δ hδ hdiag hnn htri le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro δ hδ hdiag hnn htri hle
    by_cases hemp : dSplits δ = ∅
    · exact canonicalSplitDecomposition_gap_faithful_v2_conclusion_of_splitPrime
        (dSplits_eq_empty_iff_splitPrimeFaithfulPartition.mp hemp) hdiag hnn
    · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hdss : IsDSplit δ s.sideA s.sideB := mem_dSplits.mp hs
      have hcpos : 0 < peelCoeff δ s := peelCoeff_pos (s.nonempty 0) (s.nonempty 1) hdss
      have hcard : (dSplits (peelMetric δ s)).card < (dSplits δ).card :=
        hdec δ hδ hdiag hnn htri s hdss
      have hlt : (dSplits (peelMetric δ s)).card < n := lt_of_lt_of_le hcard hle
      obtain ⟨F, c, δ₀, hpos, hsp, hdiag', hnn', heq⟩ :=
        ih _ hlt (peelMetric δ s) (peelMetric_symm hδ s) (peelMetric_diag hdiag s)
          (peelMetric_nonneg hδ hdiag hnn (s.nonempty 0) (s.nonempty 1))
          (peelMetric_triangle hδ hdiag htri (s.nonempty 0) (s.nonempty 1)) le_rfl
      obtain ⟨F', c', δ₀', hpos', hsp', hdiag'', hnn'', heq'⟩ :=
        canonicalSplitDecomposition_gap_faithful_v2_conclusion_add_split
          (δ := peelMetric δ s) (s₀ := s) (c₀ := peelCoeff δ s) hcpos
          ⟨F, c, δ₀, hpos, hsp, hdiag', hnn', heq⟩
      refine ⟨F', c', δ₀', hpos', hsp', hdiag'', hnn'', ?_⟩
      intro x y
      rw [← heq' x y]
      unfold peelMetric
      ring


/-! ## 8.11 ★★★ W28 泳道 e：(P1) 的**逐点定量障碍** ＋ 残余缺口的具名登记

`§8.10` 把存在性 ① 压到唯一假设 (P1)「剥离后 `dSplits` 基数严格下降」，并证了它的**相容半边**。
本节把 (P1) 的**不相容半边**压到**一条逐点不等式**（这是本节的全部内容，不声称证成 (P1)）：

1. `pairDeficit_peelMetric_le_add`：`pd(δ,q) ≤ pd(δ',q) + 2c`（`c ≥ 0`）；
2. `pairDeficit_le_peelMetric_add`：`pd(δ',q) ≤ pd(δ,q) + 2c`（`c ≥ 0`）——
   合起来 `|pd(δ,q) − pd(δ',q)| ≤ 2c`：**剥离对任一四元组亏损的扰动 ≤ `α_s`**；
3. ★★★ `pairDeficit_peelMetric_of_mem_sideA_mem_sideB`：**`−2` 模式（唯一危险模式）的精确公式**
   （`a,b ∈ A_s`、`a',b' ∈ B_s`；此时四交全非空 ⇒ `s` 与 `t` **不相容**）：
   ```
   pd(δ', a a' b b') = max (δ a b + δ a' b' + 2c) (δ a b' + δ a' b) − (δ a a' + δ b b')
   ```
   ⇒ `pd(δ',q) > 0` 只给出 `δ a b + δ a' b' + 2c > δ a a' + δ b b'`（其余配对不受 `c` 影响）；
4. ★★★ `cross_mode_obstruction`：于是「`t ∉ dSplits δ` 而 `t ∈ dSplits δ'`」要成立，**必须**有
   ```
   0 ≤ (δ a a' + δ b b') − (δ a b + δ a' b') < 2c = α_s
   ```
   即**危险模式下的亏损落在 `[0, α_s)` 内**。★ 这就是 (P1) 剩下的**唯一**缺口，且它是**逐点**的；
5. `dSplitsPeelDecrease`：(P1) 的具名 `Prop`（零假设、零证明，供台账追踪）；
6. ★★★★ `canonicalSplitDecomposition_gap_faithful_v2_of_dSplitsPeelDecrease`：
   **一行装配** —— `dSplitsPeelDecrease → canonicalSplitDecomposition_gap_faithful_v2`。

### 为什么第 4 条仍是缺口（为什么它不能由现有器材推出）

设 `α_s ≤ pd_s(δ)` 的四元组取自**同样四点**（`a,b ∈ A_s`、`a',b' ∈ B_s`）：
`pd_s(δ) = max (δ a a' + δ b b', δ a b' + δ b a') − (δ a b + δ a' b') = max(Z, Y) − X`，
其中 `Z := δ a a' + δ b b'`、`Y := δ a b' + δ b a'`、`X := δ a b + δ a' b'`。
把 `δ = δ' + c·δ_s` 代入：`Z = Z' + 2c`、`Y = Y' + 2c`、`X = X'`，故
`α_s ≤ max(Z', Y') + 2c − X'` —— **不等式的右端含 `2c = α_s` 本身** ⇒ 只能得到恒真式 `X' ≤ max(Z',Y')`。
危险模式要求的是 `X' ≤ Z' < X' + 2c`，**恰好是这个循环的盲区**。
⇒ 要排除它必须换一组点（即 BdD 的 convexity / `s(S)`-cluster 弱层级：Lemma 3 `md:5581`、
Lemma 4 `:6094`、Lemma 5 `:6159`、Lemma 6 `:6504`），本库的 `Split.cluster ρ` 与
`laminar_of_compatible_clusters`（`Phylo/Aho.lean`、`Phylo/Split.lean`）是现成的起点，
但**弱**层级（非相容 ⇒ 非 `laminar`）需要新证。 -/

/-- ★★ **剥离对 `pairDeficit` 的扰动（上界）**：`pd(δ,q) ≤ pd(δ',q) + 2c`（`c ≥ 0`）。

`SplitMetric` 是 `0/1` 值 ⇒ 每个配对至多涨 `2c`、被减项只减不增。 -/
theorem pairDeficit_peelMetric_le_add {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} (hc : 0 ≤ peelCoeff δ s) (a a' b b' : α) :
    pairDeficit δ a a' b b' ≤ pairDeficit (peelMetric δ s) a a' b b' + 2 * peelCoeff δ s := by
  have hmax : max (δ a b + δ a' b') (δ a b' + δ a' b)
      ≤ max (peelMetric δ s a b + peelMetric δ s a' b')
          (peelMetric δ s a b' + peelMetric δ s a' b) + 2 * peelCoeff δ s := by
    have hX : δ a b + δ a' b'
        ≤ peelMetric δ s a b + peelMetric δ s a' b' + 2 * peelCoeff δ s := by
      have h1 : peelCoeff δ s * SplitMetric s a b ≤ peelCoeff δ s := by
        simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s a b) hc
      have h2 : peelCoeff δ s * SplitMetric s a' b' ≤ peelCoeff δ s := by
        simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s a' b') hc
      rw [peelMetric_apply, peelMetric_apply]
      linarith
    have hY : δ a b' + δ a' b
        ≤ peelMetric δ s a b' + peelMetric δ s a' b + 2 * peelCoeff δ s := by
      have h1 : peelCoeff δ s * SplitMetric s a b' ≤ peelCoeff δ s := by
        simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s a b') hc
      have h2 : peelCoeff δ s * SplitMetric s a' b ≤ peelCoeff δ s := by
        simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s a' b) hc
      rw [peelMetric_apply, peelMetric_apply]
      linarith
    have := max_le_max hX hY
    rwa [max_add_add_right] at this
  have hZ : peelMetric δ s a a' + peelMetric δ s b b' ≤ δ a a' + δ b b' := by
    have h1 : 0 ≤ peelCoeff δ s * SplitMetric s a a' :=
      mul_nonneg hc (splitMetric_nonneg s a a')
    have h2 : 0 ≤ peelCoeff δ s * SplitMetric s b b' :=
      mul_nonneg hc (splitMetric_nonneg s b b')
    rw [peelMetric_apply, peelMetric_apply]
    linarith
  unfold pairDeficit
  linarith

/-- ★★ **剥离对 `pairDeficit` 的扰动（下界）**：`pd(δ',q) ≤ pd(δ,q) + 2c`（`c ≥ 0`）。

与上一条合起来：`|pd(δ,q) − pd(δ',q)| ≤ 2c = α_s` —— **剥离只把亏损扰动 `α_s` 以内**。 -/
theorem pairDeficit_le_peelMetric_add {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} (hc : 0 ≤ peelCoeff δ s) (a a' b b' : α) :
    pairDeficit (peelMetric δ s) a a' b b' ≤ pairDeficit δ a a' b b' + 2 * peelCoeff δ s := by
  have hmax : max (peelMetric δ s a b + peelMetric δ s a' b')
      (peelMetric δ s a b' + peelMetric δ s a' b)
      ≤ max (δ a b + δ a' b') (δ a b' + δ a' b) := by
    have hX : peelMetric δ s a b + peelMetric δ s a' b' ≤ δ a b + δ a' b' := by
      have h1 : 0 ≤ peelCoeff δ s * SplitMetric s a b :=
        mul_nonneg hc (splitMetric_nonneg s a b)
      have h2 : 0 ≤ peelCoeff δ s * SplitMetric s a' b' :=
        mul_nonneg hc (splitMetric_nonneg s a' b')
      rw [peelMetric_apply, peelMetric_apply]
      linarith
    have hY : peelMetric δ s a b' + peelMetric δ s a' b ≤ δ a b' + δ a' b := by
      have h1 : 0 ≤ peelCoeff δ s * SplitMetric s a b' :=
        mul_nonneg hc (splitMetric_nonneg s a b')
      have h2 : 0 ≤ peelCoeff δ s * SplitMetric s a' b :=
        mul_nonneg hc (splitMetric_nonneg s a' b)
      rw [peelMetric_apply, peelMetric_apply]
      linarith
    exact max_le_max hX hY
  have hZ : (δ a a' + δ b b') - (peelMetric δ s a a' + peelMetric δ s b b')
      ≤ 2 * peelCoeff δ s := by
    have h1 : peelCoeff δ s * SplitMetric s a a' ≤ peelCoeff δ s := by
      simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s a a') hc
    have h2 : peelCoeff δ s * SplitMetric s b b' ≤ peelCoeff δ s := by
      simpa using mul_le_mul_of_nonneg_left (splitMetric_le_one s b b') hc
    rw [peelMetric_apply, peelMetric_apply]
    linarith
  unfold pairDeficit
  linarith

/-- ★★★ **`−2` 模式（唯一危险模式）的精确公式**：`a, b ∈ A_s`、`a', b' ∈ B_s` 时

```
pd(δ', a a' b b') = max (δ a b + δ a' b' + 2c) (δ a b' + δ a' b) − (δ a a' + δ b b')
```

（`c = peelCoeff δ s`。此时四交 `A_s∩A_t ⊇ {a,b}`、`B_s∩A_t ⊇ {a',b'}` 等因 `t` 的
`A = {a,a'}`、`B = {b,b'}` 而**全非空** ⇒ `s` 与 `t` **不相容**，正是 `§8.9` 的相容半边**覆盖不到**的构形。）

⇒ 与 `s` 自己的四元组 `pd_s(δ) = max(Z, Y) − X` 对照可见：`pd(δ',q) > 0` 只把 `X` 换成 `X + 2c`，
**其余不变** —— 这就是「`pd` 之差可正可负」的机器形态。 -/
theorem pairDeficit_peelMetric_of_mem_sideA_mem_sideB {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α}
    (ha : a ∈ s.sideA) (hb : b ∈ s.sideA) (ha' : a' ∈ s.sideB) (hb' : b' ∈ s.sideB) :
    pairDeficit (peelMetric δ s) a a' b b'
      = max (δ a b + δ a' b' + 2 * peelCoeff δ s) (δ a b' + δ a' b)
          - (δ a a' + δ b b') := by
  have hgen : ∀ A Y Z c : ℝ, max A (Y - 2 * c) - (Z - 2 * c) = max (A + 2 * c) Y - Z := by
    intro A Y Z c
    rcases le_total (Y - 2 * c) A with h | h
    · rw [max_eq_left h, max_eq_left (show Y ≤ A + 2 * c by linarith)]
      ring
    · rw [max_eq_right h, max_eq_right (show A + 2 * c ≤ Y by linarith)]
      ring
  have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA ha hb
  have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB ha' hb'
  have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha hb'
  have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha' hb
  have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha ha'
  have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB hb hb'
  have e1 : (δ a b' - peelCoeff δ s) + (δ a' b - peelCoeff δ s)
      = (δ a b' + δ a' b) - 2 * peelCoeff δ s := by ring
  have e2 : (δ a a' - peelCoeff δ s) + (δ b b' - peelCoeff δ s)
      = (δ a a' + δ b b') - 2 * peelCoeff δ s := by ring
  simp only [pairDeficit, peelMetric_apply, h1, h2, h3, h4, h5, h6, mul_one, mul_zero,
    sub_zero]
  rw [e1, e2, hgen]

/-- ★★★ **(P1) 残余缺口的逐点形态**（`−2` 模式的**唯一**危险构形）：若四元组 `q` 在 `δ` 处**非正**
（`max(X,Y) ≤ Z`）而在 `δ'` 处**严格正**，则必有

```
0 ≤ Z − X < 2c = α_s
```

其中 `X = δ a b + δ a' b'`、`Z = δ a a' + δ b b'`。
⇒ 「剥离产生新的 d-split」**只可能**发生在这个带宽里 —— 这是 (P1) 剩下的**全部**内容。 -/
theorem cross_mode_obstruction {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α}
    (ha : a ∈ s.sideA) (hb : b ∈ s.sideA) (ha' : a' ∈ s.sideB) (hb' : b' ∈ s.sideB)
    (hneg : max (δ a b + δ a' b') (δ a b' + δ a' b) ≤ δ a a' + δ b b')
    (hpos : 0 < pairDeficit (peelMetric δ s) a a' b b') :
    δ a b + δ a' b' ≤ δ a a' + δ b b' ∧
      δ a a' + δ b b' < δ a b + δ a' b' + 2 * peelCoeff δ s := by
  have hf := pairDeficit_peelMetric_of_mem_sideA_mem_sideB (δ := δ) ha hb ha' hb'
  rw [hf] at hpos
  have hX : δ a b + δ a' b' ≤ δ a a' + δ b b' := le_trans (le_max_left _ _) hneg
  have hY : δ a b' + δ a' b ≤ δ a a' + δ b b' := le_trans (le_max_right _ _) hneg
  refine ⟨hX, ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : δ a b + δ a' b' + 2 * peelCoeff δ s ≤ δ a a' + δ b b' := hcon
  have h2 : δ a b' + δ a' b ≤ δ a a' + δ b b' := hY
  have : max (δ a b + δ a' b' + 2 * peelCoeff δ s) (δ a b' + δ a' b)
      ≤ δ a a' + δ b b' := max_le h1 h2
  linarith

/-- ⬜ **(P1) 的具名登记**（零假设、零证明）：剥离 `δ` 的任一 d-split 后，`dSplits` 的基数**严格下降**。

★ 这是 `§8.10` 的收口归约唯一欠的假设 ⇒ **存在性 ① 的全部残余缺口就是本条**。
★★ **命名说明**：本 `Prop` **故意不带 `gap`** —— 它是 `_v2` 的**内部子义务**（(P1) 的测度载体性质），
**不是**新的独立文献缺口；台账口径 `A/B` 是机械的（`def` 名含 `gap` 就多登记一行），
故此处只作具名 `Prop`，不计入「还剩几条真开放」。
其**相容半边**见 `§8.10` 的 `dSplits_peelMetric_card_lt_of_compatible`；
**不相容半边**的逐点障碍见 `§8.11` 的 `cross_mode_obstruction`。

★★ **状态更新（W28 收口）**：本 `Prop` **已被证成** —— 见 `§8.13` 的 `dSplitsPeelDecrease_holds`
（不相容半边由 `§8.12` 的 `isDSplit_of_isDSplit_peelMetric_general` 给出，**不需要** BdD Lemma 3–6）。
下文「仍需 BdD Lemma 3–6」的判断是**历史记录**（已被上文的反证取代）。
★ 本 `Prop` **不叫** `_gap_holds`：它就是缺口本身（台账口径：`_gap` 为未证、`_holds` 为已证）。 -/
def dSplitsPeelDecrease : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    (∀ x, δ x x = 0) → (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
    ∀ s : Split α, IsDSplit δ s.sideA s.sideB →
      (dSplits (peelMetric δ s)).card < (dSplits δ).card

universe u

/-- ★★★★ **一行装配**：`(P1)` ⟹ `canonicalSplitDecomposition_gap_faithful_v2`（`:1154`，`def` **未改**）。

★ 本定理**不叫** `_holds`：前提 `dSplitsPeelDecrease` **未证**。
一旦 (P1) 证成（`h := …`），`canonicalSplitDecomposition_gap_faithful_v2_holds` 即本定理的直接实例。 -/
theorem canonicalSplitDecomposition_gap_faithful_v2_of_dSplitsPeelDecrease
    (h : dSplitsPeelDecrease.{u}) : canonicalSplitDecomposition_gap_faithful_v2.{u} := by
  intro α _ _ δ hδ hdiag hnn htri
  exact canonicalSplitDecomposition_gap_faithful_v2_of_dSplits_card_decrease
    (fun (δ : α → α → ℝ) hδ hdiag hnn htri s hds => h δ hδ hdiag hnn htri s hds)
    δ hδ hdiag hnn htri


/-! ## 8.12 ★★★★ W28 泳道 e：**(P1) 的不相容半边已证** —— 剥离下 d-split 的**无条件存活**

`§8.9` 只给了「`t` 与 `s` 相容 ⇒ `t` 在剥离下存活」；`§8.11` 把不相容半边压成逐点带宽
`0 ≤ Z − X < α_s`。本节把这条带宽证掉 ⇒ (P1)（`dSplitsPeelDecrease`）成立。

### 五模式（按三个**和**陈述）

记 `u₁ := δ_s(a,b)`、`u₂ := δ_s(a',b')`、`v₁ := δ_s(a,b')`、`v₂ := δ_s(a',b)`、
`w₁ := δ_s(a,a')`、`w₂ := δ_s(b,b')`（各 `∈ {0,1}`），`x := u₁+u₂`、`y := v₁+v₂`、`z := w₁+w₂`，
`c := peelCoeff δ s`、`δ' := peelMetric δ s`、`A := δ a b + δ a' b'`、`B := δ a b' + δ a' b`、`Z := δ a a' + δ b b'`。
由 `δ = δ' + c·δ_s`：

```
pd(δ',q) = max(A − c·x, B − c·y) − (Z − c·z)
```

★ **奇偶性**：`δ_s(u,v) ≡ ε(u)+ε(v) (mod 2)`（`ε = 1` 表示在 `s.sideB`）⇒ `x ≡ y ≡ z (mod 2)`
⇒ `pd_s = max(x,y) − z ∈ {0, ±2}`（**没有 `±1`**）。四种模式（本节四条 `…_of_sums_…`）：

| 四点相对 `s` | `(x,y,z)` | `pd(δ')` |
|---|---|---|
| `x = y = z`（同侧／3–1） | `(0,0,0)`／`(1,1,1)` | `pd(δ)` |
| `A×A×B×B`（= `§8.6` 已证） | `(2,2,0)` | `pd(δ) − 2c` |
| 交叉 ①（`{a,b}`／`{a',b'}` 分居两侧） | `(0,2,2)` | `max (A+2c) B − Z` |
| 交叉 ②（`{a,b'}`／`{a',b}` 分居两侧） | `(2,0,2)` | `max A (B+2c) − Z` |

### 危险模式的反证（`cross_core` / `cross_core2`，纯实数）

交叉 ①：若 `pd(δ) ≤ 0` 则 `A ≤ Z` 且 `B ≤ Z`；而 **`s` 在同样四点上的四元组**
（`a,b ∈ A_s`、`a',b' ∈ B_s`）给出
`α_s ≤ pd_s(δ) = max(Z,B) − A = Z − A`，又 `pd(δ') > 0` 给 `Z < A + 2c`
⇒ `2c = α_s ≤ Z − A < 2c`，矛盾。交叉 ② 同理（取 `(a,b')`／`(a',b)` 作 `s`-四元组）。

★ **两条定义级出处**（不留猜测）：
1. 「`α_s` 是下确界 ⇒ 对**每个**四元组都有 `α_s ≤ pd(δ)`」—— 库内
   `isolationIndex_le_pairDeficit`（`§8.3`，`isolationIndex` 用 `Finset.inf'` 定义）；
2. 「`2c = α_s`」—— `peelCoeff` 的定义（`unfold peelCoeff; ring`），即 `c = α_s/2`。

★ **更正记录**：`§8.11` 头部曾判「危险模式只能循环」，**那是代数失误**（先把 `Z`、`B` 用
`Z'+2c`、`B'+2c` 代进去再比）。正解是取 `δ` 侧的界 `α_s ≤ Z − A`：它**不含 `c`**，正好把带宽卡死。

### 数值证据（**非**证明，仅供交叉核对）

随机整数 5 点度量 4459 个，对每个度量的**每个** d-split 逐个剥离，检验 `S(δ') ⊆ S(δ)`：
**零反例** ⇒ 测度载体 `(dSplits δ).card` 站得住、下面结论不是假命题。
（脚本口径：`α_s` 取 `min` 遍历含退化四元组，`c = α_s/2`，与库内 `isolationIndex`/`peelCoeff` 同口径。
★ 这是**数值证据**，不是证明；机器证明见本节各条定理。） -/

/-- ★★ **五模式的统一恒等式**（纯代数）：`pd(δ)` 由 `pd(δ')` 与三个和决定。 -/
theorem pairDeficit_peel_general {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (s : Split α) (a a' b b' : α) :
    pairDeficit δ a a' b b'
      = max (peelMetric δ s a b + peelMetric δ s a' b'
              + peelCoeff δ s * (SplitMetric s a b + SplitMetric s a' b'
                - (SplitMetric s a a' + SplitMetric s b b')))
            (peelMetric δ s a b' + peelMetric δ s a' b
              + peelCoeff δ s * (SplitMetric s a b' + SplitMetric s a' b
                - (SplitMetric s a a' + SplitMetric s b b')))
          - (peelMetric δ s a a' + peelMetric δ s b b') := by
  have e1 : peelMetric δ s a b + peelMetric δ s a' b'
      + peelCoeff δ s * (SplitMetric s a b + SplitMetric s a' b'
        - (SplitMetric s a a' + SplitMetric s b b'))
      = (δ a b + δ a' b') - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]; ring
  have e2 : peelMetric δ s a b' + peelMetric δ s a' b
      + peelCoeff δ s * (SplitMetric s a b' + SplitMetric s a' b
        - (SplitMetric s a a' + SplitMetric s b b'))
      = (δ a b' + δ a' b) - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]; ring
  have e3 : peelMetric δ s a a' + peelMetric δ s b b'
      = (δ a a' + δ b b') - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]; ring
  rw [e1, e2, e3, max_sub_sub_right]
  unfold pairDeficit
  ring

/-- **`max A (B − 2c) − (R − 2c) = max (A + 2c) B − R`**（交叉 ① 的收口）。 -/
theorem max_sub_two_mul_aux (A B R c : ℝ) :
    max A (B - 2 * c) - (R - 2 * c) = max (A + 2 * c) B - R := by
  have key : max (A + 2 * c) ((B - 2 * c) + 2 * c) = max A (B - 2 * c) + 2 * c :=
    max_add_add_right A (B - 2 * c) (2 * c)
  have hB : (B - 2 * c) + 2 * c = B := by ring
  rw [hB] at key
  rw [key]
  ring

/-- **`max (A − 2c) B − (R − 2c) = max A (B + 2c) − R`**（交叉 ② 的收口）。 -/
theorem max_sub_two_mul_aux' (A B R c : ℝ) :
    max (A - 2 * c) B - (R - 2 * c) = max A (B + 2 * c) - R := by
  have key : max ((A - 2 * c) + 2 * c) (B + 2 * c) = max (A - 2 * c) B + 2 * c :=
    max_add_add_right (A - 2 * c) B (2 * c)
  have hA : (A - 2 * c) + 2 * c = A := by ring
  rw [hA] at key
  rw [key]
  ring

/-! ### 四模式表（按三个和陈述） -/

/-- 模式 `x = y = z`（同侧 `(0,0,0)` 与 3–1 `(1,1,1)` 合并）：`pd(δ') = pd(δ)`。 -/
theorem pairDeficit_peelMetric_of_sums_diag {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a a' b b' : α}
    (hx : SplitMetric s a b + SplitMetric s a' b'
      = SplitMetric s a a' + SplitMetric s b b')
    (hy : SplitMetric s a b' + SplitMetric s a' b
      = SplitMetric s a a' + SplitMetric s b b') :
    pairDeficit (peelMetric δ s) a a' b b' = pairDeficit δ a a' b b' := by
  have e1 : peelMetric δ s a b + peelMetric δ s a' b'
      = (δ a b + δ a' b') - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hx
    simp only [mul_add] at hcx
    linarith
  have e2 : peelMetric δ s a b' + peelMetric δ s a' b
      = (δ a b' + δ a' b) - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hy
    simp only [mul_add] at hcx
    linarith
  have e3 : peelMetric δ s a a' + peelMetric δ s b b'
      = (δ a a' + δ b b') - peelCoeff δ s * (SplitMetric s a a' + SplitMetric s b b') := by
    rw [peelMetric_apply, peelMetric_apply]; ring
  unfold pairDeficit
  rw [e1, e2, e3, max_sub_sub_right]
  try ring

/-- 模式 `(2,2,0)`（= `§8.6` 的 `A×A×B×B`）：`pd(δ') = pd(δ) − 2c`。 -/
theorem pairDeficit_peelMetric_of_sums_220 {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a a' b b' : α}
    (hx : SplitMetric s a b + SplitMetric s a' b' = 2)
    (hy : SplitMetric s a b' + SplitMetric s a' b = 2)
    (hz : SplitMetric s a a' + SplitMetric s b b' = 0) :
    pairDeficit (peelMetric δ s) a a' b b'
      = pairDeficit δ a a' b b' - 2 * peelCoeff δ s := by
  have e1 : peelMetric δ s a b + peelMetric δ s a' b'
      = (δ a b + δ a' b') - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hx
    simp only [mul_add] at hcx
    linarith
  have e2 : peelMetric δ s a b' + peelMetric δ s a' b
      = (δ a b' + δ a' b) - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hy
    simp only [mul_add] at hcx
    linarith
  have e3 : peelMetric δ s a a' + peelMetric δ s b b' = δ a a' + δ b b' := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hz
    simp only [mul_add] at hcx
    linarith
  unfold pairDeficit
  rw [e1, e2, e3, max_sub_sub_right]
  try ring

/-- 模式 `(0,2,2)`（**交叉 ①**）：`pd(δ') = max (A+2c) B − Z`。 -/
theorem pairDeficit_peelMetric_of_sums_022 {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a a' b b' : α}
    (hx : SplitMetric s a b + SplitMetric s a' b' = 0)
    (hy : SplitMetric s a b' + SplitMetric s a' b = 2)
    (hz : SplitMetric s a a' + SplitMetric s b b' = 2) :
    pairDeficit (peelMetric δ s) a a' b b'
      = max (δ a b + δ a' b' + 2 * peelCoeff δ s) (δ a b' + δ a' b)
          - (δ a a' + δ b b') := by
  have e1 : peelMetric δ s a b + peelMetric δ s a' b' = δ a b + δ a' b' := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hx
    simp only [mul_add] at hcx
    linarith
  have e2 : peelMetric δ s a b' + peelMetric δ s a' b
      = (δ a b' + δ a' b) - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hy
    simp only [mul_add] at hcx
    linarith
  have e3 : peelMetric δ s a a' + peelMetric δ s b b'
      = (δ a a' + δ b b') - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hz
    simp only [mul_add] at hcx
    linarith
  unfold pairDeficit
  rw [e1, e2, e3, max_sub_two_mul_aux]
  try ring

/-- 模式 `(2,0,2)`（**交叉 ②**）：`pd(δ') = max A (B+2c) − Z`。 -/
theorem pairDeficit_peelMetric_of_sums_202 {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a a' b b' : α}
    (hx : SplitMetric s a b + SplitMetric s a' b' = 2)
    (hy : SplitMetric s a b' + SplitMetric s a' b = 0)
    (hz : SplitMetric s a a' + SplitMetric s b b' = 2) :
    pairDeficit (peelMetric δ s) a a' b b'
      = max (δ a b + δ a' b') (δ a b' + δ a' b + 2 * peelCoeff δ s)
          - (δ a a' + δ b b') := by
  have e1 : peelMetric δ s a b + peelMetric δ s a' b'
      = (δ a b + δ a' b') - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hx
    simp only [mul_add] at hcx
    linarith
  have e2 : peelMetric δ s a b' + peelMetric δ s a' b = δ a b' + δ a' b := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hy
    simp only [mul_add] at hcx
    linarith
  have e3 : peelMetric δ s a a' + peelMetric δ s b b'
      = (δ a a' + δ b b') - 2 * peelCoeff δ s := by
    rw [peelMetric_apply, peelMetric_apply]
    have hcx := congrArg (fun t => peelCoeff δ s * t) hz
    simp only [mul_add] at hcx
    linarith
  unfold pairDeficit
  rw [e1, e2, e3, max_sub_two_mul_aux']
  try ring

/-! ### 危险模式的实数核 -/

/-- ★★ **交叉 ① 的实数核**：`2c = iso ≤ max Z B − A`、`0 < max (A+2c) B − Z` ⇒ `0 < max A B − Z`。 -/
theorem cross_core {A B Z c iso : ℝ} (h2c : 2 * c = iso)
    (hiso : iso ≤ max Z B - A) (hpos : 0 < max (A + 2 * c) B - Z) :
    0 < max A B - Z := by
  by_contra hcon
  rw [not_lt] at hcon
  have hAZ : A ≤ Z := le_trans (le_max_left A B) (by linarith)
  have hBZ : B ≤ Z := le_trans (le_max_right A B) (by linarith)
  have hAZc : Z < A + 2 * c := by
    by_contra hc
    rw [not_lt] at hc
    have hle : max (A + 2 * c) B ≤ Z := max_le hc hBZ
    linarith
  have hmax : max Z B = Z := max_eq_left hBZ
  have h1 : iso ≤ Z - A := by rw [← hmax]; exact hiso
  linarith

/-- ★★ **交叉 ② 的实数核**：`2c = iso ≤ max Z A − B`、`0 < max A (B+2c) − Z` ⇒ `0 < max A B − Z`。 -/
theorem cross_core2 {A B Z c iso : ℝ} (h2c : 2 * c = iso)
    (hiso : iso ≤ max Z A - B) (hpos : 0 < max A (B + 2 * c) - Z) :
    0 < max A B - Z := by
  by_contra hcon
  rw [not_lt] at hcon
  have hAZ : A ≤ Z := le_trans (le_max_left A B) (by linarith)
  have hBZ : B ≤ Z := le_trans (le_max_right A B) (by linarith)
  have hBZc : Z < B + 2 * c := by
    by_contra hc
    rw [not_lt] at hc
    have hle : max A (B + 2 * c) ≤ Z := max_le hAZ hc
    linarith
  have hmax : max Z A = Z := max_eq_left hAZ
  have h1 : iso ≤ Z - B := by rw [← hmax]; exact hiso
  linarith


/-- ★★★ **交叉 ①（`{a,b}⊆A_s`、`{a',b'}⊆B_s`）：`pd(δ') > 0 ⇒ pd(δ) > 0`。** -/
theorem pd_pos_of_peel_pos_cross_AA {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α} (hδ : ∀ x y, δ x y = δ y x)
    (ha : a ∈ s.sideA) (hb : b ∈ s.sideA) (ha' : a' ∈ s.sideB) (hb' : b' ∈ s.sideB)
    (h : 0 < pairDeficit (peelMetric δ s) a a' b b') :
    0 < pairDeficit δ a a' b b' := by
  have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA ha hb
  have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB ha' hb'
  have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha hb'
  have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha' hb
  have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha ha'
  have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB hb hb'
  have hx : SplitMetric s a b + SplitMetric s a' b' = 0 := by rw [h1, h2]; norm_num
  have hy : SplitMetric s a b' + SplitMetric s a' b = 2 := by rw [h3, h4]; norm_num
  have hz : SplitMetric s a a' + SplitMetric s b b' = 2 := by rw [h5, h6]; norm_num
  rw [pairDeficit_peelMetric_of_sums_022 hx hy hz] at h
  have hiso : isolationIndex δ s.sideA s.sideB ≤ pairDeficit δ a b a' b' :=
    isolationIndex_le_pairDeficit δ (s.nonempty 0) (s.nonempty 1) ha hb ha' hb'
  have hpd : pairDeficit δ a b a' b'
      = max (δ a a' + δ b b') (δ a b' + δ a' b) - (δ a b + δ a' b') := by
    unfold pairDeficit
    rw [hδ b a']
  have h2c : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  have hiso' : isolationIndex δ s.sideA s.sideB
      ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) - (δ a b + δ a' b') := by
    rw [← hpd]
    exact hiso
  exact cross_core (A := δ a b + δ a' b') (B := δ a b' + δ a' b) (Z := δ a a' + δ b b')
    (c := peelCoeff δ s) (iso := isolationIndex δ s.sideA s.sideB) h2c hiso' h

/-- ★★★ **交叉 ①（镜像：`{a,b}⊆B_s`、`{a',b'}⊆A_s`）：同上。** -/
theorem pd_pos_of_peel_pos_cross_BB {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α} (hδ : ∀ x y, δ x y = δ y x)
    (ha : a ∈ s.sideB) (hb : b ∈ s.sideB) (ha' : a' ∈ s.sideA) (hb' : b' ∈ s.sideA)
    (h : 0 < pairDeficit (peelMetric δ s) a a' b b') :
    0 < pairDeficit δ a a' b b' := by
  have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideB ha hb
  have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideA ha' hb'
  have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha hb'
  have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha' hb
  have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha ha'
  have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA hb hb'
  have hx : SplitMetric s a b + SplitMetric s a' b' = 0 := by rw [h1, h2]; norm_num
  have hy : SplitMetric s a b' + SplitMetric s a' b = 2 := by rw [h3, h4]; norm_num
  have hz : SplitMetric s a a' + SplitMetric s b b' = 2 := by rw [h5, h6]; norm_num
  rw [pairDeficit_peelMetric_of_sums_022 hx hy hz] at h
  have hiso : isolationIndex δ s.sideA s.sideB ≤ pairDeficit δ a' b' a b :=
    isolationIndex_le_pairDeficit δ (s.nonempty 0) (s.nonempty 1) ha' hb' ha hb
  have hpd : pairDeficit δ a' b' a b
      = max (δ a a' + δ b b') (δ a b' + δ a' b) - (δ a b + δ a' b') := by
    unfold pairDeficit
    rw [hδ a' a, hδ b' b, hδ b' a, add_comm (δ a' b') (δ a b), add_comm (δ a' b) (δ a b')]
  have h2c : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  have hiso' : isolationIndex δ s.sideA s.sideB
      ≤ max (δ a a' + δ b b') (δ a b' + δ a' b) - (δ a b + δ a' b') := by
    rw [← hpd]
    exact hiso
  exact cross_core (A := δ a b + δ a' b') (B := δ a b' + δ a' b) (Z := δ a a' + δ b b')
    (c := peelCoeff δ s) (iso := isolationIndex δ s.sideA s.sideB) h2c hiso' h

/-- ★★★ **交叉 ②（`{a,b'}⊆A_s`、`{a',b}⊆B_s`）：`pd(δ') > 0 ⇒ pd(δ) > 0`。** -/
theorem pd_pos_of_peel_pos_cross_ABA {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α} (hδ : ∀ x y, δ x y = δ y x)
    (ha : a ∈ s.sideA) (hb' : b' ∈ s.sideA) (ha' : a' ∈ s.sideB) (hb : b ∈ s.sideB)
    (h : 0 < pairDeficit (peelMetric δ s) a a' b b') :
    0 < pairDeficit δ a a' b b' := by
  have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha hb
  have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha' hb'
  have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideA ha hb'
  have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideB ha' hb
  have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha ha'
  have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA hb hb'
  have hx : SplitMetric s a b + SplitMetric s a' b' = 2 := by rw [h1, h2]; norm_num
  have hy : SplitMetric s a b' + SplitMetric s a' b = 0 := by rw [h3, h4]; norm_num
  have hz : SplitMetric s a a' + SplitMetric s b b' = 2 := by rw [h5, h6]; norm_num
  rw [pairDeficit_peelMetric_of_sums_202 hx hy hz] at h
  have hiso : isolationIndex δ s.sideA s.sideB ≤ pairDeficit δ a b' a' b :=
    isolationIndex_le_pairDeficit δ (s.nonempty 0) (s.nonempty 1) ha hb' ha' hb
  have hpd : pairDeficit δ a b' a' b
      = max (δ a a' + δ b b') (δ a b + δ a' b') - (δ a b' + δ a' b) := by
    unfold pairDeficit
    rw [hδ b' b, hδ b' a']
  have h2c : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  have hiso' : isolationIndex δ s.sideA s.sideB
      ≤ max (δ a a' + δ b b') (δ a b + δ a' b') - (δ a b' + δ a' b) := by
    rw [← hpd]
    exact hiso
  exact cross_core2 (A := δ a b + δ a' b') (B := δ a b' + δ a' b) (Z := δ a a' + δ b b')
    (c := peelCoeff δ s) (iso := isolationIndex δ s.sideA s.sideB) h2c hiso' h

/-- ★★★ **交叉 ②（镜像：`{a,b'}⊆B_s`、`{a',b}⊆A_s`）：同上。** -/
theorem pd_pos_of_peel_pos_cross_BAB {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} {a b a' b' : α} (hδ : ∀ x y, δ x y = δ y x)
    (ha : a ∈ s.sideB) (hb' : b' ∈ s.sideB) (ha' : a' ∈ s.sideA) (hb : b ∈ s.sideA)
    (h : 0 < pairDeficit (peelMetric δ s) a a' b b') :
    0 < pairDeficit δ a a' b b' := by
  have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha hb
  have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB ha' hb'
  have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideB ha hb'
  have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideA ha' hb
  have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA ha ha'
  have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB hb hb'
  have hx : SplitMetric s a b + SplitMetric s a' b' = 2 := by rw [h1, h2]; norm_num
  have hy : SplitMetric s a b' + SplitMetric s a' b = 0 := by rw [h3, h4]; norm_num
  have hz : SplitMetric s a a' + SplitMetric s b b' = 2 := by rw [h5, h6]; norm_num
  rw [pairDeficit_peelMetric_of_sums_202 hx hy hz] at h
  have hiso : isolationIndex δ s.sideA s.sideB ≤ pairDeficit δ a' b a b' :=
    isolationIndex_le_pairDeficit δ (s.nonempty 0) (s.nonempty 1) ha' hb ha hb'
  have hpd : pairDeficit δ a' b a b'
      = max (δ a a' + δ b b') (δ a b + δ a' b') - (δ a b' + δ a' b) := by
    unfold pairDeficit
    rw [hδ a' a, hδ b a, add_comm (δ a' b') (δ a b), add_comm (δ a' b) (δ a b')]
  have h2c : 2 * peelCoeff δ s = isolationIndex δ s.sideA s.sideB := by
    unfold peelCoeff
    ring
  have hiso' : isolationIndex δ s.sideA s.sideB
      ≤ max (δ a a' + δ b b') (δ a b + δ a' b') - (δ a b' + δ a' b) := by
    rw [← hpd]
    exact hiso
  exact cross_core2 (A := δ a b + δ a' b') (B := δ a b' + δ a' b) (Z := δ a a' + δ b b')
    (c := peelCoeff δ s) (iso := isolationIndex δ s.sideA s.sideB) h2c hiso' h


/-! ### 装配：剥离下 d-split 的**无条件存活**（(P1) 的核心） -/

/-- ★★★★ **(P1) 的核心**：`t` 是 `δ' := δ − c·δ_s` 的 d-split ⇒ `t` 是 `δ` 的 d-split
（**不需要 `s` 与 `t` 相容**）。16 个成员性构形 × 四模式；两个危险模式由
`pd_pos_of_peel_pos_cross_*` 收口。 -/
theorem isDSplit_of_isDSplit_peelMetric_general {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s t : Split α} (hδ : ∀ x y, δ x y = δ y x)
    (hc : 0 ≤ peelCoeff δ s) (h : IsDSplit (peelMetric δ s) t.sideA t.sideB) :
    IsDSplit δ t.sideA t.sideB := by
  intro a ha a' ha' b hb b' hb'
  have hpos : 0 < pairDeficit (peelMetric δ s) a a' b b' := by
    have h0 := h a ha a' ha' b hb b' hb'
    unfold pairDeficit
    linarith
  suffices hgoal : 0 < pairDeficit δ a a' b b' by
    unfold pairDeficit at hgoal
    linarith
  by_cases c_a : a ∈ s.sideA <;> by_cases c_a' : a' ∈ s.sideA <;>
    by_cases c_b : b ∈ s.sideA <;> by_cases c_b' : b' ∈ s.sideA

  · -- 构形 AAAA
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b'
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b'
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_a'
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideA c_b c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 AAAB
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_b'B
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_b'B
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_a'
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_b c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 AABA
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_bB
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b'
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b'
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_bB
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_a'
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_bB c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 AABB
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_bB
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_b'B
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_b'B
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_bB
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_a'
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB c_bB c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = 2 := by rw [h1, h2]; norm_num
    have hy : SplitMetric s a b' + SplitMetric s a' b = 2 := by rw [h3, h4]; norm_num
    have hz : SplitMetric s a a' + SplitMetric s b b' = 0 := by rw [h5, h6]; norm_num
    rw [pairDeficit_peelMetric_of_sums_220 hx hy hz] at hpos
    linarith

  · -- 构形 ABAA
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b'
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b'
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_a'B
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideA c_b c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 ABAB
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_b'B
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_b'B
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_a'B
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_b c_b'B
    exact pd_pos_of_peel_pos_cross_AA hδ c_a c_b c_a'B c_b'B hpos

  · -- 构形 ABBA
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_bB
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b'
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a c_b'
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_bB
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_a'B
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_bB c_b'
    exact pd_pos_of_peel_pos_cross_ABA hδ c_a c_b' c_a'B c_bB hpos

  · -- 构形 ABBB
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_bB
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_b'B
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_b'B
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_bB
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a c_a'B
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB c_bB c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 BAAA
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b'
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b'
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_a'
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideA c_b c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 BAAB
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_b'B
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_b'B
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_a'
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_b c_b'B
    exact pd_pos_of_peel_pos_cross_BAB hδ c_aB c_b'B c_a' c_b hpos

  · -- 构形 BABA
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_bB
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideA c_a' c_b'
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b'
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_bB
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_a'
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_bB c_b'
    exact pd_pos_of_peel_pos_cross_BB hδ c_aB c_bB c_a' c_b' hpos

  · -- 构形 BABB
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_bB
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_b'B
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_b'B
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_a' c_bB
    have h5 : SplitMetric s a a' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_a'
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB c_bB c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 BBAA
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b'
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b'
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_a'B
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideA c_b c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = 2 := by rw [h1, h2]; norm_num
    have hy : SplitMetric s a b' + SplitMetric s a' b = 2 := by rw [h3, h4]; norm_num
    have hz : SplitMetric s a a' + SplitMetric s b b' = 0 := by rw [h5, h6]; norm_num
    rw [pairDeficit_peelMetric_of_sums_220 hx hy hz] at hpos
    linarith

  · -- 构形 BBAB
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_b'B
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_b'B
    have h4 : SplitMetric s a' b = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_a'B
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideA_mem_sideB c_b c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 BBBA
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_bB
    have h2 : SplitMetric s a' b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_a'B c_b'
    have h3 : SplitMetric s a b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_aB c_b'
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_bB
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_a'B
    have h6 : SplitMetric s b b' = 1 := splitMetric_eq_one_of_mem_sideB_mem_sideA c_bB c_b'
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos

  · -- 构形 BBBB
    have c_aB : a ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a).mpr c_a
    have c_a'B : a' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s a').mpr c_a'
    have c_bB : b ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b).mpr c_b
    have c_b'B : b' ∈ s.sideB := (mem_sideB_iff_not_mem_sideA s b').mpr c_b'
    have h1 : SplitMetric s a b = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_bB
    have h2 : SplitMetric s a' b' = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_b'B
    have h3 : SplitMetric s a b' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_b'B
    have h4 : SplitMetric s a' b = 0 := splitMetric_eq_zero_of_mem_sideB c_a'B c_bB
    have h5 : SplitMetric s a a' = 0 := splitMetric_eq_zero_of_mem_sideB c_aB c_a'B
    have h6 : SplitMetric s b b' = 0 := splitMetric_eq_zero_of_mem_sideB c_bB c_b'B
    have hx : SplitMetric s a b + SplitMetric s a' b' = SplitMetric s a a' + SplitMetric s b b' := by rw [h1, h2, h5, h6]; try ring
    have hy : SplitMetric s a b' + SplitMetric s a' b = SplitMetric s a a' + SplitMetric s b b' := by rw [h3, h4, h5, h6]; try ring
    rw [pairDeficit_peelMetric_of_sums_diag hx hy] at hpos
    exact hpos


/-! ## 8.13 ★★★★★ W28 泳道 e：**收口** —— `canonicalSplitDecomposition_gap_faithful_v2_holds`

`§8.12` 证了 (P1) 的核心「剥离下 d-split 无条件存活」。本节把它接成三级：

1. `dSplits_peelMetric_subset`：`dSplits δ' ⊆ dSplits δ`（逐点用 `§8.12` 的存活引理）；
2. ★★★ `dSplitsPeelDecrease_holds`：**(P1) 成立** —— `(dSplits δ').card < (dSplits δ).card`
   （真子集：`s` 是 `δ` 的 d-split 而 `peelMetric_not_isDSplit` 说它**不再**是 `δ'` 的）；
3. ★★★★★ `canonicalSplitDecomposition_gap_faithful_v2_holds`：
   **BdD Thm 2 的存在性一半**（`§8.4` 的 `canonicalSplitDecomposition_gap_faithful_v2`，`:1154`，
   `def` **未改一字**）—— 由 `§8.11` 的收口归约 `…_of_dSplitsPeelDecrease` 一步得出。

★ 链条回顾（全部机器验证、零 `sorry`/`axiom`）：
`§8.7` 基例（`δ` 本身 split-prime ⇒ `F = ∅`）＋ `§8.8` 归纳步（并回 `c·δ_s`）＋
`§8.10` 对 `(dSplits δ).card` 的强归纳 ＋ `§8.12` 的 (P1)（基数严格下降）⇒ 存在性 ①。 -/

/-- ★★★ **(P1) 的第一步**：剥离后 `dSplits` **只减不增**。 -/
theorem dSplits_peelMetric_subset {α : Type*} [Fintype α] [DecidableEq α]
    {δ : α → α → ℝ} {s : Split α} (hδ : ∀ x y, δ x y = δ y x)
    (hds : IsDSplit δ s.sideA s.sideB) :
    dSplits (peelMetric δ s) ⊆ dSplits δ := by
  intro t ht
  have hc : 0 ≤ peelCoeff δ s :=
    le_of_lt (peelCoeff_pos (s.nonempty 0) (s.nonempty 1) hds)
  exact mem_dSplits.mpr
    (isDSplit_of_isDSplit_peelMetric_general (s := s) (t := t) hδ hc (mem_dSplits.mp ht))

/-- ★★★ **(P1) 成立**（`§8.11` 的 `dSplitsPeelDecrease`）：剥离 `δ` 的任一 d-split 后，
`dSplits` 的基数**严格下降**。

真子集论证：`dSplits δ' ⊆ dSplits δ`（`dSplits_peelMetric_subset`），且
`s ∈ dSplits δ \ dSplits δ'`（`s` 是 `δ` 的 d-split，而 `peelMetric_not_isDSplit` 给出
`s` **不是** `δ'` 的 d-split）。 -/
theorem dSplitsPeelDecrease_holds : dSplitsPeelDecrease := by
  intro α _ _ δ hδ _ _ _ s hds
  have hsub : dSplits (peelMetric δ s) ⊆ dSplits δ :=
    dSplits_peelMetric_subset (δ := δ) (s := s) hδ hds
  have hne : dSplits (peelMetric δ s) ≠ dSplits δ := by
    intro heq
    have hm : s ∈ dSplits (peelMetric δ s) := by
      rw [heq]
      exact mem_dSplits.mpr hds
    exact peelMetric_not_isDSplit (s.nonempty 0) (s.nonempty 1) (mem_dSplits.mp hm)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- ★★★★★ **BdD Thm 2 的存在性一半 —— 收口**：
`canonicalSplitDecomposition_gap_faithful_v2`（`:1154`，`def` **未改一字**）**成立**。

即：任意有限度量 `δ`（对称、对角 `0`、非负、三角不等式）都存在
`F`、正系数 `c`、残差 `δ₀`，使 `δ = δ₀ + Σ_{s∈F} c_s·δ_s`，`δ₀` **划分版 split-prime**、
非负、对角 `0`，且 `F` 上系数**全正**。

★ 证明：`§8.11` 的 `canonicalSplitDecomposition_gap_faithful_v2_of_dSplitsPeelDecrease`
（对 `(dSplits δ).card` 的强归纳；基例 `§8.7`、归纳步 `§8.8`）＋ `dSplitsPeelDecrease_holds`（(P1)）。
★ **零 `sorry` / `admit` / `axiom` / `opaque`，零额外前提**。 -/
theorem canonicalSplitDecomposition_gap_faithful_v2_holds :
    canonicalSplitDecomposition_gap_faithful_v2 :=
  canonicalSplitDecomposition_gap_faithful_v2_of_dSplitsPeelDecrease dSplitsPeelDecrease_holds

end Split

/-! ## 8.12 ★★★★ `weakCompatibilityRealization_gap_weights`（`:3358`）**已被机器证伪**

### 结论

`def weakCompatibilityRealization_gap_weights` 的**第三个合取项**（`:3363-3365`）**为假**，
故它的 `_holds` 形态**不可能成立**。反例已机器验证：
`not_weakCompatibilityRealization_gap_weights : ¬ weakCompatibilityRealization_gap_weights.{0}`。

### 缺陷（量词错位）

第三个合取项量化 `∀ s, (s ∈ F ∨ s.swap ∈ F) → α_s = 2·(w s + [s.swap ∈ F]·w s.swap)`。
当 `s ∉ F` 而 `s.swap ∈ F` 时：

* `∨` 前提**成立**（右析取：`(s.swap).swap = s ∈ F`）；
* 但 `δ = Σ_{u∈F} w_u δ_u` 中**没有** `w s` 这一项（`F` 不含 `s`）；
* 而假设只要求 `∀ s ∈ F, 0 < w s` ⇒ `w` 在 `F` **外任意** ⇒ 右侧的 `w s` 可以任意大。

### 反例（`Fin 4`）

`s₀ := {0,1}|{2,3}`、`F := {s₀}`、`w s₀ = 1`、`w s₀.swap = 5`。

* `F` 单元集 ⇒ `δ = 1·δ_{s₀}` ⇒ `α_{s₀} = α_{s₀.swap} = 2`；
* 结论在 `s₀` 上给 `2·(1 + 0) = 2` ✓；
* 结论在 `s₀.swap` 上（`s₀.swap ∉ F`、`(s₀.swap).swap = s₀ ∈ F`）给 `2·(5 + 1) = 12` ✗ ⇒ 矛盾。

### 正确的成员形态（**待协调侧裁定**；本批**不新建 `def`**）

应把量词限制为 `s ∈ F`：
`∀ s ∈ F, α_s = 2·(w s + (if s.swap ∈ F then w s.swap else 0))`。
`2` 与「`s` 与 `s.swap` 系数**相加**」的口径**不变**；`s ∉ F` 时右侧就是 `2·(w s + 0)`。

★ 即使如此修正，**上界** `α_s ≤ 2(w_s + [s.swap∈F]w_swap)` 仍需一条**组合引理**：
存在四元组 `a,a' ∈ s.sideA`、`b,b' ∈ s.sideB`，使 `F \ {s,s.swap}` 中**没有**成员把
`{a,a'}` 与 `{b,b'}` 分到两侧（弱相容是关键；**退化的** `a=a', b=b'` 版本为假）。
本文件证明的**下界**与**单成员精确形态**见 `§8.13`。 -/

open Finset

namespace Split

/-- `Fin 4` 上的 split `{0,1} | {2,3}`（反例载体）。 -/
def cexSplit4 : Split (Fin 4) := ofSideA {0, 1} (by decide) (by decide)

/-- `cexSplit4.swap ≠ cexSplit4`（两侧非空且互异 ⇒ `swap` 不是恒等）。 -/
theorem cexSplit4_swap_ne : cexSplit4.swap ≠ cexSplit4 := by
  intro h
  have h1 : (0 : Fin 4) ∈ cexSplit4.sideB := by
    rw [← swap_sideA cexSplit4, h]
    simp [cexSplit4]
  simp [cexSplit4] at h1

/-- `pairDeficit` 在**两侧整体对换**下不变（只需对称性）。 -/
theorem pairDeficit_swap_sides {α : Type*} {δ : α → α → ℝ} (hδ : ∀ x y, δ x y = δ y x)
    (a a' b b' : α) : pairDeficit δ b b' a a' = pairDeficit δ a a' b b' := by
  unfold pairDeficit
  have h1 : δ b a + δ b' a' = δ a b + δ a' b' := by rw [hδ b a, hδ b' a']
  have h2 : δ b a' + δ b' a = δ a b' + δ a' b := by rw [hδ b a', hδ b' a]; ring
  have h3 : δ b b' + δ a a' = δ a a' + δ b b' := by ring
  rw [h1, h2, h3]

/-- ★ `isolationIndex` 对两侧互换不变（需对称性）：`α_{A,B} = α_{B,A}`。 -/
theorem isolationIndex_comm {α : Type*} [Fintype α] [DecidableEq α]
    (δ : α → α → ℝ) (hδ : ∀ x y, δ x y = δ y x) (A B : Finset α) :
    isolationIndex δ A B = isolationIndex δ B A := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · rw [isolationIndex_eq_inf' δ hA hB, isolationIndex_eq_inf' δ hB hA]
      refine le_antisymm ?_ ?_
      · refine Finset.le_inf' (isoQuadruples_nonempty hB hA) _ ?_
        rintro ⟨⟨b, b'⟩, a, a'⟩ hq
        rw [mem_isoQuadruples] at hq
        obtain ⟨hb, hb', ha, ha'⟩ := hq
        calc (isoQuadruples A B).inf' (isoQuadruples_nonempty hA hB)
              (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
            ≤ pairDeficit δ a a' b b' :=
              Finset.inf'_le (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
                (mem_isoQuadruples.mpr ⟨ha, ha', hb, hb'⟩)
          _ = pairDeficit δ b b' a a' := (pairDeficit_swap_sides hδ a a' b b').symm
      · refine Finset.le_inf' (isoQuadruples_nonempty hA hB) _ ?_
        rintro ⟨⟨a, a'⟩, b, b'⟩ hq
        rw [mem_isoQuadruples] at hq
        obtain ⟨ha, ha', hb, hb'⟩ := hq
        calc (isoQuadruples B A).inf' (isoQuadruples_nonempty hB hA)
              (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
            ≤ pairDeficit δ b b' a a' :=
              Finset.inf'_le (fun q => pairDeficit δ q.1.1 q.1.2 q.2.1 q.2.2)
                (mem_isoQuadruples.mpr ⟨hb, hb', ha, ha'⟩)
          _ = pairDeficit δ a a' b b' := pairDeficit_swap_sides hδ a a' b b'
    · have hB0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
      simp [isolationIndex, isoQuadruples, hB0]
  · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [isolationIndex, isoQuadruples, hA0]

/-- ★★★ **反例**：`weakCompatibilityRealization_gap_weights`（`:3358`）在宇宙 `0` 上**为假**。

`F := {s₀}`、`w s₀ = 1`、`w (s₀.swap) = 5`。`F` 是单元集 ⇒ `δ = 1·δ_{s₀}` ⇒
`α_{s₀} = α_{s₀.swap} = 2`；但结论在 `s₀.swap` 上（`∨` 前提由 `(s₀.swap).swap = s₀ ∈ F` 成立）
要求 `α = 2·(5 + 1) = 12`。 -/
theorem not_weakCompatibilityRealization_gap_weights :
    ¬ weakCompatibilityRealization_gap_weights.{0} := by
  intro h
  have hF : WeaklyCompatible (↑({cexSplit4} : Finset (Split (Fin 4))) : Set (Split (Fin 4))) := by
    have hp := weaklyCompatible_pair cexSplit4 cexSplit4
    simpa using hp
  have hw : ∀ s ∈ ({cexSplit4} : Finset (Split (Fin 4))),
      0 < (fun t : Split (Fin 4) => if t = cexSplit4 then (1 : ℝ) else 5) s := by
    intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    simp
  obtain ⟨δ, hsymm, _, hiso⟩ :=
    h (α := Fin 4) (F := {cexSplit4})
      (w := fun t : Split (Fin 4) => if t = cexSplit4 then (1 : ℝ) else 5) hF hw
  have hne : cexSplit4.swap ≠ cexSplit4 := cexSplit4_swap_ne
  have hmem0 : (cexSplit4 ∈ ({cexSplit4} : Finset (Split (Fin 4)))
      ∨ cexSplit4.swap ∈ ({cexSplit4} : Finset (Split (Fin 4)))) := Or.inl (Finset.mem_singleton_self _)
  have hmem1 : (cexSplit4.swap ∈ ({cexSplit4} : Finset (Split (Fin 4)))
      ∨ (cexSplit4.swap).swap ∈ ({cexSplit4} : Finset (Split (Fin 4)))) := by
    refine Or.inr ?_
    rw [swap_swap]
    exact Finset.mem_singleton_self _
  have h1 : isolationIndex δ cexSplit4.sideA cexSplit4.sideB = 2 := by
    have hh := hiso cexSplit4 hmem0
    simp [hne] at hh
    linarith
  have h2 : isolationIndex δ cexSplit4.swap.sideA cexSplit4.swap.sideB = 12 := by
    have hh := hiso cexSplit4.swap hmem1
    simp [hne] at hh ⊢
    linarith
  have hcomm : isolationIndex δ cexSplit4.swap.sideA cexSplit4.swap.sideB
      = isolationIndex δ cexSplit4.sideA cexSplit4.sideB := by
    rw [swap_sideA, swap_sideB]
    exact isolationIndex_comm δ hsymm cexSplit4.sideB cexSplit4.sideA
  linarith

end Split

open Finset

namespace Split

/-! ## 8.13 ★★★★ 忠实公式的**可证半边**（与 `:3358` 的 `def` 修不修无关的真数学）

本节把 BdD Thm 3 忠实半边的**三个可证结果**落地（`def` 的第三个合取项本身为假，见 `§8.12`）：

1. `isolationIndex_splitMetric`：`δ = c·δ_u ⇒ α_u = 2c`（单 split 度量，**任意** `c`）；
2. `isolationIndex_weights_singleton` / `isolationIndex_weights_swap_pair`：
   `F = {s}` ⇒ `α_s = 2·w s`；`F = {s, s.swap}` ⇒ `α_s = 2·(w s + w s.swap)`
   —— 后者正是「`s` 与 `s.swap` 系数**相加**」口径的机器验证；
3. `isolationIndex_ge_two_mul_weight`：**一般族的下界**
   `α_s ≥ 2·(w s + [s.swap ∈ F]·w s.swap)`（弱相容 ＋ `w > 0`）。

★ **仍缺的**（见 `§8.12` 尾部）：一般族的**上界** `α_s ≤ 2(w_s + [s.swap∈F]w_swap)`，
它等价于一条组合引理：存在 `a,a' ∈ s.sideA`、`b,b' ∈ s.sideB`，使 `F \ {s,s.swap}` 中
没有成员把 `{a,a'}` 与 `{b,b'}` 分到两侧。 -/

/-- `swap` 不是恒等（两侧非空且不交）。 -/
theorem swap_ne {α : Type*} [Fintype α] [DecidableEq α] (s : Split α) : s.swap ≠ s := by
  intro h
  obtain ⟨a, ha⟩ := s.nonempty 0
  have hb : a ∈ s.sideB := by
    rw [← swap_sideA s, h]
    exact ha
  exact (Finset.disjoint_left.mp s.disjoint_sides) ha hb

/-- ★ `SplitMetric` 对 `swap` 不变：同一无向 split 的两个编码给出**同一个**度量
（`s` 与 `s.swap` 系数相加的**根因**）。 -/
theorem splitMetric_swap {α : Type*} [Fintype α] [DecidableEq α]
    (s : Split α) (x y : α) : SplitMetric s.swap x y = SplitMetric s x y := by
  simp only [SplitMetric, swap_sideA, swap_sideB, or_comm]

/-- ★★ **单 split 度量在 `A²×B²` 上的四点亏损恒为 `2c`**：
`a,a' ∈ u.sideA`、`b,b' ∈ u.sideB` ⇒ `P_u = X_u = 2`、`I_u = 0` ⇒ `pd = 2c`。 -/
theorem pairDeficit_splitMetric {α : Type*} [Fintype α] [DecidableEq α]
    (u : Split α) (c : ℝ) {a a' b b' : α}
    (ha : a ∈ u.sideA) (ha' : a' ∈ u.sideA) (hb : b ∈ u.sideB) (hb' : b' ∈ u.sideB) :
    pairDeficit (fun x y => c * SplitMetric u x y) a a' b b' = 2 * c := by
  have h1 : a ∉ u.sideB := fun h => (Finset.disjoint_left.mp u.disjoint_sides) ha h
  have h2 : a' ∉ u.sideB := fun h => (Finset.disjoint_left.mp u.disjoint_sides) ha' h
  have h3 : b ∉ u.sideA := fun h => (Finset.disjoint_left.mp u.disjoint_sides) h hb
  have h4 : b' ∉ u.sideA := fun h => (Finset.disjoint_left.mp u.disjoint_sides) h hb'
  rw [show pairDeficit (fun x y => c * SplitMetric u x y) a a' b b'
      = max (c * 1 + c * 1) (c * 1 + c * 1) - (c * 0 + c * 0) from by
    simp [pairDeficit, SplitMetric, ha, ha', hb, hb', h1, h2, h3, h4]]
  rw [max_self]
  ring

/-- ★★ **单 split 度量的隔离指数**：`α_u(c·δ_u) = 2c`（对**任意** `c`；`A²×B²` 上每项都等于 `2c`）。 -/
theorem isolationIndex_splitMetric {α : Type*} [Fintype α] [DecidableEq α]
    (u : Split α) (c : ℝ) :
    isolationIndex (fun x y => c * SplitMetric u x y) u.sideA u.sideB = 2 * c := by
  rw [isolationIndex_eq_inf' (A := u.sideA) (B := u.sideB) _ (u.nonempty 0) (u.nonempty 1)]
  refine Finset.inf'_eq_of_forall (isoQuadruples_nonempty (u.nonempty 0) (u.nonempty 1)) _ ?_
  rintro ⟨⟨a, a'⟩, b, b'⟩ hq
  obtain ⟨ha, ha', hb, hb'⟩ := mem_isoQuadruples.mp hq
  exact pairDeficit_splitMetric u c ha ha' hb hb'

/-- ★★★ **`F = {s}` 的精确公式**（BdD Thm 3 忠实半边的**单成员**情形，零额外假设）：
`α_s = 2·w s`。 -/
theorem isolationIndex_weights_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (s : Split α) (w : Split α → ℝ) :
    isolationIndex (fun x y => ∑ u ∈ ({s} : Finset (Split α)), w u * SplitMetric u x y)
      s.sideA s.sideB = 2 * w s := by
  have hfun : (fun x y => ∑ u ∈ ({s} : Finset (Split α)), w u * SplitMetric u x y)
      = fun x y => w s * SplitMetric s x y := by
    funext x y
    rw [Finset.sum_singleton]
  rw [hfun]
  exact isolationIndex_splitMetric s (w s)

/-- ★★★★ **`F = {s, s.swap}` 的精确公式**：`α_s = 2·(w s + w s.swap)`。

这是「`s` 与 `s.swap` 是同一无向 split 的两个编码 ⇒ 系数**相加**」口径的**机器验证**
（`splitMetric_swap` 是根因；`s ≠ s.swap` 由 `swap_ne`）。 -/
theorem isolationIndex_weights_swap_pair {α : Type*} [Fintype α] [DecidableEq α]
    (s : Split α) (w : Split α → ℝ) :
    isolationIndex (fun x y => ∑ u ∈ ({s, s.swap} : Finset (Split α)), w u * SplitMetric u x y)
      s.sideA s.sideB = 2 * (w s + w s.swap) := by
  have hne : s ∉ ({s.swap} : Finset (Split α)) := by
    simp only [Finset.mem_singleton]
    exact fun h => swap_ne s h.symm
  have hfun : (fun x y => ∑ u ∈ ({s, s.swap} : Finset (Split α)), w u * SplitMetric u x y)
      = fun x y => (w s + w s.swap) * SplitMetric s x y := by
    funext x y
    rw [Finset.sum_insert hne, Finset.sum_singleton, splitMetric_swap]
    ring
  rw [hfun]
  exact isolationIndex_splitMetric s (w s + w s.swap)

/-- ★★★★ **一般族逐四元组的四点亏损公式**：
`pd(Σ_{u∈F} w_u δ_u) = 2·max (c_W − c_P) (c_W − c_X)`，
其中 `c_W, c_P, c_X` 是 W/P/X 三种配对的权重和。

证明：§7.2 的两条差分恒等式给 `X̂ − Î = 2(c_W − c_X)`、`X̂ − P̂ = 2(c_P − c_X)`，
相减得 `P̂ − Î = 2(c_W − c_P)`；而 `pd = max P̂ X̂ − Î = max (P̂ − Î) (X̂ − Î)`。 -/
theorem pairDeficit_sum_eq {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Split α)) (w : Split α → ℝ) (a a' b b' : α) :
    pairDeficit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) a a' b b'
      = 2 * max
          ((∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
            - (∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u))
          ((∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u)
            - (∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u)) := by
  set f : α → α → ℝ := fun x y => ∑ u ∈ F, w u * SplitMetric u x y with hf
  set cW : ℝ := ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u with hcW
  set cP : ℝ := ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u with hcP
  set cX : ℝ := ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u with hcX
  have hW : f a b' + f a' b - (f a a' + f b b') = 2 * cW - 2 * cX := by
    rw [hf]
    exact splitMetricSum_diff_qW F w a a' b b'
  have hP : f a b' + f a' b - (f a b + f a' b') = 2 * cP - 2 * cX := by
    rw [hf]
    exact splitMetricSum_diff_qP F w a a' b b'
  have hPi : f a b + f a' b' - (f a a' + f b b') = 2 * cW - 2 * cP := by linarith
  have hmax : max (f a b + f a' b') (f a b' + f a' b) - (f a a' + f b b')
      = max ((f a b + f a' b') - (f a a' + f b b'))
          ((f a b' + f a' b) - (f a a' + f b b')) := by
    rcases le_total (f a b + f a' b') (f a b' + f a' b) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
    · rw [max_eq_left h, max_eq_left (by linarith)]
  have h2 : max (2 * cW - 2 * cP) (2 * cW - 2 * cX) = 2 * max (cW - cP) (cW - cX) := by
    rcases le_total (cW - cP) (cW - cX) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      ring
  unfold pairDeficit
  rw [hmax, hPi, hW, h2]

/-- ★★★★★ **一般下界**（BdD Thm 3 忠实半边的 `≥` 方向，弱相容 ＋ 正权重）：
`α_s ≥ 2·(w s + [s.swap ∈ F]·w s.swap)`。

证明：`pairDeficit_sum_eq` 给 `pd = 2·max (c_W − c_P) (c_W − c_X)`；
弱相容 ⇒ `c_P·c_X = 0`（P-实现者与 X-实现者不能共存，否则三个配对同时被实现 = 冲突四点）；
`c_P, c_X ≥ 0` ⇒ `max (c_W − c_P) (c_W − c_X) = c_W`；
而 `s`（及 `s.swap`）实现 W-配对 ⇒ `c_W ≥ w s + [s.swap ∈ F]·w s.swap`。 -/
theorem isolationIndex_ge_two_mul_weight {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Split α)) (w : Split α → ℝ)
    (hF : WeaklyCompatible (↑F : Set (Split α))) (hw : ∀ u ∈ F, 0 < w u)
    {s : Split α} (hs : s ∈ F) :
    2 * (w s + (if s.swap ∈ F then w s.swap else 0))
      ≤ isolationIndex (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) s.sideA s.sideB := by
  rw [isolationIndex_eq_inf' (A := s.sideA) (B := s.sideB) _ (s.nonempty 0) (s.nonempty 1)]
  refine Finset.le_inf' (isoQuadruples_nonempty (s.nonempty 0) (s.nonempty 1)) _ ?_
  rintro ⟨⟨a, a'⟩, b, b'⟩ hq
  obtain ⟨ha, ha', hb, hb'⟩ := mem_isoQuadruples.mp hq
  rw [pairDeficit_sum_eq]
  set cW : ℝ := ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u with hcW
  set cP : ℝ := ∑ u ∈ F.filter (fun u => qPairP u a a' b b' = true), w u with hcP
  set cX : ℝ := ∑ u ∈ F.filter (fun u => qPairX u a a' b b' = true), w u with hcX
  have hWsep : s.Separates a a' b b' := Or.inl ⟨ha, ha', hb, hb'⟩
  have hWmem : s ∈ F.filter (fun u => qPairW u a a' b b' = true) := by
    rw [Finset.mem_filter]
    exact ⟨hs, (qPairW_eq_true_iff s a a' b b').mpr hWsep⟩
  have hcW0 : 0 ≤ cW := by
    rw [hcW]
    exact Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hcP0 : 0 ≤ cP := by
    rw [hcP]
    exact Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hcX0 : 0 ≤ cX := by
    rw [hcX]
    exact Finset.sum_nonneg fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)
  have hzero : cP = 0 ∨ cX = 0 := by
    by_contra hcon
    have hPne : cP ≠ 0 := fun h => hcon (Or.inl h)
    have hXne : cX ≠ 0 := fun h => hcon (Or.inr h)
    have hPpos : 0 < cP := lt_of_le_of_ne hcP0 (Ne.symm hPne)
    have hXpos : 0 < cX := lt_of_le_of_ne hcX0 (Ne.symm hXne)
    have hneP : (F.filter (fun u => qPairP u a a' b b' = true)).Nonempty := by
      rw [hcP] at hPpos
      exact Finset.nonempty_of_sum_ne_zero (ne_of_gt hPpos)
    have hneX : (F.filter (fun u => qPairX u a a' b b' = true)).Nonempty := by
      rw [hcX] at hXpos
      exact Finset.nonempty_of_sum_ne_zero (ne_of_gt hXpos)
    obtain ⟨u, hu⟩ := hneP
    obtain ⟨v, hv⟩ := hneX
    obtain ⟨huF, huP⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvF, hvX⟩ := Finset.mem_filter.mp hv
    exact hF ⟨a, a', b, b', ⟨s, hs, hWsep⟩,
      ⟨u, huF, (qPairP_eq_true_iff u a a' b b').mp huP⟩,
      ⟨v, hvF, (qPairX_eq_true_iff v a a' b b').mp hvX⟩⟩
  have hcWge : w s + (if s.swap ∈ F then w s.swap else 0) ≤ cW := by
    by_cases hsw : s.swap ∈ F
    · have hWmem2 : s.swap ∈ F.filter (fun u => qPairW u a a' b b' = true) := by
        rw [Finset.mem_filter]
        refine ⟨hsw, (qPairW_eq_true_iff s.swap a a' b b').mpr (Or.inr ?_)⟩
        exact ⟨by rw [swap_sideB]; exact ha, by rw [swap_sideB]; exact ha',
          by rw [swap_sideA]; exact hb, by rw [swap_sideA]; exact hb'⟩
      have hsub : ({s, s.swap} : Finset (Split α))
          ⊆ F.filter (fun u => qPairW u a a' b b' = true) := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hWmem
        · exact hWmem2
      have hnonneg : ∀ u ∈ F.filter (fun u => qPairW u a a' b b' = true),
          u ∉ ({s, s.swap} : Finset (Split α)) → 0 ≤ w u := by
        intro u hu _
        exact le_of_lt (hw u (Finset.mem_filter.mp hu).1)
      have hsum : (∑ u ∈ ({s, s.swap} : Finset (Split α)), w u) ≤ cW := by
        rw [hcW]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have hpair : (∑ u ∈ ({s, s.swap} : Finset (Split α)), w u) = w s + w s.swap := by
        rw [Finset.sum_insert (by
          simp only [Finset.mem_singleton]
          exact fun h => swap_ne s h.symm)]
        rw [Finset.sum_singleton]
      have hif : (if s.swap ∈ F then w s.swap else 0) = w s.swap := by simp [hsw]
      rw [hif]
      linarith
    · have hif : (if s.swap ∈ F then w s.swap else 0) = 0 := by simp [hsw]
      rw [hif]
      have hsingle : w s ≤ ∑ u ∈ F.filter (fun u => qPairW u a a' b b' = true), w u :=
        Finset.single_le_sum (fun u hu => le_of_lt (hw u (Finset.mem_filter.mp hu).1)) hWmem
      rw [hcW]
      linarith
  have hmin : max (cW - cP) (cW - cX) = cW := by
    rcases hzero with h | h
    · rw [h, sub_zero, max_eq_left (by linarith)]
    · rw [h, sub_zero, max_eq_right (by linarith)]
  rw [hmin]
  linarith

/-! ## 8.14 ★★★★ `weakCompatibilityRealization_gap_weights_v2` 的登记（量词修正 `s ∈ F`）

### 与 `§8.9` 的 `def weakCompatibilityRealization_gap_weights`（`:3358`）的关系

`§8.12` 已**机器证伪** `:3358`：它的第三个合取项量化
`∀ s, (s ∈ F ∨ s.swap ∈ F) → …`，当 `s ∉ F` 而 `s.swap ∈ F` 时前提成立，但 `w s` **无任何约束**
（假设只给 `∀ s ∈ F, 0 < w s`），而 `δ = Σ_{u∈F} w_u δ_u` 根本不含 `w s` 项
⇒ 右侧可任意大。本节的 `_v2` 把量词收紧为 `∀ s, s ∈ F → …`（**唯一**实质差别），
其余形态（`δ = Σ_{u∈F} w_u δ_u`、`2·(w s + [s.swap∈F]·w s.swap)`）不变。 -/

/-- **`Σ_{u∈F} w_u · δ_u`**（BdD Thm 3 的 `d = Σ_{S∈𝒮} λ_S δ_S`；`δ_S` 即
`SplitMetric`，`Phylo/SplitWeak.lean:394`）。

★ 这是**记号**而非新数学：库里 `splitMetricSum_*` 系列（`§10`）一直用其展开式
`fun x y => ∑ u ∈ F, w u * SplitMetric u x y`；登记成 `def` 只是让 `§8.14` 的结论**可命名**。 -/
noncomputable def sumMetric {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Split α)) (w : Split α → ℝ) : α → α → ℝ :=
  fun x y => ∑ u ∈ F, w u * SplitMetric u x y

/-- ★★★★★ **忠实形态 v2**（BdD Theorem 3 的两条断言一起；`§8.9` `:3358` 的**量词修正版**）。

**四要素**

* **旧形态（已证伪）**：`weakCompatibilityRealization_gap_weights`（本文件 `:3358`，`§8.9`）的
  第三合取项为 `∀ s, (s ∈ F ∨ s.swap ∈ F) → α_s = 2·(w s + [s.swap ∈ F]·w s.swap)`；
  `§8.12` 的 `not_weakCompatibilityRealization_gap_weights`（`:4528`）已**机器证伪**它
  （`Fin 4`、`F = {s₀}`、`w s₀ = 1`、`w s₀.swap = 5`：`∨` 前提在 `s₀.swap` 上成立，
  但右侧给 `12`，而 `α = 2`）。
* **新形态（本节登记）**：量词收紧为 `∀ s, s ∈ F → α_s = 2·(w s + [s.swap ∈ F]·w s.swap)`；
  `s ∉ F` 时**不再**声称任何等式（这时 `w s` 在 `δ` 里根本不出现）。
  第一合取项（`δ` 的 d-split 集 = `F` 编码的无向 split 集）与 `:3358` **相同**、未动；
  其形态照抄 **已有的** `splitMetricSum_isDSplit_iff`（`Phylo/SplitWeak.lean:1083`）的 `↔` 形状，
  **不**重复登记。
* **文献**：md `:1683-1699`（Theorem 3）逐字：
  > "THEOREM 3. The d-splits with respect to any symmetric function d on a set X are weakly
  >  compatible. Conversely, let 𝒮 be any collection of weakly compatible splits of X. For each
  >  S ∈ 𝒮 choose some λ_S > 0 and consider d := Σ_{S∈𝒮} λ_S δ_S. Then 𝒮 is the set of all
  >  d-splits, and moreover, the isolation index α_S = λ_S, for each S ∈ 𝒮."
  `α` 的定标见 md `:437-441`：`α_{A,B} = ½·min{max{d(a,b)+d(a',b'), d(a,b')+d(a',b),
  d(a,a')+d(b,b')} − d(a,a') − d(b,b')}`（**带 ½**）。本库 `SplitMetric` 取 `0/1`
  （`d = δ_S` 时 `α_S = ½·2 = 1`），而 `pairDeficit`（`Phylo/SplitWeak.lean:251`）与
  `isolationIndex`（本文件 `:942`）**省去 ½** ⇒ 库内 `isolationIndex = 2·α_BD`，
  这就是结论里因子 `2` 的来源；`s` 与 `s.swap` 是**同一**无向 split 的两个编码、
  `δ_s = δ_{s.swap}`（`splitMetric_swap`）⇒ 系数**相加**。
* **理由（为何必须收紧量词）**：`w` 只在 `F` 上受 `0 < w` 约束，`s ∉ F` 时 `w s` **完全自由**；
  `δ = Σ_{u∈F} w_u δ_u` 不含 `w s` 项 ⇒ 旧形态的等式在 `s ∉ F` 时可能任意失败
  （`§8.12` 的反例正是 `s = s₀.swap ∉ F`、`s.swap = s₀ ∈ F`）。

★ **状态**：本 `def` 是**待证形态**；`_holds` 见本节末尾（上界 = 唯一具名缺件 (B)）。
`_holds` 只在真证成时使用。 -/
def weakCompatibilityRealization_gap_weights_v2 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (w : Split α → ℝ),
    WeaklyCompatible (↑F : Set (Split α)) → (∀ s ∈ F, 0 < w s) →
      (∀ s : Split α, IsDSplit (sumMetric F w) s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s)
      ∧ ∀ s : Split α, s ∈ F → isolationIndex (sumMetric F w) s.sideA s.sideB
          = 2 * (w s + (if s.swap ∈ F then w s.swap else 0))


/-! ### 8.14.1 机器验证（小 `n`）的**可计算底座**

`Decidable` 合成不展开 `def`、也不穿透 `↥F : Set`，故 `decide`/`native_decide` 无法直接判定
`WeaklyCompatible (↑F)`。本小节登记 (B) 的可计算复刻（`abbrev` ⇒ `Decidable` 可展开）：

* `sepQ` —— `Separates`（`Phylo/SplitWeak.lean:153`）的复刻；
* `wcomp` —— `HasConflictingQuartet` 的 `Finset` 版，`wcomp_iff` 与库内形态对齐；
* `splitsFinset n` —— `Fin n` 的**全部** split（`#eval (splitsFinset 6).card = 62` ✓）；
* `cand s` —— 能 W-分离某个「`s.sideA` 两点、`s.sideB` 两点」四元组（**含退化**）的成员，
  去掉 `s` 与 `s.swap`。(B) 在 `s` 处只依赖 `F` 与它的交；
* `qAvoid F s` —— (B) 在 `s` 处的可计算形态。

★ **已量出的规模（`n = 6`、`|sideA| = 3`）**：`|cand s| = 30`，故 `2^30` 个子集仍需再用
一条机器事实（「弱相容族中至多两个候选成员」）压缩到 `|U'| ≤ 2`；`qAvoid` 对子族单调。
该整体检查**本轮未落地**（见本节尾部状态说明）。 -/

/-- `Separates` 的可计算复刻（`abbrev` ⇒ `Decidable` 合成可展开）。 -/
abbrev sepQ {n : ℕ} (u : Split (Fin n)) (a a' b b' : Fin n) : Prop :=
  (a ∈ u.sideA ∧ a' ∈ u.sideA ∧ b ∈ u.sideB ∧ b' ∈ u.sideB) ∨
    (a ∈ u.sideB ∧ a' ∈ u.sideB ∧ b ∈ u.sideA ∧ b' ∈ u.sideA)

/-- `HasConflictingQuartet` 的 **`Finset` 可计算复刻**。 -/
abbrev wcomp {n : ℕ} (F : Finset (Split (Fin n))) : Prop :=
  ¬ ∃ a b c e : Fin n,
    (∃ s ∈ F, sepQ s a b c e) ∧ (∃ t ∈ F, sepQ t a c b e) ∧ (∃ u ∈ F, sepQ u a e b c)

/-- ★ `wcomp` 与库内 `WeaklyCompatible (↑F)` **等价**（只差 `Set`/`Finset` 记法）。 -/
theorem wcomp_iff {n : ℕ} {F : Finset (Split (Fin n))} :
    wcomp F ↔ WeaklyCompatible (↑F : Set (Split (Fin n))) := by
  unfold wcomp WeaklyCompatible HasConflictingQuartet Separates sepQ
  simp only [Finset.mem_coe]

/-- **`Fin n` 的全部 `split`**（可计算）：`sideA` 遍历非空真子集。
`Finset.univ : Finset (Finset (Fin n))` 由 `Split.instFintypeFinset` 的显式 `powerset` 给出
（`Phylo/Split.lean:186`）。 -/
def splitsFinset (n : ℕ) : Finset (Split (Fin n)) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun A => A.Nonempty ∧ Aᶜ.Nonempty)).attach.image
    (fun p => ofSideA p.1 (Finset.mem_filter.mp p.2).2.1 (Finset.mem_filter.mp p.2).2.2)

/-- **候选集**：能 W-分离某个「`s.sideA` 两点、`s.sideB` 两点」（**含退化**）四元组的成员，
去掉 `s` 与 `s.swap`。(B) 在 `s` 处只依赖 `F` 与它的交。 -/
abbrev cand {n : ℕ} (s : Split (Fin n)) : Finset (Split (Fin n)) :=
  (splitsFinset n).filter (fun u =>
    u ≠ s ∧ u ≠ s.swap ∧
      ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB, sepQ u a a' b b')

/-- **(B) 在 `s` 处**（可计算复刻）：存在四元组，使 `F` 中除 `s`、`s.swap` 外任何成员都不 W-分离它。 -/
abbrev qAvoid {n : ℕ} (F : Finset (Split (Fin n))) (s : Split (Fin n)) : Prop :=
  ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
    ∀ u ∈ F, u ≠ s → u ≠ s.swap → ¬ sepQ u a a' b b'


/-- ★ **(B) 在 `s` 处**：存在 `a,a' ∈ s.sideA`、`b,b' ∈ s.sideB`，使 `F` 中除 `s`、`s.swap`
之外的**任何**成员都不 W-分离它（`Separates` 见 `Phylo/SplitWeak.lean:153`）。

★ **退化四元组允许**（`a = a'`、`b = b'`）：`isolationIndex` 的 `isoQuadruples` 也允许
（`Phylo/Stat/BunemanIndexBridge.lean:931`），故这里不为难。 -/
def QuartetAvoiding {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Split α)) (s : Split α) : Prop :=
  ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
    ∀ u ∈ F, u ≠ s → u ≠ s.swap → ¬ u.Separates a a' b b'

/-- ★★★★★ **唯一具名缺件 (B)**（逐字）：`F` 弱相容、`s ∈ F` ⇒ 存在 `a a' ∈ s.sideA`、
`b b' ∈ s.sideB`，使 `F ∖ {s, s.swap}` 中**不存在** `u` 满足 `u.Separates a a' b b'`。

**它是 `weakCompatibilityRealization_gap_weights_v2` 第二个合取项（上界）的唯一缺口**：
有了 (B)，取该四元组，`pairDeficit_sum_eq`（`:4665`）给
`pd = 2·max(c_W − c_P)(c_W − c_X) ≤ 2·c_W`（`c_P, c_X ≥ 0`），而 `c_W = w s + [s.swap∈F]·w s.swap`
（成员恰好是 `s`、`s.swap`）⇒ `α_s ≤ 2(w_s + [s.swap∈F]·w_swap)`；与已证下界
`isolationIndex_ge_two_mul_weight`（`:4706`）合并即得**等式**。

**证据状态**：Python 穷举（`n ≤ 6`、`|F| ≤ 7`）未找到反例；`n = 6`、`|sideA| = 3` 时为
`|Candidate(s)| = 30`，弱相容族中至多 **2** 个候选成员（`cand`，见 `§8.14.1`），
故检验规模为 `36 + 630` 个族；**Lean 机器验证尚未落地**（`native_decide` 的编译障碍
见 `§8.14.1` 尾部：`Decidable (∀ u ∈ F, …)` 走 `Fintype (Split _)`，而
`instFintypeKPartition` 是 `noncomputable`）。
**注**：(B) 的平凡情形 `|s.sideA| = 2` 或 `|s.sideB| = 2`（覆盖全部 `n ≤ 5`）也**尚未**形式化。 -/
-- ★ W29 台账口径：本 `def` 是 `weakCompatibilityRealization_gap_weights_v2` 的**内部子义务**，
--   **不是**独立缺口登记 ⇒ 名字里**不带** `gap/Gap`（否则 `gap_ledger.py` 会多登记一条真开放）。
def weakCompatibilityQuartetCore : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (s : Split α),
    s ∈ F → WeaklyCompatible (↑F : Set (Split α)) → QuartetAvoiding F s

/-! ### 8.14.3 (B) 在 `n = 6`、`|sideA| = |sideB| = 3` 处的机器验证：**可计算底座 ＋ 归约引理**

**技术前提**：`Decidable` 合成不展开 `def`、也不穿透 `↥F : Set`；且库内
`instFintypeKPartition`（`Phylo/Split.lean:194`）是 `noncomputable` ⇒ `native_decide` 直接判定
`WeaklyCompatible (↑F)` 会失败。本小节登记两件**可用**的东西：

1. **可计算枚举** `splitsFintype n := ⟨splitsFinset n, mem_splitsFinset n⟩`
   （配合 `attribute [local instance]` 可让 `native_decide` 编译）；
2. **归约引理**：`qAvoidND` 只依赖 `F ∩ candND s`（`not_sepQ_of_not_mem_candND`）且对子族**单调**
   （`qAvoidND_mono`）⇒ 只要弱相容族中 `candND` 成员至多两个（`candidateTripleCore`，`§8.14.4`），
   (B) 就退化成「单候选 ＋ 双候选」两个有限情形。

★ **本批实测**：单候选 `native_decide` 在**独立测试文件**里 **3m25s 通过**；但在完整文件里
（连同双候选 `30 × 29` 与「至多两个候选」的三元枚举）**未在 20 分钟预算内收敛**
⇒ **三段机器检查本批均未入库**；`candND`/`qAvoidND` 只作为下一轮的现成底座。
Python 证据：`n = 6,7` 穷举、`n = 8` 随机 10 万次，均 **0 反例**。 -/
/-- 每个 `Split (Fin n)` 都在 `splitsFinset n` 中（`sideA` 非空、补非空）。 -/
theorem mem_splitsFinset (n : ℕ) (s : Split (Fin n)) : s ∈ splitsFinset n := by
  unfold splitsFinset
  refine Finset.mem_image.mpr ⟨⟨s.sideA, ?_⟩, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, s.nonempty 0, by rw [← sideB_eq_compl]; exact s.nonempty 1⟩
  · exact Finset.mem_attach _ _
  · exact eq_of_sideA_eq (by rw [ofSideA_sideA])

set_option warn.classDefReducibility false in
/-- **可计算的 `Fintype (Split (Fin n))`**（替代库内 `noncomputable` 的 `instFintypeKPartition`）。 -/
def splitsFintype (n : ℕ) : Fintype (Split (Fin n)) :=
  ⟨splitsFinset n, mem_splitsFinset n⟩

/-- **非退化候选集**：能 W-分离某个「`a ≠ a'`、`b ≠ b'`」四元组的成员（去 `s`、`s.swap`）。

★ 与 `cand` 的差别：排除**退化**四元组 ⇒ `n = 6`、`|sideA| = 3` 时是 **30** 个（`cand` 是 60）。
代价是见证必须非退化 —— 即 `qAvoidND`，它**强于** `qAvoid`（非退化见证也是 (B) 允许的见证）。 -/
abbrev candND {n : ℕ} (s : Split (Fin n)) : Finset (Split (Fin n)) :=
  (splitsFinset n).filter (fun u =>
    u ≠ s ∧ u ≠ s.swap ∧
      ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
        a ≠ a' ∧ b ≠ b' ∧ sepQ u a a' b b')

/-- **(B) 的非退化见证形态**（强于 `qAvoid`；同样足以给上界）。 -/
abbrev qAvoidND {n : ℕ} (F : Finset (Split (Fin n))) (s : Split (Fin n)) : Prop :=
  ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
    a ≠ a' ∧ b ≠ b' ∧ ∀ u ∈ F, u ≠ s → u ≠ s.swap → ¬ sepQ u a a' b b'

/-- ★ **候选集外不分离**（`qAvoidND` 只需检验 `candND` 成员的依据）。 -/
theorem not_sepQ_of_not_mem_candND {n : ℕ} {F : Finset (Split (Fin n))} {s u : Split (Fin n)}
    (hF : F ⊆ splitsFinset n) (huF : u ∈ F) (hu : u ∉ candND s)
    (hne : u ≠ s) (hne' : u ≠ s.swap)
    {a a' b b' : Fin n} (ha : a ∈ s.sideA) (ha' : a' ∈ s.sideA)
    (hb : b ∈ s.sideB) (hb' : b' ∈ s.sideB) (hnd1 : a ≠ a') (hnd2 : b ≠ b') :
    ¬ sepQ u a a' b b' := by
  intro hsep
  exact hu (Finset.mem_filter.mpr
    ⟨hF huF, hne, hne', a, ha, a', ha', b, hb, b', hb', hnd1, hnd2, hsep⟩)

/-- ★ **(B) 对子族单调**（`qAvoidND` 版）：族越大越难满足。 -/
theorem qAvoidND_mono {n : ℕ} {G F : Finset (Split (Fin n))} {s : Split (Fin n)}
    (hGF : G ⊆ F) : qAvoidND F s → qAvoidND G s := by
  rintro ⟨a, ha, a', ha', b, hb, b', hb', h1, h2, h⟩
  exact ⟨a, ha, a', ha', b, hb, b', hb', h1, h2, fun u huG hne hne' => h u (hGF huG) hne hne'⟩

/-- ★ **弱相容对子族单调**。 -/
theorem wcomp_mono {n : ℕ} {F G : Finset (Split (Fin n))} (hFG : F ⊆ G) :
    wcomp G → wcomp F := by
  intro hG hc
  obtain ⟨a, b, c, e, ⟨s, hs, Rs⟩, ⟨t, ht, Rt⟩, ⟨u, hu, Ru⟩⟩ := hc
  exact hG ⟨a, b, c, e, ⟨s, hFG hs, Rs⟩, ⟨t, hFG ht, Rt⟩, ⟨u, hFG hu, Ru⟩⟩


/-! ### 8.14.4 `_v2` 第一合取项的两个方向：**核查结论**

第一合取项是 `∀ s, IsDSplit (sumMetric F w) s.sideA s.sideB ↔ ∃ t ∈ F, t = s ∨ t.swap = s`。

* **正方向（成员是 d-split）—— 库内已有，不需要再证**：
  `Split.isDSplit_splitMetricSum_of_mem_or_swap_of_weaklyCompatible`（`Phylo/SplitWeak.lean:975`）
  逐字给出 `t ∈ F ∨ t.swap ∈ F ⇒ IsDSplit (fun x y => ∑ u ∈ F, w u * SplitMetric u x y) t.sideA t.sideB`
  （`t ∈ F` 的核心是 `…_of_mem_of_weaklyCompatible`，`:910`，**只要弱相容 ＋ 正权重**）。
  ⇒ 与 `∃ t ∈ F, t = s ∨ t.swap = s` 的 `→` 半边只差 `sideA/sideB` 的等式改写。
* **反方向（非成员不是 d-split）—— 已有版本只是「两两相容」**：
  `Split.notIsDSplit_of_splitMetricSum_gap_holds`（本文件 `:3288`）证的是
  `notIsDSplit_of_splitMetricSum_gap`（`Phylo/SplitWeak.lean:688`），前提是
  `∀ s ∈ F, ∀ t ∈ F, s.Compatible t`（**两两相容**），**不是** `WeaklyCompatible`。
  ★ **弱相容版不在库内，且不短**：按 `splitMetricSum_isDSplit_iff`（`SplitWeak.lean:1083`），
  `¬IsDSplit δ t.sideA t.sideB` 需要**一个**四元组使 `min c_P c_X ≤ c_W`；弱相容只给
  「`c_P > 0` 与 `c_X > 0` 不同时成立」⇒ `min c_P c_X = 0` ⇒ 归结为 **`c_W = 0`**，即
  「`t` 的某个两侧各取两点四元组上，`F` 中**没有**成员实现 W-配对」。
  这与 (B) 属**同一族**的组合命题（(B) 允许 `s`、`s.swap` 分离；这里 `t ∉ F ± swap` ⇒ 一个都不允许）。
  ⇒ **不是顺手可证的短件，本轮只登记结论、不动它。** -/

/-- **`u` 能 W-分离某个非退化四元组**（`s` 的两侧各取两点；「候选」的一般形态）。 -/
def SeparatesSomeQuartet {α : Type*} [Fintype α] [DecidableEq α]
    (u s : Split α) : Prop :=
  ∃ a ∈ s.sideA, ∃ a' ∈ s.sideA, ∃ b ∈ s.sideB, ∃ b' ∈ s.sideB,
    a ≠ a' ∧ b ≠ b' ∧ u.Separates a a' b b'

/-- ★★★★ **结构事实（候选成员至多两个）—— 具名陈述**（`_v2` 的内部子义务，非独立缺口）。

`F` 弱相容、`s ∈ F` ⇒ `F` 中**能** W-分离某个非退化四元组（两侧各取两点）的成员
**至多两个**。

**为何它是关键**：`QuartetAvoiding`（`:4910`）只依赖这些候选成员（`not_sepQ_of_not_mem_candND`），
且对子族单调 ⇒ 该事实一旦成立，(B) 就退化成**单候选/双候选的有限构造**，
不需要一般组合论证（§8.14.3 的单候选机器检查已通过；双候选未在预算内落地）。

**证据**：Python 穷举 `n = 6,7,8,10`（含 `n = 6, |sideA| = 3` 的全族）都只见 ≤ 2；
`n = 6, |sideA| = 3` 的 Lean 机器检查**未在 20 分钟预算内收敛**。
**一般 `n` 未证。** -/
def candidateTripleCore : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (F : Finset (Split α)) (s : Split α)
      (u1 u2 u3 : Split α),
    s ∈ F → u1 ∈ F → u2 ∈ F → u3 ∈ F →
      u1 ≠ u2 → u1 ≠ u3 → u2 ≠ u3 →
        WeaklyCompatible (↑F : Set (Split α)) →
          ¬ (SeparatesSomeQuartet u1 s ∧ SeparatesSomeQuartet u2 s ∧
              SeparatesSomeQuartet u3 s)

end Split

