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

/-! ## 8.2 ⬜ **BdD Theorem 2 的忠实形态**（W25-b 登记；未证） -/

/-- ⬜ **`canonicalSplitDecomposition_gap` 的忠实形态（W25-b 登记；未证）**：

`δ` 是 `X` 上的**度量**（`M(X)`：对称、`x = x ⟹ 0`、非负、三角不等式 —— `:673-684`、
`:816`、`:825` 的框架），且**残差 `δ₀` 仍是度量**、并且 split-prime（隔离指数处处 `0`）。

★ 与 `……_correct_shape` 的**唯一差别**就是「`δ` 与 `δ₀` 仍在 `M(X)` 里」—— 但这一条
**恰好挡住** `§8.1` 的「全体 split 大系数下压」构造（那里 `δ₀` 非对角为负），
故本形态**不是空转**；它等价于 `:1651-1655` Thm 2 的**存在性**一半
（本 `Prop` 未要求 `c s = α_s` 与唯一性，故弱于 Thm 2 全文）。缺的具名器材见报告「卡点」。 -/
def canonicalSplitDecomposition_gap_faithful : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (δ : α → α → ℝ), (∀ x y, δ x y = δ y x) →
    (∀ x, δ x x = 0) → (∀ x y, 0 ≤ δ x y) → (∀ x y z, δ x z ≤ δ x y + δ y z) →
    ∃ (F : Finset (Split α)) (c : Split α → ℝ) (δ₀ : α → α → ℝ),
      (∀ s ∈ F, 0 < c s) ∧ SplitPrimeFaithful δ₀ ∧ (∀ x, δ₀ x x = 0) ∧
        (∀ x y, 0 ≤ δ₀ x y) ∧
          ∀ x y, δ x y = δ₀ x y + ∑ s ∈ F, c s * SplitMetric s x y

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

end Split

