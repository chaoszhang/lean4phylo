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

## 交付（零未证占位符、零新公理）

1. `Split.IsDSplitStrong` —— BdD 隔离指数 `α_{A,B} > 0` 的等价形式（「两配对都为正」）；
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

/-- **强 d-split**（≡ BdD 隔离指数 `α_{A,B} > 0`，BdD p. 51）：对**每个**四元组
`a, a' ∈ A`、`b, b' ∈ B`，**两个配对都**严格为正。

⚠️ 与 `Split.IsDSplit` 的 `max` 形式**不同**：后者只要「两者之一」为正。 -/
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

/-- ⬜ **正确形态（W12j 登记；未证）**：`Σ` 弱相容 ⟹ 存在**对称零对角** `δ`，使 `Σ` 恰是
其**正隔离指数**的 split 集，且**隔离指数就是给定权重 `w`**、非成员的隔离指数为 `0`。 -/
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

end Split
