/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.CladogramBuild

/-!
# `Phylo.TwoParentTrees` —— B-5 的**分类定理**（W21 任务 C / **C3**）

## 0. 目标

`Phylo/SupertreeLimits.lean` 的 `two_parent_trees_gap_correct_shape`（`:716`）第 ② 条
（原文 Steel–Böcker–Dress 2000, `:113-116` 的 **"there are precisely two trees that are
parent trees for this collection of trees"**）：

> 每个展示 `prof` 的 `Cladogram (Fin 6)`，其（非平凡）split 系统**恰是** `T₁` 的或 `T₂` 的。

库内已把它**归约到有限核心**（`SBD.two_parent_trees_core`，`:1139`），
且**桥已证**（`SBD.two_parent_trees_classification_of_core`，`:1157`）。
W12a 的记录说：两条 `decide` 路线（`Finset (Fin 6)` 直写 / `Fin 64` 位掩码）**都走不通**
（`Decidable` 综合不出；或 64³ = 262144 例下 `maxRecDepth` / heartbeats 超限），
建议走「**手写原文 Figure 1 的情形分析**（估 100–200 行）」。

## 1. 本文件的路线（W21）

**把「手写情形分析」换成「先归约、再 `decide`」** —— 关键观察：

* 每个 quartet 的**展示条件**把见证 split 的 `sideA` 压缩到**至多 4 个候选**（去重后）；
* 于是三元组只有 `4 × 4 × 4 = 64` 例（而非 64³），**且每例都是 1–3 量词的小 `decide`**；
* 更关键：对**相容的三元组**，与三者都相容的非平凡 split **恰为** `famP1`（或 `famP2`）的 6 条
  —— 这使第 ② 条的 **`↔`（双向）** 都可做。

★ 所有有限断言一律写成**闭命题**（`∀` 写在陈述内）后 `by decide`，**零人工情形分析**。
其真值已由穷举脚本独立核过（三个全 PASS）：
`scripts/msc/w21_c3_core_recon.py` · `w21_c3_core_form.py` · `w21_c3_core_exact.py`。

## 2. 有限引理一览（全部 `by decide`）

| 引理 | 量词数 | 内容 |
|---|---|---|
| `cand1` / `cand2` / `cand3` | 1（`64`） | 展示 `qᵢ` 的非平凡 `A`，其**无序类**必在 4 元候选表内 |
| `triple_class` | 3（`4³ = 64`） | 两两相容的候选三元组**必**是 `P₁` 的三条或 `P₂` 的三条（无序口径） |
| `core_P1` / `core_P2` | 1（`64`） | 与 `P₁`（或 `P₂`）三条都相容的非平凡 `B` **必**落在 `P1A`（或 `P2A`）内 |
| `P1A_determined` / `P2A_determined` | 4（`4³·64`） | **反向**：`P1A` 的值**必**是三条见证的 `sideA` 之一（或其补） |

## 3. 成果

* `two_parent_trees_core_holds` —— ★★★★ **有限核心已成定理**（原 `def Prop` 缺口闭合）；
* `two_parent_trees_classification_holds` —— ★★★★ **树层分类定理**（由库内已证的桥得到）。
-/

universe u

namespace TwoParent

/-! ## 4. 候选表与 `sideA` 像 -/

/-- `SidesCompatible`（`Split.lean:40` 的 `def`，半可约）在 `Fin 6` 上的**可判定实例**。

⚠️ 没有它，`decide` 会在「（含 `SidesCompatible` 的）闭命题」上**综合不出** `Decidable`
（实例搜索不展开半可约 `def`）—— 这正是 W12a 记录「`Decidable` 综合不出」的真因之一。 -/
instance instDecidableSidesCompatible (A B : Finset (Fin 6)) : Decidable (SidesCompatible A B) := by
  unfold SidesCompatible
  infer_instance

/-- `q1 = {{0,1},{3,4}}` 的候选（`{0,1}` 朝向）：`A ⊇ {0,1}`、`Aᶜ ⊇ {3,4}`。 -/
noncomputable def c1 (i : Fin 4) : Finset (Fin 6) :=
  if i = 0 then {0, 1} else if i = 1 then {0, 1, 2} else if i = 2 then {0, 1, 5} else {0, 1, 2, 5}

/-- `q2 = {{2,3},{0,5}}` 的候选（`{2,3}` 朝向）。 -/
noncomputable def c2 (i : Fin 4) : Finset (Fin 6) :=
  if i = 0 then {2, 3} else if i = 1 then {1, 2, 3} else if i = 2 then {2, 3, 4} else {1, 2, 3, 4}

/-- `q3 = {{4,5},{1,2}}` 的候选（`{4,5}` 朝向）。 -/
noncomputable def c3 (i : Fin 4) : Finset (Fin 6) :=
  if i = 0 then {4, 5} else if i = 1 then {0, 4, 5} else if i = 2 then {3, 4, 5} else {0, 3, 4, 5}

/-- 一个 split 族的 `sideA` 之像。 -/
noncomputable def sideAOf (F : Finset (Split (Fin 6))) : Finset (Finset (Fin 6)) :=
  F.image fun s => s.sideA

/-- `famP1` 的 `sideA` 集（6 个：`±{0,1}`、`±{2,3}`、`±{4,5}`）。 -/
noncomputable def P1A : Finset (Finset (Fin 6)) := sideAOf SBD.famP1

/-- `famP2` 的 `sideA` 集（6 个：`±{3,4}`、`±{0,5}`、`±{1,2}`）。 -/
noncomputable def P2A : Finset (Finset (Fin 6)) := sideAOf SBD.famP2

/-- `famP1 ∪ famP2` 的 `sideA` 集（12 个）。 -/
noncomputable def FAMA : Finset (Finset (Fin 6)) := sideAOf (SBD.famP1 ∪ SBD.famP2)

/-! ## 5. ★ 有限引理（全部 `decide`；`∀` 一律写在陈述内以保持目标闭合）

### 5.1 候选归约（`L1`） -/

/-- ★ **`L1`（`q1`）**：若 `A` 展示 `q1` 且非平凡，则 `A` 的无序类在 `c1` 表内。 -/
theorem cand1 : ∀ A : Finset (Fin 6), (∃ p ∈ SBD.q1, p ⊆ A) →
    (∃ p' ∈ SBD.q1, p' ⊆ Aᶜ) → 2 ≤ A.card → 2 ≤ Aᶜ.card →
    ∃ i : Fin 4, A = c1 i ∨ A = (c1 i)ᶜ := by
  decide

/-- ★ **`L1`（`q2`）**。 -/
theorem cand2 : ∀ A : Finset (Fin 6), (∃ p ∈ SBD.q2, p ⊆ A) →
    (∃ p' ∈ SBD.q2, p' ⊆ Aᶜ) → 2 ≤ A.card → 2 ≤ Aᶜ.card →
    ∃ i : Fin 4, A = c2 i ∨ A = (c2 i)ᶜ := by
  decide

/-- ★ **`L1`（`q3`）**。 -/
theorem cand3 : ∀ A : Finset (Fin 6), (∃ p ∈ SBD.q3, p ⊆ A) →
    (∃ p' ∈ SBD.q3, p' ⊆ Aᶜ) → 2 ≤ A.card → 2 ≤ Aᶜ.card →
    ∃ i : Fin 4, A = c3 i ∨ A = (c3 i)ᶜ := by
  decide

/-! ### 5.2 三元组分类（`L2`） -/

/-- ★★ **`L2`**：两两相容的候选三元组**必**是 `P₁` 的三条（`{0,1}`/`{2,3}`/`{4,5}` 的无序类）
或 `P₂` 的三条（`{3,4}`/`{0,5}`/`{1,2}` 的无序类）。 -/
theorem triple_class : ∀ i j k : Fin 4, SidesCompatible (c1 i) (c2 j) →
    SidesCompatible (c1 i) (c3 k) → SidesCompatible (c2 j) (c3 k) →
    ((c1 i = {0, 1} ∨ c1 i = ({0, 1} : Finset (Fin 6))ᶜ) ∧
      (c2 j = {2, 3} ∨ c2 j = ({2, 3} : Finset (Fin 6))ᶜ) ∧
      (c3 k = {4, 5} ∨ c3 k = ({4, 5} : Finset (Fin 6))ᶜ)) ∨
    ((c1 i = {3, 4} ∨ c1 i = ({3, 4} : Finset (Fin 6))ᶜ) ∧
      (c2 j = {0, 5} ∨ c2 j = ({0, 5} : Finset (Fin 6))ᶜ) ∧
      (c3 k = {1, 2} ∨ c3 k = ({1, 2} : Finset (Fin 6))ᶜ)) := by
  decide

/-! ### 5.3 强化的有限核心（`L3`）：**恰是** `famP1` / `famP2` -/

/-- ★★★ **`L3`（`P₁` 情形）**：与 `{0,1}`、`{2,3}`、`{4,5}` 都相容的非平凡 `B`，
其 `sideA` **必**落在 `famP1` 的 `sideA` 集内。 -/
theorem core_P1 : ∀ B : Finset (Fin 6), 2 ≤ B.card → 2 ≤ Bᶜ.card →
    SidesCompatible B ({0, 1} : Finset (Fin 6)) →
    SidesCompatible B ({2, 3} : Finset (Fin 6)) →
    SidesCompatible B ({4, 5} : Finset (Fin 6)) → B ∈ P1A := by
  decide

/-- ★★★ **`L3`（`P₂` 情形）**：与 `{3,4}`、`{0,5}`、`{1,2}` 都相容的非平凡 `B`，
其 `sideA` **必**落在 `famP2` 的 `sideA` 集内。 -/
theorem core_P2 : ∀ B : Finset (Fin 6), 2 ≤ B.card → 2 ≤ Bᶜ.card →
    SidesCompatible B ({3, 4} : Finset (Fin 6)) →
    SidesCompatible B ({0, 5} : Finset (Fin 6)) →
    SidesCompatible B ({1, 2} : Finset (Fin 6)) → B ∈ P2A := by
  decide

/-- ★ **弱形态**：与 `P₁` 三条都相容的非平凡 `B` 落在 `famP1 ∪ famP2` 的 `sideA` 集内。 -/
theorem core_weak : ∀ B : Finset (Fin 6), 2 ≤ B.card → 2 ≤ Bᶜ.card →
    SidesCompatible B ({0, 1} : Finset (Fin 6)) →
    SidesCompatible B ({2, 3} : Finset (Fin 6)) →
    SidesCompatible B ({4, 5} : Finset (Fin 6)) → B ∈ FAMA := by
  decide

/-! ### 5.4 反向确定（`L4`）

⚠️ `L4`（`P1A_determined` / `P2A_determined`）服务于第 ② 条的 **`↔`** 方向，
本文件**改用**「`famP1` 的 6 个成员逐个落到见证上」的路线（`mem_famP1_cases`，见 §9），
故此处不再需要 `L4` 的 `decide` 形态。 -/

/-! ## 6. 从 `sideA` 回到 `Split`（`Finset` 像的拆解） -/

theorem mem_famP1_of_sideA {s : Split (Fin 6)} (h : s.sideA ∈ P1A) : s ∈ SBD.famP1 := by
  obtain ⟨t, ht, htA⟩ := Finset.mem_image.mp h
  exact (Split.ext_sideA htA) ▸ ht

theorem mem_famP2_of_sideA {s : Split (Fin 6)} (h : s.sideA ∈ P2A) : s ∈ SBD.famP2 := by
  obtain ⟨t, ht, htA⟩ := Finset.mem_image.mp h
  exact (Split.ext_sideA htA) ▸ ht

theorem mem_fam_or_of_sideA {s : Split (Fin 6)} (h : s.sideA ∈ FAMA) :
    s ∈ SBD.famP1 ∨ s ∈ SBD.famP2 := by
  obtain ⟨t, ht, htA⟩ := Finset.mem_image.mp h
  rw [Finset.mem_union] at ht
  exact ht.imp (fun h1 => (Split.ext_sideA htA) ▸ h1) (fun h2 => (Split.ext_sideA htA) ▸ h2)

/-! ## 7. 相容性的补不变性（把候选归约搬回原 `sideA`） -/

/-- ★ 把「`A` 的无序类等于 `A'`」翻译成相容性：`SidesCompatible A B ↔ SidesCompatible A' B'`。 -/
theorem sidesCompatible_normalize {A B A' B' : Finset (Fin 6)}
    (hA : A = A' ∨ A = A'ᶜ) (hB : B = B' ∨ B = B'ᶜ) (h : SidesCompatible A B) :
    SidesCompatible A' B' := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · rwa [hA, hB] at h
  · rw [hA, hB] at h
    exact (sidesCompatible_compl_right (A := A') (B := B')).mp h
  · rw [hA, hB] at h
    exact (sidesCompatible_compl_left (A := A') (B := B')).mp h
  · rw [hA, hB] at h
    exact (sidesCompatible_compl_left (A := A') (B := B')).mp
      ((sidesCompatible_compl_right (A := A'ᶜ) (B := B')).mp h)

/-! ## 8. ★★★★ 有限核心已成定理 -/

/-- 把「非平凡」从 `sideB` 形态搬到 `sideAᶜ` 形态。 -/
theorem nontrivial_sideA {s : Split (Fin 6)} (h : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) :
    2 ≤ s.sideA.card ∧ 2 ≤ s.sideAᶜ.card := by
  obtain ⟨h1, h2⟩ := h
  rw [Split.sideB_eq_compl] at h2
  exact ⟨h1, h2⟩

/-- ★★★★ **有限核心（`SBD.two_parent_trees_core`）已成定理** —— 原 `def Prop` 缺口闭合。 -/
theorem two_parent_trees_core_holds : SBD.two_parent_trees_core := by
  intro F hnt hcomp hdisp s hsF
  -- ① 三条见证
  obtain ⟨s1, hs1F, h1a, h1b⟩ := hdisp SBD.q1 (by decide)
  obtain ⟨s2, hs2F, h2a, h2b⟩ := hdisp SBD.q2 (by decide)
  obtain ⟨s3, hs3F, h3a, h3b⟩ := hdisp SBD.q3 (by decide)
  -- ② 把「展示」写成 `sideA` / `sideAᶜ` 形态
  have hd1b : ∃ p' ∈ SBD.q1, p' ⊆ s1.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h1b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  have hd2b : ∃ p' ∈ SBD.q2, p' ⊆ s2.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h2b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  have hd3b : ∃ p' ∈ SBD.q3, p' ⊆ s3.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h3b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  -- ③ 三条见证都非平凡
  have hn1 := nontrivial_sideA (hnt s1 hs1F)
  have hn2 := nontrivial_sideA (hnt s2 hs2F)
  have hn3 := nontrivial_sideA (hnt s3 hs3F)
  -- ④ 候选归约
  obtain ⟨i, hi⟩ := cand1 s1.sideA h1a hd1b hn1.1 hn1.2
  obtain ⟨j, hj⟩ := cand2 s2.sideA h2a hd2b hn2.1 hn2.2
  obtain ⟨k, hk⟩ := cand3 s3.sideA h3a hd3b hn3.1 hn3.2
  -- ⑤ 三元组分类（先把三者的候选索引搬到 `c1 i`/`c2 j`/`c3 k` 上）
  have hij : SidesCompatible (c1 i) (c2 j) :=
    sidesCompatible_normalize hi hj (Split.compatible_iff_sides.mp (hcomp s1 hs1F s2 hs2F))
  have hik : SidesCompatible (c1 i) (c3 k) :=
    sidesCompatible_normalize hi hk (Split.compatible_iff_sides.mp (hcomp s1 hs1F s3 hs3F))
  have hjk : SidesCompatible (c2 j) (c3 k) :=
    sidesCompatible_normalize hj hk (Split.compatible_iff_sides.mp (hcomp s2 hs2F s3 hs3F))
  -- ⑥ 待判的 `s` 非平凡，且与三条见证都相容
  have hsn := nontrivial_sideA (hnt s hsF)
  have hs1 : SidesCompatible s.sideA (c1 i) :=
    sidesCompatible_normalize (Or.inl rfl) hi
      (Split.compatible_iff_sides.mp (hcomp s hsF s1 hs1F))
  have hs2 : SidesCompatible s.sideA (c2 j) :=
    sidesCompatible_normalize (Or.inl rfl) hj
      (Split.compatible_iff_sides.mp (hcomp s hsF s2 hs2F))
  have hs3 : SidesCompatible s.sideA (c3 k) :=
    sidesCompatible_normalize (Or.inl rfl) hk
      (Split.compatible_iff_sides.mp (hcomp s hsF s3 hs3F))
  rcases triple_class i j k hij hik hjk with ⟨hp1, hp2, hp3⟩ | ⟨hp1, hp2, hp3⟩
  · -- `P₁` 情形
    refine Or.inl (mem_famP1_of_sideA (core_P1 s.sideA hsn.1 hsn.2 ?_ ?_ ?_))
    · exact sidesCompatible_normalize (Or.inl rfl) hp1 hs1
    · exact sidesCompatible_normalize (Or.inl rfl) hp2 hs2
    · exact sidesCompatible_normalize (Or.inl rfl) hp3 hs3
  · -- `P₂` 情形
    refine Or.inr (mem_famP2_of_sideA (core_P2 s.sideA hsn.1 hsn.2 ?_ ?_ ?_))
    · exact sidesCompatible_normalize (Or.inl rfl) hp1 hs1
    · exact sidesCompatible_normalize (Or.inl rfl) hp2 hs2
    · exact sidesCompatible_normalize (Or.inl rfl) hp3 hs3

/-- ★★★★ **树层分类定理**（`SBD.two_parent_trees_classification`）—— 由库内已证的桥得到。 -/
theorem two_parent_trees_classification_holds : SBD.two_parent_trees_classification :=
  SBD.two_parent_trees_classification_of_core two_parent_trees_core_holds

/-! ## 9. 第 ② 条的 **`↔`** 形态（`two_parent_trees_gap_correct_shape` 的内容）

第 8 节只给出 `⊆`（`T` 的 split 都在 `famP1 ∪ famP2` 内）。本节补**反向**：
若见证三元组属于 `P₁` 类，则 `famP1 ⊆ T.splits`，故**两侧相等** ⇒ `↔`。

路线（避开 W12a 记录的两条死路）：

* `isSplitOf_of_sameClass` —— 「`s` 与某条见证 split 的无序类相同」⟹ `s` 也被 `T` 展示；
* `isSplitOf_of_mem_famP1` —— 把 `famP1` 的 **6 个成员逐个**落到三条见证上
  （`sP1a` ↔ 类 `{0,1}`、`sP1c` ↔ 类 `{2,3}`、`sP1b` ↔ 类 `{4,5}`，各含换向）。 -/

/-- ★★ **同类 ⟹ 同样被展示**：若 `s` 与 `s1` 的 `sideA` 落在同一个「无序类」`{A, Aᶜ}` 里，
则 `T.IsSplitOf s1 ⟹ T.IsSplitOf s`（两条情形分别走「相等」与「取 `swap`」）。 -/
theorem isSplitOf_of_sameClass {T : Cladogram.{0, 0} (Fin 6)} {s s1 : Split (Fin 6)}
    {A : Finset (Fin 6)} (hs1 : T.IsSplitOf s1) (h1 : s1.sideA = A ∨ s1.sideA = Aᶜ)
    (h2 : s.sideA = A ∨ s.sideA = Aᶜ) : T.IsSplitOf s := by
  have key : s.sideA = s1.sideA ∨ s.sideA = s1.swap.sideA := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (by rw [h2, h1])
    · exact Or.inr (by rw [h2, Split.swap_sideA, Split.sideB_eq_compl, ← h1])
    · exact Or.inr (by rw [h2, Split.swap_sideA, Split.sideB_eq_compl, h1, compl_compl])
    · exact Or.inl (by rw [h2, h1])
  rcases key with key | key
  · exact (Split.ext_sideA key) ▸ hs1
  · exact (Split.ext_sideA key) ▸ (T.isSplitOf_swap hs1)

/-- ★★ **`famP1` 的成员都被 `T` 展示**（给定三条见证及其无序类）。
`famP1` 的 6 个成员与见证的对应：`sP1a`↔`{0,1}`、`sP1c`↔`{2,3}`、`sP1b`↔`{4,5}`（各含换向）。 -/
theorem isSplitOf_of_mem_famP1 {T : Cladogram.{0, 0} (Fin 6)} {s s1 s2 s3 : Split (Fin 6)}
    (hs : s ∈ SBD.famP1) (h1 : T.IsSplitOf s1) (h2 : T.IsSplitOf s2) (h3 : T.IsSplitOf s3)
    (hd1 : s1.sideA = {0, 1} ∨ s1.sideA = ({0, 1} : Finset (Fin 6))ᶜ)
    (hd2 : s2.sideA = {2, 3} ∨ s2.sideA = ({2, 3} : Finset (Fin 6))ᶜ)
    (hd3 : s3.sideA = {4, 5} ∨ s3.sideA = ({4, 5} : Finset (Fin 6))ᶜ) :
    T.IsSplitOf s := by
  rw [SBD.famP1, SBD.baseP1] at hs
  rcases Finset.mem_union.mp hs with hs | hs
  · -- `baseP1 = {sP1a, sP1b, sP1c}`
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact isSplitOf_of_sameClass h1 hd1 (Or.inr (by decide))
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact isSplitOf_of_sameClass h3 hd3 (Or.inl (by decide))
      · rcases Finset.mem_singleton.mp hs with rfl
        exact isSplitOf_of_sameClass h2 hd2 (Or.inl (by decide))
  · -- `baseP1.image swap`：三个换向成员
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact isSplitOf_of_sameClass h1 hd1 (Or.inl (by decide))
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact isSplitOf_of_sameClass h3 hd3 (Or.inr (by decide))
      · rcases Finset.mem_singleton.mp ht with rfl
        exact isSplitOf_of_sameClass h2 hd2 (Or.inr (by decide))

/-- ★★ **`famP2` 的成员都被 `T` 展示**：`sP2a`↔`{3,4}`、`sP2b`↔`{1,2}`、`sP2c`↔`{0,5}`。 -/
theorem isSplitOf_of_mem_famP2 {T : Cladogram.{0, 0} (Fin 6)} {s s1 s2 s3 : Split (Fin 6)}
    (hs : s ∈ SBD.famP2) (h1 : T.IsSplitOf s1) (h2 : T.IsSplitOf s2) (h3 : T.IsSplitOf s3)
    (hd1 : s1.sideA = {3, 4} ∨ s1.sideA = ({3, 4} : Finset (Fin 6))ᶜ)
    (hd2 : s2.sideA = {0, 5} ∨ s2.sideA = ({0, 5} : Finset (Fin 6))ᶜ)
    (hd3 : s3.sideA = {1, 2} ∨ s3.sideA = ({1, 2} : Finset (Fin 6))ᶜ) :
    T.IsSplitOf s := by
  rw [SBD.famP2, SBD.baseP2] at hs
  rcases Finset.mem_union.mp hs with hs | hs
  · rcases Finset.mem_insert.mp hs with rfl | hs
    · exact isSplitOf_of_sameClass h1 hd1 (Or.inl (by decide))
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact isSplitOf_of_sameClass h3 hd3 (Or.inl (by decide))
      · rcases Finset.mem_singleton.mp hs with rfl
        exact isSplitOf_of_sameClass h2 hd2 (Or.inr (by decide))
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact isSplitOf_of_sameClass h1 hd1 (Or.inr (by decide))
    · rcases Finset.mem_insert.mp ht with rfl | ht
      · exact isSplitOf_of_sameClass h3 hd3 (Or.inr (by decide))
      · rcases Finset.mem_singleton.mp ht with rfl
        exact isSplitOf_of_sameClass h2 hd2 (Or.inl (by decide))

/-- ★★ **把候选索引与原 `sideA` 合起来**：`s ∈ c`（或 `cᶜ`）且 `c ∈ {A, Aᶜ}` ⟹ `s ∈ {A, Aᶜ}`。 -/
theorem combine {s : Split (Fin 6)} {C A : Finset (Fin 6)}
    (h1 : s.sideA = C ∨ s.sideA = Cᶜ) (h2 : C = A ∨ C = Aᶜ) :
    s.sideA = A ∨ s.sideA = Aᶜ := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (by rw [h1, h2])
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inl (by rw [h1, h2, compl_compl])

theorem mem_splits_of {T : Cladogram.{0, 0} (Fin 6)} {s : Split (Fin 6)}
    (h : T.IsSplitOf s) : s ∈ T.splits := by
  change T.IsSplitOf s
  exact h

/-- `q1` 的成员都是 2 元集。 -/
theorem card_of_mem_q1 {p : Finset (Fin 6)} (h : p ∈ SBD.q1) : p.card = 2 := by
  simp only [SBD.q1, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> decide

/-- `q2` 的成员都是 2 元集。 -/
theorem card_of_mem_q2 {p : Finset (Fin 6)} (h : p ∈ SBD.q2) : p.card = 2 := by
  simp only [SBD.q2, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> decide

/-- `q3` 的成员都是 2 元集。 -/
theorem card_of_mem_q3 {p : Finset (Fin 6)} (h : p ∈ SBD.q3) : p.card = 2 := by
  simp only [SBD.q3, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> decide

/-- ★★★ **见证二分**：展示 `prof` 的树 `T`，或给出 `P₁` 类的三条见证，或给出 `P₂` 类的三条。 -/
theorem witness_dichotomy (T : Cladogram.{0, 0} (Fin 6))
    (hT : ∀ q ∈ SBD.prof, SBD.DisplaysQP T q) :
    (∃ s1 s2 s3 : Split (Fin 6),
      T.IsSplitOf s1 ∧ T.IsSplitOf s2 ∧ T.IsSplitOf s3 ∧
      (s1.sideA = {0, 1} ∨ s1.sideA = ({0, 1} : Finset (Fin 6))ᶜ) ∧
      (s2.sideA = {2, 3} ∨ s2.sideA = ({2, 3} : Finset (Fin 6))ᶜ) ∧
      (s3.sideA = {4, 5} ∨ s3.sideA = ({4, 5} : Finset (Fin 6))ᶜ)) ∨
    (∃ s1 s2 s3 : Split (Fin 6),
      T.IsSplitOf s1 ∧ T.IsSplitOf s2 ∧ T.IsSplitOf s3 ∧
      (s1.sideA = {3, 4} ∨ s1.sideA = ({3, 4} : Finset (Fin 6))ᶜ) ∧
      (s2.sideA = {0, 5} ∨ s2.sideA = ({0, 5} : Finset (Fin 6))ᶜ) ∧
      (s3.sideA = {1, 2} ∨ s3.sideA = ({1, 2} : Finset (Fin 6))ᶜ)) := by
  obtain ⟨s1, hs1T, h1a, h1b⟩ := hT SBD.q1 (by decide)
  obtain ⟨s2, hs2T, h2a, h2b⟩ := hT SBD.q2 (by decide)
  obtain ⟨s3, hs3T, h3a, h3b⟩ := hT SBD.q3 (by decide)
  have hd1b : ∃ p' ∈ SBD.q1, p' ⊆ s1.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h1b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  have hd2b : ∃ p' ∈ SBD.q2, p' ⊆ s2.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h2b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  have hd3b : ∃ p' ∈ SBD.q3, p' ⊆ s3.sideAᶜ := by
    obtain ⟨p', hp'q, hp'sub⟩ := h3b
    rw [Split.sideB_eq_compl] at hp'sub
    exact ⟨p', hp'q, hp'sub⟩
  -- 三条见证的非平凡性：quartet 的每个配对都是 2 元集 ⟹ 见证 split 两侧各 ≥ 2
  have hn1 : 2 ≤ s1.sideA.card ∧ 2 ≤ s1.sideAᶜ.card := by
    refine ⟨?_, ?_⟩
    · exact le_trans (le_of_eq (card_of_mem_q1 h1a.choose_spec.1).symm)
        (Finset.card_le_card h1a.choose_spec.2)
    · have hp : (h1b.choose : Finset (Fin 6)) ⊆ s1.sideAᶜ := by
        rw [← Split.sideB_eq_compl]
        exact h1b.choose_spec.2
      exact le_trans (le_of_eq (card_of_mem_q1 h1b.choose_spec.1).symm)
        (Finset.card_le_card hp)
  have hn2 : 2 ≤ s2.sideA.card ∧ 2 ≤ s2.sideAᶜ.card := by
    refine ⟨?_, ?_⟩
    · exact le_trans (le_of_eq (card_of_mem_q2 h2a.choose_spec.1).symm)
        (Finset.card_le_card h2a.choose_spec.2)
    · have hp : (h2b.choose : Finset (Fin 6)) ⊆ s2.sideAᶜ := by
        rw [← Split.sideB_eq_compl]
        exact h2b.choose_spec.2
      exact le_trans (le_of_eq (card_of_mem_q2 h2b.choose_spec.1).symm)
        (Finset.card_le_card hp)
  have hn3 : 2 ≤ s3.sideA.card ∧ 2 ≤ s3.sideAᶜ.card := by
    refine ⟨?_, ?_⟩
    · exact le_trans (le_of_eq (card_of_mem_q3 h3a.choose_spec.1).symm)
        (Finset.card_le_card h3a.choose_spec.2)
    · have hp : (h3b.choose : Finset (Fin 6)) ⊆ s3.sideAᶜ := by
        rw [← Split.sideB_eq_compl]
        exact h3b.choose_spec.2
      exact le_trans (le_of_eq (card_of_mem_q3 h3b.choose_spec.1).symm)
        (Finset.card_le_card hp)
  obtain ⟨i, hi⟩ := cand1 s1.sideA h1a hd1b hn1.1 hn1.2
  obtain ⟨j, hj⟩ := cand2 s2.sideA h2a hd2b hn2.1 hn2.2
  obtain ⟨k, hk⟩ := cand3 s3.sideA h3a hd3b hn3.1 hn3.2
  have hc12 : Split.Compatible s1 s2 :=
    pairwiseCompatible T s1 (mem_splits_of hs1T) s2 (mem_splits_of hs2T)
  have hc13 : Split.Compatible s1 s3 :=
    pairwiseCompatible T s1 (mem_splits_of hs1T) s3 (mem_splits_of hs3T)
  have hc23 : Split.Compatible s2 s3 :=
    pairwiseCompatible T s2 (mem_splits_of hs2T) s3 (mem_splits_of hs3T)
  have hij : SidesCompatible (c1 i) (c2 j) :=
    sidesCompatible_normalize hi hj (Split.compatible_iff_sides.mp hc12)
  have hik : SidesCompatible (c1 i) (c3 k) :=
    sidesCompatible_normalize hi hk (Split.compatible_iff_sides.mp hc13)
  have hjk : SidesCompatible (c2 j) (c3 k) :=
    sidesCompatible_normalize hj hk (Split.compatible_iff_sides.mp hc23)
  rcases triple_class i j k hij hik hjk with ⟨hp1, hp2, hp3⟩ | ⟨hp1, hp2, hp3⟩
  · exact Or.inl ⟨s1, s2, s3, hs1T, hs2T, hs3T, combine hi hp1, combine hj hp2, combine hk hp3⟩
  · exact Or.inr ⟨s1, s2, s3, hs1T, hs2T, hs3T, combine hi hp1, combine hj hp2, combine hk hp3⟩

/-- ★★★★ **第 ② 条的 `↔` 形态**：每个展示 `prof` 的 `T`，其 split 系统**恰是**
`treeP1` 的或 `treeP2` 的。 -/
theorem tree_splits_classified (T : Cladogram.{0, 0} (Fin 6))
    (hT : ∀ q ∈ SBD.prof, SBD.DisplaysQP T q) :
    (∀ s : Split (Fin 6), Cladogram.treeP1.IsSplitOf s ↔ T.IsSplitOf s) ∨
    (∀ s : Split (Fin 6), Cladogram.treeP2.IsSplitOf s ↔ T.IsSplitOf s) := by
  have hnts : ∀ {s : Split (Fin 6)}, T.IsSplitOf s →
      ¬ ((∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ)) →
      2 ≤ s.sideA.card ∧ 2 ≤ s.sideAᶜ.card := by
    intro s _ htriv
    have hA1 : 1 ≤ s.sideA.card := Finset.card_pos.mpr (s.nonempty 0)
    have hAc : s.sideAᶜ.Nonempty := by
      rw [← Split.sideB_eq_compl]
      exact s.nonempty 1
    have hAc1 : 1 ≤ s.sideAᶜ.card := Finset.card_pos.mpr hAc
    constructor
    · rcases Nat.lt_or_ge s.sideA.card 2 with h2 | h2
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : s.sideA.card = 1)
        exact absurd (Or.inl ⟨x, hx⟩) htriv
      · exact h2
    · rcases Nat.lt_or_ge s.sideAᶜ.card 2 with h2 | h2
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : s.sideAᶜ.card = 1)
        exact absurd (Or.inr ⟨x, by rw [← hx, compl_compl]⟩) htriv
      · exact h2
  have p1case :
      (∃ s1 s2 s3 : Split (Fin 6),
        T.IsSplitOf s1 ∧ T.IsSplitOf s2 ∧ T.IsSplitOf s3 ∧
        (s1.sideA = {0, 1} ∨ s1.sideA = ({0, 1} : Finset (Fin 6))ᶜ) ∧
        (s2.sideA = {2, 3} ∨ s2.sideA = ({2, 3} : Finset (Fin 6))ᶜ) ∧
        (s3.sideA = {4, 5} ∨ s3.sideA = ({4, 5} : Finset (Fin 6))ᶜ)) →
      (∀ s : Split (Fin 6), Cladogram.treeP1.IsSplitOf s ↔ T.IsSplitOf s) := by
    rintro ⟨s1, s2, s3, h1T, h2T, h3T, hd1, hd2, hd3⟩ s
    refine ⟨?_, ?_⟩
    · intro hs
      rw [Cladogram.treeP1_isSplitOf] at hs
      rcases hs with hs | hs | hs
      · exact isSplitOf_of_mem_famP1 hs h1T h2T h3T hd1 hd2 hd3
      · obtain ⟨x, hx⟩ := hs
        exact Cladogram.isSplitOf_of_sideA_singleton T hx
      · obtain ⟨x, hx⟩ := hs
        exact Cladogram.isSplitOf_of_sideB_singleton T
          (by rw [Split.sideB_eq_compl, hx, compl_compl])
    · intro hs
      by_cases htriv : (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ)
      · rw [Cladogram.treeP1_isSplitOf]
        exact Or.inr htriv
      · have hsn := hnts hs htriv
        have k1 : SidesCompatible s.sideA ({0, 1} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd1
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s1 (mem_splits_of h1T)))
        have k2 : SidesCompatible s.sideA ({2, 3} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd2
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s2 (mem_splits_of h2T)))
        have k3 : SidesCompatible s.sideA ({4, 5} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd3
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s3 (mem_splits_of h3T)))
        rw [Cladogram.treeP1_isSplitOf]
        exact Or.inl (mem_famP1_of_sideA (core_P1 s.sideA hsn.1 hsn.2 k1 k2 k3))
  have p2case :
      (∃ s1 s2 s3 : Split (Fin 6),
        T.IsSplitOf s1 ∧ T.IsSplitOf s2 ∧ T.IsSplitOf s3 ∧
        (s1.sideA = {3, 4} ∨ s1.sideA = ({3, 4} : Finset (Fin 6))ᶜ) ∧
        (s2.sideA = {0, 5} ∨ s2.sideA = ({0, 5} : Finset (Fin 6))ᶜ) ∧
        (s3.sideA = {1, 2} ∨ s3.sideA = ({1, 2} : Finset (Fin 6))ᶜ)) →
      (∀ s : Split (Fin 6), Cladogram.treeP2.IsSplitOf s ↔ T.IsSplitOf s) := by
    rintro ⟨s1, s2, s3, h1T, h2T, h3T, hd1, hd2, hd3⟩ s
    refine ⟨?_, ?_⟩
    · intro hs
      rw [Cladogram.treeP2_isSplitOf] at hs
      rcases hs with hs | hs | hs
      · exact isSplitOf_of_mem_famP2 hs h1T h2T h3T hd1 hd2 hd3
      · obtain ⟨x, hx⟩ := hs
        exact Cladogram.isSplitOf_of_sideA_singleton T hx
      · obtain ⟨x, hx⟩ := hs
        exact Cladogram.isSplitOf_of_sideB_singleton T
          (by rw [Split.sideB_eq_compl, hx, compl_compl])
    · intro hs
      by_cases htriv : (∃ x : Fin 6, s.sideA = {x}) ∨ (∃ x : Fin 6, s.sideA = {x}ᶜ)
      · rw [Cladogram.treeP2_isSplitOf]
        exact Or.inr htriv
      · have hsn := hnts hs htriv
        have k1 : SidesCompatible s.sideA ({3, 4} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd1
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s1 (mem_splits_of h1T)))
        have k2 : SidesCompatible s.sideA ({0, 5} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd2
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s2 (mem_splits_of h2T)))
        have k3 : SidesCompatible s.sideA ({1, 2} : Finset (Fin 6)) :=
          sidesCompatible_normalize (Or.inl rfl) hd3
            (Split.compatible_iff_sides.mp
              (pairwiseCompatible T s (mem_splits_of hs) s3 (mem_splits_of h3T)))
        rw [Cladogram.treeP2_isSplitOf]
        exact Or.inl (mem_famP2_of_sideA (core_P2 s.sideA hsn.1 hsn.2 k1 k2 k3))
  rcases witness_dichotomy T hT with h | h
  · exact Or.inl (p1case h)
  · exact Or.inr (p2case h)

/-! ## 10. ★★★★ 端到端：`two_parent_trees_gap_correct_shape` 收官 -/

/-- ★★ `treeP1` 展示 `prof` 的三条输入 quartet。 -/
theorem treeP1_displays_prof : ∀ q ∈ SBD.prof, SBD.DisplaysQP Cladogram.treeP1 q := by
  intro q hq
  simp only [SBD.prof, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨SBD.sP1a, by rw [Cladogram.treeP1_isSplitOf]; decide,
      ⟨{3, 4}, by decide, by decide⟩, ⟨{0, 1}, by decide, by decide⟩⟩
  · exact ⟨SBD.sP1c, by rw [Cladogram.treeP1_isSplitOf]; decide,
      ⟨{2, 3}, by decide, by decide⟩, ⟨{0, 5}, by decide, by decide⟩⟩
  · exact ⟨SBD.sP1b, by rw [Cladogram.treeP1_isSplitOf]; decide,
      ⟨{4, 5}, by decide, by decide⟩, ⟨{1, 2}, by decide, by decide⟩⟩

/-- ★★ `treeP2` 展示 `prof` 的三条输入 quartet。 -/
theorem treeP2_displays_prof : ∀ q ∈ SBD.prof, SBD.DisplaysQP Cladogram.treeP2 q := by
  intro q hq
  simp only [SBD.prof, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨SBD.sP2a, by rw [Cladogram.treeP2_isSplitOf]; decide,
      ⟨{3, 4}, by decide, by decide⟩, ⟨{0, 1}, by decide, by decide⟩⟩
  · exact ⟨SBD.sP2c, by rw [Cladogram.treeP2_isSplitOf]; decide,
      ⟨{2, 3}, by decide, by decide⟩, ⟨{0, 5}, by decide, by decide⟩⟩
  · exact ⟨SBD.sP2b, by rw [Cladogram.treeP2_isSplitOf]; decide,
      ⟨{1, 2}, by decide, by decide⟩, ⟨{4, 5}, by decide, by decide⟩⟩

/-- ★★★★ **B-5 缺口改写形态（`SBD.two_parent_trees_gap_correct_shape`）收官**。

`T₁ := Cladogram.treeP1`、`T₂ := Cladogram.treeP2`（W21 任务 A/C1 新造的**可命名**精确树）：

* ① 两者都展示 `prof`（`treeP1_displays_prof` / `treeP2_displays_prof`）；
* ② `σ` 交换两者的 split 系统（`famP2 = famP1.image (relabel σ)` ＋ 平凡 split 的 `relabel` 不变性）；
* ③ ★ **分类定理**（"precisely two"）：`tree_splits_classified`；
* ④ 非退化：`sP2a` 在 `treeP2` 而不在 `treeP1`。 -/
theorem two_parent_trees_gap_correct_shape_holds : SBD.two_parent_trees_gap_correct_shape :=
  ⟨Cladogram.treeP1, Cladogram.treeP2, treeP1_displays_prof, treeP2_displays_prof,
    (by
      intro s
      rw [Cladogram.treeP2_isSplitOf s, Cladogram.treeP1_isSplitOf (Split.relabel SBD.sig s),
        SBD.mem_famP2_iff_relabel_mem_famP1 s]
      exact or_congr Iff.rfl (SBD.trivial_relabel_iff SBD.sig s)),
    (fun T hT => tree_splits_classified T hT),
    ⟨SBD.sP2a, by rw [Cladogram.treeP2_isSplitOf]; exact Or.inl (by decide),
      by rw [Cladogram.treeP1_isSplitOf]; decide⟩⟩

/-- ★★★★ **B-5 原登记形态（`SBD.two_parent_trees_gap`）** —— 由改写形态经库内已证的桥得到。 -/
theorem two_parent_trees_gap_holds : SBD.two_parent_trees_gap :=
  SBD.two_parent_trees_gap_of_correct_shape two_parent_trees_gap_correct_shape_holds

end TwoParent
