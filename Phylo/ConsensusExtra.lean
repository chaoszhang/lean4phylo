/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Supertree
import Phylo.Algorithm.RF

/-!
# `Phylo.ConsensusExtra` —— 共识族（W11a）：Day 的 `M_l` 家族 / 半严格共识 / 严格共识的树空间性质

本文件实现 **W11a 共识族** 的第 (1)、(3) 项（第 (2) 项 Adams 共识见 `Phylo.AdamsConsensus`，
它是**有根/簇**范式，与本文件的 split 范式不同）。

## (1) C1：Day (1985) 的 `M_l` 家族与**半严格共识**

文献：`references/md/Day1985_OptimalAlgorithmsComparingTrees.md`。
Day 把「严格性」参数化为 **`M_l`**（md 第 238–247 行）：

> let `l` be an integer such that `k/2 < l ≤ k` … `M_l(T₁,…,T_k)'` contains a cluster
> **if and only if it is in at least `l` of `T₁',…,T_k'`**. If `l = k`, `M_l` is strict
> consensus `C`; while if `l = ⌊k/2⌋+1`, `M_l` is the majority rule consensus tree method
> of Margush and McMorris (1981).

本文件把该族形式化为 `lSplits l T`（`l ≤ supportCount T s` 的 split），并证明

* ★★ `lSplits_compatible`：`2l > k` 时 `M_l` 的 split **两两相容**
  （鸽笼原理：两个基数 `≥ l` 的支持集在 `k < 2l` 时必有交，交处取一棵树，
  该树的 split 系统两两相容 —— `pairwiseCompatible`）；
* ★★★ `lSplits_consensus_exists`：**`M_l` 共识树存在**，且其 split 集**恰为** `lSplits l T`
  （定向 `IsSplitOf` 的 `↔`，与 `Phylo.Supertree.strict_consensus_exists` 同款收口）。

**半严格共识** = Day 的 `M_2`（**至少两棵**树含它 ⟺ 不是「只出现一次」），
落地为 `nonstrictSplits T := lSplits 2 T`。

### ⚠️ 边界（★B，**实测反例**；详见交付报告与 `scripts/msc/w11a_checks.py`）

1. **`ι` 空**：`lSplits l T = ∅`，而 `strictSplits T = univ`（含不相容对）——
   故全部结论都需要 `[Nonempty ι]`（与 `strict_compatible` 同款边界）。
2. **`|ι| = 1`**：`nonstrictSplits T = ∅`，而 `strictSplits T = treeSplits (T ())` 通常非空，
   故「严格 ⟹ 半严格」（`strictSplits_subset_nonstrictSplits`）**必须**带 `2 ≤ |ι|`。
3. **`|ι| ≥ 4` 时「至少两棵」不保证相容**：两个基数 `≥ 2` 的支持集在 `|ι| ≥ 4` 时可以**不交**
   （如 `{1,2}` 与 `{3,4}`）。**具体反例**（`|ι| = 4`，叶集 `Fin 5`）：
   `T 0 = T 1` 的 split 系统 `{{0,1}|rest, {2,3}|rest}`，`T 2 = T 3` 的为
   `{{0,2}|rest, {1,4}|rest}`；则 `{0,1}`、`{0,2}` 支持度都是 `2 ≥ 2`，
   但 `{0,1}` 与 `{0,2}` **不相容**（四个交全非空）。
   故 `nonstrict_compatible` / `nonstrict_consensus_exists` 都带 **`|ι| ≤ 3`**
   （此时 `2·2 = 4 > |ι|`，落回鸽笼原理）。
   等价地：`M_l` 的相容性判据 `2l > k` 在 `(l,k) = (2,4)` 时**失效**，
   这正是 Day 限定 `k/2 < l`（即对 `M_2` 要求 `k < 4`）的原因。

## (3) F9：严格共识的**树空间性质**

* ★★★ `strictSplits_eq_iInter_splits`：**严格共识 = 各棵树 split 集之交**
  （`Set` 版 `⋂ i, (T i).splits`）；
* ★★★ `subset_strictSplits_iff`：该交的**泛性质**（`S ⊆ strictSplits ↔ ∀ i, S ⊆ treeSplits`），
  即 `strictSplits` 是各 `treeSplits (T i)` 的**最大下界**；
* ★★★ `strictSplits_subset_treeSplits`：严格共识的 split **含于每棵输入树**；
* ★★ `rfDistance_strictSplits_treeSplits`：
  `rfDistance (strictSplits T) (treeSplits (T i)) = |T i| - |strictSplits T|`
  —— 严格共识与第 `i` 棵树的 RF 距离**恰好是被丢弃的 split 数**
  （Day 1985 的 `D(T₁,T₂) = |T₁' Δ T₂'|`，md 第 340–348 行；本库 `Phylo/Algorithm/RF.lean`）。

RF 距离自身的度量性（对称、`= 0 ⟺ 相等`、三角不等式）已在 `Phylo/Algorithm/RF.lean`
证过，本文件**不重复**。
-/

open Phylo

universe u

attribute [local instance] Classical.propDecidable

/-! ## 0. split 的 `sideA` 决定性与换向引理 -/

namespace Split

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **split 由 `sideA` 唯一决定**（`sideA` 与 `sideB` 互为补，见 `sideB_eq_sdiff`）。

有了它，「两个 split 相等」只需比对一侧。 -/
theorem ext_sideA {s t : Split α} (h : s.sideA = t.sideA) : s = t := by
  rw [KPartition.eq_iff_parts]
  funext i
  fin_cases i
  · simpa [sideA] using h
  · show s.sideB = t.sideB
    rw [sideB_eq_sdiff s, sideB_eq_sdiff t, h]

/-- `s.sideA` 恰是 `t` 的**另一侧** ⟹ `s = t.swap`。 -/
theorem eq_swap_of_sideA_eq_sideB {s t : Split α} (h : s.sideA = t.sideB) : s = t.swap :=
  ext_sideA (by rw [h, swap_sideA])

end Split

variable {X : Type u} [Fintype X] [DecidableEq X]

/-! ## 1. 树的有限 split 集 -/

/-- 一棵树的 **split 集（有限版）**。

`Cladogram.splits`（`Phylo/Split.lean:623`）是 `Set` 版；本定义是它的 `Finset` 版，
供 RF 距离（`Split.rfDistance : Finset (Split α) → …`）与基数运算使用。 -/
noncomputable def treeSplits (T : Cladogram X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s : Split X => T.IsSplitOf s

theorem mem_treeSplits {T : Cladogram X} {s : Split X} :
    s ∈ treeSplits T ↔ T.IsSplitOf s := by
  classical
  simp [treeSplits]

/-- `treeSplits` 与 `Cladogram.splits` 一致（集合层面）。 -/
theorem coe_treeSplits_eq_splits (T : Cladogram X) :
    ((treeSplits T : Finset (Split X)) : Set (Split X)) = T.splits := by
  ext s
  rw [Finset.mem_coe, mem_treeSplits]
  rfl

/-! ## 2. Day (1985) 的 `M_l` 家族 -/

/-- `s` 在树族 `T` 中的**支持集**：含 `s` 的树之集。 -/
noncomputable def supportSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Cladogram X) (s : Split X) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (T i).IsSplitOf s

theorem mem_supportSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ι → Cladogram X} {s : Split X} {i : ι} :
    i ∈ supportSet T s ↔ (T i).IsSplitOf s := by
  classical
  simp [supportSet]

/-- 若**每棵树**都展示 `s`，则支持集是全体（支持度 = 树数）。 -/
theorem supportSet_eq_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ι → Cladogram X} {s : Split X} (h : ∀ i, (T i).IsSplitOf s) :
    supportSet T s = (Finset.univ : Finset ι) := by
  classical
  simp only [supportSet]
  exact Finset.filter_true_of_mem fun i _ => h i

/-- 支持集的基数就是库内 `Phylo.supportCount`（`Phylo/Consensus.lean:34`）。 -/
theorem card_supportSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Cladogram X) (s : Split X) :
    (supportSet T s).card = supportCount T s := by
  classical
  simp only [supportSet, supportCount]

/-- ★★ **`M_l`**（Day 1985, md 第 238–247 行）：出现在**至少 `l` 棵**输入树中的 split。

* `l = |ι|`：**严格共识**（`strictSplits`）；
* `l = ⌊|ι|/2⌋+1`：**多数共识**（`majoritySplits`，Margush–McMorris 1981）；
* `l = 2`：本文件的**半严格**取法（`nonstrictSplits`，「不是只出现一次」）。 -/
noncomputable def lSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ℕ) (T : ι → Cladogram X) : Finset (Split X) := by
  classical
  exact Finset.univ.filter fun s : Split X => l ≤ (supportSet T s).card

theorem mem_lSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : ℕ} {T : ι → Cladogram X} {s : Split X} :
    s ∈ lSplits l T ↔ l ≤ (supportSet T s).card := by
  classical
  simp [lSplits]

/-- `mem_lSplits` 的 `supportCount` 版本（与库内多数共识的措辞对齐）。 -/
theorem mem_lSplits' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : ℕ} {T : ι → Cladogram X} {s : Split X} :
    s ∈ lSplits l T ↔ l ≤ supportCount T s := by
  rw [mem_lSplits, card_supportSet]

/-- **`M_l` 对 `l` 单调递减**：门槛越高，保留的 split 越少。 -/
theorem lSplits_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l l' : ℕ} (h : l ≤ l') (T : ι → Cladogram X) : lSplits l' T ⊆ lSplits l T :=
  fun _ hs => mem_lSplits.mpr (le_trans h (mem_lSplits.mp hs))

/-- ★★ **严格 ⟹ `M_l`**（`l ≤ |ι|` 时）。 -/
theorem strictSplits_subset_lSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : ℕ} (hl : l ≤ Fintype.card ι) (T : ι → Cladogram X) :
    strictSplits T ⊆ lSplits l T := by
  intro s hs
  rw [mem_lSplits]
  have h1 : supportSet T s = (Finset.univ : Finset ι) := by
    simp only [supportSet, Finset.filter_true_of_mem fun i _ => (mem_strictSplits.mp hs) i]
  rw [h1, Finset.card_univ]
  exact hl

/-- ★★ **`M_l` 的 split 两两相容**（鸽笼原理；`2l > |ι|`）。

`s`、`t` 的支持集基数都 `≥ l`，而 `|ι| < 2l` 迫使两者**相交**；
交处取一棵树 `T i`，`s`、`t` 都是它的 split，由 `pairwiseCompatible` 相容。

（对比 `Phylo/Consensus.lean:50` 的 `majority_compatible`：那是 `l = ⌊k/2⌋+1` 的特例。） -/
theorem lSplits_compatible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ℕ) (T : ι → Cladogram X) (hk : Fintype.card ι < 2 * l)
    {s t : Split X} (hs : s ∈ lSplits l T) (ht : t ∈ lSplits l T) :
    Split.Compatible s t := by
  classical
  by_contra hc
  have hdisj : Disjoint (supportSet T s) (supportSet T t) := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨i, hi⟩
    rw [Finset.mem_inter, mem_supportSet, mem_supportSet] at hi
    exact hc (pairwiseCompatible (T i) s hi.1 t hi.2)
  have hle : (supportSet T s ∪ supportSet T t).card ≤ Fintype.card ι := by
    have h := Finset.card_le_card (Finset.subset_univ (supportSet T s ∪ supportSet T t))
    rwa [Finset.card_univ] at h
  rw [Finset.card_union_of_disjoint hdisj] at hle
  have hs' := mem_lSplits.mp hs
  have ht' := mem_lSplits.mp ht
  omega

/-! ## 3. `M_l` 共识树存在（★★★）

先把 `Phylo.Supertree.exists_cladogram_of_compatible` 的**边侧刻画**升级为
「该树的 split 集**恰是** 族 ∪ 平凡 split」的 `↔`，再对 `M_l` 的非平凡部分施用。 -/

set_option maxHeartbeats 800000 in
/-- ★★★ **相容（非平凡）split 族 ⟹ 存在树，其 split 集恰为「族 ∪ 平凡 split」**。

这是 `Phylo.Supertree.exists_cladogram_of_compatible` 的 **`↔` 加强版**：
该构造给出的树 `M`，其**全部** split 被完全刻画 —— 非平凡的那些恰是族成员
（或其换向，由 `hswap`「族对 `swap` 封闭」拉回族内），其余是平凡 split
（一侧为单点），而平凡 split 被任何树的叶边定向展示。 -/
theorem isSplitOf_iff_mem_or_trivial (fam : Finset (Split X)) (ρ : X)
    (hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t)
    (hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (hswap : ∀ s ∈ fam, s.swap ∈ fam)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s : Split X,
      M.IsSplitOf s ↔ s ∈ fam ∨ (∃ x : X, s.sideA = {x}) ∨ (∃ x : X, s.sideA = {x}ᶜ) := by
  classical
  obtain ⟨M, hM, hcases⟩ := exists_cladogram_of_compatible fam ρ hcomp hnt h3
  refine ⟨M, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rcases hcases s hs with ⟨B, hB, hBne, hBA⟩ | ⟨x, hx⟩
    · -- `M` 的边侧是某个族成员（或补）的规范簇 `B`，故 `s.sideA` 是那棵 split 的某一侧
      have hBF : B ∈ fam.image (fun s : Split X => s.cluster ρ) :=
        ((mem_normFinset.mp hB).resolve_left hBne).1
      obtain ⟨t, ht, htB⟩ := Finset.mem_image.mp hBF
      have hside : s.sideA = t.sideA ∨ s.sideA = t.sideB := by
        have hcl := t.cluster_eq_sideA_or_compl ρ
        rcases hBA with hBA | hBA
        · rcases hcl with hcl | hcl
          · exact Or.inl (by rw [hBA, ← htB, hcl])
          · exact Or.inr (by rw [hBA, ← htB, hcl, ← Split.sideB_eq_compl])
        · rcases hcl with hcl | hcl
          · exact Or.inr (by rw [hBA, ← htB, hcl, Split.sideB_eq_compl])
          · exact Or.inl (by rw [hBA, ← htB, hcl, compl_compl])
      rcases hside with hside | hside
      · exact Or.inl (Split.ext_sideA hside ▸ ht)
      · exact Or.inl (Split.eq_swap_of_sideA_eq_sideB hside ▸ hswap t ht)
    · rcases hx with hx | hx
      · exact Or.inr (Or.inl ⟨x, hx⟩)
      · exact Or.inr (Or.inr ⟨x, hx⟩)
  · rcases hs with hs | (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact hM s hs
    · exact Cladogram.isSplitOf_of_sideA_singleton M (s := s) (x := x) hx
    · exact Cladogram.isSplitOf_of_sideB_singleton M (s := s) (x := x)
        (by rw [Split.sideB_eq_compl, hx, compl_compl])

set_option maxHeartbeats 800000 in
/-- ★★★ **`M_l` 共识树存在**（Day 1985；Aho–Buneman 收口）。

对任一树族 `T : ι → Cladogram X`（`ι` 非空、`2l > |ι|`、`l ≤ |ι|`、`3 ≤ |X|`），
存在 cladogram `M` 使

    `M.IsSplitOf s ↔ s ∈ lSplits l T`（即 `s` 出现在至少 `l` 棵树中）。

即：**共识树的 split 集恰好是 `M_l` 的 split 集**（定向 `IsSplitOf` 的 `↔`，
与 `strict_consensus_exists`、`majority_consensus_exists` 同一模式）。

**证明**：取 `M_l` 中**非平凡**的部分 `fam`（平凡 split 由任何树的叶边展示，
见 `mem_strictSplits_of_sideA_singleton`），`lSplits_compatible` 给两两相容，
`isSplitOf_iff_mem_or_trivial` 建树并给出 `↔` 刻画。 -/
theorem lSplits_consensus_exists {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (l : ℕ) (T : ι → Cladogram X) (hl : l ≤ Fintype.card ι) (hk : Fintype.card ι < 2 * l)
    (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s : Split X, M.IsSplitOf s ↔ s ∈ lSplits l T := by
  classical
  obtain ⟨ρ⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card X by omega)
  set fam : Finset (Split X) :=
    (lSplits l T).filter fun s : Split X => 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card with hfam
  have hcomp : ∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t := fun s hs t ht =>
    lSplits_compatible l T hk (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1
  have hnt : ∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := fun s hs =>
    (Finset.mem_filter.mp hs).2
  have hswap : ∀ s ∈ fam, s.swap ∈ fam := by
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_lSplits] at hs ⊢
      -- 支持集对 `swap` 不变（一棵树展示 `s` ⟺ 它展示 `s.swap`）
      have hset : supportSet T s.swap = supportSet T s := by
        ext i
        rw [mem_supportSet, mem_supportSet]
        constructor
        · intro h
          have h' := (T i).isSplitOf_swap h
          rwa [Split.swap_swap] at h'
        · intro h
          exact (T i).isSplitOf_swap h
      rw [hset]
      exact hs.1
    · rw [Split.swap_sideA]; exact hs.2.2
    · rw [Split.swap_sideB]; exact hs.2.1
  obtain ⟨M, hM⟩ := isSplitOf_iff_mem_or_trivial fam ρ hcomp hnt hswap h3
  refine ⟨M, fun s => ?_⟩
  rw [hM s]
  constructor
  · -- `fam` 成员或平凡 ⟹ 出现在至少 `l` 棵树中
    rintro (hs | (⟨x, hx⟩ | ⟨x, hx⟩))
    · exact (Finset.mem_filter.mp hs).1
    · rw [mem_lSplits]
      have h1 : supportSet T s = (Finset.univ : Finset ι) :=
        supportSet_eq_univ fun i =>
          Cladogram.isSplitOf_of_sideA_singleton (T i) (s := s) (x := x) hx
      rw [h1, Finset.card_univ]; exact hl
    · rw [mem_lSplits]
      have h1 : supportSet T s = (Finset.univ : Finset ι) :=
        supportSet_eq_univ fun i =>
          Cladogram.isSplitOf_of_sideB_singleton (T i) (s := s) (x := x)
            (by rw [Split.sideB_eq_compl, hx, compl_compl])
      rw [h1, Finset.card_univ]; exact hl
  · -- 出现在至少 `l` 棵树中 ⟹ `fam` 成员或平凡
    intro hs
    by_cases htriv : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs, htriv⟩)
    · by_cases ha : 2 ≤ s.sideA.card
      · have hpos : 0 < s.sideB.card := by
          simpa [Split.sideB] using Finset.card_pos.mpr (s.nonempty 1)
        have hlt : s.sideB.card < 2 := Nat.lt_of_not_le fun hb => htriv ⟨ha, hb⟩
        have hcard1 : s.sideB.card = 1 := by omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
        have hcompl : s.sideAᶜ = ({x} : Finset X) := by
          rw [← Split.sideB_eq_compl, hx]
        exact Or.inr (Or.inr ⟨x, by rw [← hcompl, compl_compl]⟩)
      · have hpos : 0 < s.sideA.card := by
          simpa [Split.sideA] using Finset.card_pos.mpr (s.nonempty 0)
        have hlt : s.sideA.card < 2 := Nat.lt_of_not_le ha
        have hcard1 : s.sideA.card = 1 := by omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
        exact Or.inr (Or.inl ⟨x, hx⟩)

/-! ## 4. 半严格共识（Day 的 `M_2`：**不是「只出现一次」**） -/

/-- ★★ **半严格共识的 split 集**：**至少两棵**输入树含它的 split。

即 Day (1985) 的 **`M_2`**（`l = 2`）：「不是只出现一次」的 split。
（严格共识是 `M_k`，多数共识是 `M_{⌊k/2⌋+1}`——`lSplits` 一族统一之。） -/
noncomputable def nonstrictSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Cladogram X) : Finset (Split X) :=
  lSplits 2 T

theorem mem_nonstrictSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ι → Cladogram X} {s : Split X} :
    s ∈ nonstrictSplits T ↔ 2 ≤ (supportSet T s).card :=
  mem_lSplits

/-- ★★★ **半严格共识：`M_2` 的 split 两两相容**（需 `|ι| ≤ 3`，见文件头 ⚠️ 反例 3）。 -/
theorem nonstrict_compatible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Cladogram X) (hk : Fintype.card ι ≤ 3) {s t : Split X}
    (hs : s ∈ nonstrictSplits T) (ht : t ∈ nonstrictSplits T) : Split.Compatible s t :=
  lSplits_compatible 2 T (by omega) hs ht

/-- ★★ **严格 ⟹ 半严格**（`2 ≤ |ι|`；`|ι| = 1` 时反例见文件头 ⚠️ 反例 2）。 -/
theorem strictSplits_subset_nonstrictSplits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : 2 ≤ Fintype.card ι) (T : ι → Cladogram X) :
    strictSplits T ⊆ nonstrictSplits T :=
  strictSplits_subset_lSplits (l := 2) h2 T

/-- ★★★ **半严格共识树存在**（`2 ≤ |ι| ≤ 3`、`3 ≤ |X|`）。

存在 cladogram `M`，其 split 集**恰是**半严格共识的 split 集
（即「出现在至少两棵树中」的 split）。 -/
theorem nonstrict_consensus_exists {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h2 : 2 ≤ Fintype.card ι) (hk : Fintype.card ι ≤ 3)
    (T : ι → Cladogram X) (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s : Split X, M.IsSplitOf s ↔ s ∈ nonstrictSplits T :=
  lSplits_consensus_exists 2 T h2 (by omega) h3

/-- ★★ **半严格共识树展示严格共识的每个 split**（「半严格 ⊇ 严格」的树层形态）。 -/
theorem nonstrict_displays_strictSplits {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h2 : 2 ≤ Fintype.card ι) (hk : Fintype.card ι ≤ 3)
    (T : ι → Cladogram X) (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, ∀ s ∈ strictSplits T, M.IsSplitOf s := by
  obtain ⟨M, hM⟩ := nonstrict_consensus_exists h2 hk T h3
  exact ⟨M, fun s hs => (hM s).mpr (strictSplits_subset_nonstrictSplits h2 T hs)⟩

/-! ## 5. F9：严格共识的树空间性质（Day 1985） -/

/-- ★★★ **严格共识 = 各棵树 split 集之**交（`Set` 版 `iInter`）。

`Cladogram.splits`（`Phylo/Split.lean:623`）把一棵树读成它的 split 集；
严格共识正是这些集合的**交** —— Day (1985) 的
`C(T₁,…,T_k)' = ⋂_{1≤i≤k} T_i'`（md 第 224 行）。 -/
theorem strictSplits_eq_iInter_splits {ι : Type*} (T : ι → Cladogram X) :
    ((strictSplits T : Finset (Split X)) : Set (Split X)) = ⋂ i, (T i).splits := by
  ext s
  rw [Finset.mem_coe, Set.mem_iInter]
  exact mem_strictSplits

/-- ★★ 同一事实的**有限版**：`strictSplits` 就是各 `treeSplits (T i)` 的交
（`Finset.univ.filter (∀ i, s ∈ treeSplits (T i))`）。 -/
theorem strictSplits_eq_filter_iInter {ι : Type*} [Fintype ι]
    (T : ι → Cladogram X) :
    strictSplits T = Finset.univ.filter (fun s : Split X => ∀ i, s ∈ treeSplits (T i)) := by
  ext s
  rw [mem_strictSplits, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, mem_treeSplits]

/-- ★★★ **严格共识的 split 含于每棵输入树**。 -/
theorem strictSplits_subset_treeSplits {ι : Type*} (T : ι → Cladogram X) (i : ι) :
    strictSplits T ⊆ treeSplits (T i) :=
  fun _ hs => mem_treeSplits.mpr ((mem_strictSplits.mp hs) i)

/-- ★★★ **严格共识的泛性质**（「交 = 最大下界」）：
`S` 含于严格共识 ⟺ `S` 含于**每棵**树的 split 集。 -/
theorem subset_strictSplits_iff {ι : Type*} [Fintype ι]
    (T : ι → Cladogram X) (S : Finset (Split X)) :
    S ⊆ strictSplits T ↔ ∀ i, S ⊆ treeSplits (T i) := by
  constructor
  · intro h i s hs
    exact strictSplits_subset_treeSplits T i (h hs)
  · intro h s hs
    rw [mem_strictSplits]
    exact fun i => mem_treeSplits.mp (h i hs)

/-- ★ 严格共识的规模不超过任一输入树的 split 数。 -/
theorem card_strictSplits_le_treeSplits {ι : Type*} (T : ι → Cladogram X) (i : ι) :
    (strictSplits T).card ≤ (treeSplits (T i)).card :=
  Finset.card_le_card (strictSplits_subset_treeSplits T i)

/-- ★★ **严格共识的 RF 距离 = 被丢弃的 split 数**。

`rfDistance (strictSplits T) (treeSplits (T i)) = |treeSplits (T i)| - |strictSplits T|`：
因为严格共识的 split **全部**落在每棵输入树里（`strictSplits_subset_treeSplits`），
对称差只剩 `treeSplits (T i) \ strictSplits T` 一边 —— 正是严格共识**丢弃**的部分。

（Day 1985, md 第 340–348 行：`D(T₁,T₂) = |T₁' Δ T₂'|`。） -/
theorem rfDistance_strictSplits_treeSplits {ι : Type*} (T : ι → Cladogram X) (i : ι) :
    Split.rfDistance (strictSplits T) (treeSplits (T i))
      = (treeSplits (T i)).card - (strictSplits T).card := by
  rw [Split.rfDistance_def]
  have hsub := strictSplits_subset_treeSplits T i
  have hempty : strictSplits T \ treeSplits (T i) = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr hsub
  rw [hempty, Finset.empty_union]
  exact Finset.card_sdiff_of_subset hsub

/-- ★★ 严格共识的 split 同时落在任意两棵树的 split 集里（交的结合形态）。 -/
theorem strictSplits_subset_inter_treeSplits {ι : Type*} (T : ι → Cladogram X) (i j : ι) :
    strictSplits T ⊆ treeSplits (T i) ∩ treeSplits (T j) :=
  fun _ hs => Finset.mem_inter.mpr
    ⟨strictSplits_subset_treeSplits T i hs, strictSplits_subset_treeSplits T j hs⟩

/-! ## 6. 显式缺口

本文件未做的事（照实报告）：

1. **`M_l` 的家谱完整性**：`majoritySplits`（`Phylo/Consensus.lean`）与本文件的
   `lSplits` 的**逐点等价**（`IsMajority T s ↔ ⌊k/2⌋+1 ≤ supportCount T s`）未证 ——
   这只是算术改写，但需要 `⌊·⌋` 与 `2·` 的换算层，本文件未做。
2. **半严格共识在 `|ι| ≥ 4` 的正确取法**：Day 的 `M_l` 要求 `k/2 < l`，
   故 `l = 2` 只对 `k ≤ 3` 合法（见文件头 ⚠️ 反例 3）。
   真正的「半严格共识」（Bremer 1990 的 *combinable component consensus*）定义
   **不在** `references/md/` 中（Day 1985 全文无 `semi-strict` 字样），
   故本文件**不硬编**它的定义；`def semistrict_gap : Prop := False` 无信息量，
   这里以本条说明代替（如实报告文献缺口）。 -/
