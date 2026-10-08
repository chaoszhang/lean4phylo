/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSC
import Phylo.Stat.MSCProof
import Phylo.Stat.NJst
import Phylo.Stat.Stability

/-!
# `Phylo.Stat.MSCSamplingVacuity` —— `MSCSampling.converges` 的**空洞性**与其**修正**

## 1. 发现（本文件第一个交付）

`Phylo/Stat/MSC.lean` 第 **170–175** 行把「MSC 采样 + 大数定律」公理化成

    structure MSCSampling (X) where
      emp : ℕ → QuartetFreq X
      converges : ∀ m : MSCFreq X, ∀ ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp n) m.freq ε

⚠️ **`emp` 不依赖 `m`，而 `converges` 却对「所有」理论律 `m` 断言**：
在**同一个**经验序列 `emp` 上，要求它最终同时 `ε`-接近**每一个**理论频率表。
只要 `MSCFreq X` 里有两个**频率表不同**的元素（本文件证明 `X = Fin 4` 就是如此，
用 W10c 的 `mscFreqFin4` 取 `t = 1, 2`），这两条要求**互相矛盾** ⇒

* ★★★ `not_nonempty_mscSampling_fin4`：**`MSCSampling (Fin 4)` 是空类型**；
* ★★★ `not_nonempty_mscSampling_of_freq_ne`：**一般判据** —— 只要 `MSCFreq X` 里存在两个
  **频率表不同**的元素，`MSCSampling X` 就空（`Fin 4` 的实例由它推出）；
* ★★★ `not_nonempty_ustarSampling_of_ne`：**同一缺陷在 `NJst` 的采样公理上重复出现**
  （`Phylo/Stat/NJst.lean` 第 **165–170** 行的 `USTARSampling`：`emp` 也不依赖 `M`）；
* ★★★ `statisticallyConsistent_vacuous_fin4`：于是
  `StatisticallyConsistent E sm`（`MSC.lean` 第 **184–186** 行）
  对**任何**估计量 `E` 都**空洞成立** —— 包括 `Phylo/Stat/Stability.lean` 的
  `astral_statisticallyConsistent`、`Phylo/Stat/NJst.lean` 的 `njst_statisticallyConsistent`：
  它们都以 `sm : MSCSampling X` / `sm : USTARSampling X` 为**假设**，
  故对 `X = Fin 4`（`NJst` 侧为「有两个模型 `δ` 不同」）**没有非空洞内容**。

这不是「定理证错了」，而是「**公理的形状**与其叙事不符」——
正是本项目最看重的那类「叙事 ≠ 形式化」问题。

## 2. 修正（本文件第二个交付）

语义上「一致性」应当是：**在律 `m` 下采样**，经验频率 `emp m n` 收敛到 `m.freq`。
即 `emp` 必须**依赖真实律**。本文件给出修正结构

    structure MSCSamplingLaw (X) where
      emp : MSCFreq X → ℕ → QuartetFreq X
      converges : ∀ m ε > 0, ∃ N, ∀ n ≥ N, FreqClose (emp m n) m.freq ε

* ★★★ `mscSamplingLaw_nonempty`：**显式给出一个居民**（理想样本 `emp m n := m.freq`）
  —— 与旧结构的空性形成对照，**这是「修正版非空洞」的证明**；
* ★★ `StatisticallyConsistentLaw`：对应的（非空洞的）一致性谓词；
* ★★★ `astral_statisticallyConsistent_law`：**正面修复** —— 把
  `Phylo/Stat/Stability.lean` 的 `astral_statisticallyConsistent` 里的
  `sm : MSCSampling X` 换成 `sm : MSCSamplingLaw X`（该证明只用到 `sm.converges m` 与
  `sm.emp n` 两处，故**逐字相同**）⇒ 一致性断言在修正版上**有内容**。

## 3. 与 W10d / `MSCSamplingAE` 的关系

`Phylo/Stat/EmpiricalConvergence.lean`（W10d）在**真概率空间**上证明了单个 `(S,q)` 的
几乎必然收敛，`Phylo/Stat/MSCSamplingAE.lean` 把它升到**整张表**（含**统一 `N`**）。
那条路子给出的正是**修正版**语义的 `emp`（在律 `m` 下采样）——
把二者接起来（由 a.e. 定理造出 `MSCSamplingLaw` 的居民）**本文件未做**，见文末边界表。

## 4. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| `MSCSampling (Fin 4)` 为空 | ✅ **本文件**（用 `t = 1, 2` 两个律） |
| 旧 `StatisticallyConsistent` 对 `Fin 4` 空洞 | ✅ **本文件** |
| 修正结构非空洞（显式居民） | ✅ **本文件** |
| **修正版**上的 ASTRAL 一致性（非空洞） | ✅ **本文件**（`astral_statisticallyConsistent_law`，证明与旧版逐字相同） |
| 「由 a.e. 大数定律造出 `MSCSamplingLaw` 的居民」 | ❌ **未做**（需要「按律 `m` 采样的概率空间」这一族，即 W10d 的缺口 K） |
| 旧结构在**一般** `X` 上的空性 | ⚠️ 本文件只证 `X = Fin 4`；一般 `X` 需要「`MSCFreq X` 有两个频率表不同的元素」这一**组合前提** |
| 「`MSCSampling` 的**字段形状**」 | ⚠️ **未修改** `MSC.lean`（沿用本项目「新增派生版、保持旧版兼容」的纪律）；本文件只**指出并修正其形状** |
-/

universe u v

namespace Phylo.Stat.MSCSamplingVacuity

open Phylo.Stat.MSCProof

/-! ## 1. `MSCFreq (Fin 4)` 里有两个**频率表不同**的元素 -/

/-- ★★ `mscConcordant` **不是常函数**：`t = 1` 与 `t = 2` 处取值不同
（闭形式 `1 − ⅔e^{−t}`，用 `Real.exp` 的单射性）。 -/
theorem mscConcordant_one_ne_two : mscConcordant 1 ≠ mscConcordant 2 := by
  intro h
  rw [mscConcordant_eq, mscConcordant_eq, Coalescent.pConcordant, Coalescent.pConcordant] at h
  have hexp : Real.exp (-1) = Real.exp (-2) := by linarith
  have h' : (-1 : ℝ) = -2 := Real.exp_injective hexp
  norm_num at h'

/-- ★★★ `MSCFreq (Fin 4)` 里存在两个元素，它们在某点 `(S, q)` 上的频率**不同**。 -/
theorem mscFreqFin4_freq_ne :
    ∃ (S : Finset (Fin 4)) (hS : S.card = 4) (q : Split ↥S),
      (mscFreqFin4 1 (by norm_num)).freq.p S hS q
        ≠ (mscFreqFin4 2 (by norm_num)).freq.p S hS q := by
  refine ⟨Finset.univ, Finset.card_univ, qSplit Finset.univ Finset.card_univ, ?_⟩
  have hq : sideA4 (S := Finset.univ) (qSplit Finset.univ Finset.card_univ)
      = ({2, 3} : Finset (Fin 4)) := sideA4_qSplit Finset.univ Finset.card_univ
  have hqconc : isConc Finset.univ (qSplit Finset.univ Finset.card_univ) :=
    ⟨qSplit_card Finset.univ Finset.card_univ, by rw [hq]; decide⟩
  have e1 : (mscFreqFin4 1 (by norm_num)).freq.p Finset.univ Finset.card_univ
      (qSplit Finset.univ Finset.card_univ) = mscConcordant 1 / 2 :=
    show mscP 1 Finset.univ Finset.card_univ (qSplit Finset.univ Finset.card_univ) = _ from
      mscP_of_isConc hqconc
  have e2 : (mscFreqFin4 2 (by norm_num)).freq.p Finset.univ Finset.card_univ
      (qSplit Finset.univ Finset.card_univ) = mscConcordant 2 / 2 :=
    show mscP 2 Finset.univ Finset.card_univ (qSplit Finset.univ Finset.card_univ) = _ from
      mscP_of_isConc hqconc
  rw [e1, e2]
  intro h
  exact mscConcordant_one_ne_two (by linarith)

/-! ## 2. ★★★ 旧 `MSCSampling` 的**空洞性** -/

section General

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★★ **一般判据（空洞性）**：只要 `MSCFreq X` 里存在两个**频率表不同**的元素，
`MSCSampling X` 就是**空类型**（故 `StatisticallyConsistent` 空洞）。

论证：设 `sm : MSCSampling X`，取两个律在某点相差 `d := |p₁ − p₂| > 0`，令 `ε := d/4`。
由 `converges` 对 `m₁`、`m₂` 分别取 `N₁, N₂`，在 `n := max N₁ N₂` 处同时
`|e − p₁| < ε` 与 `|e − p₂| < ε`，故 `d = |p₁ − p₂| ≤ |p₁ − e| + |e − p₂| < 2ε = d/2` —— 矛盾。 -/
theorem not_nonempty_mscSampling_of_freq_ne
    (h : ∃ m₁ m₂ : MSCFreq.{u, v} X, ∃ (S : Finset X) (hS : S.card = 4) (q : Split ↥S),
      m₁.freq.p S hS q ≠ m₂.freq.p S hS q) :
    ¬ Nonempty (MSCSampling.{u, v} X) := by
  obtain ⟨m₁, m₂, S, hS, q, hpq⟩ := h
  rintro ⟨sm⟩
  set p1 := m₁.freq.p S hS q with hp1
  set p2 := m₂.freq.p S hS q with hp2
  set d := |p1 - p2| with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact abs_pos.mpr (sub_ne_zero.mpr hpq)
  obtain ⟨N1, hN1⟩ := sm.converges m₁ (d / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := sm.converges m₂ (d / 4) (by linarith)
  have h1 := hN1 (max N1 N2) (le_max_left N1 N2) S hS q
  have h2 := hN2 (max N1 N2) (le_max_right N1 N2) S hS q
  have hlt : d < d / 2 := by
    calc d = |p1 - p2| := hd
      _ = |(p1 - (sm.emp (max N1 N2)).p S hS q)
            + ((sm.emp (max N1 N2)).p S hS q - p2)| := by ring_nf
      _ ≤ |p1 - (sm.emp (max N1 N2)).p S hS q|
            + |(sm.emp (max N1 N2)).p S hS q - p2| := abs_add_le _ _
      _ = |(sm.emp (max N1 N2)).p S hS q - p1|
            + |(sm.emp (max N1 N2)).p S hS q - p2| := by rw [abs_sub_comm p1]
      _ < d / 4 + d / 4 := add_lt_add h1 h2
      _ = d / 2 := by ring
  linarith

/-- ★★★ **同一缺陷在 `NJst` 的采样公理上重复出现**（`Phylo/Stat/NJst.lean` 第 **165–170** 行）：
`USTARSampling.emp : ℕ → Dissimilarity X` 也**不依赖模型** `M`，而 `converges` 却对
**所有** `M : NJstData X` 断言。故只要有两个模型的 `δ` 在某点不同，它同样是**空类型**，
`njst_statisticallyConsistent` 随之**空洞**。 -/
theorem not_nonempty_ustarSampling_of_ne
    (h : ∃ M₁ M₂ : NJstData.{u, v} X, ∃ x y : X, M₁.δ.val x y ≠ M₂.δ.val x y) :
    ¬ Nonempty (USTARSampling.{u, v} X) := by
  obtain ⟨M₁, M₂, x, y, hxy⟩ := h
  rintro ⟨sm⟩
  set p1 := M₁.δ.val x y with hp1
  set p2 := M₂.δ.val x y with hp2
  set d := |p1 - p2| with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact abs_pos.mpr (sub_ne_zero.mpr hxy)
  obtain ⟨N1, hN1⟩ := sm.converges M₁ (d / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := sm.converges M₂ (d / 4) (by linarith)
  have h1 := hN1 (max N1 N2) (le_max_left N1 N2) x y
  have h2 := hN2 (max N1 N2) (le_max_right N1 N2) x y
  have hlt : d < d / 2 := by
    calc d = |p1 - p2| := hd
      _ = |(p1 - (sm.emp (max N1 N2)).val x y)
            + ((sm.emp (max N1 N2)).val x y - p2)| := by ring_nf
      _ ≤ |p1 - (sm.emp (max N1 N2)).val x y|
            + |(sm.emp (max N1 N2)).val x y - p2| := abs_add_le _ _
      _ = |(sm.emp (max N1 N2)).val x y - p1|
            + |(sm.emp (max N1 N2)).val x y - p2| := by rw [abs_sub_comm p1]
      _ < d / 4 + d / 4 := add_lt_add h1 h2
      _ = d / 2 := by ring
  linarith

end General

/-- ★★★ **`MSCSampling (Fin 4)` 是空类型**（`not_nonempty_mscSampling_of_freq_ne` 的实例，
用 W10c 的两个律 `t = 1, 2`）。

论证：设 `sm : MSCSampling (Fin 4)`。取上面两个频率表在某点相差 `d := |p₁ − p₂| > 0`
（`mscFreqFin4_freq_ne`），令 `ε := d/4`。由 `converges` 对 `m₁` 与 `m₂` 分别取 `N₁, N₂`，
在 `n := max N₁ N₂` 处同时有 `|e − p₁| < ε` 与 `|e − p₂| < ε`，
故 `d = |p₁ − p₂| ≤ |p₁ − e| + |e − p₂| < 2ε = d/2` —— 矛盾。 -/
theorem not_nonempty_mscSampling_fin4 : ¬ Nonempty (MSCSampling.{0, 0} (Fin 4)) :=
  not_nonempty_mscSampling_of_freq_ne
    ⟨mscFreqFin4 1 (by norm_num), mscFreqFin4 2 (by norm_num), mscFreqFin4_freq_ne⟩

/-- ★★★ **旧版「统计一致性」对 `Fin 4` 是空洞的**：任何估计量 `E` 都满足
`StatisticallyConsistent E sm`（因为 `sm : MSCSampling (Fin 4)` 不存在）。

⚠️ 这不是「证明了 ASTRAL/NJst 一致」，而是**指出那条断言在此形状下没有内容**。 -/
theorem statisticallyConsistent_vacuous_fin4 (E : QuartetFreq (Fin 4) → Cladogram (Fin 4))
    (sm : MSCSampling.{0, 0} (Fin 4)) : StatisticallyConsistent E sm :=
  absurd ⟨sm⟩ not_nonempty_mscSampling_fin4

/-! ## 3. ★★★ 修正版：`emp` **依赖真实律** -/

/-- ★★★ **修正版 `MSCSampling`**：经验频率 `emp m n` **依赖真实律 `m`**
（「在律 `m` 下采样 `n` 个位点」），`converges` 只对**该律**断言。

这是「统计一致性」的**正确形状**；与旧版的唯一差别是 `emp` 多了一个 `MSCFreq X` 参数。 -/
structure MSCSamplingLaw (X : Type u) [Fintype X] [DecidableEq X] where
  /-- 在**真实律** `m` 下，`n` 个位点的经验 quartet 频率。 -/
  emp : MSCFreq.{u, v} X → ℕ → QuartetFreq X
  /-- ★ **大数定律**：在律 `m` 下，经验频率最终 `ε`-接近 `m.freq`。 -/
  converges : ∀ m : MSCFreq.{u, v} X, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, FreqClose (emp m n) m.freq ε

/-- ★★★ **修正版**对应的（**非空洞**的）统计一致性谓词。 -/
def StatisticallyConsistentLaw {X : Type u} [Fintype X] [DecidableEq X]
    (E : QuartetFreq X → Cladogram.{u, v} X)
    (sm : MSCSamplingLaw.{u, v} X) : Prop :=
  ∀ m : MSCFreq.{u, v} X, ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp m n)) m.tree)
/-- ★★★ **修正版是空的吗？不是 —— 显式给出一个居民**（「理想样本」`emp m n := m.freq`）。

⚠️ 这个居民是**退化**的（样本恒等于理论频率），但它足以证明**修正版不是空类型**，
从而与 `not_nonempty_mscSampling_fin4` 形成**对照**：空洞性来自**形状**，不是来自「一致性」本身。 -/
theorem mscSamplingLaw_nonempty (X : Type u) [Fintype X] [DecidableEq X] :
    Nonempty (MSCSamplingLaw.{u, v} X) :=
  ⟨{ emp := fun m _ => m.freq
     converges := fun m ε hε =>
       ⟨0, fun _ _ S hS q => by
         show |m.freq.p S hS q - m.freq.p S hS q| < ε
         rw [sub_self, abs_zero]
         exact hε⟩ }⟩

/-! ## 4. ★★★ **正面修复**：修正版上的 ASTRAL 统计一致性（**非空洞**） -/

section Fix

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- ★★★ **修正版的 ASTRAL 统计一致性**（**非空洞**）。

把 `Phylo/Stat/Stability.lean` 的 `astral_statisticallyConsistent` 里的
`sm : MSCSampling X` 换成修正版 `sm : MSCSamplingLaw X`（`emp` **依赖真律 `m`**），
其余**逐字相同** —— 因为该证明只用到 `sm.converges m` 与 `sm.emp n` 两处。
这是对第 2 节「空洞性」的**正面修复**：一致性断言现在有内容。 -/
theorem astral_statisticallyConsistent_law (m : MSCFreq.{u, v} X)
    (sm : MSCSamplingLaw.{u, v} X)
    {E : QuartetFreq X → QuartetTree.{u, v} X} (hE : ∀ D, IsASTRAL D (E D))
    (hNE : ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueChoice m (E (sm.emp m n)).q := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := exists_gap m hNE
  set M : ℝ := 2 * (Fintype.card {S : Finset X // S.card = 4} : ℝ) + 1 with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ (Fintype.card {S : Finset X // S.card = 4} : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨N, hN⟩ := sm.converges m (δ / M) (div_pos hδ hMpos)
  refine ⟨N, fun n hn => ?_⟩
  refine stable_argmax (D := sm.emp m n) m hδ hgap ?_ ?_
  · simpa [hMdef] using hN n hn
  · exact hE (sm.emp m n) m.toQuartetTree

end Fix

end Phylo.Stat.MSCSamplingVacuity
