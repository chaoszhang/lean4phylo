/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERGeneTree
import Phylo.Stat.CASTERLM1
import Phylo.Stat.CASTERTopoSplit

/-!
# `Phylo.Stat.CASTERInstances` —— 各模型的**端到端定理 1**集中地

每个模型（JC69 / LM1 / F84）都只需两件事：
1. 一条 `PropAData` 实例（模型的命题 A，即「基因树层得分差」）；
2. 把它喂给 `CASTERTopo.TopoIdeal.ofModel`（+ 桥接 `propB_of_bridge`），
   再由 ★★★ `propAData_caster_statisticallyConsistent`（`Phylo.Stat.CASTERGeneTree`，**泛型**）
   给出**定理 1**。

⇒ 本文件的作用是把「模型 ⇒ 定理 1」这一步写**一次**，
避免每个模型各写一遍样板；新模型只要给一条 `PropAData` 就能照抄。

## 已就位（三个模型全部就位）

* ★★★ `lm1_caster_statisticallyConsistent` —— **LM1**（`sm.tex` 1611–1700）。
* JC69 的对应定理在 `Phylo.Stat.CASTERGeneTree.jc69_caster_statisticallyConsistent`（模型专属文件里）。
* ★★★ `Phylo.Stat.CASTERF84PropA.f84_caster_statisticallyConsistent` —— **F84**（模型专属文件里）：
  `π, κ` 退为参数，命题 A 的三条核恒等式由 `Phylo.Stat.CASTERF84Scaffold` 的
  ★★★ `Ew_diag` / `EwA_zero` / `EwB_zero` **无条件**供给（不再作为假设）。
* 树级收口三件套：★★★ `jc69_recovers_true_tree` / ★★★ `lm1_recovers_true_tree` /
  ★★★ `f84_recovers_true_tree`。

## 🔻 诚实边界

* 结论停在**无根 quartet 拓扑层**（`IsTrueT`：每个 4-元集的拓扑都判对）。
  升级到「估计量的树与真树**同构**」的路已经铺好：
  ★★★ `CASTERTopoSplit.TopoIdeal.toSplitIdeal`（`TopoIdeal → CASTERIdeal`）
  ＋ 既有 `QuartetDecidesTree`；对 `X = Fin 4`（只有唯一 4-元集）这一步是同义反复。
* 大数定律是**显式假设** `hconv`（不新增公理）；可积性 `hint`/`hf_int` 对应正文条件 (2)。 -/

universe u

namespace Phylo.Stat.CASTERInstances

open Phylo.Stat.CASTERWeights (Topo)
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERTopoSplit
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERGeneTree
open Phylo.CASTERLM1
open MeasureTheory

/-- ★★★ **LM1 下的 CASTER 定理 1**（单个 quartet，无根 quartet 拓扑层）。

把 LM1 的命题 A（`Phylo.CASTERLM1.lm1PropAData`：`E[w(ab|cd)] − E[w(ac|bd)] =
8π_R²π_Y²·e^{−λL_T}·(1 − e^{−2λl_x})`）喂给抽象引擎，得到：
**在 LM1 下最大化 CASTER 得分的估计量最终把 quartet 拓扑判对**。

假设全部显式：`hdeep`/`hpos`（MSC 侧：无深合并事件可测且有正概率）、
`hf_int`/`hf_pos`（幅度可积且在无深合并时为正）、`hint`（三拓扑期望权重可积 = 正文条件 (2)）、
`hconv`（大数定律）；`hNE`（存在非真选择）在泛型定理内部就地证出。 -/
theorem lm1_caster_statisticallyConsistent
    (S : MSCTopoSym ((Fin 4 → ℝ) × ℝ)) (ν : Measure ((Fin 4 → ℝ) × ℝ)) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | S.deep θ}) (π : Fin 4 → ℝ) (hsum : piR π + piY π = 1) (lam : ℝ)
    (hf_int : Integrable (lm1PropAData π hsum lam).f ν)
    (hf_pos : ∀ θ, ¬ S.deep θ → 0 < (lm1PropAData π hsum lam).f θ)
    (hpos : 0 < ν {θ | ¬ S.deep θ})
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo, S.τd θ T' * (lm1PropAData π hsum lam).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n)
      (TopoIdeal.ofModel S ν hdeep (lm1PropAData π hsum lam) hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)), topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent S ν hdeep (lm1PropAData π hsum lam)
    hf_int hf_pos hpos hint emp hconv hE

/-- ★★★ **定理 1 的树同构收口（通用形状）**：若估计量每一步输出的**二元树**的每个 quartet 拓扑
都等于真拓扑（即 `Topo` 层判对了），则它与真树**同构**。

这是把「quartet 拓扑判对」升级为「树判对」的**唯一**一步，对三个模型通用：
用 ★★★ `CASTERTopoSplit.eq_or_swap_of_topoOfSplit_eq` 把「拓扑类相同」翻成
「`split` 相同或互为 `swap`」，再由 ★★★ `QuartetDecidesTree` 收口。

（对 `X = Fin 4`——只有唯一 4-元集——这一步是重言式；对更多物种它是必要的。） -/
theorem iso_of_quartets_true {X : Type u} [Fintype X] [DecidableEq X]
    (e : QuartetLabel X)
    {Ttrue Qt : QuartetTree.{u, u} X} (hTtrue : Ttrue.tree.IsBinary) (hQt : Qt.tree.IsBinary)
    (hqtrue_card : ∀ (S : Finset X) (hS : S.card = 4), (Ttrue.q S hS).sideA.card = 2)
    (hQt_card : ∀ (S : Finset X) (hS : S.card = 4), (Qt.q S hS).sideA.card = 2)
    (hclass : ∀ (S : Finset X) (hS : S.card = 4),
      topoOfSplit (e S hS) (Qt.q S hS) = topoOfSplit (e S hS) (Ttrue.q S hS)) :
    Nonempty (Iso Qt.tree Ttrue.tree) := by
  refine QuartetDecidesTree X Qt Ttrue hQt hTtrue fun S hS => ?_
  rcases eq_or_swap_of_topoOfSplit_eq (e S hS) (hQt_card S hS) (hqtrue_card S hS)
    (hclass S hS) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- ★★★ **定理 1 的树级形式**（通用）：Topo 层的估计量 `E` 最终判对（定理 1 的结论），
`Qt n` 是**实现** `E n` 的二元树（每个 4-元集上它的 split 拓扑类就是 `E n` 在该集上的选择），
`Ttrue` 是实现真选择 `qtrue` 的真树 ⇒ `Qt n` 最终与 `Ttrue` **同构**。

`2|2` 条件不必再传：它是 `QuartetTree.q_card` 字段（T0.6 治本）。 -/
theorem tree_iso_of_topo_consistency {X : Type u} [Fintype X] [DecidableEq X]
    (e : QuartetLabel X) (qtrue : TopoChoice X) {E : ℕ → TopoChoice X}
    (hE : ∃ N : ℕ, ∀ n ≥ N, IsTrueT qtrue (E n))
    {Ttrue : QuartetTree.{u, u} X} {Qt : ℕ → QuartetTree.{u, u} X}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset X) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = qtrue S hS)
    (hreal : ∀ (n : ℕ) (S : Finset X) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) := by
  obtain ⟨N, hN⟩ := hE
  exact ⟨N, fun n hn => iso_of_quartets_true e hTtrue (hQt n)
    (fun S hS => Ttrue.q_card S hS) (fun S hS => (Qt n).q_card S hS)
    (fun S hS => by rw [hreal n S hS, hN n hn S hS, htrue_class S hS])⟩


/-- ★★★ **JC69 下 CASTER 恢复真物种树的拓扑**（**树级**，正文定理 1 的最终形式）。

薄壳：`hE` 由 ★★★ `jc69_caster_statisticallyConsistent` 供给（一行），
本定理把它经 ★★★ `tree_iso_of_topo_consistency` 升级为「估计量的树与真树**同构**」。 -/
theorem jc69_recovers_true_tree (e : QuartetLabel (Fin 4)) {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd) hE hTtrue hQt
    htrue_class hreal


/-- ★★★ **LM1 下 CASTER 恢复真物种树的拓扑**（**树级**，同 `jc69_recovers_true_tree`；
`hE` 由 ★★★ `lm1_caster_statisticallyConsistent` 供给）。 -/
theorem lm1_recovers_true_tree (e : QuartetLabel (Fin 4)) {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd) hE hTtrue hQt
    htrue_class hreal

/-- ★★★ **F84 下 CASTER 恢复真物种树的拓扑**（**树级**，同 `jc69_recovers_true_tree`；
`hE` 由 ★★★ `Phylo.Stat.CASTERF84PropA.f84_caster_statisticallyConsistent` 供给——
那条定理本身已**无条件**：命题 A 的三条核恒等式由 `Phylo.Stat.CASTERF84Scaffold` 给出）。 -/
theorem f84_recovers_true_tree (e : QuartetLabel (Fin 4)) {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd) hE hTtrue hQt
    htrue_class hreal

/-- ★★★ **定理 1（任意物种数，条件形式）**：只要**每个 4-元集都有自己的 MSC 模型**
（`M S hS`：该 quartet 的基因树拓扑分布）与**自己的命题 A 数据**（`P S hS`）
——这正是正文的设定（各 quartet 的支长不同）——则最大化 CASTER 得分的估计量
最终把**每一个** quartet 的拓扑都判对。

用的就是 ★★★ `TopoIdeal.ofFamily`（逐 quartet 建模）与 ★★★ `topo_statisticallyConsistent`。
`hNE`（存在非真选择）由调用方给出（例如取 `fun _ _ => Topo.ac_bd`）；
对单个 quartet（`X = Fin 4`）该见证在 `jc69_/lm1_…statisticallyConsistent` 内部就地证出。 -/
theorem caster_statisticallyConsistent_of_family {X : Type u} [Fintype X] [DecidableEq X]
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
      Integrable (fun θ => ∑ T' : Topo, (M S hS).τd θ T' * (P S hS).A θ T' T) (ν S hS))
    (emp : ℕ → TopoWeight X)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n)
      (TopoIdeal.ofFamily Θ M ν hdeep P hf_int hf_pos hpos hint).W ε)
    (hNE : ∃ q : TopoChoice X, ¬ IsTrueT (fun _ _ => Topo.ab_cd) q)
    {E : ℕ → TopoChoice X}
    (hE : ∀ (n : ℕ) (q : TopoChoice X), topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  topo_statisticallyConsistent (TopoIdeal.ofFamily Θ M ν hdeep P hf_int hf_pos hpos hint)
    emp hconv hNE hE

/-- ★★★ **定理 2（贪心放置一致，任意物种数，条件形式）**。

附录对定理 2 的归纳证明（`sm.tex` 1706–1720）说：**基例**是定理 1（四叶），
**归纳步**是「把物种 `a` 放到骨架树 `S'` 上时，真树一定在候选集里」，
于是若贪心的输出不等于真树就与定理 1 的严格分离矛盾。

本定理正是这条归纳步的抽象形式：候选集 `C n`（放置的空间）**含真选择**，
估计量在 `C n` 上最大化经验得分 ⇒ 最终把每个 quartet 都判对。
**候选集的具体形状（三划分 / 放置位置 / DP 约束）不影响结论** —— 这也是为什么附录能一句话带过。

（照 ★★★ `topo_greedy_consistent`；各 quartet 的模型与命题 A 数据同
`caster_statisticallyConsistent_of_family`。） -/
theorem caster_greedy_consistent_of_family {X : Type u} [Fintype X] [DecidableEq X]
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
      Integrable (fun θ => ∑ T' : Topo, (M S hS).τd θ T' * (P S hS).A θ T' T) (ν S hS))
    (emp : ℕ → TopoWeight X)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, TopoClose (emp n)
      (TopoIdeal.ofFamily Θ M ν hdeep P hf_int hf_pos hpos hint).W ε)
    (hNE : ∃ q : TopoChoice X, ¬ IsTrueT (fun _ _ => Topo.ab_cd) q)
    (C : ℕ → Set (TopoChoice X))
    (hfeas : ∀ n : ℕ, (fun _ _ => Topo.ab_cd) ∈ C n)
    {E : ℕ → TopoChoice X}
    (hmax : ∀ (n : ℕ) (q : TopoChoice X), q ∈ C n →
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  topo_greedy_consistent (TopoIdeal.ofFamily Θ M ν hdeep P hf_int hf_pos hpos hint)
    emp hconv hNE C hfeas hmax

end Phylo.Stat.CASTERInstances
