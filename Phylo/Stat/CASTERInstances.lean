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

## 已就位

* ★★★ `lm1_caster_statisticallyConsistent` —— **LM1**（`sm.tex` 1611–1700）。
* JC69 的对应定理在 `Phylo.Stat.CASTERGeneTree.jc69_caster_statisticallyConsistent`（模型专属文件里）。
* F84 待其 `PropAData` 实例就位（见 `CASTER_F84_FINDING.md`：记账需按「系数各除以 4」的口径）。

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

end Phylo.Stat.CASTERInstances
