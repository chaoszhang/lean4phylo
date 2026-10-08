/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERWeights
import Phylo.Stat.CASTERTopo
import Phylo.Stat.CASTERInstances
import Phylo.Stat.CASTERF84PropA
import Phylo.Stat.MSCKingman

/-!
# `Phylo.Stat.MSCInstance` —— 把 Kingman `MSCTopoSym` 实例**接回**端到端定理（W9 Phase 2）

## 0. ⚠️ 这里为什么**不能**写 `import Phylo`

本模块**已被登记进 `Phylo.lean`**；若再 `import Phylo` 就构成
`Phylo → MSCInstance → Phylo` **构建环**（lake 报 `build cycle detected`，
`lake build` 直接失败）。故只 import 真正提供名字的**具体子模块**：
`CASTERTopo`（`TopoIdeal` / `TopoWeight` / `Iso` 等）· `CASTERInstances`（`tree_iso_of_topo_consistency`、
并传递 `CASTERGeneTree` / `CASTERLM1` / `CASTERTopoSplit`）· `CASTERF84PropA`（F84 的 `PropAData`）·
`MSCKingman`（Kingman 实例）。
**⚠️ 另一个陷阱**：登记**之前**单跑 `lake build Phylo.Stat.MSCInstance` 会是**假绿灯**
（此时 `import Phylo` 还没把自己算进去）—— 一定要在**登记之后**再跑全量 `lake build`。

## 1. 本文件补的是哪一段

```
模型（JC69 / LM1 / F84）        Phylo.Stat.CASTERGeneTree / CASTERLM1 / CASTERF84PropA
      │  命题 A：E[w(真)|G] − f = E[w(错₁)|G] = E[w(错₂)|G]
      ▼
对称性（MSC 溯祖层）            ★★★ Phylo.Stat.MSCKingman.kingmanMSCTopoSym   ← W9 Phase 1
      │  `deep` ⇒ 三拓扑各 1/3；`¬deep` ⇒ 点质量
      ▼
引擎（命题 B）                  Phylo.Stat.CASTEREngine.MSCTopoSym / CASTERTopo.ofModel
      ▼
定理 1（一致性）                ★★★ 本文件的 `*_caster_statisticallyConsistent_kingman`
```

Phase 1 之前，全库**每一处** `MSCTopoSym` 都只是**假设参数**（`S : MSCTopoSym Θ`），
没有一处具体构造 ⇒ 命题 B 与定理 1 的 MSC 一侧**悬在半空**。
Phase 1 给出了具体实例；**本文件把那个实例真正喂进端到端定理**。

## 2. 为什么能「原样搬运」既有模型数据

`KingmanΘ` 的**第一个分量刻意就是端到端定理里既有的样本空间** `(Fin 4 → ℝ) × ℝ`
（叶长 × 内部枝长，见 `Phylo.Stat.MSCKingman.KingmanΘ`）。因此三个模型的 `PropAData`
（`jc69PropAData` / `Phylo.CASTERLM1.lm1PropAData` / `Phylo.Stat.CASTERF84PropA.f84PropAData`，
它们的样本空间都恰是 `(Fin 4 → ℝ) × ℝ`）可以沿投影 `Prod.fst` **原样前推**
（★★ `transportPropAData`），不必改动任何一个模型的证明。

⇒ **旧版定理一字未动**（`jc69_…` / `lm1_…` / `f84_caster_statisticallyConsistent` 全部保留），
本文件只**新增派生版**：把 `S` 这个参数换成 ★★★ `kingmanMSCTopoSym`。

## 3. 诚实边界（**没有**变的东西）

`ν`（`KingmanΘ` 上的概率测度）、`hdeep` / `hpos`（MSC 侧可测性与正概率）、
`hf_int` / `hf_pos`（幅度可积且正）、`hint`（正文条件 (2)「权重一致有界」）、
`hconv`（大数定律）**仍然是显式假设** —— 它们属于**渐近层与解析正则性**，
与缺口 G5′（溯祖层的拓扑分布从哪来）是两件事。本文件只把 `S` 这一个参数真正消掉。

## 4. 文献

* Allman, Degnan & Rhodes (2011) **Lemma 4**（`references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md`
  **962–971** 行；边界注记 **973–974** 行：该引理**只对 5 taxa 成立、6 taxa 起失效**）
  —— 由 `Phylo.Stat.MSCKingman.AllSameShape` 显式承载；
* Kingman (1982) 溯祖 —— `Phylo.Stat.Coalescent`；
* CASTER：Zhang, Nielsen & Mirarab (2025), *Science* **387**(6737) eadk9688。
-/

noncomputable section

namespace Phylo.Stat.MSCInstance

open MeasureTheory
open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTEREngine
open Phylo.Stat.CASTERBridge
open Phylo.Stat.CASTERTopo
open Phylo.Stat.CASTERTopoSplit
open Phylo.Stat.CASTERGeneTree
open Phylo.Stat.CASTERInstances
open Phylo.Stat.MSCKingman

/-! ## 1. `PropAData` 沿投影的搬运 -/

/-- ★★ **把 `PropAData Θ` 沿 `φ : Θ' → Θ` 前推**：三个模型的命题 A 数据都定义在
`(Fin 4 → ℝ) × ℝ` 上，而 `KingmanΘ` 的第一个分量就是它，故取 `φ = Prod.fst` 即可原样搬运。
三条子句是**纯搬运**（不涉及任何模型内容）。 -/
def transportPropAData {Θ Θ' : Type*} (φ : Θ' → Θ) (P : PropAData Θ) : PropAData Θ' where
  A := fun θ T' τ => P.A (φ θ) T' τ
  f := fun θ => P.f (φ θ)
  clause_ab := fun θ T' h => P.clause_ab (φ θ) T' h
  clause_ac := fun θ T' h => P.clause_ac (φ θ) T' h
  clause_ad := fun θ T' h => P.clause_ad (φ θ) T' h

/-! ## 2. JC69 -/

/-- JC69 的命题 A 数据搬到 `KingmanΘ` 上。 -/
abbrev jc69PropADataK : PropAData KingmanΘ :=
  transportPropAData Prod.fst jc69PropAData

/-- ★★★ **JC69 的 CASTER 定理 1（MSC 侧取 Kingman 具体构造）**：
与 `Phylo.Stat.CASTERGeneTree.jc69_caster_statisticallyConsistent` 逐条同形，
只是把假设参数 `(S : MSCTopoSym Θ)` **换成** ★★★ `kingmanMSCTopoSym`。

结论：最大化 CASTER 得分的估计量最终把唯一的 quartet 判成真拓扑 `ab|cd`。 -/
theorem jc69_caster_statisticallyConsistent_kingman
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hf_int : Integrable jc69PropADataK.f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ → 0 < jc69PropADataK.f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * jc69PropADataK.A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep jc69PropADataK
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent kingmanMSCTopoSym ν hdeep jc69PropADataK
    hf_int hf_pos hpos hint emp hconv hE

/-- ★★★ **JC69 下 CASTER 恢复真物种树的拓扑**（**树级**）：
把 ★★★ `jc69_caster_statisticallyConsistent_kingman` 的结论经
`Phylo.Stat.CASTERInstances.tree_iso_of_topo_consistency` 升级为「估计量的树与真树同构」。 -/
theorem jc69_recovers_true_tree_kingman
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hf_int : Integrable jc69PropADataK.f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ → 0 < jc69PropADataK.f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo, kingmanMSCTopoSym.τd θ T' * jc69PropADataK.A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep jc69PropADataK
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n))
    (e : QuartetLabel (Fin 4))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd)
    (jc69_caster_statisticallyConsistent_kingman ν hdeep hpos hf_int hf_pos hint
      emp hconv hE)
    hTtrue hQt htrue_class hreal

/-! ## 3. LM1 -/

/-- LM1 的命题 A 数据搬到 `KingmanΘ` 上。 -/
abbrev lm1PropADataK (π : Fin 4 → ℝ)
    (hsum : Phylo.CASTERLM1.piR π + Phylo.CASTERLM1.piY π = 1) (lam : ℝ) :
    PropAData KingmanΘ :=
  transportPropAData Prod.fst (Phylo.CASTERLM1.lm1PropAData π hsum lam)

/-- ★★★ **LM1 的 CASTER 定理 1（MSC 侧取 Kingman 具体构造）**：
与 `Phylo.Stat.CASTERInstances.lm1_caster_statisticallyConsistent` 逐条同形，
`S` 换成 ★★★ `kingmanMSCTopoSym`。 -/
theorem lm1_caster_statisticallyConsistent_kingman
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (π : Fin 4 → ℝ) (hsum : Phylo.CASTERLM1.piR π + Phylo.CASTERLM1.piY π = 1) (lam : ℝ)
    (hf_int : Integrable (lm1PropADataK π hsum lam).f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ → 0 < (lm1PropADataK π hsum lam).f θ)
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo,
        kingmanMSCTopoSym.τd θ T' * (lm1PropADataK π hsum lam).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep (lm1PropADataK π hsum lam)
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent kingmanMSCTopoSym ν hdeep
    (lm1PropADataK π hsum lam) hf_int hf_pos hpos hint emp hconv hE

/-- ★★★ **LM1 下 CASTER 恢复真物种树的拓扑**（**树级**）。 -/
theorem lm1_recovers_true_tree_kingman
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (π : Fin 4 → ℝ) (hsum : Phylo.CASTERLM1.piR π + Phylo.CASTERLM1.piY π = 1) (lam : ℝ)
    (hf_int : Integrable (lm1PropADataK π hsum lam).f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ → 0 < (lm1PropADataK π hsum lam).f θ)
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo,
        kingmanMSCTopoSym.τd θ T' * (lm1PropADataK π hsum lam).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep (lm1PropADataK π hsum lam)
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n))
    (e : QuartetLabel (Fin 4))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd)
    (lm1_caster_statisticallyConsistent_kingman ν hdeep π hsum lam
      hf_int hf_pos hpos hint emp hconv hE)
    hTtrue hQt htrue_class hreal

/-! ## 4. F84 -/

/-- F84 的命题 A 数据（**无条件版**）搬到 `KingmanΘ` 上。 -/
abbrev f84PropADataK (pi : Fin 4 → ℝ) (kap : ℝ)
    (hR : Phylo.CASTERF84.piR pi ≠ 0) (hY : Phylo.CASTERF84.piY pi ≠ 0) :
    PropAData KingmanΘ :=
  transportPropAData Prod.fst (Phylo.Stat.CASTERF84PropA.f84PropAData pi kap hR hY)

/-- ★★★ **F84 的 CASTER 定理 1（MSC 侧取 Kingman 具体构造）**：
与 `Phylo.Stat.CASTERF84PropA.f84_caster_statisticallyConsistent` 逐条同形，
`S` 换成 ★★★ `kingmanMSCTopoSym`。

注意两条非退化假设 `hR : π_R ≠ 0` / `hY : π_Y ≠ 0` 落在**参数** `π` 上（不是样本点上）——
这是 F84 命题 A 的三条核恒等式所要求的，与 W8 的无条件化口径一致。 -/
theorem f84_caster_statisticallyConsistent_kingman
    (pi : Fin 4 → ℝ) (kap : ℝ)
    (hR : Phylo.CASTERF84.piR pi ≠ 0) (hY : Phylo.CASTERF84.piY pi ≠ 0)
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hf_int : Integrable (f84PropADataK pi kap hR hY).f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ →
      0 < (f84PropADataK pi kap hR hY).f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo,
        kingmanMSCTopoSym.τd θ T' * (f84PropADataK pi kap hR hY).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep (f84PropADataK pi kap hR hY)
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n)) :
    ∃ N : ℕ, ∀ n ≥ N, IsTrueT (fun _ _ => Topo.ab_cd) (E n) :=
  propAData_caster_statisticallyConsistent kingmanMSCTopoSym ν hdeep
    (f84PropADataK pi kap hR hY) hf_int hf_pos hpos hint emp hconv hE

/-- ★★★ **F84 下 CASTER 恢复真物种树的拓扑**（**树级**）。 -/
theorem f84_recovers_true_tree_kingman
    (pi : Fin 4 → ℝ) (kap : ℝ)
    (hR : Phylo.CASTERF84.piR pi ≠ 0) (hY : Phylo.CASTERF84.piY pi ≠ 0)
    (ν : Measure KingmanΘ) [IsProbabilityMeasure ν]
    (hdeep : MeasurableSet {θ | kingmanMSCTopoSym.deep θ})
    (hpos : 0 < ν {θ | ¬ kingmanMSCTopoSym.deep θ})
    (hf_int : Integrable (f84PropADataK pi kap hR hY).f ν)
    (hf_pos : ∀ θ, ¬ kingmanMSCTopoSym.deep θ →
      0 < (f84PropADataK pi kap hR hY).f θ)
    (hint : ∀ T : Topo, Integrable
      (fun θ => ∑ T' : Topo,
        kingmanMSCTopoSym.τd θ T' * (f84PropADataK pi kap hR hY).A θ T' T) ν)
    (emp : ℕ → TopoWeight (Fin 4))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      TopoClose (emp n)
        (TopoIdeal.ofModel kingmanMSCTopoSym ν hdeep (f84PropADataK pi kap hR hY)
          hf_int hf_pos hpos hint).W ε)
    {E : ℕ → TopoChoice (Fin 4)}
    (hE : ∀ (n : ℕ) (q : TopoChoice (Fin 4)),
      topoScore (emp n) q ≤ topoScore (emp n) (E n))
    (e : QuartetLabel (Fin 4))
    {Ttrue : QuartetTree.{0, 0} (Fin 4)} {Qt : ℕ → QuartetTree.{0, 0} (Fin 4)}
    (hTtrue : Ttrue.tree.IsBinary) (hQt : ∀ n : ℕ, (Qt n).tree.IsBinary)
    (htrue_class : ∀ (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) (Ttrue.q S hS) = Topo.ab_cd)
    (hreal : ∀ (n : ℕ) (S : Finset (Fin 4)) (hS : S.card = 4),
      topoOfSplit (e S hS) ((Qt n).q S hS) = (E n) S hS) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (Qt n).tree Ttrue.tree) :=
  tree_iso_of_topo_consistency (X := Fin 4) e (fun _ _ => Topo.ab_cd)
    (f84_caster_statisticallyConsistent_kingman pi kap hR hY ν hdeep hpos
      hf_int hf_pos hint emp hconv hE)
    hTtrue hQt htrue_class hreal

end Phylo.Stat.MSCInstance

end
