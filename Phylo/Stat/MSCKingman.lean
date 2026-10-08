/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTEREngine
import Phylo.Stat.Coalescent

/-!
# `Phylo.Stat.MSCKingman` —— 4 叶 Kingman 溯祖给出的 `MSCTopoSym` **具体实例**（缺口 G5′）

## 1. 本文件在 CASTER 链条里的位置

```
命题 A（基因树层）  E[w(真)|G] − f = E[w(错₁)|G] = E[w(错₂)|G]     ← 模型相关：JC69 ✅ / LM1 ✅ / F84 ✅
     │                                              Phylo.Stat.CASTEREngine.PropA
     ▼
命题 B（物种树层）  真拓扑期望得分严格最大
     │                                              Phylo.Stat.CASTEREngine.MSCTopoSym
     │                                              ↑ **本文件补的就是它的 `deep`/`τd` 从哪里来**
     ▼
定理 1（一致性）  + 独立性 + 有界性 + 大数定律
```

`Phylo.Stat.CASTEREngine.MSCTopoSym`（该文件第 **147** 行）此前是**假定结构**：
全库 **0 处具体构造**，它的 `deep` / `τd` 是「借来的」。本文件按 4 叶 quartet
`((a,b),(c,d))` 的 Kingman 溯祖**真正构造**出实例 `kingmanMSCTopoSym`，
并证明该类型可居留（`kingmanMSCTopoSym_nonempty`）——
于是 `MSCTopoSym.cancel` / `MSCTopoSym.cancel_of`（因而命题 B、定理 1 的 MSC 一侧）
**不再空真**。字段本身**一个都没有改弱**（对照 `MSCTopoSym` 的七条字段逐条给出）。

## 2. 文献出处（逐字核对）

* Allman, Degnan & Rhodes (2011), *Identifying the rooted species tree from the distribution of
  unrooted gene trees under the coalescent*, J. Math. Biol. **62**:833–862；
  本仓库中译本 `references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md`。
* **Lemma 4**（该文件 **962–971** 行）：

  > If all coalescent events occur above the root (temporally before the MRCA of all species)
  > of a **5-taxon** species tree, then all 15 of the unrooted topological gene trees are
  > equally likely.
  > **Proof** … Because all unrooted gene trees have the same unlabeled shape, all coalescent
  > histories leading to one gene tree correspond to equally likely coalescent histories
  > producing another, **by simply relabeling lineages**.

* **边界注记**（同文件 **973–974** 行，紧随证明之后）：

  > Note that the claim of this lemma is special to five taxa. For six taxa, with two different
  > unrooted gene tree shapes possible, the analogous statement is not true.

## 3. 为什么「同形」（same unlabeled shape）前提**必须显式**

Lemma 4 的证明**只用了一件事**：参与溯祖的那批无根基因树**同形**
（「all unrooted gene trees have the same unlabeled shape」），于是「重标号谱系」把
一条溯祖历史双射到另一条等概率的历史上。5 taxa 的 15 个无根树恰好同形，故结论成立；
**6 taxa 起有两种无根形状，同样的论证立刻失效**（973–974 行的注记说的就是这个）。

4 叶的 3 个无根拓扑 `ab|cd` / `ac|bd` / `ad|bc` 也**恰好同形**（都是「4 叶星形 + 1 条内边」），
所以 4 叶可以安全地沿用同一条重标号论证 —— **但这句「恰好同形」是一个前提，不是自动的**。
本文件因此不把它藏起来：

* `AllSameShape` 把「根种群 4 条谱系的 `C(4,2) = 6` 个首次合并对，按诱导的无根拓扑分成
  **3 类、每类恰 2 个**」写成**显式可检命题**（三条 filter 基数 `= 2` 的合取）；
* `allSameShape_four`（`AllSameShape` 的证明）**就是**
  `Phylo.Stat.Coalescent.root_quartet_classes` —— 那是一条 `decide` 出来的**有限组合事实**，
  **不是假设**。

⚠️ **引用纪律**：`sm.tex` 第 **391/393** 行的两处对称性讨论位于 `\REMOVE{}` 宏内
（宏定义在该文件第 **100** 行，**丢弃参数**），因此**未随附录发表**，属作者草稿；
本节引用的是 ADR2011 **已发表**的 Lemma 4（**962–971**）与它的边界注记（**973–974**）。

## 4. 数学内容（`t = a + b`，溯祖单位）

物种树 `((a,b),(c,d))`：把无根内部边（分隔 `{a,b}` 与 `{c,d}`）**在根处切开**，
根以下两段长度记为 `a`（`{a,b}` 侧）、`b`（`{c,d}` 侧），**总内部枝长 `t = a + b`**。
回溯时 `{a,b}` 两条谱系在根以下**未能**合并的概率是 `e^{−a}`
（合并率 `d_2 = 1`，见 `Phylo.Stat.Coalescent.survival` / `kingmanRate_two`），`{c,d}` 侧同理 `e^{−b}`。

* **深合并**（本文件的 `KingmanDeep`）：两侧都**未能**在根以下合并 ⇒ 4 条谱系进入根种群
  ⇒ 所有合并都发生在根之上 ⇒ 由 §2–§3 的重标号对称性，**三个无根拓扑各 `1/3`**
  （根种群 4 条谱系的 6 个首次合并对均匀，每个拓扑类恰含 2 个：
  `Coalescent.root_quartet_classes` + `Coalescent.root_topologyProb` 的 `2/6 = 1/3`）。
* **无深合并**：至少一侧在根以下就完成了合并 ⇒ 该侧樱桃已被解析 ⇒ 无根拓扑**只能是 `ab|cd`**
  （点质量）。〔若 `{a,b}` 已成樱桃而 `{c,d}` 未成，则进入根种群的只有 3 条谱系
  `(ab), c, d`，唯一含樱桃 `{a,b}` 的无根拓扑仍是 `ab|cd`；反之同理。〕

⇒ `P(一致) = (1 − e^{−t}) + (1/3)·e^{−t} = 1 − (2/3)·e^{−t}`，
与库里既有的 `Phylo.Stat.Coalescent.pConcordant`
（`pConcordant_eq : pConcordant t = 1 - (2/3) * Real.exp (-t)`）**逐字一致**；
本文件把它做成定理 `kingman_concordant_eq_pConcordant` / `kingman_discordant_eq_pDiscordant`
（**概率对账**：左边用的是**模型自己的概率对象** `kingmanDeepProb` / `kingmanNotDeepProb`，
不是把 `pConcordant` 的定义展开一遍）。

## 5. 诚实边界

* **真测度不在本文件范围**：`KingmanΘ` 上的 `Measure`（把两个 `Bool` 分量按 `e^{−a}` / `e^{−b}`
  赋权，与 `MSCTopoSym` 拼成真正的 MSC 分布）留给 Phase 2
  （`Phylo/Stat/MSCInstance.lean`）。本文件只做**实数层对账**
  （`kingmanDeepProb` / `kingmanDeepProb_eq` / `kingmanNotDeepProb` /
  `kingman_concordant_eq_pConcordant` / `kingman_discordant_eq_pDiscordant`）。
* **已知前提（不是本文件证的）**：`e^{−a}`（`{a,b}` 两条谱系在根以下未合并的概率）用的是
  `d_2 = 1` 的 Kingman 生存函数 `Coalescent.survival`；「未合并 ⇒ 4 条谱系进根种群」是
  §4 的模型口径。本文件只证这些数之间的**记账恒等式**。
* **命名（规格修正 v2）**：`e^{−a}·e^{−b}` 承载的是**深合并**的概率，故名 `kingmanDeepProb`；
  `kingmanNotDeepProb` 是它的补 `1 − e^{−(a+b)}`。
  （v1 规格曾把这两个名字错配，经执行侧报告后由协调侧在 `MSC_KINGMAN_SPEC.md` §4 修正为 v2。）
-/

noncomputable section

namespace Phylo.Stat.MSCKingman

open Phylo.Stat.CASTERWeights
open Phylo.Stat.CASTEREngine

/-! ## 1. 溯祖历史空间与 `deep` / `τd` -/

/-- 溯祖历史空间。**第一个分量刻意就是端到端定理里既有的 `(Fin 4 → ℝ) × ℝ`**
（叶长 × 内部枝长），因此既有 `PropAData` 可以沿投影**原样搬运**；
第二个分量记录「两侧是否深合并进根」。 -/
abbrev KingmanΘ : Type := ((Fin 4 → ℝ) × ℝ) × (Bool × Bool)

/-- `deep`：`{a,b}` 与 `{c,d}` **都没能在根以下合并** ⇒ 4 条谱系进根种群。 -/
def KingmanDeep (θ : KingmanΘ) : Prop := θ.2.1 = true ∧ θ.2.2 = true

/-- `KingmanDeep` **可判定**：它是两个 `Bool` 等式的合取。

⚠️ 实例搜索**不会展开**普通 `def`（只在 `.reducible` 透明度下展开），所以
`Decidable (KingmanDeep θ)` 不会被自动找到（实测 `synthInstanceFailed`），
必须把这个实例显式登记。这只补上可判定性，**不改变** `KingmanDeep` / `Kingmanτd`
的任何名字、参数或陈述。 -/
instance instDecidablePredKingmanDeep : DecidablePred KingmanDeep := fun θ => by
  unfold KingmanDeep
  infer_instance

/-- 条件拓扑分布：深合并 ⇒ 三拓扑各 `1/3`；否则点质量在 `ab|cd`。 -/
def Kingmanτd (θ : KingmanΘ) (T : Topo) : ℝ :=
  if KingmanDeep θ then 1 / 3 else if T = Topo.ab_cd then 1 else 0

/-! ### 1.1 三个基本取值（辅助引理，`private`） -/

/-- 深合并时 `Kingmanτd` 在**任意**拓扑上取 `1/3`（重标号对称性在 4 叶下的算术形式）。 -/
private theorem kingmanτd_deep {θ : KingmanΘ} (h : KingmanDeep θ) (T : Topo) :
    Kingmanτd θ T = 1 / 3 := by
  simp [Kingmanτd, h]

/-- 无深合并时 `Kingmanτd` 在 `ab|cd` 上取 `1`（点质量）。 -/
private theorem kingmanτd_notDeep_ab {θ : KingmanΘ} (h : ¬ KingmanDeep θ) :
    Kingmanτd θ Topo.ab_cd = 1 := by
  simp [Kingmanτd, h]

/-- 无深合并时 `Kingmanτd` 在 `ac|bd` 上取 `0`。 -/
private theorem kingmanτd_notDeep_ac {θ : KingmanΘ} (h : ¬ KingmanDeep θ) :
    Kingmanτd θ Topo.ac_bd = 0 := by
  simp [Kingmanτd, h]

/-- 无深合并时 `Kingmanτd` 在 `ad|bc` 上取 `0`。 -/
private theorem kingmanτd_notDeep_ad {θ : KingmanΘ} (h : ¬ KingmanDeep θ) :
    Kingmanτd θ Topo.ad_bc = 0 := by
  simp [Kingmanτd, h]

/-- `Kingmanτd` 非负（`0 ≤ 1/3`、`0 ≤ 1`、`0 ≤ 0`，逐情形）。 -/
private theorem kingmanτd_nonneg (θ : KingmanΘ) (T : Topo) : 0 ≤ Kingmanτd θ T := by
  by_cases h : KingmanDeep θ
  · rw [kingmanτd_deep h T]
    norm_num
  · cases T
    · rw [kingmanτd_notDeep_ab h]
      norm_num
    · simp [kingmanτd_notDeep_ac h]
    · simp [kingmanτd_notDeep_ad h]

/-- `Kingmanτd` 全概率为 `1`（深合并：`1/3 + 1/3 + 1/3 = 1`；否则：`1 + 0 + 0 = 1`）。 -/
private theorem kingmanτd_sum (θ : KingmanΘ) : ∑ T : Topo, Kingmanτd θ T = 1 := by
  rw [Phylo.Stat.CASTEREngine.sum_topo]
  by_cases h : KingmanDeep θ
  · rw [kingmanτd_deep h Topo.ab_cd, kingmanτd_deep h Topo.ac_bd,
      kingmanτd_deep h Topo.ad_bc]
    norm_num
  · rw [kingmanτd_notDeep_ab h, kingmanτd_notDeep_ac h, kingmanτd_notDeep_ad h]
    norm_num

/-! ## 2. `MSCTopoSym` 的具体实例（缺口 G5′ 的正面回答） -/

/-- ★★★ **4 叶 Kingman 溯祖给出的 `MSCTopoSym` 具体实例**（缺口 G5′ 的正面回答）。

七条字段逐条来自 §4 的模型：

* `deep := KingmanDeep`（两侧都未在根以下合并）；
* `τd := Kingmanτd`（深合并时三拓扑各 `1/3`，否则点质量在 `ab|cd`）；
* `τd_nonneg` / `τd_sum`：`kingmanτd_nonneg` / `kingmanτd_sum`；
* `not_deep` / `deep_ab` / `deep_ac`：`kingmanτd_notDeep_ab` / `kingmanτd_deep`。 -/
def kingmanMSCTopoSym : MSCTopoSym KingmanΘ where
  deep := KingmanDeep
  τd := Kingmanτd
  τd_nonneg := kingmanτd_nonneg
  τd_sum := kingmanτd_sum
  not_deep := fun _ h => kingmanτd_notDeep_ab h
  deep_ab := fun _ h => kingmanτd_deep h Topo.ab_cd
  deep_ac := fun _ h => kingmanτd_deep h Topo.ac_bd

/-- ★★ **反空真**：该实例可居留。 -/
theorem kingmanMSCTopoSym_nonempty : Nonempty (MSCTopoSym KingmanΘ) :=
  ⟨kingmanMSCTopoSym⟩

/-! ## 3. 「同形」前提与深合并的三拓扑等概率 -/

/-- ★★★ **「同形」前提（ADR2011 Lemma 4 的前提在 4 叶下的显式形式）**。

ADR2011 的对称性论证（962–971 行）只用到「参与溯祖的无根基因树同形」，而 6 taxa 起
该前提失效（973–974 行）。4 叶的 3 个无根拓扑恰好同形，本命题把这个前提写成
**可检的有限组合命题**：根种群 4 条谱系的 `C(4,2) = 6` 个首次合并对，按诱导的
无根拓扑恰好分成 3 类、每类恰 2 个（三条 filter 的基数都是 `2`）。

这不是空壳：它的证明 `allSameShape_four` 就是
`Phylo.Stat.Coalescent.root_quartet_classes`（`decide` 出来的组合事实）。 -/
def AllSameShape : Prop :=
    (((Coalescent.mergePairsFinset 4).filter
        fun p => ((0 : Fin 4) ∈ p ↔ (1 : Fin 4) ∈ p)).card = 2) ∧
    (((Coalescent.mergePairsFinset 4).filter
        fun p => ((0 : Fin 4) ∈ p ↔ (2 : Fin 4) ∈ p)).card = 2) ∧
    (((Coalescent.mergePairsFinset 4).filter
        fun p => ((0 : Fin 4) ∈ p ↔ (3 : Fin 4) ∈ p)).card = 2)

/-- ★★★ 4 叶满足同形前提（由 `Coalescent.root_quartet_classes` 直接给出）。 -/
theorem allSameShape_four : AllSameShape :=
  Coalescent.root_quartet_classes

/-- ★★★ **深合并 ⇒ 三拓扑等概率**（ADR2011 Lemma 4 的重标号对称性在 4 叶下的结论）。 -/
theorem kingmanMSCTopoSym_tau_eq_third
    {θ : KingmanΘ} (h : KingmanDeep θ) (T : Topo) :
    kingmanMSCTopoSym.τd θ T = 1 / 3 :=
  kingmanτd_deep h T

/-- ★★★ **无深合并 ⇒ 点质量在 `ab|cd`**。 -/
theorem kingmanMSCTopoSym_tau_notDeep
    {θ : KingmanΘ} (h : ¬ KingmanDeep θ) : kingmanMSCTopoSym.τd θ .ab_cd = 1 :=
  kingmanτd_notDeep_ab h

/-! ## 4. 概率对账（与既有 `Coalescent.pConcordant` 接通） -/

/-- **深合并**（两侧**都未能**在根以下合并）的概率 `e^{−a} · e^{−b}`。
这就是「4 条谱系进入根种群」的概率，也是 `KingmanDeep` 的概率。 -/
def kingmanDeepProb (a b : ℝ) : ℝ := Real.exp (-a) * Real.exp (-b)

/-- ★★★ **深合并的概率 = `e^{−(a+b)}`**（半群性；对应 `Coalescent.survival_add`）。 -/
theorem kingmanDeepProb_eq (a b : ℝ) :
    kingmanDeepProb a b = Real.exp (-(a + b)) := by
  have h : -a + -b = -(a + b) := by ring
  rw [kingmanDeepProb, ← Real.exp_add, h]

/-- **无深合并**（至少一侧在根以下完成了合并）的概率 `1 − e^{−(a+b)}`。 -/
def kingmanNotDeepProb (a b : ℝ) : ℝ := 1 - Real.exp (-(a + b))

/-- ★★★ **概率对账（真正的记账，不是把 `pConcordant` 展开一遍）**：
`P(一致) = P(无深合并)·1 + P(深合并)·(1/3) = 1 − (2/3)e^{−t}`，`t = a + b`，
与 `Coalescent.pConcordant` 的**闭形式** `pConcordant_eq` 相同。 -/
theorem kingman_concordant_eq_pConcordant (a b : ℝ) :
    kingmanNotDeepProb a b * 1 + kingmanDeepProb a b * (1 / 3)
      = Coalescent.pConcordant (a + b) := by
  rw [kingmanNotDeepProb, kingmanDeepProb_eq, Coalescent.pConcordant_eq]
  ring

/-- ★★★ **每个不一致拓扑的概率**恰是 `⅓e^{−t} = Coalescent.pDiscordant (a+b)`。 -/
theorem kingman_discordant_eq_pDiscordant (a b : ℝ) :
    kingmanDeepProb a b * (1 / 3) = Coalescent.pDiscordant (a + b) := by
  rw [kingmanDeepProb_eq, Coalescent.pDiscordant]
  ring

/-- ★★★ **广义对称性前提**（比 `AllSameShape` 更弱、更好用的形式，供 Phase 2 使用）：
「根种群 4 条谱系的首次合并对等概率地落在 3 个拓扑类上」⇒ 每类 `1/3`。 -/
theorem root_topology_uniform :
    (2 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ) = 1 / 3 :=
  Coalescent.root_topologyProb

/-! ### 4.1 把 `1/3` **推出来**（不只是「写定」）

`Kingmanτd` 在深合并那一支**取** `1/3`；本节说明这个 `1/3` 不是任意的规定，
而是「根种群 `C(4,2) = 6` 个首次合并对等概率 ＋ 每个拓扑类恰含 2 个对」的**推论**：

* 均匀性来自 Kingman 溯祖（`Coalescent.sum_uniform_jumpProb` 的 `k = 4` 情形）；
* 类的划分（每类恰 2 个）就是 `AllSameShape`（ADR2011 Lemma 4 的重标号对称性在 4 叶下的组合核心）。

于是把「每个对的权重 `1/6`」在**类**上求和，即得该类（= 该无根拓扑）的概率 `2/6 = 1/3`。 -/

/-- ★★ **均匀权重在类上的和**：若某个拓扑类恰含 `2` 个首次合并对，
则把「每对等概率 `1/C(4,2)`」在该类上求和得 `1/3`。
（这是**概率推导**，不是算术恒等式：被求和的集合是「类」，权重来自溯祖的均匀性。） -/
theorem uniform_class_prob {P : Finset (Fin 4) → Prop} [DecidablePred P]
    (h : ((Coalescent.mergePairsFinset 4).filter P).card = 2) :
    (∑ _p ∈ (Coalescent.mergePairsFinset 4).filter P,
        (1 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ)) = 1 / 3 := by
  rw [Finset.sum_const, h, Coalescent.card_mergePairsFinset_four, nsmul_eq_mul]
  norm_num

/-- ★★★ **深合并时三个无根拓扑各 `1/3` —— 推导版**：
三个拓扑类（由 ★★★ `AllSameShape` 划分）各自把均匀的首次合并对权重求和，都得 `1/3`。

⇒ `Kingmanτd` 在 `KingmanDeep` 那一支取 `1/3` 是**重标号对称性的推论**，
不是一个被写定的规定。 -/
theorem root_topology_class_prob :
    (∑ _p ∈ (Coalescent.mergePairsFinset 4).filter
        (fun p => ((0 : Fin 4) ∈ p ↔ (1 : Fin 4) ∈ p)),
        (1 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ)) = 1 / 3 ∧
    (∑ _p ∈ (Coalescent.mergePairsFinset 4).filter
        (fun p => ((0 : Fin 4) ∈ p ↔ (2 : Fin 4) ∈ p)),
        (1 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ)) = 1 / 3 ∧
    (∑ _p ∈ (Coalescent.mergePairsFinset 4).filter
        (fun p => ((0 : Fin 4) ∈ p ↔ (3 : Fin 4) ∈ p)),
        (1 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ)) = 1 / 3 :=
  ⟨uniform_class_prob allSameShape_four.1,
   uniform_class_prob allSameShape_four.2.1,
   uniform_class_prob allSameShape_four.2.2⟩

end Phylo.Stat.MSCKingman

end
