/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCKingman
import Phylo.Stat.NJstWitness
import Phylo.Stat.CASTERTopoSplit
import Phylo.QuartetInhabitation

/-!
# `Phylo.Stat.MSCProof` —— 把 MSC 的 quartet 分布**由 Kingman 溯祖构造出来**

`Phylo/Stat/MSC.lean` 顶部的决策是「**先把 MSC 公理化**」并把「证明 MSC」另立为课题
`Phylo.Stat.MSCProof`。**本文件就是开工做那个课题**：不再是「给定一个 `MSCFreq`」，
而是**构造**一个 —— 它的 quartet 频率**真的**是 4 叶 Kingman 溯祖算出来的分布。

## 1. 4 叶 MSC 的分布（文献）

物种树 `((a,b),(c,d))`，内部枝长 `t`（溯祖单位，即 `2N` 世代）。两条谱系 `A,B` 在内部枝内
合并的概率 `1 − e^{−t}`（`d₂ = 1` 的指数等待时间）；否则 4 条谱系一起进入根种群，
首次合并均匀地取 `C(4,2) = 6` 个对之一，每个 quartet 拓扑恰由 **2** 个对诱导 ⟹ `2/6 = 1/3`。

出处：`references/md/AllmanDegnanRhodes2011_IdentifyingRootedSpeciesTree.md` 第 **356–360** 行
（`p₁ = 1 − (2/3)exp(−t)`、`p₂ = p₃ = (1/3)exp(−t)`，Nei 1987）；
`references/md/Kingman1982_TheCoalescent.md` 第 **129–137** 行（(1.7)：`τ_k ~ Exp(d_k)`，
`d_k = ½k(k−1)`）；`Coalescent.root_quartet_classes` 在 `Phylo/Stat/Coalescent.lean`
第 **286–290** 行；根种群均匀性的**推导版** `root_topology_class_prob` 在
`Phylo/Stat/MSCKingman.lean` 第 **301–313** 行。

## 2. 本文件交付

* ★★★ `rootTopoProb` —— 根种群的拓扑概率 `1/3` 是**推导值**（跳链均匀权重在拓扑**类**上的
  求和，`MSCKingman.root_topology_class_prob`），**不是写定的常数**（正面回应 W9 的批评点）；
* ★★★ `mscConcordant` / `mscDiscordant` —— **由溯祖等待时间拼出**的 MSC 权重
  （`firstMergeCDF 2 t + survival 2 t · rootTopoProb`），并证其闭形式 `1 − ⅔e^{−t}` 与 `⅓e^{−t}`；
* ★★★ `mscQuartetFreq` —— `Fin 4` 上的**具体** `QuartetFreq`，`p` 就是 MSC 权重
  （`p_nonneg` / `p_sum_one` / `p_swap` **三条都真证**）；
* ★★★ `mscQuartetTree` —— `Fin 4` 上的**具体** `QuartetTree`（真树 = `NJstWitness.T1234`，
  各边权 `1` 的 `01|23` 二叉树），`q_card` / `displays` 都真证；
* ★★★ `mscFreqFin4` + ★★ `mscFreqFin4_nonempty` —— `MSCFreq (Fin 4)` 的**可居留实例**
  ⇒ `MSCFreq` 不再是「只被假设的结构」；
* ★★★ `mscWeights_majorizes` —— 把 `MSCFreq.majorizes` 这条**核心不等式**表述成
  **关于权重的定理**（对任意 `t > 0`）。
* ★★★ **§6 推广**：`mscQuartetFreqOf` —— **任意有限 `X`**、任意 4-元集的真 quartet 选择 `q`
  （含 `q_card`）⇒ 具体 `QuartetFreq X`（三条字段全真证），配上
  `mscQuartetFreqOf_majorizes`（任意 `X` 的 `majorizes`）。
  关键计数 `card_splits_two`（任意 4-元集上 `2|2` 有向 split 恰 6 个）、
  `card_eq_or_swap`（`{q, q.swap}` 恰 2 个）、`card_other_two`（其余 `2|2` 恰 4 个）。

## 3. 关键记账（为什么是 `/2`）

库内 `Split α = KPartition α 2` 把两侧**有序化**（`sideA` / `sideB`），故每个**无向**
quartet 拓扑对应**两个**有向 split。因此本文件里每个有向 split 拿「无向概率的一半」：
一致拓扑的两个有向 split 合计 `mscConcordant t`，两个不一致拓扑的四个有向 split 合计
`2 · mscDiscordant t`，`1|3` 的 split 拿 `0`。合计 `= 1` 即 `mscConcordant_add_two`。
这与库内 `Coalescent.directed_quartetWeights_sum` 的记账完全一致。

## 4. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| `p_nonneg` / `p_sum_one` / `p_swap` | **已证**（`mscP_*`；`2\|2` 有向 split 与 `Fin 4` 二元子集的计数是 `decide` 可判的纯组合事实） |
| `q_card` / `displays` | **已证**（`qSplit_*`，真树用 `NJstWitness.T1234`） |
| `majorizes` | **已证**（它是 `mscDiscordant_lt_mscConcordant` 的推论，**不是**被假设的字段） |
| `X = Fin 4` **之外**的 `X`：**频率表** | ✅ **已构造**（§6 ★★★ `mscQuartetFreqOf`：任意有限 `X` ＋任意「每个 4-元集的真 quartet 选择 `q`」（含 `q_card`）⇒ `QuartetFreq X`，`p_nonneg`/`p_sum_one`/`p_swap` **全真证**；`mscQuartetFreqOf_majorizes` 给出任意 `X` 的 `majorizes`） |
| `X = Fin 4` 之外的 **`MSCFreq`（含真树）** | ❌ **未构造**：剩下的是**纯组合**的「binary 树上每个 4-元集的 quartet 选择」接口（闸门见 `Phylo/Stat/QuartetDecides.lean`）—— **不再是溯祖/概率问题** |
| `1 − e^{−t}` 是**测度层**的概率 | ⚠️ **本文件用的是实数层的 `Coalescent.firstMergeCDF`**；把它换成 `ProbabilityTheory.expMeasure` 的测度层陈述属 W10b（`Phylo/Stat/KingmanCoalescent.lean`），**不在本文件** |
| 跳链的**绝对分布 (2.2)** | 属 W10a（`Phylo/Stat/KingmanJumpChain.lean`），**不在本文件** |
| `MSCSampling.converges`（大数定律） | ❌ 仍公理化（W10d）；本文件**不**声称去掉它 |
-/

noncomputable section

open Classical

universe u v

namespace Phylo.Stat.MSCProof

/-- `Fin 4` 上恰有 `4` 个元素的子集只能是全集。 -/
theorem eq_univ_of_card_four (S : Finset (Fin 4)) (hS : S.card = 4) : S = Finset.univ := by
  refine Finset.eq_of_subset_of_card_le (Finset.subset_univ S) ?_
  rw [Finset.card_univ, Fintype.card_fin, hS]

theorem mem_of_card_four (S : Finset (Fin 4)) (hS : S.card = 4) (x : Fin 4) : x ∈ S := by
  rw [eq_univ_of_card_four S hS]; exact Finset.mem_univ x

/-! ## 1. 由溯祖等待时间给出的 MSC 权重 -/

/-- ★★★ **根种群的拓扑概率 `1/3` 是「推导值」而不是「写定的常数」**：
它是**跳链均匀权重** `1/C(4,2)` 在「`0,1` 同类」这一拓扑**类**上的求和
（`C(4,2) = 6` 个首次合并对按拓扑分成 3 类、每类恰 2 个 —— K82 (2.2) 的均匀性 ＋
ADR2011 Lemma 4 的重标号对称性在 4 叶下的组合内容）。

⚠️ 这与 W9 被指出的问题**正面相对**：W9 的 `1/3` 是 `Kingmanτd` 的**定义**；
这里它是 `MSCKingman.root_topology_class_prob` 的**应用**（一个真求和）。 -/
noncomputable def rootTopoProb : ℝ :=
  ∑ _p ∈ (Coalescent.mergePairsFinset 4).filter
      (fun p => ((0 : Fin 4) ∈ p ↔ (1 : Fin 4) ∈ p)),
    (1 : ℝ) / ((Coalescent.mergePairsFinset 4).card : ℝ)

/-- ★★★ 该求和恰为 `1/3`（`MSCKingman.root_topology_class_prob` 的第一个合取项）。 -/
theorem rootTopoProb_eq_third : rootTopoProb = 1 / 3 :=
  Phylo.Stat.MSCKingman.root_topology_class_prob.1

/-- ★★★ **一致（concordant）quartet 的概率，由溯祖等待时间拼出**：
`P(A,B 在内部枝内合并) + P(未合并) · P(根种群给出 01|23) = (1 − e^{−t}) + e^{−t} · (1/3)`，
其中 `1/3` 是 `rootTopoProb`（**推导值**，见上）。
与闭形式 `1 − ⅔e^{−t}` 相等见 `mscConcordant_closed`。 -/
def mscConcordant (t : ℝ) : ℝ :=
  Coalescent.firstMergeCDF 2 t + Coalescent.survival 2 t * rootTopoProb

/-- ★★★ **每个不一致 quartet 的概率**：`P(未在内部枝合并) · ⅓ = ⅓e^{−t}`。 -/
def mscDiscordant (t : ℝ) : ℝ := Coalescent.survival 2 t * rootTopoProb

/-- `mscConcordant` 就是库内既有的 `Coalescent.pConcordant`。 -/
theorem mscConcordant_eq (t : ℝ) : mscConcordant t = Coalescent.pConcordant t := by
  rw [mscConcordant, rootTopoProb_eq_third, Coalescent.pConcordant_eq_kingman, mul_comm]

/-- `mscDiscordant` 就是库内既有的 `Coalescent.pDiscordant`。 -/
theorem mscDiscordant_eq (t : ℝ) : mscDiscordant t = Coalescent.pDiscordant t := by
  rw [mscDiscordant, rootTopoProb_eq_third, Coalescent.pDiscordant_eq_survival, mul_comm]

/-- ★★ **一致概率的闭形式** `1 − ⅔e^{−t}`。 -/
theorem mscConcordant_closed (t : ℝ) :
    mscConcordant t = 1 - (2 / 3) * Real.exp (-t) := by
  rw [mscConcordant_eq]; exact Coalescent.pConcordant_eq t

/-- ★★★ **全概率为 `1`**：一致 + 两个不一致 = `1`。 -/
theorem mscConcordant_add_two (t : ℝ) : mscConcordant t + 2 * mscDiscordant t = 1 := by
  rw [mscConcordant_eq, mscDiscordant_eq, Coalescent.pConcordant_eq_one_sub_two_pDiscordant]
  ring

/-- `t > 0` 时一致概率严格为正。 -/
theorem mscConcordant_pos {t : ℝ} (ht : 0 < t) : 0 < mscConcordant t := by
  rw [mscConcordant_closed]
  have h : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- 不一致概率恒为正。 -/
theorem mscDiscordant_pos (t : ℝ) : 0 < mscDiscordant t := by
  rw [mscDiscordant]
  exact mul_pos (Coalescent.survival_pos 2 t) (by rw [rootTopoProb_eq_third]; norm_num)

/-- `t ≥ 0` 时一致概率非负。 -/
theorem mscConcordant_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mscConcordant t := by
  rw [mscConcordant_eq]; exact Coalescent.pConcordant_nonneg ht

/-- ★★★ `t > 0` 时不一致概率**严格小于**一致概率（`MSCFreq.majorizes` 的全部解析内容）。 -/
theorem mscDiscordant_lt_mscConcordant {t : ℝ} (ht : 0 < t) :
    mscDiscordant t < mscConcordant t := by
  rw [mscDiscordant_eq, mscConcordant_eq]
  exact Coalescent.pDiscordant_lt_pConcordant ht

/-! ## 2. `Fin 4` 上的 quartet 侧（`Split ↥S` 的计数） -/

/-- `↥(univ : Finset (Fin 4))` 的简写：**`Fin 4` 的 `4` 个元素**。 -/
abbrev U : Type := ↥(Finset.univ : Finset (Fin 4))

/-- `r : Split ↥S` 的 `sideA` 在 `Fin 4` 里的「实际元素」。 -/
def sideA4 {S : Finset (Fin 4)} (r : Split ↥S) : Finset (Fin 4) :=
  r.sideA.image (Function.Embedding.subtype fun x => x ∈ S)

theorem card_sideA4 {S : Finset (Fin 4)} (r : Split ↥S) :
    (sideA4 r).card = r.sideA.card :=
  Finset.card_image_of_injective _ (Function.Embedding.subtype _).injective

/-- ★ **与真树 `01|23` 一致**（有向 split 层面）：`sideA` 的像是 `{0,1}` 或 `{2,3}`。
用「`0`、`1` 同在或同不在」＋「`sideA` 恰 `2` 元」刻画 —— 这形式在 `swap` 下**不变**。 -/
abbrev isConc (S : Finset (Fin 4)) (r : Split ↥S) : Prop :=
  r.sideA.card = 2 ∧ ((0 : Fin 4) ∈ sideA4 r ↔ (1 : Fin 4) ∈ sideA4 r)

/-- 把 `Fin 4` 的子集**拉回**到 `↥(univ : Finset (Fin 4))`。 -/
def liftU (T : Finset (Fin 4)) : Finset U :=
  Finset.univ.filter fun x => (x : Fin 4) ∈ T

theorem image_liftU (T : Finset (Fin 4)) :
    (liftU T).image (Function.Embedding.subtype fun x => x ∈ (Finset.univ : Finset (Fin 4)))
      = T := by
  ext x
  simp only [liftU, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, Finset.mem_univ x⟩, hx, rfl⟩

theorem card_liftU (T : Finset (Fin 4)) : (liftU T).card = T.card := by
  rw [← Finset.card_image_of_injective _ (Function.Embedding.subtype _).injective, image_liftU]

/-- ★★ **`sideA4` 完全决定 `sideA`**：`r.sideA` 就是 `sideA4 r` 的拉回。 -/
theorem sideA_eq_liftU (r : Split U) :
    r.sideA = liftU (sideA4 (S := Finset.univ) r) := by
  ext x
  simp only [liftU, Finset.mem_filter, Finset.mem_univ, true_and, sideA4, Finset.mem_image,
    Function.Embedding.subtype_apply]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [h] at hy

/-- `sideA4` 在 `↥univ` 上**单射**（故可用来数 split）。 -/
theorem sideA4_inj {r r' : Split U}
    (h : sideA4 (S := Finset.univ) r = sideA4 (S := Finset.univ) r') : r = r' := by
  apply Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq
  rw [sideA_eq_liftU r, sideA_eq_liftU r', h]

theorem sideA4_splitOf_liftU (T : Finset (Fin 4))
    (h1 : (liftU T).Nonempty) (h2 : (liftU T)ᶜ.Nonempty) :
    sideA4 (S := Finset.univ) (Phylo.splitOf (liftU T) h1 h2) = T := by
  unfold sideA4
  rw [Phylo.splitOf_sideA]
  exact image_liftU T

/-- ★★ **核心计数引理**：`2|2` 的（有向）split 与 `Fin 4` 的**二元子集**一一对应
（`r ↦ sideA4 r`），故任何只依赖 `sideA4` 的谓词在两边的计数相同。 -/
theorem card_filter_two (P : Finset (Fin 4) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Split U)).filter
        (fun r => r.sideA.card = 2 ∧ P (sideA4 (S := Finset.univ) r))).card
      = (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter P).card := by
  set s : Finset (Split U) := (Finset.univ : Finset (Split U)).filter
    (fun r => r.sideA.card = 2 ∧ P (sideA4 (S := Finset.univ) r)) with hs
  have hinj : Set.InjOn (fun r : Split U => sideA4 (S := Finset.univ) r) ↑s := by
    intro r1 _ r2 _ h
    exact sideA4_inj h
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext T
  constructor
  · intro hT
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hT
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨hr2, hPr⟩ := hr
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, by rw [card_sideA4]; exact hr2⟩, hPr⟩
  · intro hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨-, hcard⟩, hP⟩ := hT
    have h1 : (liftU T).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have hc := card_liftU T
      rw [h, Finset.card_empty] at hc
      omega
    have h2 : (liftU T)ᶜ.Nonempty := by
      apply Phylo.compl_nonempty_of_ne_univ
      intro h
      have hc := card_liftU T
      rw [h, Finset.card_univ, Fintype.card_coe, Finset.card_univ, Fintype.card_fin] at hc
      omega
    exact Finset.mem_image.mpr
      ⟨Phylo.splitOf (liftU T) h1 h2, by
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by rw [Phylo.splitOf_sideA, card_liftU]; exact hcard,
          by rw [sideA4_splitOf_liftU T h1 h2]; exact hP⟩,
        sideA4_splitOf_liftU T h1 h2⟩

/-! ### 2.1 三个计数 -/

/-- `2|2` 的（有向）split 恰有 `C(4,2) = 6` 个。 -/
theorem card_two_two : ((Finset.univ : Finset (Split U)).filter
    (fun r => r.sideA.card = 2)).card = 6 := by
  have h := card_filter_two (P := fun _ : Finset (Fin 4) => True)
  have h' : ((Finset.univ : Finset (Split U)).filter (fun r => r.sideA.card = 2)).card
      = ((Finset.univ : Finset (Split U)).filter
          (fun r => r.sideA.card = 2 ∧ True)).card := by
    congr 1
    ext r
    simp
  rw [h', h]
  simp only [Finset.filter_true, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

/-- 一致的（有向）split 恰有 `2` 个：`sideA4 ∈ {{0,1}, {2,3}}`。 -/
theorem card_isConc : ((Finset.univ : Finset (Split U)).filter
    (fun r => isConc Finset.univ r)).card = 2 := by
  have h : ((Finset.univ : Finset (Split U)).filter (fun r => isConc Finset.univ r)).card
      = (((Finset.univ : Finset (Fin 4)).powersetCard 2).filter
          (fun T => (0 : Fin 4) ∈ T ↔ (1 : Fin 4) ∈ T)).card := by
    simpa only [isConc] using
      (card_filter_two (P := fun T : Finset (Fin 4) => (0 : Fin 4) ∈ T ↔ (1 : Fin 4) ∈ T))
  rw [h]
  decide

/-- 不一致的 `2|2`（有向）split 恰有 `4` 个（`6 − 2`）。 -/
theorem card_notConc_two : ((Finset.univ : Finset (Split U)).filter
    (fun r => r.sideA.card = 2 ∧ ¬ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r ↔
      (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r))).card = 4 := by
  have h := card_filter_two (P := fun T : Finset (Fin 4) =>
    ¬ ((0 : Fin 4) ∈ T ↔ (1 : Fin 4) ∈ T))
  rw [h]
  decide

/-! ### 2.2 `swap` 不变性 -/

theorem sideA4_swap (r : Split U) :
    sideA4 (S := Finset.univ) r.swap
      = (Finset.univ : Finset (Fin 4)) \ sideA4 (S := Finset.univ) r := by
  ext x
  constructor
  · intro hx
    rw [sideA4, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Split.swap_sideA, Split.sideB_eq_sdiff, Finset.mem_sdiff] at hy
    obtain ⟨-, hyA⟩ := hy
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hxA => hyA ?_⟩
    rw [sideA4, Finset.mem_image] at hxA
    obtain ⟨z, hz, hzx⟩ := hxA
    have hzy : z = y := Subtype.ext (by simpa using hzx.trans hyx.symm)
    rwa [hzy] at hz
  · intro hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨-, hxA⟩ := hx
    rw [sideA4, Finset.mem_image]
    refine ⟨⟨x, Finset.mem_univ x⟩, ?_, rfl⟩
    rw [Split.swap_sideA, Split.sideB_eq_sdiff, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, fun hmem => hxA ?_⟩
    rw [sideA4, Finset.mem_image]
    exact ⟨⟨x, Finset.mem_univ x⟩, hmem, rfl⟩

/-- ★ **`isConc` 在 `swap` 下不变**（故 MSC 权重对无向 quartet 拓扑良定义）。 -/
theorem isConc_swap (S : Finset (Fin 4)) (hS : S.card = 4) (r : Split ↥S) :
    isConc S r.swap ↔ isConc S r := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  have hcard : (r.swap.sideA.card = 2) ↔ (r.sideA.card = 2) := by
    rw [Split.swap_sideA]
    have h := Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB r
    have hc : Fintype.card ↥(Finset.univ : Finset (Fin 4)) = 4 := by simp
    have h4 : r.sideA.card + r.sideB.card = 4 := by rw [h, hc]
    constructor <;> intro h2 <;> omega
  have hiff : ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r.swap
      ↔ (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r.swap)
      ↔ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r
          ↔ (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r) := by
    rw [sideA4_swap]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  unfold isConc
  rw [hcard]
  exact and_congr_right (fun _ => hiff)

/-! ## 3. ★★★ `Fin 4` 上由 Kingman 溯祖构造的 `QuartetFreq` -/

/-- ★★★ **MSC 的 quartet 概率表**（`Fin 4`）：一致的（有向）split 各 `mscConcordant t / 2`，
不一致的 `2|2` split 各 `mscDiscordant t / 2`，其余（`1|3`）为 `0`。
「一半」的记账见文件头 §3。 -/
def mscP (t : ℝ) (S : Finset (Fin 4)) (_hS : S.card = 4) (r : Split ↥S) : ℝ :=
  if isConc S r then mscConcordant t / 2
  else if r.sideA.card = 2 then mscDiscordant t / 2 else 0

/-- `mscP` 在一致 split 上取值 `mscConcordant t / 2`。 -/
theorem mscP_of_isConc {t : ℝ} {S : Finset (Fin 4)} {hS : S.card = 4} {r : Split ↥S}
    (hc : isConc S r) : mscP t S hS r = mscConcordant t / 2 := by
  unfold mscP
  simp [hc]

/-- `mscP` 在不一致 `2|2` split 上取值 `mscDiscordant t / 2`。 -/
theorem mscP_of_not_isConc_of_card {t : ℝ} {S : Finset (Fin 4)} {hS : S.card = 4}
    {r : Split ↥S} (hc : ¬ isConc S r) (h2 : r.sideA.card = 2) :
    mscP t S hS r = mscDiscordant t / 2 := by
  unfold mscP
  simp [hc, h2]

/-- `mscP` 在其余（`1|3`）split 上取值 `0`。 -/
theorem mscP_of_not_isConc_of_not_card {t : ℝ} {S : Finset (Fin 4)} {hS : S.card = 4}
    {r : Split ↥S} (hc : ¬ isConc S r) (h2 : r.sideA.card ≠ 2) :
    mscP t S hS r = 0 := by
  unfold mscP
  simp [hc, h2]

theorem mscP_nonneg {t : ℝ} (ht : 0 ≤ t) (S : Finset (Fin 4)) (hS : S.card = 4)
    (r : Split ↥S) : 0 ≤ mscP t S hS r := by
  by_cases hc : isConc S r
  · rw [mscP_of_isConc hc]
    exact div_nonneg (mscConcordant_nonneg ht) (by norm_num)
  · by_cases h2 : r.sideA.card = 2
    · rw [mscP_of_not_isConc_of_card hc h2]
      exact div_nonneg (mscDiscordant_pos t).le (by norm_num)
    · rw [mscP_of_not_isConc_of_not_card hc h2]

theorem mscP_swap (t : ℝ) (S : Finset (Fin 4)) (hS : S.card = 4) (r : Split ↥S) :
    mscP t S hS r.swap = mscP t S hS r := by
  have hcard : (r.swap.sideA.card = 2) ↔ (r.sideA.card = 2) := by
    obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
    rw [Split.swap_sideA]
    have h := Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB r
    have hc : Fintype.card ↥(Finset.univ : Finset (Fin 4)) = 4 := by simp
    have h4 : r.sideA.card + r.sideB.card = 4 := by rw [h, hc]
    constructor <;> intro h2 <;> omega
  have hcc : isConc S r.swap ↔ isConc S r := isConc_swap S hS r
  by_cases hc : isConc S r
  · rw [mscP_of_isConc (hcc.mpr hc), mscP_of_isConc hc]
  · have hc' : ¬ isConc S r.swap := fun h => hc (hcc.mp h)
    by_cases h2 : r.sideA.card = 2
    · rw [mscP_of_not_isConc_of_card hc' (hcard.mpr h2), mscP_of_not_isConc_of_card hc h2]
    · rw [mscP_of_not_isConc_of_not_card hc' (fun h => h2 (hcard.mp h)),
        mscP_of_not_isConc_of_not_card hc h2]

/-- `∑ x, (if p x then c else 0) = #{x | p x} · c`。 -/
theorem sum_ite_zero {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℝ) :
    ∑ x : α, (if p x then c else 0) = ((Finset.univ.filter p).card : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- ★★★ **归一化 (`QuartetFreq.p_sum_one`)**：`Fin 4` 上 MSC 权重之和恰为 `1`。 -/
theorem mscP_sum (t : ℝ) (S : Finset (Fin 4)) (hS : S.card = 4) :
    ∑ r : Split ↥S, mscP t S hS r = 1 := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  have hterm : ∀ r : Split U, mscP t Finset.univ hS r
      = (if isConc Finset.univ r then mscConcordant t / 2 else 0)
        + (if r.sideA.card = 2 ∧ ¬ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r ↔
            (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r) then mscDiscordant t / 2 else 0) := by
    intro r
    by_cases hc : isConc Finset.univ r
    · rw [mscP_of_isConc hc]
      simp [hc]
    · by_cases h2 : r.sideA.card = 2
      · have hni : ¬ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r ↔
            (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r) := by
          intro hiff; exact hc ⟨h2, hiff⟩
        rw [mscP_of_not_isConc_of_card hc h2]
        simp [hc, h2, hni]
      · have hnot : ¬ (r.sideA.card = 2 ∧ ¬ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r ↔
            (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r)) := fun h => h2 h.1
        rw [mscP_of_not_isConc_of_not_card hc h2]
        simp [hc, hnot]
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_add_distrib]
  rw [sum_ite_zero (fun r : Split U => isConc Finset.univ r) (mscConcordant t / 2),
      sum_ite_zero (fun r : Split U => r.sideA.card = 2 ∧
        ¬ ((0 : Fin 4) ∈ sideA4 (S := Finset.univ) r ↔
           (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r)) (mscDiscordant t / 2),
      card_isConc, card_notConc_two]
  push_cast
  linarith [mscConcordant_add_two t]

/-- ★★★ **`Fin 4` 上由 Kingman 溯祖给出的 `QuartetFreq`**（三条字段全部真证）。 -/
def mscQuartetFreq (t : ℝ) (ht : 0 ≤ t) : QuartetFreq (Fin 4) where
  p := mscP t
  p_nonneg := mscP_nonneg ht
  p_sum_one := mscP_sum t
  p_swap := mscP_swap t

/-! ## 4. 真树与 `QuartetTree` -/

/-- 真树 quartet 所选的 split：`sideA = {x ∈ S | x ∈ {2,3}}`，即无根拓扑 `01|23`。 -/
def qSplit (S : Finset (Fin 4)) (hS : S.card = 4) : Split ↥S :=
  Phylo.splitOf (Finset.univ.filter fun x : ↥S => (x : Fin 4) ∈ ({2, 3} : Finset (Fin 4)))
    ⟨⟨2, mem_of_card_four S hS 2⟩,
      by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp⟩
    ⟨⟨0, mem_of_card_four S hS 0⟩,
      by
        simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
        simp⟩

theorem qSplit_sideA (S : Finset (Fin 4)) (hS : S.card = 4) :
    (qSplit S hS).sideA
      = Finset.univ.filter (fun x : ↥S => (x : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) :=
  Phylo.splitOf_sideA _ _ _

theorem qSplit_card (S : Finset (Fin 4)) (hS : S.card = 4) :
    (qSplit S hS).sideA.card = 2 := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  rw [qSplit_sideA]
  decide

theorem sideA4_qSplit (S : Finset (Fin 4)) (hS : S.card = 4) :
    sideA4 (qSplit S hS) = ({2, 3} : Finset (Fin 4)) := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  rw [sideA4, qSplit_sideA]
  exact image_liftU _

theorem qSplit_displays (S : Finset (Fin 4)) (hS : S.card = 4) :
    T1234.toCladogram.DisplaysSplitOn S (qSplit S hS) := by
  refine ⟨Phylo.splitOf ({2, 3} : Finset (Fin 4)) nonempty_pair_F1234
    (Phylo.compl_nonempty_of_ne_univ pair_ne_univ_F1234), isSplitOf_pair_F1234, ?_⟩
  intro x
  rw [qSplit_sideA, Phylo.splitOf_sideA]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- ★★★ **`Fin 4` 上的具体 `QuartetTree`**：真树 = 各边权 `1` 的 `01|23` 二叉树（`T1234`）。 -/
def mscQuartetTree : QuartetTree (Fin 4) where
  tree := T1234.toCladogram
  q := qSplit
  q_card := qSplit_card
  displays := qSplit_displays

/-! ## 5. ★★★ MSC 核心不等式（定理，不是字段） -/

/-- ★★★ **MSC 核心不等式的无条件版本**：只要频率表取值恰为 4 叶 Kingman/MSC 的
quartet 分布（一致 `mscConcordant t`、不一致 `mscDiscordant t`），`t > 0` 时真树 quartet
**唯一严格最大**。这正是 `MSCFreq.majorizes` 的全部数学内容。 -/
theorem mscWeights_majorizes {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (_hS : S.card = 4) (q : Split ↥S) {t : ℝ} (ht : 0 < t)
    (freq : Split ↥S → ℝ)
    (hconc : freq q = mscConcordant t)
    (hdisc : ∀ r : Split ↥S, r ≠ q → r ≠ q.swap → freq r = mscDiscordant t) :
    ∀ r : Split ↥S, r ≠ q → r ≠ q.swap → freq r < freq q := by
  intro r hr hrs
  rw [hdisc r hr hrs, hconc]
  exact mscDiscordant_lt_mscConcordant ht

/-- 一致的 `2|2` 有向 split（在 `↥univ` 上）的 `sideA4` 只能是 `{0,1}` 或 `{2,3}`。 -/
theorem isConc_sideA4 {r : Split U} (h : isConc Finset.univ r) :
    sideA4 (S := Finset.univ) r = ({0, 1} : Finset (Fin 4)) ∨
      sideA4 (S := Finset.univ) r = ({2, 3} : Finset (Fin 4)) := by
  obtain ⟨hcard, hiff⟩ := h
  have h2 : (sideA4 (S := Finset.univ) r).card = 2 := by rw [card_sideA4]; exact hcard
  by_cases h0 : (0 : Fin 4) ∈ sideA4 (S := Finset.univ) r
  · left
    have h1 : (1 : Fin 4) ∈ sideA4 (S := Finset.univ) r := hiff.mp h0
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h0
      · exact h1
    · rw [h2]; decide
  · right
    have h1 : (1 : Fin 4) ∉ sideA4 (S := Finset.univ) r := fun h1 => h0 (hiff.mpr h1)
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      fin_cases x
      · exact absurd hx h0
      · exact absurd hx h1
      · decide
      · decide
    · rw [h2]; decide

/-- `sideA4` 在 `swap` 下取补，故一致 split 的 `swap` 的 `sideA4` 是 `{0,1}`。 -/
theorem sideA4_qSplit_swap (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    sideA4 (S := Finset.univ) (qSplit Finset.univ hS).swap = ({0, 1} : Finset (Fin 4)) := by
  rw [sideA4_swap, sideA4_qSplit Finset.univ hS]
  decide

/-- ★★★ **`Fin 4` 上由 Kingman 溯祖构造的 `MSCFreq`** —— `Phylo/Stat/MSC.lean`
顶部「先把 MSC 公理化」的**终结**：`MSCFreq` 有了**具体实例**，且其 `majorizes`
是 `mscDiscordant_lt_mscConcordant` 的推论，而不是被假设的字段。 -/
def mscFreqFin4 (t : ℝ) (ht : 0 < t) : MSCFreq (Fin 4) where
  toQuartetTree := mscQuartetTree
  freq := mscQuartetFreq t ht.le
  majorizes := by
    intro S hS r hr hrs
    obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
    show mscP t Finset.univ hS r < mscP t Finset.univ hS (qSplit Finset.univ hS)
    have hq : sideA4 (S := Finset.univ) (qSplit Finset.univ hS) = ({2, 3} : Finset (Fin 4)) :=
      sideA4_qSplit Finset.univ hS
    have hqswap : sideA4 (S := Finset.univ) (qSplit Finset.univ hS).swap
        = ({0, 1} : Finset (Fin 4)) := sideA4_qSplit_swap hS
    have hqconc : isConc Finset.univ (qSplit Finset.univ hS) :=
      ⟨qSplit_card Finset.univ hS, by rw [hq]; decide⟩
    rw [mscP_of_isConc hqconc]
    by_cases hc : isConc Finset.univ r
    · rcases isConc_sideA4 hc with h | h
      · exact absurd (sideA4_inj (h.trans hqswap.symm)) hrs
      · exact absurd (sideA4_inj (h.trans hq.symm)) hr
    · by_cases h2 : r.sideA.card = 2
      · rw [mscP_of_not_isConc_of_card hc h2]
        exact div_lt_div_of_pos_right (mscDiscordant_lt_mscConcordant ht) (by norm_num)
      · rw [mscP_of_not_isConc_of_not_card hc h2]
        exact div_pos (mscConcordant_pos ht) (by norm_num)

/-- ★★ **反空真**：`Fin 4` 上 `MSCFreq` **可居留** —— 「MSC 公理」不是一个空结构。 -/
theorem mscFreqFin4_nonempty : Nonempty (MSCFreq.{0, 0} (Fin 4)) :=
  ⟨mscFreqFin4 1 one_pos⟩

/-- 真树 quartet 在 MSC 权重下**严格为正**。 -/
theorem mscP_qSplit_pos (t : ℝ) (ht : 0 < t) (S : Finset (Fin 4)) (hS : S.card = 4) :
    0 < mscP t S hS (qSplit S hS) := by
  obtain rfl : S = Finset.univ := eq_univ_of_card_four S hS
  rw [mscP_of_isConc ⟨qSplit_card Finset.univ hS,
    by rw [sideA4_qSplit Finset.univ hS]; decide⟩]
  exact div_pos (mscConcordant_pos ht) (by norm_num)

/-- ★★ **反空真（更强）**：真树 quartet 在该实例下概率**严格为正**
（故 `majorizes` 的严格不等式**不是空真**）。 -/
theorem mscFreqFin4_freq_pos (t : ℝ) (ht : 0 < t) :
    0 < (mscFreqFin4 t ht).freq.p Finset.univ (by decide)
      ((mscFreqFin4 t ht).q Finset.univ (by decide)) := by
  rw [show (mscFreqFin4 t ht).freq.p = mscP t from rfl]
  rw [show (mscFreqFin4 t ht).q = qSplit from rfl]
  exact mscP_qSplit_pos t ht Finset.univ (by decide)

/-! ## 6. ★★★ 推广：**任意** `X` 上由 Kingman 溯祖给出的 `QuartetFreq`

§3–§5 只做到 `X = Fin 4`（因为那里的真树用了 `NJstWitness.T1234`）。本节把**频率表**
这一半推广到**任意有限 `X`**：只要对每个 4-元集 `S` 给定一个「真 quartet」`q S hS`
（形状与 `QuartetTree.q` 一致，含 `q_card`），就能构造出 `QuartetFreq X`。

⇒ 于是「`X = Fin 4` 之外」这条边界的**剩余部分只剩「树」**（一个纯组合的
`Cladogram` 展示问题，见 `Phylo/Stat/QuartetDecides.lean`），**不再是溯祖/概率的问题**。 -/

section General

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- `r : Split ↥S` 的 `sideA` 在 `X` 里的实际元素。 -/
def sideAX {S : Finset X} (r : Split ↥S) : Finset X :=
  r.sideA.image (Function.Embedding.subtype fun x => x ∈ S)

omit [Fintype X] in
theorem sideAX_subset {S : Finset X} (r : Split ↥S) : sideAX r ⊆ S := by
  intro x hx
  rw [sideAX, Finset.mem_image] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

omit [Fintype X] in
theorem card_sideAX {S : Finset X} (r : Split ↥S) : (sideAX r).card = r.sideA.card :=
  Finset.card_image_of_injective _ (Function.Embedding.subtype _).injective

omit [Fintype X] in
/-- 把 `T : Finset X` **拉回** `↥S`（只保留落在 `T` 里的元素）。 -/
def liftS (S T : Finset X) : Finset ↥S :=
  Finset.univ.filter fun x => (x : X) ∈ T

omit [Fintype X] in
theorem image_liftS (S T : Finset X) :
    (liftS S T).image (Function.Embedding.subtype fun x => x ∈ S)
      = S.filter (fun x => x ∈ T) := by
  ext x
  simp only [liftS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  · rintro ⟨hxS, hxT⟩; exact ⟨⟨x, hxS⟩, hxT, rfl⟩

omit [Fintype X] in
theorem card_liftS (S T : Finset X) : (liftS S T).card = (S.filter fun x => x ∈ T).card := by
  rw [← Finset.card_image_of_injective _ (Function.Embedding.subtype _).injective, image_liftS]

omit [Fintype X] in
/-- ★★ `sideAX` 完全决定 `sideA`。 -/
theorem sideA_eq_liftS (S : Finset X) (r : Split ↥S) :
    r.sideA = liftS S (sideAX (S := S) r) := by
  ext x
  simp only [liftS, sideAX, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Function.Embedding.subtype_apply]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    rwa [h] at hy

omit [Fintype X] in
theorem sideAX_inj {S : Finset X} {r r' : Split ↥S}
    (h : sideAX (S := S) r = sideAX (S := S) r') : r = r' := by
  apply Phylo.Stat.CASTERTopoSplit.eq_of_sideA_eq
  rw [sideA_eq_liftS S r, sideA_eq_liftS S r', h]

omit [Fintype X] in
theorem sideAX_splitOf_liftS (S T : Finset X)
    (h1 : (liftS S T).Nonempty) (h2 : (liftS S T)ᶜ.Nonempty) :
    sideAX (S := S) (Phylo.splitOf (liftS S T) h1 h2) = S.filter (fun x => x ∈ T) := by
  unfold sideAX
  rw [Phylo.splitOf_sideA]
  exact image_liftS S T

omit [Fintype X] in
/-- ★★★ **一般 4-元集上 `2|2` 的（有向）split 恰 `C(4,2) = 6` 个**
（`r ↦ sideAX r` 与 `S.powersetCard 2` 一一对应）。 -/
theorem card_splits_two (S : Finset X) (hS : S.card = 4) :
    ((Finset.univ : Finset (Split ↥S)).filter (fun r => r.sideA.card = 2)).card = 6 := by
  set s : Finset (Split ↥S) :=
    (Finset.univ : Finset (Split ↥S)).filter (fun r => r.sideA.card = 2) with hs
  have hinj : Set.InjOn (fun r : Split ↥S => sideAX (S := S) r) ↑s := by
    intro r1 _ r2 _ h
    exact sideAX_inj h
  have hcard : s.card = (S.powersetCard 2).card := by
    rw [← Finset.card_image_of_injOn hinj]
    congr 1
    ext T
    constructor
    · intro hT
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hT
      simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.mem_powersetCard]
      exact ⟨sideAX_subset r, by rw [card_sideAX]; exact hr⟩
    · intro hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨hsub, hcardT⟩ := hT
      have hfil : S.filter (fun x => x ∈ T) = T := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
      have hcard2 : (liftS S T).card = 2 := by rw [card_liftS, hfil, hcardT]
      have h1 : (liftS S T).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h, Finset.card_empty] at hcard2
        omega
      have h2 : (liftS S T)ᶜ.Nonempty := by
        apply Phylo.compl_nonempty_of_ne_univ
        intro h
        rw [h, Finset.card_univ, Fintype.card_coe, hS] at hcard2
        omega
      exact Finset.mem_image.mpr
        ⟨Phylo.splitOf (liftS S T) h1 h2, by
          simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and, Phylo.splitOf_sideA,
            card_liftS, hfil, hcardT],
          by rw [sideAX_splitOf_liftS S T h1 h2, hfil]⟩
  rw [hcard, Finset.card_powersetCard, hS]
  decide

omit [Fintype X] in
/-- 一个有向 split 与它的 `swap` 不同（两侧不交且非空）。 -/
theorem ne_swap_of_split {S : Finset X} (q : Split ↥S) : q ≠ q.swap := by
  intro h
  have hs : q.sideA = q.sideB := by
    have := congrArg Split.sideA h
    rwa [Split.swap_sideA] at this
  have hd : Disjoint q.sideA q.sideA := by
    have h' := q.disjoint_sides
    rwa [← hs] at h'
  obtain ⟨x, hx⟩ := q.nonempty 0
  exact (Finset.disjoint_left.mp hd) hx hx

omit [Fintype X] in
theorem card_eq_or_swap {S : Finset X} (q : Split ↥S) :
    ((Finset.univ : Finset (Split ↥S)).filter (fun r => r = q ∨ r = q.swap)).card = 2 := by
  have hset : (Finset.univ.filter (fun r : Split ↥S => r = q ∨ r = q.swap)) = {q, q.swap} := by
    ext r; simp
  rw [hset, Finset.card_pair (ne_swap_of_split q)]

omit [Fintype X] in
/-- `q` 与 `q.swap` 都是 `2|2` 时，「其余 `2|2`」恰 4 个（`6 − 2`）。 -/
theorem card_other_two (S : Finset X) (hS : S.card = 4) (q : Split ↥S)
    (hq : q.sideA.card = 2) :
    ((Finset.univ : Finset (Split ↥S)).filter
      (fun r => r.sideA.card = 2 ∧ ¬ (r = q ∨ r = q.swap))).card = 4 := by
  have hqswap : q.swap.sideA.card = 2 := by
    rw [Split.swap_sideA]
    have h := Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB q
    have hc4 : Fintype.card ↥S = 4 := by rw [Fintype.card_coe]; exact hS
    have h4 : q.sideA.card + q.sideB.card = 4 := by rw [h, hc4]
    omega
  have hBsub : (Finset.univ.filter (fun r : Split ↥S => r = q ∨ r = q.swap))
      ⊆ (Finset.univ.filter (fun r : Split ↥S => r.sideA.card = 2)) := by
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    obtain ⟨-, h | h⟩ := hr
    · rw [h]; exact ⟨Finset.mem_univ _, hq⟩
    · rw [h]; exact ⟨Finset.mem_univ _, hqswap⟩
  have hdiff : (Finset.univ.filter (fun r : Split ↥S =>
        r.sideA.card = 2 ∧ ¬ (r = q ∨ r = q.swap)))
      = (Finset.univ.filter (fun r : Split ↥S => r.sideA.card = 2)) \
        (Finset.univ.filter (fun r : Split ↥S => r = q ∨ r = q.swap)) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hdiff, Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub,
    card_splits_two S hS, card_eq_or_swap q]

omit [Fintype X] in
/-- ★★★ **一般 `X` 上由 Kingman 溯祖给出的 quartet 概率表**：
给定每个 4-元集 `S` 的「真 quartet」`q S hS`（`q_card` 为 `2|2`），
一致的（有向）split `q`/`q.swap` 各得 `mscConcordant t / 2`，其余 `2|2` 各得
`mscDiscordant t / 2`，`1|3` 得 `0`。 -/
def mscPOf (t : ℝ) (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (S : Finset X) (hS : S.card = 4) (r : Split ↥S) : ℝ :=
  if r = q S hS ∨ r = (q S hS).swap then mscConcordant t / 2
  else if r.sideA.card = 2 then mscDiscordant t / 2 else 0

omit [Fintype X] in
theorem mscPOf_of_eq {t : ℝ} {q : (S : Finset X) → S.card = 4 → Split ↥S}
    {S : Finset X} {hS : S.card = 4} {r : Split ↥S}
    (h : r = q S hS ∨ r = (q S hS).swap) : mscPOf t q S hS r = mscConcordant t / 2 := by
  unfold mscPOf
  simp [h]

omit [Fintype X] in
theorem mscPOf_of_ne_of_card {t : ℝ} {q : (S : Finset X) → S.card = 4 → Split ↥S}
    {S : Finset X} {hS : S.card = 4} {r : Split ↥S}
    (h : ¬ (r = q S hS ∨ r = (q S hS).swap)) (h2 : r.sideA.card = 2) :
    mscPOf t q S hS r = mscDiscordant t / 2 := by
  unfold mscPOf
  simp [h, h2]

omit [Fintype X] in
theorem mscPOf_of_ne_of_not_card {t : ℝ} {q : (S : Finset X) → S.card = 4 → Split ↥S}
    {S : Finset X} {hS : S.card = 4} {r : Split ↥S}
    (h : ¬ (r = q S hS ∨ r = (q S hS).swap)) (h2 : r.sideA.card ≠ 2) :
    mscPOf t q S hS r = 0 := by
  unfold mscPOf
  simp [h, h2]

omit [Fintype X] in
theorem mscPOf_nonneg {t : ℝ} (ht : 0 ≤ t)
    (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (S : Finset X) (hS : S.card = 4) (r : Split ↥S) : 0 ≤ mscPOf t q S hS r := by
  by_cases h : r = q S hS ∨ r = (q S hS).swap
  · rw [mscPOf_of_eq h]
    exact div_nonneg (mscConcordant_nonneg ht) (by norm_num)
  · by_cases h2 : r.sideA.card = 2
    · rw [mscPOf_of_ne_of_card h h2]
      exact div_nonneg (mscDiscordant_pos t).le (by norm_num)
    · rw [mscPOf_of_ne_of_not_card h h2]

omit [Fintype X] in
theorem mscPOf_swap {t : ℝ} (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (S : Finset X) (hS : S.card = 4) (r : Split ↥S) :
    mscPOf t q S hS r.swap = mscPOf t q S hS r := by
  have hiff : (r.swap = q S hS ∨ r.swap = (q S hS).swap) ↔ (r = q S hS ∨ r = (q S hS).swap) := by
    constructor
    · rintro (h | h)
      · refine Or.inr (Split.swap_injective ?_)
        rw [Split.swap_swap]; exact h
      · exact Or.inl (Split.swap_injective h)
    · rintro (h | h)
      · exact Or.inr (by rw [h])
      · exact Or.inl (by rw [h, Split.swap_swap])
  have hcard : (r.swap.sideA.card = 2) ↔ (r.sideA.card = 2) := by
    rw [Split.swap_sideA]
    have h := Phylo.Stat.CASTERTopoSplit.card_sideA_add_card_sideB r
    have hc4 : Fintype.card ↥S = 4 := by rw [Fintype.card_coe]; exact hS
    have h4 : r.sideA.card + r.sideB.card = 4 := by rw [h, hc4]
    constructor <;> intro h2 <;> omega
  by_cases hc : r = q S hS ∨ r = (q S hS).swap
  · rw [mscPOf_of_eq (hiff.mpr hc), mscPOf_of_eq hc]
  · have hc' : ¬ (r.swap = q S hS ∨ r.swap = (q S hS).swap) := fun h => hc (hiff.mp h)
    by_cases h2 : r.sideA.card = 2
    · rw [mscPOf_of_ne_of_card hc' (hcard.mpr h2), mscPOf_of_ne_of_card hc h2]
    · rw [mscPOf_of_ne_of_not_card hc' (fun h => h2 (hcard.mp h)),
        mscPOf_of_ne_of_not_card hc h2]

omit [Fintype X] in
/-- ★★★ **归一化（一般 `X`）**：`Σ_{r} mscPOf t q S hS r = 1`。 -/
theorem mscPOf_sum {t : ℝ} (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (hq2 : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2)
    (S : Finset X) (hS : S.card = 4) :
    ∑ r : Split ↥S, mscPOf t q S hS r = 1 := by
  have hterm : ∀ r : Split ↥S, mscPOf t q S hS r
      = (if r = q S hS ∨ r = (q S hS).swap then mscConcordant t / 2 else 0)
        + (if r.sideA.card = 2 ∧ ¬ (r = q S hS ∨ r = (q S hS).swap)
            then mscDiscordant t / 2 else 0) := by
    intro r
    by_cases h : r = q S hS ∨ r = (q S hS).swap
    · rw [mscPOf_of_eq h]; simp [h]
    · by_cases h2 : r.sideA.card = 2
      · rw [mscPOf_of_ne_of_card h h2]; simp [h, h2]
      · rw [mscPOf_of_ne_of_not_card h h2]; simp [h, h2]
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_add_distrib]
  rw [sum_ite_zero (fun r : Split ↥S => r = q S hS ∨ r = (q S hS).swap) (mscConcordant t / 2),
      sum_ite_zero (fun r : Split ↥S =>
        r.sideA.card = 2 ∧ ¬ (r = q S hS ∨ r = (q S hS).swap)) (mscDiscordant t / 2),
      card_eq_or_swap (q S hS), card_other_two S hS (q S hS) (hq2 S hS)]
  push_cast
  linarith [mscConcordant_add_two t]

/-- ★★★ **任意 `X` 上由 Kingman 溯祖给出的 `QuartetFreq`**（三条字段全部真证）。 -/
def mscQuartetFreqOf (t : ℝ) (ht : 0 ≤ t)
    (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (hq2 : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2) :
    QuartetFreq X where
  p := mscPOf t q
  p_nonneg := mscPOf_nonneg ht q
  p_sum_one := mscPOf_sum q hq2
  p_swap := mscPOf_swap q

/-- ★★★ **MSC 核心不等式（一般 `X`，无条件版本）**：对任意 4-元集 `S`，
`mscQuartetFreqOf` 给出的频率表在真 quartet 上**唯一严格最大**（`t > 0`）。 -/
theorem mscQuartetFreqOf_majorizes (t : ℝ) (ht : 0 < t)
    (q : (S : Finset X) → S.card = 4 → Split ↥S)
    (hq2 : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2) :
    ∀ (S : Finset X) (hS : S.card = 4) (r : Split ↥S),
      r ≠ q S hS → r ≠ (q S hS).swap →
        (mscQuartetFreqOf t ht.le q hq2).p S hS r
          < (mscQuartetFreqOf t ht.le q hq2).p S hS (q S hS) := by
  intro S hS r hr hrs
  show mscPOf t q S hS r < mscPOf t q S hS (q S hS)
  have hc : q S hS = q S hS ∨ q S hS = (q S hS).swap := Or.inl rfl
  rw [mscPOf_of_eq hc]
  have hn : ¬ (r = q S hS ∨ r = (q S hS).swap) := fun h => h.elim hr hrs
  by_cases h2 : r.sideA.card = 2
  · rw [mscPOf_of_ne_of_card hn h2]
    exact div_lt_div_of_pos_right (mscDiscordant_lt_mscConcordant ht) (by norm_num)
  · rw [mscPOf_of_ne_of_not_card hn h2]
    exact div_pos (mscConcordant_pos ht) (by norm_num)

end General

/-! ## 7. ★★★ 任意 `X`：存在 binary 树 ⇒ `MSCFreq X` **非空**（频率表由 Kingman 权重构造）

§3–§5 的 `mscFreqFin4` 只对 `X = Fin 4`（真树固定为 `NJstWitness.T1234`）。本节的
`mscFreq_nonempty_of_binary` 把它**一般化**到**任意** `X`：只要**存在**一棵 binary
`Cladogram`，就能构造出 `MSCFreq X` ——

* 每个 4-元集上的 quartet 由 `Cladogram.exists_displaysSplitOn_card_two`
  （`Phylo/QuartetInhabitation.lean` 第 **652** 行）取出（**纯组合**，与溯祖无关）；
* 频率表由 §6 的 `mscQuartetFreqOf` 给出（**Kingman/MSC 权重**）；
* `majorizes` 是 `mscQuartetFreqOf_majorizes` 给出的**定理**（不是被假设的字段）。

⇒ 「`MSCFreq` 有具体实例」**不再限于 `Fin 4`**；剩下的唯一前提是「存在一棵 binary 树」，
那是**组合**假设而不是**溯祖**假设。 -/

/-- ★★★ **任意 `X`：binary 树 ⇒ `MSCFreq X` 非空**（频率表由 Kingman/MSC 权重构造）。 -/
theorem mscFreq_nonempty_of_binary {X : Type u} [Fintype X] [DecidableEq X]
    {T : Cladogram.{u, v} X} (hT : T.IsBinary) : Nonempty (MSCFreq.{u, v} X) := by
  classical
  have hchoice : ∀ (S : Finset X) (hS : S.card = 4),
      ∃ q : Split ↥S, T.DisplaysSplitOn S q ∧ q.sideA.card = 2 :=
    fun S hS => Cladogram.exists_displaysSplitOn_card_two hT hS
  let q : (S : Finset X) → S.card = 4 → Split ↥S := fun S hS => (hchoice S hS).choose
  have hq2 : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2 :=
    fun S hS => ((hchoice S hS).choose_spec).2
  have hdisp : ∀ (S : Finset X) (hS : S.card = 4), T.DisplaysSplitOn S (q S hS) :=
    fun S hS => ((hchoice S hS).choose_spec).1
  exact ⟨{ toQuartetTree := ⟨T, q, hq2, hdisp⟩
           freq := mscQuartetFreqOf 1 zero_le_one q hq2
           majorizes := mscQuartetFreqOf_majorizes 1 one_pos q hq2 }⟩

end Phylo.Stat.MSCProof
