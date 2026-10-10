/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Identifiability
import Phylo.Stat.QuartetDecides

/-!
# `Phylo.Stat.MLIdentifiability` —— 最大似然（ML）的可识别性与一致性

## 本文件解决的问题

「**ML 是可识别的**」这句话在有限/离散层上有一个**精确且可证**的形态：

> **真树的期望得分唯一最大**（`Identifiable`）⟹ 存在正 gap `δ`（有限性）
> ⟹ 观测得分 `δ/2`-接近期望得分时，**任何** argmax 都恰是真树
> ⟹ （大数定律）ML 估计量**最终**选真树。

这就是本库 `Phylo/Stat/Stability.lean` 里「① 理想一致性 ＋ ② gap ＋ ③ 稳定性」的
**算法无关版本**：那里 `T = QuartetChoice X`（ASTRAL 的候选空间），
这里 `T` 是**任意有限候选空间**（ML 的候选空间：有限拓扑集）。本文件把这三层
**从 quartet 专用提升为通用引擎**，并在树层用 ★★★ `QuartetDecidesTree` 收口。

## 文献（**在手**，`references/md/`）

* **Chang 1996** —— *Full reconstruction for Markov models: identifiability and consistency*
  （`references/md/Chang1996_FullReconstructionMarkovModelsIdentifiabilityConsistency.md`）：
  **可识别性 = 真树的期望得分唯一最大**，一致性 = 可识别性 ＋ 大数定律。本文件的
  `Identifiable` 就是该文「identifiability」的形式化，`ml_statisticallyConsistent` 是其推论形状。
* **Rogers 1997** —— *On the consistency of maximum likelihood estimation of phylogenetic trees*
  （`references/md/Rogers1997_ConsistencyMaximumLikelihoodNucleotideSequences.md`）：ML 一致性的
  充分条件是「期望对数似然在真树处**唯一**最大」＋ 紧性 ⇒ **正 gap**。本文件 `exists_gap` 即
  有限候选空间上的这一紧性论证（无需一般拓扑紧性定理）。
* **Steel 1994** —— *Recovering a tree from a Markov model*（`references/md/Steel1994_...md`）：
  模型参数到分布的单射性 ⇒ 拓扑可识别；本库 `Phylo/Stat/Identifiability.lean` 已把
  **三分支 MSC** 那一情形证成定理（`branchLength_eq`、`mscConcordant_injective`、`argmax_unique`）。
* **Tuffley & Steel 1997** —— ML 与 parsimony 的联系（`references/md/TuffleySteel1997_...md`）：
  ML 与 parsimony 的一致性可共用同一「期望得分唯一最大」的引擎 —— 正是本文件的形状。
* **Roch & Steel 2015** —— 拼接（concatenation）下似然可能**不一致**
  （`references/md/RochSteel2015_LikelihoodConcatenationInconsistent.md`）：**模型误设**时
  `Identifiable` 会失败 ⇒ `ml_inconsistent_of_not_identifiable`（★B 反例，非空洞性证据）。

## 本文件证什么（全部 `sorry`-free）

| 声明 | 内容 |
|---|---|
| ★★ `MLProblem.exists_gap` | 期望得分在真树处**严格最大** ⟹ 存在**正**（统一）gap `δ`（**有限性**，即 ②） |
| ★★ `MLProblem.argmax_eq_truth_of_close` | 观测得分 `δ/2`-接近期望 ⟹ 任何 argmax **恰是真树**（③） |
| ★★★ `MLProblem.ml_statisticallyConsistent` | `Identifiable` ＋ 大数定律（**公理化**）⟹ ML 估计量**最终**选真树 |
| ★★★ `ml_tree_iso_of_quartet_agreement` | 树层收口：逐 quartet 一致 ＋ two binary ⟹ **树同构**（复用 `QuartetDecidesTree`） |
| ★★ `threeTaxon_gap` | **接线**：ADR2011/MSC 三分支给出**显式** gap `mscConcordant t − mscDiscordant t > 0`（`t > 0`）⟹ 本引擎的 `Identifiable` 前提**非空洞** |
| ★B `ml_finite_sample_not_true` | **有限样本下 ML 不必选真树**（2 候选 ＋ 具体反例，`n = 0`） |
| ★B `strict_max_no_uniform_gap` | **无正 gap 的严格最大**（无限候选空间）⟹ `exists_gap` 的**有限性**不可去 |
| ★B `ml_inconsistent_of_not_identifiable` | 期望得分最大者**不是**真树（模型误设 ⇒ 不可识别）时，**任何** argmax 估计量都不一致 |
| ★C `fourTaxonProblem` ＋ `fourTaxonML_gap` ＋ `fourTaxon_argmax_eq_truth` | 4 taxon / 3 拓扑的具体 ML 问题（有理数表 `(0, −1/8, −3/8)`，gap `= 1/8`，`norm_num`）；**模型层**的精确有理核验见 `scripts/msc/w11d_ml_ident_check.py` |

## 诚实边界（**不弱化、不硬编**）

| 条目 | 状态 |
|---|---|
| 「期望得分唯一最大」这一**可识别性输入** | 本文件**证成通用引擎**（`exists_gap` 等）；对**具体模型**（JC69/GTR/…）的**一般 `n`** 唯一最大性 —— **未做**，见下方缺口 `generalModelIdentifiability_gap` |
| 大数定律 `MLProblem.converges` | **公理化**（与本库 `MSCSampling.converges` 同款处理）：形状与算法内容先定死，概率层进展只需替换该字段 |
| ML 的**有限样本**行为 | **不成立**（★B `ml_finite_sample_not_true`）；本文件的结论一律是「**最终**」（`∃ N, ∀ n ≥ N`） |
| 无限候选空间（如把枝长也当候选） | gap 引理**失效**（★B `strict_max_no_uniform_gap`）⇒ 有限性是**必要**假设 |
| GTR 等一般模型类的**统计一致性** | ❌ **超出本批范围**：落在 `generalModelIdentifiability_gap`（显式 `def … : Prop` 缺口）——需要「GTR 的期望对数似然在真树处唯一最大」这一**模型层**定理 |
-/

noncomputable section

namespace Phylo.Stat.MLIdentifiability

open Phylo.Stat.MSCProof

universe u v

/-! ## 1. 通用有限 ML 引擎 -/

/-- **有限候选空间上的 ML 问题**。

* `truth` —— 真树（候选空间里的那个元素）；
* `expected` —— **期望**得分（每位点对数似然，除以位点数；即「理想无穷样本」的得分）；
* `obs n` —— `n` 个位点的**观测**得分；
* `converges` —— **大数定律**（公理化，与本库 `MSCSampling.converges` 同款）：
  观测得分最终任意 `ε`-接近期望得分。

⚠️ `converges` 是**确定性**的「最终 ε-接近」，把概率层的「依概率/几乎必然收敛」抽象掉；
换成真概率陈述即得真·依概率一致性（课题 `Phylo.Stat.MSCProof`）。 -/
structure MLProblem (T : Type u) [Fintype T] where
  /-- 真树。 -/
  truth : T
  /-- 期望得分（理想无穷样本）。 -/
  expected : T → ℝ
  /-- `n` 个位点的观测得分。 -/
  obs : ℕ → T → ℝ
  /-- ★ **大数定律**（公理化）：观测得分最终 `ε`-接近期望得分。 -/
  converges : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t : T, |obs n t - expected t| < ε

namespace MLProblem

variable {T : Type u} [Fintype T]

/-- ★ **可识别性**（Chang 1996 / Rogers 1997 的输入）：真树的**期望**得分**唯一**最大。

这正是「ML 是可识别的」在有限候选空间上的精确含义。 -/
def Identifiable (P : MLProblem T) : Prop :=
  ∀ t : T, t ≠ P.truth → P.expected t < P.expected P.truth

/-- ★★ **gap 引理（②）**：期望得分的**严格**最大性在**有限**候选空间上自动一致化 ——
存在统一的 `δ > 0`，任何非真候选都至少差 `δ`。

**证明**：`{expected truth − expected t | t ≠ truth}` 是有限非空实数集，取其最小值。 -/
theorem exists_gap (P : MLProblem T) (h : P.Identifiable) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : T, t ≠ P.truth → P.expected t + δ ≤ P.expected P.truth := by
  classical
  by_cases hne : (Finset.univ.filter (fun t : T => t ≠ P.truth)).Nonempty
  · set S : Finset ℝ := (Finset.univ.filter (fun t : T => t ≠ P.truth)).image
      (fun t => P.expected P.truth - P.expected t) with hS
    have hSne : S.Nonempty := by rw [hS]; exact hne.image _
    refine ⟨S.min' hSne, ?_, ?_⟩
    · obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp (S.min'_mem hSne)
      have htne : t ≠ P.truth := (Finset.mem_filter.mp ht).2
      rw [← heq]
      linarith [h t htne]
    · intro t ht
      have hmem : P.expected P.truth - P.expected t ∈ S := by
        rw [hS]
        exact Finset.mem_image.mpr
          ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩, rfl⟩
      have := S.min'_le _ hmem
      linarith
  · exact ⟨1, one_pos, fun t ht =>
      absurd ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩⟩ hne⟩

/-- ★★ **稳定性（③）**：若第 `n` 个样本的观测得分逐点 `δ/2`-接近期望得分
（`δ` 为 `exists_gap` 的 gap），则**任何**观测 argmax 都**恰是真树**。

⚠️ 注意这是**逐样本**结论，前提是「该样本已足够接近期望」；一般样本不满足（★B）。 -/
theorem argmax_eq_truth_of_close (P : MLProblem T) {δ : ℝ}
    (hgap : ∀ t : T, t ≠ P.truth → P.expected t + δ ≤ P.expected P.truth)
    {n : ℕ} (hclose : ∀ t : T, |P.obs n t - P.expected t| < δ / 2)
    {t : T} (hmax : ∀ s : T, P.obs n s ≤ P.obs n t) : t = P.truth := by
  by_contra hne
  have h1 : P.obs n t < P.expected t + δ / 2 := by
    have := (abs_lt.mp (hclose t)).2
    linarith
  have h2 : P.expected P.truth < P.obs n P.truth + δ / 2 := by
    have := (abs_lt.mp (hclose P.truth)).1
    linarith
  have h3 : P.expected t + δ ≤ P.expected P.truth := hgap t hne
  have h4 : P.obs n P.truth ≤ P.obs n t := hmax P.truth
  linarith

/-- **ML 估计量的样本一致性谓词**：最终恒等于真树。 -/
def Consistent (P : MLProblem T) (E : ℕ → T) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, E n = P.truth

/-- ★★★ **ML 的统计一致性**（Chang 1996 / Rogers 1997 的形状）：

若候选空间**有限**、期望得分在真树处**唯一最大**（`Identifiable`），
且估计量 `E` 在**每个**样本上取观测得分的最大化者，则 `E` **最终**输出真树。

**证明**：`exists_gap` 给 `δ > 0`；大数定律（`converges`，取 `ε = δ/2`）给 `N`；
`argmax_eq_truth_of_close` 把 `n ≥ N` 时的 argmax 钉在真树上。

⚠️ 两条边界：(i) `converges` 是**公理化**的；(ii) 结论是**最终**的 ——
**有限样本**下 ML 可以选错树（★B `ml_finite_sample_not_true`）。 -/
theorem ml_statisticallyConsistent (P : MLProblem T) (h : P.Identifiable)
    (E : ℕ → T) (hE : ∀ n : ℕ, ∀ t : T, P.obs n t ≤ P.obs n (E n)) : P.Consistent E := by
  obtain ⟨δ, hδ, hgap⟩ := P.exists_gap h
  obtain ⟨N, hN⟩ := P.converges (δ / 2) (by linarith)
  exact ⟨N, fun n hn =>
    argmax_eq_truth_of_close P hgap (hN n hn) (hE n)⟩

/-- ★ **`MLProblem` 非空洞**（反空真）：显式居民（2 候选、恒真观测）。 -/
theorem mlProblem_nonempty : Nonempty (MLProblem (Fin 2)) :=
  ⟨{ truth := 0
     expected := fun _ => 0
     obs := fun _ _ => 0
     converges := fun ε hε => ⟨0, fun _ _ _ => by
       rw [sub_self, abs_zero]; exact hε⟩ }⟩

end MLProblem

/-! ## 2. 树层收口（复用 `QuartetDecidesTree`）

ML/得分型估计量在**有限拓扑空间**上给出的 argmax 是一棵**候选树**；一旦它逐 quartet 与
真树一致，`Phylo/Stat/QuartetDecides.lean` 的 ★★★ `QuartetDecidesTree` 立即把它升到**树同构**。
这是 `astral_iso` / `parsimony_iso` 内部用的同一步，此处抽成**可复用引理**。 -/

/-- ★★★ **逐 quartet 一致 ⟹ 树同构**（binary 情形）。

ASTRAL / parsimony / 任何「逐 quartet 得分最大」的估计量在树层的收口步骤。 -/
theorem ml_tree_iso_of_quartet_agreement (X : Type u) [Fintype X] [DecidableEq X]
    {m : MSCFreq.{u, v} X} (hT : m.tree.IsBinary)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (hagree : ∀ (S : Finset X) (hS : S.card = 4),
      qt.q S hS = m.q S hS ∨ qt.q S hS = (m.q S hS).swap) :
    Nonempty (Iso qt.tree m.tree) :=
  QuartetDecidesTree X qt m.toQuartetTree hqt hT hagree

/-! ## 3. 接线：三分支 MSC 给出**显式** gap（`Identifiable` 前提非空洞） -/

/-- ★★ **接线（`Identifiability.argmax_unique` 的定量版）**：

三分支 MSC 的期望得分（一致概率 `mscConcordant t` 与竞争拓扑概率 `mscDiscordant t`）
在 `t > 0` 时给出**显式正 gap** `mscConcordant t − mscDiscordant t > 0`。

⟹ 本文件 `MLProblem.Identifiable` 的前提在**具体模型**上确有实例（`n = 3`），
且 gap 可**精确算出**（`= 1 − e^{−t}`，见 `mscConcordant_closed`）。 -/
theorem threeTaxon_gap (t : ℝ) (ht : 0 < t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ mscConcordant t - mscDiscordant t :=
  ⟨mscConcordant t - mscDiscordant t,
    by linarith [mscDiscordant_lt_mscConcordant ht], le_rfl⟩

/-! ## 4. ★B 反例（先造反例检查）

### 4.1 **有限样本下 ML 不必选真树**（两候选，最小反例）

候选 `{t, t'}`，真树 `t`，期望得分 `(0, −1)`（gap `δ = 1`）。
`n = 0`（一个位点）时观测得分取 `(−1, 0)`，与期望的偏差 `1 > δ/2`：
argmax 是 `t' ≠ truth`。**⟹ 「有限样本下 ML 一定选真树」是假命题** ✗
（本文件的 `ml_statisticallyConsistent` 只能是「最终」形式，不可加强为逐样本）。 -/

/-- 2 候选类型（`t` 真树 / `t'` 竞争树）。

⚠️ `Fintype` **手工给**（不用 `deriving`）：deriving 生成的 `univ` 在本环境里
触发 `↑enumList` 与 `enumList` 的强制转换不一致（`Finset.mem_univ` 无法改写）。 -/
inductive TwoTree where
  | good : TwoTree
  | bad : TwoTree
  deriving DecidableEq

instance : Fintype TwoTree where
  elems := {TwoTree.good, TwoTree.bad}
  complete := by intro x; cases x <;> simp

/-- 期望得分：真树 `t` 得 `0`，竞争树 `t'` 得 `−1`。 -/
def twoTreeExpected : TwoTree → ℝ
  | .good => 0
  | .bad => -1

/-- 观测得分：`n = 0` 时**反了**（`t'` 反而更高），`n ≥ 1` 起等于期望。 -/
def twoTreeObs (n : ℕ) : TwoTree → ℝ
  | .good => if n = 0 then -1 else 0
  | .bad => if n = 0 then 0 else -1

theorem twoTreeObs_eq_of_ne_zero {n : ℕ} (hn : n ≠ 0) (t : TwoTree) :
    twoTreeObs n t = twoTreeExpected t := by
  cases t <;> simp [twoTreeObs, twoTreeExpected, hn]

theorem twoTreeObs_converges :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t : TwoTree,
      |twoTreeObs n t - twoTreeExpected t| < ε := by
  intro ε hε
  refine ⟨1, fun n hn t => ?_⟩
  rw [twoTreeObs_eq_of_ne_zero (by omega) t, sub_self, abs_zero]
  exact hε

/-- ★B 用的 ML 问题（`n = 0` 是一个**有限样本**）。 -/
def twoTreeProblem : MLProblem TwoTree where
  truth := .good
  expected := twoTreeExpected
  obs := twoTreeObs
  converges := twoTreeObs_converges

/-- `t' ≠ t`（★B 反例里用来表述「选错树」）。 -/
theorem twoTree_ne : (TwoTree.bad : TwoTree) ≠ TwoTree.good := by decide

theorem twoTreeProblem_identifiable : twoTreeProblem.Identifiable := by
  intro t ht
  cases t
  · exact absurd rfl ht
  · norm_num [MLProblem.Identifiable, twoTreeProblem, twoTreeExpected]

/-- ★B **有限样本下 ML 可以选错树**：存在 ML 问题 ＋ 观测 argmax 规则，
使**期望得分唯一最大**（可识别）成立，但第 `0` 个样本的 argmax **不是**真树。 -/
theorem ml_finite_sample_not_true :
    ∃ (P : MLProblem TwoTree) (E : ℕ → TwoTree),
      P.Identifiable ∧ (∀ t : TwoTree, P.obs 0 t ≤ P.obs 0 (E 0)) ∧ E 0 ≠ P.truth := by
  refine ⟨twoTreeProblem, fun _ => .bad, twoTreeProblem_identifiable, ?_, ?_⟩
  · intro t
    cases t <;> norm_num [twoTreeProblem, twoTreeObs, twoTreeExpected]
  · exact twoTree_ne

/-! ### 4.2 **有限性不可去**：无限候选空间上「严格最大」不给正 gap -/

/-- ★B **严格最大 ⟹ 正 gap 需要有限性**：在**无限**候选空间 `[0, ∞)`（取 `−x`）
上，`x = 0` 处**严格**最大，但**不存在**正的统一 gap。

⟹ 本文件 `exists_gap` 的 `[Fintype T]` 是**必要**假设：
「ML 可识别」若把**枝长**也放进候选空间，gap 引理即失效。 -/
theorem strict_max_no_uniform_gap :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → -(x) + δ ≤ -(0 : ℝ) := by
  rintro ⟨δ, hδ, h⟩
  have := h (δ / 2) (by linarith)
  linarith

/-! ### 4.3 **不可识别 ⟹ 不一致**（模型误设 ⇒ 任何 argmax 规则都不一致） -/

/-- 期望得分**最大值不在真树处**（模型误设 / Felsenstein zone 型失效）：真树 `t` 得 `−1`，
竞争树 `t'` 得 `0`。 -/
def misspecifiedExpected : TwoTree → ℝ
  | .good => -1
  | .bad => 0

/-- 观测得分恒等于（误设的）期望得分 —— 即「无穷样本」的极限情形。 -/
def misspecifiedObs (_n : ℕ) : TwoTree → ℝ := misspecifiedExpected

theorem misspecifiedObs_converges :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t : TwoTree,
      |misspecifiedObs n t - misspecifiedExpected t| < ε := by
  intro ε hε
  refine ⟨0, fun n _ t => ?_⟩
  have hzero : misspecifiedObs n t - misspecifiedExpected t = 0 := by
    cases t <;> simp [misspecifiedObs, misspecifiedExpected]
  rw [hzero, abs_zero]
  exact hε

def misspecifiedProblem : MLProblem TwoTree where
  truth := .good
  expected := misspecifiedExpected
  obs := misspecifiedObs
  converges := misspecifiedObs_converges

theorem misspecifiedProblem_not_identifiable : ¬ misspecifiedProblem.Identifiable := by
  intro h
  have h' := h TwoTree.bad twoTree_ne
  norm_num [MLProblem.Identifiable, misspecifiedProblem, misspecifiedExpected] at h'

/-- ★B **不可识别 ⟹ 不一致**：期望得分最大者不是真树时，
**任何**取观测 argmax 的估计量 `E` 都**不**收敛到真树（每个 `N` 之后都有错样本）。

⟹ 「ML 一致性」**不能**去掉可识别性假设（Chang 1996；模型误设的失效见
Roch & Steel 2015 的拼接不一致）。 -/
theorem ml_inconsistent_of_not_identifiable :
    ∃ P : MLProblem TwoTree, ¬ P.Identifiable ∧
      ∀ E : ℕ → TwoTree, (∀ n : ℕ, ∀ t : TwoTree, P.obs n t ≤ P.obs n (E n)) →
        ¬ P.Consistent E := by
  refine ⟨misspecifiedProblem, misspecifiedProblem_not_identifiable, ?_⟩
  intro E hE hcons
  obtain ⟨N, hN⟩ := hcons
  have hEt : E N = TwoTree.bad := by
    have h1' : (0 : ℝ) ≤ misspecifiedObs N (E N) := by
      have := hE N (TwoTree.bad : TwoTree)
      simpa [misspecifiedProblem, misspecifiedObs, misspecifiedExpected] using this
    cases hEN : E N
    · rw [hEN] at h1'
      norm_num [misspecifiedObs, misspecifiedExpected] at h1'
    · rfl
  have hthis : E N = misspecifiedProblem.truth := hN N le_rfl
  rw [hEt] at hthis
  exact absurd hthis twoTree_ne

/-! ## 5. ★C 4 taxon / 3 拓扑的最小例子（有理数，`norm_num`）

**设置**：4 taxon，三个候选拓扑 `12|34`（真）· `13|24` · `14|23`。

**两层分工（诚实说明）**：

* **Lean 侧（本节）**：把该 ML 问题写成一张**具体的、有理数的**期望得分表
  `(0, −1/8, −3/8)`（真拓扑最大，gap `= 1/8`），用 `norm_num` **机械**验出
  `Identifiable` / 正 gap / argmax 唯一 —— 这是**结构**的机器核验；
  ⚠️ 表中数字是**该例子的取值**，**不是**任何模型的物理数值。
* **脚本侧**（`scripts/msc/w11d_ml_ident_check.py`，**从镜像取件**）：在 **2-状态对称模型**
  （Neyman；4 taxon，边参数为精确有理数）上**不分**地算出三个拓扑的 16 个位点模式概率
  （`fractions.Fraction`，**无 Monte Carlo**），并核验：三分布精确归一；
  两两**精确不同** ⟹ 由 **Gibbs 不等式**真拓扑的**期望对数似然严格最大**（这就是
  「ML 可识别」的模型层结论）；再用 **Pinsker** `KL ≥ ½·TV²` 给出该 gap 的**精确有理下界**
  （脚本实测 `TV = 1/42`、`4/105` ⟹ 下界 `1/3528`、`8/11025`，均 `> 0`）。
* ⟹ 本节的 `Identifiable` 前提**非空洞**：模型层确有实例（脚本），结构的机器核验在 Lean 侧。 -/

/-- ★C 4 taxon 三拓扑的**具体期望得分表**（有理数）：`12|34` 真树 `0`，另两个 `−1/8`、`−3/8`。 -/
def fourTaxonExpected : Fin 3 → ℝ := ![0, -1 / 8, -3 / 8]

/-- ★C 的具体 ML 问题（观测恒等于期望 —— 无穷样本极限；有限样本反例见 ★B）。 -/
def fourTaxonProblem : MLProblem (Fin 3) where
  truth := 0
  expected := fourTaxonExpected
  obs := fun _ => fourTaxonExpected
  converges := fun ε hε => ⟨0, fun _ _ t => by
    have hzero : fourTaxonExpected t - fourTaxonExpected t = 0 := sub_self _
    rw [hzero, abs_zero]; exact hε⟩

/-- ★C **4 taxon 例子的可识别性**（真拓扑唯一最大）。 -/
theorem fourTaxonProblem_identifiable : fourTaxonProblem.Identifiable := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  · simp [fourTaxonProblem, fourTaxonExpected]; norm_num
  · simp [fourTaxonProblem, fourTaxonExpected]; norm_num

/-- ★C **具体 gap `= 1/8`**：任何非真拓扑都至少差 `1/8`。

⚠️ `1/8` 是**该例子**的数字（**本节的取值**，不是模型层的物理数值 ——
模型层的 gap 见 `scripts/msc/w11d_ml_ident_check.py` 的精确有理下界 `1/3528` / `8/11025`），
不是一般定理的常数。 -/
theorem fourTaxonML_gap :
    ∀ t : Fin 3, t ≠ fourTaxonProblem.truth →
      fourTaxonExpected t + 1 / 8 ≤ fourTaxonExpected fourTaxonProblem.truth := by
  intro t ht
  fin_cases t
  · exact absurd rfl ht
  · simp [fourTaxonProblem, fourTaxonExpected]; norm_num
  · simp [fourTaxonProblem, fourTaxonExpected]; norm_num

/-- ★C **反空真**：4 taxon 例子的 argmax 恰是真树（对任何 argmax 规则）。 -/
theorem fourTaxon_argmax_eq_truth {t : Fin 3}
    (hmax : ∀ s : Fin 3, fourTaxonProblem.obs 0 s ≤ fourTaxonProblem.obs 0 t) :
    t = fourTaxonProblem.truth := by
  refine MLProblem.argmax_eq_truth_of_close fourTaxonProblem
    (δ := 1 / 8) (fun s hs => fourTaxonML_gap s hs) (n := 0) ?_ hmax
  intro s
  have hzero : fourTaxonProblem.obs 0 s - fourTaxonProblem.expected s = 0 := by
    simp [fourTaxonProblem]
  rw [hzero, abs_zero]
  norm_num
/-! ## 6. 显式缺口（**不硬编、不弱化**） -/

/-- ❌ **缺口（一般模型类的可识别性输入 · 模型层）**：对 **JC69 / K80 / GTR**、
任意 `n ≥ 4`、任意枝长，**期望对数似然在真树处唯一最大**（Chang 1996 的 identifiability 定理）。

**为何落缺口而不是硬编**：本库尚无「一般 `n` 的位点模式似然」对象（即 `expected` 从何而来），
故此处只能把该**输入**抽象声明为谓词。本文件已把它的**下游**证成定理
（`exists_gap` ＋ `argmax_eq_truth_of_close` ＋ `ml_statisticallyConsistent`），
并给出 `n = 3` 三分支 MSC 的**已证**实例（`threeTaxon_gap`）。 -/
def generalModelIdentifiability_gap (Θ : Type) [Fintype Θ] (truth : Θ) (expected : Θ → ℝ) : Prop :=
  ∀ θ : Θ, θ ≠ truth → expected θ < expected truth

/-- ★ **缺口只在模型层**：一旦模型层输入（上方谓词）到位，**下游无条件成立** ——
这正是 `MLProblem.exists_gap` 的同一论证（`wrong := (· ≠ truth)`）。 -/
theorem generalModelIdentifiability_gap_of_finite
    (Θ : Type) [Fintype Θ] (truth : Θ) (expected : Θ → ℝ) (wrong : Θ → Prop)
    (h : ∀ θ, wrong θ → expected θ < expected truth) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ, wrong θ → expected θ + δ ≤ expected truth := by
  classical
  by_cases hne : (Finset.univ.filter (fun θ : Θ => wrong θ)).Nonempty
  · set S : Finset ℝ := (Finset.univ.filter (fun θ : Θ => wrong θ)).image
      (fun θ => expected truth - expected θ) with hS
    have hSne : S.Nonempty := by rw [hS]; exact hne.image _
    refine ⟨S.min' hSne, ?_, ?_⟩
    · obtain ⟨θ, hθ, heq⟩ := Finset.mem_image.mp (S.min'_mem hSne)
      have hw : wrong θ := (Finset.mem_filter.mp hθ).2
      rw [← heq]
      linarith [h θ hw]
    · intro θ hw
      have hmem : expected truth - expected θ ∈ S := by
        rw [hS]
        exact Finset.mem_image.mpr
          ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ θ, hw⟩, rfl⟩
      have := S.min'_le _ hmem
      linarith
  · exact ⟨1, one_pos, fun θ hw =>
      absurd ⟨θ, Finset.mem_filter.mpr ⟨Finset.mem_univ θ, hw⟩⟩ hne⟩

end Phylo.Stat.MLIdentifiability
