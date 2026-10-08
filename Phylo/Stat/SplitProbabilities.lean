/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.Stat.MSC

/-!
# `Phylo.Stat.SplitProbabilities` —— ADR2017 的 split 概率与「`1/3` 阈值」

文献：E. S. Allman, J. H. Degnan, J. A. Rhodes, *Split probabilities and species tree
inference under the multispecies coalescent model*。引用一律用
`references/md/AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md` 的**行号**定位。

## 1. 原文（逐字摘录 + 行号）

**Lemma 3.1（第 315–316 行）**

```text
Lemma 3.1. If |X | = n, then the sum of the non-trivial split probabilities
is n − 3.
```

其证明（第 318–357 行）只用到两件事：(i) `Σ_{A|B} P_σ(A|B) = Σ_T P_σ(T)·(2n−3) = 2n−3`，
即「每条 unrooted binary 树恰展示 `2n−3` 个 split」；(ii) 「`X` 的 `n` 个**平凡** split 的
概率都是 `1`」（第 355–357 行）。两式相减即 `n−3`。
⚠️ 注意 `P_σ(A|B)` 是**展示概率**（`Σ_T P_σ(T)·δ_{A|B}(T)`），其全和为 `2n−3`，
**不是**归一化到 `1` 的分布。

**Proposition 3.2（第 363–374 行）**

```text
Proposition 3.2. Let σ be a binary species tree on X , with internal edge
lengths λi > ε ≥ 0, and A|B a split of X . Then under the multispecies
coalescent model if

Pσ(A|B) ≥ (1/3) exp(−ε)

then A|B is a split on σ.

Furthermore, if (1/3) exp(−ε) is replaced with any smaller number, this
statement is no longer true: For any α < (1/3) exp(−ε), there exists a
species tree σ with branch lengths λi > ε ≥ 0 and a split A|B of X not
displayed on σ with Pσ(A|B) > α.
```

证明的两步（第 376–414 行）：**(a) 组合** —— 若 `A|B` 不被 `σ` 展示，则存在 `a₁,a₂ ∈ A`、
`b₁,b₂ ∈ B` 使 quartet `a₁a₂|b₁b₂` 也不被展示（第 379–380 行），且「展示 `A|B`」是
「展示 `a₁a₂|b₁b₂`」的**子事件**（第 387–388 行），故
`P_σ(A|B) ≤ P_σ(a₁a₂|b₁b₂) = (1/3)exp(−ℓ)`，其中 `ℓ > ε` 是诱导 quartet 的中心路径长；
**(b) 解析** —— `(1/3)exp(−ℓ) < (1/3)exp(−ε)`。紧性（第 395–414 行）：取
`σ = (((a,b):λ₁,σ₁:λ₂):λ₃,σ₂:λ₄)`，`λ₂,λ₄` 充分大时 `A|B` 不被展示而 `P_σ(A|B)` 可任意接近
`(1/3)exp(−λ₁)`，取 `λ₁ > ε` 即可超过任意 `α < (1/3)exp(−ε)`。

**Corollary 3.3（第 415–421 行）**：正枝长时 `P_σ(A|B) ≥ 1/3 ⟹ A|B` 被 `σ` 展示
（第 423 行：`Set ε = 0 in the preceding theorem`）。

**Theorem 4.1（第 656–677 行）**：`a,b,c,d` 在 `σ` 上诱导 quartet `ab|cd` 时
`Σ_{sep ac,bd} P_σ(A|B) ≤ Σ_{sep ad,bc} P_σ(A|B) = Σ_{sep ab,cd} P_σ(A|B)`
（分离的定义见第 652–654 行）。

## 2. `|X| = 4`：非平凡 split 恰 `3` 个

`|X| = 4` 时非平凡（**无向**）split 恰 `3` 个，与 `MSCProof` 的权重一一对应：被物种树
展示的那个为 `mscConcordant t`，另两个各为 `mscDiscordant t`（`t` = 内部枝长，溯祖单位）。
`splitProb4 t displayed` 就是 ADR2017 的 `P_σ(A|B)`（**无向**口径）；`n = 4` 的 Lemma 3.1
（`lemma_3_1_four`）与 Prop 3.2（`prop_3_2_four`，紧性 `prop_3_2_tight_four`）都已证。

## 3. 记账（有向 / 无向）

`Phylo.Split` 的 `Split α = KPartition α 2` 用 `Fin 2` 索引把两侧**有序化**
（`Phylo/Split.lean` 第 210–220 行：`sideA = parts 0`、`sideB = parts 1`；`swap` 对调两侧），
所以 ADR2017 的一个**无向** split 在本库对应 `r` 与 `r.swap` **两个**值。两个后果：

* `MSCProof.mscP` 给每个**有向** `2|2` split「无向概率的一半」，故 `r` 与 `r.swap` 的**和**
  才是无向概率（`mscP_add_swap_of_isConc` / `mscP_add_swap_of_not_isConc`）；
* 「平凡 split 恰 `n` 个」在本库的**有向**口径里是 `2n` 个（缺口 G1）。

⚠️ 另有一条**不同的**记账：`MSCProof.mscP` 是 4 元集上**归一化到 `1`** 的分布（`mscP_sum`），
它给 `1|3` 的平凡 split 记 `0`；而 ADR2017 的 `P_σ(A|B)` 是**展示概率**，平凡 split 取 `1`、
全和 `2n−3`。两者只在**平凡 split** 上不同，在非平凡 split 上一致（这正是 `n = 4` 时
`lemma_3_1_four` 与 `mscP_sum` 给出同一个 `1` 的原因）。

## 4. 本文件交付（零 `sorry` / 零 `axiom`）

* `splitProb4` —— `|X| = 4` 的无向 split 概率（`true` = 被展示，`false` = 不被展示）；
* `lemma_3_1_four` —— **Lemma 3.1 的 `n = 4` 实例**（`n − 3 = 1`）；
* `prop_3_2_four` / `prop_3_2_four_ge` —— **Prop 3.2 的 `n = 4` 实例**（阈值 `(1/3)exp(−ε)`）；
* `prop_3_2_tight_four` —— **紧性**的 `n = 4` 实例；
* `cor_3_3_four` —— **Cor 3.3 的 `n = 4` 实例**（`ε = 0`，阈值 `1/3`）；
* `sum_filter_not_eq_sub_card` —— 一般账目恒等式（**已证**）；
* `lemma_3_1_arithmetic_core` / `lemma_3_1_ordered_conditional` —— 一般 `n` 的 Lemma 3.1 的
  **算术核**（**条件形式**：把原文证明里的两条计数事实当假设）；
* `prop_3_2_analytic_step` / `prop_3_2_general_conditional` —— 一般 `n` 的 Prop 3.2 的
  **解析收尾**与**逻辑收尾**（**条件形式**：把 quartet 归约 + 子事件不等式当假设）；
* `Separates` + `mscP_add_swap_of_isConc` / `mscP_add_swap_of_not_isConc` / `sum_two_two_mscP`
  —— 与 `Phylo.Split`（`sideA` / `sideB` / `swap`）和 `MSCProof.mscP` 的接合；
  **Theorem 4.1 的 `n = 4` 实例未做**（它需要的分离族计数落成缺口 G3）。

## 5. 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| `\|X\| = 4` 的 Lemma 3.1 | ✅ **已证**（`lemma_3_1_four`） |
| `\|X\| = 4` 的 Prop 3.2 与**紧性**、Cor 3.3 | ✅ **已证**（`prop_3_2_four`, `prop_3_2_tight_four`, `cor_3_3_four`） |
| 一般 `n`：Lemma 3.1 的**算术核**（给定两条计数事实） | ✅ **已证**（`lemma_3_1_arithmetic_core`, `lemma_3_1_ordered_conditional`） |
| 一般 `n`：Prop 3.2 的**解析收尾**（`ℓ > ε` ⟹ `(1/3)exp(−ℓ) < (1/3)exp(−ε)`） | ✅ **已证**（`prop_3_2_analytic_step`） |
| 一般 `n`：Prop 3.2 的**逻辑收尾**（子事件不等式 ⟹ 阈值命题） | ✅ **已证**（`prop_3_2_general_conditional`） |
| 有向 → 无向的记账桥（`mscP` 的 `r` 与 `r.swap`） | ✅ **已证**（`mscP_add_swap_of_isConc`, `mscP_add_swap_of_not_isConc`, `sum_two_two_mscP`） |
| **一般 `n` 的「MSC split 概率」对象** `P_σ(A\|B)` | ❌ **未构造**（本库只有 `Fin 4` 的 quartet 权重；缺口 G2） |
| 一般 `n` 的 **Lemma 3.1 本体**、**Prop 3.2 本体**、**Cor 3.3 本体** | ❌ **未证**（缺 `P_σ(A\|B)`；缺口 G2） |
| quartet 归约 + 子事件不等式（第 379–388 行） | ❌ **未证**（`prop_3_2_general_conditional` 把它当**假设**） |
| `Split (Fin n)` 的**平凡 split 计数 `= 2n`**（有向口径，`n ≥ 3`） | ❌ **未证**（缺口 G1；连 `n = 4` 也未在本文件判定，见 §4） |
| `n = 4` 的三个**分离族计数**各 `= 2`（Thm 4.1 所需） | ❌ **未证**（缺口 G3） |
| 一般 `n` 的 **MSC gene tree 分布**（`Σ_T P_σ(T) = 1`） | ❌ **未构造**（Lemma 3.1 的证明第 318–353 行缺此载体） |
| 「每条 unrooted binary 树恰展示 `2n−3` 个 split」 | ⚠️ **库内已有两条组件**：边数 `IsBinary.card_edgeFinset`（`Phylo/Algorithm/BinaryCount.lean` 第 74 行，`\|E\| = 2ℓ − 3`）与「边 ↔ split」的 `Split.IsSplitOf` / `splitOfEdge`（`Phylo/Split.lean`；`Phylo/InternalEdge.lean` 第 933 行给出 `\|Σ(T)\| = 4\|X\| − 6` 的记账，即无向 `2n−3`）。本文件**未**把它们与 gene tree 分布拼起来 |
| **Theorem 4.1（一般 `n` 与 `n = 4`）** | ❌ **未做**（规格 §5.1 说「有余力再做」） |
| `P_σ(A\|B)` 的**测度层**解释 | ⚠️ 本文件与 `Coalescent` / `MSCProof` 同一层次：**实数层**，不是测度层的随机变量 |

### 缺口的确切内容（全文零 `sorry` / 零 `axiom`）

* **缺口 G1** —— `card_trivial_splits_gap`：`Split (Fin n)`（有向）上平凡 split 恰 `2n` 个
  （`n ≥ 3`）。缺的是「`r ↦` `sideA` 的唯一单点」这一双射的一般 `n` 形式。
* **缺口 G2** —— `msc_split_probability_object_gap`：一般 `n` 的 MSC split 概率对象
  `P_σ(A|B)`（binary 物种树 `σ` + MSC）。它的**两条计数性质**与**阈值性质**就是
  Lemma 3.1 / Prop 3.2 在一般 `n` 下的全部内容。⚠️ 该 `Prop` 里**没有**「内部枝长 `> ε`」
  与「展示 `A|B` 是展示某个 quartet 的子事件」这两条（没有带长度的树对象，无法陈述）；
  ⚠️ 它的断言**弱于**真正的数学内容（真正的缺口是 `P` 必须由 gene tree 分布**诱导**）；
  它是「还欠什么」的账目，**本文件不在任何证明中使用它**。
* **缺口 G3** —— `card_separates_four_gap`：`n = 4` 的三个分离族各恰 `2` 个有向 split
  （Theorem 4.1 的 `n = 4` 实例所需的组合计数）。
-/

noncomputable section

open Classical

open Phylo.Stat.MSCProof

namespace Phylo.Stat.SplitProbabilities

/-! ## 0. 两个拆分侧谓词 -/

/-- **平凡 split**：有一侧是单点集（即 `{x} | X∖{x}`）。
⚠️ ADR2017 用**无向**口径（`n` 个平凡 split，第 355–357 行）；本库 `Split α` 是**有向**的
（`sideA` / `sideB`，`swap` 对调两侧），故每个无向平凡 split 对应 `r` 与 `r.swap` 两个值，
有向口径下共 `2n` 个（缺口 G1）。 -/
def IsTrivialSplit {α : Type*} [Fintype α] [DecidableEq α] (r : Split α) : Prop :=
  r.sideA.card = 1 ∨ r.sideB.card = 1

/-- `A|B` **分离** `Y₀` 与 `Y₁`（ADR2017 第 652–654 行：`Y₀ ⊆ A`、`Y₁ ⊆ B`，或对调两侧）。 -/
def Separates {α : Type*} [Fintype α] [DecidableEq α] (r : Split α) (Y₀ Y₁ : Finset α) : Prop :=
  (Y₀ ⊆ r.sideA ∧ Y₁ ⊆ r.sideB) ∨ (Y₁ ⊆ r.sideA ∧ Y₀ ⊆ r.sideB)

/-! ## 1. `|X| = 4` 的 (无向) split 概率 -/

/-- `|X| = 4`：split `A|B` 在内部枝长 `t` 的 **binary** 物种树下的 MSC split 概率。
`displayed = true` 表示 `A|B` 是该物种树**展示**的那个非平凡 split（概率 `mscConcordant t`）；
`displayed = false` 表示另两个**不被展示**的非平凡 `2|2` split（各 `mscDiscordant t`，
`MSCProof`）。取值是 ADR2017 的 `P_σ(A|B)`（**无向**口径，见文件头 §3）。 -/
noncomputable def splitProb4 (t : ℝ) (displayed : Bool) : ℝ :=
  if displayed then mscConcordant t else mscDiscordant t

/-- `splitProb4` 在被展示的 split 上取值 `mscConcordant t`。 -/
theorem splitProb4_true (t : ℝ) : splitProb4 t true = mscConcordant t := by
  simp only [splitProb4, ↓reduceIte]

/-- `splitProb4` 在不被展示的 split 上取值 `mscDiscordant t`。 -/
theorem splitProb4_false (t : ℝ) : splitProb4 t false = mscDiscordant t := by
  simp only [splitProb4, Bool.false_eq_true, ↓reduceIte]

/-- 被展示的 split 的概率就是库内既有的 `Coalescent.pConcordant`。 -/
theorem splitProb4_true_eq_pConcordant (t : ℝ) :
    splitProb4 t true = Coalescent.pConcordant t := by
  rw [splitProb4_true, mscConcordant_eq]

/-- 不被展示的 split 的概率就是库内既有的 `Coalescent.pDiscordant`。 -/
theorem splitProb4_false_eq_pDiscordant (t : ℝ) :
    splitProb4 t false = Coalescent.pDiscordant t := by
  rw [splitProb4_false, mscDiscordant_eq]

/-- `t ≥ 0` 时 split 概率非负。 -/
theorem splitProb4_nonneg {t : ℝ} (ht : 0 ≤ t) (A : Bool) : 0 ≤ splitProb4 t A := by
  cases A with
  | false => rw [splitProb4_false]; exact (mscDiscordant_pos t).le
  | true => rw [splitProb4_true]; exact mscConcordant_nonneg ht

/-- `t > 0` 时被展示的 split 概率严格为正。 -/
theorem splitProb4_true_pos {t : ℝ} (ht : 0 < t) : 0 < splitProb4 t true := by
  rw [splitProb4_true]; exact mscConcordant_pos ht

/-- 不被展示的 split 概率对**任意** `t` 都严格为正（`mscDiscordant_pos`）。 -/
theorem splitProb4_false_pos (t : ℝ) : 0 < splitProb4 t false := by
  rw [splitProb4_false]; exact mscDiscordant_pos t

/-! ## 2. Lemma 3.1（`n = 4`）与一般 `n` 的账目核 -/

/-- ★★★ **Lemma 3.1 的 `n = 4` 实例**（ADR2017 第 315–316 行）：
`4` 元集的 `3` 个非平凡（无向）split 的概率之和 `= 4 − 3 = 1`。
（`MSCProof.mscConcordant_add_two` 的改写。） -/
theorem lemma_3_1_four (t : ℝ) :
    mscConcordant t + mscDiscordant t + mscDiscordant t = 1 := by
  have h := mscConcordant_add_two t
  linarith

/-- `lemma_3_1_four` 的 `splitProb4` 形式。 -/
theorem lemma_3_1_four_splitProb4 (t : ℝ) :
    splitProb4 t true + splitProb4 t false + splitProb4 t false = 1 := by
  rw [splitProb4_true, splitProb4_false]
  exact lemma_3_1_four t

/-- **Lemma 3.1 证明的账目（`n = 4`，并列事实，不是推论）**：ADR2017 的口径下
`4` 个平凡 split 各取 `1`、`3` 个非平凡 split 合计 `1`，故全部 `7` 个（无向）split 之和
`= 4 + 1 = 5 = 2·4 − 3`。这里把两项**并列写下**，只是为了与原文第 353 行的 `2n − 3` 对账。 -/
theorem lemma_3_1_four_bookkeeping (t : ℝ) :
    (4 : ℝ) * 1 + (mscConcordant t + mscDiscordant t + mscDiscordant t) = 2 * 4 - 3 := by
  rw [lemma_3_1_four]
  norm_num

/-- **一般账目恒等式（已证）**：若 `w` 在 `triv` 上恒取值 `1`，则
`Σ_{¬triv} w = Σ_all w − #triv`。这就是 ADR2017 第 353–357 行「`2n−3` 减去 `n`」的一般形式
（把「全部」「平凡」两侧的计数换成假设）。 -/
theorem sum_filter_not_eq_sub_card {ι : Type*} [Fintype ι] (triv : ι → Prop)
    [DecidablePred triv] (w : ι → ℝ) (htriv : ∀ i, triv i → w i = 1) :
    ∑ i ∈ Finset.univ.filter (fun i => ¬ triv i), w i
      = (∑ i, w i) - ((Finset.univ.filter triv).card : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset ι))
    (p := triv) (f := w)
  have htrivsum : ∑ i ∈ Finset.univ.filter triv, w i = ((Finset.univ.filter triv).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun i hi => htriv i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const]
    simp
  linarith

/-- ★★ **一般 `n` 的 Lemma 3.1 的算术核（条件形式，已证）**：
设在一个有限 split 集合 `ι` 上，平凡 split 恰 `n` 个、各取 `1`，且**全部** split 的
展示概率之和为 `2n − 3`（ADR2017 第 318–353 行的结论），则非平凡 split 的展示概率之和
为 `n − 3`。
⚠️ 两条计数事实是**假设**（一般 `n` 下未证：平凡 split 计数见缺口 G1，`2n−3` 见缺口 G2）；
本定理只做账目。 -/
theorem lemma_3_1_arithmetic_core {ι : Type*} [Fintype ι] (triv : ι → Prop)
    [DecidablePred triv] (w : ι → ℝ) (n : ℕ)
    (hcard : ((Finset.univ.filter triv).card : ℝ) = (n : ℝ))
    (htriv : ∀ i, triv i → w i = 1) (hsum : ∑ i, w i = 2 * (n : ℝ) - 3) :
    ∑ i ∈ Finset.univ.filter (fun i => ¬ triv i), w i = (n : ℝ) - 3 := by
  rw [sum_filter_not_eq_sub_card triv w htriv, hsum, hcard]
  ring

/-- ★★ **一般 `n` 的 Lemma 3.1 的算术核（本库 `Split (Fin n)` 的**有向**口径，条件形式）**：
本库 `Split (Fin n)` 把两侧有序化，故每个无向 split 计两次（文件头 §3）：
平凡 split 有 `2n` 个、全部展示概率之和为 `2(2n − 3)`，于是非平凡之和为 `2(n − 3)`
（除以 `2` 即原文的无向 `n − 3`；`n = 4` 时 `= 2`，对应 `lemma_3_1_four` 的 `1` 的两倍）。
⚠️ `hcard` 是**假设**（缺口 G1）。 -/
theorem lemma_3_1_ordered_conditional {n : ℕ} (w : Split (Fin n) → ℝ)
    (hcard : ((Finset.univ.filter (fun r : Split (Fin n) => IsTrivialSplit r)).card : ℝ)
      = 2 * (n : ℝ))
    (htriv : ∀ r : Split (Fin n), IsTrivialSplit r → w r = 1)
    (hsum : (∑ r : Split (Fin n), w r) = 2 * (2 * (n : ℝ) - 3)) :
    ∑ r ∈ Finset.univ.filter (fun r : Split (Fin n) => ¬ IsTrivialSplit r), w r
      = 2 * ((n : ℝ) - 3) := by
  rw [sum_filter_not_eq_sub_card (fun r : Split (Fin n) => IsTrivialSplit r) w htriv, hsum,
    hcard]
  ring

/-! ## 3. Prop 3.2（`1/3` 阈值）与 Cor 3.3 -/

/-- ★★★ **Prop 3.2 的 `n = 4` 实例**（ADR2017 第 363–369 行）：内部枝长 `t > ε` 时，
**不被**物种树展示的 split 的 MSC 概率 `< (1/3)exp(−ε)`。
（原文的 `λ_i > ε` 在 `n = 4` 时就是 `t > ε`，`ε ≥ 0` 不是必需的。） -/
theorem prop_3_2_four {t ε : ℝ} (h : ε < t) (A : Bool) (hdis : A = false) :
    splitProb4 t A < (1 / 3) * Real.exp (-ε) := by
  subst hdis
  rw [splitProb4_false, mscDiscordant_eq, Coalescent.pDiscordant]
  have hexp : Real.exp (-t) < Real.exp (-ε) := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- ★★★ **Prop 3.2 的 `n = 4` 实例（原文方向）**：若 split 概率 `≥ (1/3)exp(−ε)`
（`t > ε`），则它**被**物种树展示（即 `A = true`）。 -/
theorem prop_3_2_four_ge {t ε : ℝ} (h : ε < t) (A : Bool)
    (hge : (1 / 3) * Real.exp (-ε) ≤ splitProb4 t A) : A = true := by
  cases A with
  | false => exact absurd hge (not_le.mpr (prop_3_2_four h false rfl))
  | true => rfl

/-- ★★ **Prop 3.2 证明的解析收尾（一般 `n`，已证）**：若一个 split 的展示概率被
`(1/3)exp(−ℓ)` 控制（`ℓ` = 它诱导的 quartet 的中心路径长），而 `ℓ > ε`，则该概率
`< (1/3)exp(−ε)`。即原文第 384 行的 `(1/3)exp(−ℓ) < (1/3)exp(−ε)`。 -/
theorem prop_3_2_analytic_step {ℓ ε p : ℝ} (hℓ : ε < ℓ)
    (h : p ≤ (1 / 3) * Real.exp (-ℓ)) : p < (1 / 3) * Real.exp (-ε) := by
  have hexp : Real.exp (-ℓ) < Real.exp (-ε) := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- ★★★ **一般 `n` 的 Prop 3.2（条件形式，已证）**：若「每个不被展示的 split `r` 都存在
`ℓ > ε` 使 `P r ≤ (1/3)exp(−ℓ)`」（= 原文第 379–388 行的 quartet 归约 + 子事件不等式，
其中 `ℓ` 是诱导 quartet 的中心路径长），则 `P r ≥ (1/3)exp(−ε) ⟹ r` 被展示。
⚠️ 那条 quartet 归约本身是**假设**（一般 `n` 下未证，见诚实边界表）。 -/
theorem prop_3_2_general_conditional {n : ℕ} (P : Split (Fin n) → ℝ)
    (displayed : Split (Fin n) → Prop) {ε : ℝ}
    (hq : ∀ r : Split (Fin n), ¬ displayed r →
      ∃ ℓ : ℝ, ε < ℓ ∧ P r ≤ (1 / 3) * Real.exp (-ℓ)) :
    ∀ r : Split (Fin n), (1 / 3) * Real.exp (-ε) ≤ P r → displayed r := by
  intro r hr
  by_contra hnot
  obtain ⟨ℓ, hℓ, hbound⟩ := hq r hnot
  exact absurd hr (not_le.mpr (prop_3_2_analytic_step hℓ hbound))

/-- ★★★ **紧性（`n = 4`）**（ADR2017 第 371–374 / 395–414 行）：对**任意**
`α < (1/3)exp(−ε)`，存在内部枝长 `t > ε` 使**不被展示**的 split 的概率 `> α`。
（原文用 `λ₂,λ₄ → ∞` 把 `P_σ(A|B)` 压到 `(1/3)exp(−λ₁)`；`n = 4` 时该概率**恰好**是
`(1/3)exp(−t)`，故取 `t > ε` 充分接近 `ε` 即可。） -/
theorem prop_3_2_tight_four {ε α : ℝ} (hα : α < (1 / 3) * Real.exp (-ε)) :
    ∃ t : ℝ, ε < t ∧ α < splitProb4 t false := by
  rcases lt_or_ge 0 α with hα0 | hα0
  · have h3pos : 0 < 3 * α := by linarith
    have h3lt : 3 * α < Real.exp (-ε) := by linarith
    have hlog : Real.log (3 * α) < -ε := by
      have h := Real.log_lt_log h3pos h3lt
      rwa [Real.log_exp] at h
    refine ⟨(ε + -Real.log (3 * α)) / 2, by linarith, ?_⟩
    rw [splitProb4_false, mscDiscordant_eq, Coalescent.pDiscordant]
    have hlt : Real.log (3 * α) < -((ε + -Real.log (3 * α)) / 2) := by linarith
    have hexp : 3 * α < Real.exp (-((ε + -Real.log (3 * α)) / 2)) := by
      have h := Real.exp_lt_exp.mpr hlt
      rwa [Real.exp_log h3pos] at h
    linarith
  · refine ⟨ε + 1, by linarith, ?_⟩
    rw [splitProb4_false, mscDiscordant_eq, Coalescent.pDiscordant]
    have hpos : 0 < (1 / 3) * Real.exp (-(ε + 1)) := by positivity
    linarith

/-- ★★ **Cor 3.3 的 `n = 4` 实例**（ADR2017 第 415–421 行）：正内部枝长 `t > 0` 时
（`ε = 0`）`P_σ(A|B) ≥ 1/3 ⟹ A|B` 被物种树展示。 -/
theorem cor_3_3_four {t : ℝ} (ht : 0 < t) (A : Bool)
    (h : 1 / 3 ≤ splitProb4 t A) : A = true := by
  cases A with
  | false =>
    rw [splitProb4_false, mscDiscordant_eq] at h
    exact absurd h (not_le.mpr (Coalescent.pDiscordant_lt_third ht))
  | true => rfl

/-! ## 4. 与 `Split` / `QuartetFreq` 的接合

⚠️ `n = 4` 的**计数**（平凡 split `= 8`、`02|13` 等三个分离族各 `= 2`）在本文件里
**没有**证出：`Split α = KPartition α 2` 的 `Fintype` 实例是 `Fintype.ofInjective` 拉回来的，
`decide` **无法**把 `(Finset.univ : Finset (Split (Fin 4))).card`（或它的过滤）归约成数字。
`MSCProof` 之所以能用 `decide`，是因为它先用 `card_filter_two` 把计数搬到
`Fin 4` 的 `powersetCard` 上；那条桥只覆盖 `↥univ` 口径的 `2|2` split。
故这些计数落成缺口 G3（见 §5）。`MSCProof.card_two_two` 已给出 `↥univ` 口径下
`2|2`（有向）split 恰 `6` 个。 -/

/-- ★★ **有向 → 无向的记账桥（一致 split）**：`4` 元集上一个**一致** `2|2` split 的两个
有向版本（`r` 与 `r.swap`）的 MSC 权重之和 = 该无向 split 的概率 `splitProb4 t true`。 -/
theorem mscP_add_swap_of_isConc {t : ℝ} {S : Finset (Fin 4)} {hS : S.card = 4}
    {r : Split ↥S} (hc : isConc S r) :
    mscP t S hS r + mscP t S hS r.swap = splitProb4 t true := by
  rw [mscP_of_isConc hc, mscP_swap t S hS r, mscP_of_isConc hc, splitProb4_true]
  ring

/-- ★★ **有向 → 无向的记账桥（不一致 `2|2` split）**。 -/
theorem mscP_add_swap_of_not_isConc {t : ℝ} {S : Finset (Fin 4)} {hS : S.card = 4}
    {r : Split ↥S} (hc : ¬ isConc S r) (h2 : r.sideA.card = 2) :
    mscP t S hS r + mscP t S hS r.swap = splitProb4 t false := by
  rw [mscP_of_not_isConc_of_card hc h2, mscP_swap t S hS r,
    mscP_of_not_isConc_of_card hc h2, splitProb4_false]
  ring

/-- ★★ **`n = 4` 的「非平凡 split 之和」在 `MSCProof.mscP` 上的对账**：
`4` 元集的 `6` 个有向 `2|2` split 的权重之和 `= 1 = 4 − 3`
（`1|3` 的平凡 split 在 `mscP` 的归一化下取 `0`，见文件头 §3 的第二条记账）。
即 `MSCProof.mscP_sum` 的 `2|2` 部分，与 `lemma_3_1_four` 说的是同一个 `1`。 -/
theorem sum_two_two_mscP (t : ℝ) (hS : (Finset.univ : Finset (Fin 4)).card = 4) :
    (∑ r ∈ (Finset.univ : Finset (Split MSCProof.U)).filter (fun r => r.sideA.card = 2),
        mscP t Finset.univ hS r) = 1 := by
  rw [← mscP_sum t Finset.univ hS]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro r _ hr
  exact mscP_of_not_isConc_of_not_card
    (fun hc => hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.1⟩))
    (fun h2 => hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))

/-! ## 5. 诚实边界：显式缺口（`def … : Prop`，**不是** `axiom`，也**不是** `sorry`）

下面三条把本文件**没有**证明的东西写成显式命题（规格 §0.4 / §5.2 的要求：宁可留缺口，
不许把未证内容伪装成定理）。它们在本文件中**从未被当作假设使用**。 -/

/-- ❌ **缺口 G1**：`Split (Fin n)`（**有向**口径）上的**平凡 split 计数**。
`Split α = KPartition α 2` 用 `Fin 2` 索引把两侧有序化（`Phylo/Split.lean` 第 210–220 行），
每个无向平凡 split `{x} | X∖{x}` 对应 `r` 与 `r.swap` 两个值，故 `n ≥ 3` 时恰 `2n` 个。

**未证**：缺「`r ↦` `sideA` 的唯一单点」这个双射的一般 `n` 形式（`n = 2` 时公式不同：
`Split (Fin 2)` 只有 `2` 个元素，两侧都是单点，故 `2 ≠ 2n = 4`）。
本文件也没有对 `n = 4` 判定它 —— `Split (Fin 4)` 的 `Fintype` 实例无法被 `decide` 归约
（见 §4 的说明）。**未证。** -/
def card_trivial_splits_gap : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (Finset.univ.filter (fun r : Split (Fin n) => IsTrivialSplit r)).card = 2 * n

/-- ❌ **缺口 G2（一般 `n` 的 MSC split 概率对象）** —— ADR2017 一般 `n` 的 Lemma 3.1 /
Prop 3.2 / Cor 3.3 **唯一**真正缺的载体。

ADR2017 的 `P_σ(A|B)` 是「随机 gene tree **展示** split `A|B`」的概率
（第 318–353 行：`Σ_{A|B} P_σ(A|B) = Σ_T P_σ(T)(2n−3) = 2n−3`），
它**不是**归一化到 `1` 的分布（平凡 split 取 `1`，全和 `2n−3`）。
本库只有 `Fin 4` 的 quartet 权重（`MSCProof`），**没有**一般 `n` 的这个对象；
一般 `n` 的 **MSC gene tree 分布**（`Σ_T P_σ(T) = 1`）同样未构造。

本 `Prop` 把「要造什么」写成一条存在性清单：`σ` 索引 binary 物种树；平凡 split 恒被展示
且取 `1`；每个 `σ` 上全部 split 的展示概率之和 `= 2(2n−3)`（**有向**口径 = 无向 `2n−3` 的
两倍，见文件头 §3）；且 Prop 3.2 的阈值结论成立。

⚠️ 两处**没有**写进这个 `Prop`：(i) 「内部枝长 `> ε`」（没有「带长度」的树对象，故无法陈述）；
(ii) 「展示 `A|B`」是「展示某个 quartet」的子事件（缺口 G3 之外的组合内容）。
⚠️ **该断言的强度弱于**真正的数学内容：真正的缺口是 `P` 必须由「binary 物种树 + MSC 的
gene tree 分布」**诱导**，而本式只要求存在一个满足上述性质的 `P`。**未构造、未证**，
且**本文件不在任何证明中使用它**。 -/
def msc_split_probability_object_gap : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ ε : ℝ, 0 ≤ ε →
    ∃ (σ : Type) (_ : Nonempty σ) (Displays : σ → Split (Fin n) → Prop)
      (P : σ → Split (Fin n) → ℝ),
      (∀ s r, IsTrivialSplit r → Displays s r ∧ P s r = 1) ∧
      (∀ s, ∑ r : Split (Fin n), P s r = 2 * (2 * (n : ℝ) - 3)) ∧
      (∀ s r, (1 / 3) * Real.exp (-ε) ≤ P s r → Displays s r)

/-- ❌ **缺口 G3（Theorem 4.1 的 `n = 4` 计数，第 656–677 行）**：
`(a,b,c,d) = (0,1,2,3)` 时，分离 `{0,2}` 与 `{1,3}`、`{0,3}` 与 `{1,2}`、`{0,1}` 与 `{2,3}`
的（有向）split **各恰 `2` 个**（即 `02|13`、`03|12`、`01|23` 三个无向 split 的两个方向）。

有了它 + `mscP_add_swap_of_isConc` / `mscP_add_swap_of_not_isConc`，Theorem 4.1 的 `n = 4`
实例就是 `mscDiscordant t ≤ mscDiscordant t ≤ mscConcordant t`（`MSCProof.mscDiscordant_lt_mscConcordant`）。

**未证**：`Split (Fin 4)` 的 `Fintype` 实例（`Fintype.ofInjective` 拉回）无法被 `decide`
归约，而 `MSCProof.card_filter_two` 这条计数桥只覆盖 `↥univ` 口径的 `2|2` split。**未证。** -/
def card_separates_four_gap : Prop :=
  ((Finset.univ : Finset (Split (Fin 4))).filter
      (fun r => Separates r ({0, 2} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4)))).card = 2 ∧
    ((Finset.univ : Finset (Split (Fin 4))).filter
      (fun r => Separates r ({0, 3} : Finset (Fin 4)) ({1, 2} : Finset (Fin 4)))).card = 2 ∧
    ((Finset.univ : Finset (Split (Fin 4))).filter
      (fun r => Separates r ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)))).card = 2

end Phylo.Stat.SplitProbabilities
