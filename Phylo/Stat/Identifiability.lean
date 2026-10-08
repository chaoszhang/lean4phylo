/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof

/-!
# `Phylo.Stat.Identifiability` —— ADR 2011：由 rooted triple 概率**反解内部枝长**

Allman–Degnan–Rhodes (2011) 第 **300–306** 行给出三分支物种树的**关键公式**：

> 设 `a,b` 比 `c` 更近，内部枝长为 `t`，`p` = 随机有根基因树里「`a,b` 比二者与 `c` 更近」的概率，
> 则 **`t = − log( (3/2)(1 − p) )`**。（引 Nei 1987；Wakeley 2008。）

而本库 `Phylo/Stat/MSCProof.lean` 的 `mscConcordant t = 1 − ⅔e^{−t}` **正是**这个 `p`
（同一个 4 叶/三分支公式）。于是：

* ★★★ `three_halves_mul_one_sub`：等价的无 `log` 形式 `(3/2)(1 − p) = e^{−t}`；
* ★★★ `branchLength_eq`：ADR2011 的**原式** `−log((3/2)(1 − mscConcordant t)) = t`；
* ★★★ `mscConcordant_injective`：`t ↦ p(t)` **单射** ⇒ **内部枝长可识别**；
* ★★★ `argmax_unique`：`t > 0` 时**任何**竞争拓扑的概率都**严格小于**真拓扑的
  ⇒ **拓扑可识别**（argmax 唯一）；
* ★★ `tripleDist` / `tripleDist_sum` / `tripleDist_injective`：把三分支的 rooted-triple
  **分布**写成一个三元组对象，给出 **Corollary 2**（第 **316** 行）的单射版。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| ADR2011 第 300–306 行的公式（三分支） | **已证**（`branchLength_eq`） |
| **Proposition 1**（第 309 行）在 `n = 3` 的情形 | **已证**（`mscConcordant_injective` + `argmax_unique`） |
| **Corollary 2**（第 316 行）的三分支情形 | **已证**（`tripleDist_injective`） |
| **Proposition 1 的一般 `n ≥ 3`** | ❌ **未做**：需要「**有根 triple 系统**」这一**纯组合**接口（「每条内部边都有两个叶子其 MRCA 在该边上，外加一个从该边父结点分出的叶子」），本库**尚无**该接口；缺的是组合层，不是概率层 |
| **Lemma 4 的 5-taxon 版本**（第 962–971 行） | ❌ **未做**：其证明是「**完整**溯祖历史的重标号对称性」（五个标记谱系进入祖先种群后合并，所有无根基因树同形 ⇒ 重标号给出等概率），**不是**首次合并对的计数。本库现有的是 **4 叶**版本（`MSCKingman.root_topology_class_prob`，首次合并对 `6 = 3 × 2`）。⚠️ 该引理**只对 5 taxa 成立**（第 **973–974** 行：6 taxa 起有两种无根形状，结论失效） |
| **Proposition 3**（第 900 行，`\|X\| = 4`：`σ⁻` 可识别、`σ⁺` 不可） | ❌ **未做**：依赖 4 叶**无根**基因树分布（`(2n−5)!! = 3` 个无根拓扑的显式概率表） |
| 一般 `n` 的基因树分布 | ❌ 未做（属 W10e） |
-/

noncomputable section

namespace Phylo.Stat.Identifiability

open Phylo.Stat.MSCProof

/-! ## 1. ADR2011 第 300–306 行的公式 -/

/-- ★★★ **ADR2011 第 300–306 行公式的无 `log` 形式**：`(3/2)·(1 − p) = e^{−t}`，
即 `p = 1 − ⅔e^{−t}` 的等价改写。 -/
theorem three_halves_mul_one_sub (t : ℝ) :
    (3 / 2) * (1 - mscConcordant t) = Real.exp (-t) := by
  rw [mscConcordant_closed]
  have h : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  field_simp
  ring

/-- ★★★ **ADR2011 第 300–306 行的原式**：内部分支长度由概率**反解**出来，
`t = − log( (3/2)(1 − p) )`，`p = mscConcordant t`。 -/
theorem branchLength_eq (t : ℝ) :
    -Real.log ((3 / 2) * (1 - mscConcordant t)) = t := by
  rw [three_halves_mul_one_sub, Real.log_exp, neg_neg]

/-! ## 2. 可识别性 -/

/-- ★★★ **内部枝长可识别**：`t ↦ p(t)` 是**单射**（不同的枝长给出不同的概率）。 -/
theorem mscConcordant_injective : Function.Injective mscConcordant := by
  intro a b h
  rw [mscConcordant_closed, mscConcordant_closed] at h
  have h2 : (2 / 3 : ℝ) * Real.exp (-a) = (2 / 3) * Real.exp (-b) := by linarith
  have h3 : Real.exp (-a) = Real.exp (-b) :=
    mul_left_cancel₀ (show (2 / 3 : ℝ) ≠ 0 by norm_num) h2
  have h4 : -a = -b := Real.exp_injective h3
  linarith

/-- ★★★ **拓扑可识别（argmax 唯一）**：`t > 0` 时**任何**竞争拓扑的概率都**严格小于**
真拓扑的概率 ⇒ 「取概率最大的那个拓扑」唯一地还原出真拓扑。 -/
theorem argmax_unique {t : ℝ} (ht : 0 < t) {q : ℝ} (hq : q ≤ mscDiscordant t) :
    q < mscConcordant t :=
  lt_of_le_of_lt hq (mscDiscordant_lt_mscConcordant ht)

/-! ## 3. Corollary 2（三分支版）：分布决定枝长 -/

/-- 三分支物种树的 **rooted-triple 概率分布**：`(一致, 不一致₁, 不一致₂)`。 -/
def tripleDist (t : ℝ) : ℝ × ℝ × ℝ := (mscConcordant t, mscDiscordant t, mscDiscordant t)

/-- 它确实是一个概率分布（三项和 `= 1`）。 -/
theorem tripleDist_sum (t : ℝ) :
    (tripleDist t).1 + (tripleDist t).2.1 + (tripleDist t).2.2 = 1 := by
  rw [tripleDist]
  linarith [mscConcordant_add_two t]

/-- ★★ **Corollary 2（三分支版）**：rooted-triple **分布**决定内部枝长。 -/
theorem tripleDist_injective : Function.Injective tripleDist := by
  intro a b h
  exact mscConcordant_injective (congrArg Prod.fst h)

/-- ★★ 分布相同 ⇒ 枝长相同（`Corollary 2` 的直白形式）。 -/
theorem branchLength_determined_by_distribution {a b : ℝ}
    (h : mscConcordant a = mscConcordant b) : a = b :=
  mscConcordant_injective h

/-- ★★ **一致的概率 > 1/3 ⟺ 内部枝长 > 0**（[`Coalescent`] 侧严格性判据的移植）：
`p = 1/3` 恰对应星形树（`t = 0`），`t > 0` 才使真拓扑严格占优。 -/
theorem concordant_gt_third_iff {t : ℝ} (ht : 0 ≤ t) :
    1 / 3 < mscConcordant t ↔ 0 < t := by
  rw [mscConcordant_closed]
  have hexp : 0 < Real.exp (-t) := Real.exp_pos _
  constructor
  · intro h
    by_contra hle
    have h0 : t = 0 := le_antisymm (not_lt.mp hle) ht
    rw [h0, neg_zero, Real.exp_zero] at h
    norm_num at h
  · intro h
    have h1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith

end Phylo.Stat.Identifiability
