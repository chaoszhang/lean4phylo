/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.InternalEdge

/-!
# `Phylo.Stat.ReciprocalMonophyly` —— Zhu–Degnan–Steel 2011 的 clade/clan 闭形式

本文件形式化 **Zhu, Degnan & Steel (2011)** *Clades, clans and reciprocal monophyly under
neutral evolutionary models*（arXiv:1101.1311）中**能落地**的部分：
论文各定理的**闭形式**（有理函数）＋它们之间的**算术恒等式**，
以及 Prop 6.5 的**树层**内容（与本库 `Cladogram.IsClade` 接合）。

## 1. 文献摘录（逐条带行号；行号指 `references/md/ZhuDegnanSteel2011_*.md`）

> **模型（第 191–216 行）**：`3. The Yule-Harding-Kingman process`。
> 「…the resulting probability distribution on rooted binary tree topologies is the same as
> that given by any … birth-death process …」（第 200–205 行）；
> 「this probability distribution on trees is precisely the same as that given by a quite
> different process, namely **Kingman's coalescent process** …」（第 208–212 行）；
> 「we will refer to it as the **Yule-Harding-Kingman (YHK) process**」（第 214–216 行）。

> **clade / clan 的定义（第 124–147 行、第 985–988 行）**：clade = **有根**树某内部顶点的
> 后代叶集（第 128–129 行）；clan = **无根**树中 `A | X−A` 是一条 split 的集合
> （第 985–988 行：「we say that a subset `A` of `X` is a **clan** of an unrooted
> phylogenetic `X`–tree `T′` if `A|X − A` is a split of `T′`」）。

> **Lemma 6.1（第 991–992 行）**：
> 「Given a rooted binary `X`–tree, `T`, a set `A` is a clan of `T −ρ` if and only if either
> `A` is a clade of `T` or `X − A` is a clade of `T`.」
> 其证明（第 1038–1044 行）给出 **包含-排除**：
> 「`qn(A) = pn(A) + pn(X − A) − pn(A, X − A)`」（第 1040 行）。

> **YHK 的性质（第 230–249 行）**：(EP) 交换性（第 230–232 行）、(GE) 群消除（第 234–238 行）、
> (SC) 抽样一致性（第 246–249 行）。

> **Lemma 4.1（第 279–286 行）**：「Let `Xn(a)` be the number of proper clades of size `a`
> in `TX`. Then `E[Xn(a)] = 2n / (a(a+1))`, `1 ≤ a ≤ n − 1`.」

> **Lemma 4.2（第 294–317 行）**：`pn(a) = (2n / (a(a+1))) · C(n,a)^{-1}` 若 `1 ≤ a ≤ n − 1`；
> 否则 `0`。（OCR 把公式拆散，原文即 `2n/(a(a+1))` 乘 `C(n,a)` 的倒数。）

> **Lemma 4.3（第 369–385 行）**：「For `1 ≤ a ≤ n`, `p̂n(a, n − a) = (2/(n − 1)) · C(n,a)^{-1}`。」

> **Lemma 4.4（第 389–396 行）**：「Let `k = a + b`. Then
> `p̂n(a, b) = 4·a!·b!·(n − k)! / ((n − 1)! · k(k² − 1))`.」
> ⚠️ **范围修正（脚本复核，见 §3）**：`k = n` 时该表达式**不等于**真值
> （真值就是 Lemma 4.3 的值），故本文件把 Lemma 4.4 限定在 `k = a + b < n`。

> **Theorem 4.5（第 452–526 行）**：`pn(A, B)`（有根树上 `A`、`B` **都是 proper clade** 的概率）
> 按 6 种情形给出；其中
> `Rn(a, b) := 4n / (a(a+1)(b+1)) · C(n,b)^{-1} · C(b,a)^{-1}`（第 479–503 行，情形 2 `A ⊊ B`），
> `rn(a, b) := 4a!b!(n − a − b)! / (n − 1)! · Gn(a, b)`（第 504–509 行，情形 5），
> `Gn(a, b) := n/(ab(a+1)(b+1)) − (a(a+1) + b(b+1) + ab)/(ab(a+1)(b+1)(a+b+1))
> + 1/((a+b)((a+b)² − 1))`（第 511–526 行），
> 情形 4（`A ∩ B = ∅, A ∪ B = Xn`）给 `p̂n(a, n − a)`（第 466 行），情形 6 给 `0`（第 475 行）。

> **Theorem 5.1（第 849–888 行）**：`k > 1` 时
> 　(i) `p(a1, …, ak; Tk) = (2^{k−1} / n!) · ∏_{i=1}^{k} ai! · ∏_{v ∈ I(Tk)}
>      (Σ_{i} ai·Iv(Ai) − 1)!`（第 853–873 行）；
> 　(ii) `p(a1, …, ak) = Σ_{Tk} p(a1, …, ak; Tk)`（第 881–888 行）。
> `I(Tk)` = `Tk` 的内部顶点集（第 846–847 行），`Iv(Ai)` 是指示变量（第 872–873 行）。

> **Lemma 6.2（第 1007–1036 行）**：「`qn(a) = 2n[1/(a(a+1)) + 1/(b(b+1)) − 1/((n−1)n)]·C(n,a)^{-1}`，
> where `a = |A|, b = n − a`.」证明即第 1040 行的包含-排除。

> **Theorem 6.3（第 1077–1110 行）**：
> 　(i) `a + b = n` 时 `qn(a, b) = q_{a+b}(A) = (2a!b!/(a+b−1)!)[1/(a(a+1)) + 1/(b(b+1))
>      − 1/((a+b)(a+b−1))]`（第 1079–1103 行）；
> 　(ii) `a + b < n` 时 `qn(a, b) = rn(a, b) + Rn(a, n−b) + Rn(b, n−a) − p̂n(b, n−b)p_{n−b}(a)
>      − p̂n(a, n−a)p_{n−a}(b)`（第 1105–1110 行）；
> 论文举例 `q6(2, 2) = 7/225`（第 1051 行）。

> **Theorem 6.4（第 1171–1191 行）**：`n = a1 + a2 + a3` 时
> 　(i) `q(a1, a2, a3) = (4a1!a2!a3!/(n−1)!) · Σ_{i=1}^{3} 1/((n−ai)((n−ai)²−1))`（第 1173–1182 行）；
> 　(ii) `q′(a1,a2,a3) = qn(a1,a2) + qn(a1,a3) + qn(a2,a3) − 2q(a1,a2,a3)`（第 1190–1191 行）；
> 论文举例 `q(2,2,2) = 1/75`、`q′(2,2,2) = 1/15`（第 1166 行）。

> **Proposition 6.5（第 1265–1288 行）**：`A1, A2` 有交、`ai = |Ai|`。
> 　(i) 若 `A1 ⊂ A2` 则 `Qn(A1, A2) = qn(a1, n − a2)`；`A2 ⊂ A1` 同理（第 1267–1272 行）；
> 　(ii) 否则（互不包含）：`Qn(A1, A2) = qn(a1 − a12, a2 − a12)` 若 `A1 ∪ A2 = X`，否则 `0`，
>      其中 `a12 = |A1 ∩ A2|`（第 1276–1288 行）。
> 证明（第 1290–1299 行）：「if `A1 ⊂ A2` then `A1` and `A2` are clans of an unrooted
> phylogenetic `X`–tree `T` **if and only if** `A1` and `X − A2` are clans of `T`.」
> 「in order for `A1` and `A2` to be clans of the same unrooted phylogenetic `X`–tree `T`
> a **necessary condition** is that `A1 ∪ A2 = X`. Moreover, under this condition, `A1` and
> `A2` are clans of `T` **if and only if** `A1 − A1 ∩ A2` and `A2 − A1 ∩ A2` are clans of `T`。」

## 2. 两个层次：**树层** vs **概率层**（本文件的分界线）

* **树层**：给定一棵树，「`A` 是 clade / clan」是**确定性**命题。本库的载体
  `Cladogram X`（`Phylo/Core.lean`）是**无根**的，其
  `Cladogram.IsClade A := ∃ s, T.IsSplitOf s ∧ s.sideA = A`（`Phylo/InternalEdge.lean:589`）
  —— 按 `Phylo/InternalEdge.lean:585–587` 的术语提示，**这正是学界的「clan」**（= 论文
  第 985–988 行的 clan），**不是**论文第 128–129 行的有根 clade。
  本文件 §5 把 Prop 6.5 的树层内容接到这个 `IsClade` 上。
* **概率层**：论文的 `pn` / `p̂n` / `qn` / `q` 都是**随机 YHK 树**上的**事件概率**。
  这需要「`n` 叶 rooted binary 树上的 YHK 概率律」这一对象 ——
  **本库没有它**：库内只有 `Coalescent.mergePairsFinset`（一步合并均匀，
  `Phylo/Stat/Coalescent.lean:264`）、`MSCKingman.root_topology_class_prob`
  （`Fin 4` 的拓扑类权重）与 `MSCProof.mscFreqFin4`（`Fin 4` 的具体 `MSCFreq`）。
  故本文件把概率层**如实**落成缺口（§6）。

⚠️ **措辞纪律**：本文件里 `pn`、`qn` 等是**闭形式函数**（`def`），
**不是**「概率」——除 §4 的 `qnExhaustive_two_two_eq_mscConcordant_zero`（4 叶数值桥）之外，
本文件**不声称**它们等于任何概率。
它们**是**论文公式的**忠实转写**，且已由脚本在 `n ≤ 6` 上以**精确有理数全穷举**核对为正确数值。

## 3. 数值复核（`scripts/msc/zds2011_monophyly.py`，精确有理数、无 Monte Carlo）

脚本独立实现 YHK 生成过程（均匀随机标签次序 + 每步均匀随机选叶分裂，
= 论文第 193–216 行 / 第 1000 行），在 `n ≤ 6` 上**穷举所有** `n!·(n−1)!` 条路径，
与论文闭形式逐条比对。结论（`总判定：ALL OK`）：

| 复核项 | 结果 |
|---|---|
| Lemma 4.2（`n = 4,5,6` 全部 `a`） | ✅ 一致 |
| Lemma 4.3（`n = 4,5,6` 全部 `a`） | ✅ 一致 |
| Lemma 4.4（`k = a+b < n`，6 组） | ✅ 一致 |
| Lemma 4.4 的 `k = n` 取值 | ❌ **与真值不符**（真值 = Lemma 4.3）；故限定 `k < n` |
| Theorem 4.5 情形 2（`R_n`，4 组） | ✅ 一致 |
| Theorem 4.5 情形 5（`r_n`，4 组） | ✅ 一致 |
| Lemma 6.2（`n = 4,5,6` 全部 `a`） | ✅ 一致 |
| Theorem 6.3(i)（8 组，且 = Lemma 6.2 在 `n = a+b`） | ✅ 一致 |
| Theorem 6.3(ii)（5 组） | ✅ 一致 |
| Theorem 6.4(i)（5 组三元组） | ✅ 一致 |
| 论文锚点 `q(2,2,2) = 1/75`、`q′(2,2,2) = 1/15`、`q6(2,2) = 7/225` | ✅ 一致 |

## 4. 本文件交付

* **§3**（`def` 层）：论文各定理闭形式的**忠实转写**（11 个 `def`）；
* **§4**：这些闭形式之间的**算术恒等式**（真证，无 `sorry`）＋ 论文三个数值锚点；
* **§5**：Prop 6.5 的**树层**内容（与库内 `Cladogram.IsClade` 接合）；
* **§6**：**显式缺口**（概率层，3 个 `def … : Prop`，未被证、也未被引用）。

## 5. 诚实边界（**没做到的**，逐条）

| 条目 | 状态 |
|---|---|
| 闭形式的**数值正确性** | ✅ 脚本 `n ≤ 6` 全穷举复核（§3） |
| 闭形式之间的**算术恒等式** | ✅ 已证 4 条：`clanProb_eq_inclusionExclusion`（Lemma 6.2 ⟸ Lemma 6.1 的包含-排除）、`pnHat_eq_pn_mul`（Lemma 4.4 ⟸ 4.2 ⊗ 4.3，论文第 398–444 行的证明）、`qnExhaustive_eq_clanProb`（Theorem 6.3(i) ⟸ Lemma 6.2）、`clanProb_eq_unfolded`；另有 `choose_mul_pn`（Lemma 4.1 **右端**的算术核对）、`qnExhaustive_two_two`、`qn_six_two_two`、`qTriple_two_two_two`、`qConvex_two_two_two` 等锚点 |
| **`pn` 是 YHK 律下的 clade 概率**（Lemma 4.1 / 4.2 的**概率层**） | ❌ **未证** —— 缺口 `YHKClanLawGap`（§6） |
| **`qn` 是「两个 clan」的概率**（Theorem 6.3 的概率层） | ❌ **未证** —— 缺口 `TwoClanLawGap`（§6） |
| **`q` 是「三个 clan」的概率**（Theorem 6.4 的概率层） | ❌ **未证** —— 缺口 `TripleClanLawGap`（§6） |
| **Theorem 5.1**（一般 `k` 个 clade，含指定 `Tk`） | ❌ **未落地**（连闭形式都依赖 `Iv(Ai)` 这套 `Tk` 上的指示变量；本库无「内部顶点 + 后代叶集」的层面对象） |
| **Theorem 4.5 一般形** | ⚠️ **部分**：情形 2 / 5 的 `Rn` / `rn` / `Gn` 已转录并复核；**情形 1 / 3 / 4 / 6 的分情形组合**未写成单一 `def` |
| 论文 Lemma 4.4 印刷范围 `k ≤ n` | ⚠️ **修正为 `k < n`**（脚本证据见 §3；`k = n` 用 Lemma 4.3） |
| **有根树 clade** 的库内对象 | ❌ **不存在**：库内 `Cladogram` 是无根载体、`IsClade` 是 clan 语义，故 Theorem 4.5（有根 clade）**没有**库内对应物 |
| Prop 6.5 的**树层**内容 | ⚠️ **部分**：`isClade_compl`（补集对称）、`union_eq_univ_of_isClade`（第 1294–1295 行的**必要性**）、`isClade_sdiff_inter_iff`（第 1296–1297 行）、`isClade_and_compl_iff`（第 1291–1292 行）、`disjoint_compl_of_subset` 已证；**未**把 Prop 6.5 的两条情形组合成单一 `theorem` |
| Prop 6.5 的**概率层** | ❌ **未证**（树层部分见上一行） |
| `x = 4` 之外的**概率层**桥 | ❌ 只有 `qnExhaustive 2 2 = mscConcordant 0` 这一条**数值**桥（§4） |
-/

noncomputable section

open Classical

namespace Phylo.Stat.ReciprocalMonophyly

/-! ## 3. 闭形式（论文公式的忠实转写）

⚠️ 本节的每个 `def` 都是**论文公式的字面转写**，不是概率断言（见文件头 §2）。 -/

/-- **Lemma 4.2**（`references/md/ZhuDegnanSteel2011_*.md` 第 **294–317** 行）：
`pn(a) = (2n / (a(a+1))) · C(n,a)^{-1}`（`1 ≤ a ≤ n − 1`），否则 `0`。
即「给定 `a` 元子集 `A` 是 `n` 叶 YHK 树的 **proper clade** 的概率」—— ⚠️ **概率层的意义未证**
（缺口 `YHKClanLawGap`）；本 `def` 只是那个有理函数。 -/
noncomputable def pn (n a : ℕ) : ℝ :=
  if a = 0 ∨ n ≤ a then 0
  else 2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) * ((n.choose a : ℝ))⁻¹

/-- **Lemma 4.3**（第 **369–385** 行）：`p̂n(a, n − a) = (2/(n − 1)) · C(n,a)^{-1}`。
即「`A` 与 `X − A` 是**姐妹 clade**（等价地 `A` 是**极大真 clade**）的概率」。 -/
noncomputable def pnHatExh (n a : ℕ) : ℝ := 2 / ((n : ℝ) - 1) * ((n.choose a : ℝ))⁻¹

/-- **Lemma 4.4**（第 **389–396** 行）：`p̂n(a, b) = 4·a!·b!·(n−k)! / ((n−1)!·k(k²−1))`，`k = a+b`。
⚠️ 脚本复核显示**只在 `k < n` 时成立**（`k = n` 时应取 `pnHatExh`，见文件头 §3）。 -/
noncomputable def pnHat (n a b : ℕ) : ℝ :=
  4 * (a.factorial : ℝ) * (b.factorial : ℝ) * ((n - a - b).factorial : ℝ)
    / (((n - 1).factorial : ℝ) * ((a + b : ℕ) : ℝ) * (((a + b : ℕ) : ℝ) ^ 2 - 1))

/-- **Lemma 6.2**（第 **1007–1036** 行）：`qn(a) = 2n[1/(a(a+1)) + 1/(b(b+1)) − 1/((n−1)n)]·C(n,a)^{-1}`，
`b = n − a`。即论文的「`A` 是无根 YHK 树的 **clan** 的概率」。
⚠️ 本 `def` 用 `n − a` 的 `ℕ` 截断；有意义的用法都带 `a ≤ n`。
其语义来源是 Lemma 6.1 的**包含-排除**（第 1040 行），见 `clanProb_eq_inclusionExclusion`。 -/
noncomputable def clanProb (n a : ℕ) : ℝ :=
  2 * (n : ℝ)
    * (1 / ((a : ℝ) * ((a : ℝ) + 1))
       + 1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
       - 1 / (((n : ℝ) - 1) * (n : ℝ)))
    * ((n.choose a : ℝ))⁻¹

/-- **Theorem 6.3(i)**（第 **1079–1103** 行）：`a + b = n` 时
`qn(a, b) = (2a!b!/(a+b−1)!)·[1/(a(a+1)) + 1/(b(b+1)) − 1/((a+b)(a+b−1))]`。
论文把它读作**互单系**（reciprocal monophyly）情形：两组互斥且穷尽 ⟹ 它们同时成 clan。
⚠️ **概率层的意义未证**（缺口 `TwoClanLawGap`）；本 `def` 只是那个有理函数。 -/
noncomputable def qnExhaustive (a b : ℕ) : ℝ :=
  2 * (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b - 1).factorial : ℝ)
    * (1 / ((a : ℝ) * ((a : ℝ) + 1)) + 1 / ((b : ℝ) * ((b : ℝ) + 1))
       - 1 / (((a + b : ℕ) : ℝ) * (((a + b : ℕ) : ℝ) - 1)))

/-- **Theorem 4.5 的 `Gn`**（第 **511–526** 行，属于情形 5）：
`Gn(a,b) = n/(ab(a+1)(b+1)) − (a(a+1)+b(b+1)+ab)/(ab(a+1)(b+1)(a+b+1))
+ 1/((a+b)((a+b)²−1))`。 -/
noncomputable def Gn (n a b : ℕ) : ℝ :=
  (n : ℝ) / ((a : ℝ) * (b : ℝ) * ((a : ℝ) + 1) * ((b : ℝ) + 1))
    - ((a : ℝ) * ((a : ℝ) + 1) + (b : ℝ) * ((b : ℝ) + 1) + (a : ℝ) * (b : ℝ))
        / ((a : ℝ) * (b : ℝ) * ((a : ℝ) + 1) * ((b : ℝ) + 1) * ((a : ℝ) + (b : ℝ) + 1))
    + 1 / (((a : ℝ) + (b : ℝ)) * (((a : ℝ) + (b : ℝ)) ^ 2 - 1))

/-- **Theorem 4.5 情形 5 的 `rn`**（第 **504–509** 行）：
`rn(a,b) = 4a!b!(n − a − b)! / (n − 1)! · Gn(a,b)`（`A ∩ B = ∅`、`A ∪ B ⊊ Xn`）。 -/
noncomputable def rn (n a b : ℕ) : ℝ :=
  4 * (a.factorial : ℝ) * (b.factorial : ℝ) * ((n - a - b).factorial : ℝ)
    / ((n - 1).factorial : ℝ) * Gn n a b

/-- **Theorem 4.5 情形 2 的 `Rn`**（第 **479–503** 行）：
`Rn(a,b) = 4n/(a(a+1)(b+1)) · C(n,b)^{-1} · C(b,a)^{-1}`（`A ⊊ B`）。 -/
noncomputable def Rn (n a b : ℕ) : ℝ :=
  4 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1) * ((b : ℝ) + 1))
    * ((n.choose b : ℝ))⁻¹ * ((b.choose a : ℝ))⁻¹

/-- **Theorem 6.3(ii)**（第 **1105–1110** 行，`a + b < n`）：
`qn(a,b) = rn(a,b) + Rn(a, n−b) + Rn(b, n−a) − p̂n(b, n−b)p_{n−b}(a) − p̂n(a, n−a)p_{n−a}(b)`。
⚠️ 其中 `p̂n(·, n−·)` 取 **Lemma 4.3**（穷尽情形），不是 Lemma 4.4 —— 见文件头 §3。 -/
noncomputable def qn (n a b : ℕ) : ℝ :=
  rn n a b + Rn n a (n - b) + Rn n b (n - a)
    - pnHatExh n b * pn (n - b) a - pnHatExh n a * pn (n - a) b

/-- **Theorem 6.4(i)**（第 **1173–1182** 行）：`n = a1 + a2 + a3` 时
`q(a1,a2,a3) = (4a1!a2!a3!/(n−1)!) · Σ_{i=1}^{3} 1/((n−ai)((n−ai)²−1))`。
（`n − ai` 就是另外两者之和，故这里直接写成 `a2+a3` 等，数值相同。） -/
noncomputable def qTriple (a1 a2 a3 : ℕ) : ℝ :=
  4 * (a1.factorial : ℝ) * (a2.factorial : ℝ) * (a3.factorial : ℝ)
      / ((a1 + a2 + a3 - 1).factorial : ℝ)
    * (1 / (((a2 + a3 : ℕ) : ℝ) * (((a2 + a3 : ℕ) : ℝ) ^ 2 - 1))
       + 1 / (((a1 + a3 : ℕ) : ℝ) * (((a1 + a3 : ℕ) : ℝ) ^ 2 - 1))
       + 1 / (((a1 + a2 : ℕ) : ℝ) * (((a1 + a2 : ℕ) : ℝ) ^ 2 - 1)))

/-- **Theorem 6.4(ii)**（第 **1190–1191** 行）：
`q′(a1,a2,a3) = qn(a1,a2) + qn(a1,a3) + qn(a2,a3) − 2q(a1,a2,a3)`（convex 的概率）。 -/
noncomputable def qConvex (a1 a2 a3 : ℕ) : ℝ :=
  qn (a1 + a2 + a3) a1 a2 + qn (a1 + a2 + a3) a1 a3 + qn (a1 + a2 + a3) a2 a3
    - 2 * qTriple a1 a2 a3

/-! ## 4. 闭形式之间的算术恒等式（真证）

本节全部是**实数算术**，不含任何概率断言。 -/

/-- `n · (n − 1)! = n!`（`n ≥ 1`）；论文把 `2n·C(n,a)^{-1}` 化成 `2a!b!/(n−1)!` 用的就是这步。 -/
theorem self_mul_factorial_pred {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * ((n - 1).factorial : ℝ) = (n.factorial : ℝ) := by
  cases n with
  | zero => omega
  | succ m =>
      rw [Nat.add_sub_cancel m 1, Nat.factorial_succ]
      push_cast
      ring

/-- `C(n,k)^{-1} = k!·(n−k)!/n!`（`k ≤ n`）。 -/
theorem choose_inv_eq (n k : ℕ) (h : k ≤ n) :
    ((n.choose k : ℝ))⁻¹ = (k.factorial : ℝ) * ((n - k).factorial : ℝ) / (n.factorial : ℝ) := by
  have hcast : ((n.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ)
      = (n.factorial : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial h]
  have hk : ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) ≠ 0 := by
    apply mul_ne_zero <;> exact_mod_cast Nat.factorial_ne_zero _
  have hmain : ((n.choose k : ℝ)) * ((k.factorial : ℝ) * ((n - k).factorial : ℝ))
      = (n.factorial : ℝ) := by
    rw [← hcast]; ring
  calc ((n.choose k : ℝ))⁻¹
      = ((n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)))⁻¹ := by
        congr 1
        rw [eq_div_iff hk]
        exact hmain
    _ = (k.factorial : ℝ) * ((n - k).factorial : ℝ) / (n.factorial : ℝ) := inv_div _ _

/-- **Lemma 4.2 的「否则」支**。 -/
theorem pn_eq_zero_of_not_range {n a : ℕ} (h : a = 0 ∨ n ≤ a) : pn n a = 0 := by
  simp only [pn, h, ↓reduceIte]

/-- **Lemma 4.2 的闭形式**（`1 ≤ a < n`）。 -/
theorem pn_of_range {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) :
    pn n a = 2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) * ((n.choose a : ℝ))⁻¹ := by
  have h : ¬ (a = 0 ∨ n ≤ a) := by omega
  simp only [pn, h, ↓reduceIte]

/-- `pn` 在有效范围内非负。 -/
theorem pn_nonneg {n a : ℕ} (h2 : a < n) : 0 ≤ pn n a := by
  by_cases h1 : a = 0
  · rw [pn_eq_zero_of_not_range (Or.inl h1)]
  · rw [pn_of_range (by omega) h2]
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have ha : (0 : ℝ) < (a : ℝ) := by
      have : 0 < a := by omega
      exact_mod_cast this
    have hc : (0 : ℝ) < ((n.choose a : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (le_of_lt h2)
    positivity

/-- `pn` 在有效范围内严格为正。 -/
theorem pn_pos {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) : 0 < pn n a := by
  rw [pn_of_range h1 h2]
  have hn : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have hc : (0 : ℝ) < ((n.choose a : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (le_of_lt h2)
  positivity

/-- ★★ **Lemma 4.1 的右端（算术核对）**：`C(n,a) · pn(a) = 2n/(a(a+1))`（`1 ≤ a < n`）。

⚠️ **这不等价于证明 Lemma 4.1**：Lemma 4.1 是关于**随机树**的 `E[Xn(a)]`，
本式只是把 `C(n,a)·pn(a)` 算出来等于论文右端 —— 概率层是缺口 `YHKClanLawGap`。 -/
theorem choose_mul_pn {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) :
    ((n.choose a : ℕ) : ℝ) * pn n a = 2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) := by
  rw [pn_of_range h1 h2]
  have hc : ((n.choose a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (le_of_lt h2)).ne'
  rw [mul_comm (2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1))) ((n.choose a : ℝ))⁻¹,
    ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- ⚙️ **Lemma 6.2 的「展开形式」**（把 `2n·(1/((n−1)n))` 算成 `2/(n−1)`）：
`clanProb n a = (2n/(a(a+1)) + 2n/((n−a)((n−a)+1)) − 2/(n−1)) · C(n,a)^{-1}`。 -/
theorem clanProb_eq_unfolded {n a : ℕ} (hn : 2 ≤ n) :
    clanProb n a
      = (2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1))
         + 2 * (n : ℝ) / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
         - 2 / ((n : ℝ) - 1)) * ((n.choose a : ℝ))⁻¹ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  have h3 : 2 * (n : ℝ) * (1 / (((n : ℝ) - 1) * (n : ℝ))) = 2 / ((n : ℝ) - 1) := by
    field_simp
  rw [clanProb,
    show 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1))
          + 1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
          - 1 / (((n : ℝ) - 1) * (n : ℝ)))
        = 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1))
            + 1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)))
          - 2 * (n : ℝ) * (1 / (((n : ℝ) - 1) * (n : ℝ))) from by ring,
    h3,
    show 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1))
          + 1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)))
        = 2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1))
          + 2 * (n : ℝ) / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)) from by ring]

/-- ★★★ **Lemma 6.2 ⟸ Lemma 6.1（包含-排除）**（第 **1040** 行）：
`qn(A) = pn(A) + pn(X − A) − p̂n(A, X − A)`。
即本文件的 `clanProb`（Lemma 6.2 的显示形式）与「自己或补是 clade」的包含-排除一致。 -/
theorem clanProb_eq_inclusionExclusion {n a : ℕ} (h1 : 1 ≤ a) (ha : a < n) :
    clanProb n a = pn n a + pn n (n - a) - pnHatExh n a := by
  have han : a ≤ n := le_of_lt ha
  have hna : n - a < n := by omega
  have hn : 2 ≤ n := by omega
  have hsub : (((n - a : ℕ)) : ℝ) = (n : ℝ) - (a : ℝ) := Nat.cast_sub han
  have hsymm : ((n.choose (n - a) : ℕ) : ℝ) = ((n.choose a : ℕ) : ℝ) := by
    rw [Nat.choose_symm han]
  rw [clanProb_eq_unfolded hn, pn_of_range h1 ha, pn_of_range (by omega) hna, pnHatExh,
    hsub, hsymm]
  ring

/-- ★★ **`pnHat`（Lemma 4.4） ⟸ `pn` ⊗ `pnHatExh`**（论文第 **398–444** 行的证明）：
`p̂n(a,b) = pn(a+b) · p̂_{a+b}(a, a+b−a)`。 -/
theorem pnHat_eq_pn_mul {n a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a + b < n) :
    pnHat n a b = pn n (a + b) * pnHatExh (a + b) a := by
  have hk1 : 1 ≤ a + b := by omega
  have hle : a ≤ a + b := by omega
  have hk2 : 2 ≤ a + b := by omega
  rw [pnHat, pn_of_range hk1 h, pnHatExh, choose_inv_eq n (a + b) (le_of_lt h),
    choose_inv_eq (a + b) a hle, Nat.sub_sub]
  have hfac : ((a + b : ℕ) : ℝ) * ((a + b - 1).factorial : ℝ) = ((a + b).factorial : ℝ) :=
    self_mul_factorial_pred hk1
  have hna : a + b - a = b := Nat.add_sub_cancel_left a b
  rw [hna]
  have hN : ((a + b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : (a + b) ≠ 0)
  have hkR : ((a + b : ℕ) : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < a + b)
    linarith
  have hk2R : ((a + b : ℕ) : ℝ) ^ 2 - 1 ≠ 0 := by
    have h2 : (2 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast hk2
    nlinarith
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have ha1R : (a : ℝ) + 1 ≠ 0 := by positivity
  have hb1R : (b : ℝ) + 1 ≠ 0 := by positivity
  have hfa : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hfb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have hf1 : ((a + b - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a + b - 1)
  have hf2 : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have hf3 : ((n - (a + b)).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - (a + b))
  have hf4 : ((a + b).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + b)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnfac : ((n).factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) :=
    (self_mul_factorial_pred (by omega : 1 ≤ n)).symm
  rw [hnfac]
  field_simp
  ring_nf

/-- ★★★ **Theorem 6.3(i) ⟸ Lemma 6.2**：`a + b = n` 时两个闭形式一致
（论文第 1112 行：「Part (i) follows from Lemma 6.2, noting that `n = a + b`」）。 -/
theorem qnExhaustive_eq_clanProb {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    qnExhaustive a b = clanProb (a + b) a := by
  have hn : 1 ≤ a + b := by omega
  have hb' : a + b - a = b := Nat.add_sub_cancel_left a b
  have hle : a ≤ a + b := by omega
  rw [qnExhaustive, clanProb, choose_inv_eq (a + b) a hle, hb']
  have hfac : ((a + b : ℕ) : ℝ) * ((a + b - 1).factorial : ℝ) = ((a + b).factorial : ℝ) :=
    self_mul_factorial_pred hn
  have hN : ((a + b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : (a + b) ≠ 0)
  have hnm1 : ((a + b : ℕ) : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < a + b)
    linarith
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have ha1R : (a : ℝ) + 1 ≠ 0 := by positivity
  have hb1R : (b : ℝ) + 1 ≠ 0 := by positivity
  have hfa : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hfb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have hf1 : ((a + b - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (a + b - 1)
  have hf2 : ((a + b).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + b)
  rw [← hfac]
  field_simp

/-- ★★ **Lemma 6.2 在 `a = 1` 的锚点**：`clanProb n 1 = 1`（`n ≥ 2`）——
单点在**任何**树上都是 clan（论文第 987 行的直接推论）。 -/
theorem clanProb_one {n : ℕ} (hn : 2 ≤ n) : clanProb n 1 = 1 := by
  have hle : (1 : ℕ) ≤ n := by omega
  have hsub : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hle]; norm_num
  have h1 : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by rw [hsub]; ring
  have hc : ((n.choose 1 : ℕ) : ℝ) = (n : ℝ) := by rw [Nat.choose_one_right]
  rw [clanProb, h1, hsub, hc]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    linarith
  field_simp
  ring_nf

/-- ★★ **Theorem 6.3(i) 在 `a = 1` 的锚点**：`qnExhaustive 1 b = 1`。 -/
theorem qnExhaustive_one_left {b : ℕ} (hb : 1 ≤ b) : qnExhaustive 1 b = 1 := by
  have hsub : (1 + b - 1 : ℕ) = b := by omega
  rw [qnExhaustive, hsub, Nat.factorial_one]
  push_cast
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
  have hbf : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have h1 : (1 : ℝ) + (b : ℝ) - 1 = (b : ℝ) := by ring
  rw [h1]
  field_simp
  ring_nf

/-- ★★ **Theorem 6.3(i) 在 `b = 1` 的锚点**：`qnExhaustive a 1 = 1`。 -/
theorem qnExhaustive_one_right {a : ℕ} (ha : 1 ≤ a) : qnExhaustive a 1 = 1 := by
  have hsub : (a + 1 - 1 : ℕ) = a := by omega
  rw [qnExhaustive, hsub, Nat.factorial_one]
  push_cast
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
  have haf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have h1 : (a : ℝ) + 1 - 1 = (a : ℝ) := by ring
  rw [h1]
  field_simp
  ring_nf

/-- `qnExhaustive 2 2 = 1/3`（论文第 1079–1103 行的 `(a,b) = (2,2)`）。 -/
theorem qnExhaustive_two_two : qnExhaustive 2 2 = 1 / 3 := by
  unfold qnExhaustive
  norm_num [Nat.factorial]

/-- ★★ **`Fin 4` 数值桥**：`qnExhaustive 2 2 = 1/3` 恰等于库内
`Phylo.Stat.MSCProof.mscConcordant 0`（4 叶 MSC 在内部枝长 `0` 时一致 quartet 的概率）。

⚠️ 这条只声称**数值相等**；「两侧是同一个 4 叶概率事件」这一**解释**依赖
「4 叶 YHK 拓扑律 = MSC 在 `t = 0` 的律」，其一般 `n` 版本是缺口 `YHKClanLawGap`。 -/
theorem qnExhaustive_two_two_eq_mscConcordant_zero :
    qnExhaustive 2 2 = Phylo.Stat.MSCProof.mscConcordant 0 := by
  rw [qnExhaustive_two_two]
  have h := Phylo.Stat.MSCProof.mscConcordant_closed 0
  rw [h]
  norm_num

/-- ★★ **Theorem 6.3(ii) 在 `(n,a,b) = (6,2,2)`**：`qn 6 2 2 = 7/225` —— 与论文第 **1051** 行
「`q6(2, 2) = 7/225`」逐字一致（脚本亦穷举复核）。 -/
theorem qn_six_two_two : qn 6 2 2 = 7 / 225 := by
  unfold qn rn Rn pnHatExh pn Gn
  norm_num [Nat.choose, Nat.factorial]

/-- **Theorem 6.4(i) 在 `(1,1,1)`**：`qTriple 1 1 1 = 1`。 -/
theorem qTriple_one_one_one : qTriple 1 1 1 = 1 := by
  unfold qTriple
  norm_num [Nat.factorial]

/-- ★★ **Theorem 6.4(i) 在 `(2,2,2)`**：`qTriple 2 2 2 = 1/75` —— 与论文第 **1166** 行一致。 -/
theorem qTriple_two_two_two : qTriple 2 2 2 = 1 / 75 := by
  unfold qTriple
  norm_num [Nat.factorial]

/-- ★★ **Theorem 6.4(ii) 在 `(2,2,2)`**：`qConvex 2 2 2 = 1/15` —— 与论文第 **1166** 行一致。 -/
theorem qConvex_two_two_two : qConvex 2 2 2 = 1 / 15 := by
  unfold qConvex
  rw [qn_six_two_two, qTriple_two_two_two]
  norm_num

/-! ## 5. 树层：Prop 6.5 与库内 `Cladogram.IsClade`

⚠️ 库内 `Cladogram.IsClade A := ∃ s, T.IsSplitOf s ∧ s.sideA = A`
（`Phylo/InternalEdge.lean:589`）取自本库的 `Cladogram`（**无根**载体），
按 `Phylo/InternalEdge.lean:585–587` 的术语提示，它**就是**论文第 985–988 行的 **clan**。
本节因此只主张 **Prop 6.5 的树层（确定性）内容**；其**概率层**是缺口 `TwoClanLawGap`。 -/

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **`IsClade` 对补集封闭**（clan 的两侧对称）：`T.IsClade Aᶜ ↔ T.IsClade A`。

这是 Prop 6.5 证明（第 1290–1299 行）两次用到的**唯一**树层事实：
「`A1` and `A2` are clans … iff `A1` and `X − A2` are clans」（第 1291–1292 行）、
「`A1` and `A2` are clans of `T` iff `A1 − A1 ∩ A2` and `A2 − A1 ∩ A2` are clans of `T`」
（第 1296–1297 行）。 -/
theorem isClade_compl (T : Cladogram X) (A : Finset X) : T.IsClade Aᶜ ↔ T.IsClade A := by
  constructor
  · rintro ⟨s, hs, hside⟩
    refine ⟨s.swap, T.isSplitOf_swap hs, ?_⟩
    rw [Split.swap_sideA, Split.sideB_eq_compl, hside]
    ext x
    simp
  · rintro ⟨s, hs, hside⟩
    refine ⟨s.swap, T.isSplitOf_swap hs, ?_⟩
    rw [Split.swap_sideA, Split.sideB_eq_compl, hside]

/-- ★★ **同一棵树上两个 clan 的两侧相容**（`SidesCompatible`），
由 `pairwiseCompatible`（`Phylo/Split.lean:894`）与 `Split.compatible_iff_sides` 得到。 -/
theorem compatible_of_isClade {T : Cladogram X} {A B : Finset X}
    (hA : T.IsClade A) (hB : T.IsClade B) : SidesCompatible A B := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  exact Split.compatible_iff_sides.mp (pairwiseCompatible T s hs t ht)

/-- ★★★ **Prop 6.5(ii) 的「必要性」半**（第 1294–1295 行）：
两个**有交**、**互不包含**的 clan 必有 `A ∪ B = X`。
（论文原文：「a **necessary condition** is that `A1 ∪ A2 = X`」。） -/
theorem union_eq_univ_of_isClade {T : Cladogram X} {A B : Finset X}
    (hA : T.IsClade A) (hB : T.IsClade B) (hne : (A ∩ B).Nonempty)
    (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) : A ∪ B = Finset.univ := by
  rcases compatible_of_isClade hA hB with h | h | h | h
  · exact absurd h hAB
  · exact absurd h hBA
  · obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter] at hx
    exact absurd hx.2 (Finset.disjoint_left.mp h hx.1)
  · exact h

/-- ★★ **Prop 6.5(ii) 的「充分性」半的算术核心**：`A ∪ B = X` 时 `A \ (A ∩ B) = Bᶜ`
（论文第 1296–1297 行把「`A1, A2` 是 clan」化归为「两个**互斥**集合是 clan」）。 -/
theorem sdiff_inter_eq_compl {A B : Finset X} (h : A ∪ B = Finset.univ) :
    A \ (A ∩ B) = Bᶜ := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  constructor
  · rintro ⟨hA, hnb⟩
    exact fun hB => hnb ⟨hA, hB⟩
  · intro hB
    refine ⟨?_, fun hAB => hB hAB.2⟩
    rcases Finset.mem_union.mp (by rw [h]; exact Finset.mem_univ x) with h' | h'
    · exact h'
    · exact absurd h' hB

/-- `sdiff_inter_eq_compl` 的对偶（`B \ (A ∩ B) = Aᶜ`）。 -/
theorem sdiff_inter_eq_compl' {A B : Finset X} (h : A ∪ B = Finset.univ) :
    B \ (A ∩ B) = Aᶜ := by
  rw [Finset.inter_comm]
  exact sdiff_inter_eq_compl (Finset.union_comm A B ▸ h)

/-- ★★★ **Prop 6.5(ii)**：`A ∪ B = X` 时「`A, B` 都是 clan」⟺「`A \ (A∩B), B \ (A∩B)` 都是 clan」。 -/
theorem isClade_sdiff_inter_iff {T : Cladogram X} {A B : Finset X}
    (h : A ∪ B = Finset.univ) :
    (T.IsClade (A \ (A ∩ B)) ∧ T.IsClade (B \ (A ∩ B))) ↔ (T.IsClade A ∧ T.IsClade B) := by
  rw [sdiff_inter_eq_compl h, sdiff_inter_eq_compl' h]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(isClade_compl T A).mp h2, (isClade_compl T B).mp h1⟩,
    fun ⟨h1, h2⟩ => ⟨(isClade_compl T B).mpr h2, (isClade_compl T A).mpr h1⟩⟩

/-- ★★ **Prop 6.5(i) 的树层核心**：`A1 ⊂ A2` 时，「`A1, A2` 都是 clan」⟺「`A1, A2ᶜ` 都是 clan」
（第 1291–1292 行）。后者的两个集合**互斥**，故可落到 Theorem 6.3 的互斥情形。 -/
theorem isClade_and_compl_iff {T : Cladogram X} {A B : Finset X} :
    (T.IsClade A ∧ T.IsClade B) ↔ (T.IsClade A ∧ T.IsClade Bᶜ) :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, (isClade_compl T B).mpr h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (isClade_compl T B).mp h2⟩⟩

/-- `A ⊆ B` ⟹ `A` 与 `Bᶜ` 互斥（Prop 6.5(i) 化归到 Theorem 6.3 的合法性）。 -/
theorem disjoint_compl_of_subset {A B : Finset X} (h : A ⊆ B) : Disjoint A Bᶜ := by
  rw [Finset.disjoint_left]
  intro x hA hB
  exact (Finset.mem_compl.mp hB) (h hA)

/-! ## 6. 显式缺口（**未证**，也不被任何已证定理使用）

以下三条 `def … : Prop` 是本文件**没有**做到的部分的可引用形式。
它们的**措辞**就是「还需要什么」；文件内**不**主张它们成立。 -/

/-- **缺口 G1（一般 `n` 的 YHK 拓扑律 + clan 事件概率 = Lemma 6.2）**。

本库**没有**一般 `n` 的 YHK / Kingman **拓扑律**（只有 `Fin 4` 的 `MSCFreq` 实例与
一步合并的均匀性）。故 `clanProb`（乃至 `pn`）目前只是**闭形式**，
它们与概率空间的接通就是本缺口。 -/
def YHKClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A : Finset (Fin n), A.Nonempty → A.card < n →
      (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
        = clanProb n A.card

/-- **缺口 G2（Theorem 6.3 的概率层：两个 clan）**。
互斥的两组 `A`、`B` 同时成 clan 的概率 = `qnExhaustive`（`a + b = n`）或 `qn`（`a + b < n`）。 -/
def TwoClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A B : Finset (Fin n), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card ≤ n →
      (∑ ω ∈ Finset.univ.filter
          (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B), prob ω)
        = if A.card + B.card = n then qnExhaustive A.card B.card else qn n A.card B.card

/-- **缺口 G3（Theorem 6.4(i) 的概率层：三个 clan）**。
互斥且穷尽的三组 `A1,A2,A3` 同时成 clan 的概率 = `qTriple`。 -/
def TripleClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A1 A2 A3 : Finset (Fin n),
      (A1 ∪ A2 ∪ A3 = Finset.univ) →
      (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A1 ∧ (tree ω).IsClade A2
          ∧ (tree ω).IsClade A3), prob ω)
        = qTriple A1.card A2.card A3.card

end Phylo.Stat.ReciprocalMonophyly
