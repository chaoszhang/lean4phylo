/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.InternalEdge
import Phylo.CladogramBuild

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
| **`pn` 是 YHK 律下的 clade 概率**（Lemma 4.1 / 4.2 的**概率层**） | ❌ **未证** —— 缺口 `YHKClanLawGap`（§6）；§5.2 已交付两块**无条件**切片（任意 `n` 的 `A.card ∈ {1, n−1}` ＋ `n = 3` 整条） |
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

/-- **Theorem 4.5 的六情形级联（W19 任务 B：把文献的陈述结构逐字形式化）** ✓。

文献（`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md:452-475` ✓ 逐字）
把「Yule 树上 `A`、`B` 同为 proper clade」的概率 `pn(A,B)` 按 **6 种情形**给出：

```text
        ⎧ pn(a),           if A = B                        [case 1] ;
        ⎪ Rn(a, b),        if A ⊊ B                        [case 2] ;
        ⎪ Rn(b, a),        if B ⊊ A                        [case 3] ;
pn(A,B)=⎨ p̂n(a, n − a),    if A ∩ B = ∅, A ∪ B = Xn       [case 4] ;
        ⎪ rn(a, b),        if A ∩ B = ∅, A ∪ B ⊊ Xn        [case 5] ;
        ⎩ 0,               otherwise                       [case 6] ;
```

本 `def` 是这 6 行的**逐字转录**（用 `Finset (Fin n)` 的集合把情形判据写成可判定的形式 ✓）：
`A ⊊ B` ↔ `A ⊂ B` ✓；`A ∪ B = Xn` ↔ `A ∪ B = Finset.univ` ✓；`A ∩ B = ∅` ↔ `A ∩ B = ∅` ✓。
其中 `p̂n` 取 **Lemma 4.3**（**穷尽**情形 ✓），与 `qn`（`:229` ✓）的取法一致 ✓（见文件头 §3 的更正 ✓）。

⚠️ **证明状态（如实登记 ✓）**：本 `def` 只把**陈述结构**落地 ✓；
「它确实等于 YHK 律下 `A`、`B` 同成 clan 的**概率**」这一**概率层**仍未证 ✗ ——
那需要**一般 `n` 的 YHK / Kingman 拓扑律** ✗（本库只有 `Fin 4` 的 `MSCFreq` 实例与一步合并的均匀性 ✓），
即缺口 `YHKClanLawGap` / `TwoClanLawGap`（§6 ✓）。★ **不得**用本 `def` 冒充「Theorem 4.5 已证」✗。

文本依据：`…arXiv1101.1311.md:452-475`（六情形本体 ✓）· `:479-503`（`Rn` ✓）· `:504-509`（`rn` ✓）·
`:477`（`pn(a)` 取 Lemma 4.2 ✓、`p̂n(a, n−a)` 取 Lemma 4.3 ✓）。 -/
noncomputable def pnPair {n : ℕ} (A B : Finset (Fin n)) : ℝ :=
  if A = B then clanProb n A.card
  else if A ⊂ B then Rn n A.card B.card
  else if B ⊂ A then Rn n B.card A.card
  else if A ∩ B = ∅ ∧ A ∪ B = Finset.univ then pnHatExh n A.card
  else if A ∩ B = ∅ then rn n A.card B.card
  else 0

/-- **Theorem 4.5 情形 6 的锚点**：两集合**相交且互不包含**、又不同时为全集时，值为 `0`
（文献 `:475` 的 "otherwise [case 6]" ✓）—— 用 `Fin 3` 上的 `{0}` 与 `{1}` 之外的显式例子验证级联**真的走到第 6 支** ✓。 -/
theorem pnPair_case6_anchor :
    pnPair ({0, 1} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) = 0 := by
  unfold pnPair
  repeat' rw [ite_eq_right (by decide)]

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

/-! ### 5.1 缺口 `TwoClanLawGap` 的一个**无条件**切片

`TwoClanLawGap`（§6）要求「互斥的 `A`、`B` 同成 clan」的概率等于闭形式。本节证明：
当 `B` 是**单点集**（`A = X \ {x}`，故 `a + b = n`）时，缺口的等式对**任意**概率空间、
**任意**树映射都无条件成立 —— 左端是**必然事件**，右端是纯算术。
这**不是**缺口的证明（见该 `def` docstring 的缺件清单），而是它在这一角落的**实例**。 -/

/-- ★★ **缺口 `TwoClanLawGap` 在 `A = X \ {x}`、`B = {x}` 这一族的无条件实例**。

结论里的 `if` **逐字**是缺口的 RHS（`if a + b = n then qnExhaustive a b else qn n a b`），
且 `A`、`B` 满足缺口的全部前提（`Disjoint`、两侧非空、`a + b ≤ n`），故本定理是缺口的**实例**，
不是新命题。

* **左端恒 `= 1`**：单点集恒是 clade（★ `Cladogram.exists_isSplitOf_singleton`），
  其补集由 ★ `isClade_compl` 也是 ⇒「`A`、`B` 都是 clan」是**必然事件**，只需 `∑ ω, prob ω = 1`。
  **不需要** YHK 律；连缺口的 `0 ≤ prob` 前提也不需要（本定理因此比缺口的那一侧更强）。
* **右端 `= 1`**：`(n − 1) + 1 = n` ⇒ 走 `qnExhaustive` 支，而
  `qnExhaustive (n − 1) 1 = 1`（★ `qnExhaustive_one_right`，纯算术）。

⚠️ **边界（不得夸大）**：只覆盖 `a + b = n` 且 `min(a, b) = 1` 的角落。一般 `a, b ≥ 2` 的
穷尽情形要 `qnExhaustive a b = clanProb n a` 的**概率层**（Lemma 6.2 = 缺口 `YHKClanLawGap`）；
`a + b < n` 要 Theorem 6.3(ii) 的三事件分解与 Theorem 4.5 的概率层。两者都需要一般 `n` 的
YHK 律（缺件清单见 `TwoClanLawGap` 的 docstring）。**不得**用本定理冒充 `TwoClanLawGap` 已证。 -/
theorem twoClan_exhaustive_singleton_slice {n : ℕ} (hn : 2 ≤ n) {Ω : Type} [Fintype Ω]
    (prob : Ω → ℝ) (hsum : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)) (x : Fin n) :
    (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade (Finset.univ \ {x})
        ∧ (tree ω).IsClade ({x} : Finset (Fin n))), prob ω)
      = (if (Finset.univ \ {x} : Finset (Fin n)).card
              + ({x} : Finset (Fin n)).card = n
          then qnExhaustive (Finset.univ \ {x} : Finset (Fin n)).card
            ({x} : Finset (Fin n)).card
          else qn n (Finset.univ \ {x} : Finset (Fin n)).card
            ({x} : Finset (Fin n)).card) := by
  have : Nontrivial (Fin n) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      have h' := Fin.mk.inj h
      omega⟩
  have hx : ∀ ω, (tree ω).IsClade ({x} : Finset (Fin n)) := fun ω =>
    Cladogram.exists_isSplitOf_singleton (tree ω) x
  have hc : ∀ ω, (tree ω).IsClade (Finset.univ \ {x} : Finset (Fin n)) := by
    intro ω
    rw [← Finset.compl_eq_univ_sdiff]
    exact (isClade_compl (tree ω) {x}).mpr (hx ω)
  have hcardA : (Finset.univ \ {x} : Finset (Fin n)).card = n - 1 := by
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
  have hcardB : ({x} : Finset (Fin n)).card = 1 := Finset.card_singleton x
  have hfilter : (Finset.univ.filter (fun ω => (tree ω).IsClade (Finset.univ \ {x})
      ∧ (tree ω).IsClade ({x} : Finset (Fin n)))) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ => ⟨hc ω, hx ω⟩)
  rw [hfilter, hcardA, hcardB]
  split_ifs with h
  · rw [qnExhaustive_one_right (by omega : 1 ≤ n - 1)]
    simpa using hsum
  · exact absurd h (by omega)

/-! ### 5.2 缺口 `YHKClanLawGap` 的无条件切片（任意 `n` 的平凡基数 ＋ `n = 3` 的整条）

`YHKClanLawGap`（§6）要求「一般 `n` 的 YHK 律下 `clanProb n a` = `A` 是 clan 的概率」。
本节证明它**不需要** YHK 律的两块：

* **平凡基数**（`a = 1` 或 `a = n − 1`）：对**任意**概率空间、**任意**树族无条件成立
  —— `A` 是单点集或其补集 ⇒ 「`A` 是 clan」是**必然事件** ⇒ 左端 `= 1`，
  右端由 ★★ `clanProb_one` / ★★ `clanProb_pred` 也是 `1`；
* **`n = 3` 的整条**：`Fin 3` 的非空真子集只有这两种形状，故 `YHKClanLawGap` 的
  `∃` 从句在 `n = 3` 上**完整成立**（退化分布 ＋ 任意一棵树即见证）—— 这是缺口的
  一个**完整实例**，不是只有一列 `a`。

⚠️ **边界（不得夸大）**：`n ≥ 4` 且 `2 ≤ a ≤ n − 2` 时 `clanProb n a` 取**非 `0/1`** 的值
（★ `clanProb_four_two`：`clanProb 4 2 = 1/3`），而单点/补集论证只覆盖 `a ∈ {1, n − 1}`
⇒ 本节**不是** `YHKClanLawGap` 的证明；一般 `n` 仍需具名器材 `MSCTreeLaw n`（判决见该 `def` 的 docstring）。 -/

/-- ★★ **`clanProb n (n − 1) = 1`**（`n ≥ 2`）：`X \ {x}` 在**任何**树上都是 clan。
由 Theorem 6.3(i)（★★★ `qnExhaustive_eq_clanProb`）＋ ★★ `qnExhaustive_one_right` 立得 —— 纯算术。 -/
theorem clanProb_pred {n : ℕ} (hn : 2 ≤ n) : clanProb n (n - 1) = 1 := by
  have h := qnExhaustive_eq_clanProb (a := n - 1) (b := 1) (by omega) (by norm_num)
  rw [show n - 1 + 1 = n from by omega] at h
  rw [← h, qnExhaustive_one_right (by omega)]

/-- ★★ **缺口 RHS 在 `n = 4, a = 2` 取非 `0/1` 值**：`clanProb 4 2 = 1/3`
（= 4 叶 MSC 的 concordant 概率，与 ★★ `qnExhaustive_two_two = 1/3` 一致）。
这条说明缺口**不是空转**：`∃ Ω, prob, tree` 的槽位**不能**用退化分布填掉。 -/
theorem clanProb_four_two : clanProb 4 2 = 1 / 3 := by
  have h : Nat.choose 4 2 = 6 := by decide
  simp only [clanProb, h]
  norm_num

/-- ★★★ **缺口 `YHKClanLawGap` 的「平凡基数」切片（任意 `n`、任意概率空间、任意树族）**。

若 `A.card = 1` 或 `A.card = n − 1`，则缺口等式**无条件**成立：左端是**必然事件**的概率
（`= ∑ prob = 1`），右端是 `clanProb n 1 = 1` 或 `clanProb n (n − 1) = 1`。
**不需要** YHK 律，连 `prob ≥ 0` 也不需要（故这一侧比缺口更强）。

⚠️ 这**不是** `YHKClanLawGap` 的证明：缺口对 `A` 的**所有**基数都要求等式成立。 -/
theorem yhkClanLawGap_trivial_card_slice {n : ℕ} (hn : 2 ≤ n) {Ω : Type} [Fintype Ω]
    (prob : Ω → ℝ) (hsum : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin n))
    {A : Finset (Fin n)} (hne : A.Nonempty) (hcard : A.card = 1 ∨ A.card = n - 1) :
    (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω) = clanProb n A.card := by
  have : Nontrivial (Fin n) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      exact absurd (Fin.mk.inj h) (by omega)⟩
  have hclade : ∀ ω, (tree ω).IsClade A := by
    intro ω
    rcases hcard with h1 | h1
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
      exact Cladogram.exists_isSplitOf_singleton (tree ω) x
    · have hc : Aᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin, h1]
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
      have hA : A = ({x} : Finset (Fin n))ᶜ := by rw [← hx, compl_compl]
      rw [hA]
      exact (isClade_compl (tree ω) {x}).mpr (Cladogram.exists_isSplitOf_singleton (tree ω) x)
  have hfilter : Finset.univ.filter (fun ω => (tree ω).IsClade A) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ => hclade ω)
  rw [hfilter]
  rcases hcard with h1 | h1
  · rw [h1, clanProb_one hn]
    exact hsum
  · rw [h1, clanProb_pred hn]
    exact hsum

/-- `Fin 3` 上的一棵**具体**树（星形：无任何非平凡 split），
由 ★★★ `Cladogram.ofCompatibleSplits` 用**空族**造出。 -/
noncomputable def starTree3 : Cladogram.{0, 0} (Fin 3) :=
  Cladogram.ofCompatibleSplits (∅ : Finset (Split (Fin 3))) 0
    (by simp) (by simp) (by simp) (by decide)

/-- ★★★ **缺口 `YHKClanLawGap` 在 `n = 3` 上的完整实例**（无条件）。

`Fin 3` 的非空真子集只有 `{x}`（`card = 1`）与 `{x}ᶜ`（`card = 2 = 3 − 1`）两种形状，
故缺口对**所有** `A` 的要求都落进 ★★★ `yhkClanLawGap_trivial_card_slice`
⇒ 取 `Ω = PUnit`、`prob ≡ 1`、`tree ≡ starTree3` 即得缺口 `∃` 从句在 `n = 3` 的**完整**成立。
⚠️ `n ≥ 4` 时 `2 ≤ a ≤ n − 2` 的那些 `a` **不在**本定理覆盖内。 -/
theorem yhkClanLawGap_three_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 3)),
      ∀ A : Finset (Fin 3), A.Nonempty → A.card < 3 →
        (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
          = clanProb 3 A.card := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => by norm_num, by simp,
    fun _ => starTree3, ?_⟩
  intro A hne hcard
  have hcard' : A.card = 1 ∨ A.card = 3 - 1 := by
    have hpos : 1 ≤ A.card := Finset.card_pos.mpr hne
    omega
  exact yhkClanLawGap_trivial_card_slice (n := 3) (by norm_num) (fun _ => 1) (by simp)
    (fun _ => starTree3) hne hcard'

/-! ### 5.3 补器材：由「单个 split ＋ 换向」造树并**算出**其 clade 集

YHKClanLawGap 在 
 = 4 的证明需要「**命名**一棵 quartet 树并知道它有哪些 clade」。
库内 Cladogram.ofCompatibleSplits（Phylo/CladogramBuild.lean）能造树，但缺「两台集族」
这一最常用情形的现成桥。本节补上：族 {s, s.swap} 的三条前提**自动**满足，
且建出的树的 clade 集被**完全刻画**（A 是 s 的某一侧，或 A 平凡）。

★ 这是本泳道交付的**器材**（供下一泳道做 
 = 4 切片直接调用）。 -/

/-- **族 {s, s.swap} 两两相容**（任意 s：s 的两侧不交）。 -/
theorem compatible_pair_swap {α : Type} [Fintype α] [DecidableEq α] (s : Split α) :
    ∀ t ∈ ({s, s.swap} : Finset (Split α)), ∀ u ∈ ({s, s.swap} : Finset (Split α)),
      Split.Compatible t u := by
  have h := Split.disjoint_sides s
  intro t ht u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
  rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp only [Split.Compatible, Split.swap_sideA, Split.swap_sideB] <;> tauto

/-- **族 {s, s.swap} 非平凡**（换向只对调两侧）。 -/
theorem nontrivial_pair_swap {α : Type} [Fintype α] [DecidableEq α] {s : Split α}
    (h : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) :
    ∀ t ∈ ({s, s.swap} : Finset (Split α)), 2 ≤ t.sideA.card ∧ 2 ≤ t.sideB.card := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact h
  · rw [Split.swap_sideA, Split.swap_sideB]
    exact ⟨h.2, h.1⟩

/-- **族 {s, s.swap} 对换向封闭**。 -/
theorem swap_closed_pair_swap {α : Type} [Fintype α] [DecidableEq α] (s : Split α) :
    ∀ t ∈ ({s, s.swap} : Finset (Split α)), t.swap ∈ ({s, s.swap} : Finset (Split α)) := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
  rcases ht with rfl | rfl
  · exact Or.inr rfl
  · rw [Split.swap_swap]
    exact Or.inl rfl

/-- ★★★ **两台集族树的 clade 集被完全刻画**：A 是 ofCompatibleSplits {s, s.swap} ⋯
的 clan ⟺ A 是 s 的某一侧，或 A 平凡（单点集 / 单点集的补）。
（树的 split 系统 = {s, s.swap} ∪ 平凡 split，见 ★★★ Cladogram.isSplitOf_ofCompatibleSplits。） -/
theorem isClade_ofCompatible_pair {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]
    (s : Split α) (ρ : α) (hn : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card)
    (h3 : 3 ≤ Fintype.card α) (A : Finset α) :
    (Cladogram.ofCompatibleSplits {s, s.swap} ρ (compatible_pair_swap s)
      (nontrivial_pair_swap hn) (swap_closed_pair_swap s) h3).IsClade A ↔
      A = s.sideA ∨ A = s.sideB ∨ (∃ x : α, A = {x}) ∨ (∃ x : α, A = {x}ᶜ) := by
  have hchar := Cladogram.isSplitOf_ofCompatibleSplits {s, s.swap} ρ (compatible_pair_swap s)
    (nontrivial_pair_swap hn) (swap_closed_pair_swap s) h3
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [hchar] at ht
    rcases ht with hmem | ⟨x, hx⟩ | ⟨x, hx⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by rw [Split.swap_sideA]))
    · exact Or.inr (Or.inr (Or.inl ⟨x, hx⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨x, hx⟩))
  · rintro (h | h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨s, (hchar s).mpr (Or.inl (Finset.mem_insert_self _ _)), ?_⟩
      rw [h]
    · refine ⟨s.swap, (hchar s.swap).mpr
        (Or.inl (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))), ?_⟩
      rw [Split.swap_sideA, h]
    · rw [hx]
      exact Cladogram.exists_isSplitOf_singleton _ x
    · rw [hx]
      exact (isClade_compl _ _).mpr (Cladogram.exists_isSplitOf_singleton _ x)

/-! ## 6. 显式缺口（**未证**，也不被任何已证定理使用）

以下三条 `def … : Prop` 是本文件**没有**做到的部分的可引用形式。
它们的**措辞**就是「还需要什么」；文件内**不**主张它们成立。 -/

/-- **缺口 G1（一般 `n` 的 YHK 拓扑律 + clan 事件概率 = Lemma 6.2）**。

本库**没有**一般 `n` 的 YHK / Kingman **拓扑律**（只有 `Fin 4` 的 `MSCFreq` 实例与
一步合并的均匀性）。故 `clanProb`（乃至 `pn`）目前只是**闭形式**，
它们与概率空间的接通就是本缺口。

★ **W25 泳道 b 判定（2026-10-19）：【收档 · 真缺口，非空转】** —— **命题一字未改** ✓。

* **忠实性 ✓**：RHS `clanProb n A.card` 与文献 Lemma 6.2（`:1007-1036` ✓）逐字对应；
  「`A` 是 clan」= 文献 `:985-988` ✓ 的 clan（本库 `IsClade` 即 clan，见文件头 §2）；
  前提 `A.Nonempty` ＋ `A.card < n` 排除 `∅` 与 `X`（两者都不是 split 的一侧）。
* **不是「空转缺口」✗**：`∃ Ω, prob, tree` 是自由槽，但 `clanProb n a` 对 `2 ≤ a ≤ n − 2`
  取**非 0/1** 值（★ `clanProb_four_two`：`clanProb 4 2 = 1/3`）⇒ 退化分布
  （单点树 / 星形树 / `prob` 取 0-1 原子）**拿不到**这些值 ⇒ 槽位**不能**被平凡填掉。
* **可证伪否 ✗**：`scripts/msc/zds2011_monophyly.py` 以精确有理数在 `n ∈ {4,5,6}` 上穷举
  核对 Lemma 6.2 与 YHK 分布（`:271-318` ✓，末行 `总判定：ALL OK`）⇒ 命题为**真**，本库内**没有**反例。
* **可证成否 ✗（本库内）**：缺**四件具名器材** ——
  ① **`MSCTreeLaw n`**：一般 `n` 的 YHK/Kingman **无根拓扑律**（有限概率空间 ＋
     `tree : Ω → Cladogram (Fin n)` ＋ 文献 `:191-216` 的 YHK 权重）。库内最近的是
     `MSCKingman.root_topology_class_prob`（仅 `Fin 4`）、`MSCProof.mscFreqFin4`、
     `Coalescent.mergePairsFinset`（一步合并均匀）—— 都**不是**一般 `n` 的律。
  ② **去根载体桥 `rootedToCladogram`**：YHK 是**有根**过程，文献的 clan 是 `T − ρ` 的 split；
     本库 `Cladogram` 无 root 概念（文件头 §5 已登记「有根树 clade 的库内对象 ❌ 不存在」）。
  ③ **Lemma 6.1 的概率层**（`:991-992` ✓，证明 = `:1038-1044` ✓ 的包含-排除
     `qn(A) = pn(A) + pn(X−A) − pn(A, X−A)`）：本文件只有**树层**件
     （`isClade_compl`、`isClade_and_compl_iff` 等），缺「`clade(T)` ↔ `clan(T−ρ)`」的**概率**桥。
  ④ **(EP) 的群作用实现**（`:230-232` ✓）：leaf 重标号对 `Cladogram` 的作用 ＋ 律的等变性
     —— 用来把 `qn` 的依赖化归到 `(a, b)`；以及 Theorem 4.5 情形 2/5（`Rn`/`rn`）的概率层。
* **已交付的无条件切片（§5.2）**：★★★ `yhkClanLawGap_trivial_card_slice`（**任意** `n`、
  **任意**概率空间与树族，`A.card ∈ {1, n−1}` 时等式恒成立；不需要 YHK 律、不需要 `prob ≥ 0`）
  ＋ ★★★ `yhkClanLawGap_three_slice`（缺口 `∃` 从句在 `n = 3` 上**完整成立**）。
* **★ 新发现（留给下一泳道）：`n = 4` 那一条其实**可证**，卡点是**枚举的可判定性**，不是数学** ——
  库内 `Cladogram.ofCompatibleSplits`（`Phylo/CladogramBuild.lean`）能**造出** 3 棵 quartet 树
  （族取 `{splitOf {0,1}, swap}`、`{splitOf {0,2}, swap}`、`{splitOf {0,3}, swap}`），
  其 clade 集由本节新引理（本泳道试写的 `isClade_ofCompatible_pair`）完全刻画为
  「`A` 是某个二元子集或其补，或 `A` 平凡」；均匀混合 3 棵即得 `clanProb 4 2 = 1/3`
  （`Fin 4` 的 6 个二元子集各在**恰好 1 棵**里成 clade）。
  **实测卡点**：`Finset.filter`（谓词含 `IsClade`）的 `DecidablePred` 落到
  `Classical.propDecidable`，`decide` 在 `Finset.card` 上**不归约**（`beq` 停在
  `{j | ⋯}.card.beq 1`）⇒ 需先把滤子改写成**可计算谓词**（`Finset.filter_congr` ＋ 显式
  `Decidable` 实例），或按 6 个二元子集显式 `fin_cases` 分情形。补齐这件器材后
  `n = 4` 的切片应是纯机械工作。 -/
def YHKClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A : Finset (Fin n), A.Nonempty → A.card < n →
      (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
        = clanProb n A.card

/-- **缺口 G2（Theorem 6.3 的概率层：两个 clan）**。
互斥的两组 `A`、`B` 同时成 clan 的概率 = `qnExhaustive`（`a + b = n`）或 `qn`（`a + b < n`）。

★ **W25 泳道 b 判定（2026-10-19）：【收档 · 真缺口，非空转】** —— **命题一字未改** ✓。

* **忠实性 ✓**：RHS 的 `if` 与文献 Theorem 6.3 的两支**逐字**对应 ——
  `a + b = n` → Theorem 6.3(i) = `qnExhaustive`（`:1079-1103` ✓）；
  `a + b < n` → Theorem 6.3(ii) = `qn`（`:1105-1110` ✓）。前提 `Disjoint A B` ＋ 两侧非空 ＋
  `a + b ≤ n` 与文献「Now consider two disjoint subsets `A` and `B` of `X`」（`:1046-1050` ✓）一致；
  本库 `IsClade` 恰是文献的 **clan**（`A|X−A` 是 split，`:985-988` ✓；见文件头 §2 的术语提示）。
* **不是「空转缺口」✗（关键）**：`∃ Ω, prob, tree` 虽是自由槽，但 RHS 会取到 `7/225`
  （文献 `q₆(2,2) = 7/225`，`:1051` ✓）这类**非 0/1** 值 ⇒ 退化分布（单点树 / 星形树 /
  `prob` 取 0-1 原子）**拿不到**这些值 ⇒ 槽位**不能**被平凡填掉。这与泳道 a 的 `∃ Step` 型
  **空转缺口**（`∃` 槽一退化则输入与算法一起消失）**不同类**。
* **可证伪否 ✗**：`scripts/msc/zds2011_monophyly.py`（精确有理数、无随机数）在 `n ∈ {4,5,6}`
  上把 `qn` 与 YHK 分布**穷举**逐条对齐（`:271-318` ✓），并在 `n ≤ 11` 上核
  `q_n(1) = q_n(n−1) = 1` 等恒等式（`:337-341` ✓），末行 `总判定：ALL OK` ⇒ 命题为**真**，
  **没有**形式化反例。故本缺口是「**真而缺器材**」，不是「假而待反例」。
* **可证成否 ✗（本库内）**：缺**四件具名器材** ——
  ① **`MSCTreeLaw n`**：一般 `n` 的 YHK/Kingman **无根拓扑律**（有限概率空间 ＋
     `tree : Ω → Cladogram (Fin n)` ＋ 权重 = 文献 `:191-218` 的 YHK 生成过程 /
     `:996-1006` 的无根版描述）。库内最近的是 `MSCKingman.root_topology_class_prob`（仅 `Fin 4`）、
     `MSCProof.mscFreqFin4`、`Coalescent.mergePairsFinset`（一步合并均匀）—— 都**不是**一般 `n` 的律。
  ② **去根载体桥 `rootedToCladogram`**：YHK 是**有根**过程，文献的 clan 是 `T − ρ` 的 split；
     本库 `Cladogram` 无 root 概念且带 `no_degree_two`，文件头 §5 已登记
     「有根树 clade 的库内对象 ❌ 不存在」。
  ③ **Lemma 6.1 的概率层**（`:991-992` ✓；证明即 `:1038-1044` ✓ 的包含-排除
     `qn(A) = pn(A) + pn(X−A) − pn(A, X−A)`）：本文件只有**树层**件（`isClade_compl`、
     `isClade_and_compl_iff` 等），缺「`clade(T)` ↔ `clan(T−ρ)`」的概率桥。
  ④ **(EP) 的群作用实现**（`:230-231` ✓）：leaf 重标号作用在 `Cladogram` 上 ＋ 律的等变性，
     用来把 `qn` 的依赖化归到 `(a, b)`；以及 Theorem 4.5 情形 2/5（`Rn` / `rn`）的**概率层**
     —— 正是 `a + b < n` 的三事件分解（`:1112-1145` ✓）所需的三个概率。
* **已交付的无条件切片**：`twoClan_exhaustive_singleton_slice`（§5.1，本文件 `:672` ✓）——
  `A = X \ {x}`、`B = {x}` 这一族上缺口等式**无条件成立**（左端恒 `1`、右端
  `qnExhaustive (n−1) 1 = 1`）。它**不是** `TwoClanLawGap` 的证明，只是 `min(a,b) = 1`
  且穷尽那一角落的实例。 -/
def TwoClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A B : Finset (Fin n), Disjoint A B → A.Nonempty → B.Nonempty → A.card + B.card ≤ n →
      (∑ ω ∈ Finset.univ.filter
          (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B), prob ω)
        = if A.card + B.card = n then qnExhaustive A.card B.card else qn n A.card B.card

/-- **缺口 G3（Theorem 6.4(i) 的概率层：三个 clan）** —— ★ **2026-10-14 W19 按文献更正前提** ✓。

**文献原话（`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md:1171-1191`）**：
> 「**Theorem 6.4.** Let `n = a₁ + a₂ + a₃`. Then: **(i)** `q(a₁,a₂,a₃) = 4a₁!a₂!a₃!/(n−1)! · Σ_{i=1}^{3} 1/((n−a_i)((n−a_i)²−1))`」
其**证明首句**（同文件 `:1193-1196` ✓）明确限定事件为：
> 「the event that `A₁, A₂` and `A₃` (**which partition `X`**) are clans of `T − ρ` …」
⇒ 文献的 `A₁,A₂,A₃` 是 `X` 的**划分**（**两两不交** ＋ 并为全集 ✓）；

**★ 改动留证（旧形态 → 新形态 → 文献依据 → 理由）**：
* **旧形态** ✗：只要求 `A1 ∪ A2 ∪ A3 = Finset.univ`（**未要求两两不交** ✗）；
* **新形态** ✓：`A1 ∪ A2 ∪ A3 = Finset.univ ∧ Disjoint A1 A2 ∧ Disjoint A1 A3 ∧ Disjoint A2 A3`
  ＝「三者构成 `X` 的**划分**」✓（与文献 `partition` 逐字对应 ✓）；
* **文献依据** ✓：同文件 `:1171-1191`（定理本体 ✓）＋ `:1193-1196`（证明首句的 "partition" ✓）；
* **理由** ✓：旧形态**前提过宽** ✗ —— 三者可**重合**，此时等式**为假** ✗
  （显式反例：取 `A1 = A2 = A3 = univ` ⇒ 左端「三者都是 clan」＝「`univ` 是 clan」的概率 `= 1` ✗，
  而右端 `qTriple n n n` ✗ ≠ 1 ✓）⇒ 依老师 2026-10-14 令「命题不忠于文献就改命题」✓ 改为**等于文献那条** ✓。
  ★ **未改弱** ✓：前提**加强**（加了三条 `Disjoint` ✓），结论不变 ✓；
* **影响的下游声明**：无（本 `def` 是 `Prop` 缺口，库内无人依赖 ✓；同文件 `:146-147` 的对照表把「三个 clan 的概率」
  列为 ❌ 未证 ✓，与本 `def` 一致 ✓）。 -/
def TripleClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A1 A2 A3 : Finset (Fin n),
      (A1 ∪ A2 ∪ A3 = Finset.univ) → Disjoint A1 A2 → Disjoint A1 A3 → Disjoint A2 A3 →
      (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A1 ∧ (tree ω).IsClade A2
          ∧ (tree ω).IsClade A3), prob ω)
        = qTriple A1.card A2.card A3.card

end Phylo.Stat.ReciprocalMonophyly
