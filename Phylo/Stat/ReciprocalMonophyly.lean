/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MSCProof
import Phylo.InternalEdge
import Phylo.CladogramBuild
import Mathlib.Combinatorics.SimpleGraph.Star
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
* **§6**：**显式缺口**（概率层，3 个 `def … : Prop`，未被证、也未被引用）；
* **§8**：一般 `n` 的**律容器** `MSCTreeLaw n`（有限概率空间 ＋ 树映射 ＋ 概率公理）
  ＋ **`n = 4` 的 YHK 律实例**（三棵 quartet 树等权 `1/3`，★★★ `yhkLawFour`）
  ＋ 缺口 `YHKClanLawGap` 在 **`n = 4` 的整条**（★★★ `yhkClanLawGap_four_slice`）。

## 5. 诚实边界（**没做到的**，逐条）

| 条目 | 状态 |
|---|---|
| 闭形式的**数值正确性** | ✅ 脚本 `n ≤ 6` 全穷举复核（§3） |
| 闭形式之间的**算术恒等式** | ✅ 已证 4 条：`clanProb_eq_inclusionExclusion`（Lemma 6.2 ⟸ Lemma 6.1 的包含-排除）、`pnHat_eq_pn_mul`（Lemma 4.4 ⟸ 4.2 ⊗ 4.3，论文第 398–444 行的证明）、`qnExhaustive_eq_clanProb`（Theorem 6.3(i) ⟸ Lemma 6.2）、`clanProb_eq_unfolded`；另有 `choose_mul_pn`（Lemma 4.1 **右端**的算术核对）、`qnExhaustive_two_two`、`qn_six_two_two`、`qTriple_two_two_two`、`qConvex_two_two_two` 等锚点 |
| **`pn` 是 YHK 律下的 clade 概率**（Lemma 4.1 / 4.2 的**概率层**） | ❌ **未证** —— 缺口 `YHKClanLawGap`（§6）；§5.2 已交付两块**无条件**切片（任意 `n` 的 `A.card ∈ {1, n−1}` ＋ `n = 3` 整条 ＋ §8 的 **`n = 4` 整条**） |
| **`qn` 是「两个 clan」的概率**（Theorem 6.3 的概率层） | ❌ **一般 `n` 未证** —— 缺口 `TwoClanLawGap`（§6）；§8.7 已把 **`n = 3`（对任意律）** 与 **`n = 4` 整条** 落地（★★★ `twoClanLawGap_three_slice`、★★★ `twoClanLawGap_four_slice`） |
| **`q` 是「三个 clan」的概率**（Theorem 6.4 的概率层） | ❌ **未证** —— 缺口 `TripleClanLawGap`（§6） |
| **Theorem 5.1**（一般 `k` 个 clade，含指定 `Tk`） | ❌ **未落地**（连闭形式都依赖 `Iv(Ai)` 这套 `Tk` 上的指示变量；本库无「内部顶点 + 后代叶集」的层面对象） |
| **Theorem 4.5 一般形** | ⚠️ **部分**：情形 2 / 5 的 `Rn` / `rn` / `Gn` 已转录并复核；**情形 1 / 3 / 4 / 6 的分情形组合**未写成单一 `def` |
| 论文 Lemma 4.4 印刷范围 `k ≤ n` | ⚠️ **修正为 `k < n`**（脚本证据见 §3；`k = n` 用 Lemma 4.3） |
| **有根树 clade** 的库内对象 | ❌ **不存在**：库内 `Cladogram` 是无根载体、`IsClade` 是 clan 语义，故 Theorem 4.5（有根 clade）**没有**库内对应物 |
| Prop 6.5 的**树层**内容 | ⚠️ **部分**：`isClade_compl`（补集对称）、`union_eq_univ_of_isClade`（第 1294–1295 行的**必要性**）、`isClade_sdiff_inter_iff`（第 1296–1297 行）、`isClade_and_compl_iff`（第 1291–1292 行）、`disjoint_compl_of_subset` 已证；**未**把 Prop 6.5 的两条情形组合成单一 `theorem` |
| Prop 6.5 的**概率层** | ❌ **未证**（树层部分见上一行） |
| `x = 4` 之外的**概率层**桥 | ⚠️ **部分**：`qnExhaustive 2 2 = mscConcordant 0` 这一条**数值**桥（§4）；`n = 4` 的**整条概率层**已由 §8 落地（★★★ `yhkClanLawGap_four_slice`；两 clan 的对应物见 §8.7 的 ★★★ `twoClanLawGap_four_slice`） |
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
* **★ W26 泳道 a 判定（2026-10-21）：`n = 4` 的**整条**已落地**（§8）—— 本 `def` **一字未改** ✓。
  交付 ★★★ `yhkClanLawGap_four_slice`：缺口 `∃` 从句在 `n = 4` 上**完整成立**
  （`Ω = Fin 3`、`prob ≡ 1/3`、3 棵 quartet 树等权；`A.card = 2` 时概率 `= 1/3 = clanProb 4 2`）。
  W25 认定的卡点（`Finset.filter` 的 `DecidablePred` 落到 `Classical.propDecidable`、
  `decide` 在 `Finset.card` 上不归约）**被绕过而非被解决**：不求值滤子，改用
  **`Finset.ext` ＋ `∃!`**（★★★ `existsUnique_qPair`：`Fin 4` 的每个二元子集**恰在 1 棵**
  quartet 树里成 clan，★★★ `isClade_qTree_iff`）把滤子结构性化成单点集，故**不需要**
  「可计算谓词」这件器材。容器 `MSCTreeLaw n`（§8，一般 `n`）＋ `n = 4` 的律实例
  ★★★ `yhkLawFour` 同时交付；一般 `n` 仍缺 §8.4 的两件具名器材。 -/
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
  且穷尽那一角落的实例。
* **★ W26 泳道 a 判定（2026-10-21）：`n = 3`（任意律）与 `n = 4` 的整条已落地（§8.7）
  —— 本 `def` 一字未改** ✓。交付 ★★★ `twoClanLawGap_three_slice`（`n = 3`，对**任意**律成立，
  无需 `0 ≤ prob`）与 ★★★ `twoClanLawGap_four_slice`（`n = 4`，`yhkLawFour` 的三棵 quartet 等权）；
  RHS 的**两块**（`qnExhaustive` / `qn`）分别被击中：6 种基数组合
  `(1,1)(1,2)(1,3)(2,1)(2,2)(3,1)` 逐一化归，算术侧新增锚点 ★★ `qn_four_one_one`、★★
  `qn_four_one_two`、★★ `qn_four_two_one`（外加既有 `qnExhaustive_one_left/right`、`qnExhaustive_two_two`）。
  容器侧 ★★★ `yhkLawFour_twoClanEvent`。
  ★ **未被绕开的部分**：`a + b < n` 在**一般 `n`** 上仍要 Theorem 6.3(ii) 的三事件分解
  （`rn` ＋ 两个 `Rn` ＋ 两个 `p̂n·p`）的**概率层**，即仍需 §8.4 的两件具名器材。 -/
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
  列为 ❌ 未证 ✓，与本 `def` 一致 ✓）。
*
* ★ **W25 泳道 b 判定（2026-10-19）：【证伪 · 命题为假 —— 缺「非空」前提】** —— 本 `def` **一字未改** ✓，
  但**不成立** ✗：★★★ `tripleClanLawGap_false : ¬ TripleClanLawGap`（§7）。
  **反例**：`n = 3`、`A₁ = ∅`、`A₂ = {0}`、`A₃ = {1,2}`（合法划分：并为 `univ`、两两不交）⇒
  左端**恒** `0`（`∅` **永远不是** clan：★★ `not_isClade_empty` —— clan 的见证是某条 split 的 `sideA`，
  而 `Split = KPartition α 2` 的每块**非空**），右端 `qTriple 0 1 2 = 5/6 ≠ 0`（★★ `qTriple_zero_one_two`）。
  左端与 `prob`、`tree` **无关** ⇒ `∃ Ω, prob, tree` 的三个槽位**无**任何见证可救 ✗。
  **根因**：文献 `aᵢ ≥ 1` ＋ "partition"（`…arXiv1101.1311.md:1171-1196` ✓）被丢掉了 ——
  本 `def` 只写 `∪ = univ` ＋ 两两 `Disjoint`，**漏了** `Aᵢ.Nonempty`（姊妹缺口
  `YHKClanLawGap` / `TwoClanLawGap` 都有 ✓）。
  **修法（四要素）**：**旧形态** = 现形态；**新形态** = 再加 `A1.Nonempty`、`A2.Nonempty`、`A3.Nonempty`；
  **文献** = 同上 `:1154` ＋ `:1171-1196`；**理由** = 不加则**命题为假**（★ 反例），加后与另两条缺口同形。
  ★ **只加强前提、不动结论** ✓。修后 `n = 3` 的整条**无障碍**（★★★ `tripleClanLawGap_nonempty_three_slice`）。
  ★ **结论边界（不得夸大）**：被否证的是**本 `def` 的措辞**，**不是**文献 Theorem 6.4 ✓。 -/
def TripleClanLawGap : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
    (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin n)),
    ∀ A1 A2 A3 : Finset (Fin n),
      (A1 ∪ A2 ∪ A3 = Finset.univ) → Disjoint A1 A2 → Disjoint A1 A3 → Disjoint A2 A3 →
      (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A1 ∧ (tree ω).IsClade A2
          ∧ (tree ω).IsClade A3), prob ω)
        = qTriple A1.card A2.card A3.card

/-! ### 7. 缺口 G3（`TripleClanLawGap`）的判定：**命题为假** —— 缺「非空」前提

`TripleClanLawGap`（§6）的前提写的是「`A₁, A₂, A₃` 构成 `X` 的**划分**」：
`A1 ∪ A2 ∪ A3 = univ` ＋ 两两 `Disjoint`，但**没有**要求三者非空。
这与文献**不符**：Theorem 6.4 的 `n = a₁ + a₂ + a₃` 中每个 `aᵢ ≥ 1`，
证明首句的事件是「`A₁, A₂` and `A₃` (which **partition** `X`) are clans of `T − ρ`」
（`…arXiv1101.1311.md:1154`「Suppose `A1, A2, . . . , Ak` **partition** `X`」＋ `:1171` 的 `n = a1+a2+a3`＋ `:1193` 的 "which partition X"，即三块**非空**）；
也与同文件另两条缺口**不一致** —— `YHKClanLawGap` 有 `A.Nonempty`、
`TwoClanLawGap` 有 `A.Nonempty` 与 `B.Nonempty`。

后果不是「前提略松」，而是**命题为假**。取 `n = 3` 与合法划分
`A₁ = ∅`、`A₂ = {0}`、`A₃ = {1,2}`：

* **左端恒 `0`**：`∅` **永远不是** clan —— clan 的见证是某条 split 的 `sideA`，
  而 `KPartition` 的每块**非空**（★★ `not_isClade_empty`）。故 `ω` 上取交的集合**空**，
  概率和 `= 0`，与 `prob`、`tree` **无关**；
* **右端 `= qTriple 0 1 2 = 5/6 ≠ 0`**（★★ `qTriple_zero_one_two`）。

`Ω`、`prob`、`tree` 都是缺口的 `∃` 自由槽，但左端恒 `0` ⇒ **无任何见证可救**
⇒ ★★★ `tripleClanLawGap_false : ¬ TripleClanLawGap`（本节给出）。

★ **修法（四要素留证）**：**旧形态** = 只要求划分（现 §6 的 `def`）；
**新形态** = 再加 `A1.Nonempty`、`A2.Nonempty`、`A3.Nonempty` 三条前提；
**文献** = `…arXiv1101.1311.md:1154`（"partition `X`"）+ `:1171`（`n = a₁+a₂+a₃`）+ `:1193`（"which partition `X`"）；
**理由** = 不加则**命题为假**（本节的反例），加后与另两条缺口同形。
★ **未改弱结论**（只**加强前提**，RHS 一字未改），且 `def` 本体**未动** —— 修法留给老师裁决。
修好之后 `n = 3` 的整条**无障碍**（★★★ `tripleClanLawGap_nonempty_three_slice`）。 -/

/-- ★★ **`∅` 永远不是 clan**：`IsClade A` 的见证是某条 split 的 `sideA`，
而 `KPartition`（`Split = KPartition α 2`）的每块**非空**。
（`TripleClanLawGap` 的反例全靠它：左端因此**恒** `0`。） -/
theorem not_isClade_empty {X : Type} [Fintype X] [DecidableEq X] (T : Cladogram X) :
    ¬ T.IsClade (∅ : Finset X) := by
  rintro ⟨s, -, hs⟩
  have h := s.nonempty (0 : Fin 2)
  have hside : (s.parts 0 : Finset X) = (∅ : Finset X) := hs
  rw [hside] at h
  simp at h

/-- ★★ **缺口 RHS 在 `(0, 1, 2)` 上的值**：`qTriple 0 1 2 = 5 / 6 ≠ 0`。

`qTriple` 的定义对 `aᵢ = 0` 仍**算得出**一个正数（`1/((a₁+a₂)((a₁+a₂)²−1))` 那项
在 `a₁ + a₂ = 1` 处是 `1/0 = 0`，另两项不为零）⇒ 与左端的 `0` **必然**不等。 -/
theorem qTriple_zero_one_two : qTriple 0 1 2 = 5 / 6 := by
  unfold qTriple
  norm_num

/-- ★★★ **缺口 `TripleClanLawGap` 为假**（形式化反例，`n = 3`）。

划分取 `A₁ = ∅`、`A₂ = {0}`、`A₃ = {1,2}`（合法：并为 `univ`、两两不交）。
`∅` 不是 clan ⇒ 左端 `= 0`；右端 `= qTriple 0 1 2 = 5/6`。矛盾。
★ 结论是**闭命题的否定**（不是「某实例」）：`∃ Ω, prob, tree` 的槽位**无法**填
—— 左端恒 `0`、与见证无关。

⚠️ **这否证的是 §6 里那条 `def`（缺「非空」前提），不是文献 Theorem 6.4**：
加上 `Aᵢ.Nonempty` 后 `n = 3` 是**真**的（★★★ `tripleClanLawGap_nonempty_three_slice`）。 -/
theorem tripleClanLawGap_false : ¬ TripleClanLawGap := by
  rintro h
  obtain ⟨Ω, hΩ, prob, hprob, hsum, tree, hpart⟩ := h 3 (by norm_num)
  have hunion : (∅ : Finset (Fin 3)) ∪ ({0} : Finset (Fin 3)) ∪ ({1, 2} : Finset (Fin 3))
      = Finset.univ := by decide
  have hd12 : Disjoint (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) := by simp
  have hd13 : Disjoint (∅ : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) := by simp
  have hd23 : Disjoint ({0} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3)) := by decide
  have key := hpart (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) ({1, 2} : Finset (Fin 3))
    hunion hd12 hd13 hd23
  have hempty : (Finset.univ.filter (fun ω => (tree ω).IsClade (∅ : Finset (Fin 3))
      ∧ (tree ω).IsClade ({0} : Finset (Fin 3))
      ∧ (tree ω).IsClade ({1, 2} : Finset (Fin 3)))) = ∅ :=
    Finset.filter_false_of_mem (fun ω _ h => not_isClade_empty (tree ω) h.1)
  rw [hempty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair (by decide : (1 : Fin 3) ≠ 2)] at key
  simp only [Finset.sum_empty] at key
  rw [qTriple_zero_one_two] at key
  norm_num at key

/-- ★★★ **加回「非空」前提后，缺口 G3 在 `n = 3` 上**完整成立**（无条件）。

见证：`Ω = PUnit`、`prob ≡ 1`、`tree ≡ starTree3`（★ 其实**任意**树都行）。
`Fin 3` 的**非空**三分划只有一种形状 —— 三块 `card ≥ 1` 且**和为 `3`** ⇒ 各 `card = 1`
⇒ 三块都是单点集 ⇒ 三者**恒**是 clan ⇒ 左端 `= ∑ prob = 1`；
右端 `= qTriple 1 1 1 = 1`（★★ `qTriple_one_one_one`）。

⚠️ 这是**加前提后**那条命题的实例（**不是** §6 那条 `def` 的证明 —— 那条为假，
见 ★★★ `tripleClanLawGap_false`）。`n ≥ 4` 时 `aᵢ ≥ 2` 的分划仍要 `MSCTreeLaw n`。 -/
theorem tripleClanLawGap_nonempty_three_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 3)),
      ∀ A1 A2 A3 : Finset (Fin 3),
        (A1 ∪ A2 ∪ A3 = Finset.univ) → Disjoint A1 A2 → Disjoint A1 A3 → Disjoint A2 A3 →
        A1.Nonempty → A2.Nonempty → A3.Nonempty →
        (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A1 ∧ (tree ω).IsClade A2
            ∧ (tree ω).IsClade A3), prob ω)
          = qTriple A1.card A2.card A3.card := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => by norm_num, by simp,
    fun _ => starTree3, ?_⟩
  intro A1 A2 A3 hunion h12 h13 h23 hne1 hne2 hne3
  have hc : (A1 ∪ A2 ∪ A3).card = A1.card + A2.card + A3.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h13, h23⟩),
      Finset.card_union_of_disjoint h12]
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hc
  have h1 : 1 ≤ A1.card := Finset.card_pos.mpr hne1
  have h2 : 1 ≤ A2.card := Finset.card_pos.mpr hne2
  have h3 : 1 ≤ A3.card := Finset.card_pos.mpr hne3
  have e1 : A1.card = 1 := by omega
  have e2 : A2.card = 1 := by omega
  have e3 : A3.card = 1 := by omega
  have hclade : ∀ (A : Finset (Fin 3)) (T : Cladogram.{0, 0} (Fin 3)),
      A.Nonempty → A.card = 1 → T.IsClade A := by
    intro A T hA hcard
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hcard
    exact Cladogram.exists_isSplitOf_singleton T x
  have hpred : ∀ ω : PUnit, ((fun _ : PUnit => starTree3) ω).IsClade A1
      ∧ ((fun _ : PUnit => starTree3) ω).IsClade A2
      ∧ ((fun _ : PUnit => starTree3) ω).IsClade A3 := fun _ =>
    ⟨hclade A1 starTree3 hne1 e1, hclade A2 starTree3 hne2 e2,
      hclade A3 starTree3 hne3 e3⟩
  rw [Finset.filter_true_of_mem (fun ω _ => hpred ω), e1, e2, e3, qTriple_one_one_one]
  simp

/-! ## 8. 杠杆器材：一般 `n` 的律容器 `MSCTreeLaw n` ＋ `n = 4` 的 YHK 律实例

### 8.1 为什么需要容器 —— 以及它**不是**什么

`YHKClanLawGap`（§6）的 `∃ Ω, prob, tree` 三个槽位在库里**没有可命名的对象**：
每次要谈「YHK 律下 `A` 是 clan 的概率」，都只能在定理里现写
`{Ω : Type} [Fintype Ω] (prob : Ω → ℝ) (h : ∑ ω, prob ω = 1) (tree : …)`。本节把这组数据收成
**可命名、可传参、可构造**的结构体：

* `MSCTreeLaw n` ＝ 有限概率空间 `Ω` ＋ `prob : Ω → ℝ`（**非负** ＋ **全概率 `1`**）＋
  `tree : Ω → Cladogram (Fin n)`，即「`n` 叶**无根**拓扑上的一个概率律」；
* `MSCTreeLaw.clanEvent L A` ＝「`A` 是 `L` 的随机树的 clan」的**事件概率**（有限和，不是测度）。

⚠️ **纪律（防止把结论写进假设）**：`MSCTreeLaw` 只装**数据与概率公理**（`0 ≤ prob`、`∑ prob = 1`），
**不装**「`clanEvent A = clanProb n A.card`」这类断言 —— 那正是缺口要证的东西。
故本容器**不能**用来假设缺口成立；它的用途是让 `n = 4` 的 YHK 律**被构造出来**（§8.3），
而不是被假定存在。

### 8.2 容器上的**一般 `n`** 性质（无假设）

`clanProb` 是闭形式（§3），`clanEvent` 是概率；两者在**平凡基数**上对**任意**律相等
（★★★ `clanEvent_eq_clanProb_of_trivial_card`）：`A` 是单点集或单点集的补 ⇒ 「`A` 是 clan」
是**必然事件** ⇒ 左端 `= ∑ prob = 1`，右端由 ★★ `clanProb_one` / ★★ `clanProb_pred` 也是 `1`。
这与 §5.2 的 `yhkClanLawGap_trivial_card_slice` 是**同一件事的容器版**（那条写成裸 `prob`/`tree`）。

### 8.3 `n = 4`：把 YHK 律**造出来**

文献 `:991-996` 指出「YHK 是**有根**过程，而在**无根**树上诱导出概率」；`Fin 4` 的无根拓扑只有
3 棵 quartet 树，且 `A | X−A` 的 6 个二元 split 在 3 棵树间**恰好各出现一次**（每棵 two-sided
split 给出两个互补的二元子集）。故 `n = 4` 的 YHK/Kingman 律是**均匀三条**（各 `1/3`）：

* 三棵树：★★ `qTree i`（`i = 0,1,2`），由 ★★★ `Cladogram.ofCompatibleSplits` 用族
  `{qSplit i, (qSplit i).swap}` 造出，`qSplit i` 的两侧是 `{0, 1+i}` 与其补
  （★★ `qPair`、★★ `sideA_qSplit`、★★ `sideB_qSplit`）；
* 「`A` 是第 `i` 棵的 clan」**完全刻画**为 `A = qPair i ∨ A = (qPair i)ᶜ`（★★★ `isClade_qTree_iff`，
  由 §5.3 的 ★★★ `isClade_ofCompatible_pair` 去掉平凡支）；
* 于是 `Fin 4` 的**每个**二元子集**恰在 1 棵**里成 clan（★★★ `existsUnique_qPair`）⇒
  事件概率 `= 1/3 = clanProb 4 2`（★★★ `qTree_clanEvent_two`、★★★ `yhkLawFour_clanEvent_two`）。

**W25 卡点的处理**：`Finset.filter`（谓词含 `IsClade`）的 `DecidablePred` 落到
`Classical.propDecidable`，`decide` 在 `Finset.card` 上**不归约**。本节的解法是
**不求值滤子** —— 用 `Finset.ext` ＋ `∃!` 把滤子**结构性地**化成单点集 `{i₀}`（不走 `decide`），
故**不需要**「把谓词改成可计算谓词」这件器材。

### 8.4 边界（不得夸大）

* 本节**没有**证 `YHKClanLawGap`：那条是 `∀ n`，一般 `n` 仍缺**两件具名器材**：
  ① **一般 `n` 的 YHK 权重函数**（`n` 叶无根拓扑上的 `2^{n−1}/(n!·∏…)` 型权；库内最近的是
  `MSCKingman.root_topology_class_prob`（仅 `Fin 4`）与 `MSCProof.mscFreqFin4`，都**不是**一般 `n`）；
  ② **有根 → 无根桥**（`Cladogram` 无 root；`Fin 4` 时由「3 棵等权」一步跨过，一般 `n` 不行）。
* 已落地的是缺口的**整条 `n = 4`**（★★★ `yhkClanLawGap_four_slice`）与 `n = 3`（§5.2）。 -/

/-- **`n` 叶无根拓扑上的一个概率律**（器材）：有限概率空间 ＋ 树映射 ＋ 概率公理。

★ 各字段的含义与**纪律**见 §8.1：本结构**只装数据**，不装任何「事件概率 = 闭形式」的断言。 -/
structure MSCTreeLaw (n : ℕ) where
  /-- 样本空间（有限）。 -/
  Ω : Type
  /-- `Ω` 的有限性（作为实例登记，便于直接写 `∑ ω`）。 -/
  [fintype : Fintype Ω]
  /-- 概率质量函数。 -/
  prob : Ω → ℝ
  /-- 非负性。 -/
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  /-- 全概率为 `1`。 -/
  prob_sum : ∑ ω, prob ω = 1
  /-- 每点是一棵 `n` 叶**无根**树（`Cladogram` 即无根载体；其 `IsClade` 是学界的 clan）。 -/
  tree : Ω → Cladogram.{0, 0} (Fin n)

/-- 把 `MSCTreeLaw.fintype` 登记为全局实例：`L : MSCTreeLaw n` 的 `L.Ω` 上可直接写 `∑ ω`。 -/
instance {n : ℕ} (L : MSCTreeLaw n) : Fintype L.Ω := L.fintype

namespace MSCTreeLaw

variable {n : ℕ} (L : MSCTreeLaw n)

/-- **`A` 是 `L` 的随机树的 clan** 的**事件概率**（§8.1 的 `clanEvent`）。 -/
noncomputable def clanEvent (A : Finset (Fin n)) : ℝ :=
  ∑ ω ∈ (Finset.univ : Finset L.Ω).filter (fun ω => (L.tree ω).IsClade A), L.prob ω

/-- ★★ **`∅` 的事件概率恒 `0`**（任意 `n`、任意律）：`∅` 永远不是 clan（★★ `not_isClade_empty`）。 -/
theorem clanEvent_empty : L.clanEvent (∅ : Finset (Fin n)) = 0 := by
  have h : (Finset.univ : Finset L.Ω).filter
      (fun ω => (L.tree ω).IsClade (∅ : Finset (Fin n))) = ∅ :=
    Finset.filter_false_of_mem (fun ω _ hc => not_isClade_empty (L.tree ω) hc)
  simp only [clanEvent, h, Finset.sum_empty]

/-- ★★ **单点集的事件概率恒 `1`**（`n ≥ 2`、任意律）：单点集在任何树上都是 clan。 -/
theorem clanEvent_singleton (hn : 2 ≤ n) (x : Fin n) :
    L.clanEvent ({x} : Finset (Fin n)) = 1 := by
  have : Nontrivial (Fin n) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      exact absurd (Fin.mk.inj h) (by omega)⟩
  have h : (Finset.univ : Finset L.Ω).filter
      (fun ω => (L.tree ω).IsClade ({x} : Finset (Fin n))) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ => Cladogram.exists_isSplitOf_singleton (L.tree ω) x)
  rw [clanEvent, h, L.prob_sum]

/-- ★★ **单点集的补的事件概率恒 `1`**（`n ≥ 2`、任意律）：由 ★★ `isClade_compl` 与上一行。 -/
theorem clanEvent_compl_singleton (hn : 2 ≤ n) (x : Fin n) :
    L.clanEvent (({x} : Finset (Fin n))ᶜ) = 1 := by
  have : Nontrivial (Fin n) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      exact absurd (Fin.mk.inj h) (by omega)⟩
  have h : (Finset.univ : Finset L.Ω).filter
      (fun ω => (L.tree ω).IsClade (({x} : Finset (Fin n))ᶜ)) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ =>
      (isClade_compl (L.tree ω) {x}).mpr (Cladogram.exists_isSplitOf_singleton (L.tree ω) x))
  rw [clanEvent, h, L.prob_sum]

/-- ★★★ **平凡基数上「概率 = 闭形式」对任意律成立**（`A.card ∈ {1, n−1}`）。

这是 §5.2 的 ★★★ `yhkClanLawGap_trivial_card_slice` 的**容器版**：
**不需要** YHK 律，也不需要 `0 ≤ prob`（本定理因此比缺口的那一侧更强）。 -/
theorem clanEvent_eq_clanProb_of_trivial_card (hn : 2 ≤ n) (A : Finset (Fin n))
    (hcard : A.card = 1 ∨ A.card = n - 1) : L.clanEvent A = clanProb n A.card := by
  rcases hcard with h1 | h1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
    rw [clanEvent_singleton L hn x, Finset.card_singleton, clanProb_one hn]
  · have hc : Aᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h1]
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have hA : A = (({x} : Finset (Fin n))ᶜ) := by rw [← hx, compl_compl]
    rw [hA, clanEvent_compl_singleton L hn x, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin, clanProb_pred hn]

end MSCTreeLaw

/-! ### 8.5 `n = 4` 的三棵 quartet 树与 `1/3` 律 -/

/-- ★★ **第 `i` 个二元 split 的一侧**：`{0, i+1}`（`i = 0,1,2` 给出 `{0,1}`、`{0,2}`、`{0,3}`）。 -/
def qPair (i : Fin 3) : Finset (Fin 4) := {0, Fin.succ i}

/-- `(0 : Fin 4) ≠ Fin.succ i`（`Fin.succ` 的值是 `i.val + 1`）。 -/
theorem zero_ne_succ_fin4 (i : Fin 3) : (0 : Fin 4) ≠ Fin.succ i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_succ] at h'
  omega

/-- `qPair` 的成员刻画。 -/
theorem mem_qPair (i : Fin 3) (x : Fin 4) : x ∈ qPair i ↔ x = 0 ∨ x = Fin.succ i := by
  simp [qPair]

/-- ★★ **每个 `qPair i` 恰有 `2` 个元素**。 -/
theorem card_qPair (i : Fin 3) : (qPair i).card = 2 := by
  simp [qPair, zero_ne_succ_fin4 i]

theorem qPair_nonempty (i : Fin 3) : (qPair i).Nonempty :=
  Finset.card_pos.mp (by rw [card_qPair]; norm_num)

/-- ★★ **`qPair i` 的补也恰有 `2` 个元素**（`Fin 4` 的互补二元子集）。 -/
theorem card_compl_qPair (i : Fin 3) : ((qPair i)ᶜ : Finset (Fin 4)).card = 2 := by
  rw [Finset.card_compl, Fintype.card_fin, card_qPair]

theorem compl_qPair_nonempty (i : Fin 3) : ((qPair i)ᶜ : Finset (Fin 4)).Nonempty :=
  Finset.card_pos.mp (by rw [card_compl_qPair]; norm_num)

/-- ★★ **`0` 不在任何 `qPair i` 的补里**（`0 ∈ qPair i`）。这条是 `∃!` 的**唯一性**支点。 -/
theorem mem_compl_qPair_zero (i : Fin 3) : (0 : Fin 4) ∉ (qPair i)ᶜ := by
  simp [qPair]

/-- ★★ **第 `i` 条 quartet split**：`{0, i+1} | 其补`（由 ★★ `splitOf` 造）。 -/
noncomputable def qSplit (i : Fin 3) : Split (Fin 4) :=
  splitOf (qPair i) (qPair_nonempty i) (compl_qPair_nonempty i)

theorem sideA_qSplit (i : Fin 3) : (qSplit i).sideA = qPair i := by
  simp [qSplit]

theorem sideB_qSplit (i : Fin 3) : (qSplit i).sideB = (qPair i)ᶜ := by
  simp [qSplit]

/-- ★★ **第 `i` 条 quartet split 非平凡**（两侧各 `2` 叶）。 -/
theorem qSplit_nontrivial (i : Fin 3) :
    2 ≤ (qSplit i).sideA.card ∧ 2 ≤ (qSplit i).sideB.card := by
  rw [sideA_qSplit, sideB_qSplit, card_qPair, card_compl_qPair]
  exact ⟨le_refl 2, le_refl 2⟩

/-- ★★★ **第 `i` 棵 quartet 树**：由族 `{qSplit i, (qSplit i).swap}` 造（§5.3 器材的直接用例）。 -/
noncomputable def qTree (i : Fin 3) : Cladogram.{0, 0} (Fin 4) :=
  Cladogram.ofCompatibleSplits {qSplit i, (qSplit i).swap} 0
    (compatible_pair_swap (qSplit i)) (nontrivial_pair_swap (qSplit_nontrivial i))
    (swap_closed_pair_swap (qSplit i)) (by decide : 3 ≤ Fintype.card (Fin 4))

/-- ★★★ **`qTree i` 的 clan 集被完全刻画**：`A`（`card = 2`）是第 `i` 棵的 clan
⟺ `A` 就是 `qPair i` 或它的补。

由 §5.3 的 ★★★ `isClade_ofCompatible_pair` 去掉两个「平凡」支（`card = 2` 排除单点集与其补）。 -/
theorem isClade_qTree_iff (i : Fin 3) (A : Finset (Fin 4)) (hA : A.card = 2) :
    (qTree i).IsClade A ↔ A = qPair i ∨ A = (qPair i)ᶜ := by
  have h := isClade_ofCompatible_pair (s := qSplit i) (ρ := (0 : Fin 4))
    (hn := qSplit_nontrivial i) (h3 := (by decide : 3 ≤ Fintype.card (Fin 4))) A
  have h' : (qTree i).IsClade A ↔
      A = qPair i ∨ A = (qPair i)ᶜ ∨ (∃ x : Fin 4, A = {x}) ∨ (∃ x : Fin 4, A = {x}ᶜ) := by
    simp only [qTree, qSplit]
    exact h
  rw [h']
  constructor
  · rintro (h1 | h1 | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      rw [hx, Finset.card_singleton] at hA
      omega
    · exfalso
      rw [hx, Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hA
      omega
  · rintro (h1 | h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

/-- ★★ **`qPair` 是单射**（`0` 固定、`Fin.succ` 单射）。 -/
theorem qPair_injective : Function.Injective qPair := by
  intro i j h
  have hmem : Fin.succ i ∈ qPair j := by rw [← h]; simp [qPair]
  rcases (mem_qPair j (Fin.succ i)).mp hmem with h0 | hs
  · exact absurd h0 (zero_ne_succ_fin4 i).symm
  · exact Fin.succ_inj.mp hs

/-- ★★ **`0 ∈ A` 且 `card A = 2` ⇒ `A = qPair i` 对某个 `i`**（`A.erase 0` 是单点集）。 -/
theorem exists_qPair_of_mem_zero {A : Finset (Fin 4)} (hA : A.card = 2)
    (h0 : (0 : Fin 4) ∈ A) : ∃ i : Fin 3, A = qPair i := by
  have herase : (A.erase 0).card = 1 := by
    rw [Finset.card_erase_of_mem h0, hA]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
  have hA' : A = {0, x} := by
    rw [← Finset.insert_erase h0, hx]
  have hxne : x ≠ 0 := by
    have hmem : x ∈ A.erase 0 := by rw [hx]; exact Finset.mem_singleton_self x
    exact (Finset.mem_erase.mp hmem).1
  have hxval : x.val ≠ 0 := fun h => hxne (Fin.ext (by simpa using h))
  have hsucc : Fin.succ (⟨x.val - 1, by omega⟩ : Fin 3) = x := Fin.ext (by simp; omega)
  exact ⟨⟨x.val - 1, by omega⟩, by rw [qPair, hA', hsucc]⟩

/-- ★★ **每个二元子集都是某个 `qPair i` 或它的补**（按 `0 ∈ A` 与否二分，补集情形化归上一行）。 -/
theorem exists_qPair {A : Finset (Fin 4)} (hA : A.card = 2) :
    ∃ i : Fin 3, A = qPair i ∨ A = (qPair i)ᶜ := by
  by_cases h0 : (0 : Fin 4) ∈ A
  · obtain ⟨i, hi⟩ := exists_qPair_of_mem_zero hA h0
    exact ⟨i, Or.inl hi⟩
  · have hc0 : (0 : Fin 4) ∈ Aᶜ := Finset.mem_compl.mpr h0
    have hcA : Aᶜ.card = 2 := by
      rw [Finset.card_compl, Fintype.card_fin, hA]
    obtain ⟨i, hi⟩ := exists_qPair_of_mem_zero hcA hc0
    exact ⟨i, Or.inr (by rw [← hi, compl_compl])⟩

/-- ★★ **唯一性**：同一条 `A = qPair i ∨ A = qPair iᶜ` 不可能是两个不同 `i` 的见证
（`qPair i` 含 `0`、`qPair iᶜ` 不含 `0`）。 -/
theorem qPair_unique {i j : Fin 3} {A : Finset (Fin 4)}
    (hi : A = qPair i ∨ A = (qPair i)ᶜ) (hj : A = qPair j ∨ A = (qPair j)ᶜ) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact qPair_injective (hi.symm.trans hj)
  · exfalso
    have hmem : (0 : Fin 4) ∈ A := by rw [hi]; simp [qPair]
    rw [hj] at hmem
    exact mem_compl_qPair_zero j hmem
  · exfalso
    have hmem : (0 : Fin 4) ∈ A := by rw [hj]; simp [qPair]
    rw [hi] at hmem
    exact mem_compl_qPair_zero i hmem
  · have hcompl : (qPair i)ᶜ = (qPair j)ᶜ := by rw [← hi, hj]
    refine qPair_injective (by simpa using congrArg (fun s : Finset (Fin 4) => sᶜ) hcompl)

/-- ★★★ **`Fin 4` 的每个二元子集恰在 1 棵 quartet 树里成 clan**（`∃!` 形态）。

这条就是 §5.2 里被 W25 判为「可证」的那件事的组合核心，也是绕开 `decide` 的关键器材：
**不**求值 `Finset.filter`，而是把「哪个 `i`」结构性指出。 -/
theorem existsUnique_qPair (A : Finset (Fin 4)) (hA : A.card = 2) :
    ∃! i : Fin 3, A = qPair i ∨ A = (qPair i)ᶜ := by
  obtain ⟨i, hi⟩ := exists_qPair hA
  exact ⟨i, hi, fun j hj => qPair_unique hj hi⟩

/-- ★★★ **`n = 4` 的 clan 事件概率**：若 `A` 的基数是 `2`，
则它在均匀三条 quartet 律下的概率 `= 1/3 = clanProb 4 2`（★★ `clanProb_four_two`）。

证明**不**用 `decide`：由 ★★★ `existsUnique_qPair` 得唯一见证 `i₀`，
再用 `Finset.ext` 把滤子化成 `{i₀}`（★★★ `isClade_qTree_iff`），最后 `sum_singleton`。 -/
theorem qTree_clanEvent_two (A : Finset (Fin 4)) (hA : A.card = 2) :
    (∑ _i ∈ Finset.univ.filter (fun i : Fin 3 => (qTree i).IsClade A), (1 / 3 : ℝ))
      = clanProb 4 A.card := by
  obtain ⟨i₀, hi₀, huniq⟩ := existsUnique_qPair A hA
  have hfilter : Finset.univ.filter (fun i : Fin 3 => (qTree i).IsClade A) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [isClade_qTree_iff i A hA]
    exact ⟨fun h => huniq i h, fun h => by rw [h]; exact hi₀⟩
  rw [hfilter, Finset.sum_singleton, hA, clanProb_four_two]

/-- ★★★ **`n = 4` 的 YHK/Kingman 无根拓扑律**（§8.3）：`Ω = Fin 3`、三棵 quartet 树**等权 `1/3`**。

`1/3` 不是规定：`Fin 4` 的 `C(4,2) = 6` 个二元 split 在 3 棵两两侧的树里**各出现一次**
（★★★ `existsUnique_qPair`），故均匀三条就是 YHK 在无根拓扑上的诱导律
（与 `MSCKingman.root_topology_class_prob` 的 `Fin 4` 推导一致，文献 `:191-216`、`:991-996`）。 -/
noncomputable def yhkLawFour : MSCTreeLaw 4 where
  Ω := Fin 3
  fintype := inferInstance
  prob := fun _ => 1 / 3
  prob_nonneg := fun _ => by norm_num
  prob_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  tree := qTree

/-- ★★ **该律不是空壳**：`MSCTreeLaw 4` 有一个**构造出来的**居留者（不是被假设存在）。 -/
theorem yhkLawFour_nonempty : Nonempty (MSCTreeLaw 4) := ⟨yhkLawFour⟩

/-- ★★★ **容器版取值定理**：在 ★★★ `yhkLawFour` 下，二元子集的事件概率 `= clanProb 4 2 = 1/3`。 -/
theorem yhkLawFour_clanEvent_two (A : Finset (Fin 4)) (hA : A.card = 2) :
    MSCTreeLaw.clanEvent yhkLawFour A = clanProb 4 A.card := by
  change (∑ _i ∈ Finset.univ.filter (fun i : Fin 3 => (qTree i).IsClade A), (1 / 3 : ℝ))
    = clanProb 4 A.card
  exact qTree_clanEvent_two A hA

/-- ★★★ **缺口 `YHKClanLawGap` 在 `n = 4` 上的整条**（无条件）。

这是 §6 的 `def` 在 `n = 4` 的 `∃` 从句的**完整**成立 —— 见证
`Ω = Fin 3`、`prob ≡ 1/3`、`tree = qTree`：
* `A.card = 1` 或 `3`：★★★ `yhkClanLawGap_trivial_card_slice`（任意律）；
* `A.card = 2`：★★★ `qTree_clanEvent_two`（`= 1/3 = clanProb 4 2`，非退化值）。

⚠️ **边界**：这不是 `YHKClanLawGap` 的证明（那条是 `∀ n`，一般 `n` 仍缺 §8.4 的两件器材）。 -/
theorem yhkClanLawGap_four_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 4)),
      ∀ A : Finset (Fin 4), A.Nonempty → A.card < 4 →
        (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
          = clanProb 4 A.card := by
  refine ⟨Fin 3, inferInstance, fun _ => 1 / 3, fun _ => by norm_num, ?_, qTree, ?_⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · intro A hne hlt
    have hpos : 1 ≤ A.card := Finset.card_pos.mpr hne
    have hcases : A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · exact yhkClanLawGap_trivial_card_slice (n := 4) (by norm_num) (fun _ => 1 / 3) (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
        _ hne (Or.inl h1)
    · simpa using qTree_clanEvent_two A h2
    · exact yhkClanLawGap_trivial_card_slice (n := 4) (by norm_num) (fun _ => 1 / 3) (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num)
        _ hne (Or.inr (by omega))


/-! ### 8.6 容器的回报：`n = 3` 的整条对**任意**律成立

§5.2 的 ★★★ `yhkClanLawGap_three_slice` 只给出**一个**见证（退化分布 ＋ 星形树）。
有了容器就能说更强的话：`Fin 3` 的**任何**律都满足缺口在 `n = 3` 的等式
（因为 `Fin 3` 的非空真子集只有 `card = 1` 与 `card = 2 = 3 − 1` 两种形状，
而平凡基数上概率恒等于闭形式，见 ★★★ `clanEvent_eq_clanProb_of_trivial_card`）。 -/

namespace MSCTreeLaw

variable (L : MSCTreeLaw 3)

/-- ★★★ **`n = 3` 的整条对任意律成立**（容器版 `yhkClanLawGap_three_slice`，但**无需**选见证）。 -/
theorem clanEvent_eq_clanProb_three (A : Finset (Fin 3)) (hne : A.Nonempty)
    (hlt : A.card < 3) : L.clanEvent A = clanProb 3 A.card := by
  have hpos : 1 ≤ A.card := Finset.card_pos.mpr hne
  rcases (show A.card = 1 ∨ A.card = 3 - 1 by omega) with h1 | h1
  · exact L.clanEvent_eq_clanProb_of_trivial_card (by norm_num) A (Or.inl h1)
  · exact L.clanEvent_eq_clanProb_of_trivial_card (by norm_num) A (Or.inr h1)

end MSCTreeLaw

/-! ### 8.7 `TwoClanLawGap`（§6 G2）在 `n = 3` 与 `n = 4` 的整条

`TwoClanLawGap` 的 RHS 是 `if a + b = n then qnExhaustive a b else qn n a b`，与
`YHKClanLawGap` 的单块 `clanProb n a` **不同**：它是**两块**（穷尽支 / 非穷尽支）。本节把这条
缺口推到与 ★★★ `yhkClanLawGap_four_slice` **同样的强度**，并把 `n = 3` 做成对**任意**律成立。

* **`n = 3`（任意律、任意概率空间）**：`Fin 3` 的非空真子集只有 `card = 1` 与 `card = 2 = 3 − 1`，
  两者恒是 clan（★★ `isClade_three_of_trivial_card`）⇒「`A`、`B` 都是 clan」是**必然事件**
  ⇒ 左端 `= ∑ prob = 1`；右端三种可能 `(1,1)`/`(1,2)`/`(2,1)` 分别是 `qn 3 1 1 = 1` 与
  `qnExhaustive 1 2 = qnExhaustive 2 1 = 1`（★★ `qn_three_one_one`、★★ `qnExhaustive_one_left/right`）。
* **`n = 4`（`yhkLawFour` 的 3 棵 quartet 等权）**：`A`、`B` 的基数落进 6 个组合
  `(1,1) (1,2) (1,3) (2,1) (2,2) (3,1)`（`A.card + B.card ≤ 4` ＋ 两侧非空 ⇒ 每个都 `≤ 3`）。
  其中基数为 `1` 或 `3` 的集合**恒**是 clan（★★ `isClade_qTree_of_trivial_card`）；
  **唯一**的实质情形是某个集合基数为 `2` —— 由 ★★★ `existsUnique_qPair` 它的成 clan 恰在
  **1 棵**树上（★★★ `qTree_filter_pair_singleton` 把滤子化成单点集，**仍不用** `decide`），
  故概率 `= 1/3`。右端对应 `qn 4 1 1 = 1`、`qn 4 1 2 = qn 4 2 1 = 1/3`（新证三条闭形式锚点）、
  `qnExhaustive 1 3 = qnExhaustive 3 1 = 1`、`qnExhaustive 2 2 = 1/3`。

⚠️ **边界（不得夸大）**：本节**没有**证 `TwoClanLawGap`（`∀ n`）：一般 `n` 的 `a + b < n` 支
需要 Theorem 6.3(ii) 的三事件分解（`rn` ＋ 两个 `Rn` ＋ 两个 `p̂n·p`）的**概率层**，
仍缺 §8.4 的那两件具名器材（一般 `n` 的 YHK 权重、有根→无根桥）。`def` **一字未改**。 -/

/-- ★★ **Theorem 6.3(ii) 的闭形式锚点**：`qn 3 1 1 = 1`（`(n,a,b) = (3,1,1)`，`a + b < n`）。

纯实数算术（`qn` / `rn` / `Rn` / `pn` / `p̂n` / `Gn` 的转写逐项求值），无概率断言。 -/
theorem qn_three_one_one : qn 3 1 1 = 1 := by
  unfold qn rn Rn pnHatExh pn Gn
  norm_num

/-- ★★ **闭形式锚点**：`qn 4 1 1 = 1`（`(n,a,b) = (4,1,1)`，`a + b < n`）。

语义上这是「两个单点集同成 clan」的概率 `= 1`（单点集恒是 clan），与 §8.7 的组合侧一致。 -/
theorem qn_four_one_one : qn 4 1 1 = 1 := by
  unfold qn rn Rn pnHatExh pn Gn
  norm_num

/-- ★★ **闭形式锚点**：`qn 4 1 2 = 1/3`（`(n,a,b) = (4,1,2)`，`a + b = 3 < 4`）。 -/
theorem qn_four_one_two : qn 4 1 2 = 1 / 3 := by
  have h1 : Nat.choose 4 2 = 6 := by decide
  unfold qn rn Rn pnHatExh pn Gn
  rw [h1]
  norm_num

/-- ★★ **闭形式锚点**：`qn 4 2 1 = 1/3`（`qn` 关于两块对称的显式核对）。 -/
theorem qn_four_two_one : qn 4 2 1 = 1 / 3 := by
  have h1 : Nat.choose 4 2 = 6 := by decide
  unfold qn rn Rn pnHatExh pn Gn
  rw [h1]
  norm_num

/-! #### 8.7.1 `n = 3`：对**任意**律成立 -/

/-- ★★★ **`Fin 3` 上 `card ∈ {1, 2}` 的集恒是 clan**（任意树）：`card = 1` 是 `{x}`，
`card = 2` 是 `{x}ᶜ`（★★ `isClade_compl` ＋ ★★ `Cladogram.exists_isSplitOf_singleton`）。 -/
theorem isClade_three_of_trivial_card (T : Cladogram (Fin 3)) (A : Finset (Fin 3))
    (h : A.card = 1 ∨ A.card = 2) : T.IsClade A := by
  rcases h with h1 | h1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
    exact Cladogram.exists_isSplitOf_singleton T x
  · have hc : Aᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h1]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have hA : A = ({x} : Finset (Fin 3))ᶜ := by rw [← hx, compl_compl]
    rw [hA]
    exact (isClade_compl T {x}).mpr (Cladogram.exists_isSplitOf_singleton T x)

/-- ★★★ **`n = 3`：缺口等式对任意概率空间、任意树族（故任意律）成立**（无需 `0 ≤ prob`）。

左端是**必然事件**的概率 `= ∑ prob = 1`；右端由三种可能的基数组合各自化成 `1`
（★★ `qn_three_one_one`、★★ `qnExhaustive_one_left` / `qnExhaustive_one_right`）。 -/
theorem clanPairEvent_three {Ω : Type} [Fintype Ω] (prob : Ω → ℝ) (hsum : ∑ ω, prob ω = 1)
    (tree : Ω → Cladogram.{0, 0} (Fin 3)) (A B : Finset (Fin 3)) (hA : A.Nonempty)
    (hB : B.Nonempty) (hc : A.card + B.card ≤ 3) :
    (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B), prob ω)
      = if A.card + B.card = 3 then qnExhaustive A.card B.card else qn 3 A.card B.card := by
  have ha1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hb1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have ha : A.card = 1 ∨ A.card = 2 := by omega
  have hb : B.card = 1 ∨ B.card = 2 := by omega
  have hfilter : Finset.univ.filter
      (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B) = Finset.univ :=
    Finset.filter_true_of_mem (fun ω _ =>
      ⟨isClade_three_of_trivial_card (tree ω) A ha,
        isClade_three_of_trivial_card (tree ω) B hb⟩)
  rw [hfilter, hsum]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb, ite_eq_right (by norm_num : ¬ ((1 : ℕ) + 1 = 3))]
    exact qn_three_one_one.symm
  · rw [ha, hb, ite_eq_left (by norm_num : (1 : ℕ) + 2 = 3),
      qnExhaustive_one_left (by norm_num : 1 ≤ 2)]
  · rw [ha, hb, ite_eq_left (by norm_num : (2 : ℕ) + 1 = 3),
      qnExhaustive_one_right (by norm_num : 1 ≤ 2)]
  · exfalso
    omega

/-- ★★★ **缺口 `TwoClanLawGap` 在 `n = 3` 上的整条**（无条件）。

见证：`Ω = PUnit`、`prob ≡ 1`、`tree ≡ starTree3`（★★ `starTree3`，星形 —— 与 ★★★
`yhkClanLawGap_three_slice` 同一个见证）。实际证明用的是 ★★★ `clanPairEvent_three`
（对**任意**律成立），故本定理的强度不依赖该见证。 -/
theorem twoClanLawGap_three_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 3)),
      ∀ A B : Finset (Fin 3), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card ≤ 3 →
        (∑ ω ∈ Finset.univ.filter
            (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B), prob ω)
          = if A.card + B.card = 3 then qnExhaustive A.card B.card
            else qn 3 A.card B.card :=
  ⟨PUnit, inferInstance, fun _ => 1, fun _ => by norm_num, by simp, fun _ => starTree3,
    fun A B _ hA hB hc => clanPairEvent_three (fun _ => 1) (by simp) (fun _ => starTree3)
      A B hA hB hc⟩

/-! #### 8.7.2 `n = 4`：用 `yhkLawFour` 的 3 棵 quartet 树 -/

/-- ★★★ **`Fin 4` 上 `card ∈ {1, 3}` 的集在任意 `qTree` 上恒是 clan**
（`card = 1` 是 `{x}`、`card = 3` 是 `{x}ᶜ`）。 -/
theorem isClade_qTree_of_trivial_card (A : Finset (Fin 4))
    (h : A.card = 1 ∨ A.card = 3) (i : Fin 3) : (qTree i).IsClade A := by
  rcases h with h1 | h1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
    exact Cladogram.exists_isSplitOf_singleton (qTree i) x
  · have hc : Aᶜ.card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h1]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    have hA : A = ({x} : Finset (Fin 4))ᶜ := by rw [← hx, compl_compl]
    rw [hA]
    exact (isClade_compl (qTree i) {x}).mpr
      (Cladogram.exists_isSplitOf_singleton (qTree i) x)

/-- ★★ **`A`、`B` 都只有平凡基数 ⇒ 「两者都是 clan」是必然事件**（滤子 ＝ 全集）。 -/
theorem qTree_filter_pair_univ {A B : Finset (Fin 4)}
    (hA : A.card = 1 ∨ A.card = 3) (hB : B.card = 1 ∨ B.card = 3) :
    Finset.univ.filter (fun i : Fin 3 => (qTree i).IsClade A ∧ (qTree i).IsClade B)
      = Finset.univ :=
  Finset.filter_true_of_mem (fun i _ =>
    ⟨isClade_qTree_of_trivial_card A hA i, isClade_qTree_of_trivial_card B hB i⟩)

/-- ★★★ **滤子化单点集**：若「两者都是 clan」只在 `i₀` 处成立、且在 `i₀` 处确实成立，
则滤子恰是单点集 `{i₀}`。

这是 §8.3 绕开 `decide` 的手法的**可复用形式**（与 ★★★ `qTree_clanEvent_two` 内的
`hfilter` 同一招）：`Finset.ext` ＋ `∃!`，**不**求值 `DecidablePred`。 -/
theorem qTree_filter_pair_singleton {A B : Finset (Fin 4)} {i₀ : Fin 3}
    (h1 : ∀ j : Fin 3, (qTree j).IsClade A ∧ (qTree j).IsClade B → j = i₀)
    (h2 : (qTree i₀).IsClade A ∧ (qTree i₀).IsClade B) :
    Finset.univ.filter (fun i : Fin 3 => (qTree i).IsClade A ∧ (qTree i).IsClade B)
      = {i₀} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨h1 j, fun h => by rw [h]; exact h2⟩

/-- ★★★ **`n = 4` 的两 clan 事件概率**（在 ★★★ `yhkLawFour`／★★★ `qTree` ＋ 等权 `1/3` 下）。

`A`、`B` 互斥、两侧非空、`A.card + B.card ≤ 4`（故各自基数 `∈ {1,2,3}`）。按 6 种基数组合
逐一处理：平凡基数的组合概率 `= 1`、含 `card = 2` 的组合概率 `= 1/3`（★★★
`qTree_filter_pair_singleton` ＋ ★★★ `existsUnique_qPair`）。 -/
theorem clanPairEvent_qTree_four (A B : Finset (Fin 4)) (hd : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (hc : A.card + B.card ≤ 4) :
    (∑ _i ∈ Finset.univ.filter
        (fun i : Fin 3 => (qTree i).IsClade A ∧ (qTree i).IsClade B), (1 / 3 : ℝ))
      = if A.card + B.card = 4 then qnExhaustive A.card B.card else qn 4 A.card B.card := by
  have ha1 : 1 ≤ A.card := Finset.card_pos.mpr hA
  have hb1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  have hcases : (A.card = 1 ∧ B.card = 1) ∨ (A.card = 1 ∧ B.card = 2) ∨
      (A.card = 1 ∧ B.card = 3) ∨ (A.card = 2 ∧ B.card = 1) ∨
      (A.card = 2 ∧ B.card = 2) ∨ (A.card = 3 ∧ B.card = 1) := by omega
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [qTree_filter_pair_univ (Or.inl ha) (Or.inl hb), ha, hb,
      ite_eq_right (by norm_num : ¬ ((1 : ℕ) + 1 = 4)), qn_four_one_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · obtain ⟨i₀, hi₀, _⟩ := existsUnique_qPair B hb
    rw [qTree_filter_pair_singleton (i₀ := i₀)
      (fun j ⟨_, h2⟩ => qPair_unique ((isClade_qTree_iff j B hb).mp h2) hi₀)
      ⟨isClade_qTree_of_trivial_card A (Or.inl ha) i₀,
        (isClade_qTree_iff i₀ B hb).mpr hi₀⟩,
      ha, hb, ite_eq_right (by norm_num : ¬ ((1 : ℕ) + 2 = 4)), qn_four_one_two,
      Finset.sum_singleton]
  · rw [qTree_filter_pair_univ (Or.inl ha) (Or.inr hb), ha, hb,
      ite_eq_left (by norm_num : (1 : ℕ) + 3 = 4), qnExhaustive_one_left (by norm_num : 1 ≤ 3),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · obtain ⟨i₀, hi₀, _⟩ := existsUnique_qPair A ha
    rw [qTree_filter_pair_singleton (i₀ := i₀)
      (fun j ⟨h1, _⟩ => qPair_unique ((isClade_qTree_iff j A ha).mp h1) hi₀)
      ⟨(isClade_qTree_iff i₀ A ha).mpr hi₀,
        isClade_qTree_of_trivial_card B (Or.inl hb) i₀⟩,
      ha, hb, ite_eq_right (by norm_num : ¬ ((2 : ℕ) + 1 = 4)), qn_four_two_one,
      Finset.sum_singleton]
  · obtain ⟨i₀, hi₀, _⟩ := existsUnique_qPair A ha
    have hun : A ∪ B = Finset.univ := by
      refine Finset.eq_univ_of_card (A ∪ B) ?_
      rw [Finset.card_union_of_disjoint hd, ha, hb]
      norm_num
    have hBc : B = Aᶜ := by
      ext x
      rw [Finset.mem_compl]
      constructor
      · intro hx hxA
        exact Finset.disjoint_left.mp hd hxA hx
      · intro hx
        rcases Finset.mem_union.mp (by rw [hun]; exact Finset.mem_univ x) with h' | h'
        · exact absurd h' hx
        · exact h'
    have hBcl : (qTree i₀).IsClade B := by
      refine (isClade_qTree_iff i₀ B hb).mpr ?_
      rcases hi₀ with h | h
      · exact Or.inr (by rw [hBc, h])
      · exact Or.inl (by rw [hBc, h, compl_compl])
    rw [qTree_filter_pair_singleton (i₀ := i₀)
      (fun j ⟨h1, _⟩ => qPair_unique ((isClade_qTree_iff j A ha).mp h1) hi₀)
      ⟨(isClade_qTree_iff i₀ A ha).mpr hi₀, hBcl⟩,
      ha, hb, ite_eq_left (by norm_num : (2 : ℕ) + 2 = 4), qnExhaustive_two_two,
      Finset.sum_singleton]
  · rw [qTree_filter_pair_univ (Or.inr ha) (Or.inl hb), ha, hb,
      ite_eq_left (by norm_num : (3 : ℕ) + 1 = 4), qnExhaustive_one_right (by norm_num : 1 ≤ 3),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

/-- ★★★ **容器版**：在 ★★★ `yhkLawFour` 下，「`A`、`B` 同为 clan」的事件概率命中缺口的 RHS。 -/
theorem yhkLawFour_twoClanEvent (A B : Finset (Fin 4)) (hd : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (hc : A.card + B.card ≤ 4) :
    (∑ ω ∈ (Finset.univ : Finset yhkLawFour.Ω).filter
        (fun ω => (yhkLawFour.tree ω).IsClade A ∧ (yhkLawFour.tree ω).IsClade B),
        yhkLawFour.prob ω)
      = if A.card + B.card = 4 then qnExhaustive A.card B.card else qn 4 A.card B.card :=
  clanPairEvent_qTree_four A B hd hA hB hc

/-- ★★★ **缺口 `TwoClanLawGap` 在 `n = 4` 上的整条**（无条件）。

与 ★★★ `yhkClanLawGap_four_slice` 同一见证：`Ω = Fin 3`、`prob ≡ 1/3`、`tree = qTree`
（3 棵 quartet 树等权 ＝ ★★★ `yhkLawFour`）。证明即 ★★★ `clanPairEvent_qTree_four`。

⚠️ **边界**：这不是 `TwoClanLawGap` 的证明（那条是 `∀ n`）。 -/
theorem twoClanLawGap_four_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 4)),
      ∀ A B : Finset (Fin 4), Disjoint A B → A.Nonempty → B.Nonempty →
        A.card + B.card ≤ 4 →
        (∑ ω ∈ Finset.univ.filter
            (fun ω => (tree ω).IsClade A ∧ (tree ω).IsClade B), prob ω)
          = if A.card + B.card = 4 then qnExhaustive A.card B.card
            else qn 4 A.card B.card :=
  ⟨Fin 3, inferInstance, fun _ => 1 / 3, fun _ => by norm_num, by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num, qTree, fun A B hd hA hB hc => clanPairEvent_qTree_four A B hd hA hB hc⟩

/-! ## 9. 去根桥：ZDS2011 **Lemma 6.1** 的树层形式（缺口 ② 的器材）

**文献**（`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md`
第 **991–992** 行，逐字）：

> **Lemma 6.1.** Given a rooted binary X–tree, `T`, a set `A` is a clan of `T − ρ` if and only if
> either `A` is a clade of `T` or `X − A` is a clade of `T`.

同文件第 **977–981** 行另有一句本节的直接推论：

> If we suppress the root `ρ` of a rooted binary phylogenetic X–tree `T`, we obtain an unrooted
> binary phylogenetic X–tree, which we will denote as `T − ρ`. … Note that **any clade of the
> rooted tree `T` becomes a clan of `T − ρ`**.

### 表示 —— **不构造 `T − ρ`**

本库的 `Cladogram` 是**无根**载体（`Phylo/Core.lean`）；按 `Phylo/InternalEdge.lean:585-587`
的术语提示，它的 `IsClade` **就是**学界的 **clan**。有根树用
`RootedCladogram X = Cladogram (X ⊕ Unit)` 表示（`Phylo/Core.lean` 的
「有根树的底层实现」一节）：标记叶 `m := Sum.inr ()` 是「名为 `root` 的叶子」，
它的**唯一邻居**就是 `ρ`。

Lemma 6.1 的三样东西因此各有**不需要造新树**的翻译：

| 文献 | 本库 |
| --- | --- |
| `A` 是 `T` 的 **clade** | `U.IsClade (A.image Sum.inl)`（该 split 的一侧**不含** `m`） |
| `X − A` 是 `T` 的 **clade** | `U.IsClade ((Aᶜ).image Sum.inl)` |
| `A` 是 `T − ρ` 的 **clan** | `IsClanMinusRoot U A` ＝ `A` 是某条边某一侧的**真叶集** |

★ **为什么不需要造 `T − ρ`**：抑制 `ρ` 只可能影响与 `ρ` 相邻的边。设 `ρ` 在 `U` 中度 `d ≥ 3`
（`m` 占了 `ρ` 的一条边）。去根后 `ρ` 的度变 `d − 1`：

* 若 `d − 1 = 2`（即 `d = 3`，`T` 二叉）则 `ρ` 被**抑制**，其两条剩余边并成一条 ——
  但这条新边的一侧恰是 `U` 中那两条边**各自一侧**的真叶集，故「`A` 是某条边一侧的真叶集」
  这一判据**自动覆盖**了抑制产生的新 split；
* 若 `d − 1 ≥ 3` 则 `ρ` 直接成活、无需抑制。

**两种情形都被 `realLeaves ⋯ = A` 一条判据一次吞掉**，于是 `IsClanMinusRoot` 无需知道 `d`
（也无需假设 `T` 二叉）。这条桥因此是**纯 split 层**的，可直接喂给 `MSCTreeLaw` 的概率层。 -/

/-- `B : Finset (X ⊕ Unit)` 的**真叶集**：`B` 里真 taxon（`Sum.inl x`）的那些 `x`。

去根桥的核心坐标：`T − ρ` 的 split 侧 ⟷ `T` 的 split 侧的**真叶集**。 -/
noncomputable def realLeaves {X : Type} [Fintype X] [DecidableEq X]
    (B : Finset (X ⊕ Unit)) : Finset X :=
  Finset.univ.filter (fun x => Sum.inl x ∈ B)

/-- 真叶集的成员刻画。 -/
theorem mem_realLeaves {X : Type} [Fintype X] [DecidableEq X]
    {B : Finset (X ⊕ Unit)} {x : X} : x ∈ realLeaves B ↔ Sum.inl x ∈ B := by
  simp only [realLeaves, Finset.mem_filter, Finset.mem_univ, true_and]

/-- ★★ **真叶集取回真 taxon 集**：`realLeaves (A.image Sum.inl) = A`。 -/
theorem realLeaves_image_inl {X : Type} [Fintype X] [DecidableEq X] (A : Finset X) :
    realLeaves (A.image Sum.inl) = A := by
  ext x
  rw [mem_realLeaves, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [Sum.inl.injEq] at hxy
    subst hxy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- ★★ **不含 `m` 的集合由它的真叶集决定**：`realLeaves B = C → Sum.inr () ∉ B → B = C.image Sum.inl`。

（`m := Sum.inr ()` 是根叶；`B` 里没有它时，`B` 完全由真叶集还原。） -/
theorem eq_image_inl_of_realLeaves {X : Type} [Fintype X] [DecidableEq X]
    {B : Finset (X ⊕ Unit)} {C : Finset X} (h : realLeaves B = C)
    (hm : Sum.inr () ∉ B) : B = C.image Sum.inl := by
  ext z
  constructor
  · intro hz
    cases z with
    | inl x =>
        exact Finset.mem_image.mpr ⟨x, h ▸ mem_realLeaves.mpr hz, rfl⟩
    | inr u =>
        cases u
        exact absurd hz hm
  · rintro hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    rw [← mem_realLeaves, h]
    exact hx

/-- ★★ **另一侧的真叶集是补集**：`realLeaves s.sideA = A → realLeaves s.sideB = Aᶜ`。 -/
theorem realLeaves_sideB {X : Type} [Fintype X] [DecidableEq X]
    (s : Split (X ⊕ Unit)) (A : Finset X) (h : realLeaves s.sideA = A) :
    realLeaves s.sideB = Aᶜ := by
  have hx : ∀ x : X, Sum.inl x ∈ s.sideA ↔ x ∈ A := fun x => by
    rw [← mem_realLeaves, h]
  ext x
  rw [mem_realLeaves, Split.sideB_eq_compl, Finset.mem_compl, Finset.mem_compl]
  exact not_congr (hx x)

/-- ★★ **另一侧的真叶集是补集**（`sideB` 版）：`realLeaves s.sideB = A → realLeaves s.sideA = Aᶜ`。 -/
theorem realLeaves_sideA {X : Type} [Fintype X] [DecidableEq X]
    (s : Split (X ⊕ Unit)) (A : Finset X) (h : realLeaves s.sideB = A) :
    realLeaves s.sideA = Aᶜ := by
  have h' : realLeaves s.swap.sideA = A := by rwa [Split.swap_sideA]
  have h2 := realLeaves_sideB s.swap A h'
  rwa [Split.swap_sideB] at h2

/-- **`A` 是 `U` 去根后的 clan**（Semple–Steel 意义；`U` 是「有根树 `T` 补一个根叶 `m`」）。

`A` 只需是**某条边某一侧的真叶集** —— 不构造 `T − ρ`（理由见本节开头）。 -/
def IsClanMinusRoot {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (A : Finset X) : Prop :=
  ∃ s : Split (X ⊕ Unit), U.IsSplitOf s ∧ (realLeaves s.sideA = A ∨ realLeaves s.sideB = A)

/-- ★★ **单边引理**：`sideA` 的真叶集是 `A` ⟹ `A` 或 `Aᶜ` 是 `U` 的 clade。 -/
theorem isClade_or_isClade_compl {X : Type} [Fintype X] [DecidableEq X]
    {U : Cladogram (X ⊕ Unit)} {s : Split (X ⊕ Unit)} (hs : U.IsSplitOf s) {A : Finset X}
    (h : realLeaves s.sideA = A) :
    U.IsClade (A.image Sum.inl) ∨ U.IsClade ((Aᶜ).image Sum.inl) := by
  have hB : realLeaves s.sideB = Aᶜ := realLeaves_sideB s A h
  by_cases hm : Sum.inr () ∈ s.sideA
  · -- `m` 在 `sideA` 侧 ⟹ `sideB` 侧全是真 taxon，且其真叶集是 `Aᶜ`
    right
    have hnot : Sum.inr () ∉ s.sideB := by
      intro hmem
      rw [Split.sideB_eq_compl, Finset.mem_compl] at hmem
      exact hmem hm
    exact ⟨s.swap, U.isSplitOf_swap hs, by
      rw [Split.swap_sideA]
      exact eq_image_inl_of_realLeaves hB hnot⟩
  · -- `m` 不在 `sideA` 侧 ⟹ `sideA` 侧全是真 taxon，且其真叶集是 `A`
    left
    exact ⟨s, hs, eq_image_inl_of_realLeaves h hm⟩

/-- ★★★ **ZDS2011 Lemma 6.1**（`…arXiv1101.1311.md:991-992` 逐字）：
`A` 是 `T − ρ` 的 clan **⟺** `A` 是 `T` 的 clade **或** `X − A` 是 `T` 的 clade。

`U : Cladogram (X ⊕ Unit)` 是「有根树 `T` 补一个根叶 `m = Sum.inr ()`」得到的无根树。
**无需** `T` 二叉、**无需** `A` 非空或真 —— 等式对所有 `A : Finset X` 成立
（`A = ∅` 与 `A = X` 两个端点由 `m` 的悬挂边自动配对，见 §9 开头的 `d = 3` 说明）。 -/
theorem isClanMinusRoot_iff {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (A : Finset X) :
    IsClanMinusRoot U A ↔
      U.IsClade (A.image Sum.inl) ∨ U.IsClade ((Aᶜ).image Sum.inl) := by
  constructor
  · rintro ⟨s, hs, h | h⟩
    · exact isClade_or_isClade_compl hs h
    · have h' : realLeaves s.swap.sideA = A := by rwa [Split.swap_sideA]
      exact isClade_or_isClade_compl (U.isSplitOf_swap hs) h'
  · rintro (h | h)
    · obtain ⟨s, hs, hside⟩ := h
      exact ⟨s, hs, Or.inl (by rw [hside, realLeaves_image_inl])⟩
    · obtain ⟨s, hs, hside⟩ := h
      refine ⟨s, hs, Or.inr ?_⟩
      rw [realLeaves_sideB s (Aᶜ) (by rw [hside, realLeaves_image_inl]), compl_compl]

/-- ★★ **文献 `:979-980` 的那句推论**：有根树的**每个** clade 都是去根树的 clan。 -/
theorem isClanMinusRoot_of_isClade {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) {A : Finset X} (h : U.IsClade (A.image Sum.inl)) :
    IsClanMinusRoot U A :=
  (isClanMinusRoot_iff U A).mpr (Or.inl h)

/-- ★★ **`∨` 是多余的**：`IsClanMinusRoot` 可以只用 `sideA` 写（用 `s.swap` 换向）。
这条让下游（概率层）**不必**对两侧各写一次。 -/
theorem isClanMinusRoot_iff_exists {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (A : Finset X) :
    IsClanMinusRoot U A ↔ ∃ s : Split (X ⊕ Unit), U.IsSplitOf s ∧ realLeaves s.sideA = A := by
  constructor
  · rintro ⟨s, hs, h | h⟩
    · exact ⟨s, hs, h⟩
    · exact ⟨s.swap, U.isSplitOf_swap hs, by rwa [Split.swap_sideA]⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, Or.inl h⟩

/-- ★★ **真叶集是互补的**（**无条件**版）：`realLeaves s.sideB = (realLeaves s.sideA)ᶜ`。

这是去根桥的「`A` 与 `X − A` 只是同一条 split 的两侧」在**真叶集**层的化身。 -/
theorem realLeaves_sideB_compl {X : Type} [Fintype X] [DecidableEq X]
    (s : Split (X ⊕ Unit)) : realLeaves s.sideB = (realLeaves s.sideA)ᶜ :=
  realLeaves_sideB s _ rfl

/-- ★★ **`IsClanMinusRoot` 对补集封闭**：去根树里 `A | X−A` 与 `(X−A) | A` 是**同一条** split，
故 `A` 是 clan ⟺ `X − A` 是 clan（与 `isClade_compl` 平行的容器版）。 -/
theorem isClanMinusRoot_compl {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (A : Finset X) :
    IsClanMinusRoot U A ↔ IsClanMinusRoot U Aᶜ := by
  rw [isClanMinusRoot_iff, isClanMinusRoot_iff, compl_compl, or_comm]

/-! ### 9.1 端点行为（**诚实登记，不夸大**）

本节的 `IsClanMinusRoot` 允许 `A = ∅` 与 `A = univ`（见证都是 `m` 的**悬挂边**：
两侧分别是 `{m}` 与 `univ.image Sum.inl`），而**学界定义**的 clan 要求**非空真子集**。因此：

* 文献 Lemma 6.1 的**逐字**版本应把 `A` 限在**非空真子集**上（例如 `A.Nonempty` ＋ `A.card < n`）；
* ★★ `isClanMinusRoot_iff` 是它在**所有** `A` 上的自然延拓 —— 两侧记账一致，**等式仍成立**
  （端点不是反例：`A = ∅` 时 RHS 的 `X − A = X` 恰是有根树的 clade，两边同为真）；
* 下游的两条缺口（`YHKClanLawGap` 要求 `A.Nonempty` ＋ `A.card < n`；`TwoClanLawGap` 要求
  `A`、`B` 非空且 `A.card + B.card ≤ n`）**自动落在合法范围内** ⇒ 端点不影响任何下游用法。
-/

/-! ### 9.2 对两条缺口 docstring 的**状态更新**（W27 派单 T4 泳道 d）

`YHKClanLawGap`（§6，`:924`）与 `TwoClanLawGap`（§6，`:977`）的 docstring 里列了四件具名器材，
其中**第 ② 件（`rootedToCladogram` 去根载体桥 ＋ `IsClade` 对应）已由本节交付**：

| docstring 的条目 | 现状 |
| --- | --- |
| ②(a) split 层的**数学内容**（Lemma 6.1） | ✅ **本节**：`realLeaves` ＋ `IsClanMinusRoot` ＋ ★★★ `isClanMinusRoot_iff`（＝ Lemma 6.1）。**不构造 `T − ρ`** 对 (a) 是正当的设计选择 —— 抑制 ρ 产生的新 split，其两侧**恰是**被并两条边各自一侧的真叶集 |
| ②(b) **载体映射** `rootedToCladogram`（`Cladogram (X ⊕ Unit) → Cladogram X`） | ❌ **未交**。★ **更正**：本节首版把 ② 整体记成 ✅ 是 **overclaim**。缺口要的 `tree : Ω → Cladogram (Fin n)` 与本节全部器材所在的 `Cladogram (Fin n ⊕ Unit)` 之间**必须有这台映射**；对 (a) 可省，对**填缺口的 `tree` 槽不可省** |
| ③ Lemma 6.1 的**概率层** | ✅ 代数侧已有 `clanProb_eq_inclusionExclusion`（`:404`）；❌ **概率**侧仍缺（见下） |
| ① 一般 `n` 的 YHK 权重函数 | ❌ 仍缺 |
| ④ (EP) 的群作用实现 | ❌ 仍缺（`TwoClanLawGap` 的 `a+b<n` 支还要 Theorem 6.3(ii) 的三事件分解） |

★ **两条缺口仍未收口**，剩余缺件（**具名、可执行**）：

1. **`rootedCladeProb`**：一般 `n` 的有根 YHK 律下 `P(A 是 clade) = pn n A.card`
   （文献 Lemma 4.2，`:294-317`）。需要一件**一般 `n` 的有根拓扑律**
   （库内 `MSCTreeLaw` 只到**无根**、且只有 `Fin 4` 实例；`Coalescent.mergePairsFinset` 只给
   **一步合并均匀**，不给整条拓扑律）。
2. **`rootedCladePairProb`**：`P(A 与 X−A 同为 clade) = pnHatExh n A.card`（Lemma 4.3，`:369-385`）。
3. 前两条 ＋ ★★★ `isClanMinusRoot_iff` ＋ `clanProb_eq_inclusionExclusion`
   ⇒ `YHKClanLawGap` **一步装配**（Lemma 6.2 的证明在文献 `:1038-1044` 正是这么做的）。
4. `TwoClanLawGap` 另需 Theorem 4.5 的**六情形级联概率层**（`pnPair`，`:452-475`）
   ＋ Theorem 6.3(ii) 的三事件分解（`:1112-1145`）。

⇒ 本节把「**形状侧的数学内容**」做完（Lemma 6.1），但**未**做完「形状侧的**载体**」：缺 `rootedToCladogram`。
故缺口剩下的是 **① 载体映射 ＋ ② 概率层**（有根 YHK 律 ＋ `M1`/`M2`），**不是**「纯粹概率层」—— 首版这句也是 overclaim，一并更正。 -/

/-! ### 9.3 ★ 接手路线（W27 收档时由泳道 d 给出，**代价从小到大**；不是承诺，是验证过的路线）

**第 1 步：`rootedToCladogram`（估 2–4 h；最便宜的路线**不是**图手术）**

用 `Cladogram.ofCompatibleSplits`（`CladogramBuild.lean:204`）造目标树，而不是抑制图：

```
fam := (U.nontrivialSplits).image splitRestrict        -- U : Cladogram (X ⊕ Unit)
splitRestrict s : Split X                              -- 两侧取 (realLeaves s.sideA)ᶜ 与 realLeaves s.sideA
```

需要三件（库内都**没有**，得新写）：
1. **`Split X` 的构造器**：从「两侧非空、不交、并为全集」造 `Split X`（`grep` 未找到现成的）；
2. **`Split.Compatible` 在限制到真叶集下保持**（有 `A ∪ B = univ` 则 `realA ∪ realB = X`，可证）；
3. **限制与 `swap` 交换**。
拿到后 `isSplitOf_ofCompatibleSplits`（`CladogramBuild.lean:204`）直接给刻画 ⇒ 与
★★★ `isClanMinusRoot_iff` 对接，得到 `(rootedToCladogram U).IsClade A ↔ IsClanMinusRoot U A`。

**第 2 步：`M1 rootedCladeProb`** —— 一般 `n` **有根** YHK 律下 `P(A clade) = pn n A.card`（文献 Lemma 4.2，`:294-317`）。
前提是一件**库内不存在**的东西：一般 `n` 的**有根拓扑律**（`MSCTreeLaw` 只装无根、非空实例仅 `yhkLawFour`；
`Coalescent.mergePairsFinset` 只给一步合并均匀；`KingmanLaw` 是测度论连续时间）。

**第 3 步：`M2 rootedCladePairProb`** —— `P(A 与 X−A 同为 clade) = pnHatExh n A.card`（Lemma 4.3，`:369-385`）。

**装配**：1+2+3 ⇒ `YHKClanLawGap` ＝ `isClanMinusRoot_iff` ＋ `clanProb_eq_inclusionExclusion`（`:404`，签名
`{n a} (h1 : 1 ≤ a) (ha : a < n) : clanProb n a = pn n a + pn n (n-a) - pnHatExh n a`，**合型、不是卡点**）
一步收口（文献 Lemma 6.2 的证明 `:1038-1044` 正是这个包含-排除）。
`TwoClanLawGap` 再加 Theorem 4.5 六情形级联概率层（`:452-475`）＋ Thm 6.3(ii) 三事件（`:1112-1145`）。

★ **反面记录（免得下一个人重走）**：把假设写成 `YHKClanLawModel : Prop` 再证 `…Model → YHKClanLawGap`
**逃不掉** —— 若 `Model` 陈述在 `Cladogram (Fin n)` 上带 clan 等式，它**就是** `YHKClanLawGap`（同义反复）；
若陈述在 `Cladogram (Fin n ⊕ Unit)` 上带 `IsClanMinusRoot`，则 `…Model → YHKClanLawGap` **恰好就是**被卡住的那一步。
-/


/-! ## 10. 去根载体映射 `rootedToCladogram`（缺口 ②(b) 的本体）

### 10.0 这一节补的是什么

**旧形态**（§9 结束时）：Lemma 6.1 的**数学内容**已在 split 层做完
（★★★ `isClanMinusRoot_iff`），但 `Cladogram (X ⊕ Unit)` 上的器材**没有**通往
`Cladogram X` 的**载体**；`YHKClanLawGap`（§6，`Phylo/Stat/ReciprocalMonophyly.lean:924`）
的 `tree` 槽要求 `Cladogram (Fin n)`，故 ②(b) 空着（§9.2 表里的「❌ 未交」）。

**新形态**（本节交付）：

* ★★★ `rootedToCladogram`（§10.3）：`Cladogram (X ⊕ Unit) → Cladogram X`，
  按 ★★★ `Cladogram.ofCompatibleSplits`（`Phylo/CladogramBuild.lean:188`）造树；
* ★★★ `isSplitOf_rootedToCladogram`（§10.3）：它的 split 系统**完全刻画**（族 ∪ 平凡）；
* ★★★ `isClade_rootedToCladogram_iff_of_nonempty`（§10.3）：
  `(rootedToCladogram U h3).IsClade A ↔ IsClanMinusRoot U A`（`A` 非空真）；
* ★★★ **两端反例**（§10.4）：**无条件**形态 `… IsClade A ↔ IsClanMinusRoot U A`
  在 `A = ∅` / `A = univ` **为假** —— 这是定理，不是口径。

**文献**：ZDS2011 **Lemma 6.1**
（`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md:991-992`，
行号沿用 §9 开头的记录 —— `references/` 不随 worktree 分发，本节无法独立复核）＋
其上一句「suppress the root」的推论（同文件 `:977-981`）；clan 的定义（同文件 `:985-988`）。

**理由**：缺口 ② 的两半 —— (a) 数学内容（§9 已交）、(b) **载体**（本节）—— 缺一不可：
`YHKClanLawGap` 的 `tree` 槽在 `Cladogram (Fin n)` 上，而全部裁决器材在
`Cladogram (Fin n ⊕ Unit)` 上。本节**不做**图上的顶点抑制：抑制 `ρ` 的几何后果**只**落在
split 系统上，而 ★★★ `Cladogram.isSplitOf_ofCompatibleSplits`（`Phylo/CladogramBuild.lean:200`）
给出「族 ∪ 平凡」的**完整**刻画 —— 这使「搬 split 系统」成为**等价且更短**的做法
（即 §9.3 第 1 步写下的路线）。 -/

/-! ### 10.1 真叶集：基数、非空、单调、不交、`swap` 交换 -/

/-- ★ **真叶集的基数只比原基数少至多 `1`**（少掉的至多一个：根叶 `m = Sum.inr ()`）。

`Y ⊆ (realLeaves Y).image Sum.inl ∪ {m}`，故 `Y.card ≤ (realLeaves Y).card + 1`。 -/
theorem card_le_realLeaves_add_one {X : Type} [Fintype X] [DecidableEq X]
    (Y : Finset (X ⊕ Unit)) : Y.card ≤ (realLeaves Y).card + 1 := by
  classical
  have hsub : Y ⊆ (realLeaves Y).image (Sum.inl : X → X ⊕ Unit) ∪ ({Sum.inr ()} : Finset (X ⊕ Unit)) := by
    intro z hz
    cases z with
    | inl x =>
        exact Finset.mem_union_left _
          (Finset.mem_image_of_mem (Sum.inl : X → X ⊕ Unit) (mem_realLeaves.mpr hz))
    | inr u => cases u; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have h1 : Y.card ≤
      ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit) ∪
        ({Sum.inr ()} : Finset (X ⊕ Unit))).card :=
    Finset.card_le_card hsub
  have h2 : ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit) ∪
      ({Sum.inr ()} : Finset (X ⊕ Unit))).card ≤ (realLeaves Y).card + 1 := by
    have h3 : ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit) ∪
        ({Sum.inr ()} : Finset (X ⊕ Unit))).card
        ≤ ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit)).card + 1 := by
      have h := Finset.card_union_le ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit))
        ({Sum.inr ()} : Finset (X ⊕ Unit))
      rw [Finset.card_singleton] at h
      exact h
    have h4 : ((realLeaves Y).image (Sum.inl : X → X ⊕ Unit)).card ≤ (realLeaves Y).card :=
      Finset.card_image_le
    omega
  omega

/-- ★★ **非平凡 split 的两侧真叶集都非空**。

每侧有 `≥ 2` 个叶，其中至多一个是根叶 `m`（`card_le_realLeaves_add_one`），故该侧真叶集 `≥ 1`。
这是 `rootedSplits` 能定义、也是 `ofCompatibleSplits` 的 `hnt` 槽能填上的**唯一**依据。 -/
theorem realLeaves_nonempty_of_not_isTrivial {X : Type} [Fintype X] [DecidableEq X]
    {s : Split (X ⊕ Unit)} (hs : ¬ s.IsTrivial) :
    (realLeaves s.sideA).Nonempty ∧ (realLeaves s.sideA)ᶜ.Nonempty := by
  have hnt := (Split.not_isTrivial_iff s).mp hs
  have hA : 0 < (realLeaves s.sideA).card := by
    have h := card_le_realLeaves_add_one s.sideA
    omega
  have hB : 0 < (realLeaves s.sideB).card := by
    have h := card_le_realLeaves_add_one s.sideB
    omega
  rw [realLeaves_sideB_compl] at hB
  exact ⟨Finset.card_pos.mp hA, Finset.card_pos.mp hB⟩

/-- 真叶集**单调**。 -/
theorem realLeaves_subset {X : Type} [Fintype X] [DecidableEq X] {Y Z : Finset (X ⊕ Unit)}
    (h : Y ⊆ Z) : realLeaves Y ⊆ realLeaves Z := by
  intro x hx
  rw [mem_realLeaves] at hx ⊢
  exact h hx

/-- 真叶集**保持不交**。 -/
theorem realLeaves_disjoint {X : Type} [Fintype X] [DecidableEq X] {Y Z : Finset (X ⊕ Unit)}
    (h : Disjoint Y Z) : Disjoint (realLeaves Y) (realLeaves Z) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hy
  rw [mem_realLeaves] at hx hy
  exact h hx hy

/-- 真叶集**把补集变补集**：`realLeaves Bᶜ = (realLeaves B)ᶜ`（因 `realLeaves` 只问 `Sum.inl x`）。 -/
theorem realLeaves_compl {X : Type} [Fintype X] [DecidableEq X] (B : Finset (X ⊕ Unit)) :
    realLeaves Bᶜ = (realLeaves B)ᶜ := by
  ext x
  rw [mem_realLeaves, Finset.mem_compl, Finset.mem_compl, mem_realLeaves]

/-- 根叶单点集的真叶集：`{inl x} ↦ {x}`。 -/
theorem realLeaves_singleton_inl {X : Type} [Fintype X] [DecidableEq X] (x : X) :
    realLeaves ({Sum.inl x} : Finset (X ⊕ Unit)) = {x} := by
  rw [← Finset.image_singleton (f := Sum.inl) (a := x), realLeaves_image_inl]

/-- 根叶本身的单点集：真叶集为空。 -/
theorem realLeaves_singleton_inr {X : Type} [Fintype X] [DecidableEq X] :
    realLeaves ({Sum.inr ()} : Finset (X ⊕ Unit)) = ∅ := by
  ext x
  simp [mem_realLeaves]

/-- `{inl x}ᶜ` 的真叶集是 `{x}ᶜ`。 -/
theorem realLeaves_compl_singleton_inl {X : Type} [Fintype X] [DecidableEq X] (x : X) :
    realLeaves (({Sum.inl x} : Finset (X ⊕ Unit))ᶜ) = {x}ᶜ := by
  rw [realLeaves_compl, realLeaves_singleton_inl]

/-- `{m}ᶜ` 的真叶集是全集（去根后 `m` 不再是 taxon）。 -/
theorem realLeaves_compl_singleton_inr {X : Type} [Fintype X] [DecidableEq X] :
    realLeaves (({Sum.inr ()} : Finset (X ⊕ Unit))ᶜ) = (Finset.univ : Finset X) := by
  rw [realLeaves_compl, realLeaves_singleton_inr, Finset.compl_empty]

/-- ★★ **平凡性对 `swap` 不变**（`IsTrivial` 只问「某一侧是单点」，两侧对称）。 -/
theorem isTrivial_swap {X : Type} [Fintype X] [DecidableEq X] (s : Split X) :
    s.swap.IsTrivial ↔ s.IsTrivial := by
  rw [Split.isTrivial_iff_card, Split.isTrivial_iff_card, Split.swap_sideA,
    Split.swap_sideB, or_comm]

/-- ★★ **限制与 `swap` 交换**：一侧换向后限制 = 限制后换向。 -/
theorem splitOf_realLeaves_sideB_eq_swap {X : Type} [Fintype X] [DecidableEq X]
    (s : Split (X ⊕ Unit))
    (h1 : (realLeaves s.sideA).Nonempty) (h2 : (realLeaves s.sideA)ᶜ.Nonempty)
    (h1' : (realLeaves s.sideB).Nonempty) (h2' : (realLeaves s.sideB)ᶜ.Nonempty) :
    splitOf (realLeaves s.sideB) h1' h2' = (splitOf (realLeaves s.sideA) h1 h2).swap := by
  refine Split.ext_sideA ?_
  rw [splitOf_sideA, Split.swap_sideA, splitOf_sideB, realLeaves_sideB_compl]

/-- ★★★ **相容性在「限制到真叶集」下保持**。

`Split.Compatible s t` 的四个「交为空」由 `realLeaves` 逐一接住（`realLeaves` 是 `Finset` 的滤子，
故把 `∩` 送到 `∩`）；第四支（`并 = univ`）同样逐点传递。这是 `hcomp` 槽的**全部**内容。 -/
theorem sidesCompatible_realLeaves {X : Type} [Fintype X] [DecidableEq X]
    {s t : Split (X ⊕ Unit)} (h : Split.Compatible s t) :
    SidesCompatible (realLeaves s.sideA) (realLeaves t.sideA) := by
  rcases Split.sidesCompatible_of_compatible h with h1 | h1 | h1 | h1
  · exact Or.inl (realLeaves_subset h1)
  · exact Or.inr (Or.inl (realLeaves_subset h1))
  · exact Or.inr (Or.inr (Or.inl (realLeaves_disjoint h1)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    ext x
    refine ⟨fun _ => Finset.mem_univ x, fun _ => ?_⟩
    have hmem : Sum.inl x ∈ s.sideA ∪ t.sideA := by simp [h1]
    rcases Finset.mem_union.mp hmem with hx | hx
    · exact Finset.mem_union_left _ (mem_realLeaves.mpr hx)
    · exact Finset.mem_union_right _ (mem_realLeaves.mpr hx)

/-! ### 10.2 族 `rootedSplits`：`U` 的每条非平凡边限制到真 taxon -/

/-- `U.nontrivialSplits` 的成员刻画。 -/
theorem mem_nontrivialSplits {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram X) (s : Split X) :
    s ∈ Cladogram.nontrivialSplits U ↔ U.IsSplitOf s ∧ ¬ s.IsTrivial := by
  classical
  rw [Cladogram.nontrivialSplits, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- `U.nontrivialSplits` 对 `swap` 封闭（每条边的两个朝向都在）。 -/
theorem mem_nontrivialSplits_swap {X : Type} [Fintype X] [DecidableEq X]
    {U : Cladogram (X ⊕ Unit)} {s : Split (X ⊕ Unit)} (hs : s ∈ U.nontrivialSplits) :
    s.swap ∈ U.nontrivialSplits := by
  classical
  rw [mem_nontrivialSplits] at hs ⊢
  exact ⟨U.isSplitOf_swap hs.1, fun h => hs.2 ((isTrivial_swap s).mp h)⟩

/-- ★★ **去根树的 split 族**：`U` 每条**非平凡**边的真叶集侧，**滤掉**限制后退化成平凡的。

退化的是 `sideA = {m, x}` 型：真叶集只剩单点 `{x}`，而单点 split 在任何树里都由叶边自动展示
（`Cladogram.isSplitOf_ofCompatibleSplits` 的「平凡」那一支），故**不放进族**（否则 `hnt` 槽会失败）。

用**存在式**而不用 `Finset.image`：`Finset.image` 的像里两个证明项不同的 `splitOf` 无法比对，
存在式把「族成员 = 某个 `splitOf ⋯`」这条**等式**直接交到手上。 -/
noncomputable def rootedSplits {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) : Finset (Split X) := by
  classical
  exact Finset.univ.filter (fun t : Split X =>
    ∃ (u : Split (X ⊕ Unit)) (h1 : (realLeaves u.sideA).Nonempty)
      (h2 : (realLeaves u.sideA)ᶜ.Nonempty),
      u ∈ U.nontrivialSplits ∧ ¬ (splitOf (realLeaves u.sideA) h1 h2).IsTrivial ∧
        splitOf (realLeaves u.sideA) h1 h2 = t)

/-- `rootedSplits` 的成员刻画。 -/
theorem mem_rootedSplits {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (t : Split X) :
    t ∈ rootedSplits U ↔
      ∃ (u : Split (X ⊕ Unit)) (h1 : (realLeaves u.sideA).Nonempty)
        (h2 : (realLeaves u.sideA)ᶜ.Nonempty),
        u ∈ U.nontrivialSplits ∧ ¬ (splitOf (realLeaves u.sideA) h1 h2).IsTrivial ∧
          splitOf (realLeaves u.sideA) h1 h2 = t := by
  classical
  rw [rootedSplits, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- ★★ `hcomp` 槽：`rootedSplits U` 两两相容。 -/
theorem rootedSplits_compatible {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) :
    ∀ s ∈ rootedSplits U, ∀ t ∈ rootedSplits U, Split.Compatible s t := by
  intro s hs t ht
  obtain ⟨u, h1, h2, hu, -, heq⟩ := (mem_rootedSplits U s).mp hs
  obtain ⟨v, h1', h2', hv, -, heq'⟩ := (mem_rootedSplits U t).mp ht
  rw [← heq, ← heq', Split.compatible_iff_sides, splitOf_sideA, splitOf_sideA]
  exact sidesCompatible_realLeaves
    (pairwiseCompatible U u ((mem_nontrivialSplits U u).mp hu).1 v
      ((mem_nontrivialSplits U v).mp hv).1)

/-- ★★ `hnt` 槽：`rootedSplits U` 的成员两侧都 `≥ 2`。 -/
theorem rootedSplits_notTrivial {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) :
    ∀ s ∈ rootedSplits U, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  intro s hs
  obtain ⟨u, h1, h2, -, hntriv, heq⟩ := (mem_rootedSplits U s).mp hs
  rw [← heq]
  exact (Split.not_isTrivial_iff (splitOf (realLeaves u.sideA) h1 h2)).mp hntriv

/-- ★★ `hswap` 槽：`rootedSplits U` 对 `swap` 封闭。 -/
theorem rootedSplits_swap {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) :
    ∀ s ∈ rootedSplits U, s.swap ∈ rootedSplits U := by
  intro s hs
  obtain ⟨u, h1, h2, hu, hntriv, heq⟩ := (mem_rootedSplits U s).mp hs
  have h1' : (realLeaves u.sideB).Nonempty := by rw [realLeaves_sideB_compl]; exact h2
  have h2' : (realLeaves u.sideB)ᶜ.Nonempty := by
    rw [realLeaves_sideB_compl, compl_compl]; exact h1
  have hsw := splitOf_realLeaves_sideB_eq_swap u h1 h2 h1' h2'
  refine (mem_rootedSplits U s.swap).mpr ⟨u.swap, h1', h2', ?_, ?_, ?_⟩
  · exact mem_nontrivialSplits_swap hu
  · show ¬ (splitOf (realLeaves u.sideB) h1' h2').IsTrivial
    rw [hsw, isTrivial_swap]
    exact hntriv
  · show splitOf (realLeaves u.sideB) h1' h2' = s.swap
    rw [hsw, heq]

/-! ### 10.3 载体映射本体与刻画 -/

/-- ★★★ **去根载体映射**（缺口 ②(b)）：`Cladogram (X ⊕ Unit) → Cladogram X`。

`U` 是「有根树 `T` 加一片名为 `root` 的叶子 `m = Sum.inr ()`」；本映射把它送去根树 `T − ρ`。
做法是**只搬 split 系统**（不做图上的顶点抑制）：族取 `rootedSplits`（`U` 每条非平凡边的真叶集侧），
再用 ★★★ `Cladogram.ofCompatibleSplits`（`Phylo/CladogramBuild.lean:188`）造树，
其 split 系统由 ★★★ `Cladogram.isSplitOf_ofCompatibleSplits`（同文件 `:200`）**完全刻画**。

`h3 : 3 ≤ |X|` 是 `ofCompatibleSplits` 的**固有**前提（`Phylo/CladogramBuild.lean:193`，
`toCladogram` 的根非退化条件），不是本节额外加的假设。 -/
noncomputable def rootedToCladogram {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (h3 : 3 ≤ Fintype.card X) : Cladogram X :=
  Cladogram.ofCompatibleSplits (rootedSplits U)
    (Classical.choice (Fintype.card_pos_iff.mp (by omega)))
    (rootedSplits_compatible U) (rootedSplits_notTrivial U) (rootedSplits_swap U) h3

/-- ★★★ **`rootedToCladogram` 的 split 系统刻画**：恰为「族 ∪ 平凡 split」。 -/
theorem isSplitOf_rootedToCladogram {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (h3 : 3 ≤ Fintype.card X) (t : Split X) :
    (rootedToCladogram U h3).IsSplitOf t ↔
      t ∈ rootedSplits U ∨ (∃ x : X, t.sideA = {x}) ∨ (∃ x : X, t.sideA = {x}ᶜ) :=
  Cladogram.isSplitOf_ofCompatibleSplits (rootedSplits U)
    (Classical.choice (Fintype.card_pos_iff.mp (by omega)))
    (rootedSplits_compatible U) (rootedSplits_notTrivial U) (rootedSplits_swap U) h3 t

/-- ★★ **单边方向**：`realLeaves u.sideA = A` 且 `u` 是 `U` 的一条边 ⟹ `A` 是 `T − ρ` 的 clan。 -/
theorem isClade_of_realLeaves_sideA {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (h3 : 3 ≤ Fintype.card X) {u : Split (X ⊕ Unit)}
    (hu : U.IsSplitOf u) {A : Finset X} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (h : realLeaves u.sideA = A) : (rootedToCladogram U h3).IsClade A := by
  classical
  by_cases htriv : u.IsTrivial
  · obtain ⟨z, hz⟩ | ⟨z, hz⟩ := htriv
    · cases z with
      | inl x =>
          have hAx : A = {x} := by rw [← h, hz, realLeaves_singleton_inl]
          refine ⟨splitOf A hA hAc, ?_, by rw [splitOf_sideA]⟩
          rw [isSplitOf_rootedToCladogram]
          exact Or.inr (Or.inl ⟨x, by rw [splitOf_sideA, hAx]⟩)
      | inr u0 =>
          cases u0
          rw [hz, realLeaves_singleton_inr] at h
          rw [← h] at hA
          exact absurd hA (by simp)
    · cases z with
      | inl x =>
          have hAx : A = {x}ᶜ := by rw [← h, hz, realLeaves_compl_singleton_inl]
          refine ⟨splitOf A hA hAc, ?_, by rw [splitOf_sideA]⟩
          rw [isSplitOf_rootedToCladogram]
          exact Or.inr (Or.inr ⟨x, by rw [splitOf_sideA, hAx]⟩)
      | inr u0 =>
          cases u0
          rw [hz, realLeaves_compl_singleton_inr] at h
          rw [← h] at hAc
          exact absurd hAc (by simp)
  · obtain ⟨h1, h2⟩ := realLeaves_nonempty_of_not_isTrivial htriv
    refine ⟨splitOf (realLeaves u.sideA) h1 h2, ?_, by rw [splitOf_sideA]; exact h⟩
    rw [isSplitOf_rootedToCladogram]
    by_cases hT : (splitOf (realLeaves u.sideA) h1 h2).IsTrivial
    · exact Or.inr hT
    · exact Or.inl ((mem_rootedSplits U _).mpr
        ⟨u, h1, h2, (mem_nontrivialSplits U u).mpr ⟨hu, htriv⟩, hT, rfl⟩)

/-- ★★★ **去根载体映射与 clan 判据一致**（缺口 ②(b) 的本体）：

`A`（非空、真）是 `T − ρ` 的 clan **⟺** `A` 是 `rootedToCladogram U` 的一条边的一侧。

配合 ★★★ `isClanMinusRoot_iff`（`Phylo/Stat/ReciprocalMonophyly.lean:1901`）即得
ZDS2011 **Lemma 6.1**（`references/md/ZhuDegnanSteel2011_CladesClansReciprocalMonophylyarXiv1101.1311.md:991-992`；
行号沿用本文件 §9 开头的记录 —— `references/` 不随 worktree 分发，本节无法独立复核）
的**载体形态**。

⚠️ **这是「端点已排除」的真形态，不是无条件版**（故定理名带 `_of_nonempty`）：题目给的
**无条件**形态 `(rootedToCladogram U).IsClade A ↔ IsClanMinusRoot U A` 在 `A = ∅` 与
`A = univ` **为假**，§10.4 已把两端**证成反例定理**（★★★ `isClanMinusRoot_empty`、
★★★ `isClanMinusRoot_univ`、★★★ `not_isClade_iff_isClanMinusRoot_empty`）：`IsClade` 对任何树
都不接受空集与全集（`Split` 的两侧由 `KPartition.nonempty`，`Phylo/Split.lean:161`，保证非空；
库内旧有的 `not_isClade_empty`，本文件 `:1060`），而 `IsClanMinusRoot` 接受（`m` 的悬挂边，§9.1）。

⇒ 两个前提是**必需**的（不是为避免困难的削弱）：下游 `YHKClanLawGap`（§6，`:924`）要求
`A.Nonempty` ＋ `A.card < n`、`TwoClanLawGap`（§6，`:977`）要求两侧非空且 `A.card + B.card ≤ n`，
本条的两条前提**落在下游合法域内**。 -/
theorem isClade_rootedToCladogram_iff_of_nonempty {X : Type} [Fintype X] [DecidableEq X]
    (U : Cladogram (X ⊕ Unit)) (h3 : 3 ≤ Fintype.card X) {A : Finset X}
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (rootedToCladogram U h3).IsClade A ↔ IsClanMinusRoot U A := by
  classical
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases (isSplitOf_rootedToCladogram U h3 t).mp ht with hfam | ⟨x, hx⟩ | ⟨x, hx⟩
    · obtain ⟨u, h1, h2, hu, -, heq⟩ := (mem_rootedSplits U t).mp hfam
      exact ⟨u, ((mem_nontrivialSplits U u).mp hu).1, Or.inl (by rw [← heq, splitOf_sideA])⟩
    · have hntsum : Nontrivial (X ⊕ Unit) := ⟨Sum.inl x, Sum.inr (), by simp⟩
      obtain ⟨s', hs', hs'A⟩ := Cladogram.exists_isSplitOf_singleton U (Sum.inl x)
      exact ⟨s', hs', Or.inl (by rw [hs'A, realLeaves_singleton_inl, hx])⟩
    · have hntsum : Nontrivial (X ⊕ Unit) := ⟨Sum.inl x, Sum.inr (), by simp⟩
      obtain ⟨s', hs', hs'A⟩ := Cladogram.exists_isSplitOf_singleton U (Sum.inl x)
      exact ⟨s', hs', Or.inr (by
        rw [realLeaves_sideB_compl, hs'A, realLeaves_singleton_inl, hx])⟩
  · rintro ⟨u, hu, h | h⟩
    · exact isClade_of_realLeaves_sideA U h3 hu hA hAc h
    · exact isClade_of_realLeaves_sideA U h3 (U.isSplitOf_swap hu) hA hAc
        (by rwa [Split.swap_sideA])


/-! ### 10.4 端点：**无条件**形态为假（hA / hAc 两条前提的**唯一**来源）

题目给的形态 (rootedToCladogram U).IsClade A ↔ IsClanMinusRoot U A 对 A = ∅ 与 A = univ
**为假**，本节把两端的**不对称**逐条证出，使主定理的前提不是「为了好证」而是**必需**。 -/

/-- ★★★ **IsClanMinusRoot U ∅ 为真**：见证是根叶 m 的**悬挂边**（
ealLeaves {m} = ∅）。

⇒ 题目的无条件形态在 A = ∅ 处**左假右真**。 -/
theorem isClanMinusRoot_empty {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : Cladogram (X ⊕ Unit)) : IsClanMinusRoot U (∅ : Finset X) := by
  have hnt : Nontrivial (X ⊕ Unit) :=
    ⟨Sum.inl (Classical.choice ‹Nonempty X›), Sum.inr (), by simp⟩
  obtain ⟨s, hs, hsA⟩ := Cladogram.exists_isSplitOf_singleton U (Sum.inr ())
  exact ⟨s, hs, Or.inl (by rw [hsA, realLeaves_singleton_inr])⟩

/-- ★★★ **IsClanMinusRoot U univ 为真**：同一条悬挂边的**另一侧**（
ealLeaves {m}ᶜ = univ）。 -/
theorem isClanMinusRoot_univ {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : Cladogram (X ⊕ Unit)) : IsClanMinusRoot U (Finset.univ : Finset X) := by
  have hnt : Nontrivial (X ⊕ Unit) :=
    ⟨Sum.inl (Classical.choice ‹Nonempty X›), Sum.inr (), by simp⟩
  obtain ⟨s, hs, hsA⟩ := Cladogram.exists_isSplitOf_singleton U (Sum.inr ())
  refine ⟨s, hs, Or.inr ?_⟩
  rw [realLeaves_sideB_compl, hsA, realLeaves_singleton_inr, Finset.compl_empty]

/-- ★★★ **无条件形态在 A = ∅ 处为假**（左假右真）—— 主定理的两条前提由此成为**必需**。 -/
theorem not_isClade_iff_isClanMinusRoot_empty {X : Type} [Fintype X] [DecidableEq X]
    [Nonempty X] (U : Cladogram (X ⊕ Unit)) (h3 : 3 ≤ Fintype.card X) :
    ¬ ((rootedToCladogram U h3).IsClade (∅ : Finset X) ↔ IsClanMinusRoot U (∅ : Finset X)) := by
  intro h
  exact not_isClade_empty (rootedToCladogram U h3) (h.mpr (isClanMinusRoot_empty U))


/-! ## 11. 一般 `n` 的 YHK 权重层（缺口 ① 的「数据槽 ＋ 权重公式」）

### 11.1 权重公式：**从生成过程推**，不照抄

文献 `:191-221`（§3 *The Yule-Harding-Kingman process*）把 YHK 律定义成**纯生过程**：
「selecting a leaf uniformly at random and 'splitting' it into two new leaves」。
把它在「形状 / 标号」两层算干净，得 `n` 叶**有根**拓扑 `T` 的权

```text
P_rooted(T) = 2^{n−1} / ( n! · ∏_{v 内部} (n_v − 1) ),      n_v = v 下方的叶数（根计入）
```

推导三行（`scripts/msc/yhk_weight_derive.py` 以精确有理数在 `n = 3..7` 上**穷举**核对）：
1. 记 `g(T) = ∏_{v} (n_v − 1)`。根的两棵子树叶数为 `a, n − a` 时 `g(T) = (n−1)·g(T₁)·g(T₂)`，
   故「标号有根树 ↦ 形状」每条纤维的大小恰为 `#hist(T) = (n−1)!/g(T)`；
2. 纯生过程在**形状**层是「以 `1/k` 均匀选叶再分裂」，故形状概率 `= #hist/(n−1)!`；
   按 `(EP)`（`:230-232`）在标号上均匀化，即得上式；
3. 归一化 `∑_T P_rooted(T) = 1` ⟺ `S_n := ∑_T 1/g(T) = n!/2^{n−1}`，
   而按根分裂归纳得 `S_n = (1/(2(n−1)))·∑_{a=1}^{n−1} C(n,a)·S_a·S_{n−a}`；
   与无根律的关系是「对 `2n−3` 个 rootings 求和」（文献 `:996-1006`：
   「the same unrooted tree can arise from different rootings」）。

⚠️ **与旧笔记的区别**：本节的 `∏(n_v − 1)` 与分母里的 `n!` 都是上面三步推出来的，
**不是**照抄的 `2^{n−1}/(n!·∏…)` 型记忆公式；`n = 4` 的对照（§11.2）与库内
`yhkLawFour`（三棵 quartet **等权** `1/3`）逐值一致。

⚠️ **本文件证到哪一步**：`n = 4`、`n = 5` 的**形状表归一化**（§11.2，纯算术）＋
**无根过程历史空间**的精确归一化（§11.3，一般 `n`）。
**未证**：一般 `n` 的「拓扑层归一化」（需要对 `Cladogram (Fin n)` 的有限性/计数，
本库无 `Fintype (Cladogram X)`），以及 Lemma 6.2 的**概率层**。 -/

/-- ★★ **YHK 有根权重** `P_rooted(T) = 2^{n−1}/(n!·g)`（§11.1 的公式），
`g = ∏_{v 内部}(n_v − 1)` 是形状不变量（`n_v` = `v` 下方叶数，根计入）。

本 `def` 只装**公式**（以 `g` 为参数），语义层（「它是 YHK 律」）见 §11.1 的推导与
`scripts/msc/yhk_weight_derive.py` 的穷举核对。 -/
noncomputable def yhkRootWeight (n g : ℕ) : ℝ :=
  (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * (g : ℝ))

/-- 权重非负。 -/
theorem yhkRootWeight_nonneg (n g : ℕ) : 0 ≤ yhkRootWeight n g := by
  unfold yhkRootWeight
  positivity

/-- 权重在 `g > 0` 时严格为正（每个真实形状都有 `g ≥ 1`）。 -/
theorem yhkRootWeight_pos {n g : ℕ} (hg : 0 < g) : 0 < yhkRootWeight n g := by
  unfold yhkRootWeight
  have hg' : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hp : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := by positivity
  positivity

/-- ★ `n = 4` 的**蝶形**形状（`4` 叶链）：`g = (4−1)(3−1)(2−1) = 6`，权 `2³/(4!·6) = 1/18`。 -/
theorem yhkRootWeight_four_caterpillar : yhkRootWeight 4 6 = 1 / 18 := by
  unfold yhkRootWeight
  norm_num

/-- ★ `n = 4` 的**平衡**形状（两个 cherry）：`g = (4−1)(2−1)(2−1) = 3`，权 `2³/(4!·3) = 1/9`。 -/
theorem yhkRootWeight_four_balanced : yhkRootWeight 4 3 = 1 / 9 := by
  unfold yhkRootWeight
  norm_num

/-- ★★ **`n = 4` 的有根归一化**：`4` 叶有根标号拓扑共 `15 = (2·4−3)!!` 棵 ——
`12` 棵蝶形（`g = 6`）＋ `3` 棵平衡（`g = 3`）（`scripts/msc/yhk_weight_derive.py` 穷举），
按 §11.1 的权重求和恰为 `1`：`12·(1/18) + 3·(1/9) = 1`。 -/
theorem yhkRootWeight_four_total :
    12 * yhkRootWeight 4 6 + 3 * yhkRootWeight 4 3 = 1 := by
  rw [yhkRootWeight_four_caterpillar, yhkRootWeight_four_balanced]
  norm_num

/-- ★★★ **`n = 4` 的无根权重 ＝ `1/3`，与库内 `yhkLawFour` 的「三棵 quartet **等权** `1/3`」对齐**。

`T − ρ` 有 `2n−3 = 5` 个 rootings（文献 `:996-1006`）：`1` 个走内部边（得平衡形状，`1/9`）、
`4` 个走叶边（得蝶形，`1/18`）⇒ 无根权 `= 1/9 + 4·(1/18) = 1/3` ——
正是 ★★★ `yhkLawFour`（`:1445`）的 `prob ≡ 1/3`，也是 `clanProb 4 2 = 1/3`（★★ `clanProb_four_two`）。 -/
theorem yhkUnrootedWeight_four :
    yhkRootWeight 4 3 + 4 * yhkRootWeight 4 6 = 1 / 3 := by
  rw [yhkRootWeight_four_caterpillar, yhkRootWeight_four_balanced]
  norm_num

/-- ★★ **`n = 5` 的有根归一化**：`105` 棵有根标号拓扑分三个形状
（`g = 24, 8, 12`，计数 `60, 30, 15`，脚本穷举）：
`60·(1/180) + 30·(1/60) + 15·(1/90) = 1/3 + 1/2 + 1/6 = 1`。 -/
theorem yhkRootWeight_five_total :
    60 * yhkRootWeight 5 24 + 30 * yhkRootWeight 5 8 + 15 * yhkRootWeight 5 12 = 1 := by
  unfold yhkRootWeight
  norm_num

/-! ### 11.3 无根过程的**历史空间**与它的精确归一化（一般 `n`）

文献 `:1000-1006` 给出无根 YHK 律的一个**直接**生成过程：
「a leaf is selected uniformly at random and a new leaf (with a random label) is
attached to its incident edge」。

从 `3` 叶的 `Y` 形出发，第 `k` 步（`4 ≤ k ≤ n`）在**现有 `k−1` 片叶**里均匀选一片，故
历史（history）空间大小 `3·4···(n−1) = (n−1)!/2`，每条历史等概率 `2/(n−1)!`。
下面把这两件在**一般 `n`** 上形式化（这是缺口 ① 的「数据槽」：`MSCTreeLaw n` 的
`Ω` 与 `prob` 两个槽；`tree` 槽需要把历史送到 `Cladogram (Fin n)`，见 §11.1 末的说明）。 -/

/-- ★★ **YHK 无根过程的历史空间**（文献 `:1000-1006`）：第 `k` 步在 `k−1` 片叶里选一片，
故用 `Fin (n−3) → Fin (k+3)` 编码（`k` 从 `0` 起，第 `k` 步有 `k+3` 片叶）。

`n = 4` 时 `Fin 1 → Fin 3`，即 `3` 条历史（无根 `4` 叶树共 `3` 棵，与 ★★★ `yhkLawFour`
的 `Ω = Fin 3` 完全一致）。 -/
abbrev yhkHistorySpace (n : ℕ) : Type := (k : Fin (n - 3)) → Fin (k.val + 3)

/-- ★ `2·(3·4···(m+2)) = (m+2)!`（纯 `ℕ` 乘法形式，避开除法；`m = n − 3` 即历史数）。 -/
theorem two_mul_prod_range_add_three (m : ℕ) :
    2 * ∏ i ∈ Finset.range m, (i + 3) = (m + 2).factorial := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ, ← Nat.mul_assoc, ih,
        show k + 1 + 2 = k + 2 + 1 by omega, Nat.factorial_succ (k + 2),
        show k + 2 + 1 = k + 3 by omega]
      exact Nat.mul_comm _ _

/-- ★★★ **历史空间的大小**：`|Ω_n| = 3·4···(n−1) = (n−1)!/2`
（写成 `2·|Ω_n| = (n−1)!` 以免 `ℕ` 除法；`n ≥ 3` 时 `(n−1)!` 为偶数）。 -/
theorem two_mul_card_yhkHistorySpace {n : ℕ} (hn : 3 ≤ n) :
    2 * Fintype.card (yhkHistorySpace n) = (n - 1).factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [← Finset.prod_range (fun i : ℕ => i + 3), two_mul_prod_range_add_three]
  congr 1
  omega

/-- ★★ **历史空间的大小（除法形式）**：`|Ω_n| = (n−1)!/2`。 -/
theorem card_yhkHistorySpace {n : ℕ} (hn : 3 ≤ n) :
    Fintype.card (yhkHistorySpace n) = (n - 1).factorial / 2 := by
  have h := two_mul_card_yhkHistorySpace hn
  omega

/-- ★★ **YHK 无根过程的历史概率** `2/(n−1)!`（每条历史等概率）。 -/
noncomputable def yhkHistoryProb (n : ℕ) : ℝ := 2 / ((n - 1).factorial : ℝ)

/-- 历史概率非负。 -/
theorem yhkHistoryProb_nonneg (n : ℕ) : 0 ≤ yhkHistoryProb n := by
  unfold yhkHistoryProb
  positivity

/-- 历史概率严格为正。 -/
theorem yhkHistoryProb_pos (n : ℕ) : 0 < yhkHistoryProb n := by
  unfold yhkHistoryProb
  have hN : (0 : ℝ) < ((n - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  positivity

/-- ★★★ **YHK 无根过程的全概率为 `1`**（一般 `n ≥ 3`）：
`|Ω_n| · 2/(n−1)! = ((n−1)!/2)·(2/(n−1)!) = 1`。 -/
theorem sum_yhkHistoryProb {n : ℕ} (hn : 3 ≤ n) :
    ∑ _ω : yhkHistorySpace n, yhkHistoryProb n = 1 := by
  have hcard := two_mul_card_yhkHistorySpace hn
  have hN : ((n - 1).factorial : ℝ) ≠ 0 := by
    have : 0 < (n - 1).factorial := Nat.factorial_pos _
    exact_mod_cast this.ne'
  have hcast : (2 : ℝ) * (Fintype.card (yhkHistorySpace n) : ℝ) = ((n - 1).factorial : ℝ) := by
    rw [← Nat.cast_two, ← Nat.cast_mul, hcard]
  have hhalf : (Fintype.card (yhkHistorySpace n) : ℝ) = ((n - 1).factorial : ℝ) / 2 := by
    linarith
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold yhkHistoryProb
  rw [hhalf]
  field_simp

/-- ★★★ **`n = 4` 的历史空间与库内 `yhkLawFour`（`Ω = Fin 3`、`prob ≡ 1/3`）完全一致**：
`|Ω_4| = 3! / 2 = 3`、`prob = 2/3! = 1/3`。 -/
theorem yhkHistoryLawFour_match :
    Fintype.card (yhkHistorySpace 4) = 3 ∧ yhkHistoryProb 4 = (1 : ℝ) / 3 := by
  have h3 : (4 - 1).factorial = 6 := by decide
  refine ⟨?_, ?_⟩
  · have h := card_yhkHistorySpace (n := 4) (by norm_num)
    rw [h, h3]
  · unfold yhkHistoryProb
    rw [h3]
    norm_num

/-- ★★ **`n = 4`：历史空间是 `MSCTreeLaw 4` 的 `Ω` 与 `prob` 两个槽**
（`tree` 槽取 ★★★ `yhkLawFour` 的 `qTree`；两者的 `prob_sum` 因此是**同一条**算术）。 -/
theorem yhkHistoryLawFour_prob_sum :
    (∑ _ω : yhkHistorySpace 4, yhkHistoryProb 4) = ∑ _i : Fin 3, (1 : ℝ) / 3 := by
  rw [sum_yhkHistoryProb (by norm_num)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num


/-! ### 11.4 `clanProb` 的**一致性恒等式**（缺口的任何见证都必须满足的必要条件）

★★★ **`sum_mul_clanProb`**：`∑_{a=1}^{n−1} C(n,a)·clanProb(n,a) = 4n − 6`（`Ico 1 n = Icc 1 (n−1)`）。

两侧的语义：
* 左端 = 随机无根 YHK 树的 **proper clan 数**的期望 —— 基数 `a` 的子集有 `C(n,a)` 个，
  每个是 clan 的概率都恰是 `clanProb n a`（这正是缺口 `YHKClanLawGap` 的结论对 `A` 求和）；
* 右端 = `2·(2n−3)`：无根二叉树恰有 `2n−3` 条边，每条边给**两侧**两个 proper clan。

⇒ 缺口 `YHKClanLawGap` 的**任何**见证都必须让这条等式成立；本节证明**库内 `clanProb`
的闭形式自动满足它**（即闭形式与「树是二叉、共 `2n−3` 条边」这一事实相容）。

⚠️ 这仍是**闭形式之间的算术**（§4 的体例），**不是**概率层 —— `YHKClanLawGap` 本身未证；
本定理**不**以任何「存在一个律」为前提（无条件）。

推导：逐项用 ★★ `clanProb_eq_unfolded`（`C(n,a)^{-1}` 约掉）得三项分解
`2n/(a(a+1)) + 2n/((n−a)((n−a)+1)) − 2/(n−1)`，其中
* `∑_{a=1}^{n−1} 1/(a(a+1)) = 1 − 1/n`（望远镜，★ `sum_Ico_inv_mul_succ`）；
* 第二项由 `a ↦ n−a` 的双射与之相同（★ `sum_Ico_inv_mul_succ_tsub`）；
* 常数项 `(n−1)·2/(n−1) = 2`。
故总和 `= 2n(1−1/n) + 2n(1−1/n) − 2 = 4n − 6`。
（`scripts/msc/yhk_weight_derive.py` 在 `n = 3..7` 上以精确有理数核对同一条恒等式。） -/

/-- ★ 望远镜：`∑_{k<m} 1/((k+1)(k+2)) = 1 − 1/(m+1)`。 -/
theorem sum_range_inv_mul_succ (m : ℕ) :
    ∑ k ∈ Finset.range m, (1 : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 2))
      = 1 - 1 / ((m : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : ((j : ℝ) + 1 + 1) ≠ 0 := by positivity
      have h2 : ((j : ℝ) + 1 + 2) ≠ 0 := by positivity
      field_simp
      ring

/-- ★ `∑_{a=1}^{n−1} 1/(a(a+1)) = 1 − 1/n`（望远镜）。 -/
theorem sum_Ico_inv_mul_succ {n : ℕ} (hn : 1 ≤ n) :
    ∑ a ∈ Finset.Ico 1 n, (1 : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) = 1 - 1 / (n : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have h := sum_range_inv_mul_succ (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  rw [hcast, show (n : ℝ) - 1 + 1 = (n : ℝ) by ring] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring_nf

/-- ★ **换向**：`a ↦ n−a` 是 `{1,…,n−1}` 上的双射，故
`∑_{a=1}^{n−1} 1/((n−a)(n−a+1)) = ∑_{a=1}^{n−1} 1/(a(a+1)) = 1 − 1/n`。 -/
theorem sum_Ico_inv_mul_succ_tsub {n : ℕ} (hn : 1 ≤ n) :
    ∑ a ∈ Finset.Ico 1 n, (1 : ℝ) / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
      = 1 - 1 / (n : ℝ) := by
  rw [← sum_Ico_inv_mul_succ hn]
  refine Finset.sum_nbij' (fun a => n - a) (fun a => n - a) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    omega
  · intro a _
    rfl

/-- ★★★ **`clanProb` 的一致性恒等式**（§11.4）：`∑_{a=1}^{n−1} C(n,a)·clanProb(n,a) = 4n − 6`。

即「随机无根二叉树的 proper clan 数的期望 = `2·(2n−3)`」—— 缺口 `YHKClanLawGap` 的
任何见证都必须满足它；本定理证明库内闭形式无条件满足它。 -/
theorem sum_mul_clanProb {n : ℕ} (hn : 2 ≤ n) :
    ∑ a ∈ Finset.Ico 1 n, ((n.choose a : ℝ) * clanProb n a) = 4 * (n : ℝ) - 6 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hterm : ∀ a ∈ Finset.Ico 1 n,
      ((n.choose a : ℝ) * clanProb n a)
        = 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1)))
          + 2 * (n : ℝ) * (1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)))
          - 2 / ((n : ℝ) - 1) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp ha
    have hc : ((n.choose a : ℝ)) ≠ 0 := by
      have hpos : 0 < n.choose a := Nat.choose_pos (le_of_lt h2)
      exact_mod_cast hpos.ne'
    rw [clanProb_eq_unfolded hn]
    have hcc : ((n.choose a : ℝ)) * ((n.choose a : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hc
    calc ((n.choose a : ℝ))
          * ((2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1))
             + 2 * (n : ℝ) / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
             - 2 / ((n : ℝ) - 1)) * ((n.choose a : ℝ))⁻¹)
        = (2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1))
             + 2 * (n : ℝ) / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1))
             - 2 / ((n : ℝ) - 1)) * (((n.choose a : ℝ)) * ((n.choose a : ℝ))⁻¹) := by
          ring
      _ = 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1)))
          + 2 * (n : ℝ) * (1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)))
          - 2 / ((n : ℝ) - 1) := by
          rw [hcc, mul_one]
          ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hA : ∑ a ∈ Finset.Ico 1 n, 2 * (n : ℝ) * (1 / ((a : ℝ) * ((a : ℝ) + 1)))
      = 2 * (n : ℝ) * (1 - 1 / (n : ℝ)) := by
    rw [← Finset.mul_sum, sum_Ico_inv_mul_succ (by omega)]
  have hB : ∑ a ∈ Finset.Ico 1 n,
        2 * (n : ℝ) * (1 / (((n - a : ℕ) : ℝ) * (((n - a : ℕ) : ℝ) + 1)))
      = 2 * (n : ℝ) * (1 - 1 / (n : ℝ)) := by
    rw [← Finset.mul_sum, sum_Ico_inv_mul_succ_tsub (by omega)]
  have hC : ∑ _a ∈ Finset.Ico 1 n, (2 / ((n : ℝ) - 1)) = 2 := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    rw [hcast]
    field_simp
  rw [hA, hB, hC]
  field_simp
  ring


/-! ### 11.5 有根 carrier 上的**概率层运输**（缺口 ②(b) 的概率层 —— 无条件）＋ 条件收口

★ 本节的定位：缺口 `YHKClanLawGap` 要的是「无根树上的 clan 事件概率」。而 YHK 过程是**有根**的
（文献 `:191-221`），其载体在库内是 `Cladogram (X ⊕ Unit)`（§10 的「有根树 = 加一片名为 root 的
标记叶」）。★ `clanEvent_rootedToCladogram` 把两者的**事件求和**精确接起来 ——
这一步是**无条件**真证，且正是 §8.4 ②(b) 登记为缺的「有根 → 无根桥」的**概率层**（树层已由
★★★ `isClade_rootedToCladogram_iff_of_nonempty`（§10.3）给出）。

★ `yhkClanLawGap_slice_of_rootedClanEvent` 是**条件收口**（命名带 `_of_`，**不是** `_holds`）：
它把缺口在 `n ≥ 3` 上**归约**为有根 carrier 上的同一条命题。剩下要证的因此**只有一件**：

```text
∀ n ≥ 3, ∃ 有根 n 叶 YHK 型律 (Ω, prob, U : Ω → Cladogram (Fin n ⊕ Unit)),
  ∀ A, A.Nonempty → A.card < n →  ∑_{ω : IsClanMinusRoot (U ω) A} prob ω = clanProb n A.card
```

即「Lemma 6.1 的**概率层**」：`qₙ(A) = pₙ(a) + pₙ(n−a) − p̂ₙ(a, n−a)`（文献 `:1040`），
右端三件闭形式库内都已有（`pn`、`pnHatExh`），算术恒等式也已证
（★★★ `clanProb_eq_inclusionExclusion`，`:404`）；缺的是**权重层**：
`pn(a)` 与 `p̂n(a, n−a)` 的**概率**意义，即对有根 YHK 权（§11.1）求和。
⚠️ 另有一件**小缺口**：`n = 2`。`rootedToCladogram` 要求 `3 ≤ |X|`，而 `Cladogram (Fin 2)`
在库内**没有现成件**（`Cladogram.ofCompatibleSplits` 同样要求 `3 ≤ |X|`）——
这是 `_holds` 之外仅剩的边角（`n = 2` 的等式本身是平凡的：`A.card = 1` 且 `clanProb 2 1 = 1`）。 -/

/-- ★★★ **去根映射下的 clan 事件求和恒等**（**无条件**）：对任意有限概率空间、任意有根树族
`U : Ω → Cladogram (Fin n ⊕ Unit)`、任意非空**真**子集 `A`（`A.Nonempty` ＋ `Aᶜ.Nonempty`），

`∑_{ω : A 是 rootedToCladogram (U ω) 的 clan} prob ω = ∑_{ω : IsClanMinusRoot (U ω) A} prob ω`。

即 ★★★ `isClade_rootedToCladogram_iff_of_nonempty`（§10.3）的**概率层**：无根侧的 `clanEvent`
被精确换成有根侧的 `IsClanMinusRoot`（ZDS Lemma 6.1 的载体形态，`:991-992`）。

⚠️ 它**不是** `YHKClanLawGap` 的证明：右端的具体值（`= clanProb n |A|`）仍需要有根 YHK 律上的
`pn(a) + pn(n−a) − p̂n(a, n−a)` 计算。前提 `hAc` 不是可以省的：`A = univ` 时 `IsClade` 为假而
`IsClanMinusRoot` 为真（§10.4 的 ★★★ `isClanMinusRoot_univ`）；缺口的 `A.card < n` 恰好排除它。 -/
theorem clanEvent_rootedToCladogram {n : ℕ} {Ω : Type} [Fintype Ω]
    (h3 : 3 ≤ Fintype.card (Fin n))
    (prob : Ω → ℝ) (U : Ω → Cladogram (Fin n ⊕ Unit)) {A : Finset (Fin n)}
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (∑ ω ∈ (Finset.univ : Finset Ω).filter
        (fun ω => (rootedToCladogram (U ω) h3).IsClade A), prob ω)
      = ∑ ω ∈ (Finset.univ : Finset Ω).filter
        (fun ω => IsClanMinusRoot (U ω) A), prob ω := by
  have h : (Finset.univ : Finset Ω).filter
      (fun ω => (rootedToCladogram (U ω) h3).IsClade A)
      = (Finset.univ : Finset Ω).filter (fun ω => IsClanMinusRoot (U ω) A) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isClade_rootedToCladogram_iff_of_nonempty (U ω) h3 hA hAc
  rw [h]

/-- ★★ **`n ≥ 3` 的条件收口**（**不是** `_holds`）：若在有根 carrier 上，
对每个 `n ≥ 3` 都有一个 YHK 型律使 `IsClanMinusRoot` 事件的概率 `= clanProb n |A|`，
则缺口 `YHKClanLawGap` 在 `n ≥ 3` 上成立。

**为什么这不是空转**：`H` 不是缺口本身 —— 命中它要**造出** `U : Ω → Cladogram (Fin n ⊕ Unit)`
（有根载体）并算出 `IsClanMinusRoot` 的概率，而缺口的 `∃` 只要求无根 `Cladogram (Fin n)`；
两者的差别由 ★★★ `clanEvent_rootedToCladogram` ＋ §10 的载体桥精确支付。
（口径参考 `scripts/gap_ledger.py`：本条的命名后缀 `_of_rootedClanEvent` 不在收口后缀表内，
故台账**不会**把 `YHKClanLawGap` 记成已收口 ✓ —— 它仍应是 `[真开放]`。） -/
theorem yhkClanLawGap_slice_of_rootedClanEvent
    (H : ∀ n : ℕ, 3 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
      (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
      (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit)),
      ∀ A : Finset (Fin n), A.Nonempty → A.card < n →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter (fun ω => IsClanMinusRoot (U ω) A), prob ω)
          = clanProb n A.card) :
    ∀ n : ℕ, 3 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
      (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
      (tree : Ω → Cladogram.{0, 0} (Fin n)),
      ∀ A : Finset (Fin n), A.Nonempty → A.card < n →
        (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
          = clanProb n A.card := by
  intro n h3
  obtain ⟨Ω, hF, prob, hnn, hsum, U, hU⟩ := H n h3
  refine ⟨Ω, hF, prob, hnn, hsum,
    fun ω => rootedToCladogram (U ω) (by simpa using h3), ?_⟩
  intro A hA hlt
  have hAc : Aᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hkey := clanEvent_rootedToCladogram (by simpa using h3) prob U hA hAc
  show (∑ ω ∈ (Finset.univ : Finset Ω).filter
      (fun ω => (rootedToCladogram (U ω) (by simpa using h3)).IsClade A), prob ω)
      = clanProb n A.card
  exact hkey.trans (hU A hA hlt)


/-! ### 11.6 缺口 `n = 2` 的边角（★ 现成 2 叶树）＋ 条件收口的**完整版**

`rootedToCladogram`（§10.3）要求 `3 ≤ |X|`，而 `Cladogram (Fin 2)` 在库内**没有**现成件
（`Cladogram.ofCompatibleSplits` 同样要求 `3 ≤ |X|`）。本节把它补上：
`V = Fin 2`、`graph = starGraph 0`（单边）、`leaf = id` —— 度全为 `1`、无度 2 顶点、
单边连通无圈（`SimpleGraph.isTree_starGraph`）。

于是 ★★★ `yhkClanLawGap_of_rootedClanEvent` 把缺口**完整**归约到有根 carrier 上
（不再留 `n = 2` 的洞）。 -/

/-- ★ `starGraph 0` 在 `Fin 2` 上处处度 `1`（两个顶点互为唯一邻居）。 -/
theorem degree_starGraph_fin_two (v : Fin 2) :
    (SimpleGraph.starGraph (0 : Fin 2)).degree v = 1 := by
  fin_cases v
  · simpa using SimpleGraph.degree_starGraph_center (r := (0 : Fin 2))
  · exact SimpleGraph.degree_starGraph_of_ne_center (by decide : (1 : Fin 2) ≠ 0)

/-- ★★ **2 叶 `Cladogram` 的现成件**（缺口 `n = 2` 边角）：`V = Fin 2`、
`graph = starGraph 0`（即单边 `0—1`）、`leaf = id`（两顶点都是叶）。

这是 ★★★ `yhkClanLawGap_two_slice` 与 ★★ `yhkClanLawGap_of_rootedClanEvent` 的唯一缺口 ——
库内 `Cladogram.ofCompatibleSplits` 要求 `3 ≤ |X|`，故 `|X| = 2` 必须**单独造**。 -/
noncomputable def twoLeafCladogram : Cladogram (Fin 2) where
  V := Fin 2
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := SimpleGraph.starGraph (0 : Fin 2)
  decAdj := inferInstance
  isTree := SimpleGraph.isTree_starGraph 0
  leaf := Function.Embedding.refl (Fin 2)
  leaf_iff_degree_one := by
    intro v
    exact ⟨fun _ => degree_starGraph_fin_two v, fun _ => ⟨v, rfl⟩⟩
  no_degree_two := by
    intro v h
    have := degree_starGraph_fin_two v
    omega

/-- ★★★ **缺口在 `n = 2` 上的整条**：`Ω = PUnit`、`prob ≡ 1`、`tree ≡ twoLeafCladogram`。
（`A.card < 2` 且 `A.Nonempty` ⇒ `A.card = 1`，走 ★★★ `yhkClanLawGap_trivial_card_slice`。） -/
theorem yhkClanLawGap_two_slice :
    ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ) (_ : ∀ ω, 0 ≤ prob ω)
      (_ : ∑ ω, prob ω = 1) (tree : Ω → Cladogram.{0, 0} (Fin 2)),
      ∀ A : Finset (Fin 2), A.Nonempty → A.card < 2 →
        (∑ ω ∈ Finset.univ.filter (fun ω => (tree ω).IsClade A), prob ω)
          = clanProb 2 A.card := by
  have hsum1 : (∑ _ω : PUnit, (1 : ℝ)) = 1 := by simp
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => by norm_num, hsum1,
    fun _ => twoLeafCladogram, ?_⟩
  intro A hA hlt
  have hcard : A.card = 1 ∨ A.card = 2 - 1 := by
    left
    have h1 : 1 ≤ A.card := Finset.card_pos.mpr hA
    omega
  exact yhkClanLawGap_trivial_card_slice (n := 2) (by norm_num) (fun _ => 1) hsum1
    (fun _ => twoLeafCladogram) hA hcard

/-- ★★ **条件收口的完整版（覆盖 `∀ n, 2 ≤ n`）**：有根 carrier 上的同一命题 ⟹ `YHKClanLawGap`。
（`n = 2` 由 ★★★ `yhkClanLawGap_two_slice` 补，`n ≥ 3` 由
★★ `yhkClanLawGap_slice_of_rootedClanEvent` 转。） -/
theorem yhkClanLawGap_of_rootedClanEvent
    (H : ∀ n : ℕ, 3 ≤ n → ∃ (Ω : Type) (_ : Fintype Ω) (prob : Ω → ℝ)
      (_ : ∀ ω, 0 ≤ prob ω) (_ : ∑ ω, prob ω = 1)
      (U : Ω → Cladogram.{0, 0} (Fin n ⊕ Unit)),
      ∀ A : Finset (Fin n), A.Nonempty → A.card < n →
        (∑ ω ∈ (Finset.univ : Finset Ω).filter (fun ω => IsClanMinusRoot (U ω) A), prob ω)
          = clanProb n A.card) :
    YHKClanLawGap := by
  intro n hn
  rcases Nat.lt_or_ge n 3 with h2 | h3
  · have hn2 : n = 2 := by omega
    subst hn2
    exact yhkClanLawGap_two_slice
  · exact yhkClanLawGap_slice_of_rootedClanEvent H n h3


/-! ### 11.7 有根 YHK 律的 **split 族载体**（`Fintype (Cladogram X)` 死结的绕法）

§11.5 的收口把缺口归约到「造有根 `n` 叶 YHK 律并算 `IsClanMinusRoot` 的概率」。**障碍**是
`Fintype (Cladogram X)` 在库内不存在（`Cladogram.V : Type*` 任意），故「对拓扑求和/归一化」
连陈述都不能。

**绕法（本节落地）**：把样本空间换成 **split 族** —— `Finset (Split X)` 是有限类型
（`instFintypeKPartition` ＋ `instFintypeFinset`），而**树由族给出**（★★★
`Cladogram.ofCompatibleSplits`），且其 split 系统被**完全刻画**（★★
`isSplitOf_ofCompatibleSplits`）。于是：

* `rootedSplitFamily n` —— 载体（相容 ＋ 非平凡 ＋ `swap`-封闭 ＋ 恰 `2(n−2)` 个定向 split）；
* ★★ `rootedSplitFamilyFintype n` —— **`Fintype` 实例**（死结在此绕开）；
* ★★ `rootedSplitTree` —— 族 ↦ 有根树；
* ★★★ `isClanMinusRoot_rootedSplitTree` —— **clan 事件 = 「族里有该 split」**（＋ `A.card ∈ {1, n−1}`
  两档平凡情形），这正是第 3 步（Lemma 6.2 的求和）要的接口；
* ★★★ `rootedSplitWeight` ＋ 非负/正 —— §11.1 的 YHK 权在载体上的显式形式；
* ★★ `rootedSplitFamily_two_card` —— `n = 2` 的载体恰 `1` 个元素（不空转）。

⚠️ **本节的 `Σ = 1` 未证**：那正是 ① 的「拓扑层归一化」，等价于
`S_n := Σ_T 1/g(T) = n!/2^{n−1}`（§11.1 推导第 3 步），需要一个**计数**论证
（`rootedSplitFamily n` 的元素 ↔ 有根二叉标号拓扑），本批未做。 -/

/-! ## ② 有根 YHK 律的 split 族载体 -/

/-- ★★★ **有根 `n` 叶 YHK 律的 split 族载体**：`Ω_n` = 「相容 ＋ 非平凡 ＋ `swap`-封闭 ＋
恰 `2(n−2)` 个定向 split」的族，作用在 `Cladogram (Fin n ⊕ Unit)` 的 split 系统上。

**为什么用族而不是树**：`Fintype (Cladogram X)` 在库内**不存在**（`Cladogram.V : Type*` 任意），
故「对拓扑求和」连陈述都不能；而 `Finset (Split X)` 是有限类型（`instFintypeKPartition`），
树由 ★★★ `Cladogram.ofCompatibleSplits` 给出 ⇒ `Ω_n` **是** `Fintype`。

`2(n−2)` 的来源：有根二叉树加根叶后是 `n+1` 叶无根二叉树，边数 `2n−1`，其中 `n+1` 条叶边
（平凡），故非平凡 split 恰 `n−2` 个；`Split` 是**定向**的，`swap`-封闭使计数翻倍。 -/
abbrev rootedSplitFamily (n : ℕ) : Type :=
  { fam : Finset (Split (Fin n ⊕ Unit)) //
      (∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t) ∧
      (∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) ∧
      (∀ s ∈ fam, s.swap ∈ fam) ∧
      fam.card = 2 * (n - 2) }

/-- ★★ **`Ω_n` 是有限类型**（缺口 ② 的死结在这里被绕开）。 -/
noncomputable instance rootedSplitFamilyFintype (n : ℕ) : Fintype (rootedSplitFamily n) := by
  classical
  exact Subtype.fintype _

/-- ★★★ **把 split 族送成一棵有根树**（`Cladogram.ofCompatibleSplits`）。
前提「相容 / 非平凡 / `swap`-封闭」直接从 `ω` 的字段读出；`3 ≤ |Fin n ⊕ Unit|` 来自 `n ≥ 2`。 -/
noncomputable def rootedSplitTree {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n) :
    Cladogram.{0, 0} (Fin n ⊕ Unit) :=
  Cladogram.ofCompatibleSplits ω.val (Sum.inr ()) ω.2.1 ω.2.2.1 ω.2.2.2.1 (by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega)

/-- ★★ **`rootedSplitTree` 的 split 系统被完全刻画**：恰为「族 ∪ 平凡 split」。 -/
theorem isSplitOf_rootedSplitTree {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n)
    (s : Split (Fin n ⊕ Unit)) :
    (rootedSplitTree hn ω).IsSplitOf s ↔
      s ∈ ω.val ∨ (∃ x : Fin n ⊕ Unit, s.sideA = {x}) ∨
        (∃ x : Fin n ⊕ Unit, s.sideA = {x}ᶜ) :=
  Cladogram.isSplitOf_ofCompatibleSplits ω.val (Sum.inr ()) ω.2.1 ω.2.2.1 ω.2.2.2.1 _ s

/-- ★★ **`n = 2` 的载体非空**：空族（`card = 2·(2−2) = 0`）满足全部条件。 -/
theorem rootedSplitFamily_two_nonempty : Nonempty (rootedSplitFamily 2) :=
  ⟨⟨∅, by refine ⟨?_, ?_, ?_, by simp⟩ <;> simp⟩⟩

/-- ★★★ **`n = 2` 的载体恰有一个元素**（唯一的 2 叶有根拓扑 = 三叶星）⇒ 载体不空转。 -/
theorem rootedSplitFamily_two_card : Fintype.card (rootedSplitFamily 2) = 1 := by
  have hempty : ∀ x : rootedSplitFamily 2, x.val = ∅ := by
    intro x
    apply Finset.card_eq_zero.mp
    calc x.val.card = 2 * (2 - 2) := x.2.2.2.2
      _ = 0 := by norm_num
  have hle : Fintype.card (rootedSplitFamily 2) ≤ 1 := by
    rw [Fintype.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext ((hempty a).trans (hempty b).symm)⟩
  have hpos : 0 < Fintype.card (rootedSplitFamily 2) :=
    Fintype.card_pos_iff.mpr rootedSplitFamily_two_nonempty
  omega

/-- ★★★ **有根 YHK 权**（§11.1 的 `P_rooted`）在 split 族载体上的形式：
`g = (n−1) · ∏_{s ∈ fam, ρ ∉ s.sideA} (|s.sideA| − 1)`。

依据：有根树 `T` 的每个内部顶点 `v ≠ root` 对应 `T − ρ` 的一个非平凡 split，
`n_v` = **不含 `ρ` 的那一侧**的叶数（该侧无根叶，故就是 `|s.sideA|`）；
根顶点给出 `n_{root} = n`，即因子 `(n−1)`。`swap`-封闭保证每个（无序）split 里
**恰有一个**定向满足 `ρ ∉ sideA`。 -/
noncomputable def rootedSplitWeight {n : ℕ} (ω : rootedSplitFamily n) : ℝ :=
  yhkRootWeight n
    ((n - 1) * ∏ s ∈ ω.val.filter (fun s => Sum.inr () ∉ s.sideA), (s.sideA.card - 1))

/-- ★★ **权的形状不变量为正**：`0 < (n−1)·∏(…)`（每个因子 `≥ 1`）。 -/
theorem rootedSplitWeight_shape_pos {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n) :
    0 < (n - 1) * ∏ s ∈ ω.val.filter (fun s => Sum.inr () ∉ s.sideA), (s.sideA.card - 1) := by
  have hn1 : 0 < n - 1 := by omega
  have hprod : 0 < ∏ s ∈ ω.val.filter (fun s => Sum.inr () ∉ s.sideA),
      (s.sideA.card - 1) := by
    refine Finset.prod_pos (fun s hs => ?_)
    have hmem : s ∈ ω.val := (Finset.mem_filter.mp hs).1
    have h2 : 2 ≤ s.sideA.card := (ω.2.2.1 s hmem).1
    omega
  exact Nat.mul_pos hn1 hprod

/-- ★★★ **权严格为正**（故非负）。 -/
theorem rootedSplitWeight_pos {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n) :
    0 < rootedSplitWeight ω := by
  unfold rootedSplitWeight
  exact yhkRootWeight_pos (rootedSplitWeight_shape_pos hn ω)

/-- ★★ **权非负**。 -/
theorem rootedSplitWeight_nonneg {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n) :
    0 ≤ rootedSplitWeight ω :=
  (rootedSplitWeight_pos hn ω).le

/-- clan 事件在 split 族载体上的精确刻画（第 3 步的接口）。 -/
theorem isClanMinusRoot_rootedSplitTree {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n)
    {A : Finset (Fin n)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    IsClanMinusRoot (rootedSplitTree hn ω) A ↔
      (∃ s ∈ ω.val, realLeaves s.sideA = A) ∨ A.card = 1 ∨ A.card = n - 1 := by
  constructor
  · intro h
    obtain ⟨s, hs, hside⟩ :=
      (isClanMinusRoot_iff_exists (rootedSplitTree hn ω) A).mp h
    rcases (isSplitOf_rootedSplitTree hn ω s).mp hs with hfam | ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨s, hfam, hside⟩
    · rcases x with a | u
      · rw [hx, realLeaves_singleton_inl] at hside
        exact Or.inr (Or.inl (by rw [← hside]; simp))
      · cases u
        rw [hx, realLeaves_singleton_inr] at hside
        rw [← hside] at hA
        exact absurd hA (by simp)
    · rcases x with a | u
      · rw [hx, realLeaves_compl_singleton_inl] at hside
        exact Or.inr (Or.inr (by
          rw [← hside, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]))
      · cases u
        rw [hx, realLeaves_compl_singleton_inr] at hside
        rw [← hside] at hAc
        exact absurd hAc (by simp)
  · rintro (⟨s, hfam, hside⟩ | h1 | h1)
    · exact (isClanMinusRoot_iff_exists _ A).mpr
        ⟨s, (isSplitOf_rootedSplitTree hn ω s).mpr (Or.inl hfam), hside⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      have hB : ({Sum.inl a} : Finset (Fin n ⊕ Unit)).Nonempty := ⟨Sum.inl a, by simp⟩
      have hBc : (({Sum.inl a} : Finset (Fin n ⊕ Unit))ᶜ).Nonempty := ⟨Sum.inr (), by simp⟩
      refine (isClanMinusRoot_iff_exists _ ({a} : Finset (Fin n))).mpr
        ⟨splitOf ({Sum.inl a} : Finset (Fin n ⊕ Unit)) hB hBc, ?_, ?_⟩
      · exact (isSplitOf_rootedSplitTree hn ω _).mpr (Or.inr (Or.inl ⟨Sum.inl a, rfl⟩))
      · rw [splitOf_sideA, realLeaves_singleton_inl]
    · have hcomp : Aᶜ.card = 1 := by
        rw [Finset.card_compl, Fintype.card_fin]; omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcomp
      have hAeq : A = ({a} : Finset (Fin n))ᶜ := by rw [← ha]; simp
      have hB : (({Sum.inl a} : Finset (Fin n ⊕ Unit))ᶜ).Nonempty := ⟨Sum.inr (), by simp⟩
      have hBc : ((({Sum.inl a} : Finset (Fin n ⊕ Unit))ᶜ)ᶜ).Nonempty := by
        rw [compl_compl]; exact ⟨Sum.inl a, by simp⟩
      rw [hAeq]
      refine (isClanMinusRoot_iff_exists _ (({a} : Finset (Fin n))ᶜ)).mpr
        ⟨splitOf (({Sum.inl a} : Finset (Fin n ⊕ Unit))ᶜ) hB hBc, ?_, ?_⟩
      · exact (isSplitOf_rootedSplitTree hn ω _).mpr (Or.inr (Or.inr ⟨Sum.inl a, rfl⟩))
      · rw [splitOf_sideA, realLeaves_compl_singleton_inl]

/-- clan 事件在载体上的求和形式（第 3 步要算的对象）。 -/
theorem clanEvent_rootedSplitFamily {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ≤ n)
    {A : Finset (Fin n)} (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    (∑ ω ∈ (Finset.univ : Finset (rootedSplitFamily n)).filter
        (fun ω => (rootedToCladogram (rootedSplitTree hn ω) (by simpa using h3)).IsClade A),
        rootedSplitWeight ω)
      = ∑ ω ∈ (Finset.univ : Finset (rootedSplitFamily n)).filter
          (fun ω => (∃ s ∈ ω.val, realLeaves s.sideA = A) ∨ A.card = 1 ∨ A.card = n - 1),
          rootedSplitWeight ω := by
  rw [clanEvent_rootedToCladogram (by simpa using h3) rootedSplitWeight
    (fun ω => rootedSplitTree hn ω) hA hAc]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isClanMinusRoot_rootedSplitTree hn ω hA hAc


/-! ### 11.8 载体的**不空转**检查与「非平凡 split」收窄

`rootedSplitFamily n` 若对 `n ≥ 3` 是空的，则 §11.7 的 `Σ = 1` 会退化成 `0 = 1`（假），
下一步全白做。本节把非空性显式造出来（`n = 2` 已在 §11.7 由 `rootedSplitFamily_two_card` 覆盖）。
★ 顺带把 ★★ `isSplitOf_rootedSplitTree` 的两档「平凡」支去掉：族的成员恰是树的**非平凡**
split（这正是 `Split` 层上「clan = split」的接口）。 -/

/-- 非平凡时 `IsSplitOf` 恰为族成员（去掉两档平凡 split）。 -/
theorem isSplitOf_rootedSplitTree_of_notTrivial {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n)
    {s : Split (Fin n ⊕ Unit)} (hs : ¬ s.IsTrivial) :
    (rootedSplitTree hn ω).IsSplitOf s ↔ s ∈ ω.val := by
  rw [isSplitOf_rootedSplitTree hn ω s]
  constructor
  · rintro (h | ⟨x, hx⟩ | ⟨x, hx⟩)
    · exact h
    · exact absurd (Or.inl ⟨x, hx⟩) hs
    · exact absurd (Or.inr ⟨x, hx⟩) hs
  · exact fun h => Or.inl h

/-- `n = 3` 时载体的具体见证：`{0,1} | {2,ρ}` 及其换向。 -/
theorem rootedSplitFamily_three_nonempty : Nonempty (rootedSplitFamily 3) := by
  have hB : ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} : Finset (Fin 3 ⊕ Unit)).Nonempty :=
    ⟨Sum.inl 0, by simp⟩
  have hBc : (({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} : Finset (Fin 3 ⊕ Unit))ᶜ).Nonempty :=
    ⟨Sum.inr (), by simp⟩
  refine ⟨⟨{splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
      Finset (Fin 3 ⊕ Unit)) hB hBc,
    (splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
      Finset (Fin 3 ⊕ Unit)) hB hBc).swap}, ?_, ?_, ?_, ?_⟩⟩
  · -- 相容（自身与换向两两相容）
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inr (Or.inl (Split.disjoint_sides _))
    · exact Or.inl (by rw [Split.swap_sideA]; exact Split.disjoint_sides _)
    · exact Or.inl (by
        rw [Split.swap_sideA]
        exact disjoint_comm.mpr (Split.disjoint_sides _))
    · exact Or.inr (Or.inl (by
        rw [Split.swap_sideA, Split.swap_sideB]
        exact disjoint_comm.mpr (Split.disjoint_sides _)))
  · -- 非平凡（两侧各 2）
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [splitOf_sideA, splitOf_sideB]
      constructor
      · decide
      · rw [Finset.card_compl, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
        decide
    · rw [Split.swap_sideA, Split.swap_sideB, splitOf_sideA, splitOf_sideB]
      constructor
      · rw [Finset.card_compl, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
        decide
      · decide
  · -- swap-封闭
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
    rcases ha with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (Split.swap_swap _)
  · -- card = 2·(3−2) = 2
    have hne : splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
        Finset (Fin 3 ⊕ Unit)) hB hBc ≠
        (splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Unit)) hB hBc).swap := by
      intro h
      have h1 : (splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
          Finset (Fin 3 ⊕ Unit)) hB hBc).sideA =
          (splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
            Finset (Fin 3 ⊕ Unit)) hB hBc).sideB := by
        rw [← Split.swap_sideA]
        exact congrArg Split.sideA h
      have h2 : Sum.inl (0 : Fin 3) ∈
          (splitOf ({Sum.inl (0 : Fin 3), Sum.inl (1 : Fin 3)} :
            Finset (Fin 3 ⊕ Unit)) hB hBc).sideA := by
        rw [splitOf_sideA]; simp
      rw [h1, splitOf_sideB] at h2
      simp at h2
    rw [Finset.card_pair hne]


/-! ### 11.9 载体**不重复计数**（归一化的那一半前提）

★ `rootedSplitTree_family_eq`：两个族若给出同一个（非平凡）split 系统，则两个族相等 ——
即 `fam ↦ tree` 在**拓扑类**上是单射，故 §11.7 的 `Σ_ω weight ω` **不会把同一棵拓扑算两次**。
这是 ① 的拓扑层归一化（`Σ = 1`，仍未证）的**一半**前提；另一半是「每个拓扑类都被击中」
（需要 `rootedSplitFamily n` 与有根二叉标号拓扑的**计数**双射，本批未做）。 -/

/-- ★★ **族里只有非平凡 split**（`hnt` 的直接推论）。 -/
theorem not_isTrivial_of_mem_rootedSplitFamily {n : ℕ} (ω : rootedSplitFamily n)
    {s : Split (Fin n ⊕ Unit)} (hs : s ∈ ω.val) : ¬ s.IsTrivial := by
  intro h
  rcases (Split.isTrivial_iff_card s).mp h with h1 | h1
  · have h2 := (ω.2.2.1 s hs).1
    omega
  · have h2 := (ω.2.2.1 s hs).2
    omega

/-- ★★★ **载体不重复计数**：两族若给出同一个（非平凡）split 系统，则两族相等。

即 `fam ↦ tree` 在「拓扑类」上是**单射** —— 这是 ① 的拓扑层归一化
（`Σ_ω weight ω = 1`）**不重复计数**的那一半前提。 -/
theorem rootedSplitTree_family_eq {n : ℕ} (hn : 2 ≤ n) {ω₁ ω₂ : rootedSplitFamily n}
    (h : ∀ s : Split (Fin n ⊕ Unit), ¬ s.IsTrivial →
      ((rootedSplitTree hn ω₁).IsSplitOf s ↔ (rootedSplitTree hn ω₂).IsSplitOf s)) :
    ω₁ = ω₂ := by
  have hfam : ω₁.val = ω₂.val := by
    ext s
    by_cases hs : s.IsTrivial
    · exact iff_of_false (fun hmem => not_isTrivial_of_mem_rootedSplitFamily ω₁ hmem hs)
        (fun hmem => not_isTrivial_of_mem_rootedSplitFamily ω₂ hmem hs)
    · rw [← isSplitOf_rootedSplitTree_of_notTrivial hn ω₁ hs,
        ← isSplitOf_rootedSplitTree_of_notTrivial hn ω₂ hs]
      exact h s hs
  exact Subtype.ext hfam


/-! ### 11.10 权重的乘积**恰好 `n − 2` 个因子**（`g` 的形状对得上）

`rootedSplitWeight`（§11.7）是 `yhkRootWeight n ((n−1) · ∏_{s ∈ fam, ρ ∉ s.sideA}(|s.sideA| − 1))`；
要让它真的是 `∏_{v 内部}(n_v − 1)`（§11.1），乘积必须有**恰好 `n − 2` 个因子** ——
因为非根内部顶点恰 `n − 2` 个。

★ `rootedSplitWeight_filter_card` 证明的就是这件事：`swap`-封闭把 `2(n−2)` 个定向 split 配成
`n−2` 对，每对里**恰有一个**定向的 `sideA` 不含 `ρ`（`ρ` 必在两侧之一，且两侧不交）。 -/

/-- ★ SWAP 是对合，故单射。 -/
theorem swap_injective_fin {n : ℕ} : Function.Injective (Split.swap : Split (Fin n ⊕ Unit) → _) := by
  intro a b h
  have := congrArg Split.swap h
  simpa [Split.swap_swap] using this

/-- ★★ **权重乘积的因子数恰为 `n − 2`**（= 非根内部顶点数）：`swap`-封闭把族配成对，
每对里**恰有一个**定向满足 `ρ ∉ sideA`（`ρ` 恰在两侧之一）。 -/
theorem rootedSplitWeight_filter_card {n : ℕ} (ω : rootedSplitFamily n) :
    (ω.val.filter (fun s => Sum.inr () ∉ s.sideA)).card = n - 2 := by
  have hcard : ω.val.card = 2 * (n - 2) := ω.2.2.2.2
  have hmem : ∀ s : Split (Fin n ⊕ Unit), Sum.inr () ∉ s.sideA → Sum.inr () ∈ s.sideB := by
    intro s hs
    have h : Sum.inr () ∈ s.sideA ∪ s.sideB := by
      rw [Split.union_sides]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp h with h' | h'
    · exact absurd h' hs
    · exact h'
  have hnot : ∀ s : Split (Fin n ⊕ Unit), Sum.inr () ∈ s.sideB → Sum.inr () ∉ s.sideA := by
    intro s hs hA
    exact (Finset.disjoint_left.mp (Split.disjoint_sides s)) hA hs
  have himg : (ω.val.filter (fun s => Sum.inr () ∉ s.sideA)).image Split.swap
      = ω.val.filter (fun s => Sum.inr () ∈ s.sideA) := by
    ext t
    constructor
    · intro ht
      obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
      obtain ⟨hsfam, hP⟩ := Finset.mem_filter.mp hs
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [← hst]; exact ω.2.2.2.1 s hsfam
      · rw [← hst, Split.swap_sideA]
        exact hmem s hP
    · intro ht
      obtain ⟨htfam, hQ⟩ := Finset.mem_filter.mp ht
      refine Finset.mem_image.mpr ⟨t.swap, ?_, by rw [Split.swap_swap]⟩
      refine Finset.mem_filter.mpr ⟨ω.2.2.2.1 t htfam, ?_⟩
      rw [Split.swap_sideA]
      exact hnot t.swap (by rw [Split.swap_sideB]; exact hQ)
  have hsame : (ω.val.filter (fun s => Sum.inr () ∉ s.sideA)).card
      = (ω.val.filter (fun s => Sum.inr () ∈ s.sideA)).card := by
    rw [← himg, Finset.card_image_of_injective _ swap_injective_fin]
  have hpart : (ω.val.filter (fun s => Sum.inr () ∉ s.sideA)).card
      + (ω.val.filter (fun s => Sum.inr () ∈ s.sideA)).card = ω.val.card := by
    have h := Finset.card_filter_add_card_filter_not (s := ω.val)
      (p := fun s => Sum.inr () ∉ s.sideA)
    have hneg : (ω.val.filter (fun s => ¬ Sum.inr () ∉ s.sideA))
        = (ω.val.filter (fun s => Sum.inr () ∈ s.sideA)) := by
      refine Finset.filter_congr (fun s _ => ?_)
      simp
    rwa [hneg] at h
  omega


/-! ### 11.11 树 ↦ 族（块 2 的三条「免费」条件 ＋ 只差基数）

要把「拓扑类」装进 §11.7 的载体，需要每个 `n` 叶有根树 `U` 的**非平凡 split 系统**
`U.nontrivialSplits` 落在 `rootedSplitFamily n` 里（四条：相容 / 非平凡 / `swap`-封闭 / 基数）。

* 前三条本节**无条件证掉**：
  - ★★ `compatible_of_mem_nontrivialSplits` —— 同树的 split 两两相容（用
    ★★ `Cladogram.compatible_of_sameQuartetSystem` 取 `T = T'`）；
  - ★★ `sides_card_of_mem_nontrivialSplits` —— 非平凡 ⟺ 两侧各 `≥ 2`（★ `Split.not_isTrivial_iff`）；
  - ★★ `swap_mem_nontrivialSplits` —— `U.isSplitOf_swap` ＋ ★★ `isTrivial_swap`。
* 第四条（**基数** `= 2(n−2)`）**未证** —— 那正是
  「二叉 `m = n+1` 叶树恰 `m−3` 个（无序）非平凡 split」这块计数。
* ★★ `exists_rootedSplitFamily_of_card` 把它写成**唯一前提**：
  给了基数，就得到载体元素，并且 ★★★ `nontrivialSplits_rootedSplitTree` 保证
  `rootedSplitTree` 的 split 系统**还原**它（族 ↦ 树 ↦ 族 = id）。 -/

/-- ★★★ **树给出自身的非平凡 split 系统**：`rootedSplitTree hn ω` 的非平凡 split 系统
**恰为** `ω.val`（族被树精确还原）。这就把 §11.7 的逐点刻画升成 `Finset` 等式。 -/
theorem nontrivialSplits_rootedSplitTree {n : ℕ} (hn : 2 ≤ n) (ω : rootedSplitFamily n) :
    (rootedSplitTree hn ω).nontrivialSplits = ω.val :=
  Cladogram.nontrivialSplits_ofCompatibleSplits_eq ω.val (Sum.inr ())
    ω.2.1 ω.2.2.1 ω.2.2.2.1 (by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
      omega)

/-- ★★ 树的两条非平凡 split **相容**（同树的 split 族两两相容）。 -/
theorem compatible_of_mem_nontrivialSplits {n : ℕ} (U : Cladogram (Fin n ⊕ Unit))
    {s t : Split (Fin n ⊕ Unit)} (hs : s ∈ U.nontrivialSplits)
    (ht : t ∈ U.nontrivialSplits) : Split.Compatible s t := by
  simp only [Cladogram.nontrivialSplits, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  exact Cladogram.compatible_of_sameQuartetSystem (T := U) (T' := U)
    (fun _ _ _ _ _ => Iff.rfl)
    hs.1 ht.1

/-- ★★ 非平凡 split 的两侧各 `≥ 2`。 -/
theorem sides_card_of_mem_nontrivialSplits {n : ℕ} (U : Cladogram (Fin n ⊕ Unit))
    {s : Split (Fin n ⊕ Unit)} (hs : s ∈ U.nontrivialSplits) :
    2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card := by
  simp only [Cladogram.nontrivialSplits, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact (Split.not_isTrivial_iff s).mp hs.2

/-- ★★ 非平凡 split 系统对 `swap` 封闭。 -/
theorem swap_mem_nontrivialSplits {n : ℕ} (U : Cladogram (Fin n ⊕ Unit))
    {s : Split (Fin n ⊕ Unit)} (hs : s ∈ U.nontrivialSplits) :
    s.swap ∈ U.nontrivialSplits := by
  simp only [Cladogram.nontrivialSplits, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact ⟨U.isSplitOf_swap hs.1, fun h => hs.2 ((isTrivial_swap s).mp h)⟩

/-- ★★★ **块 2（只差基数）**：任何 `n` 叶有根树 `U` 的非平凡 split 系统，若基数恰
`2(n−2)`，就是一个 `rootedSplitFamily n` 的元素 —— 且其 `rootedSplitTree` 的 split 系统
**还原**它。

⇒ 本批唯一没证的就是那条**基数**（= 块 1「二叉 `m` 叶树恰 `m−3` 个非平凡 split」）。 -/
theorem exists_rootedSplitFamily_of_card {n : ℕ} (hn : 2 ≤ n) (U : Cladogram (Fin n ⊕ Unit))
    (hcard : U.nontrivialSplits.card = 2 * (n - 2)) :
    ∃ ω : rootedSplitFamily n, ω.val = U.nontrivialSplits ∧
      (rootedSplitTree hn ω).nontrivialSplits = U.nontrivialSplits :=
  ⟨⟨U.nontrivialSplits,
      fun s hs t ht => compatible_of_mem_nontrivialSplits U hs ht,
      fun s hs => sides_card_of_mem_nontrivialSplits U hs,
      fun s hs => swap_mem_nontrivialSplits U hs,
      hcard⟩,
    rfl, by rw [nontrivialSplits_rootedSplitTree]⟩


/-! ### 11.12 块 1：二叉树的 **split 计数**（`|X| − 3` 个非平凡 split）

本节把 §11.11 的「只差基数」补上，从而**块 2 完成**。

计数链条（两步挤压 ＋ 平凡 split 计数）：

* ★★ `card_splits_of_isBinary`：**全部**（有向）split 恰 `4|X| − 6` 条。
  - 下界：★★★ `Cladogram.two_mul_card_edgeFinset_le_card_splits`（每条边给两个有向 split，
    单射由 ★★★ `eq_of_sideLeaves_eq` 保证）＋ ★★ `IsBinary.card_edgeFinset`（`#E = 2ℓ−3`）
    ＋ ★★ `Cladogram.card_leafFinset`（`ℓ = |X|`）⇒ `4|X| − 6 ≤ #S`；
  - 上界：★★★ `Finset.card_add_six_le_four_mul_card_of_pairwise_compatible`
    （`X` 上两两相容族至多 `4|X| − 6` 条）＋ 同树 split 两两相容 ⇒ `#S ≤ 4|X| − 6`。
* ★★ `card_isTrivial_splits`：**平凡**（有向）split 恰 `2|X|` 条
  （`{x}` 一档 `|X|` 条、`{x}ᶜ` 一档 `|X|` 条，两档用 `Split.ext_sideA` 定值、且不相交）。
* ★★ `isSplitOf_of_isTrivial`：平凡 split **必被**任何树展示（叶边）。
* ⇒ ★★★ **`card_nontrivialSplits_of_isBinary`**：`#nontrivialSplits = 2(|X| − 3)`
  （= `|X| − 3` 个无序非平凡 split）。
* ⇒ ★★★ **`nontrivialSplits_mem_rootedSplitFamily`（块 2 完成）**：`m = n+1` ⇒ 基数
  `2(n−2)`，故任何二叉 `n` 叶有根树的非平凡 split 系统**就是** §11.7 载体的一个元素，
  且 ★★★ `nontrivialSplits_rootedSplitTree` 把它还原。

⚠️ **块 3（`Σ_ω rootedSplitWeight ω = 1`）仍未证**，且它**不能**由块 1+2 单独推出：
块 1+2 给的是「族 ↔ 拓扑类」的**双射**（§11.9 的单射 ＋ 本节的击中），
而 `Σ_ω weight ω = 1` 还需要**拓扑侧**的 `S_n := Σ_T 1/g(T) = n!/2^{n−1}`
（等价于「`n` 叶标号历史总数 `= n!(n−1)!/2^{n−1}`」）—— 那是**另一条计数**，
需要在拓扑上做「按 cherry 剥离」的归纳，本批未做。 -/

/-- ★★ **二叉树的（有向）split 数恰为 `4|X| − 6`**。 -/
theorem card_splits_of_isBinary {X : Type} [Fintype X] [DecidableEq X]
    (T : Cladogram X) (hT : T.IsBinary) (h3 : 3 ≤ Fintype.card X) :
    ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card = 4 * Fintype.card X - 6 := by
  classical
  have hE := T.two_mul_card_edgeFinset_le_card_splits
  have hbin := hT.card_edgeFinset
  have hleaf := T.card_leafFinset
  have hlower : 4 * Fintype.card X - 6
      ≤ ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card := by
    omega
  have hupper : ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card
      ≤ 4 * Fintype.card X - 6 := by
    have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    have hup := Finset.card_add_six_le_four_mul_card_of_pairwise_compatible
      ((Finset.univ : Finset (Split X)).filter T.IsSplitOf) (Classical.choice hne)
      (by omega) ?_
    · omega
    · intro s hs t ht _
      obtain ⟨-, hs'⟩ := Finset.mem_filter.mp hs
      obtain ⟨-, ht'⟩ := Finset.mem_filter.mp ht
      exact Cladogram.compatible_of_sameQuartetSystem (T := T) (T' := T)
        (fun _ _ _ _ _ => Iff.rfl) hs' ht'
  omega

/-- ★★ **平凡（有向）split 恰 `2|X|` 个**（`3 ≤ |X|`）：`{x}` 一档 `|X|` 个、`{x}ᶜ` 一档 `|X|` 个。 -/
theorem card_isTrivial_splits {X : Type} [Fintype X] [DecidableEq X]
    (h3 : 3 ≤ Fintype.card X) :
    ((Finset.univ : Finset (Split X)).filter (fun s => s.IsTrivial)).card
      = 2 * Fintype.card X := by
  classical
  have hne : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hcompl : ∀ x : X, ({x} : Finset X)ᶜ.Nonempty := by
    intro x
    apply compl_nonempty_of_ne_univ
    intro h
    have : ({x} : Finset X).card = Fintype.card X := by rw [h, Finset.card_univ]
    simp at this
    omega
  let f : X → Split X := fun x => splitOf ({x} : Finset X) (Finset.singleton_nonempty x) (hcompl x)
  have hf : ∀ x : X, (f x).sideA = {x} := fun x => splitOf_sideA _ _ _
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : ({x} : Finset X) = {y} := by rw [← hf x, ← hf y, hxy]
    simpa using h1
  have hswap_inj : Function.Injective (fun x : X => (f x).swap) := by
    intro x y hxy
    apply hf_inj
    have h := congrArg Split.swap hxy
    simpa [Split.swap_swap] using h
  have hset : (Finset.univ : Finset (Split X)).filter (fun s => s.IsTrivial)
      = (Finset.univ.image f) ∪ (Finset.univ.image (fun x => (f x).swap)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨-, htr⟩ := Finset.mem_filter.mp hs
      rcases htr with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨x, Finset.mem_univ x, (Split.ext_sideA (by rw [hf x, hx])).symm⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨x, Finset.mem_univ x, (Split.ext_sideA (by
            rw [Split.swap_sideA, splitOf_sideB, hx])).symm⟩))
    · intro hs
      rcases Finset.mem_union.mp hs with h | h
      · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨x, hf x⟩⟩
      · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨x, by
          rw [Split.swap_sideA, splitOf_sideB]⟩⟩
  rw [hset]
  have hdisj : Disjoint (Finset.univ.image f) (Finset.univ.image (fun x => (f x).swap)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hs1
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hs2
    have h1 : ({x} : Finset X) = ({y} : Finset X)ᶜ := by
      rw [← hf x, hx, ← hy, Split.swap_sideA, splitOf_sideB]
    have h2 : ({x} : Finset X).card = Fintype.card X - 1 := by
      rw [h1, Finset.card_compl, Finset.card_singleton]
    simp at h2
    omega
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hf_inj,
    Finset.card_image_of_injective _ hswap_inj, Finset.card_univ]
  omega

/-- ★★ **平凡 split 必被任何树展示**（`Nontrivial X`）。 -/
theorem isSplitOf_of_isTrivial {X : Type} [Fintype X] [DecidableEq X] [Nontrivial X]
    (T : Cladogram X) {s : Split X} (hs : s.IsTrivial) : T.IsSplitOf s := by
  rcases hs with ⟨x, hx⟩ | ⟨x, hx⟩
  · obtain ⟨s', hs', hs'A⟩ := T.exists_isSplitOf_singleton x
    exact (Split.ext_sideA (hs'A.trans hx.symm)).symm ▸ hs'
  · obtain ⟨s', hs', hs'A⟩ := T.exists_isSplitOf_singleton x
    have hgoal : (s'.swap).sideA = s.sideA := by
      rw [Split.swap_sideA, Split.sideB_eq_sdiff, hs'A, hx, Finset.compl_eq_univ_sdiff]
    exact (Split.ext_sideA hgoal).symm ▸ T.isSplitOf_swap hs'

/-- ★★★ **二叉树恰有 `2(|X| − 3)` 个有向非平凡 split**（= `|X| − 3` 个无序）。 -/
theorem card_nontrivialSplits_of_isBinary {X : Type} [Fintype X] [DecidableEq X]
    (T : Cladogram X) (hT : T.IsBinary) (h3 : 3 ≤ Fintype.card X) :
    T.nontrivialSplits.card = 2 * (Fintype.card X - 3) := by
  classical
  have hnt : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hnontriv : T.nontrivialSplits.card
      + ((Finset.univ : Finset (Split X)).filter (fun s => s.IsTrivial)).card
      = ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Split X)).filter T.IsSplitOf)
      (p := fun s => s.IsTrivial)
    -- 化简两边
    have h1 : ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).filter
        (fun s => ¬ s.IsTrivial) = T.nontrivialSplits := by
      rw [Cladogram.nontrivialSplits, Finset.filter_filter]
    have h2 : ((Finset.univ : Finset (Split X)).filter T.IsSplitOf).filter
        (fun s => s.IsTrivial)
        = (Finset.univ : Finset (Split X)).filter (fun s => s.IsTrivial) := by
      refine Finset.Subset.antisymm ?_ ?_
      · exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
      · intro s hs
        obtain ⟨-, htr⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, @isSplitOf_of_isTrivial X _ _ hnt T s htr⟩, htr⟩
    rw [h1, h2] at hpart
    omega
  have hS := card_splits_of_isBinary T hT h3
  have htr := card_isTrivial_splits (X := X) h3
  omega

/-- ★★★ **块 2（完成）**：任何 
 叶**二叉**有根树 U 的非平凡 split 系统都落在载体

ootedSplitFamily n 里，且 
ootedSplitTree 还原它。 -/
theorem nontrivialSplits_mem_rootedSplitFamily {n : ℕ} (hn : 2 ≤ n)
    (U : Cladogram (Fin n ⊕ Unit)) (hU : U.IsBinary) :
    ∃ ω : rootedSplitFamily n, ω.val = U.nontrivialSplits ∧
      (rootedSplitTree hn ω).nontrivialSplits = U.nontrivialSplits := by
  have h3 : 3 ≤ Fintype.card (Fin n ⊕ Unit) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hcard := card_nontrivialSplits_of_isBinary U hU h3
  have hV : Fintype.card (Fin n ⊕ Unit) = n + 1 := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [hV] at hcard
  have htarget : U.nontrivialSplits.card = 2 * (n - 2) := by omega
  exact exists_rootedSplitFamily_of_card hn U htarget


/-! ### 11.13 块 3 的**基例**（`n = 2`）：`Σ_ω rootedSplitWeight ω = 1`

载体 `rootedSplitFamily 2` 是单点集（§11.7 的 `rootedSplitFamily_two_card`），唯一元素是空族，
其权 `2^1/(2!·1) = 1` ⇒ 和恰为 `1`。

★ 这条的意义：`Σ_ω weight ω = 1` 在基例上**成立且非空转**，故它确实是对的命题
（不是 `0 = 1`）。一般 `n` 的情形见 §11.12 末尾的说明（缺拓扑侧计数）。 -/

/-- 载体在 `n = 2` 时的唯一元素是空族。 -/
theorem rootedSplitFamily_two_val_eq_empty (x : rootedSplitFamily 2) : x.val = ∅ := by
  apply Finset.card_eq_zero.mp
  calc x.val.card = 2 * (2 - 2) := x.2.2.2.2
    _ = 0 := by norm_num

/-- ★★★ **块 3 在 `n = 2` 的实例**：`Σ_ω rootedSplitWeight ω = 1`
（载体只有一个元素 = 空族，其权 `2^1/(2!·1) = 1`）。

这是 `Σ_ω weight ω = 1` 的**基例**，也说明该式在 `n = 2` 上**不是**空转命题。 -/
theorem sum_rootedSplitWeight_two :
    ∑ ω : rootedSplitFamily 2, rootedSplitWeight ω = 1 := by
  classical
  obtain ⟨ω₀⟩ := rootedSplitFamily_two_nonempty
  have hmem : ∀ x : rootedSplitFamily 2, x.val = ∅ := rootedSplitFamily_two_val_eq_empty
  have huniv : (Finset.univ : Finset (rootedSplitFamily 2)) = {ω₀} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun x _ =>
      Subtype.ext (by rw [hmem x, hmem ω₀])⟩
  rw [huniv, Finset.sum_singleton]
  have hval : ω₀.val = ∅ := hmem ω₀
  unfold rootedSplitWeight
  rw [hval, Finset.filter_empty, Finset.prod_empty, Nat.mul_one]
  unfold yhkRootWeight
  norm_num


/-! ### 11.14 根分裂分解（第 1 步）：clade 抽取 `awayLeaves` ＋ 基例

**目标分解式（下一轮的靶子）**。记 `c n := Fintype.card (rootedSplitFamily n)`。
有根树的根 = `ρ = Sum.inr ()` 的唯一邻居，它的两棵子树叶集 `A`、`Aᶜ` 给出**根分裂**，故

```text
2 · c n = ∑ a ∈ Ico 1 n, C(n,a) · c a · c (n − a)        (★ 取「定向」根分裂)
```

⚠️ **因子口径**：若只写 `∑_a (C(n,a)/2)·c a·c(n−a)`，则 `a ≠ n−a` 时**重复计数**
（`{A,Aᶜ}` 会以 `|A| = a` 与 `|A| = n−a` 各出现一次，而 `c a·c(n−a)` 与 `c(n−a)·c a` 是**不同**的配对）。
`(★)` 用「定向」（有序 `(A, Aᶜ)`，且每个 `ω` 恰有 **2** 个定向分解 —— 根的两个孩子可互换）避免了半边，
**乘以 2 正好补偿**。这与 §11.1 的权重递推 `S_n = (1/(2(n−1)))·∑_a C(n,a)·S_a·S_{n−a}` 是**同一条**。

**本节交付的是分解的「clade 抽取」那一半**（`ω ↦ 它的全部 clade`）：

* ★★★ `awayLeaves`：split 的 **away 真叶集**（不含 `ρ` 的那一侧的真叶集）= 有根树的一个 clade；
* ★★ `awayLeaves_eq_iff`：**两条 split 的 away 侧相同 ⟺ 它们相等或互为换向** ——
  即 `awayLeaves` 在族上是 **2 对 1**（`s` 与 `s.swap` 同像），这正是「每条无向 split 恰给一个 clade」；
* ★★ `awayLeaves_nonempty` / `awayLeaves_compl_nonempty`：clade 与其补都非空（真子集）；
* ★★★ `card_image_awayLeaves`：**`#(ω 的 clade 集) = n − 2`**
  （有根二叉 `n` 叶树的 proper clade 恰 `n−2` 个 = 非根内部顶点数）；
* ★★ `rootedSplitFamily_card_of_le_two`：>基例 `c 0 = c 1 = c 2 = 1`（`n ≤ 2` 时载体是单点集，
  唯一元素是空族）—— 递推 `(★)` 的底座；
* ★ `exists_inl_of_two_le_card`：`2 ≤ #T` 的 `T ⊆ Fin n ⊕ Unit` 必含真叶（辅助）。

**没做的那一半**：把 `ω` 拆成「根分裂 `(A, Aᶜ)` ＋ `ω_A ∈ Ω_|A|` ＋ `ω_B ∈ Ω_|B|`」以及反向的**嫁接**。
卡点在**载体运输**：子族住在 `Cladogram (A ⊕ Unit)` 上，而 `rootedSplitFamily a` 说的是
`Split (Fin a ⊕ Unit)`；库内**没有** `Cladogram`/`Split` 沿 `A ≃ Fin |A|` 的运输 API
（`Cladogram.V : Type*` 任意），故 `Ω_A ≃ Ω_|A|` 这一句先要自建 `~50–80` 行的运输层。
有了运输层，`(★)` 的证明骨架是：`ω ↦ (away 极大元对, 两个子族)` 双向 ＋
★★★ `card_image_awayLeaves` 保证「clade 数对」，★★★ `nontrivialSplits_rootedSplitTree`(:3261) 保证还原。 -/

/-! ## 基例：`n ≤ 2` 的载体都是单点 -/

theorem rootedSplitFamily_card_of_le_two {n : ℕ} (hn : n ≤ 2) :
    Fintype.card (rootedSplitFamily n) = 1 := by
  have h0 : n - 2 = 0 := by omega
  have hempty : ∀ x : rootedSplitFamily n, x.val = ∅ := by
    intro x
    apply Finset.card_eq_zero.mp
    calc x.val.card = 2 * (n - 2) := x.2.2.2.2
      _ = 0 := by rw [h0]
  have hnon : Nonempty (rootedSplitFamily n) :=
    ⟨⟨∅, by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [h0]⟩⟩
  have hle : Fintype.card (rootedSplitFamily n) ≤ 1 := by
    rw [Fintype.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext ((hempty a).trans (hempty b).symm)⟩
  have hpos : 0 < Fintype.card (rootedSplitFamily n) := Fintype.card_pos_iff.mpr hnon
  omega

/-- ★ `Fin n ⊕ Unit` 里一个大集合必含真叶（`2 ≤ card`）。 -/
theorem exists_inl_of_two_le_card {n : ℕ} {T : Finset (Fin n ⊕ Unit)} (h : 2 ≤ T.card) :
    ∃ x : Fin n, Sum.inl x ∈ T := by
  by_contra hc
  have hc' : ∀ x : Fin n, Sum.inl x ∉ T := fun x hx => hc ⟨x, hx⟩
  have hsub : T ⊆ {Sum.inr ()} := by
    intro y hy
    rcases y with x | u
    · exact absurd hy (hc' x)
    · cases u
      exact Finset.mem_singleton_self _
  have hcard := Finset.card_le_card hsub
  simp at hcard
  omega

/-! ## away 侧（clade 抽取） -/

/-- ★★ split 的 **away 真叶集**（不含 `ρ = Sum.inr ()` 那一侧的真叶集）。 -/
noncomputable def awayLeaves {n : ℕ} (s : Split (Fin n ⊕ Unit)) : Finset (Fin n) :=
  realLeaves (s.away (Sum.inr ()))

/-- ★ away 侧恰是 away 真叶集的原像（`away` 侧不含 `ρ`）。 -/
theorem away_eq_image_awayLeaves {n : ℕ} (s : Split (Fin n ⊕ Unit)) :
    s.away (Sum.inr ()) = (awayLeaves s).image Sum.inl := by
  ext y
  rcases y with x | u
  · simp only [awayLeaves, Finset.mem_image, mem_realLeaves]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨x', hx', h⟩ => by
      rw [← Sum.inl.inj h]; exact hx'⟩
  · cases u
    constructor
    · intro h
      exact absurd h (Split.not_mem_away _ _)
    · intro h
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
      exact absurd ha (by simp)

/-- ★ `awayLeaves` 对换向不变。 -/
theorem awayLeaves_swap {n : ℕ} (s : Split (Fin n ⊕ Unit)) :
    awayLeaves s.swap = awayLeaves s := by
  simp only [awayLeaves, Split.away_swap]

/-- ★★ **away 侧相同的两条 split 只差换向**。 -/
theorem awayLeaves_eq_iff {n : ℕ} {s t : Split (Fin n ⊕ Unit)} :
    awayLeaves s = awayLeaves t ↔ s = t ∨ s = t.swap := by
  have key : ∀ {a b : Split (Fin n ⊕ Unit)},
      awayLeaves a = awayLeaves b → a.sideA = b.sideA ∨ a.sideA = b.sideAᶜ := by
    intro a b h
    have hu : a.away (Sum.inr ()) = b.away (Sum.inr ()) := by
      rw [away_eq_image_awayLeaves, away_eq_image_awayLeaves, h]
    by_cases ha : Sum.inr () ∈ a.sideA <;> by_cases hb : Sum.inr () ∈ b.sideA
    · left
      rw [Split.away_of_mem _ ha, Split.away_of_mem _ hb, Split.sideB_eq_compl,
        Split.sideB_eq_compl] at hu
      simpa using congrArg (fun s : Finset (Fin n ⊕ Unit) => sᶜ) hu
    · right
      rw [Split.away_of_mem _ ha, Split.away_of_notMem _ hb, Split.sideB_eq_compl] at hu
      rw [← hu]
      simp
    · right
      rw [Split.away_of_notMem _ ha, Split.away_of_mem _ hb, Split.sideB_eq_compl] at hu
      exact hu
    · left
      rw [Split.away_of_notMem _ ha, Split.away_of_notMem _ hb] at hu
      exact hu
  constructor
  · intro h
    rcases key h with h1 | h1
    · exact Or.inl (Split.ext_sideA h1)
    · refine Or.inr (Split.ext_sideA ?_)
      rw [Split.swap_sideA, Split.sideB_eq_compl]
      exact h1
  · rintro (rfl | h)
    · rfl
    · rw [h, awayLeaves_swap]

/-- ★★ `awayLeaves` 非空。 -/
theorem awayLeaves_nonempty {n : ℕ} (s : Split (Fin n ⊕ Unit)) :
    (awayLeaves s).Nonempty := by
  obtain ⟨y, hy⟩ := s.away_nonempty (Sum.inr ())
  have hne : y ≠ Sum.inr () := by
    have h := s.away_subset (Sum.inr ()) hy
    simpa using h
  rcases y with x | u
  · exact ⟨x, by simp only [awayLeaves, mem_realLeaves]; exact hy⟩
  · cases u
    exact absurd rfl hne

/-- ★★ 族的成员（非平凡）其 `awayLeaves` 的补也非空。 -/
theorem awayLeaves_compl_nonempty {n : ℕ} (ω : rootedSplitFamily n)
    {s : Split (Fin n ⊕ Unit)} (hs : s ∈ ω.val) : (awayLeaves s)ᶜ.Nonempty := by
  have h2 := ω.2.2.1 s hs
  by_cases hρ : Sum.inr () ∈ s.sideA
  · have hu : awayLeaves s = realLeaves s.sideB := by
      simp only [awayLeaves, Split.away_of_mem _ hρ]
    obtain ⟨x, hx⟩ := exists_inl_of_two_le_card h2.1
    refine ⟨x, ?_⟩
    simp only [Finset.mem_compl, hu, mem_realLeaves]
    intro hmem
    exact (Finset.disjoint_left.mp (Split.disjoint_sides s)) hx hmem
  · have hu : awayLeaves s = realLeaves s.sideA := by
      simp only [awayLeaves, Split.away_of_notMem _ hρ]
    obtain ⟨x, hx⟩ := exists_inl_of_two_le_card h2.2
    refine ⟨x, ?_⟩
    simp only [Finset.mem_compl, hu, mem_realLeaves]
    intro hmem
    exact (Finset.disjoint_left.mp (Split.disjoint_sides s)) hmem hx

/-- ★★★ **有根二叉 
 叶树的 proper clade 恰 
 − 2 个**（= #ω.val / 2）：
wayLeaves 在族上是 **2 对 1** 的（s 与 s.swap 同像，wayLeaves_eq_iff）。 -/
theorem card_image_awayLeaves {n : ℕ} (ω : rootedSplitFamily n) :
    (ω.val.image awayLeaves).card = n - 2 := by
  classical
  have hfib : ∀ x ∈ ω.val.image awayLeaves,
      (ω.val.filter (fun s => awayLeaves s = x)).card = 2 := by
    intro x hx
    obtain ⟨s₀, hs₀, hs₀x⟩ := Finset.mem_image.mp hx
    have hset : ω.val.filter (fun s => awayLeaves s = x) = {s₀, s₀.swap} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, ht⟩
        rcases awayLeaves_eq_iff.mp (ht.trans hs₀x.symm) with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hs₀, hs₀x⟩
        · exact ⟨ω.2.2.2.1 s₀ hs₀, by rw [awayLeaves_swap, hs₀x]⟩
    have hne : s₀ ≠ s₀.swap := by
      intro h
      have h1 : s₀.sideA = s₀.sideB := by
        have := congrArg Split.sideA h
        simpa [Split.swap_sideA] using this
      obtain ⟨y, hy⟩ := s₀.nonempty 0
      have hy' : y ∈ s₀.sideB := h1 ▸ hy
      exact (Finset.disjoint_left.mp (Split.disjoint_sides s₀)) hy hy'
    rw [hset, Finset.card_pair hne]
  have hsum := Finset.card_eq_sum_card_image (awayLeaves) ω.val
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : ω.val.card = 2 * (n - 2) := ω.2.2.2.2
  have hsum2 : (ω.val.image awayLeaves).card * 2 = ω.val.card := hsum.symm
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h0 : n - 2 = 0 := by omega
    have hc : ω.val.card = 0 := by omega
    have hzero : (ω.val.image awayLeaves).card = 0 := by omega
    omega
  · have hc : ω.val.card = 2 * n - 4 := by omega
    omega


/-! ### 11.15 **载体运输层**（`Split` 沿等价）——下一轮「子族抽取」的前置器材

§11.14 差的那一半是「把 `ω` 拆成 `(根分裂, ω_A, ω_B)`」。子族住在 `Split (A ⊕ Unit)` 上
（`A : Finset (Fin n)` 是子类型），而载体 `rootedSplitFamily a` 说的是 `Split (Fin a ⊕ Unit)`；
本节的运输层就是补这两者之间的桥（即「`Ω_A ≃ Ω_|A|`」）。

* ★★★ `Split.congrFun` / `Split.congr`（`Equiv` 形态）：`KPartition` 的 `parts` 逐点取
  `Finset.image e`（相容 / 覆盖 / 非空三条字段逐条搬运）；取值引理
  ★★ `congrFun_sideA`、★★ `congrFun_sideB`、★★ `congrFun_swap`（`swap` 与传输交换）、
  ★★ `congrFun_symm_congrFun` / `congrFun_congrFun_symm`（往返）、
  ★★ `congr_sideA` / `congr_sideB` / `congr_swap` / `congr_congr_symm`（`Equiv` 形态的取值式）。
  ★ 做法上避开「硬证 `Equiv` 往返」：先证**取值式**往返（`sideA` 的 `image_image` ＋
  `Equiv.symm_apply_apply`），再用 ★★ `Split.ext_sideA` 升级成 split 相等。
* ★★ `disjoint_image_equiv` / ★★ `compatible_congrFun`：相容性沿等价保持（四支逐一搬运）；
* ★★★ `rootedSplitSet β`：**任意有限叶类型**上的载体（`rootedSplitFamily n` 的推广，
  把 `n` 换成 `Fintype.card β`），带 ★★ `rootedSplitSetFintype`；
* ★★★ `rootedSplitSetCongr` / `rootedSplitSetEquiv`：载体沿 `(β ⊕ Unit) ≃ (γ ⊕ Unit)` 运输
  （`fam ↦ fam.image (Split.congr E)`，四条载体条件逐条搬运）；
* ★★★ `card_rootedSplitSet`：**载体基数不随叶类型改变**；★★ `card_rootedSplitSet_fin`：
  特化到 `#(rootedSplitSet β) = #(rootedSplitSet (Fin #β))`。

⚠️ 下一轮用它时注意：`rootedSplitSet (Fin n)` 与 `rootedSplitFamily n` 只差索引写法
（`Fintype.card (Fin n)` vs `n`），两者**不是** `rfl` 相等，按需 `unfold` 后 `rw [Fintype.card_fin]`。 -/

namespace Split

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- ★★★ **`split` 沿等价的传输**（`parts` 逐点取 `Finset.image e`）。 -/
noncomputable def congrFun (e : α ≃ β) (s : Split α) : Split β where
  parts := fun i => (s.parts i).image e
  pairwise_disjoint := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨a, ha, rfl⟩ := hx1
    obtain ⟨b, hb, hba⟩ := hx2
    exact (Finset.disjoint_left.mp (s.pairwise_disjoint i j hij)) ha (e.injective hba ▸ hb)
  union_eq_univ := by
    rw [Finset.eq_univ_iff_forall]
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    have ha : a ∈ Finset.univ.biUnion s.parts := by
      rw [s.union_eq_univ]; exact Finset.mem_univ a
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem e hi⟩
  nonempty := fun i => Finset.image_nonempty.mpr (s.nonempty i)

/-- ★★ 取值式：`sideA` 就是 `image e`。 -/
theorem congrFun_sideA (e : α ≃ β) (s : Split α) :
    (congrFun e s).sideA = s.sideA.image e := rfl

/-- ★★ 取值式：`sideB` 就是 `image e`。 -/
theorem congrFun_sideB (e : α ≃ β) (s : Split α) :
    (congrFun e s).sideB = s.sideB.image e := rfl

/-- ★★ 取值式：传输与换向交换。 -/
theorem congrFun_swap (e : α ≃ β) (s : Split α) :
    (congrFun e s).swap = congrFun e s.swap := by
  refine Split.ext_sideA ?_
  rw [Split.swap_sideA, congrFun_sideB, congrFun_sideA, Split.swap_sideA]

/-- ★★ 往返（`e.symm` 后传回）等于原 split。 -/
theorem congrFun_symm_congrFun (e : α ≃ β) (s : Split α) :
    congrFun e.symm (congrFun e s) = s := by
  refine Split.ext_sideA ?_
  rw [congrFun_sideA, congrFun_sideA, Finset.image_image]
  have hcomp : (⇑e.symm ∘ ⇑e) = id := funext (fun a => Equiv.symm_apply_apply e a)
  rw [hcomp, Finset.image_id]

/-- ★★ 往返（`e` 后传回）等于原 split。 -/
theorem congrFun_congrFun_symm (e : α ≃ β) (t : Split β) :
    congrFun e (congrFun e.symm t) = t := by
  refine Split.ext_sideA ?_
  rw [congrFun_sideA, congrFun_sideA, Finset.image_image]
  have hcomp : (⇑e ∘ ⇑e.symm) = id := funext (fun b => Equiv.apply_symm_apply e b)
  rw [hcomp, Finset.image_id]

/-- ★★★ **`split` 沿等价的传输**（`Equiv` 形态）。 -/
noncomputable def congr (e : α ≃ β) : Split α ≃ Split β where
  toFun := congrFun e
  invFun := congrFun e.symm
  left_inv := congrFun_symm_congrFun e
  right_inv := congrFun_congrFun_symm e

/-- ★★ 取值式：`(congr e s).sideA = s.sideA.image e`。 -/
theorem congr_sideA (e : α ≃ β) (s : Split α) :
    (congr e s).sideA = s.sideA.image e := rfl

/-- ★★ 取值式：`(congr e s).sideB = s.sideB.image e`。 -/
theorem congr_sideB (e : α ≃ β) (s : Split α) :
    (congr e s).sideB = s.sideB.image e := rfl

/-- ★★ 取值式：`congr` 与 `swap` 交换。 -/
theorem congr_swap (e : α ≃ β) (s : Split α) :
    (congr e s).swap = congr e s.swap := congrFun_swap e s

/-- ★★ 取值式：`congr e` 与 `congr e.symm` 互逆（左）。 -/
theorem congr_congr_symm (e : α ≃ β) (s : Split α) :
    congr e.symm (congr e s) = s := congrFun_symm_congrFun e s

end Split

/-- ★★ 不交集的像不交（`e` 单射）。 -/
theorem disjoint_image_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {A B : Finset α} (h : Disjoint A B) :
    Disjoint (A.image e) (B.image e) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx1 hx2
  rw [Finset.mem_image] at hx1 hx2
  obtain ⟨a, ha, rfl⟩ := hx1
  obtain ⟨b, hb, hba⟩ := hx2
  exact h ha (e.injective hba ▸ hb)

/-- ★★ 相容性沿等价保持。 -/
theorem compatible_congrFun {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {s t : Split α} (h : Split.Compatible s t) :
    Split.Compatible (Split.congrFun e s) (Split.congrFun e t) := by
  rw [Split.Compatible]
  rw [Split.congrFun_sideA, Split.congrFun_sideA, Split.congrFun_sideB, Split.congrFun_sideB]
  rcases h with h | h | h | h
  · exact Or.inl (disjoint_image_equiv e h)
  · exact Or.inr (Or.inl (disjoint_image_equiv e h))
  · exact Or.inr (Or.inr (Or.inl (disjoint_image_equiv e h)))
  · exact Or.inr (Or.inr (Or.inr (disjoint_image_equiv e h)))

/-- ★★★ **任意有限叶类型上的载体**（`Fin n` 版 `rootedSplitFamily n` 的推广）。 -/
abbrev rootedSplitSet (β : Type) [Fintype β] [DecidableEq β] : Type :=
  { fam : Finset (Split (β ⊕ Unit)) //
      (∀ s ∈ fam, ∀ t ∈ fam, Split.Compatible s t) ∧
      (∀ s ∈ fam, 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) ∧
      (∀ s ∈ fam, s.swap ∈ fam) ∧
      fam.card = 2 * (Fintype.card β - 2) }

/-- ★★ **`rootedSplitSet` 是有限类型**。 -/
noncomputable instance rootedSplitSetFintype (β : Type) [Fintype β] [DecidableEq β] :
    Fintype (rootedSplitSet β) := by
  classical
  exact Subtype.fintype _

/-- ★★★ **载体沿（叶集上的）等价运输**：`fam ↦ fam.image (Split.congr E)`。 -/
noncomputable def rootedSplitSetCongr {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (E : (β ⊕ Unit) ≃ (γ ⊕ Unit)) :
    rootedSplitSet β → rootedSplitSet γ := by
  classical
  intro ω
  refine ⟨ω.val.image (fun s => Split.congr E s), ?_, ?_, ?_, ?_⟩
  · intro s hs t ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    exact compatible_congrFun E (ω.2.1 s' hs' t' ht')
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    have h := ω.2.2.1 s' hs'
    have h1 : ((Split.congr E s').sideA).card = s'.sideA.card := by
      rw [Split.congr_sideA, Finset.card_image_of_injective _ E.injective]
    have h2 : ((Split.congr E s').sideB).card = s'.sideB.card := by
      rw [Split.congr_sideB, Finset.card_image_of_injective _ E.injective]
    rw [h1, h2]
    exact h
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨s'.swap, ω.2.2.2.1 s' hs', (Split.congr_swap E s').symm⟩
  · have hcard : Fintype.card β = Fintype.card γ := by
      have h := Fintype.card_congr E
      simp only [Fintype.card_sum, Fintype.card_unit] at h
      omega
    rw [Finset.card_image_of_injective _ (Split.congr E).injective, ω.2.2.2.2, hcard]

/-- ★★★ **载体沿叶集等价的 `Equiv`**。 -/
noncomputable def rootedSplitSetEquiv {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (E : (β ⊕ Unit) ≃ (γ ⊕ Unit)) :
    rootedSplitSet β ≃ rootedSplitSet γ where
  toFun := rootedSplitSetCongr E
  invFun := rootedSplitSetCongr E.symm
  left_inv := by
    intro ω
    refine Subtype.ext ?_
    show (ω.val.image (fun s => Split.congr E s)).image (fun s => Split.congr E.symm s) = ω.val
    rw [Finset.image_image]
    have hcomp : ((fun s => Split.congr E.symm s) ∘ (fun s => Split.congr E s)) = id := by
      funext s
      exact Split.congr_congr_symm E s
    rw [hcomp, Finset.image_id]
  right_inv := by
    intro ω
    refine Subtype.ext ?_
    show (ω.val.image (fun s => Split.congr E.symm s)).image (fun s => Split.congr E s) = ω.val
    rw [Finset.image_image]
    have hcomp : ((fun s => Split.congr E s) ∘ (fun s => Split.congr E.symm s)) = id := by
      funext s
      exact Split.congrFun_congrFun_symm E s
    rw [hcomp, Finset.image_id]

/-- ★★★ **载体基数不随叶类型改变**（叶集等价 ⇒ 载体等基数）。
（下一轮「子族住在 `A ⊆ Fin n` 上」要用它把 `Ω_A` 认成 `Ω_|A|`；
`rootedSplitSet (Fin n)` 与 `rootedSplitFamily n` 只差索引写法。） -/
theorem card_rootedSplitSet {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (E : (β ⊕ Unit) ≃ (γ ⊕ Unit)) :
    Fintype.card (rootedSplitSet β) = Fintype.card (rootedSplitSet γ) :=
  Fintype.card_congr (rootedSplitSetEquiv E)

/-- ★★ **特化到 `Fin`**：`#(rootedSplitSet β) = #(rootedSplitSet (Fin #β))`。 -/
theorem card_rootedSplitSet_fin {β : Type} [Fintype β] [DecidableEq β] :
    Fintype.card (rootedSplitSet β) = Fintype.card (rootedSplitSet (Fin (Fintype.card β))) :=
  card_rootedSplitSet (Equiv.sumCongr (Fintype.equivFin β) (Equiv.refl Unit))


/-! ### 11.16 桥：`rootedSplitSet (Fin n)` ＝ `rootedSplitFamily n`

两者只差索引写法（`Fintype.card (Fin n)` vs `n`），需要 `unfold` 后 `rw [Fintype.card_fin]`
（直接 `rw`/`simpa` 会因依赖类型失败 —— 五轮留的坑，在此闭环）。 -/

/-- ★★★ **桥：`rootedSplitSet (Fin n)` 与 `rootedSplitFamily n` 相等**（只差索引写法
`Fintype.card (Fin n)` vs `n`）。 -/
theorem rootedSplitSet_fin_eq_rootedSplitFamily (n : ℕ) :
    rootedSplitSet (Fin n) = rootedSplitFamily n := by
  unfold rootedSplitSet rootedSplitFamily
  rw [Fintype.card_fin]

/-- ★★★ **基数桥**：`#(rootedSplitFamily n) = #(rootedSplitSet (Fin n))`。 -/
theorem card_rootedSplitFamily_eq_rootedSplitSet (n : ℕ) :
    Fintype.card (rootedSplitFamily n) = Fintype.card (rootedSplitSet (Fin n)) :=
  Fintype.card_congr (Equiv.cast (rootedSplitSet_fin_eq_rootedSplitFamily n)).symm

/-- ★★★ **两者的 `Equiv`**（下一轮把子族按 `A` 认成按 `Fin |A|` 时直接用）。 -/
noncomputable def rootedSplitSetFinEquivFamily (n : ℕ) :
    rootedSplitSet (Fin n) ≃ rootedSplitFamily n :=
  Equiv.cast (rootedSplitSet_fin_eq_rootedSplitFamily n)


/-! ### 11.17 子族抽取 ＋ 嫁接的**逐字规格**（下一轮照此实现即可）

器材已齐（本节只加 `inlEmbed` 及其两条基本性质）。下面把「块 2 ＋ 块 3」写成规格。

**记号**：`ω ∈ rootedSplitFamily n`；`ρ = Sum.inr ()`；`cladeSet ω := ω.val.image awayLeaves`
（§11.14，`card = n − 2`，且 `s ↦ awayLeaves s` 在 `ω.val` 上是 2 对 1，见 ★★ `awayLeaves_eq_iff`）。

**① 极大 clade 与根分裂**
```text
A := cladeSet ω 的一个 ⊆-极大元            （LaminarFamily ＋ Finset.exists_subset_maximal_member）
根分裂 := 无序对 {A, Aᶜ}                    （二叉树的根恰两个孩子；需证 Aᶜ ∈ cladeSet ω）
```
**② 子族抽取（限制）**
```text
ω_A := (ω.val.filter (fun s => awayLeaves s ⊆ A)).image (restrictToFinset A)
       —— restrictToFinset A s h : Split (A ⊕ Unit)，h : awayLeaves s ⊆ A
       —— 定义：B := {y : A ⊕ Unit | inlEmbed A y ∈ s.away ρ}，取 splitOf B
       —— 关键事实：away 侧 ⊆ A ∪ {ρ}（away 真叶集 ⊆ A 且 ρ ∉ away）⇒ away 侧 = B 的原像
ω_B := 同法（A 换成 Aᶜ）
```
要证（`rootedSplitSet A` 的四条件）：
* **相容**：`Split.Compatible` 在限制下保持（把四个「交为空」逐支下推，`inlEmbed` 单射）；
* **非平凡**：`2 ≤ sideA.card ∧ 2 ≤ sideB.card` —— 由 `ω` 的非平凡 ＋ 限制不减基数（限制是单射的像）；
* **swap-闭**：★★ `restrictToFinset_swap`（限制对换向不变：`s` 与 `s.swap` 限制到同一条）⇒ 2 对 1；
* **基数 `2(|A| − 2)`**：`#(ω_A) = 2 · #(cladeSet ω 中 ⊊ A 的元)`，再证后者 = `|A| − 2`。
  ⚠️ 这是本块**唯一非机械**的一步：等价于「子树上 proper clade 数 = 叶数 − 2」。
  两条可行路线：(a) 用 `Phylo/SideSubtree.lean` 的 `sideVertices`/`induce`/`isTree_induce_sideVertices`
  把子树做成 `Cladogram A`，再套 ★★★ `card_nontrivialSplits_of_isBinary`（`:3433`）与
  ★★★ `card_image_awayLeaves`（`:3682`）；(b) 对 laminar 族做「每个非极小元恰有两个极大真子元」的结构归纳。

**③ 嫁接（反向）**
```text
给定 A（A.Nonempty, Aᶜ.Nonempty）、ω_A ∈ rootedSplitSet A、ω_B ∈ rootedSplitSet Aᶜ：
  lift_A : Split (A ⊕ Unit) → Split (Fin n ⊕ Unit)      —— sideA := (image Sum.inl of ω_A's away side)
  ρ-split := splitOf (A.image Sum.inl)                  —— {A ∪ {ρ} | Aᶜ}
  ω := (lift_A '' ω_A) ∪ (lift_B '' ω_B) ∪ {ρ-split, ρ-split.swap}
```
要证：`ω ∈ rootedSplitFamily n`（四条件）＋ 基数算术
`2(|A|−2) + 2(|Aᶜ|−2) + 2 = 2(n−2)`（用 `|A| + |Aᶜ| = n`，定向式，**不除 2**）。

**④ 互逆 ＋ 递推**
```text
decompose ∘ glue = id、glue ∘ decompose = id
⇒ 2 · c n = ∑ a ∈ Ico 1 n, C(n,a) · c a · c (n − a)        （c n := #(rootedSplitFamily n)）
```
（因子口径：**定向式**，见 §11.14 与五轮报告；每个 `ω` 恰有 2 个定向分解。）

⚠️ **本盒的进度**：块 1 完成（§11.16）；块 2 只交了 `inlEmbed` ＋ 本规格；
`restrictToFinset` 的定义在收盒前卡在 `splitOf` 的隐式参数统一上（见六轮报告），**未提交半成品**。 -/


variable {n : ℕ}

/-- 子叶集 `A ⊆ Fin n` 嵌入 `Fin n ⊕ Unit`（子族限制/嫁接的公共载体）。 -/
def inlEmbed (A : Finset (Fin n)) : (A ⊕ Unit) → (Fin n ⊕ Unit) :=
  Sum.map (fun a => (a : Fin n)) id

/-- ★ `inlEmbed` 单射。 -/
theorem inlEmbed_injective (A : Finset (Fin n)) : Function.Injective (inlEmbed A) := by
  intro x y h
  rcases x with a | u <;> rcases y with b | v
  · have h' : (a : Fin n) = (b : Fin n) := Sum.inl.inj h
    exact congrArg Sum.inl (Subtype.ext h')
  · exact absurd h (by simp [inlEmbed])
  · exact absurd h.symm (by simp [inlEmbed])
  · rfl

/-- ★ `inlEmbed` 的像落在 `A ∪ {ρ}` 里。 -/
theorem inlEmbed_mem_union (A : Finset (Fin n)) (y : A ⊕ Unit) :
    inlEmbed A y ∈ (A.image Sum.inl) ∪ {Sum.inr ()} := by
  rcases y with a | u
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem Sum.inl a.2))
  · cases u
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))


/-! ### 11.18 `restrictToFinset`：把 split 限制到子叶集 `A ⊕ Unit`

第七轮的唯一目标（六轮失败清单的三条提示全部用上）：

* ★★ `restrictSet A s := {y : A ⊕ Unit | inlEmbed A y ∈ s.away ρ}`（**独立 `def`**，
  不是 `let` —— 这是绕开六轮那个 `splitOf` 占位符报错的关键：
  把 `B` 变成定理/定义的**参数**，占位符就没有合成歧义）；
* ★★ `restrictSet_nonempty`（需 `awayLeaves s ⊆ A`）与 ★★ `restrictSet_compl_nonempty`
  （**先 `Finset.mem_compl.mpr` 再 `intro`**，不在一次 `simp only` 里同时展开 `mem_compl`/`mem_filter`
  —— 这是六轮第二个报错 `Fintype ?m` 卡住的绕法）；
* ★★★ `restrictToFinset A s h := splitOf (restrictSet A s) (restrictSet_nonempty …) (restrictSet_compl_nonempty …)`；
* 取值引理：★★ `restrictToFinset_sideA`、★★ `mem_restrictToFinset_sideA_iff`
  （`ρ ∉ s.sideA` 时限制侧 = `s.sideA` 的原像）、★★ `mem_restrictToFinset_sideA_iff'`
  （`ρ ∈ s.sideA` 时 = `s.sideB` 的原像）。 -/


variable {n : ℕ}

/-- 限制用的集合：`A ⊕ Unit` 中落在 `s` 的 away 侧的点。 -/
noncomputable def restrictSet (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit)) : Finset (A ⊕ Unit) :=
  Finset.univ.filter (fun y => inlEmbed A y ∈ s.away (Sum.inr ()))

theorem mem_restrictSet_iff (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (y : A ⊕ Unit) : y ∈ restrictSet A s ↔ inlEmbed A y ∈ s.away (Sum.inr ()) := by
  simp only [restrictSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem restrictSet_nonempty (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) : (restrictSet A s).Nonempty := by
  obtain ⟨x, hx⟩ := awayLeaves_nonempty s
  have hx' : Sum.inl x ∈ s.away (Sum.inr ()) := by
    simpa only [awayLeaves, mem_realLeaves] using hx
  refine ⟨Sum.inl ⟨x, h (by simpa only [awayLeaves, mem_realLeaves] using hx)⟩, ?_⟩
  rw [mem_restrictSet_iff, inlEmbed, Sum.map_inl]
  exact hx'

theorem restrictSet_compl_nonempty (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit)) :
    ((restrictSet A s)ᶜ).Nonempty := by
  refine ⟨Sum.inr (), ?_⟩
  refine Finset.mem_compl.mpr ?_
  intro hmem
  have h2 := (mem_restrictSet_iff A s (Sum.inr ())).mp hmem
  rw [inlEmbed, Sum.map_inr] at h2
  exact Split.not_mem_away (Sum.inr ()) s h2

/-- ★★★ **沿子叶集限制 split**：若 `s` 的 away 真叶集含于 `A`，把 `s` 限制到 `A ⊕ Unit`。

`B := {y : A ⊕ Unit | inlEmbed A y ∈ s.away ρ}`，再 `splitOf B`。
关键：away 侧 ⊆ `A ∪ {ρ}`（away 真叶集 ⊆ `A` 且 `ρ ∉ away`），故 away 侧恰是 `B` 的原像。 -/
noncomputable def restrictToFinset (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) : Split (A ⊕ Unit) :=
  splitOf (restrictSet A s) (restrictSet_nonempty A s h) (restrictSet_compl_nonempty A s)

/-- ★★ 取值式：限制后 `sideA` 就是 `restrictSet`。 -/
theorem restrictToFinset_sideA (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) : (restrictToFinset A s h).sideA = restrictSet A s :=
  splitOf_sideA _ _ _

/-- ★★ 取值式：`sideA` 与**大集**的 `sideA` 的关系（`ρ ∉ s.sideA` 时 away 侧就是 `sideA`）。 -/
theorem mem_restrictToFinset_sideA_iff (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) (hρ : Sum.inr () ∉ s.sideA) (y : A ⊕ Unit) :
    y ∈ (restrictToFinset A s h).sideA ↔ inlEmbed A y ∈ s.sideA := by
  rw [restrictToFinset_sideA, mem_restrictSet_iff, Split.away_of_notMem _ hρ]

/-- ★★ 取值式：`ρ ∈ s.sideA` 时 away 侧是 `s.sideB`。 -/
theorem mem_restrictToFinset_sideA_iff' (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) (hρ : Sum.inr () ∈ s.sideA) (y : A ⊕ Unit) :
    y ∈ (restrictToFinset A s h).sideA ↔ inlEmbed A y ∈ s.sideB := by
  rw [restrictToFinset_sideA, mem_restrictSet_iff, Split.away_of_mem _ hρ]



/-! ### 11.18 续：`restrictToFinset` 的 **相容性搬运**（七轮的第二件）

`pullSet A W := {y : A ⊕ Unit | inlEmbed A y ∈ W}`：把大集的子集拉回 `A ⊕ Unit`。
`restrictToFinset` 的两侧恰是 `pullSet A (away ρ)` 与 `pullSet A ((away ρ)ᶜ)`，
而 `pullSet` 保持不交（`disjoint_pullSet`）⇒ ★★★ `compatible_restrictToFinset`。
证明按 `ρ ∈ s.sideA` / `ρ ∈ t.sideA` 四情形（`away` 取哪一侧），逐情形把目标四支与大集
`Compatible` 的四支对表。 -/


/-- `Finset` 的补的补。 -/
theorem compl_compl_finset {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    sᶜᶜ = s := by
  ext x
  simp only [Finset.mem_compl]
  tauto

/-- 「原像」集合：`A ⊕ Unit` 中落在 `W` 里的点（`restrictSet` 的一般形态）。 -/
noncomputable def pullSet (A : Finset (Fin n)) (W : Finset (Fin n ⊕ Unit)) : Finset (A ⊕ Unit) :=
  Finset.univ.filter (fun y => inlEmbed A y ∈ W)

theorem restrictSet_eq_pullSet (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit)) :
    restrictSet A s = pullSet A (s.away (Sum.inr ())) := rfl

theorem mem_pullSet_iff (A : Finset (Fin n)) (W : Finset (Fin n ⊕ Unit)) (y : A ⊕ Unit) :
    y ∈ pullSet A W ↔ inlEmbed A y ∈ W := by
  simp only [pullSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem compl_pullSet (A : Finset (Fin n)) (W : Finset (Fin n ⊕ Unit)) :
    (pullSet A W)ᶜ = pullSet A Wᶜ := by
  ext y
  rw [Finset.mem_compl, mem_pullSet_iff, mem_pullSet_iff, Finset.mem_compl]

theorem disjoint_pullSet (A : Finset (Fin n)) {X Y : Finset (Fin n ⊕ Unit)}
    (h : Disjoint X Y) : Disjoint (pullSet A X) (pullSet A Y) := by
  rw [Finset.disjoint_left] at h ⊢
  intro y hy1 hy2
  exact h ((mem_pullSet_iff A X y).mp hy1) ((mem_pullSet_iff A Y y).mp hy2)

theorem restrictToFinset_sideA_pull (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) :
    (restrictToFinset A s h).sideA = pullSet A (s.away (Sum.inr ())) := by
  rw [restrictToFinset_sideA]
  exact restrictSet_eq_pullSet A s

theorem restrictToFinset_sideB_pull (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) :
    (restrictToFinset A s h).sideB = pullSet A ((s.away (Sum.inr ()))ᶜ) := by
  rw [Split.sideB_eq_compl, restrictToFinset_sideA_pull, compl_pullSet]

/-- ★★★ **限制保持相容**（`inlEmbed` 下）。 -/
theorem compatible_restrictToFinset (A : Finset (Fin n)) (s t : Split (Fin n ⊕ Unit))
    (hs : awayLeaves s ⊆ A) (ht : awayLeaves t ⊆ A) (h : Split.Compatible s t) :
    Split.Compatible (restrictToFinset A s hs) (restrictToFinset A t ht) := by
  rw [Split.Compatible]
  rw [restrictToFinset_sideA_pull, restrictToFinset_sideB_pull,
    restrictToFinset_sideA_pull, restrictToFinset_sideB_pull]
  rw [Split.Compatible] at h
  by_cases hsρ : Sum.inr () ∈ s.sideA <;> by_cases htρ : Sum.inr () ∈ t.sideA
  · have es : s.away (Sum.inr ()) = s.sideB := Split.away_of_mem _ hsρ
    have es' : (s.away (Sum.inr ()))ᶜ = s.sideA := by
      rw [es, Split.sideB_eq_compl, compl_compl_finset]
    have et : t.away (Sum.inr ()) = t.sideB := Split.away_of_mem _ htρ
    have et' : (t.away (Sum.inr ()))ᶜ = t.sideA := by
      rw [et, Split.sideB_eq_compl, compl_compl_finset]
    rw [es', es, et', et]
    rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (disjoint_pullSet A h)))
    · exact Or.inr (Or.inr (Or.inl (disjoint_pullSet A h)))
    · exact Or.inr (Or.inl (disjoint_pullSet A h))
    · exact Or.inl (disjoint_pullSet A h)
  · have es : s.away (Sum.inr ()) = s.sideB := Split.away_of_mem _ hsρ
    have es' : (s.away (Sum.inr ()))ᶜ = s.sideA := by
      rw [es, Split.sideB_eq_compl, compl_compl_finset]
    have et : t.away (Sum.inr ()) = t.sideA := Split.away_of_notMem _ htρ
    have et' : (t.away (Sum.inr ()))ᶜ = t.sideB := by
      rw [et, Split.sideB_eq_compl]
    rw [es', es, et', et]
    rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (disjoint_pullSet A h)))
    · exact Or.inr (Or.inr (Or.inr (disjoint_pullSet A h)))
    · exact Or.inl (disjoint_pullSet A h)
    · exact Or.inr (Or.inl (disjoint_pullSet A h))
  · have es : s.away (Sum.inr ()) = s.sideA := Split.away_of_notMem _ hsρ
    have es' : (s.away (Sum.inr ()))ᶜ = s.sideB := by
      rw [es, Split.sideB_eq_compl]
    have et : t.away (Sum.inr ()) = t.sideB := Split.away_of_mem _ htρ
    have et' : (t.away (Sum.inr ()))ᶜ = t.sideA := by
      rw [et, Split.sideB_eq_compl, compl_compl_finset]
    rw [es', es, et', et]
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl (disjoint_pullSet A h))
    · exact Or.inl (disjoint_pullSet A h)
    · exact Or.inr (Or.inr (Or.inr (disjoint_pullSet A h)))
    · exact Or.inr (Or.inr (Or.inl (disjoint_pullSet A h)))
  · have es : s.away (Sum.inr ()) = s.sideA := Split.away_of_notMem _ hsρ
    have es' : (s.away (Sum.inr ()))ᶜ = s.sideB := by
      rw [es, Split.sideB_eq_compl]
    have et : t.away (Sum.inr ()) = t.sideA := Split.away_of_notMem _ htρ
    have et' : (t.away (Sum.inr ()))ᶜ = t.sideB := by
      rw [et, Split.sideB_eq_compl]
    rw [es', es, et', et]
    rcases h with h | h | h | h
    · exact Or.inl (disjoint_pullSet A h)
    · exact Or.inr (Or.inl (disjoint_pullSet A h))
    · exact Or.inr (Or.inr (Or.inl (disjoint_pullSet A h)))
    · exact Or.inr (Or.inr (Or.inr (disjoint_pullSet A h)))


/-! ### 11.19 子族条件之【非平凡】—— ★ 注意：第二条要 `⊊`，不是 `⊆`

第八轮块 1。**关键口径修正**：`restrictToFinset A s h` 的
* `sideA = pullSet A (away s)`：基数 = away 侧基数 ≥ 2（`s` 非平凡 ⇒ 两侧各 ≥ 2）；
* `sideB = pullSet A ((away s)ᶜ)`：它是 **`A ⊕ Unit` 内部的补**，基数为
  `|A| + 1 − |awayLeaves s|`。故 `awayLeaves s = A`（只是 `⊆` 而非 `⊊`）时 `sideB = {ρ}`，
  **限制出的 split 退化成平凡**！

⇒ 子族必须取 `{s ∈ ω.val | awayLeaves s ⊊ A}`（**proper**），不能取 `⊆`。
这与 §11.17 规格里的 `⊊` 一致；第八轮派单的块 1 文字只写了「用 `sides_card_of_mem_nontrivialSplits`
传下来」，按 `⊆` 写下会得到**假命题**（反例：`A` 自己的那条 split）。

本节交付：
* ★ `mem_pullSet_iff'`、★ `away_subset_union`（away 侧 ⊆ `A ∪ {ρ}`）；
* ★ `exists_preimage_of_mem_away`（away 侧每点都有 `A ⊕ Unit` 里的原像）；
* ★★ `two_le_card_restrictToFinset_sideA`（需 `2 ≤ |away 侧|`，即 `s` 非平凡）；
* ★★ `two_le_card_restrictToFinset_sideB`（需 `|awayLeaves s| < |A|`，即 **proper**）。 -/

theorem mem_pullSet_iff' (A : Finset (Fin n)) (W : Finset (Fin n ⊕ Unit)) (y : A ⊕ Unit) :
    y ∈ pullSet A W ↔ inlEmbed A y ∈ W := by
  simp only [pullSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- away 侧含于 `A ∪ {ρ}`。 -/
theorem away_subset_union (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) :
    s.away (Sum.inr ()) ⊆ A.image Sum.inl ∪ {Sum.inr ()} := by
  intro y hy
  have hρ : Sum.inr () ∉ s.away (Sum.inr ()) := Split.not_mem_away (Sum.inr ()) s
  rcases y with a | u
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem Sum.inl
      (h (by simpa only [awayLeaves, mem_realLeaves] using hy))))
  · cases u
    exact absurd hy hρ

/-- ★ away 侧的每个点都是 `A ⊕ Unit` 里某点的像。 -/
theorem exists_preimage_of_mem_away (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) {x : Fin n ⊕ Unit} (hx : x ∈ s.away (Sum.inr ())) :
    ∃ y : A ⊕ Unit, inlEmbed A y = x := by
  have hU := away_subset_union A s h hx
  have hne : Sum.inr () ∉ s.away (Sum.inr ()) := Split.not_mem_away (Sum.inr ()) s
  rcases x with a | u
  · have haA : a ∈ A := by
      rcases Finset.mem_union.mp hU with hh | hh
      · obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hh
        rwa [Sum.inl.inj heq] at ha'
      · rw [Finset.mem_singleton] at hh
        exact absurd hh (by simp)
    exact ⟨Sum.inl ⟨a, haA⟩, rfl⟩
  · cases u
    exact absurd hx hne

/-- ★★ **`sideA` 至少两个元素**（`away` 侧有 ≥ 2 个元素，每个都有原像）。 -/
theorem two_le_card_restrictToFinset_sideA (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) (h2 : 2 ≤ (s.away (Sum.inr ())).card) :
    2 ≤ (restrictToFinset A s h).sideA.card := by
  rw [restrictToFinset_sideA_pull]
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h2
  obtain ⟨xa, hxa⟩ := exists_preimage_of_mem_away A s h hx
  obtain ⟨ya, hya⟩ := exists_preimage_of_mem_away A s h hy
  refine Finset.one_lt_card.mpr ⟨xa, ?_, ya, ?_, ?_⟩
  · rw [mem_pullSet_iff']; rw [hxa]; exact hx
  · rw [mem_pullSet_iff']; rw [hya]; exact hy
  · intro hc
    exact hxy (by rw [← hxa, ← hya, hc])

/-- ★★ **`sideB` 至少两个元素**（`awayLeaves s ⊊ A` ⇒ `ρ` 与某个 `a ∈ A ∖ away` 都在 `sideB`）。 -/
theorem two_le_card_restrictToFinset_sideB (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) (hlt : (awayLeaves s).card < A.card) :
    2 ≤ (restrictToFinset A s h).sideB.card := by
  rw [restrictToFinset_sideB_pull]
  have hproper : awayLeaves s ⊂ A := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨h, fun heq => by rw [heq] at hlt; exact absurd hlt (lt_irrefl _)⟩
  obtain ⟨a, haA, haW⟩ := Finset.exists_of_ssubset hproper
  have h1 : Sum.inr () ∈ pullSet A ((s.away (Sum.inr ()))ᶜ) := by
    rw [mem_pullSet_iff']
    show Sum.inr () ∈ (s.away (Sum.inr ()))ᶜ
    rw [Finset.mem_compl]
    exact Split.not_mem_away (Sum.inr ()) s
  have h2 : Sum.inl ⟨a, haA⟩ ∈ pullSet A ((s.away (Sum.inr ()))ᶜ) := by
    rw [mem_pullSet_iff']
    show Sum.inl a ∈ (s.away (Sum.inr ()))ᶜ
    rw [Finset.mem_compl]
    intro hmem
    exact haW (by simpa only [awayLeaves, mem_realLeaves] using hmem)
  refine Finset.one_lt_card.mpr ⟨_, h1, _, h2, ?_⟩
  intro hc
  cases hc


/-! ### 11.20 子族 `subFamily`（`Finset (Split (A ⊕ Unit))`）＋ 限制的 2 对 1

第九轮。`subFamily ω A` = `ω` 里「away 真叶集是 `A` 的**真**子集」的那些 split **限制到 `A ⊕ Unit`**。

跨过「依赖证明的映射」（`Finset.image` 只接受非依赖函数）的办法：先取**子类型**
`{s // s ∈ ω.val ∧ awayLeaves s ⊂ A}`，再用 ★ `subset_of_ssubset_finset` 把 `⊂` 弱化成
`restrictToFinset` 需要的 `⊆`。

★ **`restrictToFinset_swap` 的正确陈述**：`s` 与 `s.swap` 限制到**同一条**（不是「`(限制 s).swap = 限制 s.swap`」—— 后者**为假**：
左边 `sideA = (pull Set (away s))ᶜ`，右边 `sideA = pullSet (away s.swap) = pullSet (away s)`，互为补）。
「相同」正是「限制在 `swap`-封闭族上**2 对 1**」的确切形式，也是块 2（swap-闭）的直接前置。

**下一轮的目标陈述（本批未证）**：`(subFamily ω A).card = 2 * (A.card - 2)`（`A` 为 `ω` 的极大 clade 时）。 -/

/-- `⊂` 弱化为 `⊆`。 -/
theorem subset_of_ssubset_finset {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : s ⊂ t) : s ⊆ t :=
  (Finset.ssubset_iff_subset_ne.mp h).1

/-- ★★★ **`s` 与 `s.swap` 限制到同一条**（`away` 对换向不变 ⇒ `pullSet (away s.swap) = pullSet (away s)`）。

⚠️ 注意：正确的陈述是「**相同**」而不是「`(限制 s).swap = 限制 s.swap`」——
后者**为假**：左边 `sideA = (pullSet (away s))ᶜ`，右边 `sideA = pullSet (away s.swap) = pullSet (away s)`，
互为补（这正是「限制在 `swap`-封闭族上是 2 对 1」）。 -/
theorem restrictToFinset_swap (A : Finset (Fin n)) (s : Split (Fin n ⊕ Unit))
    (h : awayLeaves s ⊆ A) :
    restrictToFinset A s.swap (by rw [awayLeaves_swap]; exact h) =
      restrictToFinset A s h := by
  refine Split.ext_sideA ?_
  rw [restrictToFinset_sideA_pull, restrictToFinset_sideA_pull, Split.away_swap]

/-- ★★★ **子族**：`ω` 中「away 真叶集是 `A` 的真子集」的那些 split，**限制到 `A ⊕ Unit`** 后的集合。

跨过「依赖证明的映射」的办法：先取**子类型**
`{s // s ∈ ω.val ∧ awayLeaves s ⊂ A}`（`Finset.image` 只接受非依赖函数），
再用 `subset_of_ssubset_finset` 把 `⊂` 弱化成 `restrictToFinset` 需要的 `⊆`。 -/
noncomputable def subFamily (ω : rootedSplitFamily n) (A : Finset (Fin n)) :
    Finset (Split (A ⊕ Unit)) :=
  Finset.univ.image
    (fun s : {s : Split (Fin n ⊕ Unit) // s ∈ ω.val ∧ awayLeaves s ⊂ A} =>
      restrictToFinset A s.1 (subset_of_ssubset_finset s.2.2))

/-- ★★ `subFamily` 的成员刻画。 -/
theorem mem_subFamily {ω : rootedSplitFamily n} {A : Finset (Fin n)}
    {t : Split (A ⊕ Unit)} :
    t ∈ subFamily ω A ↔ ∃ (s : Split (Fin n ⊕ Unit)) (_ : s ∈ ω.val)
      (hp : awayLeaves s ⊂ A),
      restrictToFinset A s (subset_of_ssubset_finset hp) = t := by
  constructor
  · intro ht
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp ht
    exact ⟨s.1, s.2.1, s.2.2, hs⟩
  · rintro ⟨s, hs, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨s, hs, hp⟩, Finset.mem_univ _, rfl⟩

/-- ★★ **子族的每个成员都非平凡**（`⊂` 的必要性见 §11.19）。 -/
theorem subFamily_sides_card {ω : rootedSplitFamily n} {A : Finset (Fin n)}
    {t : Split (A ⊕ Unit)} (ht : t ∈ subFamily ω A) :
    2 ≤ t.sideA.card ∧ 2 ≤ t.sideB.card := by
  obtain ⟨s, hs, hp, rfl⟩ := (mem_subFamily).mp ht
  have hnt := ω.2.2.1 s hs
  refine ⟨two_le_card_restrictToFinset_sideA A s (subset_of_ssubset_finset hp) ?_,
    two_le_card_restrictToFinset_sideB A s (subset_of_ssubset_finset hp)
      (Finset.card_lt_card hp)⟩
  -- `2 ≤ |away 侧|`：away 侧是 `s` 的某一侧，非平凡 ⇒ ≥ 2
  by_cases hρ : Sum.inr () ∈ s.sideA
  · rw [Split.away_of_mem _ hρ]; exact hnt.2
  · rw [Split.away_of_notMem _ hρ]; exact hnt.1


/-! ### 11.21 Lemma 4.1 的**归纳核**（递推 ⇒ 闭式）

ZDS 2011（论文 p.5，`.w30/img/…_p5-05.png` 已逐字读）在 Lemma 4.1 的注记里给出另一条证明：
「也可对 `n` 归纳，用 YHK 模型的已知性质：**两个极大子树之一的叶子数在 `1..n−1` 上均匀分布**」。
本节把这一段的**归纳部分**（递推 ⇒ 闭式）做完 —— 它与概率层解耦，只涉及 `ℝ` 上的求和。

递推（记 `E_n(a)` = `n` 叶有根 YHK 树中 size-`a` 的 **proper** clade 数的期望；`1 ≤ a ≤ n−1`）：

```text
E_n(a) = (2/(n−1))·Σ_{k=1}^{n−1} E_k(a) + 2/(n−1)
```

* `2/(n−1)` 的来历：给定了根分裂成 `k`、`n−k` 两棵子树，**两个子树各自**是一个 size 为
  `k`（resp. `n−k`）的 proper clade，故 `k = a` 与 `n−k = a` 各贡献 `1`；`2a = n` 时**仍然是 `2`**
  （两个子树**都**是 size-`a` 的 proper clade），不是 `1 + [2a ≠ n]`。
* 边界 `E_k(a) = 0`（`a ≥ k`：`k` 叶树没有 size-`a` 的 proper clade）。
* 端点核对：`E_n(1) = n`、`E_n(n−1) = 1`。

⚠️ **本条不证递推**：递推 = 「极大子树叶子数均匀」这条**概率公理**在库内的落地，
等价于 `rootedSplitFamily` 的**根分裂分解**（§11.17 的规格、§11.20 的载体运输）；
库内目前只有 `Fin 4` 的实例（`yhkLawFour`）。 -/

/-- ★ **Gauss 求和（实数形态）**：`∑_{i<m} i = m(m−1)/2`。 -/
theorem sum_range_cast_id (m : ℕ) :
    ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- ★ **区间求和**：`∑_{m ≤ k < n} k = (n(n−1) − m(m−1))/2`（`m ≤ n`）。 -/
theorem sum_Ico_cast_id {m n : ℕ} (h : m ≤ n) :
    ∑ k ∈ Finset.Ico m n, (k : ℝ) = ((n : ℝ) * ((n : ℝ) - 1) - (m : ℝ) * ((m : ℝ) - 1)) / 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcast : ∀ k : ℕ, ((m + k : ℕ) : ℝ) = (m : ℝ) + (k : ℝ) := by
    intro k
    push_cast
    ring
  simp only [hcast]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    sum_range_cast_id]
  have hdn : (((n - m : ℕ)) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub h
  rw [hdn]
  ring

/-- ★★★ **Lemma 4.1 的归纳核**：满足 YHK **根分裂递推**、且在 `a ≥ k` 处为零的
`E : ℕ → ℕ → ℝ`，其值必为 `2n/(a(a+1))`。

即 ZDS 2011 p.5 的「对 `n` 归纳」那一段（`E_n(a) = 2n/(a(a+1))`，`1 ≤ a ≤ n−1`），
**已机器核**；缺的只是递推本身（= YHK 的极大子树均匀性）。 -/
theorem cladeExpectation_eq_of_rootSplitRecursion
    (E : ℕ → ℕ → ℝ)
    (hzero : ∀ k a : ℕ, a ≥ k → E k a = 0)
    (hstep : ∀ n a : ℕ, 2 ≤ n → 1 ≤ a → a ≤ n - 1 →
      E n a = 2 / ((n : ℝ) - 1) * (∑ k ∈ Finset.Ico 1 n, E k a) + 2 / ((n : ℝ) - 1)) :
    ∀ n a : ℕ, 1 ≤ a → a ≤ n - 1 → E n a = 2 * (n : ℝ) / ((a : ℝ) * ((a : ℝ) + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a h1 ha
    have hn2 : 2 ≤ n := by omega
    rw [hstep n a hn2 h1 ha]
    -- 求和截断到 `k ≥ a + 1`（`k ≤ a` 的项全为 `0`）
    have hcut : ∑ k ∈ Finset.Ico 1 n, E k a = ∑ k ∈ Finset.Ico (a + 1) n, E k a := by
      have hcons := Finset.sum_Ico_consecutive (fun k => E k a)
        (show 1 ≤ a + 1 by omega) (show a + 1 ≤ n by omega)
      have hz : ∑ k ∈ Finset.Ico 1 (a + 1), E k a = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        rw [Finset.mem_Ico] at hk
        exact hzero k a (by omega)
      rw [hz, zero_add] at hcons
      exact hcons.symm
    rw [hcut]
    -- 归纳假设：`k > a` 时 `E_k(a) = 2k/(a(a+1))`
    have hterm : ∑ k ∈ Finset.Ico (a + 1) n, E k a
        = (2 / ((a : ℝ) * ((a : ℝ) + 1))) * ∑ k ∈ Finset.Ico (a + 1) n, (k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [Finset.mem_Ico] at hk
      rw [ih k hk.2 a (by omega) (by omega)]
      ring
    rw [hterm, sum_Ico_cast_id (show a + 1 ≤ n by omega)]
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn2
      linarith
    have ha0 : (0 : ℝ) < (a : ℝ) := by
      have : 0 < a := by omega
      exact_mod_cast this
    have hne1 : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
    have hne2 : ((a : ℝ) * ((a : ℝ) + 1)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring


/-! ### 11.22 Lemma 4.2 的**双重计数**（(EP) 那一步的前半，**不需要 (EP)**）

ZDS 2011 p.6（`.w30/img/…_p6-06.png` 已逐字读）对 Lemma 4.2 的证明是：

```text
p_n(A) = Σ_{k≥0} P(T has k clades of size a)·k/C(n,a) = E[X_n(a)]·C(n,a)^{-1}
```

第一个等号 = **双重计数**（把「(A, T) 对」按 A 数、按 T 数）+ **(EP)**（各 `A` 等概率）。
本节只做其中**不需要 (EP)** 的那一半（纯 `Finset.sum_comm`）：

```text
∑_{|A|=a} P(A 是 T 的 clade) = ∑_T P(T)·X_T(a)
```

左端对 `A` 的求和用库内的事件「`(tree ω).IsClade A`」表示，右端的 `X_T(a)` 写成
「size-`a` 且是 clade 的 `A` 的**个数**」。 -/

/-- ★★ **双重计数恒等式**（Lemma 4.2 证明的第一个等号，**无需** (EP) 的等变性）：
`∑_{|A|=a} P(A 是 clade) = ∑_ω prob ω · X_ω(a)`。 -/
theorem sum_cladeEvent_eq_sum_cladeCount {n : ℕ} {Ω : Type} [Fintype Ω]
    (prob : Ω → ℝ) (tree : Ω → Cladogram.{0, 0} (Fin n)) (a : ℕ) :
    (∑ A ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun A => A.card = a),
        ∑ ω ∈ (Finset.univ : Finset Ω).filter (fun ω => (tree ω).IsClade A), prob ω)
      = ∑ ω : Ω, prob ω * (((Finset.univ : Finset (Finset (Fin n))).filter
          (fun A => A.card = a ∧ (tree ω).IsClade A)).card : ℝ) := by
  classical
  have hL : ∀ A : Finset (Fin n),
      (∑ ω ∈ (Finset.univ : Finset Ω).filter (fun ω => (tree ω).IsClade A), prob ω)
        = ∑ ω : Ω, if (tree ω).IsClade A then prob ω else 0 := by
    intro A
    rw [Finset.sum_filter]
  simp only [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]


end Phylo.Stat.ReciprocalMonophyly
