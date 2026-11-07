/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJHardCore
import Phylo.AttesonRadius

/-!
# `Phylo.Stat.CASTERNJStep` —— L5a 的 **NJ-步接口层**（W46 建，W47 状态校准）

派单：`W44_TO_DSH_prompt.txt` §3.6 / §3.7 / §3.8。

## 本文件做什么（★ W47 校准：原文写的「台账仍 74」「L5a 的缺口在这里」已过时）

本文件**不证新数学**：它只把「NJ 的一步」在库里**第一次命名**（`njStep`），
并把库内**已有**的结论重述成 NJ-步语言（`njStep_isCherry` / `njStep_quartet` / `mergeStep_*`）。

**L5a 的 A/B/C 三步的去向**（★ 三件都已完成，不再是本文件 §3 的「方案」）：

| 步骤 | 内容 | 落在哪个文件 | 状态 |
|---|---|---|---|
| A | 树层樱桃收缩（`shrinkPhylogram`） | `Phylo/Stat/NJShrink.lean`（1569 行） | ★★★ 已证（W46） |
| B | 算法本体（`njRun` ＋ 归约归纳） | `Phylo/Stat/NJRun.lean` | W47 施工中 |
| C | 装配（`δ` 唯一决定拓扑） | `Phylo/Stat/NJRecovers.lean` | ★★★ 已证（W46） |

⇒ `Phylo.Stat.CASTERNJ.njAdditiveGap` **已由 `njAdditiveGap_holds` 收口**
（`CASTERNJ.lean`，台账【已收口】）；A 步的**算术核** `mergeStep_val_eq` 也早证
（`Phylo/Stat/StrictCherry.lean`）。
**本文件不含 A/B/C 的任何实现**，也不含任何「未证」的断言 —— 它只是接口层。

## 0 口径更正（派单 §3.6 的「库内没有 NJ 算法本体」）

派单的 grep 是 `^(noncomputable )?def (nj|neighborJoining|njTree|neighborJoin)`，故判「0 命中」。
实读结果更细：**度量侧的 `Q` 判据、`z`、`mergeDissim`、`mergeQ`、`card_mergeIdx` 全都有**
（`Phylo/Algorithm/NJ.lean`、`Phylo/AttesonRadius.lean:1260–1420`），
当时**缺的只有「把 n−3 轮跑完并返回一棵树」的那一层**（以及它需要的树层收缩）。
⇒ 当时判定的「L5a 的缺口 = 算法粘合层 ＋ 树层收缩 ＋ 归纳」**已按此拆解做完两步**
（树层收缩 = `NJShrink`，归纳＋装配 = `NJRecovers`）；只剩「把 n−3 轮跑完」这一层
（W47 的 `Phylo/Stat/NJRun.lean`）。

## 1 本文件已证（全部是既有定理的 NJ-步重述，不新增假设）

| 定理 | 内容 | 依据 |
|---|---|---|
| `njStep` | `a ≠ b` 且 `Q_δ(a,b)` 全局最小 | 定义 |
| `njStep_isCherry` | 正权实现树 ⇒ 该对是 `δ` 的樱桃（**第一步正确**） | ★★★ `nj_cherry_of_hasPositiveRealization` |
| `njStep_quartet` | 该对给出所有含它的 quartet 的分裂 | ★★ `max_z_gives_split_of_hasPositiveRealization` |
| `mergeStep` | 归约 `θ = ½`（`δ(u,·) = ½(δ(x,·)+δ(y,·))`） | ★★★ `mergeDissim` |
| `mergeStep_fourPoint` | 归约保持四点条件 | ★★★ `mergeDissim_fourPoint` |
| `mergeStep_card` | 归约后基数 `+1 =` 原基数（递降尺度） | ★★★ `card_mergeIdx` |

## 2 曾经卡在哪一步（★ 已不卡：W46 已把它做完）

> ~~`δ.HasPositiveRealization → δ.IsCherry x y → (mergeStep δ x y).HasPositiveRealization`~~
> —— 即「**树层樱桃收缩**」。（W46 当时）库内**没有**这条引理（度量侧有 `mergeDissim`，树侧没有对应物）。

⇒ **W46 已补上**：`Phylo/Stat/NJShrink.lean` 的 ★★★ `shrinkPhylogram` 就是那条引理
（顶点 `ShrinkV`、诱导子图 ＋ 新边 `leaf a—z`、边权 `shrinkW`），
并附带 `dist` 与 `mergeStep` 的**逐点对齐**（★★★ `shrinkPhylogram_dist`）、
正权（★★★ `shrinkPhylogram_w_pos`）与**二叉性**（★★★ `shrinkPhylogram_isBinary`）。
本文件 §3 保留为**历史方案记录**（W46 的施工顺序与工量估计），不再代表当前状态。

## 3 方案（历史记录；三步已全部落地，见 §1 的表）

### 步骤 A｜树层收缩（**200–350 行**，L5a 的唯一实质工作）

设 `T : Phylogram X`、`T.IsCherry a b`（取公共邻居 `w`，`haw : Adj (leaf a) w`、`hbw : ...`），
`T` 边权全正。构造 `T' : Phylogram (MergeIdx X a b)`：

* ⚠️★★ **★D 更正（W46，我上一版方案是错的）**：只「删叶 `b` + 把 `w—a` 的权改成 `½(w_a+w_b)`」
  **造不出合法 `Phylogram`** —— 删叶后 `w` 的度从 3 掉到 **2**，而 `Cladogram.no_degree_two`
  （`Phylo/Core.lean:44`）要求**无度 2 顶点**。正确构造必须**再抑制 `w`**：
  * 顶点集：`V' := {v : T.V // v ≠ T.leaf b ∧ v ≠ w}`（删叶 `b`、再删中点 `w`）；
    `leaf' : MergeIdx X a b ↪ V'`：`Sum.inl x ↦ ⟨T.leaf x, _⟩`、`Sum.inr () ↦ ⟨T.leaf a, _⟩`；
  * 图：`T.graph.induce {v | v ≠ T.leaf b ∧ v ≠ w}` **再加一条 `leaf a — z`** 的边
    （`z` = `w` 除 `a`、`b` 外**唯一**的邻居 —— 二叉性保证存在且唯一）；
  * 边权：新边 `s(leaf a, z)` 取 `½·(w ⟨a,w⟩ + w ⟨b,w⟩) + w ⟨w,z⟩`，其余原样；
  * **距离对齐（关键引理）**：对 `u v : MergeIdx X a b`，
    `T'.dist (leaf' u) (leaf' v) = (mergeStep (dissOf T) a b).val u v`；
  * **新–旧的那一步算术已经证好了**：★★★
    `Phylo.Stat.StrictCherry.mergeStep_val_eq` 给出
    `½·δ(x,a) + ½·δ(x,b) = ½(w_a + w_b) + d(w,x)`
    —— 正是「把新叶挂在 `w` 上、边权 `½(w_a+w_b)`」的距离。⇒ 剩下的**全是图论**。
  ★ 器械已在库：`Phylo/PhylogramContract.lean` 的 `suppressGraph` / `suppressLeaf`（抑制度 2 顶点）
  ＋ `Phylo/Algorithm/NJHardCore.lean:77–122` 的距离桥接。
  ⇒ 工作量上调到 **200–350 行**（上一版估 150–250 行漏了 `no_degree_two`）。

### 步骤 B｜算法本体（**80–120 行**）

`def njRun : (δ : Dissimilarity X) → (δ.HasPositiveRealization) → Cladogram X` 的**关系式**
（不要求可执行，只要「每轮取 `Q` 最小对并合并」这个关系成立）：

* 用 `Fintype.card` 递降做终止（`mergeStep_card`）；
* `|X| ≤ 3` 基例：任意 `Cladogram`（3 叶树无非凡 split，拓扑唯一）；
* 每轮：取 `njStep δ x y`（`Classical.choose` 于「`Q` 在有限集上取最小」），
  记录 split `{x,y} | 其余`，递归到 `mergeStep δ x y`；
* 输出 = 「把各轮的樱桃 split 沿合并历史拉回 `X`」所得的 `Cladogram`
  （`Phylo/SplitsDetermineTree.lean` 有 split 集 ⇒ `Iso` 的收口，
  但**没有**「split 集 ⇒ 存在树」；若库内也没有，需按 `Cladogram` 的构造手搭，+50 行）。

### 步骤 C｜归纳 ＋ 装配（**80–120 行**）

* 强归纳：`|X|` 递降。每轮 `njStep_isCherry` 给「选的是真樱桃」，
  步骤 A 给「归约后仍正权实现」，归纳假设给「子问题恢复」；
* 装配：末态 split 集 `= T` 的 split 集 ⇒ ★★★ `Cladogram.iso_of_isSplitOf_iff`
  （`Phylo/SplitsDetermineTree.lean:652`）；
* 引用口径（派单 §3.8，**必须照写**）：定理本体引 **SK1988 `:20-22`**、
  单步引 **MLP2006 `:135-139` Thm 1**（= 库内 ★★★ `maxZCherryCore` 同句）、
  归约引 **MLP2006 `:141-148`**、归纳骨架照 **SK1988 `:321-329`**；
  **SN1987 只引算法本体**（SK1988 `:46` 明说其证明有误）。

**合计 360–590 行**（★ 上调：步骤 A 漏了 `no_degree_two`，见上）。派单预算 100–250 行，
但**协调侧 2026-11-05 01:0x 已明确「超预算不是问题」** ⇒ 未走「允许出口」。
★ 实测收尾：步骤 A 落在 `NJShrink.lean` **1569 行**、步骤 C 落在 `NJRecovers.lean` **642 行**，
均**超出**上面的估计（估计偏低，记录在此）。
**本文件不含步骤 A/B/C 的实现** —— 它只在上面那张表里指路。

## 4 诚实边界（★ W47 逐句校准：这里的每一句都必须是**当前真值**）

* **本文件不关闭任何缺口**：`njStep` / `njStep_isCherry` / `njStep_quartet` / `mergeStep*`
  全是接口重述，无新数学。缺口的状态在 `CASTERNJ.lean` 的 `def` 上，不在本文件。
* **本库已证**（W46，台账【已收口】）：★★★ `CASTERNJ.njAdditiveGap_holds`（树层樱桃收缩）、
  ★★★ `CASTERNJ.njReductionStep`（归约保持「正权 ∧ 二叉 ∧ 实现」）、
  ★★★ `StrictCherryProved.strictCherry_of_isBinary_pos_gap_holds`、
  ★★★ `NJRecovers.iso_of_realizes_binary_additive`（★ W47 改名，原名 `nj_recovers_topology_additive`）。
* **★ W49 起非二叉支也收口了**：★★★ `CASTERNJ.njAdditiveGapUnrestricted_holds`
  （`Phylo/Stat/NJShrinkNonBinary.lean`）只假设 `HasPosReal` 就证同一结论
  ⇒ 原「本库未证」的 ★★ `CASTERNJ.njAdditiveGapUnrestricted` 已不是缺口。
  ★ 关键更正：**「非二叉」≠「`deg w ≥ 4`」**（`no_degree_two` 只排除度 2），
  故正确切法是按**樱桃中点的度**分情形，而不是按整棵树是否二叉。
* **`nj_recovers_topology_additive` 这个名字已让位**（W47 M1-②）：原定理的结论里**不含 NJ**，
  故改名为内容名 `iso_of_realizes_binary_additive`；`nj_` 系列的名字留给真正含 `njStep` 的定理
  （`Phylo/Stat/NJRun.lean` 的 `njRun_correct_additive`）。
* `njStep_quartet` 需要 `4 ≤ Fintype.card X`（`max_z_gives_split_of_hasPositiveRealization` 的签名），
  这在 `n ≤ 3` 时结论本身无意义（没有 4 个互异点）。
* L5a 的前提是**可加**（`HasPositiveRealization`）；CASTER 的 `D̃` **不满足**，
  那是 L5b（`njConsistencyGap`）的内容，两者**不许混**。
-/

namespace Phylo.Stat.CASTERNJStep

open NJ NJ.Dissimilarity

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## 5. NJ 的一步 -/

/-- **NJ 的一步**：`(a,b)` 互异且**全局最小化** `Q_δ`（`Phylo/Algorithm/NJ.lean:88` 的 `Q`）。 -/
def njStep (δ : Dissimilarity X) (a b : X) : Prop :=
  a ≠ b ∧ ∀ i j : X, i ≠ j → δ.Q a b ≤ δ.Q i j

theorem njStep_ne {δ : Dissimilarity X} {a b : X} (h : njStep δ a b) : a ≠ b := h.1

theorem njStep_le {δ : Dissimilarity X} {a b : X} (h : njStep δ a b) {i j : X}
    (hij : i ≠ j) : δ.Q a b ≤ δ.Q i j := h.2 i j hij

/-- ★★★ **L5a 的第一步正确**（MLP2006 `:135-139` Thm 1 的库内形态
★★★ `maxZCherryCore` ⇒ ★★★ `nj_cherry_of_hasPositiveRealization`）：
若 `δ` 有**边权全正**的实现树且满足四点条件，则 `Q` 的最小对是 `δ` 的真樱桃。 -/
theorem njStep_isCherry (δ : Dissimilarity X) (hpos : δ.HasPositiveRealization)
    (hfp : δ.FourPoint) {a b : X} (h : njStep δ a b) : δ.IsCherry a b :=
  nj_cherry_of_hasPositiveRealization δ hpos hfp a b h.1 h.2

/-- ★★★ **第一步给出的 quartet 分裂**：所有含 `{a,b}` 的四点都按 `ab|·` 分裂
（`4 ≤ |X|`；退化情形由 `IsCherry` 自身覆盖）。 -/
theorem njStep_quartet (δ : Dissimilarity X) (hpos : δ.HasPositiveRealization)
    (hfp : δ.FourPoint) {a b : X} (h : njStep δ a b) (hcard : 4 ≤ Fintype.card X)
    {i j : X} (hij : i ≠ j) (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    δ.val a b + δ.val i j ≤ δ.val a i + δ.val b j ∧
      δ.val a b + δ.val i j ≤ δ.val a j + δ.val b i := by
  have hmax : ∀ p q : X, p ≠ q → δ.z p q ≤ δ.z a b := by
    intro p q hpq
    have h1 : δ.Q a b ≤ δ.Q p q := h.2 p q hpq
    rw [Q_eq_neg_two_z δ, Q_eq_neg_two_z δ] at h1
    linarith
  exact max_z_gives_split_of_hasPositiveRealization δ hpos hcard hfp a b h.1 hmax i j hij
    hia hib hja hjb

/-! ## 6. 归约（reduction，θ = ½） -/

/-- **归约一步**：`δm(u, a) = ½(δ(x,a) + δ(y,a))`、旧–旧不变（MLP2006 `:141-148`）。 -/
noncomputable def mergeStep (δ : Dissimilarity X) (a b : X) :
    Dissimilarity (MergeIdx X a b) :=
  mergeDissim δ a b (1 / 2)

/-- 归约的新–旧取值：`½(δ(x,a) + δ(y,a))`。 -/
theorem mergeStep_val_merged (δ : Dissimilarity X) (a b : X) {x : X}
    (hx : x ≠ a) (hx' : x ≠ b) :
    (mergeStep δ a b).val (mergeQ a b x) (mergeQ a b b)
      = (1 / 2) * δ.val x a + (1 - 1 / 2) * δ.val x b :=
  mergeDissim_val_merged δ a b (1 / 2) hx hx'

/-- ★★★ **归约保持四点条件**（`mergeDissim_fourPoint` 在 `θ = ½` 的特例）。 -/
theorem mergeStep_fourPoint (δ : Dissimilarity X) (hfp : δ.FourPoint) {a b : X}
    (hch : δ.IsCherry a b) : (mergeStep δ a b).FourPoint :=
  mergeDissim_fourPoint δ hfp hch (by norm_num) (by norm_num)

/-- ★★★ **归约后基数 −1**（归纳的递降尺度）。 -/
theorem mergeStep_card {a b : X} (hab : a ≠ b) :
    Fintype.card (MergeIdx X a b) + 1 = Fintype.card X :=
  card_mergeIdx hab

/-- 归约点的 `Q` 判据（`AttesonRadius` 已有 `mergeQ` 的 `Q` 版本，此处只做接口重述）。 -/
theorem mergeStep_fourPoint_merged (δ : Dissimilarity X) (hfp : δ.FourPoint) {a b : X}
    (hch : δ.IsCherry a b) (p q r : MergeOld X a b) :
    (mergeStep δ a b).val (Sum.inr ()) (Sum.inl p) + (mergeStep δ a b).val (Sum.inl q) (Sum.inl r)
        ≤ (mergeStep δ a b).val (Sum.inr ()) (Sum.inl q) + (mergeStep δ a b).val (Sum.inl p) (Sum.inl r)
      ∨ (mergeStep δ a b).val (Sum.inr ()) (Sum.inl p)
          + (mergeStep δ a b).val (Sum.inl q) (Sum.inl r)
        ≤ (mergeStep δ a b).val (Sum.inr ()) (Sum.inl r)
          + (mergeStep δ a b).val (Sum.inl p) (Sum.inl q) :=
  mergeDissim_fourPoint_merged δ hfp hch (by norm_num) (by norm_num) p q r

end Phylo.Stat.CASTERNJStep
