/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Algorithm.NJHardCore
import Phylo.AttesonRadius

/-!
# `Phylo.Stat.CASTERNJStep` —— L5a 的**脚手架**与**方案**（W46）

派单：`W44_TO_DSH_prompt.txt` §3.6 / §3.7 / §3.8（L5a `nj_recovers_topology_additive`）。
本文件**不**关闭 `Phylo.Stat.CASTERNJ.njAdditiveGap`（台账仍 74）；它做两件事：

1. 把「NJ 的一步」在库里**第一次命名**（`njStep`），并把库内**已有**的三条结论
   重述成 NJ-步语言（`njStep_isCherry` / `njStep_quartet` / `mergeStep_*`）；
2. 把 L5a 剩下的工作写成**可执行的方案**（下面 §3），并说明**卡在哪一行**。

## 0 口径更正（派单 §3.6 的「库内没有 NJ 算法本体」）

派单的 grep 是 `^(noncomputable )?def (nj|neighborJoining|njTree|neighborJoin)`，故判「0 命中」。
实读结果更细：**度量侧的 `Q` 判据、`z`、`mergeDissim`、`mergeQ`、`card_mergeIdx` 全都有**
（`Phylo/Algorithm/NJ.lean`、`Phylo/AttesonRadius.lean:1260–1420`），
**缺的只有「把 n−3 轮跑完并返回一棵树」的那一层**（以及它需要的树层收缩）。
所以 L5a 的真实缺口 = **算法粘合层 ＋ 树层收缩 ＋ 归纳**，与派单判断一致。

## 1 本文件已证（全部是既有定理的 NJ-步重述，不新增假设）

| 定理 | 内容 | 依据 |
|---|---|---|
| `njStep` | `a ≠ b` 且 `Q_δ(a,b)` 全局最小 | 定义 |
| `njStep_isCherry` | 正权实现树 ⇒ 该对是 `δ` 的樱桃（**第一步正确**） | ★★★ `nj_cherry_of_hasPositiveRealization` |
| `njStep_quartet` | 该对给出所有含它的 quartet 的分裂 | ★★ `max_z_gives_split_of_hasPositiveRealization` |
| `mergeStep` | 归约 `θ = ½`（`δ(u,·) = ½(δ(x,·)+δ(y,·))`） | ★★★ `mergeDissim` |
| `mergeStep_fourPoint` | 归约保持四点条件 | ★★★ `mergeDissim_fourPoint` |
| `mergeStep_card` | 归约后基数 `+1 =` 原基数（递降尺度） | ★★★ `card_mergeIdx` |

## 2 卡在哪一步（一句话）

> **`δ.HasPositiveRealization → δ.IsCherry x y → (mergeStep δ x y).HasPositiveRealization`**
> —— 即「**树层樱桃收缩**」：把 `{x,y}` 换成挂在樱桃中点 `w` 上的单叶 `u`（边权 `½(w_x+w_y)`），
> 并把它与原树的距离矩阵对齐。库内**没有**这条引理（度量侧有 `mergeDissim`，树侧没有对应物）。

## 3 方案（三步；工作量按 W46 实读源码估）

### 步骤 A｜树层收缩（**150–250 行**，L5a 的唯一实质工作）

设 `T : Phylogram X`、`T.IsCherry x y`（取公共邻居 `w`，`haw : Adj (leaf x) w`、`hbw : ...`），
`T` 边权全正。构造 `T' : Phylogram (MergeIdx X x y)`：

* 顶点集：`V' := {v : T.V // v ≠ T.leaf y}`（**删掉叶 `y`**，别的都不动）；
  `leaf' : MergeIdx X x y ↪ V'`：`Sum.inl a ↦ ⟨T.leaf a, _⟩`、`Sum.inr () ↦ ⟨T.leaf x, _⟩`；
* 图：`T.graph.induce {v | v ≠ T.leaf y}`（诱导子图）；
  **树性**：无圈子图 + 删叶保持连通（`T.graph` 是树、`T.leaf y` 度为 1）；
* 边权：`w' e := if e = s(leaf x, w) then ½ * (w ⟨x,w⟩ + w ⟨y,w⟩) else T.w e`（其余原样）；
* **距离对齐（关键引理）**：对 `u v : MergeIdx X x y`，
  `T'.dist (leaf' u) (leaf' v) = (mergeStep (dissOf T) x y).val u v`。
  - 旧–旧：`T'.dist = T.dist`（`T'.dist` 与 `T.dist` 在删叶后一致 —— 需一条「删叶不改路径长」的引理）；
  - 新–旧：`T'.dist (leaf x) (leaf a) = ½(w_x+w_y) + d(w, a)`
    （`Phylogram.dist_eq_add_of_adj_leaf_dist`）；
    右端 `½(d(x,a)+d(y,a)) = ½(w_x + d(w,a) + w_y + d(w,a)) = ½(w_x+w_y) + d(w,a)` ✓。
  ★ 这一步**不需要**新数学，全是「删一个度为 1 的顶点」的图论 + 一次算术
  （`Phylogram` 的三条桥接引理已在 `Phylo/Algorithm/NJHardCore.lean:77–122`，
  `Phylo/PhylogramContract.lean` 有 `suppressGraph`/`suppressLeaf` 可参照）。

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

**合计 310–490 行**，超出派单给的 100–250 行预算 ⇒ 按派单 §3.7 的**允许出口**：
`njAdditiveGap` 保留，台账不变（仍 74）。

## 4 诚实边界

* 本文件**没有**证明 `nj_recovers_topology_additive`；`CASTERNJ.njAdditiveGap` 仍是 `def … : Prop`。
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
