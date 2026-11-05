/-
Copyright (c) 2026 ASTER Lab. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.NJRecovers
import Phylo.BunemanGraft
import Phylo.CladogramBuild
import Phylo.Stat.CASTERNJ

/-!
# `Phylo.Stat.NJRun` —— L5a 步骤 B：**让 `nj_recovers_topology_additive` 名副其实**

派单：`W47_TO_DSH_prompt.txt` M2。目标签名（**照抄，不改**）：

```lean
noncomputable def njRun (δ : NJ.Dissimilarity X) (hcard : 3 ≤ Fintype.card X) : Cladogram X

theorem njRun_correct_additive (δ : NJ.Dissimilarity X) (hcard : 3 ≤ Fintype.card X)
    (T : Phylogram X) (hw : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hbin : T.toCladogram.IsBinary)
    (hreal : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    Nonempty (Iso (njRun δ hcard) T.toCladogram)
```

⚠️ **本文件当前只有方案**（W47 的第一个 commit）。实现分四步落地，
每步一个 commit，见下面的 §5。

## 1 递归载体：哪个类型在变、怎么还原到 `X`

`njRun` 对 `Fintype.card X` 做**良基递归**（`termination_by Fintype.card X`）：

* 每轮取 `njStep δ a b`（`Q` 全局最小对，★★ `NJRecovers.exists_njStep`），
  递归到 `mergeStep δ a b : Dissimilarity (MergeIdx X a b)`；
* **类型在变**：`X ↝ MergeIdx X a b = ↾(univ \ {a,b}) ⊕ Unit`（少一个标签、多一个合并点）；
* **测度下降**：★★★ `mergeStep_card : card (MergeIdx X a b) + 1 = card X`；
* **还原到 `X`**：递归结果 `C : Cladogram (MergeIdx X a b)` 经
  **`graftCladogram`**（`Phylo/BunemanGraft.lean:613`，W27 已证）拉回
  `Cladogram X` —— 它把 `{a,b}` 作为两片新叶挂到 `C` 的合并叶 `t := C.leaf (Sum.inr ())` 上。

**为什么要一层 `Cladogram.relabel`**：`graftCladogram` 的输入标签类型钉死为
`BunemanShrink Y p q = {x // x ≠ p ∧ x ≠ q} ⊕ Unit`（`Buneman.lean:369`），
而 `MergeIdx X a b = ↾(univ \ {a,b}) ⊕ Unit`（`AttesonRadius.lean:1256`）——
**两者只在子类型的写法上不同**（Finset 归属 vs 命题）。故补
`Cladogram.relabel (e : X ≃ Y) : Cladogram X → Cladogram Y`（叶子重标号，顶点集不动，~15 行），
用它把递归结果搬到 `graftCladogram` 的输入类型上。
⇒ **不重写 `graftCladogram`**（它的 `isTree` / 度数 / 叶判别已经证好）。

★ **为什么不用「`Σ Y, Cladogram Y` ＋ split 表」那条路**（派单推荐的形态）：
本路线**不需要** split 表 —— graft 是**自底向上造树**，每轮的樱桃 `{a,b}` 由 graft 的
两片新叶**直接体现**，比「记 split 再重建」少一层数据（也少一层「split 集 ⇒ 存在树」的欠账）。

## 2 每轮 split 怎么记、怎么拉回

**不显式记**。每轮 `{a,b}` 成为 graft 后树的两片新叶（同一顶点 `t` 的两个子树），
即这一轮的 split 是 `{a,b} | 其余`；因为 `t` 就是上一层的 `mergeQ` 合并点，
所以 split 自动落在**上一层**的标签集上，上一层的 graft 再把它往前带。
⇒ 「拉回 `X`」由 graft 的**嵌套**自动完成，无需幂等的 `MergeIdx → X` 映射。

## 3 归纳怎么走（`njReductionStep` 用在哪一步）

对 `Fintype.card X` 强归纳，结论取

　`∀ δ, 3 ≤ card X → Iso (njRun δ hcard) T.toCladogram`（`T` 固定）。

* **基例 `card X = 3`**：三标签树上任意两棵 `Cladogram` 同构
  （★ 新引理 `Cladogram.iso_of_card_le_three`，靠「无度 2 ＋ 叶判别」夹出唯一的内部点）。
* **归纳步 `card X ≥ 4`**：
  1. ★★ `exists_njStep` 取 `(a,b)`；★★★ `NJShrink.isCherry_of_njStep` 得 `T.IsCherry a b`
     —— **这一步就是 `njStep` 真的被用到的位置**（`Q` 最小 ⇒ 真樱桃）；
  2. ★★★ `CASTERNJ.njReductionStep`（**此处用**）：`HasPosRealBinary δ → HasPosRealBinary (mergeStep δ a b)`
     ⇒ 收缩树 `shrinkPhylogram T …` 是 `mergeStep δ a b` 的**正权二叉实现**，
     于是**归纳假设**（用在 `δ' := mergeStep δ a b`、`T' := shrinkPhylogram T …` 上）给出
     `Iso (njRun δ' hcard') (shrinkPhylogram T …).toCladogram`；
  3. **graft 抬升**：`Iso C C' → Iso (graft C) (graft C')`（★ 新引理 `graftCladogram_iso_congr`），
     再拼上 ★ 新引理 **`graft_shrink_iso`**：`Iso (graft (shrink T)) T`。

## 4 退化情形

* `card X = 3`：`njRun` 无**非凡** split 可产出 ⇒ 返回**任意** `Cladogram X`
  （`exists_cladogram_of_compatible ∅`，`Phylo/Supertree.lean:310`，`3 ≤ card` 是其前提）；
  正确性靠 `iso_of_card_le_three`（三标签拓扑唯一）。
* `card X ≤ 2`：**不在签名范围内**（`hcard : 3 ≤ card X`）—— 这是 W46 陈述更正的结果
  （`|X| = 2` 归约后只剩一个标签，单标签集上不存在 `Cladogram`，见
  ★★ `CASTERNJ.not_cladogram_of_subsingleton`）。
* `MergeIdx` 上的中间层：`card ≥ 3` 保证每层都能递归（`card X ≥ 4 ⇒ card (MergeIdx X a b) ≥ 3`）。

## 5 工量与施工顺序（★ 实测值，实现完回填）

| 步 | 内容 | 估 | 状态 |
|---|---|---|---|
| B-0 | 本方案 commit | — | ✅ W47 |
| B-1 | `Cladogram.relabel` ＋ `Cladogram.iso_of_card_eq_three`（★ 实测：`relabelCladogram` ＋ 搬运件 ＋ B-1d 的三条度事实） | 90 | **✅ W47** |
| B-2 | `graftCladogram_iso_congr`（iso 沿 graft 抬升） | 80 | **✅ W47**（实测 55 行） |
| B-3 | ★ **`graft_shrink_iso`**：`Iso (graft (shrink T)) T`（本步最难） | 200 | **✅ W47**（实测 ≈240 行） |
| B-4 | `njRun`（`Nat` 结构化递降）＋ `njRun_correct_additive` | 120 | **✅ W47**（实测 ≈210 行） |

**W47 实测合计 ≈ 500 行**（含方案头与文档）。派单未给预算；
W46 估的 80–120 行**明显偏低**，因为当时没算
`graft_shrink_iso` —— 它是「`isotopic` 的逆手术」在 `Cladogram` 层的显式同构）。

**`graft_shrink_iso` 的关键观测**（B-3 的全部难度都在这里）：
`shrinkPhylogram` 删掉了叶 `b` 与中点 `w`、并把 `leaf a` 直接接到 `z`。
故 graft 回去时，收缩树里**名为 `leaf a` 的那个顶点实际上站在樱桃中点 `w` 的位置**（度 3），
⇒ 同构 `φ : ShrinkV ⊕ Fin 2 ≃ T.V` 取
`φ (inl ⟨v, _⟩) = if v = T.leaf a then w else v`、`φ (inr 0) = T.leaf a`、`φ (inr 1) = T.leaf b`。
邻接的三类情形各用一条度事实：`deg (leaf a) = 1`（唯一邻居 `w`）、`deg w = 3`
（邻居恰是 `leaf a`、`leaf b`、`z`，★★★ `NJShrink.degree_eq_three`）。

## 5′ 引用口径（★ 每一行号都经协调侧 `sed -n` 现场核对，2026-11-05 W47 补）

本文件的主定理是 **NJ 对可加矩阵的正确性**，出处必须按下面写，**不许含糊**：

* **主定理** `njRun_correct_additive` ＝ **Studier & Keppler 1988**
  （`references/md/StudierKeppler1988_NoteNeighborJoiningAlgorithm.md`）
  · **`:20-22`** 定理陈述：「NJ method, for estimating an additive tree from a distance matrix D.
    If D is treelike …, then the NJ method correctly reconstructs」；
  · **`:321-329`** 证明骨架：「The theorem is easily verified for any tree in which N ≤ 4, so let N ≥ 5」。
  **原假设 = 「all branches are positive」＋ 二叉** ⇒ 正是本文件的 `hw`（边权全正）与 `hbin`（`IsBinary`）。
  ⚠️ 这也是为什么 `njRun_correct_additive` 带 `hbin`：**不是**我们的额外要求，是文献的原假设。
* **单步**（`Q` 的最小对是樱桃）＝ **Mihaescu–Levy–Pachter 2006**
  （`references/md/MihaescuLevyPachter2006_WhyNeighborJoiningWorks.md`）**`:135-139` Theorem 1**
  —— 原文把这条同时归于 Saitou–Nei [24] 与 Studier–Keppler [28]。
  库内同一句的无条件形态是 ★★★ `maxZCherryCore`（`Phylo/Algorithm/NJHardCore.lean:308`）；
  本文件经 ★★★ `NJShrink.isCherry_of_njStep` 使用它。
* **归约**（θ = ½）＝ MLP2006 **`:141-148`**：「replace the putative cherry a and b with a leaf j_ab,
  and construct a new dissimilarity map where δ(i, j_ab) = ½(δ(i,a) + δ(i,b))」＝ `mergeStep`。
* **基例的差异要说清**：SK1988 的基例是 `N ≤ 4`，**本实现用 `card = 3`**（`njBase`：二叉树上三叶
  拓扑唯一），`card = 4` 仍走递归（归约到 3）。比文献多走一轮，但基例的「拓扑唯一」是免费的
  （★★ `Cladogram.iso_of_card_eq_three`）。这是**实现选择**，不是与文献的分歧。
* ⚠️ **不许把 Saitou–Nei 1987 当证明出处**：SK1988 **`:46`** 逐字说 SN 的证明
  「is incorrect. We describe the error and supply a correct proof below」，**`:315`** 说它
  「misapply the induction」⇒ SN1987 只引**算法本身**（「SN1987 提出 NJ」），不引证明。

## 6 忠实性边界（★ 写在这里，别误传）

* 本文件的定理**只覆盖可加情形**（`δ` 有正权二叉实现）。`njRun` 对**任意** `δ` 都有定义
  （它只要求 `3 ≤ card X`），但 `njRun_correct_additive` 的正确性依赖 `δ` 可实现 ——
  **不能**推广到 CASTER 的 `D̃`（那是 `CASTERNJ.njConsistencyGap` 的建模问题）。
* 结论里的 `njRun` 是**真递归**（每轮 `njStep` 取 `Q` 最小对并合并），
  **不是**「存在性抽取」：graft 用的 `graftCladogram` 是**无条件的树手术**，
  与「是否存在实现树」无关。
* **W47 落地状态**：`njRun` 与 ★★★ `njRun_correct_additive` **均已证**（本文件 §B-4a/B-4b），
  零 `sorry`/`axiom`/`opaque`；公理依赖 `Classical.choice, Quot.sound, propext`
  （与库内其余 68 条收口定理同一标准集）。
-/

namespace Phylo.Stat.NJRun

open Phylo NJ Phylo.Stat.CASTERNJStep Phylo.Stat.CASTERNJ Phylo.Stat.NJRecovers

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## B-1a｜标签集的搬运：`MergeIdx X a b ≃ BunemanShrink X a b`

`MergeIdx X a b = ↥(univ \ {a,b}) ⊕ Unit`（`AttesonRadius.lean:1256`，子类型由 **Finset 归属**给出）
与 `BunemanShrink X a b = {x // x ≠ a ∧ x ≠ b} ⊕ Unit`（`Buneman.lean:369`，子类型由**命题**给出）
只差子类型的写法。`graftCladogram`（`BunemanGraft.lean:613`）只吃后者，故补这一条等价
＋ `Cladogram.relabel`（叶子重标号，顶点集与图**不动**）把递归结果搬过去。 -/

/-- ★★ **`MergeOld X a b ≃ {x // x ≠ a ∧ x ≠ b}`**（Finset 归属 ↔ 命题，恒等映射）。 -/
def mergeOldEquiv (a b : X) :
    NJ.Dissimilarity.MergeOld X a b ≃ {x : X // x ≠ a ∧ x ≠ b} where
  toFun x := ⟨x.1, by
    have h := x.2
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h.2⟩
  invFun x := ⟨x.1, by
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Finset.mem_univ _, x.2⟩⟩
  left_inv x := by rfl
  right_inv x := by rfl

/-- ★★ **`MergeIdx X a b ≃ BunemanShrink X a b`**（两边都是 `_ ⊕ Unit`）。 -/
def mergeIdxEquiv (a b : X) :
    NJ.Dissimilarity.MergeIdx X a b ≃ NJ.Dissimilarity.BunemanShrink a b :=
  Equiv.sumCongr (mergeOldEquiv a b) (Equiv.refl Unit)

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- ★★ **叶子重标号**：`Cladogram X ≃ Cladogram Y` 沿标签等价（顶点集、图、树性**全不动**，
只有 `leaf` 换掉）。这是 `graftCladogram` 之前必须的一层搬运。 -/
def relabelCladogram (T : Cladogram X) (e : X ≃ Y) : Cladogram Y where
  V := T.V
  fintypeV := T.fintypeV
  decEqV := T.decEqV
  graph := T.graph
  decAdj := T.decAdj
  isTree := T.isTree
  leaf := e.symm.toEmbedding.trans T.leaf
  leaf_iff_degree_one := by
    intro v
    show (∃ y : Y, T.leaf (e.symm y) = v) ↔ _
    rw [show (∃ y : Y, T.leaf (e.symm y) = v) ↔ (∃ x : X, T.leaf x = v) from
      ⟨fun ⟨y, h⟩ => ⟨e.symm y, h⟩, fun ⟨x, h⟩ => ⟨e x, by simpa using h⟩⟩]
    exact T.leaf_iff_degree_one v
  no_degree_two := T.no_degree_two

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
@[simp] theorem relabelCladogram_leaf (T : Cladogram X) (e : X ≃ Y) (y : Y) :
    (relabelCladogram T e).leaf y = T.leaf (e.symm y) := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
@[simp] theorem relabelCladogram_graph (T : Cladogram X) (e : X ≃ Y) :
    (relabelCladogram T e).graph = T.graph := rfl

-- 与 `Phylo.BunemanGraft` 对 `graftCladogram`、`Phylo.NJShrink` 对 `shrinkCladogram` 的处理一致：
-- `V`／`graph` 投影要能在 `reducible` 透明层归约，B-3 的显示式装配才能把
-- `(graft … (relabel … (shrink …))).V` 与 `ShrinkV T b w ⊕ Fin 2` 认成同一个类型。
attribute [reducible] relabelCladogram

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- ★★ **`relabelCladogram` 在「老标号」处取值**：`(relabel C e).leaf (e x) = C.leaf x`
（B-3 的 `leaf_compat` 与「收缩树的中心」两处都要用它把 `relabel` 剥掉）。 -/
@[simp] theorem relabelCladogram_leaf_apply (T : Cladogram X) (e : X ≃ Y) (x : X) :
    (relabelCladogram T e).leaf (e x) = T.leaf x := by
  rw [relabelCladogram_leaf, Equiv.symm_apply_apply]

/-- ★★ **`mergeIdxEquiv` 在合并标签上不动**（两边都是 `Sum.inr u`）。 -/
@[simp] theorem mergeIdxEquiv_inr (a b : X) (u : Unit) :
    mergeIdxEquiv a b (Sum.inr u) = Sum.inr u := rfl

/-- ★★ **`mergeIdxEquiv.symm` 在合并标签上不动**（B-3 里「收缩树的中心」用它）。 -/
@[simp] theorem mergeIdxEquiv_symm_inr (a b : X) (u : Unit) :
    (mergeIdxEquiv a b).symm (Sum.inr u) = Sum.inr u := rfl

/-- ★★ **`mergeOldEquiv` 不动分量**（两边子类型的 `.1` 相同）。 -/
@[simp] theorem mergeOldEquiv_val (a b : X) (x : NJ.Dissimilarity.MergeOld X a b) :
    ((mergeOldEquiv a b) x).1 = x.1 := rfl

@[simp] theorem mergeOldEquiv_symm_val (a b : X)
    (x : {y : X // y ≠ a ∧ y ≠ b}) : ((mergeOldEquiv a b).symm x).1 = x.1 := rfl

/-! ## B-1d｜`graft_shrink_iso` 需要的三条**度事实**

（B-3 的 9 类邻接情形全靠它们；与 `NJShrink.shrinkGraph` 的显示式定义配着用。） -/

variable {T : Phylogram.{0, 0} X} {a b : X} {w z : T.V}

/-- ★★ **樱桃中点的邻居恰是 `{T.leaf a, T.leaf b, z}`**。

`deg w = 3`（★★★ `NJShrink.degree_eq_three`，用 `IsBinary`），且三个点是**已知**的邻点、
两两互异 ⇒ 邻居集 `⊆ {…}` 且同为三元 ⇒ 相等。 -/
theorem midpoint_neighborFinset (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) :
    T.graph.neighborFinset w = ({T.leaf a, T.leaf b, z} : Finset T.V) := by
  have h3 : T.graph.degree w = 3 := NJShrink.degree_eq_three T hbin hab haw hbw
  have hcard : (T.graph.neighborFinset w).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact h3
  have hdist : ({T.leaf a, T.leaf b, z} : Finset T.V).card = 3 := by
    have hab' : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
    have h1 : T.leaf a ∉ ({T.leaf b, z} : Finset T.V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab', Ne.symm hza⟩
    have h2 : T.leaf b ∉ ({z} : Finset T.V) := by
      simp only [Finset.mem_singleton]
      exact Ne.symm hzb
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hsub : ({T.leaf a, T.leaf b, z} : Finset T.V) ⊆ T.graph.neighborFinset w := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv1 | hv2 | hv3
    · rw [hv1]; exact (SimpleGraph.mem_neighborFinset T.graph w (T.leaf a)).mpr haw.symm
    · rw [hv2]; exact (SimpleGraph.mem_neighborFinset T.graph w (T.leaf b)).mpr hbw.symm
    · rw [hv3]; exact (SimpleGraph.mem_neighborFinset T.graph w z).mpr hwz
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- ★★★ **`w` 的邻接刻画**：`Adj w v ↔ v ∈ {leaf a, leaf b, z}`。 -/
theorem midpoint_adj_iff (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (v : T.V) :
    T.graph.Adj w v ↔ (v = T.leaf a ∨ v = T.leaf b ∨ v = z) := by
  rw [← SimpleGraph.mem_neighborFinset,
    midpoint_neighborFinset hab hbin haw hbw hwz hza hzb]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- ★★ **樱桃的两片叶不相邻**（否则 `leaf b` 的唯一邻居 `w` 就成了叶，与 `deg w = 3` 矛盾）。 -/
theorem not_adj_cherry_leaves (hab : a ≠ b) (_hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) :
    ¬ T.graph.Adj (T.leaf a) (T.leaf b) := by
  intro h
  have hbw' : T.leaf b = w := NJShrink.leaf_a_adj_eq_midpoint T haw (T.leaf b) h
  exact NJShrink.not_isLeaf_of_two_adj T hab haw hbw ⟨b, hbw'⟩

/-! ### B-3 的显示式求值件

收缩树的 `leaf`（★★ `NJShrink.leafShrink`）是**逐构造子**定义的，故 `Subtype.val` 直接归约。
B-3 的 `leaf_compat` 与全部邻接情形都靠这两条把 `⟨·, ·⟩` 的证明成分抹掉（`rfl` 即可，
这正是「显示式归约」层要钉死的第一件事）。 -/

@[simp] theorem leafShrink_val_inl (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    {x : NJ.Dissimilarity.MergeOld X a b} :
    (NJShrink.leafShrink T hbin hab haw hbw (Sum.inl x)).1 = T.leaf x.1 := rfl

@[simp] theorem leafShrink_val_inr (hbin : T.toCladogram.IsBinary) {a b : X} (hab : a ≠ b)
    {w : T.V} (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w) (u : Unit) :
    (NJShrink.leafShrink T hbin hab haw hbw (Sum.inr u)).1 = T.leaf a := rfl

/-! ### B-3 的 **inl–inl** 情形

`shrinkGraph` 的邻接是**显示式**析取
`T.Adj u.1 v.1 ∨ (u.1 = leaf a ∧ v.1 = z) ∨ (u.1 = z ∧ v.1 = leaf a)`；
换名 `u.1 ↦ (if u.1 = leaf a then w else u.1)` 之后，「假边」`leaf a — z` 恰变成真边 `w — z`。
四个子情形分别用 `leaf_a_adj_eq_midpoint`（`leaf a` 的唯一邻居是 `w`）与
★ `midpoint_adj_iff`（`w` 的邻居恰是三点）。 -/
theorem shrinkGraph_adj_rename (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (u v : NJShrink.ShrinkV T b w) :
    (NJShrink.shrinkGraph T a b w z hza).Adj u v ↔
      T.graph.Adj (if u.1 = T.leaf a then w else u.1)
        (if v.1 = T.leaf a then w else v.1) := by
  classical
  rcases Classical.em (u.1 = T.leaf a) with hu | hu <;>
    rcases Classical.em (v.1 = T.leaf a) with hv | hv
  · have huv : u = v := Subtype.ext (hu.trans hv.symm)
    subst huv
    have hw : (if u.1 = T.leaf a then w else u.1) = w := ite_eq_left hu
    rw [hw]
    exact ⟨fun h => absurd h ((NJShrink.shrinkGraph T a b w z hza).loopless.irrefl u),
           fun h => absurd h (T.graph.loopless.irrefl w)⟩
  · rw [ite_eq_left hu, ite_eq_right hv]
    have hL : (NJShrink.shrinkGraph T a b w z hza).Adj u v ↔ v.1 = z := by
      constructor
      · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
        · exact absurd (NJShrink.leaf_a_adj_eq_midpoint T haw v.1 (hu ▸ h1)) v.2.2
        · exact h3
        · exact absurd (hu ▸ h2) (fun h => hza h.symm)
      · intro hz; exact Or.inr (Or.inl ⟨hu, hz⟩)
    have hR : T.graph.Adj w v.1 ↔ v.1 = z := by
      rw [midpoint_adj_iff hab hbin haw hbw hwz hza hzb]
      simp [hv, v.2.1]
    exact hL.trans hR.symm
  · rw [ite_eq_right hu, ite_eq_left hv]
    have hL : (NJShrink.shrinkGraph T a b w z hza).Adj u v ↔ u.1 = z := by
      constructor
      · rintro (h1 | ⟨h2, h3⟩ | ⟨h2, h3⟩)
        · exact absurd (NJShrink.leaf_a_adj_eq_midpoint T haw u.1 (hv ▸ h1.symm)) u.2.2
        · exact absurd (hv ▸ h3) (fun h => hza h.symm)
        · exact h2
      · intro hz; exact Or.inr (Or.inr ⟨hz, hv⟩)
    have hR : T.graph.Adj u.1 w ↔ u.1 = z := by
      rw [SimpleGraph.adj_comm, midpoint_adj_iff hab hbin haw hbw hwz hza hzb]
      simp [hu, u.2.1]
    exact hL.trans hR.symm
  · rw [ite_eq_right hu, ite_eq_right hv]
    constructor
    · rintro (h1 | h2 | h3)
      · exact h1
      · exact absurd h2.1 hu
      · exact absurd h3.2 hv
    · exact Or.inl

/-! ### B-3 的 **inl–inr** 与 **inr–inr** 情形

`graftGraph` 把它们写成显示式：`Adj (inl x) (inr i) ↔ x = t`（`t` 是挂叶的锚点）、
`¬ Adj (inr i) (inr j)`。故左侧只与「`u` 是不是锚点」有关，右侧用
`midpoint_adj_iff`（锚点 `t` 的换名像是 `w`，邻居恰是 `leaf a, leaf b, z`）判。 -/

theorem graftGraph_adj_rename_inl_inr (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (t : NJShrink.ShrinkV T b w) (ht : t.1 = T.leaf a) (u : NJShrink.ShrinkV T b w)
    (j : Fin 2) :
    (Phylo.graftGraph (NJShrink.shrinkGraph T a b w z hza) t).Adj (Sum.inl u) (Sum.inr j) ↔
      T.graph.Adj (if u.1 = T.leaf a then w else u.1)
        (if j = (0 : Fin 2) then T.leaf a else T.leaf b) := by
  classical
  rw [Phylo.graftGraph_adj_inl_inr]
  constructor
  · rintro rfl
    rcases Classical.em (j = (0 : Fin 2)) with hj | hj
    · rw [ite_eq_left hj, ite_eq_left ht]; exact haw.symm
    · rw [ite_eq_right hj, ite_eq_left ht]; exact hbw.symm
  · intro h
    by_contra hne
    have hne' : u.1 ≠ T.leaf a := fun h1 => hne (Subtype.ext (h1.trans ht.symm))
    rw [ite_eq_right hne'] at h
    rcases Classical.em (j = (0 : Fin 2)) with hj | hj
    · rw [ite_eq_left hj] at h
      exact absurd (NJShrink.leaf_a_adj_eq_midpoint T haw u.1 h.symm).symm (Ne.symm u.2.2)
    · rw [ite_eq_right hj] at h
      exact absurd (NJShrink.leaf_b_adj_eq_midpoint T hbw u.1 h.symm).symm (Ne.symm u.2.2)

theorem graftGraph_adj_rename_inr_inr (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (t : NJShrink.ShrinkV T b w) (i j : Fin 2) :
    (Phylo.graftGraph (NJShrink.shrinkGraph T a b w z hza) t).Adj (Sum.inr i) (Sum.inr j) ↔
      T.graph.Adj (if i = (0 : Fin 2) then T.leaf a else T.leaf b)
        (if j = (0 : Fin 2) then T.leaf a else T.leaf b) := by
  classical
  refine ⟨fun h => absurd h (Phylo.graftGraph_adj_not_inr_inr
    (G := NJShrink.shrinkGraph T a b w z hza) (t := t)), ?_⟩
  intro h
  rcases Classical.em (i = (0 : Fin 2)) with hi | hi <;>
    rcases Classical.em (j = (0 : Fin 2)) with hj | hj
  · rw [ite_eq_left hi, ite_eq_left hj] at h
    exact absurd h (T.graph.loopless.irrefl (T.leaf a))
  · rw [ite_eq_left hi, ite_eq_right hj] at h
    exact absurd h (not_adj_cherry_leaves hab hbin haw hbw)
  · rw [ite_eq_right hi, ite_eq_left hj] at h
    exact absurd h.symm (not_adj_cherry_leaves hab hbin haw hbw)
  · rw [ite_eq_right hi, ite_eq_right hj] at h
    exact absurd h (T.graph.loopless.irrefl (T.leaf b))

/-! ### B-3 的 **inr–inl** 情形

由 `SimpleGraph.adj_comm` 在**两边**同时换向，归约到已证的 **inl–inr**（`φ` 的求值形状
在换向后恰好对上）；这样九类邻接情形就都齐了，装配交给下面的 `graft_shrink_iso`。 -/

theorem graftGraph_adj_rename_inr_inl (hab : a ≠ b) (hbin : T.toCladogram.IsBinary)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hwz : T.graph.Adj w z) (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b)
    (t : NJShrink.ShrinkV T b w) (ht : t.1 = T.leaf a) (i : Fin 2)
    (u : NJShrink.ShrinkV T b w) :
    (Phylo.graftGraph (NJShrink.shrinkGraph T a b w z hza) t).Adj (Sum.inr i) (Sum.inl u) ↔
      T.graph.Adj (if i = (0 : Fin 2) then T.leaf a else T.leaf b)
        (if u.1 = T.leaf a then w else u.1) :=
  (SimpleGraph.adj_comm _ (Sum.inr i) (Sum.inl u)).trans
    ((graftGraph_adj_rename_inl_inr hab hbin haw hbw hwz hza hzb t ht u i).trans
      (SimpleGraph.adj_comm _ (if u.1 = T.leaf a then w else u.1)
        (if i = (0 : Fin 2) then T.leaf a else T.leaf b)))

/-! ## B-3｜★★★ **`graft_shrink_iso`**：`Iso (graft (shrink T)) T`

收缩树删掉了叶 `T.leaf b` 与樱桃中点 `w`，并把 `T.leaf a` 直接接到 `z` 上；
故 graft 回来时，收缩树里**名为 `T.leaf a` 的那个顶点实际上站在中点 `w` 的位置**（度 3）。
同构取

　`φ (inl ⟨v,·⟩) = if v = T.leaf a then w else v`、`φ (inr 0) = T.leaf a`、`φ (inr 1) = T.leaf b`。

* 邻接：九类情形归到上面三条（★★★ `shrinkGraph_adj_rename`、★★ `…_inl_inr`、★★ `…_inr_inr`），
  inr–inl 由 ★ `graftGraph_adj_rename_inr_inl`；
* **单射**：`w` 只由 `inl ⟨T.leaf a,·⟩` 取到（`ShrinkV` 的成员**排除了 `w`**），
  两片新叶分别是 `T.leaf a`、`T.leaf b`（`T.leaf a ≠ T.leaf b`，`w` 与二者都相邻故不等），
  `Fin 2` 那一片靠 `hg`（`i ↦ if i = 0 then a else b` 单射）；
* **满射**：`T.V` 的每点 `v` 分四类 —— `v = w`（取 `inl ⟨T.leaf a,·⟩`）、
  `v = T.leaf a`（取 `inr 0`）、`v = T.leaf b`（取 `inr 1`）、其余（取 `inl v`，
  因为 `v ∉ {T.leaf b, w}` 正是 `ShrinkV` 的成员条件）。 -/
theorem graft_shrink_iso (hbin : T.toCladogram.IsBinary) (hab : a ≠ b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hza : z ≠ T.leaf a) (hzb : z ≠ T.leaf b) (hwz : T.graph.Adj w z) :
    Nonempty (Iso (graftCladogram (p := a) (q := b) hab
      (relabelCladogram (NJShrink.shrinkCladogram T hbin hab haw hbw hza hzb hwz)
        (mergeIdxEquiv a b))) T.toCladogram) := by
  classical
  -- 收缩树的中心：`relabelCladogram` 之后它就是 `T.leaf a` 那个顶点
  let ta : NJShrink.ShrinkV T b w :=
    ⟨T.leaf a, fun h => hab (T.leaf.injective h), haw.ne⟩
  let C : Cladogram (NJ.Dissimilarity.MergeIdx X a b) :=
    NJShrink.shrinkCladogram T hbin hab haw hbw hza hzb hwz
  let C' : Cladogram (NJ.Dissimilarity.BunemanShrink a b) := relabelCladogram C (mergeIdxEquiv a b)
  let φ : (NJShrink.ShrinkV T b w ⊕ Fin 2) → T.V := fun u =>
    match u with
    | Sum.inl v => if v.1 = T.leaf a then w else v.1
    | Sum.inr i => if i = (0 : Fin 2) then T.leaf a else T.leaf b
  have hφ_inl : ∀ v : NJShrink.ShrinkV T b w,
      φ (Sum.inl v) = if v.1 = T.leaf a then w else v.1 := fun _ => rfl
  have hφ_inr : ∀ i : Fin 2,
      φ (Sum.inr i) = if i = (0 : Fin 2) then T.leaf a else T.leaf b := fun _ => rfl
  have hla : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
  -- 收缩树的中心就是 `ta`
  have hcenter : C'.leaf (Sum.inr ()) = ta := by
    show C.leaf ((mergeIdxEquiv a b).symm (Sum.inr ())) = ta
    rw [mergeIdxEquiv_symm_inr]
    exact Subtype.ext rfl
  -- graft 回去的图 = `shrinkGraph` 挂在 `ta` 上
  have hgraph : (graftCladogram (p := a) (q := b) hab C').graph
      = graftGraph (NJShrink.shrinkGraph T a b w z hza) ta := by
    show graftGraph (NJShrink.shrinkGraph T a b w z hza) (C'.leaf (Sum.inr ()))
      = graftGraph (NJShrink.shrinkGraph T a b w z hza) ta
    rw [hcenter]
  -- `C'.leaf` 在**非**樱桃标签处的取值（`relabelCladogram` 与 `leafShrink` 两层都剥掉）
  have hC'leaf : ∀ (y : X) (hy : y ≠ a) (hq : y ≠ b),
      (C'.leaf ((Sum.inl ⟨y, hy, hq⟩ : NJ.Dissimilarity.BunemanShrink a b))).1 = T.leaf y := by
    intro y hy hq
    show (NJShrink.leafShrink T hbin hab haw hbw
      (Sum.inl ((mergeOldEquiv a b).symm ⟨y, hy, hq⟩))).1 = T.leaf y
    rw [leafShrink_val_inl, mergeOldEquiv_symm_val]
  -- `Fin 2` 那一片的单射
  have hg : ∀ i j : Fin 2,
      (if i = (0 : Fin 2) then T.leaf a else T.leaf b)
        = (if j = (0 : Fin 2) then T.leaf a else T.leaf b) → i = j := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · rw [hi, hj]
      · rw [ite_eq_left hi, ite_eq_right hj] at hij
        exact absurd hij hla
    · by_cases hj : j = 0
      · rw [ite_eq_right hi, ite_eq_left hj] at hij
        exact absurd hij.symm hla
      · refine Fin.ext ?_
        have hi0 : (i : Nat) ≠ 0 := fun h => hi (Fin.ext h)
        have hj0 : (j : Nat) ≠ 0 := fun h => hj (Fin.ext h)
        have hi2 : (i : Nat) < 2 := i.isLt
        have hj2 : (j : Nat) < 2 := j.isLt
        omega
  have hinj : Function.Injective φ := by
    rintro (u | i) (v | j) h
    · simp only [hφ_inl] at h
      by_cases hua : u.1 = T.leaf a <;> by_cases hva : v.1 = T.leaf a
      · exact congrArg Sum.inl (Subtype.ext (hua.trans hva.symm))
      · rw [ite_eq_left hua, ite_eq_right hva] at h
        exact absurd h.symm v.2.2
      · rw [ite_eq_right hua, ite_eq_left hva] at h
        exact absurd h u.2.2
      · rw [ite_eq_right hua, ite_eq_right hva] at h
        exact congrArg Sum.inl (Subtype.ext h)
    · simp only [hφ_inl, hφ_inr] at h
      by_cases hua : u.1 = T.leaf a <;> by_cases hj : j = (0 : Fin 2)
      · rw [ite_eq_left hua, ite_eq_left hj] at h
        exact absurd h haw.ne.symm
      · rw [ite_eq_left hua, ite_eq_right hj] at h
        exact absurd h hbw.ne.symm
      · rw [ite_eq_right hua, ite_eq_left hj] at h
        exact absurd h hua
      · rw [ite_eq_right hua, ite_eq_right hj] at h
        exact absurd h u.2.1
    · simp only [hφ_inr, hφ_inl] at h
      by_cases hi : i = (0 : Fin 2) <;> by_cases hva : v.1 = T.leaf a
      · rw [ite_eq_left hi, ite_eq_left hva] at h
        exact absurd h haw.ne
      · rw [ite_eq_left hi, ite_eq_right hva] at h
        exact absurd h.symm hva
      · rw [ite_eq_right hi, ite_eq_left hva] at h
        exact absurd h hbw.ne
      · rw [ite_eq_right hi, ite_eq_right hva] at h
        exact absurd h.symm v.2.1
    · simp only [hφ_inr] at h
      exact congrArg Sum.inr (hg i j h)
  have hsurj : Function.Surjective φ := by
    intro v
    by_cases hv_w : v = w
    · refine ⟨Sum.inl ⟨T.leaf a, hla, haw.ne⟩, ?_⟩
      rw [hφ_inl]
      show (if T.leaf a = T.leaf a then w else T.leaf a) = v
      rw [ite_eq_left rfl, hv_w]
    · by_cases hv_a : v = T.leaf a
      · refine ⟨Sum.inr 0, ?_⟩
        rw [hφ_inr]
        show (if (0 : Fin 2) = 0 then T.leaf a else T.leaf b) = v
        rw [ite_eq_left rfl, hv_a]
      · by_cases hv_b : v = T.leaf b
        · refine ⟨Sum.inr 1, ?_⟩
          rw [hφ_inr]
          have h1 : ¬ ((1 : Fin 2) = 0) := by decide
          rw [ite_eq_right h1, hv_b]
        · refine ⟨Sum.inl ⟨v, hv_b, hv_w⟩, ?_⟩
          show φ (Sum.inl (⟨v, hv_b, hv_w⟩ : NJShrink.ShrinkV T b w)) = v
          rw [hφ_inl, ite_eq_right hv_a]
  -- 九类邻接情形
  have hadj : ∀ u v : NJShrink.ShrinkV T b w ⊕ Fin 2,
      (graftGraph (NJShrink.shrinkGraph T a b w z hza) ta).Adj u v
        ↔ T.graph.Adj (φ u) (φ v) := by
    intro u v
    rcases u with u | i
    · rcases v with v | j
      · rw [graftGraph_adj_inl_inl]
        exact shrinkGraph_adj_rename hab hbin haw hbw hwz hza hzb u v
      · exact graftGraph_adj_rename_inl_inr hab hbin haw hbw hwz hza hzb ta rfl u j
    · rcases v with v | j
      · exact graftGraph_adj_rename_inr_inl hab hbin haw hbw hwz hza hzb ta rfl i v
      · exact graftGraph_adj_rename_inr_inr hab hbin haw hbw hwz hza hzb ta i j
  -- 装配
  let e : (NJShrink.ShrinkV T b w ⊕ Fin 2) ≃ T.V := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have hadj' : ∀ {a' b' : (graftCladogram (p := a) (q := b) hab C').V},
      T.graph.Adj (e a') (e b')
        ↔ (graftCladogram (p := a) (q := b) hab C').graph.Adj a' b' := by
    intro a' b'
    rw [hgraph]
    exact (hadj a' b').symm
  have hleaf : ∀ x : X, e ((graftCladogram (p := a) (q := b) hab C').leaf x) = T.leaf x := by
    intro x
    show φ (Phylo.graftLeafFun C' x) = T.leaf x
    by_cases hxa : x = a
    · rw [Phylo.graftLeafFun_eq_inr_zero C' hxa, hφ_inr]
      show (if (0 : Fin 2) = 0 then T.leaf a else T.leaf b) = T.leaf x
      rw [ite_eq_left rfl, hxa]
    · by_cases hxb : x = b
      · rw [Phylo.graftLeafFun_eq_inr_one C' hxa hxb, hφ_inr]
        have h1 : ¬ ((1 : Fin 2) = 0) := by decide
        rw [ite_eq_right h1, hxb]
      · rw [Phylo.graftLeafFun_eq_inl C' hxa hxb, hφ_inl]
        rw [hC'leaf x hxa hxb]
        rw [ite_eq_right (fun h => hxa (T.leaf.injective h))]
  exact ⟨{ gIso := (RelIso.mk e (fun {a' b'} => by
             rw [hgraph]
             exact (hadj a' b').symm) : (graftCladogram (p := a) (q := b) hab C').graph
               ≃g T.toCladogram.graph),
           leaf_compat := hleaf }⟩

/-! ## B-2｜★★ **`graftCladogram_iso_congr`**：同构沿 graft 抬升

`graftCladogram` 是**无条件的树手术**（把两片新叶挂到 `C.leaf (Sum.inr ())` 上），
所以 `Iso C D` 可以直接抬成 `Iso (graft C) (graft D)`：

* 顶点等价取 `f := Equiv.sumCongr e.gIso.toEquiv (Equiv.refl (Fin 2))`；
* 旧–旧邻接用 `e.gIso`；挂边用 `e.leaf_compat`（`D.leaf (inr ()) = g (C.leaf (inr ()))`）
  化到 `g u = g tC ↔ u = tC`（`g` 单射）；新–新两边都假；
* 标签嵌入逐 `graftLeafFun` 的三分支对齐（`p ↦ inr 0`、`q ↦ inr 1`、其余走 `Sum.inl ∘ leaf`）。 -/
theorem graftCladogram_iso_congr {Y : Type} [Fintype Y] [DecidableEq Y] {p q : Y} (hpq : p ≠ q)
    {C D : Cladogram (NJ.Dissimilarity.BunemanShrink p q)} (e : Iso C D) :
    Nonempty (Iso (graftCladogram (p := p) (q := q) hpq C)
      (graftCladogram (p := p) (q := q) hpq D)) := by
  classical
  let g : C.V ≃ D.V := e.gIso.toEquiv
  let f : C.V ⊕ Fin 2 ≃ D.V ⊕ Fin 2 := Equiv.sumCongr g (Equiv.refl (Fin 2))
  have hf_inl : ∀ u : C.V, f (Sum.inl u) = Sum.inl (g u) := fun _ => rfl
  have hf_inr : ∀ i : Fin 2, f (Sum.inr i) = Sum.inr i := fun _ => rfl
  have hgleaf : ∀ u : NJ.Dissimilarity.BunemanShrink p q, g (C.leaf u) = D.leaf u :=
    fun u => e.leaf_compat u
  have hadj : ∀ {u v : C.V}, C.graph.Adj u v ↔ D.graph.Adj (g u) (g v) :=
    fun {u v} => e.gIso.map_rel_iff'.symm
  have hkey : ∀ u : C.V, (g u = D.leaf (Sum.inr ())) ↔ (u = C.leaf (Sum.inr ())) := by
    intro u
    have h0 : g u = g (C.leaf (Sum.inr ())) ↔ (u = C.leaf (Sum.inr ())) := g.injective.eq_iff
    rwa [hgleaf (Sum.inr ())] at h0
  have hadj' : ∀ {a b : C.V ⊕ Fin 2},
      (graftGraph D.graph (D.leaf (Sum.inr ()))).Adj (f a) (f b)
        ↔ (graftGraph C.graph (C.leaf (Sum.inr ()))).Adj a b := by
    intro a b
    rcases a with u | i <;> rcases b with v | j
    · simp only [hf_inl, graftGraph_adj_inl_inl]
      exact (hadj (u := u) (v := v)).symm
    · simp only [hf_inl, hf_inr, graftGraph_adj_inl_inr]
      exact hkey u
    · simp only [hf_inl, hf_inr, graftGraph_adj_inr_inl]
      exact hkey v
    · simp only [hf_inr]
      exact ⟨fun h => absurd h
                (graftGraph_adj_not_inr_inr (G := D.graph) (t := D.leaf (Sum.inr ()))),
             fun h => absurd h
                (graftGraph_adj_not_inr_inr (G := C.graph) (t := C.leaf (Sum.inr ())))⟩
  have hleaf : ∀ y : Y, f (Phylo.graftLeafFun C y) = Phylo.graftLeafFun D y := by
    intro y
    by_cases hyp : y = p
    · rw [Phylo.graftLeafFun_eq_inr_zero C hyp, Phylo.graftLeafFun_eq_inr_zero D hyp]
      simp only [hf_inr]
    · by_cases hyq : y = q
      · rw [Phylo.graftLeafFun_eq_inr_one C hyp hyq, Phylo.graftLeafFun_eq_inr_one D hyp hyq]
        simp only [hf_inr]
      · rw [Phylo.graftLeafFun_eq_inl C hyp hyq, Phylo.graftLeafFun_eq_inl D hyp hyq]
        simp only [hf_inl, hgleaf]
  exact ⟨{ gIso := RelIso.mk f hadj', leaf_compat := hleaf }⟩

/-! ## B-4a｜★★★ **`njRun`**：真递归的 NJ 重建（**定义**）

派单 M2 的三个反例试金石：

1. 结论里**字面出现** `njRun` —— B-4b 的 `njRun_correct_additive` 满足；
2. 返回类型是 **`Cladogram X`**（原标签集，而不是 `Σ Y, Cladogram Y`）—— 本节的签名满足；
3. 定义里**真的用 `njStep`**（每轮取 `Q` 全局最小对并合并），**不是**
   `Classical.choose (存在某棵树实现 δ)` 这种「把目标当前提」的抽取。

**递归尺度**：`n := Fintype.card Y` 对 `Nat` 结构化递降
（每轮由 ★★★ `mergeStep_card` 得 `card (MergeIdx Y a b) + 1 = card Y`）。

**基例 `card = 3`**：三标签上没有非凡 split 可产出，返回
★ `Cladogram.ofCompatibleSplits ∅ ρ`（`CladogramBuild.lean:189`；相容族取空集，
三条前提全空）。这是**纯组合**的存在性（与 `δ` 无关，只用到 `3 ≤ card Y`），
正确性由 ★★ `Cladogram.iso_of_card_eq_three` 保证（三标签拓扑唯一）。 -/

/-- ★ **`Q` 最小对的存在性**（打包成 `X × X` 上的 `∃`，便于 `Classical.choose` 一次取完）。 -/
theorem exists_njStep_pair (δ : NJ.Dissimilarity X) (h : 2 ≤ Fintype.card X) :
    ∃ p : X × X, njStep δ p.1 p.2 := by
  obtain ⟨a, b, hab⟩ := exists_njStep δ h
  exact ⟨(a, b), hab⟩

/-- ★ **NJ 第一步的选点**：`Q_δ` 的**全局最小对**（`njStep` 的见证）。

★ 它是 `δ` 的函数（只依赖 `δ` 的类型层面的数据与 `2 ≤ card` 这一**证明**），
B-4b 的正确性证明里对**同一个** `h2` 展开，因此定义与证明用的是**同一对**。 -/
noncomputable def njPick (δ : NJ.Dissimilarity X) (h : 2 ≤ Fintype.card X) : X × X :=
  Classical.choose (exists_njStep_pair δ h)

/-- ★★ **`njPick` 的规格**：选出来的对确实满足 `njStep`（互异 ＋ `Q` 全局最小）。 -/
theorem njPick_spec (δ : NJ.Dissimilarity X) (h : 2 ≤ Fintype.card X) :
    njStep δ (njPick δ h).1 (njPick δ h).2 :=
  Classical.choose_spec (exists_njStep_pair δ h)

/-! ### B-4a′｜递降尺度的**可复现**接口

★ 这三条**只依赖显式参数**（不靠 `by omega` 现推），因此
`njRunAux` 的定义体与 B-4b 的正确性证明里写出来是**同一个项**
（`njRunAux` 的递归调用要传证明，若现推 `by omega` 则定义与证明失配，
因为 `Classical.choose` 不尊重证明无关性）。 -/

/-- ★ `MergeIdx` 的基数（`njPick` 选出的那对）。 -/
theorem njPick_card (δ : NJ.Dissimilarity X) (h2 : 2 ≤ Fintype.card X) :
    Fintype.card (NJ.Dissimilarity.MergeIdx X (njPick δ h2).1 (njPick δ h2).2) + 1
      = Fintype.card X :=
  mergeStep_card (njPick_spec δ h2).1

theorem njPick_three_le {δ : NJ.Dissimilarity X} {h2 : 2 ≤ Fintype.card X}
    (h3 : 3 ≤ Fintype.card X) (hne : Fintype.card X ≠ 3) :
    3 ≤ Fintype.card (NJ.Dissimilarity.MergeIdx X (njPick δ h2).1 (njPick δ h2).2) := by
  have h := njPick_card δ h2
  omega

theorem njPick_two_le {δ : NJ.Dissimilarity X} {h2 : 2 ≤ Fintype.card X}
    (h3 : 3 ≤ Fintype.card X) (hne : Fintype.card X ≠ 3) :
    2 ≤ Fintype.card (NJ.Dissimilarity.MergeIdx X (njPick δ h2).1 (njPick δ h2).2) := by
  have h := njPick_card δ h2
  omega

theorem njPick_le_pred {δ : NJ.Dissimilarity X} {h2 : 2 ≤ Fintype.card X} {m : Nat}
    (hle : Fintype.card X ≤ m + 1) :
    Fintype.card (NJ.Dissimilarity.MergeIdx X (njPick δ h2).1 (njPick δ h2).2) ≤ m := by
  have h := njPick_card δ h2
  omega

/-- ★★ **三标签的基例树**：空相容族 ⇒ ★ `ofCompatibleSplits` 给一棵**具体的**树。
与 `δ` **无关**（这正是它不构成「把目标当前提」的理由）。 -/
noncomputable def njBase (Y : Type) [Fintype Y] [DecidableEq Y]
    (h3 : 3 ≤ Fintype.card Y) : Cladogram Y :=
  Cladogram.ofCompatibleSplits (X := Y) (fam := ∅)
    (Classical.choice (Fintype.card_pos_iff.mp (by omega)))
    (by intro s hs; simp at hs) (by intro s hs; simp at hs)
    (by intro s hs; simp at hs) h3

/-- `3 ≤ m ⇒ 2 ≤ m`（`njRun` 的内部接口：把 `hcard` 转成 `njPick` 需要的 `h2`）。 -/
theorem two_le_of_three {m : Nat} (h : 3 ≤ m) : 2 ≤ m := by omega

set_option linter.unusedVariables false in
/-- ★★★ **`njRun` 的递归核**（对 `n` 结构化递降；`hle : card Y ≤ n` 就是递降尺度）。

* `h2`／`h3` 显式传入，正确性证明里对**同一组** `h2 h3` 展开
  （否则 `njPick` 的证明参数不可复现，`Classical.choose` 不尊重证明无关性）；
* 步进：★ `njPick δ h2` 取 `Q` 最小对，`graftCladogram` 把两片新叶挂回
  `njRunAux n (MergeIdx Y a b) (mergeStep δ a b) …` 的结果上；
* 三个递降尺度用 **B-4a′ 的可复现接口**（`njPick_two_le`／`njPick_three_le`／`njPick_le_pred`）。 -/
noncomputable def njRunAux : (n : Nat) → (Y : Type) → [Fintype Y] → [DecidableEq Y] →
    (δ : NJ.Dissimilarity Y) → (h2 : 2 ≤ Fintype.card Y) → (h3 : 3 ≤ Fintype.card Y) →
    (hle : Fintype.card Y ≤ n) → Cladogram Y
  | 0, Y, _, _, _, h2, _, hle => by
      exact absurd hle (by omega)
  | n + 1, Y, _, _, δ, h2, h3, hle => by
      classical
      by_cases hcard : Fintype.card Y = 3
      · exact njBase Y h3
      · exact graftCladogram (p := (njPick δ h2).1) (q := (njPick δ h2).2)
          (njPick_spec δ h2).1
          (relabelCladogram
            (njRunAux n (NJ.Dissimilarity.MergeIdx Y (njPick δ h2).1 (njPick δ h2).2)
              (mergeStep δ (njPick δ h2).1 (njPick δ h2).2)
              (njPick_two_le h3 hcard) (njPick_three_le h3 hcard) (njPick_le_pred hle))
            (mergeIdxEquiv (njPick δ h2).1 (njPick δ h2).2))

/-- ★★★ **`njRun`**：NJ 算法在 `δ` 上的**真递归重建**（返回原标签集上的 `Cladogram X`）。

* `3 ≤ card X` 才进入递归；`card X = 3` 时返回 ★★ `njBase`（三标签拓扑唯一）；
* `card X ≥ 4` 时取 ★ `njPick δ` 的 `Q` 最小对，`mergeStep` 归约后**递归**，
  再用 ★★★ `graftCladogram` 把两片新叶挂回去 —— 每轮真用 `njStep`。 -/
noncomputable def njRun (δ : NJ.Dissimilarity X) (hcard : 3 ≤ Fintype.card X) : Cladogram X :=
  njRunAux (Fintype.card X) X δ (two_le_of_three hcard) hcard le_rfl

/-! ## B-4b｜★★★ **`njRun_correct_additive`**：`njRun` 确给出 `δ` 的拓扑

**证明骨架**（对 `n` 归纳，与 `njRunAux` 的递降同构）：

* **基例 `card Y = 3`**：`njRunAux` 取值 `njBase Y h3`；两棵三标签树同构
  （★★ `Cladogram.iso_of_card_eq_three`）。
* **步进 `card Y ≥ 4`**：`njPick δ h2 =: (a,b)`，
  ★★★ `NJShrink.isCherry_of_njStep` 给出 `T.IsCherry a b`（**这正是 `njStep` 真的被用到的位置**：
  `Q` 最小 ⇒ 真樱桃），于是
  1. ★★★ `NJShrink.shrinkPhylogram` 是 `mergeStep δ a b` 的**正权二叉实现**
     （三条不变式逐条搬自 ★★★ `njReductionStep` 的证明）；
  2. **归纳假设**给出 `Iso (njRunAux n (MergeIdx Y a b) (mergeStep δ a b) …) (shrink …).toCladogram`；
  3. ★ `relabelCladogram_iso` ＋ ★★ `graftCladogram_iso_congr` 把它抬成 graft 后的同构；
  4. ★★★ `graft_shrink_iso` 把「graft 回去的收缩树」拼回 `T.toCladogram`。 -/

/-- ★ `relabelCladogram` 保同构（顶点集与图都不动，只有标签换名）。 -/
theorem relabelCladogram_iso {Y : Type} [Fintype Y] [DecidableEq Y] (e : X ≃ Y)
    {C D : Cladogram X} (h : Iso C D) :
    Nonempty (Iso (relabelCladogram C e) (relabelCladogram D e)) := by
  refine ⟨{ gIso := h.gIso, leaf_compat := ?_ }⟩
  intro y
  show h.gIso ((relabelCladogram C e).leaf y) = (relabelCladogram D e).leaf y
  rw [relabelCladogram_leaf, relabelCladogram_leaf]
  exact h.leaf_compat (e.symm y)

set_option linter.unusedVariables false in
theorem njRunAux_correct : ∀ (n : Nat) (Y : Type) [Fintype Y] [DecidableEq Y]
    (δ : NJ.Dissimilarity Y) (h2 : 2 ≤ Fintype.card Y) (h3 : 3 ≤ Fintype.card Y)
    (hle : Fintype.card Y ≤ n)
    (T : Phylogram.{0, 0} Y) (hw : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hbin : T.toCladogram.IsBinary)
    (hreal : ∀ x y : Y, T.dist (T.leaf x) (T.leaf y) = δ.val x y),
    Nonempty (Iso (njRunAux n Y δ h2 h3 hle) T.toCladogram) := by
  intro n
  induction n with
  | zero =>
      intro Y _ _ δ h2 h3 hle T hw hbin hreal
      exact absurd hle (by omega)
  | succ n ih =>
      intro Y _ _ δ h2 h3 hle T hw hbin hreal
      classical
      by_cases hcard : Fintype.card Y = 3
      · -- 基例：三标签，拓扑唯一
        have hval : njRunAux (n + 1) Y δ h2 h3 hle = njBase Y h3 := by
          simp only [njRunAux]
          rw [dif_pos hcard]
        rw [hval]
        exact Cladogram.iso_of_card_eq_three (njBase Y h3) T.toCladogram hcard
      · -- 步进：`card Y ≥ 4`
        have hval : njRunAux (n + 1) Y δ h2 h3 hle
            = graftCladogram (p := (njPick δ h2).1) (q := (njPick δ h2).2)
                (njPick_spec δ h2).1
                (relabelCladogram
                  (njRunAux n (NJ.Dissimilarity.MergeIdx Y (njPick δ h2).1 (njPick δ h2).2)
                    (mergeStep δ (njPick δ h2).1 (njPick δ h2).2)
                    (njPick_two_le h3 hcard) (njPick_three_le h3 hcard) (njPick_le_pred hle))
                  (mergeIdxEquiv (njPick δ h2).1 (njPick δ h2).2)) := by
          simp only [njRunAux]
          rw [dif_neg hcard]
        rw [hval]
        -- 1. `njStep` 给出真樱桃（★ `Q` 最小 ⇒ 樱桃：`isCherry_of_njStep`）
        have hstep : njStep δ (njPick δ h2).1 (njPick δ h2).2 := njPick_spec δ h2
        have hc : T.IsCherry (njPick δ h2).1 (njPick δ h2).2 :=
          NJShrink.isCherry_of_njStep δ hw hreal h3 hstep
        have hckeep := hc
        obtain ⟨hab, w, haw, hbw⟩ := hc
        obtain ⟨z, hwz, hza, hzb, -⟩ := NJShrink.exists_third T hbin hab haw hbw
        have hla : T.leaf (njPick δ h2).1 ≠ T.leaf (njPick δ h2).2 ∧
            T.leaf (njPick δ h2).1 ≠ w :=
          ⟨fun h => hab (T.leaf.injective h),
           NJShrink.leaf_ne_midpoint T hbin hab haw hbw (njPick δ h2).1⟩
        have hzm : z ≠ T.leaf (njPick δ h2).2 ∧ z ≠ w :=
          ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩
        -- 2. 收缩树是 `mergeStep δ a b` 的正权二叉实现（三条不变式）
        let T' : Phylogram (NJ.Dissimilarity.MergeIdx Y (njPick δ h2).1 (njPick δ h2).2) :=
          NJShrink.shrinkPhylogram T hbin hab haw hbw hza hzb hwz hw
        have hw' : ∀ e : Edge T'.toCladogram, 0 < T'.w e := by
          intro e
          have key : ∀ e' : Sym2 (NJShrink.ShrinkV T (njPick δ h2).2 w),
              e' ∈ (NJShrink.shrinkGraph T (njPick δ h2).1 (njPick δ h2).2 w z hza).edgeSet →
              0 < NJShrink.shrinkW T (njPick δ h2).1 (njPick δ h2).2 w z hza hla hzm e' :=
            Sym2.ind (fun u v he => NJShrink.shrinkW_pos T hbin hab haw hbw hza hzb hwz hw
              hla hzm ((SimpleGraph.mem_edgeSet _).mp he))
          exact key e.1 e.2
        have hbin' : T'.toCladogram.IsBinary :=
          NJShrink.shrinkPhylogram_isBinary T hbin hab haw hbw hza hzb hwz hw
        have hreal' : ∀ u v, T'.dist (T'.leaf u) (T'.leaf v)
            = (mergeStep δ (njPick δ h2).1 (njPick δ h2).2).val u v :=
          fun u v => NJShrink.shrinkPhylogram_dist T δ hbin hab haw hbw hza hzb hwz hw hckeep hreal u v
        -- 3. 归纳假设
        have hIH := ih (NJ.Dissimilarity.MergeIdx Y (njPick δ h2).1 (njPick δ h2).2)
          (mergeStep δ (njPick δ h2).1 (njPick δ h2).2)
          (njPick_two_le h3 hcard) (njPick_three_le h3 hcard) (njPick_le_pred hle)
          T' hw' hbin' hreal'
        -- 4. 抬升：`relabel` → `graft`，再用 `graft_shrink_iso` 拼回 `T`
        obtain ⟨e1⟩ := hIH
        obtain ⟨e2⟩ := relabelCladogram_iso (mergeIdxEquiv (njPick δ h2).1 (njPick δ h2).2) e1
        obtain ⟨e3⟩ := graftCladogram_iso_congr hstep.1 e2
        obtain ⟨e4⟩ := graft_shrink_iso (T := T) (a := (njPick δ h2).1) (b := (njPick δ h2).2)
          (w := w) (z := z) hbin hab haw hbw hza hzb hwz
        exact ⟨e3.trans e4⟩

/-- ★★★ **`njRun_correct_additive`**（M2 的交付定理）：若 `δ` 有**边权全正**的
**二叉**实现树 `T`，则 `njRun δ` 与 `T` 的拓扑同构。

结论里**字面出现 `njRun`**（试金石 ①），`njRun` 返回 `Cladogram X`（②），
其定义每轮真用 `njStep`（③）。 -/
theorem njRun_correct_additive (δ : NJ.Dissimilarity X) (hcard : 3 ≤ Fintype.card X)
    (T : Phylogram.{0, 0} X) (hw : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hbin : T.toCladogram.IsBinary)
    (hreal : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    Nonempty (Iso (njRun δ hcard) T.toCladogram) := by
  have h := njRunAux_correct (Fintype.card X) X δ (two_le_of_three hcard) hcard le_rfl
    T hw hbin hreal
  have hval : njRun δ hcard
      = njRunAux (Fintype.card X) X δ (two_le_of_three hcard) hcard le_rfl := rfl
  rwa [hval]

end Phylo.Stat.NJRun
