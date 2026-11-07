/-
Copyright (c) 2026 ASTER Lab. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.CASTERNJ

/-!
# `Phylo.Stat.NJShrinkNonBinary` —— B（`njAdditiveGapUnrestricted`）的**非二叉归约**

派单：`W48_TO_DSH_prompt.txt` §B。目标缺口（**陈述一字不动**，`CASTERNJ.lean:153`）：

```lean
def njAdditiveGapUnrestricted : Prop :=
  ∀ (δ : NJ.Dissimilarity X), HasPosReal δ → 3 ≤ Fintype.card X →
    ∀ a b : X, njStep δ a b → HasPosReal (mergeStep δ a b)
```

与已收口的 `njAdditiveGap`（`:127`，前提 `HasPosRealBinary`）**只差「二叉」二字**。
二叉支的归约 = ★★★ `NJShrink.shrinkPhylogram`（删叶 `b` ＋ 中点 `w`，把 `T.leaf a` 挂到
`w` 的第三邻居 `z` 上，边权 `w_a + w_b`）；它的每一步都吃了 `deg w = 3`
（★★ `NJShrink.exists_third` 的 `hbin` 只用来推 `degree w = 3`）。

**本文件 = 方案 ＋ G1–G7 落地（B 已收口）**（W48 起，W49 续）。实现进度见 §7 的勾选列。

## 0 ★D 更正①：非二叉**不等于** `deg w ≥ 4`

派单说「非二叉（`deg w ≥ 4`）时反而更简单」。**这一句只在 `deg w ≥ 4` 时成立**：
`Cladogram.IsBinary`（`Core.lean:93`）是 `∀ v, ¬ IsLeaf v → degree v = 3`，
它的否定只给出 **∃ 某点度 ≥ 4**（用 `no_degree_two` 排除度 2）——
**不保证** `njStep` 那一轮的樱桃中点 `w` 就是那个点。
一棵「只在一个远处分支点呈 polytomy」的树，其樱桃的中点仍可能是度 3。

⇒ 正确的施工切法是**按 `w` 的度分情形**，而不是按「整棵树是否二叉」：

| 情形 | 几何 | 归约手术 |
|---|---|---|
| `degree w = 3` | `w` 的邻居恰是 `{leaf a, leaf b, z}` | **复用** ★★★ `shrinkPhylogram`（只需把 `exists_third` 的 `hbin` 换成 `degree w = 3`） |
| `degree w ≥ 4` | `w` 的邻居是 `{leaf a, leaf b} ∪ (≥2 个其余)` | **本文件的新构造**（§1–§6） |

⇒ 本文件负责**第二种**；第一种要一件 20 行的**广义化**（见 §7 的 G0）。
这同时解释了为什么「非二叉支更容易」是对的但**不完整**：更容易的只是 `deg w ≥ 4` 那半。

## 1 ★D 更正②：不需要「新叶 `u`」，`u` 就是**已有的** `T.leaf a`

派单的 sketch 是「删叶 `b`、把新叶 `u` 以权 `½(w_a+w_b)` 挂回 `w`」。实核后可以**省掉新顶点**：

`a`、`b` 都挂在中点 `w` 上 ⇒ `a` 那条悬挂边本来就是「合并后的那条边」。
只要把它的权从 `w_a` 改成 `½(w_a+w_b)`、把标签 `a` 改名成合并标签即可。
于是对任意 `x ∉ {a,b}`：

　`d'(u, x) = ½(w_a+w_b) + d'(w,x)`，而 `δ(a,x) = w_a + d(w,x)`、`δ(b,x) = w_b + d(w,x)`
　（两条路径都过 `w`）⇒ 平均恰是 `mergeStep` 的取值 ✓。

好处（两个）：
* **没有新顶点** ⇒ 顶点层不需要 graft、不需要新点与旧点的邻接分支
  （二叉支为此写了 `shrinkGraph` 的 9 类情形 ＋ 一个 `graftGraph`）；
* **没有度 2 的隐患**：`w` 的度只从 `≥4` 降到 `≥3`（不像二叉支那样降到 2，因此那边必须把 `w` 删掉）。

## 2 ① 顶点类型

```
V' := { v : T.V // v ≠ T.leaf b }            -- 只删叶 b 那**一个**顶点；`w` 保留
```

叶嵌入 `leaf' : MergeIdx X a b ↪ V'`：
`Sum.inl ⟨x, hxa, hxb⟩ ↦ ⟨T.leaf x, ·⟩`、`Sum.inr () ↦ ⟨T.leaf a, ·⟩`（`u` 认到 `leaf a` 上）。
单射性由 `T.leaf` 的单射 ＋ `MergeOld` 排除 `a,b` 给出；
成员条件是 `T.leaf x ≠ T.leaf b`（由 `x ≠ b`）与 `T.leaf a ≠ T.leaf b`（由 `a ≠ b`）。

## 3 ② 图怎么造

```
graph' := T.graph.induce (fun v => v ≠ T.leaf b)      -- `SimpleGraph.induce`
```

即「删掉顶点 `leaf b` 及它唯一那条边 `(leaf b, w)`」，其余邻接**不动**。
**没有新边**（§1 的 ★D 带来的直接好处）。

## 4 ③ 树性两半

* **无环**：`induce` 是子图，`T.isTree.isAcyclic` 沿 `Walk` 搬到子图上（子图无环）；
* **连通**：删**叶**不破坏连通。关键事实：`v ≠ T.leaf b` 时，`T` 中从 `v` 出发的路**不经 `leaf b`**
  （`leaf b` 度为 1，`T.isLeaf_iff_degree_eq_one`），故任意两点间的 `T`-路可整段留在
  `{v ≠ leaf b}` 内 ⇒ `graph'.Reachable` ✓。

## 5 ④ 度数

* `v ≠ w`：`graph'.degree ⟨v,·⟩ = T.graph.degree v` —— 邻居集只少了 `leaf b` 这一项，
  而 `¬ T.graph.Adj v (T.leaf b)`（`leaf b` 的唯一邻居是 `w`）；
* `w`：`graph'.degree ⟨w,·⟩ = T.graph.degree w - 1` —— `leaf b` 是 `w` 的邻居，删掉恰少一项。

⇒ **`no_degree_two`**：`w` 支要 `T.graph.degree w - 1 ≠ 2`；由 `3 < degree w`（情形假设 `≥ 4`）得 `≥ 3` ✓；
其余支沿用 `T.no_degree_two`。
⇒ **`leaf_iff_degree_one`**：`leaf'` 的像度 1（`leaf x` 的邻居是 `w`，未删）✓；
反向要证「`graph'` 里度 1 ⇒ 是 `leaf'` 的像」：度 1 的旧点 `v` 在 `T` 里度 ≤ 2，
`T.no_degree_two` 排除 2，非 0 ⇒ 度 1 ⇒ `v = T.leaf x`（`T.leaf_iff_degree_one`），
`x ≠ b`（否则 `v = leaf b ∉ V'`），且 `x ≠ a` 时…（`x = a` 正是 `u` 的像）✓。

## 6 ⑤ `dist` 对齐三支（`mergeStep` 的取值由 `CASTERNJStep` 给）

* **新–旧**（`u` 与 `x ∉ {a,b}`）：★★ `mergeStep_val_merged`（`CASTERNJStep.lean:185`）给
  `(mergeStep δ a b).val (mergeQ a b x) (mergeQ a b b) = ½·δ(x,a) + ½·δ(x,b)`，而
  `mergeQ a b b = Sum.inr ()`（`mergeQ_j`）；右边 = `½(w_a + d(w,x)) + ½(w_b + d(w,x)) = w_ab + d(w,x)`
  = 新树上 `d'(leaf a, leaf x)`；
* **新–新**：只有对角一处，`d'(leaf a, leaf a) = 0` = `mergeStep` 的 `diag` ✓；
* **旧–旧**（`x,y ∉ {a,b}`）：路径**不经** `leaf b`（它是叶）⇒ `d' = d`；
  `mergeStep` 在旧–旧上不变（`mergeDissim_val_old` 一线）。

## 7 ⑥ 工量与施工顺序

| 步 | 内容 | 估 | 状态 |
|---|---|---|---|
| **G0** | 把 `exists_third` 的 `hbin : IsBinary` 换成 `degree w = 3`（`NJShrink.exists_third_of_degree`，旧引理由它派生） | 20 | **✅ 已落**（实测 8 行；`hbin` 在证明里**只**经 `degree_eq_three` 用了一次，纯接口改造） |
| **G1** | `ShrinkVNB`／`shrinkGraphNB`／`leafNB` ＋ 三条求值引理 | 60 | **✅ 已落**（实测 55 行） |
| **G2** | 无环（`IsCycle.map` 沿 `Subtype.val` 搬回 `T`）＋ 连通（走法提升 `exists_walk_nb`，枢纽 `w`，路径避 `leaf b` 用 `NJShrink.not_mem_support_of_degree_one`） | 150–220 | **✅ 已落**（实测 75 行） |
| **G3** | 度数（`w` 减 1、其余不变）：`degree_nb_of_ne`（`Finset.card_bij`，关键：`leaf b` 的唯一邻居是 `w` ⇒ `¬Adj v (leaf b)`）／`degree_nb_midpoint`（`neighborFinset w`.erase `leaf b` 的双射） | 100–140 | **✅ 已落**（实测 62 行） |
| **G4** | `no_degree_two` ＋ `leaf_iff_degree_one` ＋ ★★★ `shrinkCladogramNB : Cladogram (MergeIdx X a b)` | 60–90 | **✅ 已落**（实测 100 行） |
| **G5** | 边权 `shrinkWNB`（唯一边 `{leaf a, w}` 改 `½(w_a+w_b)`，其余 `T.wExt`）＋ 非负性 ＋ ★★★ `shrinkPhylogramNB : Phylogram (MergeIdx X a b)` | 50–70 | **✅ 已落**（实测 75 行） |
| **G6** | `dist` 三支：**G6a** 对角／**G6b¹** 唯一边权值／**G6b²** 两条走法搬移＋权和（`exists_walk_nb_sum`／`exists_walk_of_nb_sum`／`shrinkPhylogramNB_walkDist_eq`）／**G6b** 旧–旧两方向夹／**G6c** 新–旧／`w_pos`／三支合流 | 120–180 | **✅ 已落**（W49 实测 344 行，含文档） |
| **G7** | 装配 `HasPosReal (mergeStep δ a b)`（`degree w` 分情形） | 40 | **进行中** — ★D 见 §10 |
| | **合计** | **600–820** | G0–G6 已落（实测 125 ＋ 344 行） |

## 10 ★D 更正③（W49）：`degree w = 3` 支**不能**直接复用 `NJShrink.shrinkPhylogram`

派单 G7 说「`degree w = 3` 支：用 G0 的 `exists_third_of_degree` 复用二叉机器」。
**方向对，但接口不通**：`NJShrink.shrinkPhylogram` 的前提里带着
`hbin : T.toCladogram.IsBinary`（**整棵树**二叉），而「`degree w = 3`」只是**局部**条件 ——
一棵「只在远处分支点呈 polytomy」的树满足局部条件却**不**满足 `hbin`（与 §0 ★D① 是同一个坑）。
`exists_third` 只是 `hbin` 的**一个**消费者；把它换成 `exists_third_of_degree`
并不改变 `shrinkPhylogram` 的签名。

**但实核后是好消息**：`grep -n 'hbin [a-zA-Z_(]' Phylo/Stat/NJShrink.lean` 显示
`hbin` 在整个 A6–A8 链条里**只有一处语义使用** —— `degree_eq_three`（`:184`）内部的
`hbin w (not_isLeaf_of_two_adj …)`；其余三十余处**全是原样透传**
（`midpoint_not_mem_support T hbin …`、`degree_shrinkGraph T hbin …` 等），
另有 `leaf_ne_midpoint` 里的一次（也只需 `degree w = 3`）。

⇒ 正确施工法（**W49 已落**，见 `NJShrink.lean` 文末 §A9）：把 A5–A8 链条的前提从
`(hbin : T.toCladogram.IsBinary)` **机械改写**为 `(hdeg : T.graph.degree w = 3)`，名字统一加
`_of_degree`；`degree_eq_three`／`exists_third`／`shrinkPhylogram_isBinary` 三处保留 `hbin`；
`njAdditiveGap_holds`／`njReductionStep` 的调用点改走**薄包装**（§A9），故四个调用文件**零改动**。
这样 G7 两支都落在同一套机器上，且库内多出一批更一般的引理（不是为派单打的补丁）。

**★ 施工记录（复用价值高）**：
1. 名字改写之外还有一处**必须同时改**的接口细节：`(hbin : IsBinary)` 原来排在 `{w : T.V}` **之前**，
   而 `hdeg : T.graph.degree w = 3` 用到了 `w` ⇒ 若只换类型，`autoImplicit` 会造出一个 `w✝`，
   于是引理的陈述里出现**两个** `w`（症状：`hdeg` 的类型显示成 `T.graph.degree w✝ = 3`）。
   解法：把 `{w : T.V}`／`{w z : T.V}` 挪到 `hdeg` **之前**；显式参数的位置顺序不变，调用点无需改序。
2. `shrinkPhylogram_isBinary` 是唯一**真正**需要 `hbin` 的（结论就是二叉性），它的陈述里照旧写
   `shrinkPhylogram_of_degree T (degree_eq_three T hbin …) …`；证里要改写 `graph` 字段时不能
   `rw [hG]`（motive 含 `decAdj`，不是 type-correct）⇒ 用 `show` 转到 `shrinkGraph` 上再 `rw`。
3. 本文件的定理一用 `SimpleGraph.degree`／`neighborFinset`，就要求 `Fintype ↥(neighborSet)`，
   而它要 `DecidableRel` —— 对**抽象的** `shrinkGraphNB` 拿不到。解法与 `Phylo/BunemanGraft` 的
   `graftGraph` 一节相同：`attribute [local instance] Classical.propDecidable`（只用于证明，不追求可计算）。
4. `exists_third_of_degree` 的 `T` 是**显式**参数（`variable (T : Phylogram)`），调用须写
   `exists_third_of_degree T hab hdeg haw hbw`；`SimpleGraph.card_neighborFinset_eq_degree` 亦然
   （要写 `T.graph w`）。
5. `obtain ⟨hab, w, haw, hbw⟩ := hc` 会把 `hc` **清出上下文**（`Prop` 里的结构消去后不可回引）
   ⇒ 后面还要用就先 `have hckeep := hc`。

## 8 实施前的三条核查（★ 已现场核过两条）

1. ✓ `Cladogram.IsBinary` 的定义已核（`Core.lean:93`）：`∀ v, ¬IsLeaf v → degree v = 3`；
   `no_degree_two`（`Core.lean:46`）排除度 2 ⇒ 非叶点度 ≥ 3 ⇒ 「非二叉 ⇒ 某非叶点度 ≥ 4」免费。
2. ✓ `mergeStep_val_merged` 已核（`CASTERNJStep.lean:185`）：新–旧的取值就是 `½δ(x,a) + ½δ(x,b)`。
3. ⚠️ **待核**：`NJShrink.exists_third` 的证明里 `hbin` 的**全部**用处。
   若它只用 `degree w = 3`，则 G0 是纯接口改造（20 行）；
   若它还用了「其余点度 3」之类的全局条件（`shrinkGraph_isAcyclic` 一线可能要），
   G0 的估要上调，且 `degree w = 3` 情形仍须走**二叉支的原证明**（把 `hbin` 换成
   「`w` 的邻居恰三点」的局部假设）——**这一步实现前必须先核**。

## 9 硬要求（派单 §B，逐条照办）

1. **不证 `Iso` 版**：结论只要 `HasPosReal (mergeStep δ a b)`，收缩树二叉/非二叉都行；
2. **不复用 `exists_third`**：本构造根本不需要第三邻居（§1）；
3. **先交方案**：本文件即方案（一个 commit），再实现；
4. **根模块登记**：★D —— 派单说「未 settled 的文件不写进 `Phylo.lean`」，但
   `scripts/check_file_imports.sh` 要求**每个** `Phylo/*.lean` 都被根模块 import（W47 的
   `NJRun.lean` B-0 已实证过：不 import 就 RED）。本文件在**方案阶段只含注释、零声明**，
   入根模块零风险，故**照 W47 做法入根模块**；实现后同一位置继续加声明。
-/

namespace Phylo.Stat.NJShrinkNonBinary

open Phylo NJ NJ.Dissimilarity

-- 与 `Phylo.BunemanGraft` 的 `graftGraph` 一节同一处理：
-- `degree`／`neighborFinset` 要 `Fintype ↥(neighborSet)`，而它要 `DecidableRel`；
-- 这里不追求可计算性（只用于证明），故把 `Classical.propDecidable` 挂在局部实例上。
attribute [local instance] Classical.propDecidable

variable {X : Type} [Fintype X] [DecidableEq X]
variable {T : Phylogram.{0, 0} X}

/-! ## G1｜顶点类型、图、叶嵌入 -/

/-- ★★ **非二叉归约的顶点类型**：只删叶 `b` 那**一个**顶点，中点 `w` **保留**。

（与二叉支的 `NJShrink.ShrinkV T b w = {v // v ≠ leaf b ∧ v ≠ w}` 的关键差别：
那边必须删 `w`（度降到 2 会违反 `no_degree_two`），这边 `w` 的度只从 `≥4` 降到 `≥3`。） -/
abbrev ShrinkVNB (T : Phylogram.{0, 0} X) (b : X) : Type := { v : T.V // v ≠ T.leaf b }

/-- ★★ **非二叉归约的图**：`T.graph` 在「删掉 `leaf b`」上的**诱导**子图 ——
无新顶点、无新边（★D②：合并标签 `u` 就认在已有的 `T.leaf a` 上，见文件头 §1）。 -/
def shrinkGraphNB (T : Phylogram.{0, 0} X) (b : X) : SimpleGraph (ShrinkVNB T b) where
  Adj u v := T.graph.Adj u.1 v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => T.graph.loopless.irrefl u.1 h⟩

/-- ★ **`shrinkGraphNB` 的邻接就是 `T.graph` 的邻接**（定义层面，`Iff.rfl`）。 -/
@[simp] theorem shrinkGraphNB_adj {T : Phylogram.{0, 0} X} {b : X}
    {u v : ShrinkVNB T b} :
    (shrinkGraphNB T b).Adj u v ↔ T.graph.Adj u.1 v.1 := Iff.rfl

/-- ★★ **非二叉归约的叶嵌入** `MergeIdx X a b ↪ ShrinkVNB T b`：
旧标签 `x ↦ ⟨T.leaf x, ·⟩`、合并标签 `u ↦ ⟨T.leaf a, ·⟩`。 -/
def leafNB (T : Phylogram.{0, 0} X) {a b : X} (hab : a ≠ b) :
    NJ.Dissimilarity.MergeIdx X a b ↪ ShrinkVNB T b where
  toFun
    | Sum.inl x => ⟨T.leaf x.1, fun h => mergeOld_ne_right x (T.leaf.injective h)⟩
    | Sum.inr _ => ⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩
  inj' := by
    rintro (x | x) (y | y) h
    · have hxe : T.leaf x.1 = T.leaf y.1 := congrArg Subtype.val h
      have hxy : x = y := Subtype.ext (T.leaf.injective hxe)
      rw [hxy]
    · have hxe : T.leaf x.1 = T.leaf a := congrArg Subtype.val h
      exact absurd (T.leaf.injective hxe) (mergeOld_ne_left x)
    · have hxe : T.leaf a = T.leaf y.1 := congrArg Subtype.val h
      exact absurd (T.leaf.injective hxe).symm (mergeOld_ne_left y)
    · exact congrArg Sum.inr (Subsingleton.elim x y)

/-- ★ **`leafNB` 在旧标签上的取值**（`rfl`）。 -/
@[simp] theorem leafNB_val_inl (T : Phylogram.{0, 0} X) {a b : X} (hab : a ≠ b)
    (x : NJ.Dissimilarity.MergeOld X a b) :
    (leafNB T hab (Sum.inl x)).1 = T.leaf x.1 := rfl

/-- ★ **`leafNB` 在合并标签上的取值**（`rfl`）：`u` 就站在 `T.leaf a` 上。 -/
@[simp] theorem leafNB_val_inr (T : Phylogram.{0, 0} X) {a b : X} (hab : a ≠ b) (u : Unit) :
    (leafNB T hab (Sum.inr u)).1 = T.leaf a := rfl

/-! ## G3｜度数：`w` 减 1，其余**不变** -/

/-- ★★ **`v ≠ w` 时度不变**：`leaf b` 的唯一邻居是 `w`，故 `v` 的邻居一个都没被删。 -/
theorem degree_nb_of_ne {b : X} {v w : T.V} (hbw : T.graph.Adj (T.leaf b) w)
    (hv : v ≠ w) (hvb : v ≠ T.leaf b) :
    (shrinkGraphNB T b).degree ⟨v, hvb⟩ = T.graph.degree v := by
  have hnotadj : ¬ T.graph.Adj v (T.leaf b) := by
    intro h
    have hd1 : T.graph.degree (T.leaf b) = 1 :=
      (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
    obtain ⟨c, -, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd1
    have h1 : v = c := huniq v h.symm
    have h2 : w = c := huniq w hbw
    exact hv (h1.trans h2.symm)
  have hS : ∀ u : T.V, T.graph.Adj v u → u ≠ T.leaf b := by
    intro u hu h
    exact hnotadj (h ▸ hu)
  have hcard : (T.graph.neighborFinset v).card
      = ((shrinkGraphNB T b).neighborFinset ⟨v, hvb⟩).card := by
    refine Finset.card_bij (fun u hu =>
      (⟨u, hS u ((SimpleGraph.mem_neighborFinset T.graph v u).mp hu)⟩ : ShrinkVNB T b)) ?_ ?_ ?_
    · intro u hu
      rw [SimpleGraph.mem_neighborFinset]
      exact (SimpleGraph.mem_neighborFinset T.graph v u).mp hu
    · intro u1 _ u2 _ h
      exact congrArg Subtype.val h
    · intro y hy
      have hadj : (shrinkGraphNB T b).Adj ⟨v, hvb⟩ y :=
        (SimpleGraph.mem_neighborFinset (shrinkGraphNB T b) ⟨v, hvb⟩ y).mp hy
      exact ⟨y.1, (SimpleGraph.mem_neighborFinset T.graph v y.1).mpr hadj, Subtype.ext rfl⟩
  change ((shrinkGraphNB T b).neighborFinset ⟨v, hvb⟩).card = (T.graph.neighborFinset v).card
  exact hcard.symm

/-- ★★★ **中点 `w` 的度减 1**：`leaf b` 是 `w` 的邻居，删掉恰少一个。 -/
theorem degree_nb_midpoint {b : X} {w : T.V} (hbw : T.graph.Adj (T.leaf b) w)
    (hwb : w ≠ T.leaf b) :
    (shrinkGraphNB T b).degree ⟨w, hwb⟩ = T.graph.degree w - 1 := by
  have hmem : T.leaf b ∈ T.graph.neighborFinset w :=
    (SimpleGraph.mem_neighborFinset T.graph w (T.leaf b)).mpr hbw.symm
  have hcard : ((shrinkGraphNB T b).neighborFinset ⟨w, hwb⟩).card
      = (T.graph.neighborFinset w).card - 1 := by
    rw [← Finset.card_erase_of_mem hmem]
    refine Finset.card_bij (fun u _ => u.1) ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_erase]
      refine ⟨u.2, ?_⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact (SimpleGraph.mem_neighborFinset (shrinkGraphNB T b) ⟨w, hwb⟩ u).mp hu
    · intro u1 _ u2 _ h
      exact Subtype.ext h
    · intro y hy
      rw [Finset.mem_erase] at hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact hy.2
  change ((shrinkGraphNB T b).neighborFinset ⟨w, hwb⟩).card = T.graph.degree w - 1
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree]

/-! ## G2｜树性两半：**无环**（子图）＋ **连通**（删叶不断） -/

/-- ★★ **无环**：`T.graph` 的环沿 `Subtype.val` 搬回去仍是环（`Subtype.val` 单射），矛盾。

（`IsCycle.map`：单射图同态把环搬成环；同态就是 `Subtype.val`，`map_rel' := id`。） -/
theorem isAcyclic_nb {b : X} (hac : T.graph.IsAcyclic) :
    (shrinkGraphNB T b).IsAcyclic := by
  intro v c hc
  let f : (shrinkGraphNB T b) →g T.graph :=
    { toFun := Subtype.val, map_rel' := fun h => h }
  exact hac (c.map f) (hc.map (f := f) Subtype.val_injective)

/-- ★★ **走法提升**：`T`-走法若**支撑集不含** `leaf b`，则整段落在新图里
（每一步都是 `T`-边，且两端都不被删）。 -/
theorem exists_walk_nb {b : X} {u v : T.V} (p : T.graph.Walk u v)
    (hu : u ≠ T.leaf b) (hv : v ≠ T.leaf b)
    (hp : ∀ z ∈ p.support, z ≠ T.leaf b) :
    Nonempty ((shrinkGraphNB T b).Walk ⟨u, hu⟩ ⟨v, hv⟩) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a c d hadj q ih =>
      have hc : c ≠ T.leaf b := by
        refine hp c ?_
        rw [SimpleGraph.Walk.support_cons hadj q]
        exact List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support q)
      have hp' : ∀ z ∈ q.support, z ≠ T.leaf b := by
        intro z hz
        refine hp z ?_
        rw [SimpleGraph.Walk.support_cons hadj q]
        exact List.mem_cons_of_mem a hz
      obtain ⟨r⟩ := ih hc hv hp'
      exact ⟨SimpleGraph.Walk.cons
        (show (shrinkGraphNB T b).Adj ⟨a, hu⟩ ⟨c, hc⟩ from hadj) r⟩

/-- ★★★ **连通**：删**叶**不破坏连通。

取 `w` 作枢纽：任一点 `u` 到 `w` 的 `T`-路**不含** `leaf b`
（`leaf b` 度为 1、而两端都不是它 ⇒ `not_mem_support_of_degree_one`），故整段可提升到新图。 -/
theorem connected_nb {b : X} {w : T.V} (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b)
    (hconn : T.graph.Connected) : (shrinkGraphNB T b).Connected := by
  have hdb : T.graph.degree (T.leaf b) = 1 :=
    (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
  have hhub : ∀ u : ShrinkVNB T b,
      Nonempty ((shrinkGraphNB T b).Walk u ⟨w, hwb⟩) := by
    intro u
    obtain ⟨p, hp, -⟩ := T.toCladogram.existsUnique_path u.1 w
    have hlb : T.leaf b ∉ p.support :=
      NJShrink.not_mem_support_of_degree_one T hdb p hp u.2 hwb
    exact exists_walk_nb p u.2 hwb (fun z hz h => hlb (h ▸ hz))
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨w, hwb⟩⟩⟩
  intro u v
  obtain ⟨q1⟩ := hhub u
  obtain ⟨q2⟩ := hhub v
  exact ⟨q1.append q2.reverse⟩

/-! ## G4｜`Cladogram` 的两个度字段 ＋ 打包 -/

noncomputable def shrinkGraphNB_decidableRel (T : Phylogram.{0, 0} X) (b : X) :
    DecidableRel (shrinkGraphNB T b).Adj := fun _ _ => Classical.propDecidable _

/-- ★★ **无度 2**：`w` 支靠情形假设 `3 < degree w`，其余支搬 `T` 的 `no_degree_two`。 -/
theorem no_degree_two_nb {b : X} {w : T.V} (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b)
    (hdeg : 3 < T.graph.degree w) (v : ShrinkVNB T b) :
    (shrinkGraphNB T b).degree v ≠ 2 := by
  by_cases hvw : v.1 = w
  · have hv : v = ⟨w, hwb⟩ := Subtype.ext hvw
    rw [hv, degree_nb_midpoint hbw hwb]
    omega
  · rw [degree_nb_of_ne hbw hvw v.2]
    exact T.toCladogram.no_degree_two v.1

/-- ★★★ **叶 ⟺ 度 1**（`Cladogram.leaf_iff_degree_one` 字段）。

* `⟹`：`leafNB` 的像要么是 `⟨T.leaf x,·⟩`（`x ≠ b`，且 `T.leaf x ≠ w`，故度 = `T` 里的度 = 1），
  要么是 `⟨T.leaf a,·⟩`；
* `⟸`：`deg' v = 1` ⇒ `v.1 ≠ w`（那边 `deg' w = degree w − 1 ≥ 3`）⇒ `deg_T v.1 = 1`
  ⇒ `v.1 = T.leaf x`；`x ≠ b`（`v.2`）；`x = a` 时是 `inr ()`，否则 `x ∈ MergeOld` 给 `inl`。 -/
theorem leaf_iff_degree_one_nb {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (v : ShrinkVNB T b) :
    (∃ u : NJ.Dissimilarity.MergeIdx X a b, leafNB T hab u = v)
      ↔ (shrinkGraphNB T b).degree v = 1 := by
  have hw_notleaf : ¬ T.toCladogram.IsLeaf w := by
    intro hl
    have h1 : T.graph.degree w = 1 := (T.isLeaf_iff_degree_eq_one w).mp hl
    omega
  have hleaf_ne_w : ∀ x : X, T.leaf x ≠ w := fun x h => hw_notleaf ⟨x, h⟩
  constructor
  · rintro ⟨u, rfl⟩
    cases u with
    | inl x =>
        have hx : T.leaf x.1 ≠ T.leaf b := fun h => mergeOld_ne_right x (T.leaf.injective h)
        have h := degree_nb_of_ne (b := b) (v := T.leaf x.1) (w := w) hbw
          (hleaf_ne_w x.1) hx
        rw [show leafNB T hab (Sum.inl x) = ⟨T.leaf x.1, hx⟩ from rfl, h]
        exact (T.isLeaf_iff_degree_eq_one (T.leaf x.1)).mp ⟨x.1, rfl⟩
    | inr u =>
        cases u
        have ha : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
        have h := degree_nb_of_ne (b := b) (v := T.leaf a) (w := w) hbw (hleaf_ne_w a) ha
        rw [show leafNB T hab (Sum.inr ()) = ⟨T.leaf a, ha⟩ from rfl, h]
        exact (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
  · intro h
    have hvne : v.1 ≠ w := by
      intro hvw
      have hv : v = ⟨w, hwb⟩ := Subtype.ext hvw
      rw [hv, degree_nb_midpoint hbw hwb] at h
      omega
    have hT1 : T.graph.degree v.1 = 1 := by
      rw [degree_nb_of_ne hbw hvne v.2] at h
      exact h
    obtain ⟨x, hx⟩ := (T.isLeaf_iff_degree_eq_one v.1).mpr hT1
    have hxb : x ≠ b := by
      intro h'
      exact v.2 (by rw [← hx, h'])
    by_cases hxa : x = a
    · refine ⟨Sum.inr (), ?_⟩
      apply Subtype.ext
      show T.leaf a = v.1
      rw [hxa] at hx
      exact hx
    · refine ⟨Sum.inl ⟨x, by simp [Finset.mem_sdiff, hxa, hxb]⟩, ?_⟩
      apply Subtype.ext
      show T.leaf x = v.1
      exact hx

/-- ★★★ **非二叉归约的 `Cladogram`**（顶点 `ShrinkVNB`、图 `shrinkGraphNB`、叶 `leafNB`）。 -/
noncomputable def shrinkCladogramNB {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w) :
    Cladogram (NJ.Dissimilarity.MergeIdx X a b) where
  V := ShrinkVNB T b
  fintypeV := inferInstance
  decEqV := inferInstance
  graph := shrinkGraphNB T b
  decAdj := shrinkGraphNB_decidableRel T b
  isTree := ⟨connected_nb hbw hwb T.toCladogram.isTree.1, isAcyclic_nb T.toCladogram.isTree.2⟩
  leaf := leafNB T hab
  leaf_iff_degree_one := fun v => leaf_iff_degree_one_nb hab hbw hwb hdeg v
  no_degree_two := fun v => no_degree_two_nb hbw hwb hdeg v

/-! ## G5｜边权：旧边不变，唯一边 `{leaf a, w}` 改 `½(w_a + w_b)` -/

/-- ★★ **合并后的垂枝** `½(w_a + w_b)`。

★ 与二叉支的 `NJShrink.shrinkNewW` 的差别：那边还要**加上** `d(w,z)`（因为中点 `w` 被抑制、
新叶改挂到第三邻居 `z` 上）；这里 `w` **保留**，故**不加**任何东西。 -/
noncomputable def shrinkNewWNB (a b : X) (w : T.V) : ℝ :=
  (1 / 2) * (T.dist (T.leaf a) w + T.dist (T.leaf b) w)

/-- ★★ **新垂枝严格正**：`d(a,w)`、`d(b,w)` 两条边权都正。 -/
theorem shrinkNewWNB_pos {a b : X} {w : T.V} (haw : T.graph.Adj (T.leaf a) w)
    (hbw : T.graph.Adj (T.leaf b) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) :
    0 < shrinkNewWNB (T := T) a b w := by
  have h1 : 0 < T.dist (T.leaf a) w := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T haw]; exact hpos _
  have h2 : 0 < T.dist (T.leaf b) w := by
    rw [Phylo.TreeDist.dist_eq_w_of_adj T hbw]; exact hpos _
  unfold shrinkNewWNB
  linarith

/-- ★★ **非二叉归约的边权**（作用在 `Sym2 (ShrinkVNB)` 上）：
唯一边 `{leaf a, w}` 取 ★★ `shrinkNewWNB`，其余旧边取原树的 `T.wExt`。 -/
noncomputable def shrinkWNB {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b)
    (e : Sym2 (ShrinkVNB T b)) : ℝ :=
  if e = s((⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩ : ShrinkVNB T b), ⟨w, hwb⟩) then
    shrinkNewWNB (T := T) a b w
  else T.wExt (e.map (Function.Embedding.subtype (fun v : T.V => v ≠ T.leaf b)))

/-- ★★★ **旧边的权就是原树的边权**（`{u,v} ≠ {leaf a, w}` 时）。 -/
theorem shrinkWNB_old {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b)
    {u v : T.V} (huv : T.graph.Adj u v)
    (hu : u ≠ T.leaf b) (hv : v ≠ T.leaf b)
    (hne : s((⟨u, hu⟩ : ShrinkVNB T b), ⟨v, hv⟩)
      ≠ s((⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩ : ShrinkVNB T b), ⟨w, hwb⟩)) :
    shrinkWNB (T := T) hab hwb s((⟨u, hu⟩ : ShrinkVNB T b), ⟨v, hv⟩) = T.wExt s(u, v) := by
  unfold shrinkWNB
  rw [if_neg hne, Sym2.map_mk]
  rfl

/-- ★★ **非二叉归约的权非负**。 -/
theorem shrinkWNB_nonneg {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b)
    (haw : T.graph.Adj (T.leaf a) w) (hbw : T.graph.Adj (T.leaf b) w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) (e : Sym2 (ShrinkVNB T b)) :
    0 ≤ shrinkWNB (T := T) hab hwb e := by
  unfold shrinkWNB
  split
  · exact le_of_lt (shrinkNewWNB_pos haw hbw hpos)
  · exact Phylo.TreeDist.wExt_nonneg T _

/-! ## G5′｜★★★ 非二叉归约的 `Phylogram` -/

/-- ★★★ **非二叉归约的 `Phylogram`**（拓扑 `shrinkCladogramNB`，边权 `shrinkWNB`）。

`dist` 对齐（`mergeStep`）留到 G6；本定义**只**要求 `w` 与 `w_nonneg`。 -/
noncomputable def shrinkPhylogramNB {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) :
    Phylogram (NJ.Dissimilarity.MergeIdx X a b) where
  toCladogram := shrinkCladogramNB (T := T) hab hbw hwb hdeg
  w := fun e => shrinkWNB (T := T) hab hwb e.1
  w_nonneg := fun e => shrinkWNB_nonneg (T := T) hab hwb haw hbw hpos e.1

-- 与 `Phylo.BunemanGraft`／`Phylo.NJShrink` 对 `graftCladogram`／`shrinkPhylogram` 的处理一致：
-- `V`／`graph` 投影要能在 `reducible` 透明层归约（G6／G7 的显示式装配要用）。
attribute [reducible] shrinkCladogramNB shrinkPhylogramNB

/-! ## G6｜`dist` 对齐（三支）—— 本步先落**新–新（对角）**支 -/

/-- ★ **新–新（对角）**：合并标签只有一处，`d'(u,u) = 0` ＝ `mergeStep` 的对角。 -/
theorem shrinkPhylogramNB_dist_self {b : X} {w : T.V} (δ : NJ.Dissimilarity X) (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (u : NJ.Dissimilarity.MergeIdx X a b) :
    (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
        ((shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).leaf u)
        ((shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).leaf u)
      = (Phylo.Stat.CASTERNJStep.mergeStep δ a b).val u u := by
  rw [Phylogram.dist_self]
  exact ((Phylo.Stat.CASTERNJStep.mergeStep δ a b).diag u).symm

/-- ★ **唯一边 `{leaf a, w}` 的权就是 `½(w_a + w_b)`**（`shrinkWNB` 的 `if_pos` 支；
G6c「新–旧」支要用它）。 -/
theorem shrinkWNB_new {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b) :
    shrinkWNB (T := T) hab hwb
        s((⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩ : ShrinkVNB T b), ⟨w, hwb⟩)
      = shrinkNewWNB (T := T) a b w := by
  unfold shrinkWNB
  rw [if_pos rfl]

/-! ## G6b²｜走法搬移（带边权和）

`dist` 对齐的地基：把 `T`-走法搬进新图、把新图走法搬回 `T`，**同时**跟踪
`edges.map wExt` 的权和。两支的支点都是 ★★ `shrinkWNB_old`：
**只要走法避开了 `⟨leaf a⟩`，它就绕开了唯一那条被改权的边**。 -/

/-- ★★ **被改权的那条边不是「两端都避 `leaf a`」的边**。

`Sym2.eq_iff` 只给两种配对：`⟨u⟩ = ⟨leaf a⟩` 或 `⟨v⟩ = ⟨leaf a⟩`，两者都被 `hua`/`hva` 排掉。
（★D：这里**不**需要二叉性 —— 改权边的一个端点就**是** `T.leaf a`。） -/
theorem shrinkWNB_mk_ne_new {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b)
    {u v : T.V} (hu : u ≠ T.leaf b) (hv : v ≠ T.leaf b)
    (hua : u ≠ T.leaf a) (hva : v ≠ T.leaf a) :
    s((⟨u, hu⟩ : ShrinkVNB T b), ⟨v, hv⟩)
      ≠ s((⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩ : ShrinkVNB T b), ⟨w, hwb⟩) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hua (congrArg Subtype.val h1)
  · exact hva (congrArg Subtype.val h2)

/-- ★★ **旧边的权就是 `T.wExt`**（`hua`/`hva` 版；两支搬移都用它）。 -/
theorem shrinkWNB_old' {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b)
    {u v : T.V} (huv : T.graph.Adj u v) (hu : u ≠ T.leaf b) (hv : v ≠ T.leaf b)
    (hua : u ≠ T.leaf a) (hva : v ≠ T.leaf a) :
    shrinkWNB (T := T) hab hwb s((⟨u, hu⟩ : ShrinkVNB T b), ⟨v, hv⟩) = T.wExt s(u, v) :=
  shrinkWNB_old (T := T) hab hwb huv hu hv
    (shrinkWNB_mk_ne_new (T := T) hab hwb hu hv hua hva)

/-- ★★ **走法的 `walkDist` = `shrinkWNB` 沿边表求和**（`wExt` 落到 `shrinkWNB`）。 -/
theorem shrinkPhylogramNB_walkDist_eq {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {U V : ShrinkVNB T b} (q : (shrinkGraphNB T b).Walk U V) :
    (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).walkDist q
      = (q.edges.map (shrinkWNB (T := T) hab hwb)).sum := by
  rw [Phylogram.walkDist]
  congr 1
  refine List.map_congr_left ?_
  intro e he
  have hmem : e ∈ (shrinkGraphNB T b).edgeSet := q.edges_subset_edgeSet he
  rw [Phylogram.wExt, dif_pos hmem]

/-- ★★★ **走法搬移 `T → G`（带边权和）**：若 `T` 里走法 `p` 的支撑集**避开**
`T.leaf a`（改了权）与 `T.leaf b`（已删），则它整条落进新图，且**边权和不变**。

（★D：这里**不**需要「避开中点 `w`」——本构造把 `w` 留在了树里，
所以「旧–旧路径过 `w`」完全无害；二叉支之所以要避 `w`，是因为那边 `w` 被抑制了。） -/
theorem exists_walk_nb_sum {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b) :
    ∀ {u v : T.V} (p : T.graph.Walk u v),
      ∀ (hu : u ≠ T.leaf b) (hv : v ≠ T.leaf b),
        (∀ z ∈ p.support, z ≠ T.leaf a ∧ z ≠ T.leaf b) →
          ∃ q : (shrinkGraphNB T b).Walk ⟨u, hu⟩ ⟨v, hv⟩,
            (q.edges.map (shrinkWNB (T := T) hab hwb)).sum = (p.edges.map T.wExt).sum := by
  intro u v p
  induction p with
  | nil => intro _ _ _; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u0 m x0 hadj rest ih =>
      intro hu hv hsp
      have hmem_m : m ∈ (SimpleGraph.Walk.cons hadj rest).support :=
        List.mem_cons_of_mem u0 (SimpleGraph.Walk.start_mem_support rest)
      have hmem_u0 : u0 ∈ (SimpleGraph.Walk.cons hadj rest).support :=
        SimpleGraph.Walk.start_mem_support (SimpleGraph.Walk.cons hadj rest)
      have hu_a : u0 ≠ T.leaf a := (hsp u0 hmem_u0).1
      have hm_a : m ≠ T.leaf a := (hsp m hmem_m).1
      have hm : m ≠ T.leaf b := (hsp m hmem_m).2
      have hsp' : ∀ z ∈ rest.support, z ≠ T.leaf a ∧ z ≠ T.leaf b := by
        intro z hz
        exact hsp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem u0 hz)
      obtain ⟨r, hr⟩ := ih hm hv hsp'
      refine ⟨SimpleGraph.Walk.cons
        (show (shrinkGraphNB T b).Adj ⟨u0, hu⟩ ⟨m, hm⟩ from hadj) r, ?_⟩
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons,
        shrinkWNB_old' (T := T) hab hwb hadj hu hm hu_a hm_a, hr]

/-- ★★★ **走法搬移 `G → T`（带边权和）**：若新图里走法 `q` 的支撑集**不含** `⟨leaf a⟩`，
则它完全由旧边组成，可搬回 `T` 且**边权和不变**。

（`⟨leaf a⟩` 在新图里度为 1，故以别的顶点为端点的**路径**不会经过它 ——
★★ `not_mem_support_of_degree_one`。） -/
theorem exists_walk_of_nb_sum {b : X} {w : T.V} (hab : a ≠ b) (hwb : w ≠ T.leaf b) :
    ∀ {U V : ShrinkVNB T b} (q : (shrinkGraphNB T b).Walk U V),
      (∀ z ∈ q.support, z.1 ≠ T.leaf a) →
        ∃ p : T.graph.Walk U.1 V.1,
          (q.edges.map (shrinkWNB (T := T) hab hwb)).sum = (p.edges.map T.wExt).sum := by
  intro U V q
  induction q with
  | nil => intro _; exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons U0 M V0 hadj rest ih =>
      intro hsp
      have hmem_M : M ∈ (SimpleGraph.Walk.cons hadj rest).support :=
        List.mem_cons_of_mem U0 (SimpleGraph.Walk.start_mem_support rest)
      have hmem_U0 : U0 ∈ (SimpleGraph.Walk.cons hadj rest).support :=
        SimpleGraph.Walk.start_mem_support (SimpleGraph.Walk.cons hadj rest)
      have hU : U0.1 ≠ T.leaf a := hsp U0 hmem_U0
      have hM : M.1 ≠ T.leaf a := hsp M hmem_M
      have hsp' : ∀ z ∈ rest.support, z.1 ≠ T.leaf a := by
        intro z hz
        exact hsp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem U0 hz)
      obtain ⟨p, hp⟩ := ih hsp'
      refine ⟨SimpleGraph.Walk.cons (show T.graph.Adj U0.1 M.1 from hadj) p, ?_⟩
      rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
        List.map_cons, List.sum_cons,
        shrinkWNB_old' (T := T) hab hwb (show T.graph.Adj U0.1 M.1 from hadj)
          U0.2 M.2 hU hM, hp]

/-! ## G6b｜旧–旧距离：`dist` 不变 -/

/-- ★★★ **旧–旧距离（一般形式）**：`u, v` 都**不是**合并叶的像（`u.1, v.1 ≠ T.leaf a`）时
`T'.dist u v = T.dist u.1 v.1`。

两个方向：
* `≤`：`T` 中 `u.1 → v.1` 的**唯一**路径避开 `leaf a`、`leaf b`（两者度均为 1 且都不是端点
  ⇒ ★★ `not_mem_support_of_degree_one`），整条搬进 `G` 且权和不变
  （★★★ `exists_walk_nb_sum`）⇒ `dist' ≤ walkDist = dist_T`；
* `≥`：`G` 中唯一路径**不含** `⟨leaf a⟩`（它在 `G` 里度 1 且不是端点），搬回 `T`
  （★★★ `exists_walk_of_nb_sum`）⇒ `dist_T ≤ walkDist ≤ dist'`。

⇒ 被改权的那条边 `{leaf a, w}` **不在**任何「旧叶 ↔ 旧叶」路径上，故旧–旧距离一字不改。 -/
theorem shrinkPhylogramNB_dist_old {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {u v : ShrinkVNB T b} (hua : u.1 ≠ T.leaf a) (hva : v.1 ≠ T.leaf a) :
    (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist u v = T.dist u.1 v.1 := by
  have haa : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
  by_cases huv : u.1 = v.1
  · have hsub : u = v := Subtype.ext huv
    rw [hsub]
    simp only [Phylogram.dist_self]
  · have h1 : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist u v
        ≤ T.dist u.1 v.1 := by
      set P := (T.existsUnique_path u.1 v.1).choose with hPdef
      have hPpath : P.IsPath := (T.existsUnique_path u.1 v.1).choose_spec.1
      have hda : T.graph.degree (T.leaf a) = 1 :=
        (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
      have hdb : T.graph.degree (T.leaf b) = 1 :=
        (T.isLeaf_iff_degree_eq_one (T.leaf b)).mp ⟨b, rfl⟩
      have haP : T.leaf a ∉ P.support :=
        NJShrink.not_mem_support_of_degree_one T hda P hPpath hua hva
      have hbP : T.leaf b ∉ P.support :=
        NJShrink.not_mem_support_of_degree_one T hdb P hPpath u.2 v.2
      obtain ⟨q, hq⟩ := exists_walk_nb_sum (T := T) hab hwb P u.2 v.2
        (fun z hz => ⟨fun h => haP (h ▸ hz), fun h => hbP (h ▸ hz)⟩)
      have hqw : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).walkDist q
          = T.dist u.1 v.1 := by
        have hsum : (P.edges.map T.wExt).sum = T.dist u.1 v.1 := by
          have hwalk : (P.edges.map T.wExt).sum = T.walkDist P := rfl
          rw [hwalk, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath T P hPpath]
        rw [shrinkPhylogramNB_walkDist_eq (T := T) hab hbw hwb hdeg haw hpos q, hq]
        exact hsum
      have hdw : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist u v
          ≤ (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).walkDist q :=
        Phylo.Contract.dist_le_walkDist (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos) q
      linarith
    have h2 : T.dist u.1 v.1 ≤ (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist u v := by
      obtain ⟨q', hq'path, -⟩ :=
        (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).existsUnique_path u v
      have hdegA : (shrinkGraphNB T b).degree (⟨T.leaf a, haa⟩ : ShrinkVNB T b) = 1 := by
        rw [degree_nb_of_ne (b := b) (v := T.leaf a) hbw
          (fun h => T.graph.loopless.irrefl (T.leaf a) (h ▸ haw)) haa]
        exact (T.isLeaf_iff_degree_eq_one (T.leaf a)).mp ⟨a, rfl⟩
      have hqa : (⟨T.leaf a, haa⟩ : ShrinkVNB T b) ∉ q'.support :=
        NJShrink.not_mem_support_of_degree_one
          (T := shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos) hdegA q' hq'path
          (fun h => hua (congrArg Subtype.val h))
          (fun h => hva (congrArg Subtype.val h))
      obtain ⟨p, hp⟩ := exists_walk_of_nb_sum (T := T) hab hwb q'
        (fun t ht hcon => hqa (by
          have hteq : t = (⟨T.leaf a, haa⟩ : ShrinkVNB T b) := Subtype.ext hcon
          rwa [hteq] at ht))
      have e1 : T.dist u.1 v.1 ≤ T.walkDist p := Phylo.Contract.dist_le_walkDist T p
      have e3 : T.walkDist p = (q'.edges.map (shrinkWNB (T := T) hab hwb)).sum := hp.symm
      have e4 : (q'.edges.map (shrinkWNB (T := T) hab hwb)).sum
          = (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).walkDist q' :=
        (shrinkPhylogramNB_walkDist_eq (T := T) hab hbw hwb hdeg haw hpos q').symm
      have e5 : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).walkDist q'
          = (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist u v :=
        (Phylo.TreeDist.dist_eq_walkDist_of_isPath _ q' hq'path).symm
      linarith
    exact le_antisymm h1 h2

/-- ★★★ **旧–旧距离（叶标签形式）**：`x, y ∉ {a,b}` 时 `T'.dist (leaf' x) (leaf' y) = δ(x,y)`。 -/
theorem shrinkPhylogramNB_dist_inl_inl (δ : NJ.Dissimilarity X) {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) (x y : MergeOld X a b) :
    (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
        ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl x))
        ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl y))
      = δ.val x.1 y.1 := by
  have hxa : T.leaf x.1 ≠ T.leaf a := fun h => mergeOld_ne_left x (T.leaf.injective h)
  have hya : T.leaf y.1 ≠ T.leaf a := fun h => mergeOld_ne_left y (T.leaf.injective h)
  have hxb : T.leaf x.1 ≠ T.leaf b := fun h => mergeOld_ne_right x (T.leaf.injective h)
  have hyb : T.leaf y.1 ≠ T.leaf b := fun h => mergeOld_ne_right y (T.leaf.injective h)
  have hxu : ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl x))
      = (⟨T.leaf x.1, hxb⟩ : ShrinkVNB T b) := Subtype.ext rfl
  have hyu : ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl y))
      = (⟨T.leaf y.1, hyb⟩ : ShrinkVNB T b) := Subtype.ext rfl
  rw [hxu, hyu,
    shrinkPhylogramNB_dist_old (T := T) hab hbw hwb hdeg haw hpos hxa hya]
  exact hT x.1 y.1

/-- ★★★ **新–旧距离**：`x ∉ {a,b}` 时
`T'.dist (leaf' u) (leaf' x) = ½·δ(a,x) + ½·δ(b,x)`。

三步（★D：比二叉支短 —— 没有第三邻居要抑制）：
1. `⟨leaf a⟩` 在新图里**唯一**邻居是 `⟨w⟩`（★★ `NJShrink.leaf_a_adj_eq_midpoint`）
   ⇒ 路径第一步必到 `⟨w⟩` ⇒ `dist' = shrinkNewWNB + dist' ⟨w⟩ ⟨leaf x⟩`；
2. `dist' ⟨w⟩ ⟨leaf x⟩ = d_T(w, x)`（★★★ `shrinkPhylogramNB_dist_old`）；
3. 算术：★★★ `StrictCherry.mergeStep_val_eq` 恰好给
   `½δ(x,a) + ½δ(x,b) = shrinkNewWNB + d(w,x)`。 -/
theorem shrinkPhylogramNB_dist_new_old (δ : NJ.Dissimilarity X) {b : X} {w : T.V}
    (hab : a ≠ b) (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b)
    (hdeg : 3 < T.graph.degree w) (haw : T.graph.Adj (T.leaf a) w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hc : T.IsCherry a b) (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y)
    (x : MergeOld X a b) :
    (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
        ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inr ()))
        ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl x))
      = (1 / 2) * δ.val a x.1 + (1 - 1 / 2) * δ.val b x.1 := by
  have haa : T.leaf a ≠ T.leaf b := fun h => hab (T.leaf.injective h)
  have hlaw : T.leaf a ≠ w := fun h => T.graph.loopless.irrefl (T.leaf a) (h ▸ haw)
  have hxa : T.leaf x.1 ≠ T.leaf a := fun h => mergeOld_ne_left x (T.leaf.injective h)
  have hxb : T.leaf x.1 ≠ T.leaf b := fun h => mergeOld_ne_right x (T.leaf.injective h)
  have hu : ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inr ()))
      = (⟨T.leaf a, haa⟩ : ShrinkVNB T b) := Subtype.ext rfl
  have hxu : ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf (Sum.inl x))
      = (⟨T.leaf x.1, hxb⟩ : ShrinkVNB T b) := Subtype.ext rfl
  rw [hu, hxu]
  -- ① 第一步必到 `⟨w⟩`
  have hstep : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
      (⟨T.leaf a, haa⟩ : ShrinkVNB T b) ⟨T.leaf x.1, hxb⟩
      = shrinkNewWNB (T := T) a b w
        + (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
            (⟨w, hwb⟩ : ShrinkVNB T b) ⟨T.leaf x.1, hxb⟩ := by
    have hne : (⟨T.leaf a, haa⟩ : ShrinkVNB T b) ≠ ⟨T.leaf x.1, hxb⟩ := by
      intro h
      exact hxa (congrArg Subtype.val h).symm
    obtain ⟨P, hPpath, -⟩ :=
      (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).existsUnique_path
        (⟨T.leaf a, haa⟩ : ShrinkVNB T b) ⟨T.leaf x.1, hxb⟩
    obtain ⟨v', hv', P', hsplit⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne P
    have hv'w : v' = (⟨w, hwb⟩ : ShrinkVNB T b) := by
      have h1 : v'.1 = w := NJShrink.leaf_a_adj_eq_midpoint T haw v'.1 hv'
      exact Subtype.ext h1
    subst hv'w
    have hP'path : P'.IsPath := by
      rw [hsplit] at hPpath
      exact SimpleGraph.Walk.IsPath.of_cons hPpath
    have he : s((⟨T.leaf a, haa⟩ : ShrinkVNB T b), ⟨w, hwb⟩) ∈ (shrinkGraphNB T b).edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr
        (show (shrinkGraphNB T b).Adj ⟨T.leaf a, haa⟩ ⟨w, hwb⟩ from haw)
    have hnew : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).wExt
        s((⟨T.leaf a, haa⟩ : ShrinkVNB T b), ⟨w, hwb⟩) = shrinkNewWNB (T := T) a b w := by
      rw [Phylogram.wExt, dif_pos he]
      exact shrinkWNB_new (T := T) hab hwb
    rw [Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P hPpath, hsplit,
      Phylogram.walkDist, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, hnew,
      ← Phylogram.walkDist, ← Phylo.TreeDist.dist_eq_walkDist_of_isPath _ P' hP'path]
  rw [hstep]
  -- ② `⟨w⟩ → ⟨leaf x⟩` 是旧–旧
  have hzold : (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
      (⟨w, hwb⟩ : ShrinkVNB T b) ⟨T.leaf x.1, hxb⟩ = T.dist w (T.leaf x.1) :=
    shrinkPhylogramNB_dist_old (T := T) hab hbw hwb hdeg haw hpos hlaw.symm hxa
  rw [hzold]
  -- ③ 算术：`mergeStep_val_eq` 的原式
  obtain ⟨w', haw', -, hEq⟩ :=
    Phylo.Stat.StrictCherry.mergeStep_val_eq δ hT hc (mergeOld_ne_left x) (mergeOld_ne_right x)
  have hw'w : w' = w := NJShrink.leaf_a_adj_eq_midpoint T haw w' haw'
  subst hw'w
  have hs1 : δ.val a x.1 = δ.val x.1 a := δ.symm a x.1
  have hs2 : δ.val b x.1 = δ.val x.1 b := δ.symm b x.1
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  unfold shrinkNewWNB
  linarith

/-! ## G6c｜`HasPosReal` 的两件配套：边权严格正 ＋ 三支合流 -/

/-- ★★ **新图每条边权严格正**：唯一边取 ★★ `shrinkNewWNB`（★ `shrinkNewWNB_pos`），
其余旧边搬 `T` 的 `hpos`。 -/
theorem shrinkWNB_pos {b : X} {w : T.V} (hab : a ≠ b) (hbw : T.graph.Adj (T.leaf b) w)
    (hwb : w ≠ T.leaf b) (haw : T.graph.Adj (T.leaf a) w)
    (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    {u v : ShrinkVNB T b} (huv : (shrinkGraphNB T b).Adj u v) :
    0 < shrinkWNB (T := T) hab hwb s(u, v) := by
  unfold shrinkWNB
  by_cases hnew : s(u, v)
      = s((⟨T.leaf a, fun h => hab (T.leaf.injective h)⟩ : ShrinkVNB T b), ⟨w, hwb⟩)
  · rw [if_pos hnew]
    exact shrinkNewWNB_pos (T := T) haw hbw hpos
  · rw [if_neg hnew, Sym2.map_mk]
    change 0 < T.wExt s(u.1, v.1)
    have htedge : T.graph.Adj u.1 v.1 := huv
    rw [Phylo.TreeDist.wExt_eq_w T ((SimpleGraph.mem_edgeSet T.graph).mpr htedge)]
    exact hpos _

/-- ★★ **`Phylogram.w` 版本**（`Sym2.ind` 把边拆成端点对）。 -/
theorem shrinkPhylogramNB_w_pos {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e) :
    ∀ e : Edge (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).toCladogram,
      0 < (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).w e := by
  have key : ∀ e' : Sym2 (ShrinkVNB T b), e' ∈ (shrinkGraphNB T b).edgeSet →
      0 < shrinkWNB (T := T) hab hwb e' :=
    Sym2.ind (fun u v he =>
      shrinkWNB_pos (T := T) hab hbw hwb haw hpos ((SimpleGraph.mem_edgeSet _).mp he))
  intro e
  exact key e.1 e.2

/-- ★★★ **`dist` 对齐（三支合流）**：
`∀ u v : MergeIdx X a b`，`T'.dist (leaf' u) (leaf' v) = (mergeStep δ a b).val u v`。 -/
theorem shrinkPhylogramNB_dist (δ : NJ.Dissimilarity X) {b : X} {w : T.V} (hab : a ≠ b)
    (hbw : T.graph.Adj (T.leaf b) w) (hwb : w ≠ T.leaf b) (hdeg : 3 < T.graph.degree w)
    (haw : T.graph.Adj (T.leaf a) w) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hc : T.IsCherry a b) (hT : ∀ x y : X, T.dist (T.leaf x) (T.leaf y) = δ.val x y) :
    ∀ u v : MergeIdx X a b,
      (shrinkPhylogramNB (T := T) hab hbw hwb hdeg haw hpos).dist
          ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf u)
          ((shrinkCladogramNB (T := T) hab hbw hwb hdeg).leaf v)
        = (Phylo.Stat.CASTERNJStep.mergeStep δ a b).val u v := by
  intro u v
  cases u with
  | inl x =>
      cases v with
      | inl y =>
          rw [shrinkPhylogramNB_dist_inl_inl (T := T) δ hab hbw hwb hdeg haw hpos hT x y]
          rfl
      | inr y =>
          cases y
          rw [Phylo.TreeDist.dist_comm,
            shrinkPhylogramNB_dist_new_old (T := T) δ hab hbw hwb hdeg haw hpos hc hT x]
          simp only [Phylo.Stat.CASTERNJStep.mergeStep, mergeDissim, mergeVal]
  | inr x =>
      cases x
      cases v with
      | inl y =>
          rw [shrinkPhylogramNB_dist_new_old (T := T) δ hab hbw hwb hdeg haw hpos hc hT y]
          simp only [Phylo.Stat.CASTERNJStep.mergeStep, mergeDissim, mergeVal]
      | inr y =>
          cases y
          rw [Phylogram.dist_self]
          rfl

/-! ## G7｜★★★ 装配：`njAdditiveGapUnrestricted` 收口

两支的分界**不是**「整棵树是否二叉」，而是**樱桃中点的度**（§0 ★D①）：

* `degree w = 3` —— 收缩手术与二叉情形**逐字相同**，走 ★★★ `NJShrink.shrinkPhylogram_of_degree`
  （W49 把 A5–A8 链条的前提从 `IsBinary` 放宽成 `degree w = 3`，
  见 `Phylo/Stat/NJShrink.lean` 文末 §A9）；
* `3 < degree w` —— 走本文件的 ★★★ `shrinkPhylogramNB`（只删叶 `b`、把 `T.leaf a` 的权改成
  `½(w_a+w_b)`、其余不动）。

两支共用同一个入口：★★★ `NJShrink.isCherry_of_njStep` 给出 `T.IsCherry a b`（**与二叉性无关**，
这是 W46 起就有的接口）。`w` 的度**至少** 3：两个叶邻居给出 `2 ≤ degree w`
（★★ `SimpleGraph.card_neighborFinset_eq_degree`），而 `Cladogram.no_degree_two` 排除 `= 2`。 -/

open Phylo.Stat.CASTERNJ in
/-- ★★★ **B 的收口定理｜★★ `njAdditiveGapUnrestricted` 成立**（`CASTERNJ.lean:153`，不再是缺口）。

`HasPosReal δ`（边权**全正**的实现树，**允许 polytomy**）＋ `njStep δ a b`
⇒ `HasPosReal (mergeStep δ a b)`。★ 注意前提只有 `HasPosReal`，**没有** `IsBinary`
——这正是它与已收口的 ★★★ `njAdditiveGap_holds`（前提 `HasPosRealBinary`）的**唯一**差别；
`HasPosRealBinary` 情形现在也可由本定理推出（把二叉见证给 `HasPosReal`）。 -/
theorem njAdditiveGapUnrestricted_holds : njAdditiveGapUnrestricted (X := X) := by
  intro δ hpos hcard a b hstep
  obtain ⟨T, hwpos, hT⟩ := hpos
  have hc : T.IsCherry a b := NJShrink.isCherry_of_njStep δ hwpos hT hcard hstep
  have hckeep := hc
  obtain ⟨hab, w, haw, hbw⟩ := hc
  -- 前置：`w ≠ leaf b`，且 `2 ≤ degree w`
  have hwb : w ≠ T.leaf b := fun h => T.graph.loopless.irrefl (T.leaf b) (h ▸ hbw)
  have hmemF : ({T.leaf a, T.leaf b} : Finset T.V) ⊆ T.graph.neighborFinset w := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (SimpleGraph.mem_neighborFinset T.graph w (T.leaf a)).mpr haw.symm
    · exact (SimpleGraph.mem_neighborFinset T.graph w (T.leaf b)).mpr hbw.symm
  have hdeg2 : 2 ≤ T.graph.degree w := by
    have h1 : (T.graph.neighborFinset w).card = T.graph.degree w :=
      SimpleGraph.card_neighborFinset_eq_degree T.graph w
    have h2 : ({T.leaf a, T.leaf b} : Finset T.V).card = 2 :=
      Finset.card_pair (fun h => hab (T.leaf.injective h))
    calc 2 = ({T.leaf a, T.leaf b} : Finset T.V).card := h2.symm
      _ ≤ (T.graph.neighborFinset w).card := Finset.card_le_card hmemF
      _ = T.graph.degree w := h1
  by_cases hdeg3 : T.graph.degree w = 3
  · -- ① `degree w = 3`：复用 A5–A8 的 `hdeg` 机器（**不**需要整棵树二叉）
    obtain ⟨z, hwz, hza, hzb, -⟩ := NJShrink.exists_third_of_degree T hab hdeg3 haw hbw
    have hla : T.leaf a ≠ T.leaf b ∧ T.leaf a ≠ w :=
      ⟨fun h => hab (T.leaf.injective h),
        NJShrink.leaf_ne_midpoint_of_degree T hdeg3 hab haw hbw a⟩
    have hzm : z ≠ T.leaf b ∧ z ≠ w :=
      ⟨hzb, fun h => T.graph.loopless.irrefl z (h ▸ hwz)⟩
    refine ⟨NJShrink.shrinkPhylogram_of_degree T hdeg3 hab haw hbw hza hzb hwz hwpos, ?_, ?_⟩
    · intro e
      have key : ∀ e' : Sym2 (NJShrink.ShrinkV T b w),
          e' ∈ (NJShrink.shrinkGraph T a b w z hza).edgeSet →
            0 < NJShrink.shrinkW T a b w z hza hla hzm e' :=
        Sym2.ind (fun u v he =>
          NJShrink.shrinkW_pos_of_degree T hdeg3 hab haw hbw hza hzb hwz hwpos hla hzm
            ((SimpleGraph.mem_edgeSet _).mp he))
      exact key e.1 e.2
    · intro u v
      exact NJShrink.shrinkPhylogram_dist_of_degree T δ hdeg3 hab haw hbw hza hzb hwz hwpos hckeep hT u v
  · -- ② `3 < degree w`：本文件的非二叉机器（只删叶 `b`，`w` 保留）
    have hgt : 3 < T.graph.degree w := by
      have hnd := T.toCladogram.no_degree_two w
      omega
    exact ⟨shrinkPhylogramNB (T := T) hab hbw hwb hgt haw hwpos,
      shrinkPhylogramNB_w_pos (T := T) hab hbw hwb hgt haw hwpos,
      fun u v => shrinkPhylogramNB_dist (T := T) δ hab hbw hwb hgt haw hwpos hckeep hT u v⟩

end Phylo.Stat.NJShrinkNonBinary
