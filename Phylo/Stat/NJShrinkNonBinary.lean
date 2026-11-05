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

**本文件 = 方案（W48 的第一个 commit）**；实现分两半，见 §7。

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

| 步 | 内容 | 估 |
|---|---|---|
| **G0** | 把 `exists_third` 的 `hbin : IsBinary` 换成 `degree w = 3`（广义化，`NJShrink` 里加一条 `exists_third_of_degree`，旧引理由它派生） | 20 |
| **G1** | `V'`／`leaf'` ／两条求值引理（`leaf' (inl _) .val`、`leaf' (inr _) .val`） | 60 |
| **G2** | 图 ＋ **无环** ＋ **连通** | 150–220 |
| **G3** | 度数（`w` 减 1、其余不变） | 100–140 |
| **G4** | `no_degree_two` ＋ `leaf_iff_degree_one`（`Cladogram` 打包） | 60–90 |
| **G5** | 边权 `w'`（旧边不变、`(leaf a, w)` 改 `½(w_a+w_b)`）＋ 正性 | 50–70 |
| **G6** | `dist` 三支 | 120–180 |
| **G7** | 装配 `HasPosReal (mergeStep δ a b)`（`degree w` 分情形，`= 3` 支用 G0） | 40 |
| | **合计** | **600–820** |

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
