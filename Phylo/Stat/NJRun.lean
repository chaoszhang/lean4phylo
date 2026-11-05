/-
Copyright (c) 2026 ASTER Lab. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.NJRecovers
import Phylo.BunemanGraft

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
| B-1 | `Cladogram.relabel` ＋ `Cladogram.iso_of_card_le_three` | 90 | 待做 |
| B-2 | `graftCladogram_iso_congr`（iso 沿 graft 抬升） | 80 | 待做 |
| B-3 | ★ **`graft_shrink_iso`**：`Iso (graft (shrink T)) T`（本步最难） | 200 | 待做 |
| B-4 | `njRun`（良基递归）＋ `njRun_correct_additive` | 120 | 待做 |

**合计 ≈ 490 行**（派单未给预算；W46 估的 80–120 行**明显偏低**，因为当时没算
`graft_shrink_iso` —— 它是「`isotopic` 的逆手术」在 `Cladogram` 层的显式同构）。

**`graft_shrink_iso` 的关键观测**（B-3 的全部难度都在这里）：
`shrinkPhylogram` 删掉了叶 `b` 与中点 `w`、并把 `leaf a` 直接接到 `z`。
故 graft 回去时，收缩树里**名为 `leaf a` 的那个顶点实际上站在樱桃中点 `w` 的位置**（度 3），
⇒ 同构 `φ : ShrinkV ⊕ Fin 2 ≃ T.V` 取
`φ (inl ⟨v, _⟩) = if v = T.leaf a then w else v`、`φ (inr 0) = T.leaf a`、`φ (inr 1) = T.leaf b`。
邻接的三类情形各用一条度事实：`deg (leaf a) = 1`（唯一邻居 `w`）、`deg w = 3`
（邻居恰是 `leaf a`、`leaf b`、`z`，★★★ `NJShrink.degree_eq_three`）。

## 6 忠实性边界（★ 写在这里，别误传）

* 本文件的定理**只覆盖可加情形**（`δ` 有正权二叉实现）。`njRun` 对**任意** `δ` 都有定义
  （它只要求 `3 ≤ card X`），但 `njRun_correct_additive` 的正确性依赖 `δ` 可实现 ——
  **不能**推广到 CASTER 的 `D̃`（那是 `CASTERNJ.njConsistencyGap` 的建模问题）。
* 结论里的 `njRun` 是**真递归**（每轮 `njStep` 取 `Q` 最小对并合并），
  **不是**「存在性抽取」：graft 用的 `graftCladogram` 是**无条件的树手术**，
  与「是否存在实现树」无关。
-/

namespace Phylo.Stat.NJRun

end Phylo.Stat.NJRun
