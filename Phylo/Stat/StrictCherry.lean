/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.CherryQuartet
import Phylo.Algorithm.NJHardCore

/-!
# `Phylo.Stat.StrictCherry` —— 「二叉 ＋ 边权全正 ⇒ 四点不等式**严格**」的具名缺口（W46 ③）

协调侧 2026-11-05 01:0x 的 W46 复核第 ③ 条：
`CASTERFourPoint4`/`CASTERFourPointN` 的 `hcx`/`hcz`（严格樱桃性）此前**只写在文件头散文里**，
按本库纪律必须落成**具名缺口**并进台账。

## 缺口陈述

库内只有 **非严格**版：

```lean
Cladogram.dist_add_le_of_isCherry : T.IsCherry a b →
  T.dist a b + T.dist p q ≤ T.dist a p + T.dist b q ∧ T.dist a b + T.dist p q ≤ T.dist a q + T.dist b p
```
（`Phylo/CherryQuartet.lean:131`）

**严格**版要多一条**二叉性**：取樱桃中点 `w`，`d(a,b) + d(p,q) ≤ (…)` 的证明里唯一可能取等的地方
是「`w` 落在 `p–q` 路径上」。`w` 的度若恰为 3（二叉），除 `a`、`b` 之外只剩**一个**分支 ⇒
`p`、`q`（都 ≠ a,b）同在该分支里 ⇒ 路径不经过 `w` ⇒ **取等不可能** ⇒ 严格。

⚠️ **反例（为什么非加二叉不可）**：星形树 `T`（4 叶、中心度 4）里每对叶都满足
`IsCherry` 的定义（共享中心），但 `d(a,b) + d(p,q) = d(a,p) + d(b,q)`（三和全相等）
⇒ 严格版在**非二叉**树上**为假**。
（`Cladogram.IsBinary := ∀ v, ¬ IsLeaf v → degree v = 3`，`Phylo/Core.lean:93`。）

## 影响面

* `Phylo/Stat/CASTERFourPoint4.lean`（L4.1）与 `Phylo/Stat/CASTERFourPointN.lean`（L4.2）
  的 `hcx`/`hcz` **由本缺口供给** —— 两个文件的 docstring 已互相点名。
* 本缺口**不在** L4 的证明里被当作假设偷偷用掉：L4 的两个定理把 `hcx`/`hcz` 作为**显式参数**，
  本文件只提供「缺口 ⇒ `hcx`」这条接口（`strictCherry_of_gap`）。

## 诚实边界

* 本文件**不证明**该缺口；它只是把它写成 `def … : Prop` 并进台账。
* 缺口名带 `_gap` 后缀是**台账口径要求**（`scripts/gap_ledger.py`：名字含 `gap` 且用 `def` 落盘才计入口径 A）。
-/

noncomputable section

namespace Phylo.Stat.StrictCherry

open Phylo
open Cladogram

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **缺口（= `Cladogram.dist_add_lt_of_isCherry`）**：实现树**二叉**且**边权全正**时，
樱桃 `{a,b}` 给出的四点不等式是**严格**的。

库内只有非严格版 `Cladogram.dist_add_le_of_isCherry`（`Phylo/CherryQuartet.lean:131`）。
⚠️ 非二叉树上本命题**为假**（星形树，见文件头反例）—— 二叉性是**必需**的。 -/
def strictCherry_of_isBinary_pos_gap : Prop :=
  ∀ (T : Phylogram.{u, v} X), (∀ e : Edge T.toCladogram, 0 < T.w e) → T.toCladogram.IsBinary →
    ∀ (a b : X), T.IsCherry a b →
      ∀ p q : X, p ≠ q → p ≠ a → p ≠ b → q ≠ a → q ≠ b →
        T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf p) (T.leaf q)
            < T.dist (T.leaf a) (T.leaf p) + T.dist (T.leaf b) (T.leaf q) ∧
          T.dist (T.leaf a) (T.leaf b) + T.dist (T.leaf p) (T.leaf q)
            < T.dist (T.leaf a) (T.leaf q) + T.dist (T.leaf b) (T.leaf p)

/-- ★★★ **接口**：缺口成立时，L4.1/L4.2 的严格樱桃假设 `hcx`/`hcz` 由它**直接供给**。

（这条把「散文里的披露」变成**代码里的依赖**：谁想用 L4 的定理，就必须先有本缺口或等价的严格性。） -/
theorem strictCherry_of_gap (h : strictCherry_of_isBinary_pos_gap.{u, v} (X := X))
    (T : Phylogram.{u, v} X) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hbin : T.toCladogram.IsBinary) (x y : X) (hch : T.IsCherry x y) :
    ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      T.dist (T.leaf x) (T.leaf y) + T.dist (T.leaf p) (T.leaf q)
          < T.dist (T.leaf x) (T.leaf p) + T.dist (T.leaf y) (T.leaf q) ∧
        T.dist (T.leaf x) (T.leaf y) + T.dist (T.leaf p) (T.leaf q)
          < T.dist (T.leaf x) (T.leaf q) + T.dist (T.leaf y) (T.leaf p) :=
  fun p q hpq hpx hpy hqx hqy => h T hpos hbin x y hch p q hpq hpx hpy hqx hqy

/-- 缺口 ⟹ L4 的一侧（`hcx` 的形态；`dl` 取实现树的距离）。 -/
theorem hcx_of_gap (h : strictCherry_of_isBinary_pos_gap.{u, v} (X := X))
    (T : Phylogram.{u, v} X) (hpos : ∀ e : Edge T.toCladogram, 0 < T.w e)
    (hbin : T.toCladogram.IsBinary) (x y : X) (hch : T.IsCherry x y) :
    ∀ p q : X, p ≠ q → p ≠ x → p ≠ y → q ≠ x → q ≠ y →
      T.dist (T.leaf x) (T.leaf y) + T.dist (T.leaf p) (T.leaf q)
          < T.dist (T.leaf x) (T.leaf p) + T.dist (T.leaf y) (T.leaf q) ∧
        T.dist (T.leaf x) (T.leaf y) + T.dist (T.leaf p) (T.leaf q)
          < T.dist (T.leaf x) (T.leaf q) + T.dist (T.leaf y) (T.leaf p) :=
  strictCherry_of_gap h T hpos hbin x y hch

end Phylo.Stat.StrictCherry
