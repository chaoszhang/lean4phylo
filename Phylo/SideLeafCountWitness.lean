/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split
import Phylo.Stat.NJstWitness
import Phylo.AttesonRadius

/-!
# `Phylo.SideLeafCountWitness` —— `sideLeafCount` 的**具体树**见证（W12e7）

`Phylo/AttesonRadius.lean` §12 定义了「删边一侧叶数」`Cladogram.sideLeafCount`
（Atteson Lemma 10，`:1774–1804` 的 `|L_i(e)|`），§13 证了桥
`e ∈ P_ij ⟺ i,j 分属 e 两侧`。

本文件在库内**唯一的具体树** `C1234`（`Phylo/Stat/NJstWitness.lean:177`，即 `12|34` 二叉树：
根 `root = {0,1,2,3}`、内部点 `inner = {2,3}`、叶 `0,1,2,3`，共 6 顶点 5 条边）上把这
**5 条边的 `sideLeafCount` 算成显式数值**（★B 的「具体树」层）：

| 边 | `u` 侧 | `|L_u|` | 另一侧 | `|L_v|` |
|---|---|---|---|---|
| `root`—`lf 0` | `{0}` | `1` | `{1,2,3}` | `3` |
| `root`—`lf 1` | `{1}` | `1` | `{0,2,3}` | `3` |
| `inner`—`lf 2` | `{2}` | `1` | `{0,1,3}` | `3` |
| `inner`—`lf 3` | `{3}` | `1` | `{0,1,2}` | `3` |
| `root`–`inner`（内部边） | `{0,1}` | `2` | `{2,3}` | `2` |

挂边一侧由 ★★ `sideLeafCount_leaf_edge` 直接给 `1`；内部边两侧由 ★★★ `two_le_sideLeafCount`
（`degree ≠ 1`）＋ ★★ `sideLeafCount_add_of_adj`（两侧和 `= |X| = 4`）**夹出** `2`
（无需逐叶判定归属）。

⚠️ 本模块依赖 `Phylo.Split` ＋ `Phylo.Stat.NJstWitness` ＋ **`Phylo.AttesonRadius`**
（`sideLeafCount` 住在 `AttesonRadius.lean` §12），且**不被任何文件 import** ⇒ 无环。
注册行由协调侧加：`import Phylo.SideLeafCountWitness`。-/

open SimpleGraph

namespace SideLeafCountWitness

/-! ## 0. 顶点别名（用 `C1234.V` 固定类型，避免 `LaminarVertex F1234` 与 `C1234.V` 的 defeq 摩擦） -/

/-- 根（全簇 `{0,1,2,3}`）。 -/
abbrev root : C1234.V := Uv

/-- 内部点（簇 `{2,3}`）。 -/
abbrev inner : C1234.V := Qv

/-- 叶 `i`。 -/
noncomputable abbrev lf (i : Fin 4) : C1234.V := C1234.leaf i

/-! ## 1. 五条边的邻接 -/

theorem adj_root_inner : C1234.graph.Adj root inner := adj_Uv_Qv

theorem adj_lf0_root : C1234.graph.Adj (lf 0) root := adj_leaf0_Uv

theorem adj_lf1_root : C1234.graph.Adj (lf 1) root := adj_leaf1_Uv

theorem adj_lf2_inner : C1234.graph.Adj (lf 2) inner := adj_leaf2_Qv

theorem adj_lf3_inner : C1234.graph.Adj (lf 3) inner := adj_leaf3_Qv

/-! ## 2. 四条挂边：一侧 `1`、另一侧 `3` -/

theorem leafCount_zero : C1234.sideLeafCount s(lf 0, root) (lf 0) = 1 :=
  C1234.sideLeafCount_leaf_edge adj_lf0_root

theorem otherCount_zero : C1234.sideLeafCount s(lf 0, root) root = 3 := by
  have h := C1234.sideLeafCount_add_of_adj adj_lf0_root
  rw [leafCount_zero, Fintype.card_fin] at h
  omega

theorem leafCount_one : C1234.sideLeafCount s(lf 1, root) (lf 1) = 1 :=
  C1234.sideLeafCount_leaf_edge adj_lf1_root

theorem otherCount_one : C1234.sideLeafCount s(lf 1, root) root = 3 := by
  have h := C1234.sideLeafCount_add_of_adj adj_lf1_root
  rw [leafCount_one, Fintype.card_fin] at h
  omega

theorem leafCount_two : C1234.sideLeafCount s(lf 2, inner) (lf 2) = 1 :=
  C1234.sideLeafCount_leaf_edge adj_lf2_inner

theorem otherCount_two : C1234.sideLeafCount s(lf 2, inner) inner = 3 := by
  have h := C1234.sideLeafCount_add_of_adj adj_lf2_inner
  rw [leafCount_two, Fintype.card_fin] at h
  omega

theorem leafCount_three : C1234.sideLeafCount s(lf 3, inner) (lf 3) = 1 :=
  C1234.sideLeafCount_leaf_edge adj_lf3_inner

theorem otherCount_three : C1234.sideLeafCount s(lf 3, inner) inner = 3 := by
  have h := C1234.sideLeafCount_add_of_adj adj_lf3_inner
  rw [leafCount_three, Fintype.card_fin] at h
  omega

/-! ## 3. 内部边 `s(root, inner)`：两侧各 `2` -/

/-- ★B **`root` 侧 ≥ 2**（`root` 不是叶：`3 ≤ degree root`）。 -/
theorem two_le_root_inner_root : 2 ≤ C1234.sideLeafCount s(root, inner) root := by
  classical
  refine C1234.two_le_sideLeafCount adj_root_inner (fun hdeg => ?_)
  have h := three_le_degree_Uv
  have hdeg' : (Phylo.treeGraph F1234).degree Uv = 1 := hdeg
  omega

/-- ★B **`inner` 侧 ≥ 2**（`inner` 不是叶：`3 ≤ degree inner`）。 -/
theorem two_le_root_inner_inner : 2 ≤ C1234.sideLeafCount s(root, inner) inner := by
  classical
  have h : 2 ≤ C1234.sideLeafCount s(inner, root) inner := by
    refine C1234.two_le_sideLeafCount adj_root_inner.symm (fun hdeg => ?_)
    have h3 := three_le_degree_Qv
    have hdeg' : (Phylo.treeGraph F1234).degree Qv = 1 := hdeg
    omega
  rwa [Sym2.eq_swap] at h

/-- ★B **内部边两侧叶数之和 `= 4 = |X|`**。 -/
theorem sideLeafCount_root_inner_sum :
    C1234.sideLeafCount s(root, inner) root + C1234.sideLeafCount s(root, inner) inner = 4 := by
  have h := C1234.sideLeafCount_add_of_adj adj_root_inner
  rwa [Fintype.card_fin] at h

/-- ★B **`root` 侧叶数 `= 2`**（由「两侧各 ≥ 2」＋「和 = 4」夹出）。 -/
theorem sideLeafCount_root_inner_root : C1234.sideLeafCount s(root, inner) root = 2 := by
  have hsum := sideLeafCount_root_inner_sum
  have h1 := two_le_root_inner_root
  have h2 := two_le_root_inner_inner
  omega

/-- ★B **`inner` 侧叶数 `= 2`**。 -/
theorem sideLeafCount_root_inner_inner : C1234.sideLeafCount s(root, inner) inner = 2 := by
  have hsum := sideLeafCount_root_inner_sum
  have h1 := two_le_root_inner_root
  have h2 := two_le_root_inner_inner
  omega

/-- ★B **侧数互补**：`|L_inner| = |X| − |L_root|`（`sideLeafCount_compl` 的具体树实例）。 -/
theorem sideLeafCount_root_inner_compl :
    C1234.sideLeafCount s(root, inner) inner = 4 - C1234.sideLeafCount s(root, inner) root := by
  have h := C1234.sideLeafCount_compl adj_root_inner
  rwa [Fintype.card_fin] at h

/-! ## 4. ★B 汇总：五条边 10 个数值一次性列出 -/

example :
    C1234.sideLeafCount s(lf 0, root) (lf 0) = 1 ∧
    C1234.sideLeafCount s(lf 0, root) root = 3 ∧
    C1234.sideLeafCount s(lf 1, root) (lf 1) = 1 ∧
    C1234.sideLeafCount s(lf 1, root) root = 3 ∧
    C1234.sideLeafCount s(lf 2, inner) (lf 2) = 1 ∧
    C1234.sideLeafCount s(lf 2, inner) inner = 3 ∧
    C1234.sideLeafCount s(lf 3, inner) (lf 3) = 1 ∧
    C1234.sideLeafCount s(lf 3, inner) inner = 3 ∧
    C1234.sideLeafCount s(root, inner) root = 2 ∧
    C1234.sideLeafCount s(root, inner) inner = 2 :=
  ⟨leafCount_zero, otherCount_zero, leafCount_one, otherCount_one, leafCount_two,
    otherCount_two, leafCount_three, otherCount_three, sideLeafCount_root_inner_root,
    sideLeafCount_root_inner_inner⟩

end SideLeafCountWitness
