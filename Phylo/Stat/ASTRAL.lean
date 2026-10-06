/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Mathlib.Tactic.Linarith
import Phylo.Stat.MSC

/-!
# `Phylo.Stat.ASTRAL` —— ASTRAL 的得分理论与一致性

**ASTRAL** 的物种树估计量是「**最大化 quartet 得分**的树」：

```
score_D(q) = Σ_{S : |S| = 4}  p_S(q_S)
```

其中 `q` 是「每个 4-元集上选一个 quartet」的选择函数（`QuartetTree.q`）。

（`CONCEPTS.md` §3.11：ASTRAL 属 quartet 型方法，一致性判据是「完备 quartet 集
下真树是唯一最优解」。）

## 本文件证什么

* ★★ `astralScore_le` —— **全局得分上界**：`score_D(q) ≤ score_D(m.q)`（`m` = MSC 数据）；
* ★★ `astralScore_eq_iff` —— **等号刻画**：等号 ⟺ 每个 4-元集上概率相同；
* ★★★ `astral_maximizer_agrees` —— **ASTRAL 输出与真树逐 quartet 一致（模 `swap`）**。

⇒ ASTRAL 在 quartet 层面**完全恢复**真树；把它升成树同构需
「**quartet 系统决定树**」（`Phylo.Stat.QuartetDecides`）。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

/-- **quartet 选择函数**。 -/
abbrev QuartetChoice (X : Type u) [Fintype X] [DecidableEq X] :=
  (S : Finset X) → (hS : S.card = 4) → Split ↥S

/-- **ASTRAL 得分**：所有 4-元集上选定 quartet 的概率之和。 -/
noncomputable def astralScore (D : QuartetFreq X) (q : QuartetChoice X) : ℝ :=
  ∑ S : {S : Finset X // S.card = 4}, D.p S.1 S.2 (q S.1 S.2)

/-- ★★ **ASTRAL 得分上界**：**真树的选择函数得分最大**。

`score_D(q) ≤ score_D(m.q)` 对任意选择函数 `q` 成立 —— 由 `MSCFreq.p_le` 逐点求和。 -/
theorem astralScore_le (m : MSCFreq.{u, v} X) (q : QuartetChoice X) :
    astralScore m.freq q ≤ astralScore m.freq m.q :=
  Finset.sum_le_sum (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
    fun S _ => m.p_le S.1 S.2 (q S.1 S.2)

/-- ★★ **等号刻画**：得分相等 ⟺ 每个 4-元集上概率相同。 -/
theorem astralScore_eq_iff (m : MSCFreq.{u, v} X) (q : QuartetChoice X) :
    astralScore m.freq q = astralScore m.freq m.q ↔
      ∀ (S : Finset X) (hS : S.card = 4),
        m.freq.p S hS (q S hS) = m.freq.p S hS (m.q S hS) := by
  constructor
  · intro heq S hS
    by_contra hne
    have hlt : m.freq.p S hS (q S hS) < m.freq.p S hS (m.q S hS) :=
      lt_of_le_of_ne (m.p_le S hS (q S hS)) hne
    have hsum : astralScore m.freq q < astralScore m.freq m.q := by
      simpa [astralScore] using Finset.sum_lt_sum
        (s := (Finset.univ : Finset {S : Finset X // S.card = 4}))
        (fun S1 _ => m.p_le S1.1 S1.2 (q S1.1 S1.2))
        ⟨⟨S, hS⟩, Finset.mem_univ _, hlt⟩
    rw [heq] at hsum
    exact lt_irrefl _ hsum
  · intro heq
    exact Finset.sum_congr rfl fun S _ => heq S.1 S.2

/-- **ASTRAL 估计量**（谓词形式）：`qt` 是 quartet 树空间中得分最大者。

得分只依赖选择函数；`IsASTRAL` 把最大化要求限制到**树可实现**的选择函数上
（即 `QuartetTree`）。 -/
def IsASTRAL (D : QuartetFreq X) (qt : QuartetTree.{u, v} X) : Prop :=
  ∀ qt1 : QuartetTree.{u, v} X, astralScore D qt1.q ≤ astralScore D qt.q

/-- 真树作为 `QuartetTree` 的投影（`extends` 自动生成）的坐标式。 -/
@[simp] theorem MSCFreq.toQuartetTree_q (m : MSCFreq.{u, v} X) :
    m.toQuartetTree.q = m.q := rfl

@[simp] theorem MSCFreq.toQuartetTree_tree (m : MSCFreq.{u, v} X) :
    m.toQuartetTree.tree = m.tree := rfl

/-- **ASTRAL 最大化者的得分 = 真树的得分**（上界 + 最大化 夹逼）。 -/
theorem astralScore_eq_of_isASTRAL (m : MSCFreq.{u, v} X) {qt : QuartetTree.{u, v} X}
    (h : IsASTRAL m.freq qt) : astralScore m.freq qt.q = astralScore m.freq m.q :=
  le_antisymm (astralScore_le m qt.q) (h m.toQuartetTree)

/-- ★★★ **ASTRAL 输出与真树逐 quartet 一致（模 `swap`）**。

ASTRAL 一致性的**组合核心**：任何得分最大化者，在每个 4-元集上给出的 quartet
都等于真树的 quartet（或它的 `swap`，即同一个无向 quartet）。

**证明**：最大化者与真树得分相等（夹逼）⟹ 逐点概率相等（`astralScore_eq_iff`）
⟹ 由 MSC 的严格不等式（`majorizes`）的逆否，该点只能是 `m.q` 或 `m.q.swap`。 -/
theorem astral_maximizer_agrees (m : MSCFreq.{u, v} X) {qt : QuartetTree.{u, v} X}
    (h : IsASTRAL m.freq qt) (S : Finset X) (hS : S.card = 4) :
    qt.q S hS = m.q S hS ∨ qt.q S hS = (m.q S hS).swap := by
  have hscore := astralScore_eq_of_isASTRAL m h
  have hp := (astralScore_eq_iff m qt.q).mp hscore S hS
  by_contra hcon
  rw [not_or] at hcon
  exact absurd hp (ne_of_lt (m.majorizes S hS (qt.q S hS) hcon.1 hcon.2))
