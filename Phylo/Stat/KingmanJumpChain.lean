/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.Coalescent

/-!
# `Phylo.Stat.KingmanJumpChain` —— Kingman 1982 跳链的 (2.1) 转移与 (2.2) 绝对概率

文献：J. F. C. Kingman, *The Coalescent*, Stochastic Processes and their Applications **13**
(1982) 235–248。引用一律用 OCR 版 `references/md/Kingman1982_TheCoalescent.md` 的
**行号 + 公式内容**双重定位（该版**公式编号在版面里错位**：编号 `(2.1)`/`(2.2)`/`(2.3)`
印在显示公式**之后**，见 `W10_COALESCENT_SPEC.md` §0.5）。

## 内容

* **状态空间**：`E_n` = `{1,…,n}` 上等价关系的全体 = 集合划分（K82 第 **47–57** 行）；
  本文件用 Mathlib 的 `Finpartition (univ : Finset (Fin n))`（`abbrev Part n`），
  `k`-块层 `PartK n k`。
* **(2.1) 的载体（一步合并）**：`mergeBlock` / `mergePart`：把 `Q` 的两个块并成一个；
  证 `(mergePart …).parts.card = Q.parts.card - 1` 与对称性 `mergePart_comm`
  （K82 第 **215–217** 行「`ξ ≺ η`，`k` 个块减为 `k−1` 个」）。
* **(2.1) 的有限核**：`merge_outcomes_card`（块对总数 = `C(|Q|,2)`）与
  `merge_outcomes_injective`（不同的块对给出不同的合并结果，即「块对由结果唯一决定」）。
* **(2.2) 绝对概率**：`partitionProb n k P`
  `= (n−k)! k! (k−1)! / (n! (n−1)!) · ∏_{B ∈ P.parts} |B|!`（K82 第 **219–228** 行）。
* **(★) 单块分裂恒等式**（**有序**和）：
  `Σ_{A ⊊ B, A ≠ ∅} |A|!·|B\A|! = |B|!·(|B|−1)`；
  无限制版本 `Σ_{A ⊆ B} |A|!·|B\A|! = (|B|+1)·|B|!`。
* **(2.1) 的逆向（劈块）**：`splitBlock` / `splitBlockParts` / `splitBlock_parts` /
  `card_splitBlock` / `prod_factorial_splitBlock`，以及劈块下的 `partitionProb` 比值
  `partitionProb_splitBlock_mul`。
* **层间一致性递归（规格 §1.5）**：索引双射 `sum_mergeIdx_eq_splitIdx`（有序块对 ↔ 有序二分）、
  代数核 `splitSum_eq`、计数核 `card_pairSet`，合成
  `partitionProb_merge_recursion`（乘法形状
  `partitionProb n k P · C(k+1,2) = Σ_{Q : |Q| = k+1, MergeInto Q P} partitionProb n (k+1) Q`）
  与 `partitionProb_merge_recursion_div`（规格 §1.5 的原始除法形状）。
* **验收① 归一化**（规格 §1.4，K82 第 **274–276** 行的倒向归纳）：
  `stateSum_eq_succ`（`S_k = S_{k+1}`）、`stateSum_self`（`S_n = 1`）、
  `stateSum_eq_one`、`partitionProb_sum_eq_one`：`Σ_{|P|=k} partitionProb n k P = 1`。
* **验收③ 概率质量函数**（规格 §1.6 的「或等价物」）：`jumpWeight`（`ℝ` 值权重）+
  `jumpWeight_nonneg` + `jumpWeight_sum_eq_one`（`Σ = 1`）。

## 诚实边界（逐条）

| 条目 | 状态 |
|---|---|
| (2.1) 的一步合并 `mergePart`、块数下降 `k+1 → k`、次序对称 | **已证**（`mergePart`, `card_mergePart`, `mergePart_comm`） |
| (2.2) 的**定义**、正性、`k = n` 处的值 `= 1` | **已证**（`partitionProb`, `partitionProb_pos`, `partitionProb_self_bot`, `partitionLead_pos`） |
| (★) 单块分裂恒等式（有序）与无限制版本 | **已证**（`sum_powerset_factorial`, `sum_powerset_factorial_unrestricted`） |
| 劈块层：`splitBlock`、块数加一、阶乘积的作用、`partitionProb` 比值 | **已证**（`card_splitBlock`, `prod_factorial_splitBlock`, `partitionProb_splitBlock_mul`） |
| (2.1) 的「`C(k+1,2)` 个一步合并结果互不相同」与块对总数 | **已证**（`merge_outcomes_injective`, `merge_outcomes_card`） |
| 规格 §1.5 的层间一致性递归 | ✅ **已证**（`partitionProb_merge_recursion`, `partitionProb_merge_recursion_div`） |
| 验收① 归一化 `Σ_{\|P\|=k} partitionProb n k P = 1` | ✅ **已证**（`partitionProb_sum_eq_one`, `stateSum_eq_one`） |
| 验收③ 概率质量函数（`PMF` 的 `ℝ` 值**等价物**） | ✅ **已证**（`jumpWeight`, `jumpWeight_nonneg`, `jumpWeight_sum_eq_one`） |
| `PMF` **对象本身** | ❌ **未做**（见下：需要新 Mathlib import，本批按规格 §1 未引入） |

### 唯一的边界：没有 `PMF` 对象本身

本文件交付的是 `jumpWeight : PartK n k → ℝ` 连同它的两条定义性质（非负 + 归一），
即规格 §1.6 明确允许的「`PMF` 的**等价物**」。真正的 `PMF` 对象**没有**构造，
原因是 `Mathlib.Probability.*`（含 `PMF`）**不在**本库 import 闭包内
（实测 `#check @PMF.ofFinset` → `unknown identifier`，见 `scripts/w10a_scratch.lean`），
而规格 §1 说本子批不需要新 Mathlib import。**其余内容全部已证，全文零 `sorry` / 零 `axiom`。**

### 层间一致性递归的证明结构（三条腿）

1. **索引双射**（`sum_mergeIdx_eq_splitIdx`）：`Finset.sum_bij'` 让
   `{Q : |Q| = k+1, 有序块对 (B1,B2)，合并结果 = P}` ↦ `{X ∈ P.parts, A ⊊ X 非空}`、
   `(P, (X,A)) ↦ (splitBlock P X A, (A, X\A))`；往返恒等由 `splitBlock_mergePart` /
   `mergePart_splitBlock` 给出。两边都是**有序**指标 ⇒ 无 `1/2` 因子。
2. **代数核**（`splitSum_eq` / `splitSum_nested`）：`partitionProb_splitBlock_mul` 逐项给比值，
   `sum_powerset_factorial_of_nonempty` 给单块的有序分裂和，`Finpartition.sum_card_parts`
   给 `Σ_X (|X| − 1) = n − k`，三者相乘后 `(n−k)` 相消，得 `(k+1)k · partitionProb n k P`。
3. **计数核**（`card_pairSet`）：使 `Q` 合并到 `P` 的有序块对恰有 `2` 个（`(B1,B2)` 与
   `(B2,B1)`）当且仅当 `MergeInto Q P`；配合 `merge_outcomes_injective` 得
   `Σ_{mergeIdx} = 2 · Σ_{MergeInto}`，再约去 `2` 与 `C(k+1,2) = (k+1)k/2`（`two_mul_choose_two_cast`）。

归一化则把腿部 1+2 对 `P` 求和、再用 `Finset.sum_comm` 与腿部 3 交换求和次序，得
`(k+1)k · S_k = (k+1)k · S_{k+1}`（`stateSum_eq_succ`），加上基底 `S_n = 1`
（`stateSum_self` + `eq_bot_of_card_parts`）与倒向归纳 `stateSum_eq_one`。

## 与库内既有设施的关系

`Phylo/Stat/Coalescent.lean` 已把「`k` 个块中每一对**等概率** `1/C(k,2)`」写成
`Coalescent.jumpProb`，并证了有限核 `sum_uniform_jumpProb`，但那里的「合并对」是
`Finset.univ.powersetCard 2 : Finset (Finset (Fin k))` 这一**抽象**指标，没有块的内容与
(2.2) 的绝对权重。本文件补的正是**块层**：合并哪两个块、结果是什么划分、绝对概率是多少。

数值复核脚本：`scripts/msc/kingman_jumpchain.py`（精确有理数穷举，`n ≤ 7`）。
-/

namespace Phylo.Stat.KingmanJumpChain

open Finset

variable {n : ℕ}

/-! ## 状态空间 -/

/-- **状态空间** `E_n`：`{0,…,n−1}` 上的等价关系全体（= 集合划分）。

K82 第 **47–57** 行把状态空间取为 `{1,…,n}` 上等价关系的全体；本库用 `Fin n` 标号，
故取 `Finpartition (univ : Finset (Fin n))`（`Finpartition` 的 `Fintype` 实例已在本文件
import 闭包内，见 `Mathlib/Order/Partition/Finpartition.lean:311`）。 -/
abbrev Part (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))

/-- **`k`-块层**：恰有 `k` 个等价类的状态。 -/
abbrev PartK (n k : ℕ) := {P : Part n // P.parts.card = k}

/-- `Part n` 的块数不超过 `n`。 -/
theorem card_parts_le (P : Part n) : P.parts.card ≤ n := by
  simpa using P.card_parts_le_card

/-! ## (2.1) 的载体：一步合并 -/

/-- 把 `Q` 的两个块 `B1, B2` 并成一个块后的**块集合**（尚未证明它是划分）。 -/
def mergeBlock (Q : Part n) (B1 B2 : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  insert (B1 ∪ B2) ((Q.parts.erase B1).erase B2)

/-- `mergeBlock` 中「除合并块以外的块」的隶属刻画。 -/
lemma mem_mergeBlock_erase {Q : Part n} {B1 B2 a : Finset (Fin n)} :
    a ∈ (Q.parts.erase B1).erase B2 ↔ a ≠ B2 ∧ a ≠ B1 ∧ a ∈ Q.parts := by
  simp only [Finset.mem_erase]

/-- 两个**不同**块之并不是一个块（(2.1) 中 `ξ ≺ η` 良定义性的来源）。 -/
lemma ne_union_of_mem_parts {Q : Part n} {B1 B2 : Finset (Fin n)}
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) : B1 ∪ B2 ∉ Q.parts := by
  intro hX
  obtain ⟨b, hb⟩ := Q.nonempty_of_mem_parts hB2
  have hXB2 : B1 ∪ B2 = B2 :=
    Q.eq_of_mem_parts hX hB2 (Finset.mem_union.mpr (Or.inr hb)) hb
  obtain ⟨b1, hb1⟩ := Q.nonempty_of_mem_parts hB1
  have hb1B2 : b1 ∈ B2 := by
    rw [← hXB2]; exact Finset.mem_union.mpr (Or.inl hb1)
  exact hne (Q.eq_of_mem_parts hB1 hB2 hb1 hb1B2)

/-- `Finset.sup id` 关于 `insert` 的展开（把 `id` 与 `⊔` 的 `defeq` 差异挡在下面）。 -/
lemma sup_insert_id {s : Finset (Finset (Fin n))} {a : Finset (Fin n)} :
    (insert a s).sup id = a ∪ s.sup id := by
  rw [Finset.sup_insert]; rfl

/-- `Finset.sup id` 关于 `erase` 的展开（`a ∈ s` 时 `s.sup id = a ∪ (s.erase a).sup id`）。 -/
lemma sup_eq_union_of_mem {s : Finset (Finset (Fin n))} {a : Finset (Fin n)} (ha : a ∈ s) :
    s.sup id = a ∪ (s.erase a).sup id := by
  conv_lhs => rw [← Finset.insert_erase ha]
  rw [sup_insert_id]

/-- `mergeBlock` 仍然 `SupIndep`：合并两块后剩下的块依旧两两不交。
（`B1 ≠ B2` 不必要，但为与 `mergePart` 的接口一致而保留。） -/
lemma supIndep_mergeBlock (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (_hne : B1 ≠ B2) :
    (mergeBlock Q B1 B2).SupIndep id := by
  rw [Finset.supIndep_iff_pairwiseDisjoint]
  intro a ha b hb hab
  have ha' : a ∈ mergeBlock Q B1 B2 := ha
  have hb' : b ∈ mergeBlock Q B1 B2 := hb
  change Disjoint a b
  simp only [mergeBlock, Finset.mem_insert] at ha' hb'
  rcases ha' with rfl | ha'
  · rcases hb' with rfl | hb'
    · exact absurd rfl hab
    · rw [mem_mergeBlock_erase] at hb'
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_union.mp hx1 with hx1 | hx1
      · exact Finset.disjoint_left.mp (Q.disjoint hB1 hb'.2.2 (Ne.symm hb'.2.1)) hx1 hx2
      · exact Finset.disjoint_left.mp (Q.disjoint hB2 hb'.2.2 (Ne.symm hb'.1)) hx1 hx2
  · rcases hb' with rfl | hb'
    · rw [mem_mergeBlock_erase] at ha'
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_union.mp hx2 with hx2 | hx2
      · exact Finset.disjoint_left.mp (Q.disjoint ha'.2.2 hB1 ha'.2.1) hx1 hx2
      · exact Finset.disjoint_left.mp (Q.disjoint ha'.2.2 hB2 ha'.1) hx1 hx2
    · rw [mem_mergeBlock_erase] at ha' hb'
      exact Q.disjoint ha'.2.2 hb'.2.2 hab

/-- `mergeBlock` 的并不变：`(mergeBlock Q B1 B2).sup id = Q.parts.sup id`。

（先证这个**不含 `univ`** 的形式：`Q : Part n` 的类型里含 `Finset.univ`，
直接 `rw` `univ` 会触发依赖重写的 `motive is not type correct`。） -/
lemma sup_mergeBlock_eq (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    (mergeBlock Q B1 B2).sup id = Q.parts.sup id := by
  have hB2' : B2 ∈ Q.parts.erase B1 := Finset.mem_erase.mpr ⟨Ne.symm hne, hB2⟩
  calc (mergeBlock Q B1 B2).sup id
      = (B1 ∪ B2) ∪ ((Q.parts.erase B1).erase B2).sup id := by
        rw [mergeBlock, sup_insert_id]
    _ = B1 ∪ (B2 ∪ ((Q.parts.erase B1).erase B2).sup id) := Finset.union_assoc B1 B2 _
    _ = B1 ∪ (Q.parts.erase B1).sup id := by rw [sup_eq_union_of_mem hB2']
    _ = Q.parts.sup id := (sup_eq_union_of_mem hB1).symm

/-- `mergeBlock` 的并仍是 `univ`：合并**不丢**元素。 -/
lemma sup_mergeBlock (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    (mergeBlock Q B1 B2).sup id = (Finset.univ : Finset (Fin n)) :=
  (sup_mergeBlock_eq Q B1 B2 hB1 hB2 hne).trans Q.sup_parts

/-- `mergeBlock` 不含空块（Finset 上 `⊥ = ∅`）。 -/
lemma bot_notMem_mergeBlock (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) : (⊥ : Finset (Fin n)) ∉ mergeBlock Q B1 B2 := by
  rw [mergeBlock, Finset.mem_insert]
  rintro (h | h)
  · have hne : (B1 ∪ B2).Nonempty :=
      Finset.Nonempty.mono Finset.subset_union_left (Q.nonempty_of_mem_parts hB1)
    exact hne.ne_empty h.symm
  · exact Q.bot_notMem (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))

/-- ★ **(2.1) 的一步合并**：把 `Q` 的两个不同块 `B1, B2` 并成一个块，得同一状态空间里的
新划分（K82 第 **215–217 行**的 `ξ ≺ η` 在集合层的实现）。 -/
def mergePart (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) : Part n where
  parts := mergeBlock Q B1 B2
  supIndep := supIndep_mergeBlock Q B1 B2 hB1 hB2 hne
  sup_parts := sup_mergeBlock Q B1 B2 hB1 hB2 hne
  bot_notMem := bot_notMem_mergeBlock Q B1 B2 hB1

lemma mergePart_parts (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    (mergePart Q B1 B2 hB1 hB2 hne).parts = mergeBlock Q B1 B2 := rfl

/-- ★ **合并使块数减一**：(2.1) 的层数下降 `k+1 → k`（K82 第 **215–217** 行）。 -/
theorem card_mergePart (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    (mergePart Q B1 B2 hB1 hB2 hne).parts.card = Q.parts.card - 1 := by
  have hX : B1 ∪ B2 ∉ (Q.parts.erase B1).erase B2 := fun h =>
    ne_union_of_mem_parts hB1 hB2 hne
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hB2' : B2 ∈ Q.parts.erase B1 := Finset.mem_erase.mpr ⟨Ne.symm hne, hB2⟩
  have h2 : 2 ≤ Q.parts.card := by
    have hsub : ({B1, B2} : Finset (Finset (Fin n))) ⊆ Q.parts := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hB1
      · exact hB2
    calc 2 = ({B1, B2} : Finset (Finset (Fin n))).card := (Finset.card_pair hne).symm
      _ ≤ Q.parts.card := Finset.card_le_card hsub
  rw [mergePart_parts, mergeBlock, Finset.card_insert_of_notMem hX,
    Finset.card_erase_of_mem hB2', Finset.card_erase_of_mem hB1]
  omega

/-- `mergeBlock` 对调换 `B1, B2` 不变。 -/
lemma mergeBlock_comm (Q : Part n) (B1 B2 : Finset (Fin n)) :
    mergeBlock Q B1 B2 = mergeBlock Q B2 B1 := by
  ext x
  simp only [mergeBlock, Finset.mem_insert, Finset.mem_erase, Finset.union_comm]
  tauto

/-- `mergePart` 的值与「两块的差」的**证明项无关**（证明无关性；`parts` 不含证明）。 -/
lemma mergePart_proof_irrel (Q : Part n) (B1 B2 : Finset (Fin n)) (h1 : B1 ∈ Q.parts)
    (h2 : B2 ∈ Q.parts) (hne hne' : B1 ≠ B2) :
    mergePart Q B1 B2 h1 h2 hne = mergePart Q B1 B2 h1 h2 hne' :=
  Finpartition.ext rfl

/-- 合并与 `B1, B2` 的**次序无关**（(2.1) 的对称性）。 -/
theorem mergePart_comm (Q : Part n) (B1 B2 : Finset (Fin n))
    (hB1 : B1 ∈ Q.parts) (hB2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    mergePart Q B1 B2 hB1 hB2 hne = mergePart Q B2 B1 hB2 hB1 (Ne.symm hne) :=
  Finpartition.ext (mergeBlock_comm Q B1 B2)

/-- `Finset.erase` 的两次擦除可交换。 -/
lemma erase_erase_comm {α : Type*} [DecidableEq α] (s : Finset α) (a b : α) :
    (s.erase a).erase b = (s.erase b).erase a := by
  ext x
  simp only [Finset.mem_erase]
  tauto

/-- ★ **(2.1) 的有限核①**：`Q` 的**不同块对**给出**不同**的一步合并结果
（规格 §1.6 的 `merge_outcomes_injective`）：块对 `{B1,B2}` 由合并结果**唯一决定**。

（合并结果里那个「不是 `Q` 的块」的块恰是 `B1 ∪ B2`，把它从两边擦掉就恢复出
`Q.parts`，再对 `Q.parts = insert B1 (insert B2 S)` 用两次 `insert_erase` 即得。）
规格里写的 `Set.InjOn (fun p : {p // p ∈ Q.parts.powersetCard 2} => …) Set.univ`
是本条在「二元素块子集」指标下的等价形式。 -/
theorem merge_outcomes_injective (Q : Part n) {B1 B2 B3 B4 : Finset (Fin n)}
    (h1 : B1 ∈ Q.parts) (h2 : B2 ∈ Q.parts) (h3 : B3 ∈ Q.parts) (h4 : B4 ∈ Q.parts)
    (hne1 : B1 ≠ B2) (hne2 : B3 ≠ B4)
    (heq : mergePart Q B1 B2 h1 h2 hne1 = mergePart Q B3 B4 h3 h4 hne2) :
    ({B1, B2} : Finset (Finset (Fin n))) = {B3, B4} := by
  have hp : mergeBlock Q B1 B2 = mergeBlock Q B3 B4 := by
    rw [← mergePart_parts Q B1 B2 h1 h2 hne1, heq,
      mergePart_parts Q B3 B4 h3 h4 hne2]
  have hXnot : B1 ∪ B2 ∉ (Q.parts.erase B1).erase B2 := fun h =>
    ne_union_of_mem_parts h1 h2 hne1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hYnot : B3 ∪ B4 ∉ (Q.parts.erase B3).erase B4 := fun h =>
    ne_union_of_mem_parts h3 h4 hne2 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  -- 合并块由合并结果唯一决定
  have hXY : B1 ∪ B2 = B3 ∪ B4 := by
    have hmem : B1 ∪ B2 ∈ mergeBlock Q B3 B4 := by
      rw [← hp]; exact Finset.mem_insert.mpr (Or.inl rfl)
    rw [mergeBlock, Finset.mem_insert] at hmem
    rcases hmem with h | h
    · exact h
    · exact absurd (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
        (ne_union_of_mem_parts h1 h2 hne1)
  have hYnot' : B1 ∪ B2 ∉ (Q.parts.erase B3).erase B4 := hXY.symm ▸ hYnot
  -- 「其余块」的集合也由合并结果决定
  have hS : (Q.parts.erase B1).erase B2 = (Q.parts.erase B3).erase B4 := by
    have hthis := congrArg (fun s : Finset (Finset (Fin n)) => s.erase (B1 ∪ B2)) hp
    rw [mergeBlock, mergeBlock, ← hXY, Finset.erase_insert hXnot,
      Finset.erase_insert hYnot'] at hthis
    exact hthis
  have hQ1 : insert B1 (insert B2 ((Q.parts.erase B1).erase B2)) = Q.parts := by
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨Ne.symm hne1, h2⟩),
      Finset.insert_erase h1]
  have hB3notS2 : B3 ∉ (Q.parts.erase B3).erase B4 := by
    rw [erase_erase_comm]
    exact Finset.notMem_erase B3 (Q.parts.erase B4)
  have hB4notS2 : B4 ∉ (Q.parts.erase B3).erase B4 :=
    Finset.notMem_erase B4 (Q.parts.erase B3)
  have hB3notS1 : B3 ∉ (Q.parts.erase B1).erase B2 := by rw [hS]; exact hB3notS2
  have hB4notS1 : B4 ∉ (Q.parts.erase B1).erase B2 := by rw [hS]; exact hB4notS2
  have hB3in : B3 = B1 ∨ B3 = B2 := by
    have hmem : B3 ∈ insert B1 (insert B2 ((Q.parts.erase B1).erase B2)) := by
      rw [hQ1]; exact h3
    rw [Finset.mem_insert, Finset.mem_insert] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hB3notS1
  have hB4in : B4 = B1 ∨ B4 = B2 := by
    have hmem : B4 ∈ insert B1 (insert B2 ((Q.parts.erase B1).erase B2)) := by
      rw [hQ1]; exact h4
    rw [Finset.mem_insert, Finset.mem_insert] at hmem
    rcases hmem with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hB4notS1
  have hsub : ({B3, B4} : Finset (Finset (Fin n))) ⊆ {B1, B2} := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with rfl | rfl
    · exact hB3in
    · exact hB4in
  exact (Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair hne1, Finset.card_pair hne2])).symm

/-- ★ **(2.1) 的有限核②**：`Q` 的块对总数恰是 `C(|Q|,2)`（规格 §1.6 的
`merge_outcomes_card`）；与 `merge_outcomes_injective` 合起来即「从 `Q` 出发的 `C(k,2)` 个
一步合并互不相同、每个概率 `1/C(k,2)`」。 -/
theorem merge_outcomes_card (Q : Part n) (_hQ : 2 ≤ Q.parts.card) :
    (Q.parts.powersetCard 2).card = Q.parts.card.choose 2 :=
  Finset.card_powersetCard 2 Q.parts

/-! ## (2.1) 的逆向：把一个块劈成两块 -/

/-- 把 `P` 的块 `B` 劈成 `A` 与 `B \ A` 后的**块集合**（尚未证明它是划分）。 -/
def splitBlockParts (P : Part n) (B A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  insert A (insert (B \ A) (P.parts.erase B))

/-- `splitBlockParts` 的隶属刻画。 -/
lemma mem_splitBlockParts {P : Part n} {B A a : Finset (Fin n)} :
    a ∈ splitBlockParts P B A ↔ a = A ∨ a = B \ A ∨ (a ≠ B ∧ a ∈ P.parts) := by
  simp only [splitBlockParts, Finset.mem_insert, Finset.mem_erase]

/-- `A` 非空时 `A ≠ B \ A`（`A` 与 `B \ A` 不交）。 -/
lemma ne_sdiff_of_subset {B A : Finset (Fin n)} (hAne : A.Nonempty) : A ≠ B \ A := by
  intro h
  obtain ⟨a, ha⟩ := hAne
  exact (Finset.mem_sdiff.mp (h ▸ ha)).2 ha

/-- `A ⊆ B`、`A ≠ ∅` 时 `B \ A ≠ B`。 -/
lemma sdiff_ne_self_of_ssubset {B A : Finset (Fin n)} (hA : A ⊆ B)
    (hAne : A.Nonempty) : B \ A ≠ B := by
  intro h
  obtain ⟨a, ha⟩ := hAne
  have : a ∈ B \ A := by rw [h]; exact hA ha
  exact (Finset.mem_sdiff.mp this).2 ha

/-- `A ⊆ B`、`A ≠ B` 时 `B \ A` 非空。 -/
lemma sdiff_nonempty_of_ssubset {B A : Finset (Fin n)} (hA : A ⊆ B) (hAlt : A ≠ B) :
    (B \ A).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  exact hAlt (Finset.Subset.antisymm hA fun b hb => by
    by_contra hbA
    exact Finset.notMem_empty b (h ▸ Finset.mem_sdiff.mpr ⟨hb, hbA⟩))

/-- `A ⊆ B`、`A ≠ ∅`、`A ≠ B` 时 `A ∉ P.parts`（`P` 的块是极大块）。 -/
lemma notMem_parts_of_ssubset {P : Part n} {B A : Finset (Fin n)} (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) : A ∉ P.parts := fun hAP =>
  hAlt (P.eq_of_mem_parts hAP hB hAne.choose_spec (hA hAne.choose_spec))

/-- `A ⊆ B`、`A ≠ ∅`、`A ≠ B` 时 `B \ A ∉ P.parts`。 -/
lemma notMem_parts_sdiff {P : Part n} {B A : Finset (Fin n)} (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) : B \ A ∉ P.parts := by
  intro hBP
  have hne := sdiff_nonempty_of_ssubset hA hAlt
  exact sdiff_ne_self_of_ssubset hA hAne
    (P.eq_of_mem_parts hBP hB hne.choose_spec (Finset.mem_sdiff.mp hne.choose_spec).1)

/-- `splitBlockParts` 的并不变：`(splitBlockParts P B A).sup id = P.parts.sup id`（`A ⊆ B`）。

同样先证**不含 `univ`** 的形式（理由见 `sup_mergeBlock_eq`）。 -/
lemma sup_splitBlockParts_eq (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts)
    (hA : A ⊆ B) : (splitBlockParts P B A).sup id = P.parts.sup id := by
  calc (splitBlockParts P B A).sup id
      = A ∪ ((B \ A) ∪ (P.parts.erase B).sup id) := by
        rw [splitBlockParts, sup_insert_id, sup_insert_id]
    _ = (A ∪ (B \ A)) ∪ (P.parts.erase B).sup id := (Finset.union_assoc A (B \ A) _).symm
    _ = B ∪ (P.parts.erase B).sup id := by rw [Finset.union_sdiff_of_subset hA]
    _ = P.parts.sup id := (sup_eq_union_of_mem hB).symm

/-- ★ **劈块**：把 `P` 的块 `B` 替换成 `A` 与 `B \ A`，得块数多一个的划分。
这是 (2.1) 的**逆向**操作，也是层间一致性递归的求和指标。 -/
def splitBlock (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts) (hA : A ⊆ B)
    (hAne : A.Nonempty) (hAlt : A ≠ B) : Part n where
  parts := splitBlockParts P B A
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro a ha b hb hab
    have ha' : a ∈ splitBlockParts P B A := ha
    have hb' : b ∈ splitBlockParts P B A := hb
    change Disjoint a b
    rw [Finset.disjoint_left]
    intro x hxa hxb
    rw [mem_splitBlockParts] at ha' hb'
    rcases ha' with rfl | rfl | ⟨haB, haP⟩
    · rcases hb' with rfl | rfl | ⟨hbB, hbP⟩
      · exact hab rfl
      · exact (Finset.mem_sdiff.mp hxb).2 hxa
      · exact Finset.disjoint_left.mp (P.disjoint hB hbP (Ne.symm hbB)) (hA hxa) hxb
    · rcases hb' with rfl | rfl | ⟨hbB, hbP⟩
      · exact (Finset.mem_sdiff.mp hxa).2 hxb
      · exact hab rfl
      · exact Finset.disjoint_left.mp (P.disjoint hB hbP (Ne.symm hbB))
          (Finset.mem_sdiff.mp hxa).1 hxb
    · rcases hb' with rfl | rfl | ⟨hbB, hbP⟩
      · exact Finset.disjoint_left.mp (P.disjoint haP hB haB) hxa (hA hxb)
      · exact Finset.disjoint_left.mp (P.disjoint haP hB haB) hxa
          (Finset.mem_sdiff.mp hxb).1
      · exact Finset.disjoint_left.mp (P.disjoint haP hbP hab) hxa hxb
  sup_parts := (sup_splitBlockParts_eq P B A hB hA).trans P.sup_parts
  bot_notMem := by
    rw [splitBlockParts, Finset.mem_insert, Finset.mem_insert, Finset.mem_erase]
    rintro (h | h | h)
    · exact hAne.ne_empty h.symm
    · exact (sdiff_nonempty_of_ssubset hA hAlt).ne_empty h.symm
    · exact P.bot_notMem h.2

lemma splitBlock_parts (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) :
    (splitBlock P B A hB hA hAne hAlt).parts = splitBlockParts P B A := rfl

/-- ★ **劈块使块数加一**（`card_mergePart` 的逆向）。 -/
theorem card_splitBlock (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) :
    (splitBlock P B A hB hA hAne hAlt).parts.card = P.parts.card + 1 := by
  have hAnP := notMem_parts_of_ssubset hB hA hAne hAlt
  have hBnP := notMem_parts_sdiff hB hA hAne hAlt
  have hAnI : A ∉ insert (B \ A) (P.parts.erase B) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact ne_sdiff_of_subset hAne h
    · exact hAnP (Finset.mem_of_mem_erase h)
  have hBnI : B \ A ∉ P.parts.erase B := fun h => hBnP (Finset.mem_of_mem_erase h)
  have h1 : 1 ≤ P.parts.card := Finset.card_pos.mpr ⟨B, hB⟩
  rw [splitBlock_parts, splitBlockParts, Finset.card_insert_of_notMem hAnI,
    Finset.card_insert_of_notMem hBnI, Finset.card_erase_of_mem hB]
  omega

/-- ★ **劈块对「块大小阶乘之积」的作用**（乘 `|B|!` 后的**无除法**形式）。 -/
theorem prod_factorial_splitBlock (P : Part n) (B A : Finset (Fin n)) (hB : B ∈ P.parts)
    (hA : A ⊆ B) (hAne : A.Nonempty) (hAlt : A ≠ B) :
    (∏ B' ∈ (splitBlock P B A hB hA hAne hAlt).parts, (Nat.factorial B'.card : ℝ))
        * (Nat.factorial B.card : ℝ)
      = (∏ B' ∈ P.parts, (Nat.factorial B'.card : ℝ))
        * ((Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)) := by
  have hAnP := notMem_parts_of_ssubset hB hA hAne hAlt
  have hBnP := notMem_parts_sdiff hB hA hAne hAlt
  have hAnI : A ∉ insert (B \ A) (P.parts.erase B) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact ne_sdiff_of_subset hAne h
    · exact hAnP (Finset.mem_of_mem_erase h)
  have hBnI : B \ A ∉ P.parts.erase B := fun h => hBnP (Finset.mem_of_mem_erase h)
  have hQ : (∏ B' ∈ (splitBlock P B A hB hA hAne hAlt).parts, (Nat.factorial B'.card : ℝ))
      = (Nat.factorial A.card : ℝ) * ((Nat.factorial (B \ A).card : ℝ)
          * ∏ B' ∈ P.parts.erase B, (Nat.factorial B'.card : ℝ)) := by
    rw [splitBlock_parts, splitBlockParts, Finset.prod_insert hAnI, Finset.prod_insert hBnI]
  have hP : (∏ B' ∈ P.parts, (Nat.factorial B'.card : ℝ))
      = (Nat.factorial B.card : ℝ)
        * ∏ B' ∈ P.parts.erase B, (Nat.factorial B'.card : ℝ) := by
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.prod_insert (Finset.notMem_erase B P.parts)]
  rw [hQ, hP]; ring

/-! ## (2.2) 绝对概率 -/

/-- ★★ **Kingman 1982 (2.2)**（OCR 版第 **219–228 行**，编号印在公式**之后**）：

> `P{S_k = ξ} = (n−k)! k! (k−1)! / ( n! (n−1)! ) · λ₁! λ₂! ⋯ λ_k!`，

`λ₁,…,λ_k` 为 `ξ` 各等价类（块）的大小。

本文件用 `Nat.factorial`：库的 import 闭包内**没有** `n !` 记号（见
`scripts/w10a_scratch.lean` 的探针），故一律写 `Nat.factorial`。 -/
noncomputable def partitionProb (n k : ℕ) (P : Part n) : ℝ :=
  (Nat.factorial (n - k) : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial (k - 1) : ℝ)
    / ((Nat.factorial n : ℝ) * (Nat.factorial (n - 1) : ℝ))
    * ∏ B ∈ P.parts, (Nat.factorial B.card : ℝ)

/-- `partitionProb` 中与 `P` **无关**的主导因子 `(n−k)!k!(k−1)!/(n!(n−1)!)`。 -/
noncomputable def partitionLead (n k : ℕ) : ℝ :=
  (Nat.factorial (n - k) : ℝ) * (Nat.factorial k : ℝ) * (Nat.factorial (k - 1) : ℝ)
    / ((Nat.factorial n : ℝ) * (Nat.factorial (n - 1) : ℝ))

lemma partitionProb_eq_lead (n k : ℕ) (P : Part n) :
    partitionProb n k P
      = partitionLead n k * ∏ B ∈ P.parts, (Nat.factorial B.card : ℝ) := rfl

/-- `partitionLead` 恒正（分子分母都是阶乘之积）。 -/
theorem partitionLead_pos (n k : ℕ) : 0 < partitionLead n k := by
  have h1 : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h2 : (0 : ℝ) < (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  have h3 : (0 : ℝ) < (Nat.factorial (n - k) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - k)
  have h4 : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h5 : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  rw [partitionLead, div_eq_mul_inv]
  exact mul_pos (mul_pos (mul_pos h3 h4) h5) (inv_pos.mpr (mul_pos h1 h2))

/-- `partitionProb` 恒正。 -/
theorem partitionProb_pos (n k : ℕ) (P : Part n) : 0 < partitionProb n k P := by
  rw [partitionProb_eq_lead]
  exact mul_pos (partitionLead_pos n k)
    (Finset.prod_pos fun B _ => by exact_mod_cast Nat.factorial_pos B.card)

/-- ★ **归一化的基底**（K82 第 **274–276 行** "it being clearly true for `k = n`"）。

`k = n` 时唯一的划分是 `⊥`（全单点，`Finpartition.mem_bot_iff`），且
`partitionProb n n ⊥ = 0!·n!·(n−1)!/(n!·(n−1)!) · ∏ 1! = 1`。 -/
theorem partitionProb_self_bot (n : ℕ) : partitionProb n n (⊥ : Part n) = 1 := by
  have hprod : (∏ B ∈ (⊥ : Part n).parts, (Nat.factorial B.card : ℝ)) = 1 := by
    refine Finset.prod_eq_one fun B hB => ?_
    obtain ⟨a, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    simp
  rw [partitionProb, hprod, mul_one, Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
    one_mul]
  exact div_self (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
    (by exact_mod_cast Nat.factorial_ne_zero (n - 1)))

/-- ★★ **劈块下的 `partitionProb` 比值**（**无除法**的乘法形式）。

`partitionProb n (k+1) (splitBlock P B A) · (n−k) · |B|!`
`= partitionProb n k P · (k+1)k · |A|! · |B\A|!`。

连同 `sum_powerset_factorial`，这就是层间一致性递归（缺口 1）的**全部代数内容**：
对 `A` 求和后左侧成为 `partitionProb n (k+1) · (n−k) · |B|!` 的 `|B|!·(|B|−1)` 倍，
即 `partitionProb n k P · (k+1)k · (n−k)`。 -/
theorem partitionProb_splitBlock_mul {k : ℕ} (P : Part n) (hk0 : 1 ≤ k) (hk : k < n)
    (B A : Finset (Fin n)) (hB : B ∈ P.parts) (hA : A ⊆ B)
    (hAne : A.Nonempty) (hAlt : A ≠ B) :
    partitionProb n (k + 1) (splitBlock P B A hB hA hAne hAlt)
        * ((n : ℝ) - k) * (Nat.factorial B.card : ℝ)
      = partitionProb n k P * (((k : ℝ) + 1) * k)
        * ((Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)) := by
  have hk_le : k ≤ n := le_of_lt hk
  have hfacA : (Nat.factorial (n - k) : ℝ)
      = (Nat.factorial (n - (k + 1)) : ℝ) * ((n : ℝ) - k) := by
    have h : n - k = (n - (k + 1)) + 1 := by omega
    rw [h, Nat.factorial_succ, Nat.cast_mul]
    have h1 : ((n - (k + 1) + 1 : ℕ) : ℝ) = (n : ℝ) - k := by
      rw [show n - (k + 1) + 1 = n - k from by omega, Nat.cast_sub hk_le]
    rw [h1]; ring
  have hfacB : (Nat.factorial (k + 1) : ℝ)
      = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfacC : (Nat.factorial k : ℝ) = (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (Nat.factorial (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have hlead : partitionLead n (k + 1) * ((n : ℝ) - k)
      = partitionLead n k * (((k : ℝ) + 1) * k) := by
    have hk1 : k + 1 - 1 = k := by omega
    rw [partitionLead, partitionLead, hk1, hfacA, hfacB, hfacC]
    field_simp
  have hprod := prod_factorial_splitBlock P B A hB hA hAne hAlt
  have key : (partitionLead n (k + 1) * ((n : ℝ) - k))
        * ((∏ B' ∈ (splitBlock P B A hB hA hAne hAlt).parts,
              (Nat.factorial B'.card : ℝ)) * (Nat.factorial B.card : ℝ))
      = (partitionLead n k * (((k : ℝ) + 1) * k))
        * ((∏ B' ∈ P.parts, (Nat.factorial B'.card : ℝ))
            * ((Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ))) := by
    rw [hlead, hprod]
  rw [partitionProb_eq_lead, partitionProb_eq_lead]
  calc (partitionLead n (k + 1)
          * ∏ B' ∈ (splitBlock P B A hB hA hAne hAlt).parts, (Nat.factorial B'.card : ℝ))
        * ((n : ℝ) - k) * (Nat.factorial B.card : ℝ)
      = (partitionLead n (k + 1) * ((n : ℝ) - k))
        * ((∏ B' ∈ (splitBlock P B A hB hA hAne hAlt).parts,
              (Nat.factorial B'.card : ℝ)) * (Nat.factorial B.card : ℝ)) := by ring
    _ = (partitionLead n k * (((k : ℝ) + 1) * k))
        * ((∏ B' ∈ P.parts, (Nat.factorial B'.card : ℝ))
            * ((Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ))) := key
    _ = (partitionLead n k * ∏ B' ∈ P.parts, (Nat.factorial B'.card : ℝ))
        * (((k : ℝ) + 1) * k)
        * ((Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)) := by ring

/-! ## (★) 单块分裂恒等式 -/

/-- ★ **`powersetCard` 层的分裂和**：`B` 的每个 `j`-元子集贡献 `j!·(|B|−j)!`，
合计恰为 `|B|!`（`Nat.choose_mul_factorial_mul_factorial`）。 -/
theorem sum_powersetCard_factorial (B : Finset (Fin n)) {j : ℕ} (hj : j ≤ B.card) :
    ∑ A ∈ B.powersetCard j,
        (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
      = (Nat.factorial B.card : ℝ) := by
  have hconst : ∀ A ∈ B.powersetCard j,
      (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
        = (Nat.factorial j : ℝ) * (Nat.factorial (B.card - j) : ℝ) := by
    intro A hA
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    nsmul_eq_mul]
  have h := Nat.choose_mul_factorial_mul_factorial hj
  have h' : ((B.card.choose j : ℕ) : ℝ)
        * ((Nat.factorial j : ℝ) * (Nat.factorial (B.card - j) : ℝ))
      = (Nat.factorial B.card : ℝ) := by
    rw [← h]; push_cast; ring
  rw [h']

/-- ★ **无限制的单块分裂恒等式**：`Σ_{A ⊆ B} |A|!·|B\A|! = (|B|+1)·|B|!`
（按 `powersetCard j`、`j = 0…|B|` 分组）。 -/
theorem sum_powerset_factorial_unrestricted (B : Finset (Fin n)) :
    ∑ A ∈ B.powerset, (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
      = ((B.card : ℝ) + 1) * (Nat.factorial B.card : ℝ) := by
  have hbij : (∑ A ∈ B.powerset,
        (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ))
      = ∑ j ∈ Finset.range (B.card + 1),
          ∑ A ∈ B.powersetCard j,
            (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_bij' (fun A _ => (⟨A.card, A⟩ : Σ _ : ℕ, Finset (Fin n)))
      (fun x _ => x.2) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      refine Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · exact Nat.lt_succ_of_le (Finset.card_le_card (Finset.mem_powerset.mp hA))
      · exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hA, rfl⟩
    · intro x hx
      exact Finset.mem_powerset.mpr
        (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).2).1
    · intro A _
      rfl
    · intro x hx
      exact Sigma.ext (Finset.mem_powersetCard.mp (Finset.mem_sigma.mp hx).2).2 (HEq.refl _)
    · intro A _
      rfl
  rw [hbij]
  have hinner : ∀ j ∈ Finset.range (B.card + 1),
      ∑ A ∈ B.powersetCard j,
          (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
        = (Nat.factorial B.card : ℝ) :=
    fun j hj => sum_powersetCard_factorial B (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one]

/-- ★★★ **(★) 单块分裂恒等式**（**有序**和：`A` 与 `B\A` 各计一次）：

> `Σ_{A ⊊ B, A ≠ ∅} |A|! · |B\A|! = |B|! · (|B| − 1)`  （`|B| ≥ 2`）

`A` 走遍 `B` 的**非空真**子集。由无限制版本减去 `A = ∅` 与 `A = B` 两个边界项得到，
两项各为 `|B|!`。

⚠️ 这是**有序**和：每个无序二分 `{A, B\A}` 在此被计**两次**（`|B| = 4` 时是 `72`，不是 `36`；
`W10_COALESCENT_SPEC.md` §1.7 的 (★) 里 `|B| = 4` 的数字 `36` 其实是**无序**和）。
递归中若要用无序和，须**乘 `1/2`**（规格 §1.7 已指出这一点）。 -/
theorem sum_powerset_factorial_of_nonempty (B : Finset (Fin n)) (hB : 1 ≤ B.card) :
    ∑ A ∈ B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B),
        (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
      = (Nat.factorial B.card : ℝ) * ((B.card : ℝ) - 1) := by
  have hBne : B ≠ ∅ := by rintro rfl; simp at hB
  have hdecomp : B.powerset
      = insert ∅ (insert B (B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B))) := by
    ext A
    simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hA
      by_cases h : A = ∅
      · exact Or.inl h
      · by_cases h2 : A = B
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hA, Finset.nonempty_iff_ne_empty.mpr h, h2⟩)
    · rintro (h | h | ⟨hAB, -, -⟩)
      · rw [h]; exact Finset.empty_subset B
      · rw [h]
      · exact hAB
  have hnotB : B ∉ B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B) := by
    rw [Finset.mem_filter]
    exact fun h => h.2.2 rfl
  have hnotE : ∅ ∉ insert B (B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B)) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hBne h.symm
    · rw [Finset.mem_filter] at h
      exact h.2.1.ne_empty rfl
  have hsum := sum_powerset_factorial_unrestricted B
  rw [hdecomp, Finset.sum_insert hnotE, Finset.sum_insert hnotB] at hsum
  have h0 : (Nat.factorial (∅ : Finset (Fin n)).card : ℝ)
      * (Nat.factorial (B \ ∅).card : ℝ) = (Nat.factorial B.card : ℝ) := by
    rw [Finset.card_empty, Nat.factorial_zero, Nat.cast_one, Finset.sdiff_empty, one_mul]
  have h1 : (Nat.factorial B.card : ℝ) * (Nat.factorial (B \ B).card : ℝ)
      = (Nat.factorial B.card : ℝ) := by
    rw [Finset.sdiff_self, Finset.card_empty, Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [h0, h1] at hsum
  linarith

/-- ★★★ **(★) 单块分裂恒等式**（规格 §1.5 里的**原始形状**，`|B| ≥ 2`；**有序**和）：

> `Σ_{A ⊊ B, A ≠ ∅} |A|! · |B\A|! = |B|! · (|B| − 1)`

是 `sum_powerset_factorial_of_nonempty`（只要求 `|B| ≥ 1`）的直接推论，单独保留此名字与
`2 ≤ B.card` 前提是为了与规格 §1.5 的陈述逐字对应。

⚠️ 这是**有序**和：每个无序二分 `{A, B\A}` 在此被计**两次**（`|B| = 4` 时是 `72`，不是 `36`；
`W10_COALESCENT_SPEC.md` §1.7 的 (★) 里 `|B| = 4` 的数字 `36` 其实是**无序**和）。 -/
theorem sum_powerset_factorial (B : Finset (Fin n)) (hB : 2 ≤ B.card) :
    ∑ A ∈ B.powerset.filter (fun A => A.Nonempty ∧ A ≠ B),
        (Nat.factorial A.card : ℝ) * (Nat.factorial (B \ A).card : ℝ)
      = (Nat.factorial B.card : ℝ) * ((B.card : ℝ) - 1) :=
  sum_powerset_factorial_of_nonempty B (le_trans (by norm_num) hB)

/-- `MergeInto Q P`：`P` 由 `Q` **合并某两个块**得到（(2.1) 的「下降一步」关系）。 -/
def MergeInto {n : ℕ} (Q P : Part n) : Prop :=
  ∃ (B1 B2 : Finset (Fin n)) (h1 : B1 ∈ Q.parts) (h2 : B2 ∈ Q.parts) (hne : B1 ≠ B2),
    mergePart Q B1 B2 h1 h2 hne = P

/-! ## 层间一致性（规格 §1.5）：有序「合并 ↔ 劈块」双射

本节按协调侧同意的路线收口验收②：两边都用**有序**指标（合并侧 = 有序块对，
劈块侧 = 有序二分 `(A, X\A)`），故全程**无 `1/2` 因子**，`sum_powerset_factorial`（有序和）
正好是劈块侧的求和值。 -/

section Consistency

open Classical

/-- `s` 的**非对角有序对**：`(B1,B2)` 且 `B1 ≠ B2`（即「有序块对」）。 -/
def offDiag (s : Finset (Finset (Fin n))) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (s ×ˢ s).filter (fun p => p.1 ≠ p.2)

lemma mem_offDiag {s : Finset (Finset (Fin n))} {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ offDiag s ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 := by
  simp only [offDiag, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- 有序块对的个数：`|s|·(|s| − 1)`（每个无序块对恰被计两次）。 -/
theorem card_offDiag (s : Finset (Finset (Fin n))) :
    (offDiag s).card = s.card * (s.card - 1) := by
  have hunion : offDiag s ∪ (s ×ˢ s).filter (fun p => ¬p.1 ≠ p.2) = s ×ˢ s := by
    ext p
    simp only [offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    tauto
  have hdisj : Disjoint (offDiag s) ((s ×ˢ s).filter (fun p => ¬p.1 ≠ p.2)) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [offDiag, Finset.mem_filter] at hp1 hp2
    exact hp2.2 hp1.2
  have hsplit : (offDiag s).card + ((s ×ˢ s).filter (fun p => ¬p.1 ≠ p.2)).card
      = (s ×ˢ s).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hdiag : ((s ×ˢ s).filter (fun p => ¬p.1 ≠ p.2)).card = s.card := by
    have himg : ((s ×ˢ s).filter (fun p => ¬p.1 ≠ p.2)) = s.image (fun B => (B, B)) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        rw [not_not] at h3
        exact ⟨p.1, h1, Prod.ext rfl h3⟩
      · rintro ⟨B, hB, hBeq⟩
        have hB1 : B = p.1 := congrArg Prod.fst hBeq
        have hB2 : B = p.2 := congrArg Prod.snd hBeq
        exact ⟨⟨by rw [← hB1]; exact hB, by rw [← hB2]; exact hB⟩,
          by rw [← hB2, ← hB1]; exact fun h => h rfl⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  rw [hdiag, Finset.card_product] at hsplit
  have h2 : s.card * (s.card - 1) = s.card * s.card - s.card := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

/-- 把一对块 `(B1,B2)` 合起来（当它们是 `Q` 的两个不同块时；否则返回 `Q`）。 -/
def mergeOf (x : Part n × (Finset (Fin n) × Finset (Fin n))) : Part n :=
  if h : x.2.1 ∈ x.1.parts ∧ x.2.2 ∈ x.1.parts ∧ x.2.1 ≠ x.2.2 then
    mergePart x.1 x.2.1 x.2.2 h.1 h.2.1 h.2.2
  else x.1

lemma mergeOf_eq (Q : Part n) (B1 B2 : Finset (Fin n)) (h1 : B1 ∈ Q.parts)
    (h2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    mergeOf (Q, (B1, B2)) = mergePart Q B1 B2 h1 h2 hne := by
  rw [mergeOf, dite_eq_left ⟨h1, h2, hne⟩]

/-- 把 `P` 的块 `X` 按 `A` 劈开（当 `X ∈ P.parts` 且 `A` 是 `X` 的非空真子集时；否则返回 `P`）。 -/
def splitOf (P : Part n) (X A : Finset (Fin n)) : Part n :=
  if h : X ∈ P.parts ∧ A ⊆ X ∧ A.Nonempty ∧ A ≠ X then
    splitBlock P X A h.1 h.2.1 h.2.2.1 h.2.2.2
  else P

lemma splitOf_eq (P : Part n) (X A : Finset (Fin n)) (hX : X ∈ P.parts) (hA : A ⊆ X)
    (hAne : A.Nonempty) (hAlt : A ≠ X) :
    splitOf P X A = splitBlock P X A hX hA hAne hAlt := by
  rw [splitOf, dite_eq_left ⟨hX, hA, hAne, hAlt⟩]

lemma mem_splitBlock_parts_left (P : Part n) (X A : Finset (Fin n)) (hX : X ∈ P.parts)
    (hA : A ⊆ X) (hAne : A.Nonempty) (hAlt : A ≠ X) :
    A ∈ (splitBlock P X A hX hA hAne hAlt).parts := by
  rw [splitBlock_parts, mem_splitBlockParts]; exact Or.inl rfl

lemma mem_splitBlock_parts_right (P : Part n) (X A : Finset (Fin n)) (hX : X ∈ P.parts)
    (hA : A ⊆ X) (hAne : A.Nonempty) (hAlt : A ≠ X) :
    X \ A ∈ (splitBlock P X A hX hA hAne hAlt).parts := by
  rw [splitBlock_parts, mem_splitBlockParts]; exact Or.inr (Or.inl rfl)

/-- 不交时 `(B1 ∪ B2) \ B1 = B2`。 -/
lemma union_sdiff_eq_right {B1 B2 : Finset (Fin n)} (hd : Disjoint B1 B2) :
    (B1 ∪ B2) \ B1 = B2 := by
  ext x
  rw [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hx, hx1⟩
    rcases hx with h | h
    · exact absurd h hx1
    · exact h
  · intro hx
    exact ⟨Or.inr hx, fun hx1 => Finset.disjoint_left.mp hd hx1 hx⟩

/-- 不交且 `B2` 非空时 `B1 ≠ B1 ∪ B2`。 -/
lemma ne_union_right {B1 B2 : Finset (Fin n)} (hd : Disjoint B1 B2) (h2 : B2.Nonempty) :
    B1 ≠ B1 ∪ B2 := by
  intro h
  obtain ⟨b, hb⟩ := h2
  have hb1 : b ∈ B1 := by rw [h]; exact Finset.mem_union.mpr (Or.inr hb)
  exact (Finset.disjoint_left.mp hd hb1) hb

/-- ★ **双射的「劈块 → 合并」方向**：先合并 `B1,B2` 再按 `(B1∪B2, B1)` 劈开，回到 `Q`。 -/
lemma splitBlock_mergePart (Q : Part n) (B1 B2 : Finset (Fin n)) (h1 : B1 ∈ Q.parts)
    (h2 : B2 ∈ Q.parts) (hne : B1 ≠ B2)
    (hX : B1 ∪ B2 ∈ (mergePart Q B1 B2 h1 h2 hne).parts) (hne' : B1 ≠ B1 ∪ B2) :
    splitBlock (mergePart Q B1 B2 h1 h2 hne) (B1 ∪ B2) B1 hX Finset.subset_union_left
      (Q.nonempty_of_mem_parts h1) hne' = Q := by
  have hd : Disjoint B1 B2 := Q.disjoint h1 h2 hne
  have hXnot : B1 ∪ B2 ∉ (Q.parts.erase B1).erase B2 := fun h =>
    ne_union_of_mem_parts h1 h2 hne (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hB2' : B2 ∈ Q.parts.erase B1 := Finset.mem_erase.mpr ⟨Ne.symm hne, h2⟩
  refine Finpartition.ext ?_
  rw [splitBlock_parts, splitBlockParts, mergePart_parts, mergeBlock,
    union_sdiff_eq_right hd, Finset.erase_insert hXnot, Finset.insert_erase hB2',
    Finset.insert_erase h1]

/-- ★ **双射的「合并 → 劈块」方向**：先按 `(X,A)` 劈开再合并 `A, X\A`，回到 `P`。 -/
lemma mergePart_splitBlock (P : Part n) (X A : Finset (Fin n)) (hX : X ∈ P.parts)
    (hA : A ⊆ X) (hAne : A.Nonempty) (hAlt : A ≠ X)
    (hA' : A ∈ (splitBlock P X A hX hA hAne hAlt).parts)
    (hXA' : X \ A ∈ (splitBlock P X A hX hA hAne hAlt).parts) :
    mergePart (splitBlock P X A hX hA hAne hAlt) A (X \ A) hA' hXA'
      (ne_sdiff_of_subset hAne) = P := by
  have hAnP := notMem_parts_of_ssubset hX hA hAne hAlt
  have hBnP := notMem_parts_sdiff hX hA hAne hAlt
  have hAnI : A ∉ insert (X \ A) (P.parts.erase X) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact ne_sdiff_of_subset hAne h
    · exact hAnP (Finset.mem_of_mem_erase h)
  have hBnI : X \ A ∉ P.parts.erase X := fun h => hBnP (Finset.mem_of_mem_erase h)
  refine Finpartition.ext ?_
  rw [mergePart_parts, mergeBlock, splitBlock_parts, splitBlockParts,
    Finset.union_sdiff_of_subset hA, Finset.erase_insert hAnI, Finset.erase_insert hBnI,
    Finset.insert_erase hX]

/-- 固定 `P` 的**劈块指标**：`P` 的一张块 `X` 与其一个非空真子集 `A`（有序二分 `(A, X\A)`）。 -/
def splitIdx (P : Part n) : Finset (Σ _ : Finset (Fin n), Finset (Fin n)) :=
  P.parts.sigma (fun X => X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X))

lemma mem_splitIdx {P : Part n} {y : Σ _ : Finset (Fin n), Finset (Fin n)} :
    y ∈ splitIdx P ↔ y.1 ∈ P.parts ∧ y.2 ∈ y.1.powerset.filter
      (fun A => A.Nonempty ∧ A ≠ y.1) := by
  simp only [splitIdx, Finset.mem_sigma]

/-- 固定 `P`、层 `k` 的**合并指标**：一个 `(k+1)`-块的 `Q` 与它的一个有序块对，
其合并结果恰是 `P`。 -/
def mergeIdx (P : Part n) (k : ℕ) :
    Finset (Σ _ : Part n, Finset (Fin n) × Finset (Fin n)) :=
  (((Finset.univ : Finset (Part n)).filter (fun Q => Q.parts.card = k + 1)).sigma
    (fun Q => offDiag Q.parts)).filter (fun x => mergeOf (x.1, x.2) = P)

lemma mem_mergeIdx {P : Part n} {k : ℕ}
    {x : Σ _ : Part n, Finset (Fin n) × Finset (Fin n)} :
    x ∈ mergeIdx P k ↔ x.1.parts.card = k + 1 ∧ x.2 ∈ offDiag x.1.parts
      ∧ mergeOf (x.1, x.2) = P := by
  simp only [mergeIdx, Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
    and_assoc]

/-- 劈块侧的单个和项（把 `partitionProb (splitBlock …)` 写成**无依赖**的显式函数，
以便放进 `Finset.sum_congr`）。 -/
noncomputable def splitRatioWeight (n k : ℕ) (P : Part n) (X A : Finset (Fin n)) : ℝ :=
  partitionProb n k P * (((k : ℝ) + 1) * k)
    * ((Nat.factorial A.card : ℝ) * (Nat.factorial (X \ A).card : ℝ))
    / (((n : ℝ) - k) * (Nat.factorial X.card : ℝ))

/-- ★★ **层间一致性的代数核**（嵌套求和形式）：固定 `P`（`|P| = k < n`），
对它所有块的所有有序二分求和：

`Σ_{X ∈ P.parts} Σ_{A ⊊ X, A ≠ ∅} partitionProb n (k+1) (splitBlock P X A) = (k+1)k · partitionProb n k P`。

（`partitionProb_splitBlock_mul` 逐项给比值，`sum_powerset_factorial_of_nonempty` 给单块的分裂和，
`Finpartition.sum_card_parts` 给 `Σ_X (|X| − 1) = n − k`；三者相乘后 `(n−k)` 相消。） -/
theorem splitSum_nested (n k : ℕ) (P : Part n) (hP : P.parts.card = k) (hk0 : 1 ≤ k)
    (hk : k < n) :
    ∑ X ∈ P.parts, ∑ A ∈ X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X),
        partitionProb n (k + 1) (splitOf P X A)
      = ((k : ℝ) + 1) * k * partitionProb n k P := by
  have hc : ((n : ℝ) - k) ≠ 0 := by
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hk
    linarith
  have hinner : ∀ X ∈ P.parts,
      ∑ A ∈ X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X),
          partitionProb n (k + 1) (splitOf P X A)
        = partitionProb n k P * (((k : ℝ) + 1) * k) * ((X.card : ℝ) - 1)
          / ((n : ℝ) - k) := by
    intro X hX
    have hXfac : (Nat.factorial X.card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero X.card
    have hXpos : 1 ≤ X.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hX)
    have hstep : (∑ A ∈ X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X),
            partitionProb n (k + 1) (splitOf P X A))
        = ∑ A ∈ X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X),
            splitRatioWeight n k P X A :=
      Finset.sum_congr rfl (fun A hA => by
        rw [splitOf, dite_eq_left ⟨hX, Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1,
          (Finset.mem_filter.mp hA).2.1, (Finset.mem_filter.mp hA).2.2⟩, splitRatioWeight]
        have hmul := partitionProb_splitBlock_mul (k := k) P hk0 hk X A hX
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
          (Finset.mem_filter.mp hA).2.1 (Finset.mem_filter.mp hA).2.2
        field_simp
        linarith [hmul])
    rw [hstep]
    simp only [splitRatioWeight]
    rw [← Finset.sum_div, ← Finset.mul_sum,
      sum_powerset_factorial_of_nonempty X hXpos]
    field_simp
  rw [Finset.sum_congr rfl hinner]
  have hsum : ∑ X ∈ P.parts, ((X.card : ℝ) - 1) = (n : ℝ) - k := by
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ X ∈ P.parts, (X.card : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_sum, P.sum_card_parts]
      simp
    have h2 : ∑ _X ∈ P.parts, (1 : ℝ) = (k : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, hP]
    rw [h1, h2]
  rw [← Finset.sum_div, ← Finset.mul_sum, hsum]
  field_simp

/-- ★★ **层间一致性的代数核**（σ-指标形式，即双射的一侧）：同 `splitSum_nested`，
但求和指标写成 `splitIdx P = Σ_{X ∈ P.parts} {A ⊆ X : A ≠ ∅, A ≠ X}`。 -/
theorem splitSum_eq (n k : ℕ) (P : Part n) (hP : P.parts.card = k) (hk0 : 1 ≤ k)
    (hk : k < n) :
    ∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2)
      = ((k : ℝ) + 1) * k * partitionProb n k P := by
  rw [splitIdx, ← Finset.sum_sigma' P.parts
    (fun X => X.powerset.filter (fun A => A.Nonempty ∧ A ≠ X))
    (fun X A => partitionProb n (k + 1) (splitOf P X A))]
  exact splitSum_nested n k P hP hk0 hk

/-- `k`-块层的**总权重** `S_k = Σ_{|P|=k} partitionProb n k P`（规格 §1.4 的归一化对象）。 -/
noncomputable def stateSum (n k : ℕ) : ℝ :=
  ∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)), partitionProb n k P

/-- 合并后再按 `(B1∪B2, B1)` 劈开，回到 `Q`（双射「合并 → 劈块」方向的单块形式）。 -/
lemma splitOf_mergePart (Q : Part n) (B1 B2 : Finset (Fin n)) (h1 : B1 ∈ Q.parts)
    (h2 : B2 ∈ Q.parts) (hne : B1 ≠ B2) :
    splitOf (mergePart Q B1 B2 h1 h2 hne) (B1 ∪ B2) B1 = Q := by
  have hd : Disjoint B1 B2 := Q.disjoint h1 h2 hne
  have h2ne : B2.Nonempty := Q.nonempty_of_mem_parts h2
  have h1ne : B1.Nonempty := Q.nonempty_of_mem_parts h1
  have hX : B1 ∪ B2 ∈ (mergePart Q B1 B2 h1 h2 hne).parts := by
    rw [mergePart_parts, mergeBlock]; exact Finset.mem_insert.mpr (Or.inl rfl)
  have hne' : B1 ≠ B1 ∪ B2 := ne_union_right hd h2ne
  rw [splitOf_eq _ _ _ hX Finset.subset_union_left h1ne hne']
  exact splitBlock_mergePart Q B1 B2 h1 h2 hne hX hne'

/-- ★★★ **层间一致性的索引双射**（规格 §1.5 的核心）：固定 `P`（`|P| = k`），
「`(k+1)`-块的 `Q` + 其一个有序块对，合并结果 `= P`」与「`P` 的一张块 `X` + 其一个
非空真子集 `A`（有序二分 `(A, X\A)`）」一一对应：

* 正向 `(Q, (B1,B2)) ↦ (P, (B1∪B2, B1))`；
* 逆向 `(P, (X,A)) ↦ (splitBlock P X A, (A, X\A))`。

（两边都是**有序**指标，故无 `1/2` 因子；`splitBlock_mergePart` / `mergePart_splitBlock`
给出两个方向的往返恒等。） -/
theorem sum_mergeIdx_eq_splitIdx (n k : ℕ) (P : Part n) (hP : P.parts.card = k) :
    ∑ x ∈ mergeIdx P k, partitionProb n (k + 1) x.1
      = ∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2) := by
  refine Finset.sum_bij'
    (fun x _ => (⟨x.2.1 ∪ x.2.2, x.2.1⟩ : Σ _ : Finset (Fin n), Finset (Fin n)))
    (fun y _ => (⟨splitOf P y.1 y.2, (y.2, y.1 \ y.2)⟩ :
      Σ _ : Part n, Finset (Fin n) × Finset (Fin n)))
    ?_ ?_ ?_ ?_ ?_
  · -- hi：正向落在 splitIdx 里
    intro x hx
    obtain ⟨hcard, hoff, hmerge⟩ := mem_mergeIdx.mp hx
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hoff
    have hm := mergeOf_eq x.1 x.2.1 x.2.2 h1 h2 hne
    have hPX : P = mergePart x.1 x.2.1 x.2.2 h1 h2 hne := by rw [← hmerge, hm]
    have hd : Disjoint x.2.1 x.2.2 := x.1.disjoint h1 h2 hne
    refine mem_splitIdx.mpr ⟨?_, ?_⟩
    · rw [hPX, mergePart_parts, mergeBlock]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.subset_union_left,
        x.1.nonempty_of_mem_parts h1, ne_union_right hd (x.1.nonempty_of_mem_parts h2)⟩
  · -- hj：逆向落在 mergeIdx 里
    intro y hy
    obtain ⟨hX, hA⟩ := mem_splitIdx.mp hy
    obtain ⟨hAmem, hAne, hAX⟩ := Finset.mem_filter.mp hA
    have hAsub : y.2 ⊆ y.1 := Finset.mem_powerset.mp hAmem
    have hsplit : splitOf P y.1 y.2 = splitBlock P y.1 y.2 hX hAsub hAne hAX :=
      splitOf_eq P y.1 y.2 hX hAsub hAne hAX
    have hA' := mem_splitBlock_parts_left P y.1 y.2 hX hAsub hAne hAX
    have hXA' := mem_splitBlock_parts_right P y.1 y.2 hX hAsub hAne hAX
    refine mem_mergeIdx.mpr ⟨?_, ?_, ?_⟩
    · rw [hsplit, card_splitBlock, hP]
    · rw [hsplit]
      exact mem_offDiag.mpr ⟨hA', hXA', ne_sdiff_of_subset hAne⟩
    · rw [hsplit]
      show mergeOf (splitBlock P y.1 y.2 hX hAsub hAne hAX, (y.2, y.1 \ y.2)) = P
      rw [mergeOf_eq _ _ _ hA' hXA' (ne_sdiff_of_subset hAne)]
      exact mergePart_splitBlock P y.1 y.2 hX hAsub hAne hAX hA' hXA'
  · -- hji：逆向 ∘ 正向 = id
    intro x hx
    obtain ⟨hcard, hoff, hmerge⟩ := mem_mergeIdx.mp hx
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hoff
    have hm := mergeOf_eq x.1 x.2.1 x.2.2 h1 h2 hne
    have hd : Disjoint x.2.1 x.2.2 := x.1.disjoint h1 h2 hne
    have hsplit : splitOf P (x.2.1 ∪ x.2.2) x.2.1 = x.1 := by
      rw [← hmerge, hm]
      exact splitOf_mergePart x.1 x.2.1 x.2.2 h1 h2 hne
    refine Sigma.ext hsplit ?_
    exact heq_of_eq (Prod.ext rfl (union_sdiff_eq_right hd))
  · -- hij：正向 ∘ 逆向 = id
    intro y hy
    obtain ⟨hX, hA⟩ := mem_splitIdx.mp hy
    obtain ⟨hAmem, _, _⟩ := Finset.mem_filter.mp hA
    refine Sigma.ext ?_ (heq_of_eq rfl)
    exact Finset.union_sdiff_of_subset (Finset.mem_powerset.mp hAmem)
  · -- hf：两侧和项一致
    intro x hx
    obtain ⟨hcard, hoff, hmerge⟩ := mem_mergeIdx.mp hx
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.mp hoff
    have hm := mergeOf_eq x.1 x.2.1 x.2.2 h1 h2 hne
    have hsplit : splitOf P (x.2.1 ∪ x.2.2) x.2.1 = x.1 := by
      rw [← hmerge, hm]
      exact splitOf_mergePart x.1 x.2.1 x.2.2 h1 h2 hne
    rw [hsplit]

/-- 合并侧的全指标集（不分 `P`）：`(k+1)`-块的 `Q` 与它的一个有序块对。 -/
def mergeAll (k : ℕ) : Finset (Σ _ : Part n, Finset (Fin n) × Finset (Fin n)) :=
  ((Finset.univ : Finset (Part n)).filter (fun Q => Q.parts.card = k + 1)).sigma
    (fun Q => offDiag Q.parts)

lemma mergeIdx_eq_filter (P : Part n) (k : ℕ) :
    mergeIdx P k = (mergeAll k).filter (fun x => mergeOf (x.1, x.2) = P) := rfl

/-- 合并侧全指标集上的求和：每个 `(k+1)`-块状态贡献 `(k+1)k` 份自己的权重。 -/
theorem sum_mergeAll (n k : ℕ) :
    ∑ x ∈ mergeAll k, partitionProb n (k + 1) x.1
      = ((k : ℝ) + 1) * k * stateSum n (k + 1) := by
  rw [mergeAll, ← Finset.sum_sigma'
    (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1))
    (fun Q => offDiag Q.parts) (fun Q _ => partitionProb n (k + 1) Q)]
  have hinner : ∀ Q ∈ (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1)),
      (∑ _p ∈ offDiag Q.parts, partitionProb n (k + 1) Q)
        = ((k : ℝ) + 1) * k * partitionProb n (k + 1) Q := by
    intro Q hQ
    have hQc : Q.parts.card = k + 1 := (Finset.mem_filter.mp hQ).2
    have hk1 : k + 1 - 1 = k := by omega
    rw [Finset.sum_const, card_offDiag, hQc, hk1, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  rfl

/-- 劈块侧全指标集上的求和（用 `splitSum_eq` 逐状态求值）。 -/
theorem sum_splitIdx_stateSum (n k : ℕ) (hk0 : 1 ≤ k) (hk : k < n) :
    (∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
        ∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2))
      = ((k : ℝ) + 1) * k * stateSum n k := by
  have hinner : ∀ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
      (∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2))
        = ((k : ℝ) + 1) * k * partitionProb n k P :=
    fun P hP => splitSum_eq n k P (Finset.mem_filter.mp hP).2 hk0 hk
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  rfl

/-- ★★★ **双侧同一**：劈块侧全求和 = 合并侧全求和（由 `sum_mergeIdx_eq_splitIdx` 逐 `P` 用，
再用 `Finset.sum_comm` 交换两个 `Finset` 求和）。 -/
theorem sum_splitIdx_eq_sum_mergeAll (n k : ℕ) (hk0 : 1 ≤ k) (_hk : k < n) :
    (∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
        ∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2))
      = ∑ x ∈ mergeAll k, partitionProb n (k + 1) x.1 := by
  have h1 : (∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
        ∑ y ∈ splitIdx P, partitionProb n (k + 1) (splitOf P y.1 y.2))
      = ∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
          ∑ x ∈ mergeIdx P k, partitionProb n (k + 1) x.1 :=
    Finset.sum_congr rfl fun P hP =>
      (sum_mergeIdx_eq_splitIdx n k P (Finset.mem_filter.mp hP).2).symm
  rw [h1]
  have h2 : (∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
        ∑ x ∈ mergeIdx P k, partitionProb n (k + 1) x.1)
      = ∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
          ∑ x ∈ mergeAll k,
            (if mergeOf (x.1, x.2) = P then partitionProb n (k + 1) x.1 else 0) :=
    Finset.sum_congr rfl fun P _ => by rw [mergeIdx_eq_filter, Finset.sum_filter]
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_ite_eq]
  obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
  have hxcard : x.1.parts.card = k + 1 := (Finset.mem_filter.mp hx1).2
  obtain ⟨ho1, ho2, hone⟩ := mem_offDiag.mp hx2
  have hmem : mergeOf (x.1, x.2) ∈
      (Finset.univ.filter (fun P : Part n => P.parts.card = k)) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mergeOf_eq x.1 x.2.1 x.2.2 ho1 ho2 hone, card_mergePart, hxcard]
    omega
  rw [ite_eq_left hmem]

/-- ★★★ **层间一致性的递归步**（规格 §1.4 的倒向归纳步）：`S_k = S_{k+1}`。 -/
theorem stateSum_eq_succ (n k : ℕ) (hk0 : 1 ≤ k) (hk : k < n) :
    stateSum n k = stateSum n (k + 1) := by
  have h1 := sum_splitIdx_eq_sum_mergeAll n k hk0 hk
  have h2 := sum_splitIdx_stateSum n k hk0 hk
  have h3 := sum_mergeAll n k
  have hkey : ((k : ℝ) + 1) * k * stateSum n k
      = ((k : ℝ) + 1) * k * stateSum n (k + 1) := by
    rw [← h2, h1, h3]
  have hkne : ((k : ℝ) + 1) * k ≠ 0 := by
    have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
    positivity
  exact mul_left_cancel₀ hkne hkey

/-- 块数达最大 `n` 的划分只能是 `⊥`（全单点）：`Σ_B |B| = n = #parts` 且每块非空，
故每块大小恰为 `1`。 -/
theorem eq_bot_of_card_parts (P : Part n) (h : P.parts.card = n) : P = ⊥ := by
  have hle : ∀ B ∈ P.parts, (1 : ℕ) ≤ B.card :=
    fun B hB => Finset.card_pos.mpr (P.nonempty_of_mem_parts hB)
  have hsum : ∑ _B ∈ P.parts, (1 : ℕ) = ∑ B ∈ P.parts, B.card := by
    rw [Finset.sum_const, P.sum_card_parts, h, smul_eq_mul, mul_one]
    simp
  have hcard1 : ∀ B ∈ P.parts, B.card = 1 :=
    fun B hB => (((Finset.sum_eq_sum_iff_of_le hle).mp hsum) B hB).symm
  refine Finpartition.ext (Finset.Subset.antisymm ?_ ?_)
  · intro B hB
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hcard1 B hB)
    exact Finpartition.mem_bot_iff.mpr ⟨a, Finset.mem_univ a, rfl⟩
  · intro B hB
    obtain ⟨a, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    obtain ⟨t, ht, hat⟩ := P.exists_mem (Finset.mem_univ a)
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (hcard1 t ht)
    have hba : b = a := (Finset.mem_singleton.mp hat).symm
    rw [hba] at ht
    exact ht

/-- ★ **`k = n` 层的总权重**：`k = n` 时唯一的划分是 `⊥`（`eq_bot_of_card_parts`），
故 `S_n = partitionProb n n ⊥ = 1`。 -/
theorem stateSum_self (n : ℕ) : stateSum n n = 1 := by
  have hfilt : (Finset.univ.filter (fun P : Part n => P.parts.card = n)) = {⊥} := by
    ext P
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hP⟩
      exact eq_bot_of_card_parts P hP
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp⟩
  rw [stateSum, hfilt, Finset.sum_singleton, partitionProb_self_bot]

/-- ★★★ **验收① 归一化**（规格 §1.4）：`Σ_{|P|=k} partitionProb n k P = 1`
（`1 ≤ k ≤ n`）。由倒向归纳：`S_n = 1` 与 `S_k = S_{k+1}`（K82 第 **274–276** 行）。 -/
theorem stateSum_eq_one (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) : stateSum n k = 1 := by
  have hmain : ∀ j, j + 1 ≤ n → stateSum n (n - j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using stateSum_self n
    | succ j ih =>
      intro hj
      have hj' : j + 1 ≤ n := by omega
      have hlt : n - (j + 1) < n := by omega
      have hge : 1 ≤ n - (j + 1) := by omega
      rw [stateSum_eq_succ n (n - (j + 1)) hge hlt]
      have hsucc : n - (j + 1) + 1 = n - j := by omega
      rw [hsucc]
      exact ih hj'
  have := hmain (n - k) (by omega)
  rwa [Nat.sub_sub_self hkn] at this

/-- ★★★ **验收①（规格的原始形状）**：`Σ_{|P|=k} partitionProb n k P = 1`。 -/
theorem partitionProb_sum_eq_one (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    ∑ P ∈ (Finset.univ.filter (fun P : Part n => P.parts.card = k)),
        partitionProb n k P = 1 :=
  stateSum_eq_one n k hk0 hkn

/-- `Q` 的**有序块对中合并结果恰为 `P`** 的那些对。 -/
def pairSet (Q P : Part n) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (offDiag Q.parts).filter (fun p => mergeOf (Q, p) = P)

lemma mem_pairSet {Q P : Part n} {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ pairSet Q P ↔ p ∈ offDiag Q.parts ∧ mergeOf (Q, p) = P := by
  simp only [pairSet, Finset.mem_filter]

/-- `2 · C(m,2) = m(m−1)`（在 `ℝ` 里证，避免 `Nat` 截断减法；也避免引入闭包外的
`Nat.cast_choose_two`）。 -/
lemma two_mul_choose_two_cast (m : ℕ) :
    ((m.choose 2 : ℕ) : ℝ) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ' m 1, Nat.choose_one_right, Nat.cast_add, add_mul, ih]
    push_cast
    ring

/-- ★ **(2.1) 有限核的计数形式**：使 `Q` 合并到 `P` 的**有序**块对恰有 `2` 个
（`(B1,B2)` 与 `(B2,B1)`），当且仅当 `MergeInto Q P`。 -/
theorem card_pairSet {Q P : Part n} :
    (pairSet Q P).card = if MergeInto Q P then 2 else 0 := by
  by_cases hM : MergeInto Q P
  · have hM' : MergeInto Q P := hM
    obtain ⟨B1, B2, h1, h2, hne, hmerge⟩ := hM'
    have hrev : B2 ≠ B1 := Ne.symm hne
    have hp0 : (B1, B2) ∈ pairSet Q P :=
      mem_pairSet.mpr ⟨mem_offDiag.mpr ⟨h1, h2, hne⟩,
        by rw [mergeOf_eq Q B1 B2 h1 h2 hne]; exact hmerge⟩
    have hpair : pairSet Q P = {(B1, B2), (B2, B1)} := by
      ext p
      rw [mem_pairSet, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hoff, hme⟩
        obtain ⟨h3, h4, hne2⟩ := mem_offDiag.mp hoff
        have h34 : mergePart Q p.1 p.2 h3 h4 hne2 = P := by
          rw [← mergeOf_eq Q p.1 p.2 h3 h4 hne2]; exact hme
        have hset := merge_outcomes_injective Q h3 h4 h1 h2 hne2 hne
          (by rw [h34, hmerge])
        have hp1 : p.1 ∈ ({B1, B2} : Finset (Finset (Fin n))) := by
          rw [← hset]; exact Finset.mem_insert.mpr (Or.inl rfl)
        have hp2 : p.2 ∈ ({B1, B2} : Finset (Finset (Fin n))) := by
          rw [← hset]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
        rw [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
        rcases hp1 with h1' | h1' <;> rcases hp2 with h2' | h2'
        · exact absurd (h1'.trans h2'.symm) hne2
        · exact Or.inl (Prod.ext h1' h2')
        · exact Or.inr (Prod.ext h1' h2')
        · exact absurd (h1'.trans h2'.symm) hne2
      · rintro (h' | h')
        · rw [h']; exact mem_pairSet.mp hp0
        · rw [h']
          show (B2, B1) ∈ offDiag Q.parts ∧ mergeOf (Q, (B2, B1)) = P
          refine ⟨mem_offDiag.mpr ⟨h2, h1, hrev⟩, ?_⟩
          rw [mergeOf_eq Q B2 B1 h2 h1 hrev,
            mergePart_proof_irrel Q B2 B1 h2 h1 hrev (Ne.symm hne),
            ← mergePart_comm Q B1 B2 h1 h2 hne]
          exact hmerge
    have hne' : (B1, B2) ≠ (B2, B1) := fun hc => hne (congrArg Prod.fst hc)
    rw [hpair, Finset.card_pair hne', ite_eq_left hM]
  · have hemp : pairSet Q P = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨hoff, hme⟩ := mem_pairSet.mp hp
      obtain ⟨h3, h4, hne2⟩ := mem_offDiag.mp hoff
      exact hM ⟨p.1, p.2, h3, h4, hne2, by
        rw [← mergeOf_eq Q p.1 p.2 h3 h4 hne2]; exact hme⟩
    rw [hemp, Finset.card_empty, ite_eq_right hM]

/-- ★★★ **合并侧的 `MergeInto` 形式**：合并侧全求和 = `2 ×`（对上一层 `Q` 的 `MergeInto` 求和）。

（每个 `Q` 贡献 `2·pp(Q)`：`pp(Q)` 与块对无关，而「合并为 `P` 的有序块对」恰有 `2` 个。） -/
theorem sum_mergeIdx_eq_two_mul (n k : ℕ) (P : Part n) :
    ∑ x ∈ mergeIdx P k, partitionProb n (k + 1) x.1
      = 2 * ∑ Q ∈ (Finset.univ.filter
          (fun Q : Part n => Q.parts.card = k + 1 ∧ MergeInto Q P)),
          partitionProb n (k + 1) Q := by
  rw [mergeIdx_eq_filter, mergeAll, Finset.sum_filter,
    ← Finset.sum_sigma' (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1))
      (fun Q => offDiag Q.parts)
      (fun Q p => if mergeOf (Q, p) = P then partitionProb n (k + 1) Q else 0)]
  have hinner : ∀ Q ∈ (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1)),
      (∑ p ∈ offDiag Q.parts,
          (if mergeOf (Q, p) = P then partitionProb n (k + 1) Q else 0))
        = if MergeInto Q P then 2 * partitionProb n (k + 1) Q else 0 := by
    intro Q _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      show ((offDiag Q.parts).filter (fun p => mergeOf (Q, p) = P)) = pairSet Q P from rfl,
      card_pairSet]
    by_cases h : MergeInto Q P <;> simp [h]
  rw [Finset.sum_congr rfl hinner]
  have htwo : (∑ Q ∈ (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1)),
        (if MergeInto Q P then 2 * partitionProb n (k + 1) Q else 0))
      = 2 * ∑ Q ∈ (Finset.univ.filter (fun Q : Part n => Q.parts.card = k + 1)),
          (if MergeInto Q P then partitionProb n (k + 1) Q else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Q _ => by by_cases h : MergeInto Q P <;> simp [h]
  rw [htwo]
  congr 1
  rw [← Finset.filter_filter, ← Finset.sum_filter]

/-- ★★★ **规格 §1.5 的层间一致性递归**（K82 第 **274–276 行**倒向归纳的逐状态形式）：

`partitionProb n k P · C(k+1,2) = Σ_{Q : |Q| = k+1, MergeInto Q P} partitionProb n (k+1) Q`。

（`sum_mergeIdx_eq_splitIdx`（索引双射）+ `splitSum_eq`（代数核）给出
`2 · Σ_Q = (k+1)k · pp(P) = 2 · C(k+1,2) · pp(P)`，再约去 `2`。） -/
theorem partitionProb_merge_recursion (n k : ℕ) (hk0 : 1 ≤ k) (hk : k < n) (P : Part n)
    (hP : P.parts.card = k) :
    partitionProb n k P * (((k + 1).choose 2 : ℕ) : ℝ)
      = ∑ Q ∈ (Finset.univ.filter
          (fun Q : Part n => Q.parts.card = k + 1 ∧ MergeInto Q P)),
          partitionProb n (k + 1) Q := by
  have hchoose : (((k + 1).choose 2 : ℕ) : ℝ) * 2 = ((k : ℝ) + 1) * k := by
    have h := two_mul_choose_two_cast (k + 1)
    push_cast at h
    nlinarith [h]
  have hmain : 2 * (∑ Q ∈ (Finset.univ.filter
        (fun Q : Part n => Q.parts.card = k + 1 ∧ MergeInto Q P)),
        partitionProb n (k + 1) Q)
      = 2 * (partitionProb n k P * (((k + 1).choose 2 : ℕ) : ℝ)) := by
    rw [← sum_mergeIdx_eq_two_mul, sum_mergeIdx_eq_splitIdx n k P hP,
      splitSum_eq n k P hP hk0 hk, ← hchoose]
    ring
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hcancel := mul_left_cancel₀ h2 hmain
  rw [hcancel, mul_comm]

/-- ★★★ **规格 §1.5 的原始（除法）形状**：

`partitionProb n k P = Σ_{Q : |Q| = k+1, MergeInto Q P} partitionProb n (k+1) Q / C(k+1,2)`。 -/
theorem partitionProb_merge_recursion_div (n k : ℕ) (hk0 : 1 ≤ k) (hk : k < n)
    (P : Part n) (hP : P.parts.card = k) :
    partitionProb n k P
      = ∑ Q ∈ (Finset.univ.filter
          (fun Q : Part n => Q.parts.card = k + 1 ∧ MergeInto Q P)),
          partitionProb n (k + 1) Q / (((k + 1).choose 2 : ℕ) : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hne : (((k + 1).choose 2 : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have h := two_mul_choose_two_cast (k + 1)
    push_cast at h
    rw [h0, zero_mul] at h
    nlinarith [h, hkR]
  rw [← Finset.sum_div, ← partitionProb_merge_recursion n k hk0 hk P hP]
  field_simp

end Consistency

/-! ## 验收③：概率质量函数的 `ℝ` 值等价物

规格 §1.6 说「产出 `PMF`（**或等价物**）」。`Mathlib.Probability.*`（含 `PMF`）**不在**
本库 import 闭包内（实测 `#check @PMF.ofFinset` → `unknown identifier`，见
`scripts/w10a_scratch.lean`），而本批按规格 §1 **不引入**新 Mathlib import。
故这里给出**等价物**：`jumpWeight n k : PartK n k → ℝ`，连同它的两条定义性质 ——
非负性 `jumpWeight_nonneg` 与归一化 `jumpWeight_sum_eq_one`（这正是 `PMF` 的实质内容）。 -/

section JumpWeight

open Classical

/-- ★★ **跳链在 `k`-块层的概率质量函数**（`PMF` 的 `ℝ` 值等价物）：
`jumpWeight n k P = partitionProb n k P.1`，其中 `P : PartK n k` 即「恰有 `k` 个块的划分」。 -/
noncomputable def jumpWeight (n k : ℕ) (P : PartK n k) : ℝ := partitionProb n k P.1

/-- `jumpWeight` 非负（`PMF` 的定义性质之一）。 -/
theorem jumpWeight_nonneg (n k : ℕ) (P : PartK n k) : 0 ≤ jumpWeight n k P :=
  le_of_lt (partitionProb_pos n k P.1)

/-- ★★★ **`jumpWeight` 归一**：`Σ_{P : PartK n k} jumpWeight n k P = 1`
（`PMF` 的定义性质之二；即验收① 的归一化，见 `partitionProb_sum_eq_one`）。 -/
theorem jumpWeight_sum_eq_one (n k : ℕ) (hk0 : 1 ≤ k) (hkn : k ≤ n) :
    ∑ P : PartK n k, jumpWeight n k P = 1 := by
  simp only [jumpWeight]
  rw [← Finset.sum_subtype (p := fun P : Part n => P.parts.card = k)
    (Finset.univ.filter (fun P : Part n => P.parts.card = k))
    (fun P => by simp) (fun P => partitionProb n k P)]
  exact stateSum_eq_one n k hk0 hkn

end JumpWeight

end Phylo.Stat.KingmanJumpChain
