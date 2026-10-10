/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.ConsensusExtra
import Phylo.AdamsConsensus

/-!
# `Phylo.ConsensusGreedy` —— W11c / C3（R\* 共识）＋ C4（贪心共识）

> **本文件的性质**：C3 与 C4 的**精确定义不在手文献中**（见下 §0 逐篇核读），
> 故本文件**不发明定义**，而是
> (a) 把在手文献**唯一**有关的表述（ADR2016 的一句话转述）形式化为**带次序参数的骨架**；
> (b) 证明该骨架**能依据在手文献证**的**安全性质**与**关系定理**；
> (c) 把缺口落成显式 `def … : Prop`（`rStarConsensus_gap` / `greedyConsensus_gap`），
>     并以**可证的反例**（`greedyConsensus_gap_refuted`）说明「在位文献不足以定出贪心共识」。

## §0 核读结论（`references/md/`，行号 = 各 md 文件行号）

### C3「R\* 共识」：**在手文献完全没有**

* **全库 grep**：`references/md/`（82 篇）中字符串 `R*` **只出现 1 次** ——
  `Day1985_OptimalAlgorithmsComparingTrees.md:1229`。该处是伪代码里的**局部变量**：

  > `<L*,R*,N*,W*> := pop(S);` … `<L,R,N,W> := <min(L,L*), max(R,R*), N + N*, W + W*>;`

  这是 `NVERTEX` 例程的**栈元组**（左右端编号 `L`/`R` 与其增量），
  与「R\* 共识」**毫无关系**（同一行的 `N*`、`W*` 同理）。**不是** R\* 的定义。
* `HendySteelPennyHenderson1988`：全文涉及的是**对称差度量**与「树的家族」，
  `consensus` 一词仅出现在**泛泛讨论**中（`:459–478`「The decision on whether or not to use a
  consensus tree, and if so what form of consensus tree [8] …」、`:651–659`、`:832–838`），
  **未给出任何共识的精确算法定义**；`[8]`（`:933–935`）指向
  Margush & McMorris, *Consensus n-trees*, Bull. Math. Biol. 43 (1981) 239–244。
* `Day1985`：给出的是**严格共识**（`:19–20` 摘要、`:221–232` **定义**：
  `C(T₁,…,T_k)' = ⋂_{1≤i≤k} T_i'`）与 **`M_l`** 族（`:238–245`）；**无 R\***。
* `Adams1972`：给出的是 **Adams 共识**（簇的 LUB **乘积划分**递归定义，`:481–496`）
  与「全标签树」情形下的**祖先关系之交**（`:296–310`：*"the consensus C is merely the
  intersection of all the sets R"*）；**无 R\***。
* ⇒ **落地为缺口 `rStarConsensus_gap`（见 §6），不写任何 R\* 的猜测性定义。**
  缺的原始出处是 **Bryant, D. (2003), *A classification of consensus methods for
  phylogenetics*, DIMACS Series in Discrete Math. and Theor. Comp. Sci. 61:163–184**
  （DOI `10.1090/dimacs/061/12`）。该篇即
  `AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md:1279–1281` 的文献 `[9]` ——
  **本库 0 篇在手**（`references/md/` 无 Bryant 2003；仅 `BryantSteel1995`、
  `BryantMoulton2004` 两篇同名作者但内容无关）。

### C4「贪心共识」：在手文献**只有一句话转述，没有定义**

在手文献中 `greedy consensus` **仅出现于**（全库 grep）：

* `AllmanDegnanRhodes2016_NJst_StatisticalConsistency.md:779–781`（**唯一有内容的一处**）：

  > "For instance greedy consensus [9] accepts splits in order of decreasing frequency,
  >  if they are compatible with previously accepted splits."

  其 `[9]` = 上引 **Bryant 2003**（`:1279–1281`）。
* `AllmanDegnanRhodes2017_SplitProbabilitiesMSC.md:2168–2170`（转述应用，无定义）。
* `AllmanDegnanRhodes2013_STARGeneralizations.md:152–153`（仅类比，无定义）。

**缺失的那一条定义要素**：ADR2016 的转述给出「**过程**」而**未给出同频（tie）时的次序**。
频率相同的两个 split 谁先谁后**改变输出**（★B，§5 的 `Fin 4` 反例），
故该转述**不定义一个函数**。补齐它需要 Bryant 2003（`[9]`）—— **不在手**。

* `HendySteelPennyHenderson1988` / `Day1985` / `Adams1972` 三篇**均无** `greedy` 字样
  （逐篇 grep 均 0 命中）。
* ⇒ **落地为缺口 `greedyConsensus_gap`（§6）**，并给出**已证的反例**
  `greedyConsensus_gap_refuted`。

## §1 与在手文献的**关系定理**（本文件真正证出的部分）

* ★★★ `greedyRun_compatible`：`greedyRun`（**任意**次序）的输出**两两相容** ——
  「安全性质」；与 `pairwiseCompatible`（`Phylo/Split.lean:894`）同源；
* ★★★ `lSplits_greedyRun_eq`：**`2l > |ι|` 时贪心输出恰是 Day 的 `M_l`**，
  且**与次序无关**（任意候选次序、任意同频决胜都得到同一个 `M_l`）。
  这是依据 **Day 1985 的 `M_l`**（`:238–245`）＋**鸽笼原理**
  （`lSplits_compatible`，`Phylo/ConsensusExtra.lean:194`）能证的**关系**定理；
* ★★★ `strictSplits_greedyRun_eq`：严格共识同样是**任意贪心的不动点**
  —— 即 **Adams 1972 的「insensitive to the order」断言**（`:346–349`、`:651–658`）
  在 split 层的可证形态；
* ★★ `lSplits_perm` / `strictSplits_perm`：阈值型规则（严格 / `M_l` / 多数）
  **只依赖树族**（对索引重标号**不变**）；与贪心的**次序敏感**（★B）形成对照 ——
  这正是「为什么 R\* 那种新规则需要一篇新文献来定义」的结构性原因。
-/

open Phylo

universe u

/-! ## §2 相容性的**可计算**判定（`Split.Compatible` 无 `Decidable` 实例）

`Split.Compatible` 的定义是四个 `Finset.Disjoint` 的析取，本版 Mathlib **没有**
`Decidable (Split.Compatible s t)`（`Finset` 的 `DecidableEq` 走 `Quot.lift`，`decide` 展不开）。
故本文件自带一个 `Bool` 判定 `compatibleB`，并证它与 `Split.Compatible` **等价**。
它是 `greedyStep` 的守卫，也使 §5 的具体例子可用 `decide` 直接**算出**。 -/

/-- 两个 `Finset` **不交**（可计算 `Bool`）。 -/
def cDisjoint {α : Type*} [DecidableEq α] (A B : Finset α) : Bool :=
  decide ((A ∩ B).card = 0)

/-- `cDisjoint` 与 `Disjoint` 一致。 -/
theorem cDisjoint_eq {α : Type*} [DecidableEq α] (A B : Finset α) :
    cDisjoint A B = true ↔ Disjoint A B := by
  simp only [cDisjoint, decide_eq_true_eq, Finset.card_eq_zero,
    Finset.disjoint_iff_inter_eq_empty]

/-- **相容性的可计算判定**：四个交中**至少一个为空**（`Split.Compatible` 的 `Bool` 版）。 -/
def compatibleB {α : Type*} [Fintype α] [DecidableEq α] (s t : Split α) : Bool :=
  cDisjoint s.sideA t.sideA || cDisjoint s.sideA t.sideB ||
    cDisjoint s.sideB t.sideA || cDisjoint s.sideB t.sideB

/-- ★★ `compatibleB` **精确**判定 `Split.Compatible`（定义层的桥）。 -/
theorem compatibleB_eq {α : Type*} [Fintype α] [DecidableEq α] (s t : Split α) :
    compatibleB s t = true ↔ Split.Compatible s t := by
  simp only [compatibleB, Bool.or_eq_true, cDisjoint_eq, Split.Compatible]
  tauto

/-! ## §3 贪心骨架（在手文献 ADR2016 `:779–781` 的「过程」）

**声明**：`greedyRun L` **不是** Bryant 的贪心共识（那需要 §6 的缺口），
它只是「按给定次序 `L` 逐个接受**与已接受者相容**的 split」这一**过程**的形式化。
`L` 就是文献里「in order of decreasing frequency」给出的候选序列 ——
**同频时 `L` 取哪一支，文献没有规定**（★B）。 -/

/-- **贪心接受一步**：若 `s` 与已接受的 `acc` 中每个 split 都相容，则接受 `s`。 -/
def greedyStep {α : Type*} [Fintype α] [DecidableEq α]
    (acc : List (Split α)) (s : Split α) : List (Split α) :=
  if _h : acc.all (compatibleB s) = true then s :: acc else acc

/-- 守卫成立时的展开式。 -/
theorem greedyStep_pos {α : Type*} [Fintype α] [DecidableEq α]
    {acc : List (Split α)} {s : Split α} (h : acc.all (compatibleB s) = true) :
    greedyStep acc s = s :: acc := by
  simp only [greedyStep]
  split_ifs
  rfl

/-- 守卫不成立时的展开式。 -/
theorem greedyStep_neg {α : Type*} [Fintype α] [DecidableEq α]
    {acc : List (Split α)} {s : Split α} (h : ¬ acc.all (compatibleB s) = true) :
    greedyStep acc s = acc := by
  simp only [greedyStep]
  split_ifs
  rfl

/-- **贪心运行**：按次序 `L` 逐个尝试接受（在手文献的过程骨架）。

⚠️ 输出**依赖 `L` 的次序**（§5 ★B）；文献未规定同频次序，故它**不是**「贪心共识」的定义。 -/
def greedyRun {α : Type*} [Fintype α] [DecidableEq α] (L : List (Split α)) : Finset (Split α) :=
  (L.foldl greedyStep []).toFinset

theorem greedyRun_nil {α : Type*} [Fintype α] [DecidableEq α] :
    greedyRun ([] : List (Split α)) = ∅ := by
  simp only [greedyRun, List.foldl_nil, List.toFinset_nil]

/-! ### §3.1 ★★★ 安全性质：**无论次序如何**，输出总是两两相容 -/

/-- 折叠的不变量：**已接受列表两两相容**在每一步保持。 -/
theorem foldl_greedyStep_pairwise {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Split α)) :
    ∀ acc : List (Split α), (∀ a ∈ acc, ∀ b ∈ acc, Split.Compatible a b) →
      ∀ a ∈ L.foldl greedyStep acc, ∀ b ∈ L.foldl greedyStep acc,
        Split.Compatible a b := by
  induction L with
  | nil => intro acc hacc; exact hacc
  | cons s L ih =>
    intro acc hacc a ha b hb
    rw [List.foldl_cons] at ha hb
    by_cases hg : acc.all (compatibleB s) = true
    · rw [greedyStep_pos hg] at ha hb
      refine ih (s :: acc) ?_ a ha b hb
      intro a ha b hb
      rcases List.mem_cons.mp ha with ha' | ha'
      · rcases List.mem_cons.mp hb with hb' | hb'
        · rw [ha', hb']; exact Or.inr (Or.inl s.disjoint_sides)
        · rw [ha']; exact (compatibleB_eq s b).mp ((List.all_eq_true.mp hg) b hb')
      · rcases List.mem_cons.mp hb with hb' | hb'
        · rw [hb']
          exact (Split.compatible_comm a s).mpr
            ((compatibleB_eq s a).mp ((List.all_eq_true.mp hg) a ha'))
        · exact hacc a ha' b hb'
    · rw [greedyStep_neg hg] at ha hb
      exact ih acc hacc a ha b hb

/-- ★★★ **贪心运行的输出恒为两两相容的 split 族**（「安全性质」；§2 的把手）。

对**任意**候选次序 `L`（含任意同频决胜）成立 —— 即「贪心**不会**产出不相容的 split 族」。
与 `pairwiseCompatible`（`Phylo/Split.lean:894`）同为「树的 split 系统相容」的一侧。 -/
theorem greedyRun_compatible {α : Type*} [Fintype α] [DecidableEq α] (L : List (Split α)) :
    ∀ s ∈ greedyRun L, ∀ t ∈ greedyRun L, Split.Compatible s t := by
  intro s hs t ht
  unfold greedyRun at hs ht
  exact foldl_greedyStep_pairwise L [] (by intro a ha; exact absurd ha (by simp))
    s (List.mem_toFinset.mp hs) t (List.mem_toFinset.mp ht)

/-! ### §3.2 输出的成员含于候选集 -/

/-- 折叠的成员不变量。 -/
theorem foldl_greedyStep_subset {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Split α)) :
    ∀ acc : List (Split α), ∀ a ∈ L.foldl greedyStep acc, a ∈ acc ∨ a ∈ L := by
  induction L with
  | nil => intro acc a ha; exact Or.inl ha
  | cons s L ih =>
    intro acc a ha
    rw [List.foldl_cons] at ha
    rcases ih (greedyStep acc s) a ha with h | h
    · by_cases hg : acc.all (compatibleB s) = true
      · rw [greedyStep_pos hg] at h
        rcases List.mem_cons.mp h with h' | h'
        · exact Or.inr (h' ▸ List.mem_cons_self)
        · exact Or.inl h'
      · rw [greedyStep_neg hg] at h; exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem s h)

/-- **贪心只接受候选集里的 split**。 -/
theorem mem_greedyRun_subset {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Split α)) {s : Split α} (hs : s ∈ greedyRun L) : s ∈ L := by
  unfold greedyRun at hs
  rcases foldl_greedyStep_subset L [] s (List.mem_toFinset.mp hs) with h | h
  · exact absurd h (by simp)
  · exact h

/-! ### §3.3 ★★★ 候选族两两相容 ⟹ **全部被接受**（与次序无关） -/

/-- 折叠的基数刻画：若「世界」`U` 两两相容、且 `L ∪ acc ⊆ U`，则折叠**一个不落**全接受。 -/
theorem foldl_greedyStep_toFinset {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Split α)) :
    ∀ (U acc : List (Split α)),
      (∀ s ∈ U, ∀ t ∈ U, Split.Compatible s t) →
      (∀ s ∈ L, s ∈ U) → (∀ a ∈ acc, a ∈ U) →
      (L.foldl greedyStep acc).toFinset = acc.toFinset ∪ L.toFinset := by
  induction L with
  | nil =>
    intro U acc _ _ _
    rw [List.foldl_nil, List.toFinset_nil, Finset.union_empty]
  | cons s L ih =>
    intro U acc hU hLU haccU
    rw [List.foldl_cons]
    have hsU : s ∈ U := hLU s List.mem_cons_self
    have hguard : acc.all (compatibleB s) = true := by
      rw [List.all_eq_true]
      intro a ha
      exact (compatibleB_eq s a).mpr (hU s hsU a (haccU a ha))
    rw [greedyStep_pos hguard]
    rw [ih U (s :: acc) hU (fun a ha => hLU a (List.mem_cons_of_mem s ha)) (by
      intro a ha
      rcases List.mem_cons.mp ha with ha' | ha'
      · exact ha' ▸ hsU
      · exact haccU a ha')]
    rw [List.toFinset_cons, List.toFinset_cons]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto

/-- ★★★ **候选族两两相容 ⟹ 贪心照单全收**（输出 = 候选集，**与次序无关**）。 -/
theorem greedyRun_eq_toFinset_of_pairwiseCompatible {α : Type*} [Fintype α] [DecidableEq α]
    (L : List (Split α)) (h : ∀ s ∈ L, ∀ t ∈ L, Split.Compatible s t) :
    greedyRun L = L.toFinset := by
  have hmain := foldl_greedyStep_toFinset L L []
    h (fun _ hx => hx) (fun a ha => absurd ha (by simp))
  unfold greedyRun
  rw [hmain, List.toFinset_nil, Finset.empty_union]

/-! ## §4 与 **Day 1985 的 `M_l`**、**严格共识**的关系（在手文献可证部分）

Day (1985) 的 `M_l`（md `:238–245`，本库 `Phylo/ConsensusExtra.lean:155` 的 `lSplits`）：
`s ∈ M_l ⟺ s` 出现在**至少 `l` 棵**输入树中。
`l = |ι|` 时为严格共识（`:221–232`），`l = ⌊k/2⌋+1` 时为多数共识（`:243–245`）。

**关键**：`2l > |ι|` 时 `M_l` 的 split **两两相容**（鸽笼原理），
故由 §3.3，**任何次序**的贪心都会把它们全部接受。 -/

/-- ★★★ **`2l > |ι|` 时，贪心在 `M_l` 候选族上照单全收：输出恰是 `M_l`**（与次序无关）。

这是本文件对 C4 的**核心结论**：在手文献能撑住的贪心共识，**恰好就是 Day 的阈值族 `M_l`**
（`2l > |ι|`）；越过该阈值（`2l ≤ |ι|`，`Phylo/ConsensusExtra.lean:42–50` 有反例）
就**必须**有新的规范（R\* / Bryant 的贪心决胜规则）——而那篇文献不在手。 -/
theorem lSplits_greedyRun_eq {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (l : ℕ) (T : ι → Cladogram X)
    (hk : Fintype.card ι < 2 * l) (L : List (Split X))
    (hsub : ∀ s ∈ L, s ∈ lSplits l T) (hcov : ∀ s ∈ lSplits l T, s ∈ L) :
    greedyRun L = lSplits l T := by
  rw [greedyRun_eq_toFinset_of_pairwiseCompatible L
    (fun s hs t ht => lSplits_compatible l T hk (hsub s hs) (hsub t ht))]
  ext s
  rw [List.mem_toFinset]
  exact ⟨fun h => hsub s h, fun h => hcov s h⟩

/-- ★★★ **严格共识是任意贪心的不动点**（Adams 1972 md `:346–349`、`:651–658` 的
「insensitive to the order」在 split 层的可证形态；严格共识本身是 Day `:221–232` 的 `C`）。 -/
theorem strictSplits_greedyRun_eq {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (T : ι → Cladogram X)
    (L : List (Split X)) (hsub : ∀ s ∈ L, s ∈ strictSplits T)
    (hcov : ∀ s ∈ strictSplits T, s ∈ L) :
    greedyRun L = strictSplits T := by
  rw [greedyRun_eq_toFinset_of_pairwiseCompatible L
    (fun s hs t ht => strict_compatible T (hsub s hs) (hsub t ht))]
  ext s
  rw [List.mem_toFinset]
  exact ⟨fun h => hsub s h, fun h => hcov s h⟩

/-! ### §4.1 阈值型规则**对树族重标号不变**（Adams 1972 的次序无关性） -/

/-- 支持集的基数对索引置换不变。 -/
theorem card_supportSet_perm {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Cladogram X) (σ : Equiv.Perm ι)
    (s : Split X) :
    (supportSet (fun i => T (σ i)) s).card = (supportSet T s).card := by
  classical
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    have hi' : (T (σ i)).IsSplitOf s := (Finset.mem_filter.mp hi).2
    exact mem_supportSet.mpr hi'
  · intro i₁ _ i₂ _ h; exact σ.injective h
  · intro j hj
    exact ⟨σ.symm j, mem_supportSet.mpr (by simpa using (Finset.mem_filter.mp hj).2),
      by simp⟩

/-- ★★ **`M_l` 只依赖树族**（对索引重标号不变）—— 阈值型共识的次序无关性。 -/
theorem lSplits_perm {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (l : ℕ) (T : ι → Cladogram X)
    (σ : Equiv.Perm ι) : lSplits l (fun i => T (σ i)) = lSplits l T := by
  ext s
  rw [mem_lSplits, mem_lSplits, card_supportSet_perm T σ s]

/-- ★★ **严格共识只依赖树族**（对索引重标号不变）。 -/
theorem strictSplits_perm {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Cladogram X) (σ : Equiv.Perm ι) :
    strictSplits (fun i => T (σ i)) = strictSplits T := by
  ext s
  rw [mem_strictSplits, mem_strictSplits]
  constructor
  · intro h i
    have h' := h (σ.symm i)
    simpa using h'
  · intro h i; exact h (σ i)

/-! ## §5 ★B 反例检查：**贪心加入顺序会影响输出吗？** —— 会（最小例子 `Fin 4`，2 个候选）

叶集 `X = Fin 4`，两个**不相容**的非平凡 split：

* `exGreedyS = {0,1} | {2,3}`，
* `exGreedyT = {0,2} | {1,3}`（四个交 `{0},{1},{2},{3}` 全非空 ⟹ 不相容）。

候选**多重集**相同（`{exGreedyS, exGreedyT}`），两种次序给出**不同**输出：

| 次序 | 输出 |
|---|---|
| `[exGreedyS, exGreedyT]` | `{exGreedyS}` |
| `[exGreedyT, exGreedyS]` | `{exGreedyT}` |

两者都是**相容族**（单元素，§3.1），且各自都能被**真的树**实现
（`exGreedy_trees_exist`）—— 故这**不是**集合写法上的差别，而是**两棵不同的共识树**。
⇒ ADR2016 `:779–781` 的转述**不定义一个函数**，缺的正是 Bryant 2003 的同频决胜规则。 -/

/-- 例子用的叶集 `X = Fin 4`。 -/
abbrev Ex4 := Fin 4

/-- 例子的第一个 split `{0,1} | {2,3}`。 -/
noncomputable def exGreedyS : Split Ex4 :=
  splitOf ({0, 1} : Finset Ex4) (by decide) (by decide)

/-- 例子的第二个 split `{0,2} | {1,3}`（与 `exGreedyS` 不相容）。 -/
noncomputable def exGreedyT : Split Ex4 :=
  splitOf ({0, 2} : Finset Ex4) (by decide) (by decide)

/-- ★★ **两 split 不相容**（四个交全非空）。 -/
theorem exGreedy_not_compatible : ¬ Split.Compatible exGreedyS exGreedyT := by
  rw [Split.compatible_iff_subset]
  decide

/-- ★★★ **★B 最小反例**：同一候选多重集、两种次序 ⟹ **不同输出**。 -/
theorem greedyRun_order_dependent :
    greedyRun [exGreedyS, exGreedyT] ≠ greedyRun [exGreedyT, exGreedyS] := by
  decide

/-- 次序 `[exGreedyS, exGreedyT]` 的输出（**算出**，非「构造」）。 -/
theorem exGreedy_run_left : greedyRun [exGreedyS, exGreedyT] = {exGreedyS} := by decide

/-- 次序 `[exGreedyT, exGreedyS]` 的输出。 -/
theorem exGreedy_run_right : greedyRun [exGreedyT, exGreedyS] = {exGreedyT} := by decide

/-- 反空真：两个输出都**非空**（各含一个非平凡 split）。 -/
theorem exGreedy_mem_run : exGreedyS ∈ greedyRun [exGreedyS, exGreedyT] := by decide

/-- 反空真：第一种次序**丢掉了** `exGreedyT`（不是「两个都收」）。 -/
theorem exGreedy_not_mem_run : exGreedyT ∉ greedyRun [exGreedyS, exGreedyT] := by decide

/-- ★★★ 两个输出都满足 §3.1 的**安全性质**（相容族）——
即「贪心永远输出相容族」，但这**不够**定出它是哪一族。 -/
theorem exGreedy_run_left_compatible :
    ∀ s ∈ greedyRun [exGreedyS, exGreedyT], ∀ t ∈ greedyRun [exGreedyS, exGreedyT],
      Split.Compatible s t :=
  greedyRun_compatible _

/-- ★★★ **特定（单元素相容）split 族总能被真的树实现**（`Fin 4` 反例的「树层」见证）。 -/
theorem exists_cladogram_of_singleton {X : Type u} [Fintype X] [DecidableEq X]
    (s : Split X) (hnt : 2 ≤ s.sideA.card ∧ 2 ≤ s.sideB.card) (h3 : 3 ≤ Fintype.card X) :
    ∃ M : Cladogram.{u, u} X, M.IsSplitOf s := by
  classical
  obtain ⟨ρ⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card X by omega)
  obtain ⟨M, hM, -⟩ := exists_cladogram_of_compatible ({s} : Finset (Split X)) ρ
    (by
      intro a ha b hb
      rw [Finset.mem_singleton] at ha hb
      rw [ha, hb]
      exact Or.inr (Or.inl s.disjoint_sides))
    (by intro a ha; rw [Finset.mem_singleton] at ha; rw [ha]; exact hnt)
    h3
  exact ⟨M, hM s (Finset.mem_singleton_self s)⟩

/-- ★★★ **两个输出各自是一棵真树的 split 集**（故 `greedyRun_order_dependent`
是「两棵不同的树」的差别，不是集合写法的差别）。 -/
theorem exGreedy_trees_exist :
    (∃ M : Cladogram.{0, 0} Ex4, M.IsSplitOf exGreedyS) ∧
      (∃ M : Cladogram.{0, 0} Ex4, M.IsSplitOf exGreedyT) :=
  ⟨exists_cladogram_of_singleton exGreedyS ⟨by decide, by decide⟩ (by decide),
    exists_cladogram_of_singleton exGreedyT ⟨by decide, by decide⟩ (by decide)⟩

/-! ## §6 显式缺口（C3 / C4） -/

/-- ⬜ **缺口 C4（贪心共识）：ADR2016 `:779–781` 的一句话转述不定义一个函数。**

下式即该转述**隐含需要**的性质：贪心输出**只依赖候选多重集**（与次序无关）。
本文件**已证它为假**（`greedyConsensus_gap_refuted`）：`Fin 4` 上同一候选多重集
`{exGreedyS, exGreedyT}` 按两种次序给出 `{exGreedyS}` 与 `{exGreedyT}`。

⇒ 补齐「同频决胜规则」需要 **Bryant, D. (2003)**, *A classification of consensus methods
for phylogenetics*, DIMACS 61:163–184（= ADR2016 的 `[9]`，`:1279–1281`）—— **不在手**。

本文件**不猜**该决胜规则，也不把 `greedyRun` 冒充为贪心共识。 -/
def greedyConsensus_gap : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (L L' : List (Split X)),
    L.Perm L' → greedyRun L = greedyRun L'

/-- ★★★ **缺口 C4 的证伪**：`greedyConsensus_gap` 为**假**（`Fin 4` 反例）。

这正是「在手文献的一行转述**不足以**定义贪心共识」的**证明**。 -/
theorem greedyConsensus_gap_refuted : ¬ greedyConsensus_gap := by
  intro h
  exact greedyRun_order_dependent
    (h (Fin 4) [exGreedyS, exGreedyT] [exGreedyT, exGreedyS] (List.Perm.swap _ _ _))

/-- ⬜ **缺口 C3（R\* 共识）**：R\* 共识的**精确刻画不在手文献**（§0：
全库 `R*` 仅命中 `Day1985:1229` 的伪代码局部变量），故本文件**不写** R\* 的定义。

寄存器 `R` 为「R\*-型规则」必须满足的、**在手文献可陈述的**四条必要条件：

1. 输出**两两相容**（任何共识树的前提）；
2. **包含严格共识**（`strictSplits ⊆ R`；严格共识的支持度最大，故属 R\* 的封闭条件之内）；
3. **含于「至少出现在一棵输入树中」的 split 集**（`R ⊆ lSplits 1`，频率 ≥ 1）；
4. **只依赖树族**（对索引重标号不变；频率型规则的基本性质）。

⚠️ 这四条是**必要**而非**充分**：R\* 区别于严格/多数共识的**充分条款**
（按频率次序的相容性封闭）**无法**在手文献中陈述。§6 末给出其**反空真**
（`rStarConsensus_gap_strictSplits`：严格共识满足全部四条）与**结构障碍**
（`no_compatible_family_containing_incompatible`：一旦越过 `2l > |ι|` 的阈值，
`M_l` 已含不相容对，**任何**相容值规则都必须**丢弃**其中的 split ——
「按什么规范丢」正是 R\* / Bryant 2003 要回答、而在手文献答不出的那一条）。 -/
def rStarConsensus_gap {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : (ι → Cladogram X) → Finset (Split X)) : Prop :=
  (∀ T : ι → Cladogram X, ∀ s ∈ R T, ∀ t ∈ R T, Split.Compatible s t) ∧
    (∀ T : ι → Cladogram X, strictSplits T ⊆ R T) ∧
      (∀ T : ι → Cladogram X, R T ⊆ lSplits 1 T) ∧
        (∀ (T : ι → Cladogram X) (σ : Equiv.Perm ι), R (fun i => T (σ i)) = R T)

/-- ★★★ **反空真**：`rStarConsensus_gap` 的**前提条件束非空** ——
严格共识（Day 1985 `:221–232`）满足全部四条（第 3 条用 `strictSplits_subset_lSplits`、
第 4 条用 `strictSplits_perm`、第 1 条用 `strict_compatible`）。
故 §6 的寄存器**不是**空真命题。 -/
theorem rStarConsensus_gap_strictSplits {X : Type u} [Fintype X] [DecidableEq X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    rStarConsensus_gap (X := X) (ι := ι) (fun T => strictSplits T) :=
  ⟨fun T _ hs _ ht => strict_compatible T hs ht,
    fun _ _ hx => hx,
    fun T _ hx => strictSplits_subset_lSplits (l := 1)
      (Fintype.card_pos_iff.mpr inferInstance) T hx,
    fun T σ => strictSplits_perm T σ⟩

/-- ★★★ **结构障碍**：若 `S ⊆ R`、`R` 两两相容、而 `S` **含不相容对**，则矛盾。

⇒ 越过 `2l > |ι|` 阈值后（`M_l` 已含不相容对），**任何**相容值共识规则都必须
**丢弃** `M_l` 的部分 split；「丢弃规范」即 R\* 共识 / Bryant 2003 的核心内容 ——
不在手，故落 §6 的缺口。 -/
theorem no_compatible_family_containing_incompatible {α : Type*} [Fintype α] [DecidableEq α]
    {S R : Finset (Split α)} (hSR : S ⊆ R)
    (hR : ∀ s ∈ R, ∀ t ∈ R, Split.Compatible s t)
    (hinc : ∃ s ∈ S, ∃ t ∈ S, ¬ Split.Compatible s t) : False := by
  obtain ⟨s, hs, t, ht, h⟩ := hinc
  exact h (hR s (hSR hs) t (hSR ht))
