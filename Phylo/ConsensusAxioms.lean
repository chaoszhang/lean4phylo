/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Split
import Mathlib.Tactic

/-!
# `Phylo.ConsensusAxioms` —— n-tree 共识函数的公理化（W11h / C5）

文献：F. R. McMorris & D. Neumann, *Consensus functions defined on trees*,
Mathematical Social Sciences **4**(2) (1983) 131–136。
文本见 `references/md/McMorrisNeumann1983_ConsensusFunctionsTrees.md`；
**行号一律指该 md 的文件行号**（该文 OCR 损毁严重，凡引用处均以 `>` 标出，
文末「诚实边界」列出无法复原之处）。

> ⚠️ 新增 import：`Mathlib.Tactic`（用到 `omega` / `norm_num` / `decide` 与 `split_ifs`）；
> `Phylo.Split` 只带 `Mathlib.Tactic.FinCases`。这是**唯一**新增的 import。
> ⚠️ 本文件**不用 section variable**（与 `Phylo/Consensus.lean`、`Phylo/Supertree.lean` 一致），
> 以免 `linter.unusedSectionVars` 告警。

## 0. 原文设定（§3 *Consensus of classifications*，285–334 行）

**n-tree**（294–302 行）：

> "An n-tree on S is a set of subsets T of S satisfying: S ∈ T, ∅ ∉ T, {x} ∉ T for all x ∈ S,
>  and X ∩ Y ∈ {∅, X, Y} for all X, Y ∈ T." ... "The trivial n-tree is then considered to be
>  the empty set ∅." ... "Thus an n-tree T can be specified as a subset of 𝒫*(S) [the proper,
>  non-empty, non-singleton subsets]"

本文件用**簇族**建模：`IsNTree T := (∀ X ∈ T, IsCluster X) ∧ LaminarFamily T`，
其中 `IsCluster X := 2 ≤ X.card ∧ X ≠ univ`（即 `𝒫*(S)`）。

**共识函数**（306 行）：

> "A consensus function for n-trees on S is a function C : 𝒯^k → 𝒯."

**公理**（308–334 行，逐条抄录；OCR 有损处以 `[?]` 标注）：

> "(N) C is neutral whenever {i : X ∈ T_i} [=?] {j : Y ∈ T'_j} implies X ∈ CP if and only if Y ∈ CP'."
> "(M) C is monotone whenever {i : X ∈ T'_i} ⊇ {i : X ∈ T_i} implies X ∈ CP ⟹ X ∈ CP'."
> "(P) C is Pareto if {i : X ∈ T_i} = K implies X ∈ CP."
> "(coP) C is co-Pareto if CP ⊆ T₁ ∪ … ∪ T_k."
> "(S) C is symmetric if for every permutation σ on K, CP_σ = CP where [P_σ = (T_{σ(1)},…,T_{σ(k)})]."
> "(A) C is autonomous if for every A ∈ 𝒫*(S) there [exists a profile P such that] A ∈ CP."

由此得到（348–355 行）：

> "(i) C satisfies (M) and (N) if and only if C satisfies: (MN) If |{i : X ∈ T_i}| = |{j : Y ∈ T'_j}|,
>  then X ∈ CP implies Y ∈ CP'."
> "(ii) If C satisfies (MN), then C satisfies (coP). (iii) If C satisfies (MN) and (A), then C
>  satisfies (P)."

**Theorem 2**（362–419 行）：`C` 满足 (MN) 与 (A) ⟺ `C = M_𝒟`（`𝒟` 为**决定性族**，
`X ∈ M_𝒟(P) ⟺ {i : X ∈ T_i} ∈ 𝒟`）。

**Corollary**（429–436 行）：

> "A consensus function C satisfies (MN), (A) and (S) if and only if C = M_t [for some fixed t] ...
>  Since no two decisive sets can be disjoint, [t > ½k]."

（即：满足公理的共识函数**恰是阈值规则**；且阈值必须**严格多数**。）

## 1. 本文件证出（零 `sorry` / `axiom` / `native_decide`）

* ★★ 阈值规则 `ThresholdRule k t` 满足 **(P)**（`t ≤ k`）、**(coP)**（`1 ≤ t`）、
  **(M)**、**(MN)/(MN卡)**、**(S)**、**(A)**（`t ≤ k`）—— 即「严格共识（`t = k`）与
  多数共识（`t > k/2`）类规则满足文献指定的公理」；
* ★★ **Theorem 2 的核心**：`(MN) + 输出只含簇 ⟹ C` **就是**某个决定性族规则 `M_𝒟`，
  且 `M_𝒟` 反向满足 `(MN)`（`eq_decisiveRule_of_mnSet` / `mnSet_decisiveRule`）；
* ★★★ **严格多数阈值是 n-tree 值**（`thresholdRule_isNTree`，`k < 2t`）：
  两个支持集各 `> k/2` 必相交 ⟹ 同一棵输入 n-tree 已保证两簇镶嵌。
  这是 Margush–McMorris 多数共识「多数 split 必相容」的**簇层**对应物
  （split 层见 `Phylo/Consensus.lean:50` 的 `majority_compatible`）；
* ★★★ **不可能性（弱多数阈值）**：`2t ≤ k` 时阈值规则**不可能**是 n-tree 值
  （`thresholdRule_not_isNTree_of_le`），并给出 `Fin 4` 上 `k = 2, t = 1` 的**具体反例**
  （`no_weakmajority_threshold_isNTree`）——两个交叉簇各拿一票，输出不是镶嵌族。
  ⇒ 公理组 `{(MN), (M), (A)}` + n-tree 值 **排斥**弱多数阈值；
* ★ 非空真：`thresholdRule_isNTree_two`（`k = 2, t = 2` 确实行）与上式对照。
-/

noncomputable section

namespace NTreeConsensus

/-! ## 1. 簇、n-tree、剖面 -/

/-- **簇**：`𝒫*(S)` —— 非平凡子集（`2 ≤ |X|` 且 `X ≠ univ`；文献 299–302 行）。 -/
def IsCluster {α : Type*} [Fintype α] [DecidableEq α] (X : Finset α) : Prop :=
  2 ≤ X.card ∧ X ≠ Finset.univ

/-- **n-tree**（文献 294–302 行的簇族公理）：只含簇、两两镶嵌。 -/
def IsNTree {α : Type*} [Fintype α] [DecidableEq α] (T : Finset (Finset α)) : Prop :=
  (∀ X ∈ T, IsCluster X) ∧ LaminarFamily T

/-- **剖面**：`k` 棵 n-tree（文献 306 行的 `𝒯^k`）。 -/
abbrev Profile {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) : Type _ :=
  Fin k → Finset (Finset α)

/-- **共识函数** `C : 𝒯^k → 𝒯`（文献 306 行）。为便于陈述公理，这里定义在**整个**剖面上；
公理中对「输入是 n-tree」的要求显式写入假设。 -/
abbrev ConsensusFn {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) : Type _ :=
  Profile (α := α) k → Finset (Finset α)

/-- **平凡 n-tree**：`∅`（文献 301–302 行 "The trivial n-tree is then considered to be the
empty set ∅"）。 -/
theorem isNTree_empty {α : Type*} [Fintype α] [DecidableEq α] :
    IsNTree (∅ : Finset (Finset α)) :=
  ⟨by intro X hX; exact absurd hX (Finset.notMem_empty X),
   by intro A hA; exact absurd hA (Finset.notMem_empty A)⟩

/-- 单簇族 `{X}` 是 n-tree ⟺ `X` 是簇。 -/
theorem isNTree_singleton {α : Type*} [Fintype α] [DecidableEq α] {X : Finset α}
    (h : IsCluster X) : IsNTree ({X} : Finset (Finset α)) :=
  ⟨by intro Y hY; rw [Finset.mem_singleton] at hY; exact hY ▸ h,
   by intro A hA B hB
      rw [Finset.mem_singleton] at hA hB
      rw [hA, hB]
      exact Or.inl fun x hx => hx⟩

/-- `X` 在剖面 `P` 中的**支持集** `{i : X ∈ T_i}`（文献 350–352 行）。 -/
def support {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (P : Profile (α := α) k) (X : Finset α) : Finset (Fin k) :=
  Finset.univ.filter fun i => X ∈ P i

/-! ## 2. 公理（文献 308–334 行） -/

/-- **(P) Pareto**（329 行）：全数支持 ⟹ 入选。 -/
def Pareto {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P : Profile (α := α) k) (X : Finset α), IsCluster X → (∀ i, X ∈ P i) → X ∈ C P

/-- **(coP) co-Pareto**（330 行）：`CP ⊆ T₁ ∪ … ∪ T_k`。 -/
def CoPareto {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P : Profile (α := α) k) (X : Finset α), X ∈ C P → ∃ i, X ∈ P i

/-- **(M) 单调**（327 行）：支持集变大 ⟹ 仍然入选。 -/
def Monotone {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P P' : Profile (α := α) k) (X : Finset α), IsCluster X →
    (∀ i, X ∈ P i → X ∈ P' i) → X ∈ C P → X ∈ C P'

/-- **(MN)**（348–352 行，`(M) ∧ (N)` 的等价形式）：**支持集相等** ⟹ 隶属相同。 -/
def MNSet {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P P' : Profile (α := α) k) (X Y : Finset α), IsCluster X → IsCluster Y →
    support P X = support P' Y → X ∈ C P → Y ∈ C P'

/-- **(MN) 的基数版**（348–352 行 OCR 的读法：只有**票数**重要）。
这是**更强**的公理：基数相等是比「支持集相等」更弱的假设，故 `MNCard ⟹ MNSet`。 -/
def MNCard {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P P' : Profile (α := α) k) (X Y : Finset α), IsCluster X → IsCluster Y →
    (support P X).card = (support P' Y).card → X ∈ C P → Y ∈ C P'

/-- 支持集相等 ⟹ 基数相等，故 `(MN卡) ⟹ (MN)`。 -/
theorem mnSet_of_mnCard {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {C : ConsensusFn (α := α) k} (h : MNCard C) : MNSet C :=
  fun P P' X Y hX hY hsup hmem => h P P' X Y hX hY (by rw [hsup]) hmem

/-- **(S) 对称**（331–332 行）：剖面置换不改输出。 -/
def Symmetric {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P : Profile (α := α) k) (σ : Equiv.Perm (Fin k)), C (fun i => P (σ i)) = C P

/-- **(A) autonomous**（333–334 行，OCR 有损）：每个簇都被某个 n-tree 剖面选入。 -/
def Autonomous {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ X : Finset α, IsCluster X →
    ∃ P : Profile (α := α) k, (∀ i, IsNTree (P i)) ∧ X ∈ C P

/-- **n-tree 值**（306 行 `C : 𝒯^k → 𝒯`）：n-tree 输入 ⟹ n-tree 输出。 -/
def NTreeValued {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ P : Profile (α := α) k, (∀ i, IsNTree (P i)) → IsNTree (C P)

/-- 输出只含簇（n-tree 值的一部分）。 -/
def ClusterValued {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Prop :=
  ∀ (P : Profile (α := α) k) (X : Finset α), X ∈ C P → IsCluster X

/-! ## 3. 阈值规则（文献 387–390 行 Example 2；429–436 行推论） -/

/-- **阈值规则** `M_t`：`X ∈ CP ⟺ t ≤ |{i : X ∈ T_i}|`（且 `X` 是簇）。

`t = k` 即**严格共识**（全数支持）；`t > k/2` 即**多数共识**
（split 层见 `Phylo/Consensus.lean` 的 `majority_compatible` / `majority_consensus_exists`）。 -/
def ThresholdRule {α : Type*} [Fintype α] [DecidableEq α] (k t : ℕ)
    (P : Profile (α := α) k) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter fun X => IsCluster X ∧ t ≤ (support P X).card

theorem mem_thresholdRule {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    {P : Profile (α := α) k} {X : Finset α} :
    X ∈ ThresholdRule (α := α) k t P ↔ IsCluster X ∧ t ≤ (support P X).card := by
  classical
  simp [ThresholdRule]

/-- ★★ 阈值规则满足 **(P) Pareto**（`t ≤ k`）。 -/
theorem thresholdRule_pareto {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (ht : t ≤ k) : Pareto (α := α) (ThresholdRule (α := α) k t) := by
  intro P X hX hmem
  rw [mem_thresholdRule]
  refine ⟨hX, ?_⟩
  have hsup : support P X = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hmem i
  rw [hsup, Finset.card_univ, Fintype.card_fin]
  exact ht

/-- ★★ 阈值规则满足 **(coP) co-Pareto**（`1 ≤ t`）。 -/
theorem thresholdRule_coPareto {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (ht : 1 ≤ t) : CoPareto (α := α) (ThresholdRule (α := α) k t) := by
  intro P X hX
  rw [mem_thresholdRule] at hX
  have h0 : 0 < t := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (lt_of_lt_of_le h0 hX.2)
  exact ⟨i, by simpa [support] using hi⟩

/-- ★★ 阈值规则满足 **(M) 单调**。 -/
theorem thresholdRule_monotone {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ} :
    Monotone (α := α) (ThresholdRule (α := α) k t) := by
  intro P P' X hX hsub hmem
  rw [mem_thresholdRule] at hmem ⊢
  have hcard : (support P X).card ≤ (support P' X).card :=
    Finset.card_le_card fun i hi => by
      simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hsub i hi
  exact ⟨hX, le_trans hmem.2 hcard⟩

/-- ★★ 阈值规则满足 **(MN)**。 -/
theorem thresholdRule_mnSet {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ} :
    MNSet (α := α) (ThresholdRule (α := α) k t) := by
  intro P P' X Y hX hY hsup hmem
  rw [mem_thresholdRule] at hmem ⊢
  exact ⟨hY, by rw [← hsup]; exact hmem.2⟩

/-- ★★ 阈值规则满足 **(MN) 基数版**。 -/
theorem thresholdRule_mnCard {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ} :
    MNCard (α := α) (ThresholdRule (α := α) k t) := by
  intro P P' X Y hX hY hcard hmem
  rw [mem_thresholdRule] at hmem ⊢
  exact ⟨hY, by rw [← hcard]; exact hmem.2⟩

/-- 置换剖面不改变支持集的**基数**（对称性的全部内容）。 -/
theorem card_support_comp {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (P : Profile (α := α) k) (σ : Equiv.Perm (Fin k)) (X : Finset α) :
    (support (fun i => P (σ i)) X).card = (support P X).card := by
  have himg : (support P X).image σ.symm = support (fun i => P (σ i)) X := by
    ext i
    simp only [support, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
    · intro hi
      exact ⟨σ i, by simpa using hi, by simp⟩
  rw [← himg]
  exact Finset.card_image_of_injective _ σ.symm.injective

/-- ★★ 阈值规则满足 **(S) 对称**。 -/
theorem thresholdRule_symmetric {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ} :
    Symmetric (α := α) (ThresholdRule (α := α) k t) := by
  intro P σ
  ext X
  simp only [ThresholdRule, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [card_support_comp]

/-- ★★ 阈值规则满足 **(A) autonomous**（`t ≤ k`）。 -/
theorem thresholdRule_autonomous {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (ht : t ≤ k) : Autonomous (α := α) (ThresholdRule (α := α) k t) := by
  intro X hX
  refine ⟨fun _ : Fin k => ({X} : Finset (Finset α)), fun _ => isNTree_singleton hX, ?_⟩
  rw [mem_thresholdRule]
  refine ⟨hX, ?_⟩
  have hsup : support (fun _ : Fin k => ({X} : Finset (Finset α))) X = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => by simp
  rw [hsup, Finset.card_univ, Fintype.card_fin]
  exact ht

/-! ## 4. ★★★ 严格多数阈值 ⟹ n-tree 值 -/

/-- ★★★ **严格多数阈值（`k < 2t`）的阈值规则是 n-tree 值**。

**鸽笼**：`X, Y` 各得 `> k/2` 票 ⟹ 两个支持集必相交 ⟹ 有某棵输入 n-tree 同时含 `X, Y`
⟹ 由该 n-tree 的镶嵌性得 `X, Y` 镶嵌。故输出仍是 n-tree。

（文献 429–436 行推论的「⟸」半边：阈值必须**严格多数**。） -/
theorem thresholdRule_isNTree {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (h : k < 2 * t) : NTreeValued (α := α) (ThresholdRule (α := α) k t) := by
  intro P hP
  constructor
  · intro X hX
    exact (mem_thresholdRule.mp hX).1
  · intro X hX Y hY
    rw [mem_thresholdRule] at hX hY
    have hne : (support P X ∩ support P Y).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hsum : (support P X).card + (support P Y).card
          = (support P X ∪ support P Y).card := by
        have hcu := Finset.card_union_add_card_inter (support P X) (support P Y)
        rw [hcon, Finset.card_empty, add_zero] at hcu
        omega
      have hle : (support P X ∪ support P Y).card ≤ k := by
        have := Finset.card_le_card (Finset.subset_univ (support P X ∪ support P Y))
        simpa [Finset.card_univ, Fintype.card_fin] using this
      omega
    obtain ⟨i, hi⟩ := hne
    rw [Finset.mem_inter] at hi
    exact (hP i).2 X (by simpa [support] using hi.1) Y (by simpa [support] using hi.2)

/-! ## 5. ★★★ 不可能性：弱多数阈值不是 n-tree 值 -/

/-- **规范剖面**：`D` 中的指标放 `{X}`、`D'` 中的放 `{Y}`、其余放 `∅`（平凡 n-tree）。 -/
def twoClusterProfile {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (D D' : Finset (Fin k)) (X Y : Finset α) : Profile (α := α) k :=
  fun i => if i ∈ D then {X} else if i ∈ D' then {Y} else ∅

/-- 规范剖面**全部由 n-tree 组成**（`{X}`、`{Y}`、`∅` 都是 n-tree）。 -/
theorem isNTree_twoClusterProfile {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {D D' : Finset (Fin k)} {X Y : Finset α} (hX : IsCluster X) (hY : IsCluster Y) :
    ∀ i, IsNTree (twoClusterProfile (α := α) D D' X Y i) := by
  intro i
  rw [twoClusterProfile]
  split_ifs with h h'
  · exact isNTree_singleton hX
  · exact isNTree_singleton hY
  · exact isNTree_empty

/-- 规范剖面上 `X` 的支持集**恰是 `D`**（`X ≠ Y`）。 -/
theorem support_twoClusterProfile_left {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {D D' : Finset (Fin k)} {X Y : Finset α} (hXY : X ≠ Y) :
    support (twoClusterProfile (α := α) D D' X Y) X = D := by
  have hdef : ∀ j : Fin k, twoClusterProfile (α := α) D D' X Y j
      = (if j ∈ D then {X} else if j ∈ D' then {Y} else ∅) := fun j => rfl
  ext i
  rw [support, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, hdef i]
  split_ifs with h h'
  · exact ⟨fun _ => h, fun _ => by simp⟩
  · exact ⟨fun hx => (hXY (Finset.mem_singleton.mp hx)).elim, fun hx => (h hx).elim⟩
  · exact ⟨fun hx => absurd hx (Finset.notMem_empty X), fun hx => (h hx).elim⟩

/-- 规范剖面上 `Y` 的支持集**恰是 `D'`**（`X ≠ Y` 且 `D ⊥ D'`）。 -/
theorem support_twoClusterProfile_right {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {D D' : Finset (Fin k)} {X Y : Finset α} (hXY : X ≠ Y) (hdisj : Disjoint D D') :
    support (twoClusterProfile (α := α) D D' X Y) Y = D' := by
  have hdef : ∀ j : Fin k, twoClusterProfile (α := α) D D' X Y j
      = (if j ∈ D then {X} else if j ∈ D' then {Y} else ∅) := fun j => rfl
  ext i
  rw [support, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, hdef i]
  split_ifs with h h'
  · have hni : i ∉ D' := fun hc => Finset.disjoint_left.mp hdisj h hc
    exact ⟨fun hx => (hXY (Finset.mem_singleton.mp hx).symm).elim, fun hx => (hni hx).elim⟩
  · exact ⟨fun _ => h', fun _ => by simp⟩
  · exact ⟨fun hx => absurd hx (Finset.notMem_empty Y), fun hx => (h' hx).elim⟩

/-- ★★★ **不可能性（弱多数阈值）**：若 `2t ≤ k`（且存在两个交叉簇），
则阈值规则**不可能**是 n-tree 值。

证明：取两个不相交的 `t`-元指标集 `D, D'`（`2t ≤ k` 保证存在），
构造剖面 `D ↦ {X}`、`D' ↦ {Y}`、其余 `↦ ∅`；`X`、`Y` 各得 `t` 票而入选，
但两者交叉 ⟹ 输出不是镶嵌族。 -/
theorem thresholdRule_not_isNTree_of_le {α : Type*} [Fintype α] [DecidableEq α] {k t : ℕ}
    (h : 2 * t ≤ k) {X Y : Finset α} (hX : IsCluster X) (hY : IsCluster Y)
    (hcross : ¬ (X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y)) :
    ¬ NTreeValued (α := α) (ThresholdRule (α := α) k t) := by
  intro hNT
  have htk : t ≤ k := by omega
  obtain ⟨D, hDsub, hDcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k))) (n := t) (by
      rw [Finset.card_univ, Fintype.card_fin]; exact htk)
  obtain ⟨D', hD'sub, hD'card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin k)) \ D) (n := t) (by
      rw [Finset.card_sdiff_of_subset hDsub, Finset.card_univ, Fintype.card_fin, hDcard]
      omega)
  have hdisj : Disjoint D D' :=
    Finset.disjoint_left.mpr fun i hi hi' => (Finset.mem_sdiff.mp (hD'sub hi')).2 hi
  have hXY : X ≠ Y := fun he => hcross (Or.inl fun x hx => he ▸ hx)
  have hXmem : X ∈ ThresholdRule (α := α) k t (twoClusterProfile (α := α) D D' X Y) := by
    rw [mem_thresholdRule]
    exact ⟨hX, by rw [support_twoClusterProfile_left hXY, hDcard]⟩
  have hYmem : Y ∈ ThresholdRule (α := α) k t (twoClusterProfile (α := α) D D' X Y) := by
    rw [mem_thresholdRule]
    exact ⟨hY, by rw [support_twoClusterProfile_right hXY hdisj, hD'card]⟩
  have hnt := hNT (twoClusterProfile (α := α) D D' X Y) (isNTree_twoClusterProfile hX hY)
  exact hcross (hnt.2 X hXmem Y hYmem)

/-! ### 5.1 最小具体例子（`Fin 4`，`k = 2`，`t = 1`） -/

theorem isCluster_fin4_left : IsCluster ({0, 1} : Finset (Fin 4)) := by
  constructor <;> decide

theorem isCluster_fin4_right : IsCluster ({0, 2} : Finset (Fin 4)) := by
  constructor <;> decide

/-- `{0,1}` 与 `{0,2}` **交叉**（互不包含、也不交）。 -/
theorem not_laminar_fin4 :
    ¬ (({0, 1} : Finset (Fin 4)) ⊆ ({0, 2} : Finset (Fin 4)) ∨
        ({0, 2} : Finset (Fin 4)) ⊆ ({0, 1} : Finset (Fin 4)) ∨
        Disjoint ({0, 1} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4))) := by
  rintro (h | h | h)
  · exact absurd (h (by decide : (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))))
      (by decide : ¬ ((1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))))
  · exact absurd (h (by decide : (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))))
      (by decide : ¬ ((2 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))))
  · exact (Finset.disjoint_left.mp h) (by decide : (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4)))
      (by decide : (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4)))

/-- ★★★ **不可能性（具体形式）**：不存在等于 `k = 2, t = 1` 阈值规则、且 n-tree 值的
共识函数（`2 * 1 ≤ 2`）。即：**弱多数（一半票）共识不可能保持 n-tree 结构**。 -/
theorem no_weakmajority_threshold_isNTree :
    ¬ ∃ C : ConsensusFn (α := Fin 4) 2,
        (∀ P, C P = ThresholdRule (α := Fin 4) 2 1 P) ∧ NTreeValued C := by
  rintro ⟨C, hC, hNT⟩
  have hbad := thresholdRule_not_isNTree_of_le (α := Fin 4) (k := 2) (t := 1)
    (by decide)
    (X := ({0, 1} : Finset (Fin 4))) (Y := ({0, 2} : Finset (Fin 4)))
    isCluster_fin4_left isCluster_fin4_right not_laminar_fin4
  refine hbad ?_
  intro P hP
  rw [← hC P]
  exact hNT P hP

/-- ★ **非空真**：同一设定下**严格多数**阈值（`k = 2`，`t = 2`，即严格共识）确实 n-tree 值。 -/
theorem thresholdRule_isNTree_two :
    NTreeValued (α := Fin 4) (ThresholdRule (α := Fin 4) 2 2) :=
  thresholdRule_isNTree (by norm_num)

/-! ## 6. ★★ Theorem 2 的核心：`(MN)` ⟹ 决定性族规则 -/

/-- 由 `C` 读出的**决定性族**（文献 362–419 行 Theorem 2 的 `𝒟`）：
`D ∈ 𝒟 ⟺ 某个簇恰在支持集 `D` 上入选`。 -/
def decisiveFamily {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (C : ConsensusFn (α := α) k) : Set (Finset (Fin k)) :=
  {D | ∃ (P : Profile (α := α) k) (X : Finset α), IsCluster X ∧ X ∈ C P ∧ support P X = D}

theorem mem_decisiveFamily {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {C : ConsensusFn (α := α) k} {D : Finset (Fin k)} :
    D ∈ decisiveFamily C ↔
      ∃ (P : Profile (α := α) k) (X : Finset α),
        IsCluster X ∧ X ∈ C P ∧ support P X = D :=
  Iff.rfl

/-- **决定性族规则** `M_𝒟`（文献 373–377 行）：`X ∈ M_𝒟(P) ⟺ {i : X ∈ T_i} ∈ 𝒟`。 -/
def decisiveRule {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ)
    (𝒟 : Set (Finset (Fin k))) (P : Profile (α := α) k) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter fun X => IsCluster X ∧ support P X ∈ 𝒟

theorem mem_decisiveRule {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {𝒟 : Set (Finset (Fin k))} {P : Profile (α := α) k} {X : Finset α} :
    X ∈ decisiveRule (α := α) k 𝒟 P ↔ IsCluster X ∧ support P X ∈ 𝒟 := by
  classical
  simp [decisiveRule]

/-- ★★ **Theorem 2 的核心**（362–419 行）：满足 `(MN)` 且输出只含簇的共识函数
**就是**它的决定性族规则 `M_𝒟`。 -/
theorem eq_decisiveRule_of_mnSet {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    {C : ConsensusFn (α := α) k} (hMN : MNSet C) (hcl : ClusterValued C)
    (P : Profile (α := α) k) :
    C P = decisiveRule (α := α) k (decisiveFamily C) P := by
  ext X
  constructor
  · intro hX
    rw [mem_decisiveRule]
    refine ⟨hcl P X hX, ?_⟩
    rw [mem_decisiveFamily]
    exact ⟨P, X, hcl P X hX, hX, rfl⟩
  · intro hX
    rw [mem_decisiveRule] at hX
    obtain ⟨hXc, hDmem⟩ := hX
    rw [mem_decisiveFamily] at hDmem
    obtain ⟨P₀, X₀, hX₀c, hX₀, hspec⟩ := hDmem
    exact hMN P₀ P X₀ X hX₀c hXc hspec hX₀

/-- ★★ 反向：决定性族规则满足 `(MN)`。 -/
theorem mnSet_decisiveRule {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ)
    (𝒟 : Set (Finset (Fin k))) :
    MNSet (α := α) (decisiveRule (α := α) k 𝒟) := by
  intro P P' X Y hX hY hsup hmem
  rw [mem_decisiveRule] at hmem ⊢
  refine ⟨hY, ?_⟩
  rw [← hsup]
  exact hmem.2

/-! ## 7. 缺口（显式 `Prop`；未证） -/

/-- ⬜ **缺口 1（McMorris–Neumann 推论，429–436 行）**：满足 `(MN)`、`(M)`、`(S)`、
`(A)` 且 n-tree 值的共识函数**恰是阈值规则**，且阈值 `k < 2t`。

本文件已证两半：阈值规则满足全部公理（正向）＋ `2t ≤ k` 不可能 n-tree 值（不可能性）；
从决定性族 `𝒟` 走到「`𝒟 = {D : |D| ≥ t}`」还需 `𝒟` 的**向上封闭性**与**交封闭性**
（后者需要「任意支持集都可由 n-tree 剖面实现」的构造引理）。 -/
def mnCorollary_gap : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (C : ConsensusFn (α := α) k),
    MNSet C → Monotone C → Symmetric C → Autonomous C → NTreeValued C → ClusterValued C →
      ∃ t : ℕ, k < 2 * t ∧
        ∀ P : Profile (α := α) k, (∀ i, IsNTree (P i)) →
          C P = ThresholdRule (α := α) k t P

/-- ⬜ **缺口 2（§2 Arrow 型不可能性，127–283 行）**：`|S| ≥ 3` 时**不存在**同时满足
`(P)`（Pareto）、`(I)`（无关备选独立性）与 `(D)`（非独裁）的共识函数 `C : 𝒯^k → 𝒯`
（文献 154–155 行 Theorem 1）。

未落原因：原文的 `𝒯` 是**树拟序**（tree quasi-orders，82–104 行的定义在 OCR 中已损毁，
仅存 "that is transitive, reflexive (i.e., a [quasi-order])" 与 114–116 行的
"EU y is ancestral to EU x on the tree of r"）；忠实形式化需要
「根树上的祖先关系」+ **剖面可实现性**（对给定偏序约束构造树拟序），本批未建。
已落地的**不可能性**是 §3 口径的 `no_weakmajority_threshold_isNTree`。

（下式把「共识函数」写成 `(Fin k → S → S → Prop) → (S → S → Prop)`，三条公理分别是
Pareto、IIA、非独裁；命题本身未证，仅命名缺口。） -/
def arrowTreeQuasiOrder_gap : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S] (k : ℕ), 3 ≤ Fintype.card S →
    ¬ ∃ C : (Fin k → S → S → Prop) → (S → S → Prop),
        (∀ P x y, (∀ i, P i x y) → C P x y) ∧
          (∀ P P' (X : Finset S), (∀ i x y, x ∈ X → y ∈ X → (P i x y ↔ P' i x y)) →
            ∀ x y, x ∈ X → y ∈ X → (C P x y ↔ C P' x y)) ∧
          (∀ j : Fin k, ∃ (P : Fin k → S → S → Prop) (x y : S), P j x y ∧ ¬ C P x y)

end NTreeConsensus
