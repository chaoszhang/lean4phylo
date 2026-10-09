/-
Copyright (c) 2026 ASTER LAB. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ASTER LAB
-/
import Phylo.Stat.MultiLocusASTRAL
import Phylo.Stat.Parsimony
import Phylo.Stat.NJst
import Phylo.InternalEdge
import Phylo.SplitsMaximal
import Phylo.QuartetInhabitation
import Phylo.SplitsDetermineTree
import Phylo.SplitsDetermineTreeBase

/-!
# `Phylo.Stat.QuartetDecides` —— **quartet 系统决定 binary 树**（T0.1 收口，已证）

三个算法（ASTRAL / parsimony / NJst）的统计一致性都已证到
**「输出与真树在每个 4-元集上一致」**；**多标记 ASTRAL**（跨标记求和）经
`multiLocus_isASTRAL` 也归约到 ASTRAL，故一并适用。本文件把它升级为
**「输出与真树同构」**：

> ⚠️ **真 CASTER 不在此列**（2026-10-08 批 W8a 更正）：库内旧文件 `Phylo/Stat/CASTER.lean`
> 其实是**多标记 ASTRAL** 归约（已更名 `Phylo/Stat/MultiLocusASTRAL.lean`），
> 与其同名的 `caster_iso` 亦已更名 `multiLocus_iso`。
> 真 CASTER（Zhang–Nielsen–Mirarab 2025, *Science* 387(6737) eadk9688）是**位点 / 比对**方法，
> 其数学内容此前**库内完全没有**，正由批 W8（`Phylo/Stat/LMLumping.lean` ·
> `CASTERWeights.lean` · `CASTERJC69.lean` …）另行重建。

> ★★★ **`QuartetDecidesTree`**：两棵 **binary** cladogram 若有相同的 quartet 系统，则同构。

✦ **定性（重要，勿误传）**：这**不是学术开放问题** —— 它是 **Colonius–Schultze (1981)**
与 **Steel (1992)** 的**经典定理**，教科书 Semple & Steel, *Phylogenetics* (2003) §6.4 有完整叙述。
**2026-10-08 已在库内无条件证出**（零 `sorry`、零新公理）。

（**binary 假设不可去**：polytomy 会产生反例 ——
把多叉顶点 refine 成 binary 不改变任何 quartet。）

## ✅ 收口（2026-10-08，T0.1 完成）：三步

1. **桥**（★★★ `Cladogram.sameQuartetSystem_of_agree`）：`QuartetTree` 的
   「逐 quartet 一致」（模 `swap`）⟹ `SameQuartetSystem`（`DisplaysQuartet` 层）。
   零件：`Split.restrict` + ★★★ `Cladogram.displaysSplitOn_unique` + `QuartetTree.q_card`
   （辅以 ★ `Cladogram.displaysSplitOn_swap_iff`、★★ `Cladogram.displaysQuartet_of_agree`）。
2. **Σ 相等**（★★★ `Cladogram.isSplitOf_iff_of_sameQuartetSystem`）：`SameQuartetSystem`
   + 两棵树 binary ⟹ `∀ s, T.IsSplitOf s ↔ T'.IsSplitOf s`。零件：★★
   `Cladogram.compatible_of_sameQuartetSystem`（同一 quartet 系统 ⟹ `Σ(T) ∪ Σ(T')` 两两相容）
   + ★★★ `binarySplitsMaximal`（binary ⟹ `SplitsMaximal`，极大性收口）。
3. **收口**（**相同的 split 系统 ⟹ 同构**，Semple & Steel §3.8 的「同构版」）：
   * `3 ≤ |X|`：★★★ `Cladogram.iso_of_isSplitOf_iff`（`Phylo/SplitsDetermineTree.lean`）。
     做法：固定标签 `x₀`，把每个顶点送到它「朝 `x₀` 的簇」`Cluster x₀ v`
     （= 删去 `v` 的上边后 `v` 那侧的叶集）；核心引理
     ★★★ `Cluster_subset_iff`（`C v ⊆ C u ↔ u ∈ pathVerts v (leaf x₀)`，即 **簇包含 ⟺ 祖先**）
     把结构对应化归为**路径论证**；再由 split 系统相同把该簇映射**搬运**到另一棵树
     （`psi`），证 `psi` 是双射、与「朝 `x₀` 的父亲」交换（★ `psi_parent`），
     最后用 ★ `adj_iff_parent`（相邻 ⟺ 互为父子）收成 `Iso`。
     **不需要** `IsBinary`（`Cladogram` 自带 `no_degree_two`）。
   * `|X| ≤ 2`：★★ `Cladogram.iso_of_card_le_two`（`Phylo/SplitsDetermineTreeBase.lean`）——
     退化情形：`|X| = 0` 唯一顶点、`|X| = 1` **不存在** cladogram、`|X| = 2` 必是两点一边。

⇒ `QuartetDecidesTree` 由 `def` 变**定理**，三条 `iso` 定理**已删除 `hQD` 参数**。

## 下游收口（2026-10-08 起）

* ★★★ `astral_iso` —— ASTRAL 输出与真树**同构**（**无条件**）；
* ★★★ `multiLocus_iso` —— 多标记 ASTRAL 的同款收口（**无条件**）；
  （原名 `caster_iso`；它说的是**多标记 ASTRAL** 归约，**不是 CASTER**。
  更名见 `Phylo/Stat/MultiLocusASTRAL.lean` 的文件头「更名记录」。）
* ★★★ `parsimony_iso` —— parsimony 在**位点采样**（`SiteSampling`）下**最终**恢复真树
  （依赖采样结构，**不是**无条件）；
* ★★★ `astral_statisticallyConsistent_iso` —— ASTRAL 在 **MSC 采样**（`MSCSampling`）下
  的**树层**统计一致性（落在 `MSC.StatisticallyConsistent` 上）。

## ⚠️ 修正记录（2026-10-08）：旧陈述**是假命题**；已由 **T0.6 治本**

**本命题的旧版本（没有 `2|2` 假设）是假命题**，反例（`X = {1,2,3,4}`）：

* `T` = 唯一内部 split 为 `{1,2}|{3,4}` 的 binary 树；
* `T'` = 唯一内部 split 为 `{1,3}|{2,4}` 的 binary 树（两者显然**不同构**，
  因为 `Iso` 保标号、故保 split 系统，见 `Phylo/Core.lean` 的 `Iso.leaf_compat`）；
* 令 `q` 为**常函数**，把唯一的 4-元集 `S = {1,2,3,4}` 送到 `↥S` 上的 **1|3** split
  `{1} | {2,3,4}`，并取 `q' := q`。

`DisplaysSplitOn S q` 只要求存在 `T` 的某条 split `s` 使 `q.sideA = {x ∈ S : x ∈ s.sideA}`
—— 取 `s` = `T` 的**平凡 split** `{1}|rest` 即可（`Cladogram.sideLeaves_leaf_edge`），
`T'` 同理。于是四条假设全部成立（`q = q'` 甚至不需要模 `swap`），
但结论 `Nonempty (Iso T T')` 为**假**。

**根源**：`QuartetChoice` 只要求 `Split ↥S`，而 `Split ↥S` 的两侧只须非空 —— `1|3` 也算。
「quartet」按定义必须是 `2|2`。

### ✅ 收口（**T0.6**，2026-10-08）：`2|2` 升为 `QuartetTree` 的**字段**

当时的治标补丁是「给本命题多加一条 `2|2` 合取项」，并让 `astral_iso` / `multiLocus_iso` /
`parsimony_iso` 各自多传一条 `2|2` 假设（在旧陈述下那条假设**不可满足**，
故三条定理当时是**空真**的）。**现已治本**：

* `Phylo/Stat/MSC.lean` 的 `QuartetTree` 新增字段 ★ `q_card`
  （`∀ S hS, (q S hS).sideA.card = 2`）；`MSCFreq` 经 `extends` **自动继承**；
* `Phylo/Stat/Parsimony.lean` 的 `MSCSite` 同步新增 `q_card` 字段，
  `MSCSite.asQuartetTree` 相应补上该坐标；
* ⇒ 原 `def` **改收 `QuartetTree`**（而非裸 `QuartetChoice`）：那条 `2|2` 合取项
  不再需要（它就是 `qt.q_card`），`qt.displays` / `qt'.displays` 亦然；
* ⇒ 三条 `iso` 定理的 `2|2` 显式假设**已全部删除**。

✦ **改陈述的反例审查**（本项目纪律：改陈述前先造反例）：

* 新形状下 `q`、`q'` **都必须**带 `q_card`，故旧反例里的常函数 **`1|3` 选法不再可表达**
  ⇒ 旧反例失效；
* 对 binary 树，「被展示的 `2|2` split 在 4-元集上模 `swap` 唯一」
  （`Phylo/QuartetUnique.lean` 的 ★★★ `displaysSplitOn_unique`）⇒ 新形状**恰是**
  经典定理（Colonius–Schultze 1981 / Steel 1992）的忠实形式
  —— 两棵树「逐点一致」正是「quartet 系统相同」；
* `|X| ≤ 3` 时两侧假设自动空真，结论退化为「≤3 叶的 binary 树唯一」——
  这与**旧陈述完全相同**，不是本次改动引入的新风险。 -/

universe u v

variable {X : Type u} [Fintype X] [DecidableEq X]

open Classical in
/-- 「逐 quartet 一致」（模 `swap`）关系**对称**。 -/
theorem agreesWith_symm {q q1 : QuartetChoice X}
    (h : ∀ (S : Finset X) (hS : S.card = 4), q S hS = q1 S hS ∨ q S hS = (q1 S hS).swap) :
    ∀ (S : Finset X) (hS : S.card = 4), q1 S hS = q S hS ∨ q1 S hS = (q S hS).swap := by
  intro S hS
  rcases h S hS with h1 | h1
  · exact Or.inl h1.symm
  · refine Or.inr ?_
    have h2 : (q S hS).swap = ((q1 S hS).swap).swap := congrArg Split.swap h1
    rw [Split.swap_swap] at h2
    exact h2.symm

namespace Cladogram

/-- ★ **`DisplaysSplitOn` 对 `swap` 不变**（换成见证 split 的另一端）。

「`T` 在 `S` 上展示 `q`」当且仅当「展示 `q.swap`」—— 见证边 `s` 换成 `s.swap`
（`Cladogram.isSplitOf_swap`）。 -/
theorem displaysSplitOn_swap_iff {T : Cladogram.{u, v} X} {S : Finset X} {q : Split ↥S} :
    T.DisplaysSplitOn S q.swap ↔ T.DisplaysSplitOn S q := by
  constructor
  · rintro ⟨s, hs, hq⟩
    refine ⟨s.swap, T.isSplitOf_swap hs, fun x => ?_⟩
    have h0 : x ∈ q.sideB ↔ (x : X) ∈ s.sideA := hq x
    have hq' : x ∈ q.sideA ↔ ¬ (x ∈ q.sideB) := by
      rw [Split.mem_sideB_iff_not_mem_sideA]
      exact ⟨fun h => fun hc => hc h, fun h => by by_contra hc; exact h hc⟩
    simp only [Split.swap_sideA, Split.mem_sideB_iff_not_mem_sideA]
    exact hq'.trans h0.not
  · rintro ⟨s, hs, hq⟩
    refine ⟨s.swap, T.isSplitOf_swap hs, fun x => ?_⟩
    simp only [Split.swap_sideA, Split.mem_sideB_iff_not_mem_sideA]
    exact (hq x).not

/-- ★★ **桥的 `DisplaysQuartet` 层**：若 `q` 与 `q'` 逐点一致（模 `swap`）、`q` 是 `2|2`
且两者分别被 `T`、`T'` 展示，则 `T` 展示 `ab|cd` ⟹ `T'` 展示 `ab|cd`。

证明：把 `T` 的见证 split `s` 限制到 `S = {a,b,c,d}` 得 `q₀`（★ `Split.restrict`），
它在 `T` 上展示、且两侧各 2 个 `S`-元素（因为 `s.sideA ∩ S = {a,b}`）；
由 ★★★ `Cladogram.displaysSplitOn_unique` 得 `q₀` 与 `q S hS` 只差一个 `swap`，
于是 `q' S hS`（在 `T'` 上展示）也只差一个 `swap`，回到 `T'` 上即得 `ab|cd`。 -/
theorem displaysQuartet_of_agree {T T' : Cladogram.{u, v} X}
    {q q' : QuartetChoice X}
    (hq2 : ∀ (S : Finset X) (hS : S.card = 4), (q S hS).sideA.card = 2)
    (hdis : ∀ (S : Finset X) (hS : S.card = 4), T.DisplaysSplitOn S (q S hS))
    (hdis' : ∀ (S : Finset X) (hS : S.card = 4), T'.DisplaysSplitOn S (q' S hS))
    (hagree : ∀ (S : Finset X) (hS : S.card = 4),
      q S hS = q' S hS ∨ q S hS = (q' S hS).swap)
    {a b c d : X} (hcard : ({a, b, c, d} : Finset X).card = 4)
    (h : T.DisplaysQuartet a b c d) : T'.DisplaysQuartet a b c d := by
  classical
  obtain ⟨s, hs, hab, hcd⟩ := h
  set S : Finset X := {a, b, c, d} with hSdef
  have hScard : S.card = 4 := by rw [hSdef]; exact hcard
  have haS : a ∈ S := by rw [hSdef]; simp
  have hbS : b ∈ S := by rw [hSdef]; simp
  have hcS : c ∈ S := by rw [hSdef]; simp
  have hdS : d ∈ S := by rw [hSdef]; simp
  have haA : a ∈ s.sideA := hab (by simp)
  have hbA : b ∈ s.sideA := hab (by simp)
  have hcA : c ∉ s.sideA := fun hc =>
    (Finset.disjoint_left.mp s.disjoint_sides) hc (hcd (by simp))
  have hdA : d ∉ s.sideA := fun hd =>
    (Finset.disjoint_left.mp s.disjoint_sides) hd (hcd (by simp))
  have hInter : s.sideA ∩ S = {a, b} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxA, hxS⟩ := Finset.mem_inter.mp hx
      rw [hSdef] at hxS
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxS
      rcases hxS with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hxA fun hh => (Finset.disjoint_left.mp s.disjoint_sides) hh (hcd (by simp))
      · exact absurd hxA fun hh => (Finset.disjoint_left.mp s.disjoint_sides) hh (hcd (by simp))
    · intro x hx
      rw [Finset.mem_inter]
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haA
        · exact hbA
      · rw [hSdef]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> simp
  have hpair : ({a, b} : Finset X).card = 2 := by
    have hunion : ({a, b} : Finset X) ∪ ({c, d} : Finset X) = {a, b, c, d} := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hle := Finset.card_union_le ({a, b} : Finset X) ({c, d} : Finset X)
    rw [hunion, hcard] at hle
    have h2a : ({a, b} : Finset X).card ≤ 2 := by
      have hh := Finset.card_insert_le a ({b} : Finset X)
      simp only [Finset.card_singleton] at hh
      omega
    have h2b : ({c, d} : Finset X).card ≤ 2 := by
      have hh := Finset.card_insert_le c ({d} : Finset X)
      simp only [Finset.card_singleton] at hh
      omega
    omega
  have hcardA : (s.restrictSide S 0).card = 2 := by
    rw [Split.restrictSide]
    change (Finset.univ.filter (fun x : ↥S => (x : X) ∈ s.sideA)).card = 2
    rw [card_filter_subtype S (fun x => x ∈ s.sideA)]
    rw [Finset.filter_mem_eq_inter, Finset.inter_comm, hInter, hpair]
  have hAn : (s.restrictSide S 0).Nonempty :=
    Finset.card_pos.mp (by rw [hcardA]; norm_num)
  have hBn : (s.restrictSide S 1).Nonempty :=
    ⟨⟨d, hdS⟩, by
      simp only [Split.restrictSide, Finset.mem_filter, Finset.mem_univ, true_and]
      exact s.mem_sideB_of_not_mem_sideA hdA⟩
  let q₀ : Split ↥S := s.restrict S hAn hBn
  have hdis₀ : T.DisplaysSplitOn S q₀ :=
    ⟨s, hs, fun x => by
      simp only [q₀, Split.restrict, Split.restrictSide, Finset.mem_filter, Finset.mem_univ,
        true_and, Split.sideA]⟩
  have hcard₀ : q₀.sideA.card = 2 := hcardA
  have huniq : q₀ = q S hScard ∨ q₀ = (q S hScard).swap :=
    displaysSplitOn_unique hdis₀ (hdis S hScard) hScard hcard₀ (hq2 S hScard)
  have hdis₀' : T'.DisplaysSplitOn S q₀ := by
    rcases huniq with h | h
    · rcases hagree S hScard with he | he
      · rw [h, he]; exact hdis' S hScard
      · rw [h, he]; exact displaysSplitOn_swap_iff.mpr (hdis' S hScard)
    · rcases hagree S hScard with he | he
      · rw [h, he]; exact displaysSplitOn_swap_iff.mpr (hdis' S hScard)
      · rw [h, he, Split.swap_swap]; exact hdis' S hScard
  obtain ⟨s', hs', hq'⟩ := hdis₀'
  refine ⟨s', hs', ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxa | hxb
    · rw [hxa]
      exact (hq' ⟨a, haS⟩).mp (by
        simp only [q₀, Split.restrict, Split.restrictSide, Finset.mem_filter, Finset.mem_univ,
          true_and, Split.sideA]
        exact haA)
    · rw [hxb]
      exact (hq' ⟨b, hbS⟩).mp (by
        simp only [q₀, Split.restrict, Split.restrictSide, Finset.mem_filter, Finset.mem_univ,
          true_and, Split.sideA]
        exact hbA)
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxc | hxd
    · rw [hxc]
      refine s'.mem_sideB_of_not_mem_sideA fun hc => hcA ?_
      have := (hq' ⟨c, hcS⟩).mpr hc
      simpa only [q₀, Split.restrict, Split.restrictSide, Finset.mem_filter, Finset.mem_univ,
        true_and, Split.sideA] using this
    · rw [hxd]
      refine s'.mem_sideB_of_not_mem_sideA fun hd => hdA ?_
      have := (hq' ⟨d, hdS⟩).mpr hd
      simpa only [q₀, Split.restrict, Split.restrictSide, Finset.mem_filter, Finset.mem_univ,
        true_and, Split.sideA] using this

/-- ★★★ **桥**：`QuartetTree` 的「逐 quartet 一致」（模 `swap`）⟹ **quartet 系统相同**
（`SameQuartetSystem`，`DisplaysQuartet` 层）。 -/
theorem sameQuartetSystem_of_agree {qt qt' : QuartetTree.{u, v} X}
    (hagree : ∀ (S : Finset X) (hS : S.card = 4),
      qt.q S hS = qt'.q S hS ∨ qt.q S hS = (qt'.q S hS).swap) :
    SameQuartetSystem qt.tree qt'.tree := by
  intro a b c d hcard
  constructor
  · exact displaysQuartet_of_agree qt.q_card qt.displays qt'.displays hagree hcard
  · intro h
    exact displaysQuartet_of_agree qt'.q_card qt'.displays qt.displays
      (agreesWith_symm hagree) hcard h

/-- ★★★ **同一 quartet 系统 + binary ⟹ 相同的 split 系统**（收口第二步）。

由 ★★ `compatible_of_sameQuartetSystem` 得 `Σ(T) ∪ Σ(T')` 两两相容，
再用两棵树的**极大性** ★★★ `binarySplitsMaximal`（`T.IsBinary ⟹ T.SplitsMaximal`）
双向夹出 `Σ(T) = Σ(T')`。 -/
theorem isSplitOf_iff_of_sameQuartetSystem {T T' : Cladogram.{u, v} X}
    (hT : T.IsBinary) (hT' : T'.IsBinary) (h : SameQuartetSystem T T') :
    ∀ s : Split X, T.IsSplitOf s ↔ T'.IsSplitOf s := by
  intro s
  constructor
  · intro hs
    exact (binarySplitsMaximal X T' hT') s
      (fun t ht => compatible_of_sameQuartetSystem h hs ht)
  · intro hs
    exact (binarySplitsMaximal X T hT) s
      (fun t ht => (Split.compatible_comm s t).mpr (compatible_of_sameQuartetSystem h ht hs))

end Cladogram

/-- ★★★ **quartet 系统决定 binary 树**（**已证定理**，2026-10-08；不再是缺口）。

两棵 binary cladogram 若有相同的 quartet 系统（即每个 4-元集上「逐点一致」，模 `swap`），
则**同构**。

**证明**（三步拼接 + 退化基数，见文件头「✅ 收口」）：

1. 逐点一致 + `q_card` + `displays` ⟹ `SameQuartetSystem`（★★★ `sameQuartetSystem_of_agree`）；
2. + 两棵树 binary ⟹ 相同 split 系统（★★★ `isSplitOf_iff_of_sameQuartetSystem`）；
3. 相同 split 系统 ⟹ 同构：
   * `3 ≤ |X|`：`Phylo/SplitsDetermineTree.lean` 的 ★★★ `Cladogram.iso_of_isSplitOf_iff`
     （Semple & Steel §3.8 的同构版；核心是把「簇包含」化归为**路径祖先关系**）；
   * `|X| ≤ 2`：`Phylo/SplitsDetermineTreeBase.lean` 的 ★★ `Cladogram.iso_of_card_le_two`
     （退化情形：`|X| = 0` 唯一顶点 · `|X| = 1` 不存在 cladogram · `|X| = 2` 必是两点一边）。

✦ **经典已证定理**（Colonius–Schultze 1981 / Steel 1992；教科书 Semple & Steel §6.4），
**非**学术开放问题；本库先前把它写成 `def … : Prop` 缺口，**2026-10-08 补齐**。

✦ **`2|2` 条件在 `QuartetTree.q_card` 字段里**（T0.6 治本），故此处不必再传。 -/
theorem QuartetDecidesTree (X : Type u) [Fintype X] [DecidableEq X]
    (qt qt' : QuartetTree.{u, v} X)
    (hb : qt.tree.IsBinary) (hb' : qt'.tree.IsBinary)
    (hagree : ∀ (S : Finset X) (hS : S.card = 4),
      qt.q S hS = qt'.q S hS ∨ qt.q S hS = (qt'.q S hS).swap) :
    Nonempty (Iso qt.tree qt'.tree) := by
  have hsplit := Cladogram.isSplitOf_iff_of_sameQuartetSystem hb hb'
    (Cladogram.sameQuartetSystem_of_agree hagree)
  by_cases hcard : 3 ≤ Fintype.card X
  · exact Cladogram.iso_of_isSplitOf_iff hcard hsplit
  · exact Cladogram.iso_of_card_le_two (by omega)

/-! ## 下游收口：从「逐 quartet 一致」升级到「树同构」（**无条件**） -/

/-- ★★★ **ASTRAL 恢复真树的拓扑**（**无条件**）。

由 `astral_maximizer_agrees`（ASTRAL 输出与真树逐 quartet 一致）
+ ★★★ `QuartetDecidesTree`。`2|2` 条件现为 `QuartetTree.q_card` 字段，故**不必再传**。 -/
theorem astral_iso (m : MSCFreq.{u, v} X) (hT : m.tree.IsBinary)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (h : IsASTRAL m.freq qt) : Nonempty (Iso qt.tree m.tree) :=
  QuartetDecidesTree X qt m.toQuartetTree hqt hT fun S hS => astral_maximizer_agrees m h S hS

/-- ★★★ **多标记 ASTRAL 恢复真树的拓扑**（同 `astral_iso`，经 `multiLocus_isASTRAL`）。

⚠️ 本定理是**多标记 ASTRAL**（跨标记求和）的收口，**不是 CASTER**（真 CASTER 见
`Phylo/Stat/CASTERJC69.lean` 等）。原名 `caster_iso`，2026-10-08 批 W8a 更名。 -/
theorem multiLocus_iso (m : MSCFreq.{u, v} X) (hT : m.tree.IsBinary) (M : MultiMarkerFreq X)
    (hM : M.avg = m.freq)
    {qt : QuartetTree.{u, v} X} (hqt : qt.tree.IsBinary)
    (h : ∀ qt1 : QuartetTree.{u, v} X, multiLocusScore M qt1.q ≤ multiLocusScore M qt.q) :
    Nonempty (Iso qt.tree m.tree) :=
  astral_iso m hT hqt (hM ▸ (multiLocus_isASTRAL M).mp h)

/-- ★★★ **parsimony 恢复真树的拓扑**（在**位点采样** `SiteSampling` 下）。

由 `parsimony_statisticallyConsistent`（最简树 ⟹ 逐 quartet 一致）+ ★★★ `QuartetDecidesTree`。

⚠️ 本定理**依赖采样结构 `sm`**（**不是**无条件）。 -/
theorem parsimony_iso (M : MSCSite.{u, v} X) (hT : M.tree.IsBinary) (sm : SiteSampling.{u, v} X)
    {E : SiteSupport X → QuartetTree.{u, v} X} (hE : ∀ D, IsParsimony D (E D))
    (hEbin : ∀ D, (E D).tree.IsBinary)
    (hNE : ∃ q : QuartetChoice X, ¬ AgreesWith M.q q) :
    ∃ N : ℕ, ∀ n ≥ N, Nonempty (Iso (E (sm.emp M n)).tree M.tree) := by
  obtain ⟨N, hN⟩ := parsimony_statisticallyConsistent M sm hE hNE
  exact ⟨N, fun n hn =>
    QuartetDecidesTree X (E (sm.emp M n)) M.asQuartetTree (hEbin (sm.emp M n)) hT (hN n hn)⟩

/-! ## 树层统计一致性（落在采样谓词 `StatisticallyConsistent` 上） -/

/-- ★★★ **ASTRAL 的树层统计一致性**：`MSCSampling` 修正后，本库叙事上的**树层**一致性谓词
`StatisticallyConsistent` 对 **ASTRAL 型**估计量**真的成立**（不再空洞）。

* 先引 `Stability.astral_statisticallyConsistent`（**quartet 层**，在 `MSCSampling` 上）；
* 再用 ★★★ `QuartetDecidesTree`（quartet 一致 ⇒ **树同构**）升到树层
  —— 与 `parsimony_iso` 的收口方式相同。 -/
theorem astral_statisticallyConsistent_iso (sm : MSCSampling.{u, v} X)
    {Q : QuartetFreq X → QuartetTree.{u, v} X} (hQ : ∀ D, IsASTRAL D (Q D))
    (hQbin : ∀ D, (Q D).tree.IsBinary)
    (hT : ∀ m : MSCFreq.{u, v} X, m.tree.IsBinary)
    (hNE : ∀ m : MSCFreq.{u, v} X, ∃ q : QuartetChoice X, ¬ IsTrueChoice m q) :
    StatisticallyConsistent (fun D => (Q D).tree) sm := by
  intro m
  obtain ⟨N, hN⟩ := astral_statisticallyConsistent m sm hQ (hNE m)
  exact ⟨N, fun n hn =>
    QuartetDecidesTree X (Q (sm.emp m n)) m.toQuartetTree (hQbin _) (hT m) (hN n hn)⟩
