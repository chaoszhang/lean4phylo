# lean 项目 · MEMORY

## 项目

NJ cherry 引理形式化（Lean 4 + Mathlib）

- 源码正本（Windows）：`C:/Users/ASTER/WorkBuddy/Project/lean/`
- 构建目录（WSL 原生盘）：`~/nj-lean`（Linux 侧，需手动 `cp` 同步）
- 工具链：elan → `leanprover/lean4:v4.35.0-rc3` + mathlib4(master)，已 `lake exe cache get`
- lake 路径：`/home/chaos/.elan/bin/lake`

## 当前状态（2026-09-29，第 2 轮收口）

- ✅ `lake env lean NJ/Cherry.lean` 通过（全量 `import Mathlib`，约 3.5–5.5min；开发期最小导入 ~5s）
- ✅ 已机器验证：`Q_eq_neg_two_ell`/`Q_eq_neg_two_z`、`max_at_cherry`、`nj_cherry`
- ✅ 新增辅引理：`triangle`（四点条件⟹三角不等式）、`rho_nonneg`、`ell_eq_sum_rho`、  
  `two_mul_z`、`z_hinge`（门控恒等式）
- ⬜ **唯一剩余 `sorry` = `max_z_cherry_core`**（★ 硬核）  
  —— `max_at_cherry` 已完全由它推出（`k≠l` 归约、`k=l` 用 triangle）

## 加速技巧（重要）

- 开发期把 `import Mathlib` 换成最小导入集，编译 **~5s/次**：
  ```
  import Mathlib.Data.Real.Basic
  import Mathlib.Algebra.BigOperators.Field
  import Mathlib.Algebra.BigOperators.Ring.Finset
  import Mathlib.Data.Fintype.Card
  import Mathlib.Data.Finset.Card
  import Mathlib.Tactic
  ```
  交付前换回 `import Mathlib`。

## 编译命令

```bash
wsl -e bash -lc 'cd ~/nj-lean && cp /mnt/c/Users/ASTER/WorkBuddy/Project/lean/NJ/Cherry.lean NJ/Cherry.lean && ~/.elan/bin/lake env lean NJ/Cherry.lean'
```

## max_at_cherry 的数学现状（本轮分析）

- 定理：`FourPoint δ` + `(a,b)` 最大化 `z:=δ+ℓ` ⟹ `IsCherry δ a b`。
- **数值验证**：随机 4000 棵正权树（n=4..8），argmax z 恒为樱桃（0 反例）→ 定理成立。
- 关键恒等式：`z(i,j) = ½(A_i + A_j + (2-n)δ_ij)`，`A_x = Σ_k δ_xk`；等价于 `Q = -2z`。
- **已排除的朴素思路**（均数值反例）：
  - “最近距离对是樱桃”——假（1822 反例）。
  - “局部 quartet 分裂 ui|vj ⟹ z(u,i)≥z(u,v)”——假（局部信息不够，需全局耦合）。
  - “(u,v) 非樱桃 ⟹ ∃m, z(u,m)>z(u,v)”——假。
- 标准证明（Weller 2023「leaf-status」/ Pachter–Sturmfels 定理 2.38 / MLP 2006）都**显式用树**：取中心节点 c、沿路径的 leaf-status 单调性、子树内必存在樱桃、递归到更大 z 的对。
- **结论**：纯度量（Route A，仅用 FourPoint）的干净证明尚未找到，且标准证明依赖树结构；Route B（引入 `WeightedTree`）需要 Buneman 存在性（四点条件 ⟹ 存在实现树），这是一个独立大定理。
- Mathlib **无** 系统发生/树度量 API（只有 `SimpleGraph` 树）。

## 参考文献

Weller 2023 (arXiv:2305.18866, leaf-status); Pachter–Sturmfels, *Algebraic Statistics for Comp. Bio.* Thm 2.38; Mihaescu–Levy–Pachter 2006 (arXiv:cs/0602041); Saitou–Nei 1987; Studier–Keppler 1988.

## 研究脚本

`C:/Users/ASTER/WorkBuddy/Claw/temp/nj_explore*.py`（数值探索：定理验证 + 候选引理证伪）


## 远期目标与库设计（2026-10-02）

**远期目标**：建立**所有 phylogeny 经典算法证明的库**（Lean 4 + Mathlib）。

**Mathlib 图/树设施调研结论（grep 实证）**

- 可复用：`SimpleGraph` / `Walk`(Decomp·Subwalks·Maps·Traversal) / `IsTree`(extends Connected) / `Subgraph` / `Connected` / `Dart` / `AdjMatrix`·`IncMatrix`·`LapMatrix` / `Matroid/`(graphic matroid) / `Data/Sym/Sym2`(无序对) / `Finset.powersetCard` / `Setoid.Partition` / `Matrix`。
- ⚠️ `SimpleGraph.dist : V → V → ℕ` 是**无权重** BFS 距离；加权路径长须自建。
- ❌ 完全缺失：加权树、树度量、四点条件、Buneman、split、quartet、RF、NNI/SPR、溯祖。

**已定设计决策**

1. **树底层 = 自定义接口包 SimpleGraph**（对外 phylogeny API，内部 SimpleGraph + 权函数）。→ 现有 `TreeRealization` 未来需按此重构。
2. **起步 = 先备树零件**（叶 / 樱桃 / 子树 / quartet / split），算法无关。
3. **split 表示 = 建「划分族」，自定义 `Partition` 作共享基础（2026-10-02 定，取代旧 1a）**：
   ```lean
   structure Partition (X) (n : ℕ) where      -- 注意：与 Mathlib `Partition` 撞名，建议改名 KPartition
     parts : Fin n → Finset X
     disjoint : Pairwise (Disjoint on parts)
     union : Finset.univ.biUnion parts = Finset.univ
     nonempty : ∀ i, (parts i).Nonempty
   abbrev Split (X) := Partition X 2          -- 二分专用 API（兼容性 / Buneman）
   ```
   - Tri/Quadripartition **各自语义化**（删顶点 vs 删 k−1 边语义不同，不硬塞 `kPartition`）。
   - 旧「1a 两侧都存」**作废**；`Split` 用 `Fin 2` 索引会把两侧有序化 → 判等需商置换（配 `Split.swap`）。
   - ⚠️ Mathlib 已有 `Partition α`（`Order/Partition.lean`，`Set (Set α)`，任意多块）→ `open` 即撞名，开工前先定名（建议 `KPartition`）。
4. **quartet / triplet 表示 = 集合 + split（拓扑分离，2026-10-02 定）**：
   - **quartet = 4 元叶集（就是 set）**；**quartet topology = 支撑集 + `Split ↥S`**（2|2 分裂）；**triplet topology 同构**（3 元集 + 2|1）。
   - 统一：`structure Topology (S : Finset X) where part : Split ↥S`；`QuartetTopology` / `TripletTopology` 各加 `card` 约束。
   - ⚠️ **连带约束：`Partition`/`Split` 的底必须参数化在任意类型 `α`（`Partition (α) (n)`），否则 `Split ↥S` 写不出**。
   - **triplet 属 rooted 层**（`ab|c` 的 `c` 是外群，无根树上 3 叶只有 1 种拓扑）；quartet 属无根层。
   - 支撑集最佳表示：`{ S : Finset X // S.card = 4 }`（`Sym X 4` 是 Multiset 商、允许重复，需额外 Nodup，绕）。
   - 旧 A（`Finset`+选一对）采纳其精神并升级；B（`Sym2(Sym2 X)`）❌；C（自定义 `Quartet` structure）被 `Topology S` 取代。
5. **加权结构 = 三层（2026-10-02 定）**：
   - **第 1 层 `Cladogram`（纯拓扑，= 现有 `PhyloTree`）✅必备**；**第 2 层 `Phylogram`（+ 可加边权 `w`，`dist = Σ路径 w`）✅必备**；**第 3 层 `AnnotatedTree`（+ 任意标注）⬜待定**（留口子，不预付成本）。
   - 用 `extends` 递进：`Phylogram extends Cladogram` → 免费继承全部拓扑引理，第二层只加 `w` + `w_nonneg`。
   - **与「可加性分界」对齐**：Cladogram 无权重 / Phylogram 可加侧（→ 树度量）/ Annotated 标注侧（→ wRF·KF·支持度）。
   - **chronogram = Phylogram + ultrametric 约束**（不单开一层，用谓词）。
   - 文献是「同一拓扑的 3 种 facet」（cladogram/phylogram/chronogram 并列），老师的三层是**结构性包含**，两者不同维度不冲突。
   - 对既有代码影响：`NJ/CherryTree.lean` 的 `TreeRealization`（带 `d`）= **Phylogram 的距离投影**，将来 `d` 应变成定理而非字段。
   - **边权底层 = `E → ℝ`（2026-10-02 老师定，原话「E → ℝ 感觉自然」）**：**子路线 A 已选（老师「A」）** —— `E` **派生** `E := {e : Sym2 V // e ∈ graph.edgeSet}`（零维护，= Mathlib `SimpleGraph.edgeSet : Set (Sym2 V)`）；子路线 B（独立 `E` 字段 + `edgeEquiv`）留将来升级。「非边为 0」的 `Sym2 V → ℝ` 版本可作 helper。
6. **树相等 = A 作定义 + C 作定理（2026-10-02 老师定）**：
   - **定义用 A**：`Iso`（保标号同构，identity on X）——**白蹭 Mathlib `SimpleGraph.Iso`（`Maps.lean:307`，`abbrev Iso := RelIso G.Adj G'.Adj`，记法 `G ≃g G'`）**，只需补 `leaf_compat` + `w_compat`。
   - **C 降格为定理**：`Nonempty (Iso T T') ↔ splits T = splits T'` = **Splits-Equivalence 定理**（Semple-Steel Thm 3.1.4；Olds-Sullivant Thm 2.5：「Σ 相容且含平凡 split ⟺ ∃T，且 T 由 Σ(T) 唯一确定」）。同时也是 §5 第 10 条「首批大目标」之一。
   - B（`Quot` 商类型）不采。文献口径：MathWorld/Semple-Steel「fixes every leaf label」、Steel-Székely「label-preserving graph isomorphism」、Steel 2014「identity on X」。
   - **实操**：多数引理陈述在「同一 `V` 同一 `graph`」上用 `=`；只在跨树比较（RF/MAST/共识/树空间）用 `Iso`。
7. **restriction（`T|Y`）= 定义为映射、方案 C（`suppress`）（2026-10-02 老师定）**：
   - **Cladogram 与 Phylogram 各有一份 `restrict : T → (Y : Finset X) → T ↥Y`**（老师补充「两层都能定义为映射」）。
   - **Cladogram 侧**：诱导子树 + 抑制所有度 2 顶点（纯拓扑，无规则）。
   - **Phylogram 侧**：抑制时**两条边合并、边权相加** ⟸ 可加性；核心定理 `restrict_dist`（保 Y 内叶对距离）——这正是「为什么必须相加」的证明义务。
   - 兼容性引理：`(T.restrict Y).toCladogram = T.toCladogram.restrict Y`。
   - **强耦合 §3.2**：`no_degree_two` 是 `Cladogram` 字段 ⟹ `T|Y` 必须抑制才能同类型；放松 `Cladogram` 会动摇 §3.8-C 唯一性 → 故必须真做 `suppress`。
   - **第三层 `AnnotatedTree` 的 restriction 规则未定**（标注不可加，「合并边时标注怎么办」无唯一答案）——「restriction 可定义性」本身即「可加 vs 标注」分界的又一体现。
8. **binary = 一般树 + `IsBinary` 谓词（2026-10-02 老师定方案 B）**：
   - `def IsBinary (T : Cladogram X) : Prop := ∀ v, ¬ IsLeaf v → T.graph.degree v = 3`（无根；rooted 版 out-degree 恰 2 待 rooted 层）。
   - **需要 binary 时两种写法**（老师补充「取别名或特殊处理」）：**别名** `abbrev BinaryCladogram X := { T : Cladogram X // T.IsBinary }`（当对象传递，如 `NJ : Dissimilarity → BinaryPhylogram`）；**特殊处理** `section` + `variable (hT : T.IsBinary)`（只影响假设、签名不重复）。
   - `IsBinary` 是纯拓扑概念，与边权无关（`w=0` 内边是 polytomy 但拓扑上仍 binary）。
9. **首批大目标 = Splits-Equivalence → Buneman（2026-10-02 老师定：「这个必须证」）**：
   - **Splits-Equivalence**：Σ（X-splits）两两相容 ⟺ 存在树 T 使 `Σ = Σ(T)`，且 T 同构唯一（Semple-Steel Thm 3.1.4，原 Buneman 1971）。证明 = 归纳 + **劈顶点**（关键引理：存在 v 使 `T'∖v` 每个连通块叶集 ⊂A 或 ⊂B；用**染色+极值点**证）——**就是 BUILD 算法（Aho et al. 1981）的种子**。工作量「大而常规」，比 `max_z_cherry_core` 好啃。
   - **Buneman** 建在其上（四点条件 ⟺ 树度量）；顺带给 `NJ/CherryTree.lean` 的 `TreeRealization` 假设转正。
   - **quartet 版等价描述（老师补充）**：`(n choose 4)` 个 quartet 决定 **binary** 树（Colonius-Schultze 1981 / Bandelt-Dress 1986），**与 split 版平行**；但**判据形态不同**：**无两两判据**（split 有）、full 情形用**推理规则** `ab|cx ∧ ab|xd ⟹ ab|cd`（Colonius-Schultze，多项式）、一般情形 **NP-complete**（Steel 1992）、thin（每 k 元子集 ≤ k−3 个 quartet）⟹ 相容（充分）。⇒ **quartet 相容性只能作算法目标/存在性命题，不能当判据或定义**。
   - **§5 全部 10 条已定，`CONCEPTS.md` 设计阶段收口。**
10. **落地路线（`CONCEPTS.md` §4，2026-10-02）**：

- **Mathlib 支撑点**：★ `SimpleGraph/Acyclic.lean:240` **`isTree_iff_existsUnique_path`（树 ⟺ 路径唯一 = M0 地基）**；`Acyclic.lean:512` `IsTree.exists_ne_and_degree_eq_one`；`Maps.lean:307` `Iso := RelIso G.Adj G'.Adj`；`G.edgeSet`；`G.degree`。❌ `SimpleGraph.dist` 是无权 BFS(`ℕ`)，**加权距离必须自建**。
- **里程碑**：M0 树载体 → M1 加权层+同构 → **M2 Splits-Equivalence ★** → **M3 Buneman** → M4 quartet/triplet → M5 算法。
- **目录**：**新库 `Phylo/`**（`Core.lean`/`Split.lean`/`Metric.lean`/`Quartet.lean`/`Algorithm/*` + 根模块 `Phylo.lean`）；**现有 `NJ/Cherry.lean`、`NJ/CherryTree.lean` 保留为独立文件**（库与算法分离）。
- **第一步 M0**：新建 `Phylo/Core.lean` → 写 `Cladogram` → `IsLeaf`+四条引理 → `lake env lean` 迭代 → **停下汇报接口**（M0 跑通再确认节奏）。

1. **工程骨架（`SCAFFOLD.md`，2026-10-02）**：

- 调研源：官方 `lake new`/`lake init . math`；**`leanprover-community/physlib`（领域库范例）**；`LeanProject` 模板。
- 骨架：补 `lean-toolchain`（`v4.35.0-rc3`）+ `.gitignore` + `.vscode/` + `.github/workflows/build.yml` + `scripts/check_file_imports.lean`；`lakefile.toml` 加 `[[lean_lib]] name = "Phylo"`。
- **四条规矩**：文件头三件套（版权+import+`/-! # 模块描述 -/`）；每定义带 docstring；根模块按字母序 import + 自动检查；**开发期 `-Dwarn.sorry=false`**（PhysLib 做法，让含 sorry 的库照常编译）。
- **暂不采纳**：Blueprint、PhysLib 的 informal/semiformal 追踪、Alpha 双库。
- ⚠️ **命名（2026-10-02）**：原拟 `Nj` **不可用** —— **Windows 文件系统大小写不敏感**（实测 `ls -d nj` 匹配 `NJ/`），`Nj/` 会与现有 `NJ/` 撞目录。**最终命名（老师提议）：仓库/包名 `lean4phylo`（双关：Lean 4 phylo / lean for phylo），Lean 库名 `Phylo`（PascalCase）**。**铁律：库目录名不得与 `NJ` 仅差大小写。**
- `leanprover-community/LeanProject` 评估：**部分有用，取零件** —— ✅ 取 `build-project.yml`/`.vscode`/`.gitignore`/**`Phylo/Mathlib/` 缺声明层**/`scripts`；🔶 **Blueprint 体系**（其产物 = 定义·定理·证明状态 + 依赖图网站，**正是我们引理树的正式版**）暂缓但留位置；❌ 不取 upstreaming dashboard / Jekyll。

---


## 工程落地（2026-10-02）

- **项目根**：`C:/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/`（老师指定「全部在这里搭建」）。
- **WSL 构建目录**：`~/lean4phylo`；**`.lake/packages` 软链到 `~/nj-lean/.lake/packages`**（复用 7.2G mathlib 缓存，不复制）。
- **已落地**：`lakefile.toml`(name=lean4phylo, lean_lib Phylo) / `lean-toolchain`(v4.35.0-rc3) / `.gitignore` / `.vscode/` / `.github/workflows/build.yml` / `scripts/check_file_imports.sh` / `README.md` / 设计文档(CONCEPTS·SCAFFOLD·MEMORY)。
- **M0 完成** ✅：`Phylo/Core.lean` 编译通过（`lake build` 1218 jobs OK，仅 module-system 无害提示）。
  - `structure Cladogram`：`V` / `fintypeV` / `decEqV` / `graph` / `decAdj` / `isTree` / `leaf : X ↪ V` / `leaf_iff_degree_one` / `no_degree_two`。
  - 基础引理：`IsLeaf`、`leaf_injective`、`leaf_eq_iff`、`isLeaf_iff_degree_eq_one`、`IsLeaf.degree_eq_one`、`degree_eq_one_isLeaf`、`IsLeaf.degree_ne_two`、**`existsUnique_path`**（调 `isTree_iff_existsUnique_path`）。
- **⚠️ Lean 4 语法坑（记）**：structure 里**匿名实例字段 `[Fintype V]` 写在 `V : Type*` 之后会报 `unexpected token ']'`** —— 必须用**命名实例字段** `fintypeV : Fintype V` + `attribute [instance] Cladogram.fintypeV …`。
- **⚠️ Lean 4 坑**：`Nat.one_ne_two` 不存在 → 用 `by decide`。
- **同步命令**（Windows 正本 → WSL 构建）：
  ```bash
  cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/{lakefile.toml,lean-toolchain,Phylo.lean} ~/lean4phylo/
  cp -r /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo/Phylo/* ~/lean4phylo/Phylo/
  cd ~/lean4phylo && ~/.elan/bin/lake env lean Phylo/Core.lean   # 单文件 ~9s
  ```
- **M1 进度（2026-10-02，进行中）**：
  - ✅ `Edge`（`E` 派生自 `edgeSet`，子路线 A）
  - ✅ `Phylogram extends Cladogram`（`w : Edge → ℝ` + `w_nonneg`）· `w_nonneg'` · `w_mem`
  - ✅ `wExt`（非边取 0 的技术扩展）· `walkDist`（`Walk` 边权和，用 `Walk.edges : List (Sym2 V)`）· **`dist`**（唯一路径权和，可加性化身）· `dist_self`
  - ✅ `Iso`（`SimpleGraph.Iso` + `leaf_compat`）· `refl` · `symm`
  - ⬜ 剩：`restrict`（`suppress` + 边权相加 + `restrict_dist`）· `splits`
  - `lake build` → **1258 jobs 通过**（仍仅 module-system 无害提示）
- **Lean 4 坑（M1 新踩）**：
  - ① `Mathlib.Data.Real.Basic` **已弃用** → 改 `import Mathlib.Basic.Real.Basic`（否则只报 `OfNat ℝ 0` 失败，很难定位）。
  - ② `SimpleGraph.Iso.refl` 是**无参** abbrev（靠期望类型推断），不接 `G` 参数；`RelIso.refl` 才接关系参数。
  - ③ `∃! p, P p` 的 `.choose_spec` 类型是 `P choose ∧ (∀ y, P y → y = choose)` —— 唯一性在 `.2`，用它比用 `ExistsUnique.unique` 省事。
  - ④ `Phylogram extends Cladogram` 后**不必**重新注册实例 —— `Cladogram.fintypeV` 等已注册为 instance，沿 `toCladogram` 自动找到（但 `attribute [instance] Phylogram.toCladogram` 会报错：返回值不是 type class）。
- **restrict 进度（2026-10-06）**：地基已完成并编译通过 ——
  - `pathVerts`（两点唯一路径的顶点集）· `spanVerts`（连接 `Y` 的顶点集，`Y.biUnion`）· `leaf_mem_spanVerts` · `inducedSubgraph`（**白蹭 `SimpleGraph.induce`**，它即 `comap`）。
  - ⬜ 剩 **`suppress`**（删度 2 顶点 + 合并边）—— 大工程：要造新顶点类型 + 新图 + 三条结构证明（`IsTree` / `leaf_iff_degree_one` / `no_degree_two`）。
- **⚠️ 发现更短路径（待老师定）**：文献定义 restriction 的标准方式是 **split 层面** ——  
  `Cl(T|Y) = {C ∩ Y : C ∈ Cl(T), C ∩ Y ≠ ∅}`（Bryant–Steel；Semple & Steel §3.9）。  
  ⇒ **先做 `Split` 类型 + `splits : T → Finset (Split X)`（M2 前置），restrict 直接定义在 split 上，不必造新树**；且 `splits` 本来就是 M2（Splits-Equivalence）的必备地基，一举两得。
- **M2 进度（2026-10-06）**：`Phylo/Split.lean`（282 行）编译通过，**无 sorry** ——
  - 结构：`KPartition α n` · `Split α := KPartition α 2` · `sideA`/`sideB`/`disjoint_sides`/`union_sides` · **`Split.swap`**（`i ↦ i+1`，即 `Fin 2` 模 2 加法）+ `swap_sideA`/`swap_sideB`
  - 相容性：**`Split.Compatible`**（四个交至少一空）+ `compatible_comm`
  - restriction（route B 核心）：`restrictSide` / `disjoint_restrictSide` / **`Split.restrict`**（`A|B ↦ (A∩Y)|(B∩Y)`）——**定义在 split 层面，不造新树**
  - 树 → split：`sideLeaves`（**`Reachable` 版**）· `mem_sideLeaves` · **`not_reachable_deleteEdges_of_adj`（★ 树中每条边都是桥 —— 白蹭 `isAcyclic_iff_forall_adj_isBridge` + `isBridge_iff`）** · `not_mem_sideLeaves_of_adj` · `mem_sideLeaves_self` · `isIsolated_leaf_deleteEdges` · **`sideLeaves_leaf_edge`（叶边 → 平凡 split `{x}`）** · `splitOfEdge` · `IsSplitOf` / `splits` / `PairwiseCompatible`
  - 自建 helper：`reachable_eq_of_isIsolated`（孤立点只与自身可达；将来迁 `Phylo/Mathlib/`）
  - `lake build` → **1259 jobs 通过**；`check_file_imports.sh` 通过
  - ⬜ 剩：**Splits-Equivalence 定理**（见下）
- **Splits-Equivalence 证明路线（已推演，待实现）**：设 e₁=⟦a,b⟧、e₂=⟦c,d⟧，A={x | x ~₁ a}（~₁ = `T-e₁` 中可达）。
  - **K1**：`c,d` 同在 `T-e₁` 的**同一**分量（因 `T.Adj c d` 且 e₂≠e₁）。
  - **K2**（关键）：若连通集 `S` 不含 e₂ 的端点，则 `S` 含于 `T-e₂` 的**一个**分量内（S 在 T-e₂ 中仍连通）。
  - **推论**：`S := a 在 T-e₁ 中的分量`若不 ∋ c,d，则 `A ⊆ A'` 或 `A ⊆ B'` ⇒ 四个交之一为空 ⇒ **相容**。两类情形（c,d 在 b 侧 / 在 a 侧）分别给出 `A∩A'`/`A∩B'` 与 `B∩B'`/`B∩A'` 之一为空。
  - 实现要点：需「可达类」的传递性 + 「从 T-e₁ 的 walk 避开 e₂ 端点 ⇒ 也是 T-e₂ 的 walk」。属**可做但工程量大**。
- **★ Splits-Equivalence「树 ⟹ 相容」方向已完成（2026-10-06）** ✅
  - **主定理 `Cladogram.pairwiseCompatible`（在根 namespace，签名 `(T : Cladogram X) : T.PairwiseCompatible`）**：
    > 树的 split 系统两两相容。
  - 支撑引理链（全部编译通过、无 sorry，`Phylo/Split.lean` 630 行）：
    1. `Phylo/Mathlib/Walk.lean`（61 行）：**★ `reachable_deleteEdges_of_support_notMem`**（连通集避开某边 ⇒ 仍连通）· `reachable_of_mem_support` · `start_mem_adj_edge`
    2. 相容性接口层：`sideB_eq_sdiff` · `compatible_of_subset_left/_right/_disjoint/_union` · `compatible_of_sides`（在 `namespace Split` 内）· **`SidesCompatible`** · **`sidesCompatible_compl_left`（相容性对补侧不变，四项轮换）**
    3. 同侧关系：`inSide` + self/comm/trans · `mem_sideLeaves_iff_inSide` · `not_inSide_both` · **`sideLeaves_compl_adj`**（`sideLeaves e b = (sideLeaves e a)ᶜ`）· **`sideLeaves_eq_of_inSide`**（同侧基准可换）
    4. **★ `inSide_congr_of_adj`（关键观察）**：相邻且 ⟦c,d⟧ ≠ e₁ ⟹ c,d 在 e₁ **同侧**
    5. `eq_of_adj_of_not_inSide` · **`inSide_deleteEdges_of_inSide`（旁侧连通性，用 `Walk.mapLe` + `support_mapLe_eq_support`）** · **`inSide_or_inSide`（2 类性，用 `Walk.recOn` + 显式 motive）**
    6. **`sidesCompatible_sideLeaves_of_not_inSide`（情形 1）** · **`sidesCompatible_sideLeaves`（一般情形：用关键观察压成 2 情形，情形 2 经补侧轮换化归情形 1）**
  - `IsSplitOf` 最终形态：`∃ (a b : T.V) (_ : T.graph.Adj a b) (u : T.V), s.sideA = T.sideLeaves s(a,b) u`  
    （**以相邻点对给出**，等价于 `edgeSet` 但省去从 `Sym2` 提取端点 —— `SimpleGraph.mem_edgeSet` 只给「三角边 ↔ Adj」，不适合反向提取。）
- **⬜ 剩余：Splits-Equivalence 的另一半「相容 ⟹ 存在树」** —— **入口已铺好（2026-10-06）**：
  - ✅ 集合层面：`sidesCompatible_comm` · `sidesCompatible_compl_right` · **★ `laminar_of_sidesCompatible_of_notMem`（相容 + 避开 `ρ` ⟹ 嵌套或相离）** · `LaminarFamily` · `laminarFamily_of_pairwise`
  - ✅ `Split` 层面：**`compatible_iff_sides`（`Compatible ⟺ SidesCompatible`，双向）** · `mem_sideB_iff_not_mem_sideA` · `sideB_eq_compl` · **★ `Split.cluster`（避开 `ρ` 的规范一侧）** + `notMem_cluster` / `cluster_eq_sideA_or_compl` · `sidesCompatible_cluster` · **`laminar_of_compatible_clusters`**
  - ✅ **平凡 split 必被展示**：`exists_isSplitOf_singleton`（`Σ(T) ⊇ Σ_triv`，用 `sideLeaves_leaf_edge`）
  - `Phylo/Split.lean` → **784 行**；`lake build` 1260 jobs；无 sorry
- **路线（下一步）**：**「相容 ⟹ 存在树」的标准构造** ——
  1. 固定 `ρ`，取 Σ 的规范 cluster 族 `{s.cluster ρ}`（**全部避开 `ρ`，故两两镶嵌**：`laminar_of_compatible_clusters` 已证）。
  2. 在**镶嵌族**上建树：顶点 = 簇（+ 元素）；父 = 最小严格包含者（`IsParentOf` 已落地）。  
  3. 证 `Σ(T) = 规范 cluster 诱导的 split 集`。  
     （替代路线：Semple–Steel 的**劈顶点引理** —— 存在顶点 `v` 使 `T∖v` 各连通块叶集 ⊂ A 或 ⊂ B；染色 + 极值点。）
- **⚠️⚠️ 设计卡点（2026-10-06）：连通性需根 vs `no_degree_two`** —— **已定位根因并攻下大半（2026-10-06 晚）**：
  - **根因（两条）**：
    1. **`ρ ∉ ⋃F` 时元素孤立** ⟹ 图不连通（须加 `univ` 作根）；
    2. **单元素簇 `{x}` 与叶 `x` 重复**（它们本是同一条**叶边**）⟹ 度 2 顶点。
  - **修正构造**：`normFinset F := insert univ (F.filter (2 ≤ ·.card))` —— **删单元素簇 + 加根** ✓ 已实现（`Phylo/Laminar.lean`）。
  - **★ 已证 `three_le_degree_of_ne_univ`**：正规化后 **`A ≠ univ` ⟹ `degree(inl A) ≥ 3`** ✓✓
    - 邻居三分（互不相交）：**父**（`A ≠ univ` ⟹ 存在）· **孩子**（`IsChildOf`）· **直接元素**（`directElems`）
    - **★ 核心计数 `two_le_card_children_add_card_directElems`：`|kids| + |dirs| ≥ 2`**
      - `k = 0`：`A` 无真子集 ⟹ 每个 `t ∈ A` 的最小簇就是 `A` ⟹ `A ⊆ directElems` ⟹ `|dirs| ≥ |A| ≥ 2`
      - `k = 1`（孩子 `B`）：`B ⊊ A` ⟹ 取 `t ∈ A∖B`；若 `t` 非直接元素，则另有含 `t` 的孩子 `≠ B`，与 `k = 1` 矛盾
      - `k ≥ 2`：显然
    - 前置：**`exists_isChildOf` / `exists_isChildOf_mem`（极大真子集存在性，用 `Finset.exists_mem_eq_sup`）** · `exists_ssubset_of_not_mem_directElems` · **`isParentOf_parentOf`（`parentOf` 改用 `Finset.inf` + `Finset.inf_mem`）** · `isChildOf_isParentOf`
  - **⬜ 剩余：`univ` 自身的度** —— **精确形态已分析清楚**：
    - 记 `m` = 极大簇个数，`U` = 未被任何簇覆盖的元素（`U ∋ ρ`）。则 **`deg(univ) = m + |U|`**（`univ` 无父）。
    - **`m + |U| ≥ 3` 时**：`univ` 作根即可（度 ≥ 3 ✓）。
    - **`m = 0`（`F' = {univ}`）**：星形树，`deg(univ) = |X|`；`|X| ≥ 3` 时 ✓。
    - **`m + |U| = 2` 的两种退化子情形**（**唯一真正需要处理的点**）：
      - **(m=1, |U|=1)**：唯一极大簇 `A` + 唯一未覆盖元素 `t`。**出路**：`univ` 与 `A` 合并（`A` 升为根），`t` 变成 `A` 的直接元素 ⟹ `deg(A) = dirs + kids ≥ 3` ✓。
      - **(m=2, |U|=0)**：两个极大簇 `A₁ ⊔ A₂ = X`（如 `X={a,b,c,d}`、簇 `{a,b},{c,d}`）。**出路**：`univ` 与 `A₂` 合并 ⟹ `A₂` 为根、`A₁` 是 `A₂` 的孩子；`deg(A₂) = 1 + dirs + kids ≥ 3` ✓。
    - **更干净的替代**：直接写**一般 suppress**（压缩所有度 2 顶点）—— 但工作量更大（M1 曾刻意绕开）。
  - **⬜ 之后两步**：**`isTree`**（连通：`parentOf` 链上溯到根，`card` 严格递增保证终止；无环：**数边数** `|E| = |V| - 1` + 连通 ⟹ `IsTree`，或找势函数）；**`Σ(树) = 规范 cluster 集`**（回到 `Split`/`splits` 收口）。
  - **相关**：`Finset.min'_mem` / `min'_le` / `exists_min_image` / `max'_mem` / `le_max'` / `exists_max_image` **本版 Mathlib 全不存在** —— 极值一律走 **`Finset.exists_mem_eq_sup`**（`[LinearOrder] [OrderBot]`）。
- **（原记录）三条候选出路**：(i) 压缩度 2 顶点 / (ii) 加强假设 `Σ ⊇ Σ_triv` / (iii) 弱化结论。**现走 (i) 的思路但用「删单元素簇」实现，已绕过大半。**
- **已完成（2026-10-06 晚）**：修正构造全部构件 + 度 ≥ 3 主定理。`lake build` **1319 jobs**，无 sorry，`Phylo/Laminar.lean` **482 行**。
- **Lean 4 坑（本轮新增）**：
  - `SimpleGraph` 的 `symm : Std.Symm Adj` / `loopless : Std.Irrefl Adj` **是结构体**，必须 `⟨fun ... => ...⟩` 构造（`intro` 报 "no additional binders"）；`Std.Irreflexive` / `Symmetric` / `Irreflexive` **均非可用名**。
  - `Finset.inf'_mem` 参数顺序反直觉（第一显式参数是闭包条件）→ 已改用「特征性质」定义父关系。
- **Lean 4 坑（本轮新增）**：
  - `<;>` 同时作用于两个方向会留下 **8 个目标**，bullet 必须写满 8 个（`sidesCompatible_comm` 就栽在这）。
  - **`rw [Finset.mem_univ]` 会把「引理名」解析成「证明项」** → 报 `Expected an equality or iff proof`；改用 `Finset.mem_univ y` 作**项**。
  - `Finset.mem_sdiff` 的 `⟨_,_⟩` 构造须显式写 `.mpr`（成员关系不是语法上的 `And`）。
  - `Split.mem_xxx` 经**点记法**不可靠（`Split α` 是 `KPartition α 2` 的 abbrev，点记法找 `KPartition.xxx`）→ 写全 `Split.mem_xxx s ρ`。
  - 定义**必须前置于使用处**（`mem_sideB_iff_not_mem_sideA` 曾放在使用者之后）。
  - `contrapositive` 场景别把证明当函数用（`h (proof)` 报 `Function expected`）→ 写 `(h' : ¬P) hp`。
- **Lean 4 坑（本轮新增）**：
  - **名字须先定义后使用**：`SidesCompatible` 曾放在文件末尾 → namespace 内不可见；`compatible_of_sides` 用 `theorem Split.xxx` 形式在根 namespace 定义后，**在 `namespace Cladogram` 内引用会解析成 `Cladogram.Split.xxx` 而失败** → 改为在 `namespace Split` **内部**定义，且把主定理移到根 namespace。
  - `Finset.compl_compl` **不存在** → 手证互补。
  - `r `rw`无法进入`x ∉ s`内部** → 用`simp only [Finset.mem_compl, ...]\`。
  - `by` 块在函数参数位置**无预期类型**时会报 `invalid 'by' tactic` → 先 `have` 再应用。
  - `SidesCompatible` 的 `∪`/`Finset.univ` 需显式 `[Fintype α] [DecidableEq α]`。
- **git 节奏（2026-10-06 老师定）**：**少 push，多 commit**。已 commit `5ad4e5a` / `c178e52` / `93724a5` / **`8504245`（主定理）** / `1338529` / `a06668e` / `55a820e` / `4b30498` / `5564e32`，**均未 push**。

## M4 quartet / triplet 定义层（2026-10-06，转线后）

- **背景**：「相容 ⟹ 存在树」遇设计卡点 → **老师决定「暂缓此线，转其它」**。
- **✅ 新建 `Phylo/Quartet.lean`（185 行，无 sorry）**：
  - `Quartet X := {S : Finset X // S.card = 4}`（**`abbrev` 而非 `def`** → 自动获得 `Fintype`/`DecidableEq`）· `TripletSet X := {S // S.card = 3}`
  - **`Topology S := Split ↥S`** —— §3.5 的统一形式（quartet 2\|2 与 triplet 2\|1 同一构造）
  - `QuartetTopology` / `TripletTopology`（`structure`：`supp` + `card_supp` + `top`）
  - `Quartet.card_eq` / `nonempty` · `TripletSet.card_eq` / `nonempty`
  - **`Topology.swap` + `swap_swap`**（无序性 `ab|cd = cd|ab` 所需）· `QuartetTopology.swap` / `TripletTopology.swap` + `swap_swap`
  - `allQuartets` / `allTripletSets` 枚举 · **`card_allQuartets = C(n,4)`** · **`card_allTripletSets = C(n,3)`**
  - `lake build` → **1262 jobs 通过**；`check_file_imports.sh` 通过
- **⬜ 下一步（M4 续）**：`display`（quartet 被树展示）· Colonius–Schultze 推理规则 · quartet 距离 · 「split 相容 ⟺ 所有 quartet 相容」。
- **Lean 4 坑（Quartet 新踩）**：
  - **`abbrev Topology S := Split ↥S` 会让 `Topology.swap` 里的 `t.swap` 递归到自己**（namespace 内优先解析）→ 必须写 `Split.swap t`。
  - `Fintype.card_subtype` 方向：`Fintype.card {x // p x} = (univ.filter p).card`；计数要以 `(Finset.univ : Finset (Quartet X)).card` → `Finset.card_univ` → `Fintype.card_subtype` 的顺序 `rw`。
  - `Quartet` 用 **`abbrev`** 才能自动拿 `Fintype`/`DecidableEq`（`def` 不会自动派生）。

## M4 完成 + M5 起步（2026-10-06，老师「先B再A」）

### B：M4 续 —— display + ★ Colonius–Schultze 推理规则 ✅
- **`Phylo/Split.lean` 新地基**：
  - **★ `Split.compatible_iff_subset`**（相容的**嵌套形式**：一侧含于另一侧）—— 推理规则的支点
  - `Split.mem_sideA_of_not_mem_sideB` / `mem_sideB_of_not_mem_sideA`
  - **`Cladogram.compl_sideLeaves`**（边两侧互补）· **`Cladogram.isSplitOf_swap`**（★ `IsSplitOf` 对换向封闭 —— display 的 `comm_cd` 靠它）
- **`Phylo/Quartet.lean` display 层（307 行）**：
  - `Cladogram.DisplaysQuartet`（树展示 `ab|cd`）+ `displaysQuartet_comm_ab` / `_comm_cd`
  - **`exists_split_inter_of_displaysQuartet`**（★ 展示 ⟹ 该 split 在 4 元集上恰给出 `{a,b}|{c,d}`，§3.5 的「quartet + split」桥）
  - **★ `displaysQuartet_of_displaysQuartet_common`：`ab|ce ∧ ab|de ⟹ ab|cd`**（Colonius–Schultze 推理规则）
    - 证法：`compatible_iff_subset` 得四种嵌套 → 共同元素 `e ∈ B₁ ∩ B₂` 排除两个交叉情形 → 剩下 `A₁⊆A₂`（用 `s₁`）或 `B₁⊆B₂`（用 `s₂`）
  - `Cladogram.DisplaysTopology` + `QuartetCompatible`（**存在性命题**，非判据 —— §3.11 NP-complete）

### A：M5 起步 —— cherry + RF ✅
- **`Phylo/Split.lean`**：**`KPartition.eq_iff_parts` + `instDecidableEqKPartition`**
  - ⚠️ **坑**：`deriving DecidableEq` 会报「synthesized instance not definitionally equal」（与 `[DecidableEq α]` 参数冲突）→ **必须手写实例**（`decidable_of_iff (a.parts = b.parts) (eq_iff_parts a b).symm`，注意 `.symm` 方向！）
  - 有了它 `Finset (Split α)` 才能做 `\` / `∪` / `card`
- **`Phylo/Algorithm/Cherry.lean`（57 行）**：`Cladogram.IsCherry`（叶共享公共邻居）+ `isCherry_symm` / `isCherry_comm` / `not_isLeaf_common` / `degree_common_ne_two` / `leaf_ne_common`
- **`Phylo/Algorithm/RF.lean`（57 行）**：`Split.rfDistance`（对称差基数）+ **★ 度量三性质**：`rfDistance_comm` / `rfDistance_self` / `rfDistance_eq_zero_iff` / **`rfDistance_triangle`**
- `lake build` → **1264 jobs**；无 sorry；**1778 行**
- **⬜ 剩**：**cherry 存在性**（「每棵树有 cherry」—— 直径 + 分支论证：取最长路径、端点叶 x,y，`u`=x 的邻居，若 `u` 有非叶子邻居 z 则分支内叶 c 满足 `dist(c,y) = dist(c,u)+dist(u,y) > dist(x,y)` 矛盾；故 `u` 邻接叶 z ⇒ `{x,z}` 是 cherry）· NJ · UPGMA · KF / BHV · NNI / SPR

### A+：M5 —— ★ **每棵树都有 cherry** 证出来了 ✅
- **★ 主定理 `Cladogram.exists_isCherry (hV : 3 ≤ Fintype.card T.V) : ∃ a b : X, T.IsCherry a b`**
  —— NJ / UPGMA 等贪心归约算法的起点。
- **证法：纯组合计数（完全不用距离！）** —— 比「直径 + 最长路径」路线好形式化得多：
  - **上界 `card_leafFinset_le_internalFinset`（无 cherry ⟹ `ℓ ≤ i`）**：
    「叶 ↦ 其唯一邻居」是**单射**（否则两叶共邻居 = cherry），且落点都是**内部顶点**
    （由 `eq_or_eq_of_adj_of_degree_eq_one`：叶–叶相邻 ⟹ 树只有 2 顶点，故 `|V| ≥ 3` 时不可能）。
  - **下界 `internalFinset_card_add_two_le_leafFinset_card`（`i + 2 ≤ ℓ`）**：
    握手引理 `sum_degrees_eq_twice_card_edges` + `IsTree.card_edgeFinset`（`|E| = n-1`）
    + **`three_le_degree_of_not_isLeaf`（内部顶点度 ≥ 3）** + `ℓ + i = |V|` ⟹ `ℓ ≥ i + 2`。
  - 两者矛盾（`omega`）。
- 辅助：`leafFinset` / `internalFinset`（叶集与内部点集）· `three_le_degree_of_not_isLeaf` · `eq_or_eq_of_adj_of_degree_eq_one` · `not_isLeaf_of_adj_of_isLeaf` · `adj_leafNb` · `leafNb`
- `lake build` → **1264 jobs**；无 sorry（`Phylo/Algorithm/Cherry.lean` **217 行**）
- **⬜ 剩**：NJ 本体（用 cherry 归约 + 四点的 `z := δₓᵧ + ...` 极大性）· UPGMA · KF / BHV · NNI / SPR

### A++：M5 —— NJ 代数层移植 + ★ `four_point_z_iff` ✅
- **`Phylo/Algorithm/NJ.lean`（311 行，零 sorry）** —— 把旧 `NJ/Cherry.lean` 的 `Dissimilarity` 框架**移植进主库**并加新引理：
  - 定义：`Dissimilarity` / `FourPoint`（四点条件）/ `IsCherry`（**度量**樱桃）/ `S` / `Q`（Q-判据）/ `ell` / `z` / `rho`
  - 已证：`triangle`（四点 ⟹ 三角不等式）· `fourpoint_not_unique_max` · `fourpoint_eq_of_lt` · `rho_nonneg` · `ell_eq_sum_rho` · **`ell_comm` / `z_comm`（本轮新增）**
  - **★ `Q_eq_neg_two_ell`**：`Q = -2(δ+ℓ)` ⟹ 最小化 Q ⟺ 最大化 `z`
  - **★ `two_mul_z`**：`2z(i,j) = S(i)+S(j)+(2-n)δ(i,j)` —— z 不等式全化为线性不等式
  - **★ `z_hinge`**：门控恒等式（把 z 不等式翻译成四点和不等式）
  - **★★ `four_point_z_iff`（本轮新增）**：`n ≥ 4` 时「四点和 `P` 最小」**⟺**「`z` 的和最大」
    —— **z 最大性与 quartet 分裂的精确字典**（NJ 硬核证明的代数骨架；`z_hinge` + 系数 `(2-n)/2 < 0` 直接给出）
- **⚠️⚠️ 诚实边界（重要）**：**NJ 硬核 `max_z_cherry_core` 是 open problem**（`ROADMAP.md` §0.1 已记录）：
  - 「`z` 最大性是**全局**的（涉及所有行和 `S`），quartet 分裂是**局部**的」
  - 标准证明（Weller 2023 *leaf-status* / Pachter–Sturmfels Thm 2.38 / MLP 2006）**都显式用实现树**，即需要 **Buneman 存在性**
  - 纯度量路线（只用 `FourPoint`）**尚缺干净证明**；数值上随机 4000 棵正权树无界点
  - **本库的处理**：`MaxZCherryCore` 定义为**显式 `Prop` 假设**（**不用 `sorry`** ⟹ 库仍零 sorry），
    `nj_cherry` 表述为「**假设硬核 ⟹ NJ 樱桃引理**」—— 诚实且依赖关系可见
  - **解锁路径**：**解锁 Buneman 存在性（四点条件 ⟹ 存在实现树）= 解锁 NJ 硬核**。而 Buneman 卡在
    「连通性需根 vs `no_degree_two`」的设计问题（见上文 M2 卡点）。**两者是同一个瓶颈。**
- **旧 `NJ/Cherry.lean` 保留**（`CONCEPTS.md` §「库与算法分离」：新库 `Phylo/` 通用，`NJ/` 作为算法应用独立保留）

## 连续推进批次（2026-10-06 晚，老师「自主决策、只 commit 不 push」）

### ✅ 已完成
1. **`Iso.trans`**（`Phylo/Core.lean`）—— 同构传递性，`Iso` 构成等价关系（M1 欠账）+ `trans_apply`
2. **`Phylo/Distance.lean`（新）** —— `symmDiffCard` 通用对称差距离 + 度量三性质；`Split.rfDistance` 改为其 abbrev（去重复）
3. **`Phylo/Algorithm/UPGMA.lean`（新）** —— `Dissimilarity.Ultrametric` + **★ `ball_trans`（`≤ r` 是等价关系，分层聚类核心）** + `le_of_le`（等腰性）/ `eq_of_lt` / `ultrametric_triangle`
   - ⚠️ **超度量 + 零对角 ⟹ 非负**是**假的**（`δ ≡ -1` 于非对角是反例）→ `triangle` 显式带非负假设
4. **`Split.swap_swap`**（★ 对合）+ `swap_injective`
5. **`quartetDistance`**（`Phylo/Quartet.lean`，**固定支撑集**版 + 度量三性质）+ `Cladogram.displaysSet`
   - 全局 `Finset (QuartetTopology X)` 需**依赖型 `DecidableEq`**（`top : Topology supp` 依赖 `supp`）→ 绕开
6. **★★ 连通性（`Phylo/Laminar.lean`）** —— 「相容 ⟹ 存在树」的地基

### ★★ 连通性：关键发现与修复
- **发现真问题**：`laminarGraph F` 的顶点是**所有** `Finset α`（族外者孤立）⟹ **图不连通**！
  → 新增 **`LaminarVertex F := ↥F ⊕ α`**（族成员 + 元素）与 **`treeGraph F`**（经 `coerceV` 复用 `laminarAdj`，无重复定义）
- 新增 `instance instFintypeFinset : Fintype (Finset α)`（**本版 Mathlib 未提供**）+ `Fintype ↥F` 由 `⟨F.attach, Finset.mem_attach F⟩` 构造
- **★ `exists_isMinClusterOf`**：含 `x` 的最小簇存在（含 `x` 的族成员中 `card` 最小者，用 `Finset.exists_mem_eq_sup` + `Finset.eq_of_subset_of_card_le`）
- **★ `treeGraph_reachable_root`**：族成员沿 `parentOf` 链上溯到 `univ`（**强归纳 on `card univ - card A`**；`card` 严格递增保证终止）
- `treeGraph_reachable_root_of_elem`：元素 → 最小簇 → 根
- **★★ `connected_treeGraph`**：`treeGraph F` 连通 ✓
- `lake build` **1321 jobs**，无 sorry，`Laminar.lean` **614 行**

### ⬜ 剩余（isTree 的最后一步 + 后续）
- **数边数**：`Nat.card (treeGraph F).edgeSet = (F.card - 1) + Fintype.card α`
  （`|F| - 1` 条父边 —— 每个非根簇恰一条父边，`parentOf` 严格增卡保证不重；`|α|` 条叶边 —— 每个元素恰一条）；
  再用 **`SimpleGraph.isTree_iff_connected_and_card`** ⟹ `IsTree`
- 替代路线：`IsAcyclic` 用**唯一父（rank 势函数）+ 无环论证**，或 `isAcyclic_iff_forall_adj_isBridge`
- 之后：**① `univ` 的度**（`deg = m + |U|`，两种退化子情形）· **③ `Σ(树) = 规范 cluster 集`** · 再把 `three_le_degree_of_ne_univ` 从全图**移植到 `treeGraph`**（度数相同）

### ★★★ 里程碑：`treeGraph F` 是树（`isTree_treeGraph` 已证，2026-10-06 深夜）

**「相容 ⟹ 存在树」的核心门槛已过。** `Phylo/Laminar.lean` → **784 行**，1321 jobs，零 sorry。

- **`LaminarVertex F := ↥F ⊕ α`**（族成员 + 元素）+ **`treeGraph F`**（经 `coerceV` 复用 `laminarAdj`）
- 实例：`instFintypeFinset : Fintype (Finset α)`（`univ.powerset`）· `instFintypeSubtype : Fintype ↥F`（`F.attach`）
- **★ `exists_isMinClusterOf`**：含 `x` 的最小簇（`Finset.exists_mem_eq_sup` 最小化 card + `eq_of_subset_of_card_le`）
- **★ `treeGraph_reachable_root`**：族成员沿 `parentOf` 链上溯（**强归纳 on `card univ - card A`**）
- **★★ `connected_treeGraph`**：连通 ✓
- **父顶点层**：`rootV` / `minClusterV` / `parentV` / **`parV`**（簇→父、根→自身、元素→最小簇）· `adj_parV` · `parEdge` · `parEdge_mem_edgeSet`
- **★ `edgeSet_subset_range`（满射）**：每条边由某非根顶点的 `parEdge` 给出（四种邻接情形：簇–簇用 `isParentOf_unique`；簇–元素/元素–簇用 `isMinClusterOf_unique`；元素–元素不可能）
- **★ `card_edgeFinset_le`**：`|E| ≤ |V| - 1`（满射 + `card_image_le` + `card_erase_of_mem`）
- **★★★ `isTree_treeGraph`**：`IsTree` —— 上界由满射、下界由 `Connected.card_vert_le_card_edgeSet_add_one` 夹出，最后 `isTree_iff_connected_and_card`

### ⬜ 剩余（「相容 ⟹ 存在树」的最后两块）
1. **`univ` 的度** —— **精确刻画 `deg(univ) = |孩子| + |直接元素|`**（`univ` 无父）：
   - 邻居 = **极大簇**（`IsChildOf F univ`）∪ **未覆盖元素** `{x | IsMinClusterOf F x univ}`
   - **本轮已证**：`Sum.inr x` 度 = 1 ✓ · **非 `univ` 簇度 ≥ 3** ✓（见下）
   - **⬜ 待证**：`deg(univ)`。**已于 2026-10-06 尝试两种方案均差临门一脚**：
     - **方案 A（双射）**：`rootIdx F := (kids.image Sum.inl) ∪ (dirs.image Sum.inr) : Finset (Finset α ⊕ α)`
       （*kids 与 dirs 类型不同，无法直接 `∪`，故用 `Sum` 统一编码*）+ `rootVOf : Finset α ⊕ α → LaminarVertex F`
       （`Sum.inl B ↦ if B ∈ F then Sum.inl ⟨B,h⟩ else root`）。**坑**：`rootVOf_injOn` 里
       `rw [rootVOf, dif_pos ...]` 对 `Sum.inl B₂` 不生效（需先 `cases`/`split_ifs`）。
     - **方案 B（三元素）**：同 `three_le_degree_treeGraph`，但需 4 种情况（|kids| = 0/1/2/≥3 配 |dirs|）—— 啰嗦但可靠。
   - **数学结论**：`m + |U| ≤ 2` 的退化情形（`m` = 极大簇数、`U` = 未覆盖元素数）需**合并 `univ` 与某簇**，
     或直接**一般 `suppress`**。
2. **`Σ(树) = 规范 cluster 集`** —— 收口 Buneman 存在性 / NJ 硬核
3. **`leaf_iff_degree_one`** —— 正向（`Sum.inr x`）由 `degree_inr_eq_one` ✓；
   反向（度 1 ⟹ 是叶的像）需 `Sum.inl A` 的度 ≠ 1，由非 `univ` 的 ≥ 3 与 `univ` 的 ≥ 2 给出。

### ✅ 2026-10-06 深夜续：度条件（`no_degree_two` 的大部分）
- **`neighborFinset_inr` + `degree_inr_eq_one`**：元素 `Sum.inr x` 的邻居恰为 `{Sum.inl 最小簇}` ⟹ 度 = 1 ✓
- **★ `three_le_degree_treeGraph`**：非 `univ` 簇（且 `|A| ≥ 2`）度 ≥ 3 ✓
  - **「三元素」方案**：显式构造父 + 两个孩子（或孩子+元素、或两个元素）三个**互异**邻居
  - **避开 `Finset.image` 基数论证**（该路线在 `↥(F.filter p)` vs `↥F` 上有 `Sum.inl_injective` 类型推断障碍）
- `lake build` **1321 jobs**，无 sorry，`Phylo/Laminar.lean` **907 行**

### ★★★ 2026-10-06 深夜：`toCladogram` —— 「相容 ⟹ 存在树」的构造层完成！

**`Phylo/Laminar.lean` → 1069 行**，1321 jobs，零 sorry。

```lean
noncomputable def toCladogram (hl : LaminarFamily F) (hne : ∀ B ∈ F, B.Nonempty)
    (huniv : univ ∈ F) (hcard : ∀ B ∈ F, B = univ ∨ 2 ≤ B.card)
    (hroot : 3 ≤ |univ 的孩子| + |univ 的直接元素|) : Cladogram α
```

**所有字段都填上了**：`V := LaminarVertex F` · `graph := treeGraph F` · `leaf := Sum.inr`
· `isTree` · `no_degree_two` · `leaf_iff_degree_one` · `decAdj := Classical.decRel _`

**完整链条**（本批新增，全部零 sorry）：
| 引理 | 内容 |
|---|---|
| `neighborFinset_inr` / `degree_inr_eq_one` | 元素的邻居 = 最小簇，**度 = 1** |
| **★ `three_le_degree_treeGraph`** | 非 `univ` 簇度 **≥ 3**（三元素方案：父 + 两个孩子/元素） |
| `kidVOf` + **★ `three_le_degree_rootV`** | 根 `univ` 度 **≥ 3**（`if B ∈ F` 嵌入 + `dif_pos` 展开；取 `min |kids| 3` 个孩子 + `3 - min |kids| 3` 个元素） |
| **★★ `no_degree_two_treeGraph`** | 无度 2 顶点（三种顶点分治） |
| **★★★ `toCladogram`** | 组装成 `Cladogram` |

**⚠️ 四个假设（诚实记录）**：`F` 镶嵌 · `univ ∈ F` · 族元素非空 · `F` 已正规化（无单元素簇）· **根非退化 `|kids(univ)| + |dirs(univ)| ≥ 3`**。
最后一个对应 `MEMORY.md` 早先记录的「`deg(univ) = 2` 退化情形」（需合并 `univ` 与某簇）。

**⬜ 剩余**：① 退化情形（合并 `univ` 与某簇）· ② `Σ(toCladogram F) = 规范 cluster 集`（收口 Bunatic/NJ）· ③ `leaf_iff_degree_one` 已随 `toCladogram` 完成 ✓

## 🟢 表示层落实（2026-10-06 深夜，老师定："怎么简单怎么来"）

> 老师原话：**「证明的话怎么简单怎么来，但表示无根树肯定采取 degree=3 的形式，或者说所有内部节点 degree
> 都是 3，表示有根树可以弄个带 root 叶节点的无根树，也可选择与它 isomorphic」**

### `Phylo/Core.lean` 新增
| 实体 | 内容 |
|---|---|
| **`Cladogram.IsBinary`** | 无根树的表示：**内部顶点度恰为 3**（+ `IsBinary.degree_eq_one_or_three` / `degree_eq_three`） |
| **`RootedCladogram X := Cladogram (X ⊕ Unit)`** | 有根树的**底层实现**：标记叶 = `Sum.inr ()`（"名为 root 的叶子节点"） |
| **`IsRootedBinary`** | 有根二叉树刻画：标记叶的邻居（= root）度 2，其余内部点度 3 |

### ⚠️ 我犯的错（记录以防再犯）
第一版我把 `RootedCladogram` 写成 `structure ... extends Cladogram X where rootLeaf : X` ，
**违反了 `CONCEPTS.md` §3.3 三条纪律的第 ① 条**（「标记叶不能塞进 `X`」—— 否则类型污染扩散）。
**已改为 `Cladogram (X ⊕ Unit)`** ✓。纪律另两条：② 「根」= 标记叶的**唯一邻居**；③ `X ⊕ Unit` 只出现在**转换引理**里。

### 证明层
**`toCladogram` 的 `hroot` 假设保留**（老师「怎么简单怎么来」）—— 不做移根大重构。
`no_degree_two`（一般，只排斥度 2）与 `IsBinary`（binary，内部度恰 3）**并存**。

## ① 退化情形 —— 结论（2026-10-06）
- **★ `no_degree_two_except_root`：除根 `univ` 外所有顶点度 ≠ 2**（对任意 `F`，与 `hroot` 无关！）
  - ⇒ 退化情形下 **`univ` 是唯一的度 2 顶点**；此时 `treeGraph F` 是**合法的实现树**
    （`IsTree` + 叶嵌入 + 叶度为 1），只是不满足 `Cladogram` 的 `no_degree_two`
  - 消除这一个顶点需**改图**（移根 / suppress）—— 但既然老师批准"简单来"，保留 `hroot` 即可
- 配套：`isChildOf_erase_of_isChildOf` · `isMinClusterOf_erase_of_directElems`（删极大簇后的结构，供将来 suppress 用）

## ② 簇 ↔ split 字典 —— 进展
- ✅ **★★ `leavesOf_eq`**：`leavesOf F B = B`（`B ∈ F`）—— `B` 的子树叶集恰为 `B`
  - `leavesOf F B := {x | x 的最小簇 ⊆ B}`，证明只用 `isMinClusterOf_subset`（**不需要镶嵌性**）
- ⬜ **桥接到 `sideLeaves`**：需证「删掉 `B` 与其父的边后，`B` 的分量 = `B` 的子树」
  - 三条子引理已推演清楚：**(a)** `A ⊆ B, A ≠ B ⟹ parent(A) ⊆ B`；**(b)** 子树连通（父链）；**(c)** 唯一跨越边就是 `e`
  - 然后 `sideLeaves e (inl B) = leavesOf F B = B` ⟹ `IsSplitOf` + `Σ(toCladogram F) ⊇ F`

## ② 簇 ↔ split 字典 —— ✅ **核心完成**（2026-10-06 深夜）

**`Phylo/Laminar.lean` → 1443 行**，1321 jobs，零 sorry。

### ★★★ 主结果
```lean
theorem leafSide_parentEdge : leafSide F (parentEdge hl hne huniv B hB hBuniv) (Sum.inl ⟨B,hB⟩) = B
```
> **规范 cluster 集 `F` 的每个非 `univ` 成员 `B`，都对应 `Σ(toCladogram F)` 中的一条 split —— 其叶侧恰为 `B`。**

### 完整链条（全部零 sorry）
| 步骤 | 引理 | 要点 |
|---|---|---|
| **(a)** | `parentOf_subset_of_subset` | `A ⊆ B, A ≠ B ⟹ parentOf F A ⊆ B` —— **只用 `IsParentOf` 的最小性，不需要镶嵌性** |
| **(b)** | `reachable_of_subset` | `A ⊆ B` 的簇沿父链在 `T - e_B` 中与 `B` 可达（**强归纳 on `B.card - A.card`**）；关键：`A ⊊ B ⟹ parentOf F A ⊆ B ⟹ ≠ parentOf F B ⟹ 边 ≠ e_B` |
| **(c)** | `not_reachable_parentEdge` | `T - e_B` 中 `B` 与父不可达 —— **一行**：`IsTree ⟹ IsAcyclic ⟹ 边是桥`（`isAcyclic_iff_forall_adj_isBridge` + `isBridge_iff`） |
| **闭包** | `subtreeVerts` `C := {inl A : A ⊆ B} ∪ {inr y : y ∈ B}` | `mem_subtreeVerts_inl` / `mem_subtreeVerts_inr` |
| **★** | `subtreeVerts_closed` | `C` 对 `T - e_B` 的邻接封闭 —— **关键：`A.1 = B` 时向上走的那条边正是 `e_B`，被 `deleteEdges` 排除** |
| **★** | `walk_mem_subtreeVerts` | `SimpleGraph.Walk.recOn` + motive `a ∈ C → b ∈ C` |
| **★★** | `mem_iff_reachable` | `x ∈ B ⟺ x` 在 `T - e_B` 中与 `inl B` 可达 |
| **★★★** | `leafSide` + `leafSide_parentEdge` | 包装成 `sideLeaves` 的裸形式 |

**命名定义**：`parentEdge`（`B` 与其父的边）· `minClusterV`（选函数版最小簇）· `leafSide`

### ⬜ 剩余（② 收尾，机械工作）
1. 把 `leafSide` 对齐 `Cladogram.sideLeaves`（**definitional 相同**：`leaf = Sum.inr`、`graph = treeGraph F`）
2. 构造 `Split α`（`parts 0 = B`、`parts 1 = Bᶜ`）得 `IsSplitOf`
3. 组装 `Σ(toCladogram F) ⊇ F` —— 之后 **Buneman 存在性 / NJ 硬核同时开门**

## ★★★ 「相容 ⟹ 存在树」全线打通（2026-10-06 深夜）

**结论**：Splits-Equivalence 的另一半（「相容 ⟹ 存在树」）的**构造层完成**，
假设清单最终只剩：**`F` 镶嵌 · `univ ∈ F` · `F` 正规化（无单元素簇）· `2 ≤ |α|`**。

### 关键突破 1：`univ` 度 2 不是缺陷，而是「有根树」

原卡点：`|极大簇| + |未覆盖元素| = 2` 时 `deg(univ) = 2`，违反 `Cladogram.no_degree_two`。
**老师定夺（`CONCEPTS.md` §3.3）**：无根树 → 内部节点 degree 3；**有根树 → 无根树 + root（或同构形式）**。

⇒ 「root 度 2」**正是有根二叉树的根有两个孩子** —— 退化情形本来合法。落实为：

| 实体 | 内容 |
|---|---|
| `RootedTree`（`Core.lean`） | `Cladogram` 把 `no_degree_two` 放松为 `no_degree_two_except_root` + `root : V` |
| `Cladogram.toRootedTree (r)` | 任意 cladogram 任取顶点作 root |
| `two_le_degree_rootV` | 根的度 ≥ 2（**由 `three_le_degree_rootV` 脚本生成、把 3 换成 2，零调试成本**） |
| **`toRootedTree`** | 由镶嵌族构造，只需 `|kids| + |dirs| ≥ 2` |
| **★★★ `toRootedTreeOfCard`** | **hroot 自动满足**，只需 `2 ≤ |α|` |

### 关键突破 2：`2 ≤ |kids| + |dirs|` 的证明（只需 `2 ≤ |α|`）

`two_le_card_kids_add_dirs`，三情形：
* `|kids| ≥ 2` 显然；
* `|kids| = 0` ⟹ 族里只有 `univ`（`eq_univ_of_forall_not_isChildOf_univ`）⟹ `dirs = univ` ⟹ `|dirs| = |α| ≥ 2`；
* `|kids| = 1`（唯一孩子 `A`）⟹ 若 `dirs = ∅`，每个元素的极小簇含于某个 `univ` 的孩子
  （`exists_isChildOf_univ_superset`，用 `Finset.exists_mem_eq_sup` 取 card 最大者）—— 孩子只有 `A` ——
  于是 `A = univ`，与 `A ⊊ univ` 矛盾。

### 完整链条（全部零 `sorry`）

```
镶嵌化简（laminar_of_sidesCompatible_of_notMem）· 规范 cluster（Split.cluster）
  → parentOf / parV / parentEdge
  → 连通性（connected_treeGraph，强归纳 on card univ − card A）
  → isTree（parEdge 满射 + 夹逼 |E| = |V| − 1）
  → 度条件（元素度 1 · 非 univ 簇度 ≥ 3 · 根度 ≥ 2）
  → ★★★ toRootedTreeOfCard（hroot-free）
  → ★★★ leafSide_parentEdge_of_card（hroot-free 的 Σ ⊇ F）
```

### 本轮踩坑（4 个，都值得记）

1. **`Fin.cases` 在 `Fin 2` 上取 `1` `simp` 化简不了** —— 本版 Mathlib 认不出 `(1 : Fin 2)` 是 `Fin.succ 0`。
   自建 `finCases_two_zero` / `finCases_two_one`（`:= Fin.cases_zero` / `:= Fin.cases_succ 0`）作 `@[simp]`。
2. **`toCladogram ... .V` 投影挡住 defeq** —— `refine ⟨Sum.inl ..., ...⟩` 报 "expected to have type `(toCladogram …).V`"。
   解法：`change ∃ (a b : LaminarVertex F) ... ` 把目标换成**裸形式**（`show`/`change` 直接做 defeq 检查，绕开 elaboration 顺序问题）。
3. **`IsChildOf F A B` 的第三项是 `∀ C ∈ F, B ⊂ C → ¬ C ⊂ A`**（不是 `A ⊆ C`！）—— 前两次写错。
4. **`rw` 有时自动关闭目标** —— 多写一个 `exact` 会报 "No goals to be solved"。
5. **`Finset.mem_filter.mpr` 要 `⟨a ∈ s, p a⟩`**，而 `IsChildOf` 自带 `B ∈ F` 不是 filter 谓词的一部分 ——
   要写 `Finset.mem_filter.mpr ⟨hC.1, hC⟩`。

### ⬜ 剩余（收口 Splits-Equivalence）

1. **从任意 `Finset (Split α)` 集 Σ 组装 `F`**：取规范 cluster（避开 ρ）+ `normFinset`，
   再证 `toRootedTreeOfCard` 的假设成立（`laminar_of_compatible_clusters` / `laminarFamily_normFinset` / `normFinset` 均已有）。
2. **Σ ⊆ Σ(T)**：`s ∈ Σ` 时 `s.cluster ρ = B ∈ F`，`leafSide_parentEdge_of_card` 给
   `B` 是某边的一侧；`s = splitOf B` 或 `s = (splitOf B).swap`（`swap` 也对应同一条边的另一侧）。
3. 之后：**Buneman 存在性** 与 **NJ 硬核 `MaxZCherryCore`** 同时开门。

## ★★★★ 统计一致性层（2026-10-07 老师定，`Phylo/Stat/`，1060 行）

**任务**：证明 **ASTRAL / CASTER / parsimony** 在 quartet MSC 下、**NJst** 在多物种下的**统计一致性**。

### 决策（老师 2026-10-07）

1. **先把 MSC 公理化**，把「证明 MSC」本身另立为课题；
2. **parsimony 走 unrooted quartet + ISM**（Felsenstein zone 需同塑性；ISM 下不发生同塑性；
   Roch–Steel 2015 的 unrooted 反例是 6 taxon，不覆盖 4 taxon）。

### 架构：三层

```
① 理想一致性   MSC 频率 ⟹ E 输出 ≅ 真树            （各算法分头证）
② gap 引理     严格最大 ⟹ 存在正 gap δ              （有限性，Stability.lean）
③ 稳定性       扰动 < δ/(2N+1) ⟹ argmax 不变        （Stability.lean）
──────────────────────────────────────────────
⟹ 统计一致性   （① + ② + ③ + MSC 大数定律）
```

### 文件与成果

| 文件 | 内容 |
|---|---|
| `MSC.lean` | `QuartetFreq` / `QuartetTree` / ★★ `MSCFreq`（真树 + quartet 选择 + 频率 + `majorizes`）/ `MSCFreq.p_le` / `FreqClose(+_symm)` / `MSCSampling`（**大数定律公理化**）/ `IdeallyConsistent` / `StatisticallyConsistent` |
| `ASTRAL.lean` | `astralScore` / ★★ `astralScore_le`（真树得分最大）/ ★★ `astralScore_eq_iff` / `IsASTRAL` / ★★★ `astral_maximizer_agrees` |
| `Stability.lean` | `IsTrueChoice` / ★ `score_lt_of_not_true` / ★ `exists_gap`（`Finset.min'`）/ ★★ `stable_argmax` / ★★★ `astral_statisticallyConsistent` |
| `CASTER.lean` | `MultiMarkerFreq` / `avg` / `casterScore` / ★ `casterScore_eq`（归约 `= L·astralScore(avg)`）/ ★★ `caster_isASTRAL` / ★★★ `caster_statisticallyConsistent` |
| `Parsimony.lean` | ★ `Pattern.fitchCost_eq`（**48 情形 `native_decide` 枚举**）/ `SiteSupport` / `parsimonyScore` / ★★ `parsimonyScore_le_iff` / `MSCSite` / ★★ `stable_argmax_site` / ★★★ `parsimony_statisticallyConsistent` |
| `NJst.lean` | `NJstData` / ★ `njst_cherry`（第一步）/ **诚实边界**：`MaxZCherryCore`（open）+ NJ 归纳正确性 |
| `QuartetDecides.lean` | ★★ **`QuartetDecidesTree`（显式缺口）** / `agreesWith_symm` / ★★★ `astral_iso` / `caster_iso` / `parsimony_iso` |

### 缺口（唯一，四算法共享）

**`QuartetDecidesTree`**：两棵 binary cladogram 有相同 quartet 系统 ⟹ 同构。
（Steel 1992 / Colonius–Schultze 1981；**binary 不可去** —— polytomy refine 成 binary 不改 quartet 系统。）

**证明路线（4 步，已写进模块文档）**：
1. binary `T` 的每条内部边两侧各 `≥ 2` 叶（`deg = 3`）；
2. 边的叶侧由「被它分离的 4-元 2\|2 划分」见证；
3. 由 `q ≈ q'` 得 `Σ(T) = Σ(T')`（**库里已有 C-S 规则** `displaysQuartet_of_displaysQuartet_common`）；
4. binary 树由 `Σ` 唯一决定（接 `Laminar.toRootedTreeOfCard` + Buneman 存在性）。

**为什么卡住**：第 1 步需要「树的**分量 / 诱导子图 / 叶存在性 / 最长路径**」基础设施层 ——
Mathlib 只有 `ConnectedComponent`（`Quot G.Reachable`）与 `Walk.length`，
**没有「诱导子图是树」「最长 walk 存在」**，自建约 300–500 行。

### 本轮踩坑（Lean 4，已入共享记忆 lesson）

1. **`Exists.choose` 不做 ι-归约**（`Classical.choice` 是公理）：
   `(⟨a, h⟩ : ∃ x, p x).choose = a` **不可 `rfl`**。
   ⇒ **改用结构字段**（`MSCFreq.q`）代替 `∃` + `choose`，一切变成投影。**这是本层最关键的设计决策。**
2. **`Cladogram` 的顶点宇宙必须显式**：`Cladogram.{u, v} X`（否则 `Failed to infer universe levels`）。
   `structure` 字段里的 `∀ S hS, ...` 也**必须带类型标注**（无期望类型可推）。
3. **ℝ 没有 `OrderBot`** ⇒ `Finset.sup` 不可用；用 `Finset.min'`（`LinearOrder` + `Nonempty`）代替。
4. **Python 在 Windows 写文件默认 CRLF** ⇒ `check_file_imports.sh` 的 `grep "…$"` 失配误报
   「未 import」。**写 `.lean` 必须 `newline='\n'`**（或事后统一转 LF，8 个文件受影响）。
5. `native_decide`（Parsimony 的 48 情形枚举）引入 `Lean.ofReduceBool` 信任假设 —— 已标注。
6. **`rw` 链里 `mul_div_assoc` / `div_mul_cancel₀` 的方向**：`L * (Y/L) = Y` 用
   `rw [mul_comm, div_mul_cancel₀ _ hL]` 两步，比 `mul_div_cancel₀` 稳。

## Git / 远程（2026-10-02）
- **远程**：`git@github.com:chaoszhang/lean4phylo.git`（GitHub，**SSH** 协议）。
- **首推成功**：commit `b358df6`，`main` 分支已 track `origin/main`。
- **⚠️ 关键：认证只在 WSL 侧**！Windows 侧**没有 SSH key**（`~/.ssh` 只有 known_hosts），WSL 侧 `~/.ssh/id_ed25519` 已配到 GitHub 账号 `chaoszhang`。  
  ⇒ **所有 git 远程操作（push/pull/fetch）必须走 WSL**，且需绕过 `dubious ownership`：
  ```bash
  wsl -e bash -lc 'cd /mnt/c/Users/ASTER/WorkBuddy/Project/lean/lean4phylo && \
    GIT_SSH_COMMAND="ssh -o StrictHostKeyChecking=no -o BatchMode=yes" \
    git -c safe.directory="*" push -u origin main'
  ```
- **本机无 `gh` CLI、无 GitHub token** ⇒ **不能**用 API 建仓库（本次靠老师在网页建空仓库）。
- **工具链**：Windows git 2.55.0；提交身份 `chaoszhang <chaoszhang@users.noreply.github.com>`（仓库级 local config，noreply 式，可改）。
- **已配置**：`.gitignore`（忽略 `.lake/` 等）· `.gitattributes`（**统一 LF**，Windows 编辑 + WSL 编译）· `LICENSE`（Apache 2.0 全文）· `lake-manifest.json`（固定 mathlib rev，PhysLib 惯例）。
- **CI**：`.github/workflows/build.yml`（`lake exe cache get` → `lake build`）。
  - ✅ **run 1（M0）success** · ✅ **run 2（`cefdee9` M1: Phylogram/dist/Iso）success** —— **CI 全绿，模板可直接复用**。
  - ⚠️ **后台 bash 里 `curl` 抓不到 GitHub API 输出**（返回空），但**前台 `curl` 正常** —— 查 CI 状态要在前台跑（`curl -s https://api.github.com/repos/chaoszhang/lean4phylo/actions/runs | grep -E '"run_number"|"status"|"conclusion"'`）。
  - 查看：<https://github.com/chaoszhang/lean4phylo/actions>
- 原则：老师要求 **更多交互**，重大设计决策不擅自拍板。
- **已建 `DESIGN.md`**（库设计文档）：Mathlib 现状实测表 / 分层架构 / 已定决策 D1–D4 / **待定决策 P1–P5** / 里程碑 M0–M3。
  - 待定 P1（M0 中「叶」的定义）**阻塞 M0**；P2 推进节奏；P3 quartet 表示；P4 目录切分；P5 Buneman 放哪层。老师本轮跳过 P1/P2 未答 → **不擅自开工**。
