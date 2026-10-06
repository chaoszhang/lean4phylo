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
11. **工程骨架（`SCAFFOLD.md`，2026-10-02）**：
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
- **M2 进度（2026-10-06）**：`Phylo/Split.lean` 已完成并编译通过 ——
  - `KPartition α n`（划分族共享基础）· `Split α := KPartition α 2` · `sideA`/`sideB`/`disjoint_sides`/`union_sides`
  - **`Split.Compatible`**（四个交至少一空）+ `compatible_comm`
  - **`Split.restrictSide`** / `disjoint_restrictSide` / **`Split.restrict`**（`A|B ↦ (A∩Y)|(B∩Y)`）——**route B 的核心：restriction 定义在 split 层面，不造新树**
  - `Cladogram.sideLeaves`（删边后叶集）· `splitOfEdge`（边 → Split）· **`IsSplitOf`** / **`splits`** / `PairwiseCompatible`
  - `lake build` → **1259 jobs 通过**；`scripts/check_file_imports.sh` 通过
  - ⬜ 剩：`Split.swap`（unordered 判定）· **Splits-Equivalence 定理**（需劈顶点引理）
- **Lean 4 坑（M2 新踩）**：`Finset.biUnion_fin_two` 不存在 → 手写 `fin_cases` 或 `ext`；`Fin 2` 上的 `simp only` 易残留 `Quot.lift` 形式 → 改用 `simpa [Def, ...] using h` 显式给出引用；`s.restrictSide Y 0` **不**定义等于 `s.sideA`（`sideA` 是 def 不自动展开）→ `simp` 集里要带 `sideA`/`sideB`。
- **未 commit 前状态**：HEAD = `3b41475`（M2 前半）。

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
  - 查看：https://github.com/chaoszhang/lean4phylo/actions
- 原则：老师要求 **更多交互**，重大设计决策不擅自拍板。
- **已建 `DESIGN.md`**（库设计文档）：Mathlib 现状实测表 / 分层架构 / 已定决策 D1–D4 / **待定决策 P1–P5** / 里程碑 M0–M3。
  - 待定 P1（M0 中「叶」的定义）**阻塞 M0**；P2 推进节奏；P3 quartet 表示；P4 目录切分；P5 Buneman 放哪层。老师本轮跳过 P1/P2 未答 → **不擅自开工**。
