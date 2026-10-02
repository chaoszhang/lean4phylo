# SCAFFOLD.md —— Lean 4 库的工程骨架（模板调研 + 落地清单）

> 2026-10-02。为 phylogeny 库（`Phylo/`）选定的工程骨架。调研自三个权威来源。

---

## 1. 模板调研结论

| 来源 | 性质 | 关键可借鉴点 |
|---|---|---|
| **官方 `lake new` / `lake init . math`**（Lake 自带） | 最小标准骨架 | 目录同名根模块 + `leanfile.toml` + `lean-toolchain` + `.gitignore`；`lake init . math` 直接带 Mathlib 依赖 |
| **`leanprover-community/physlib`** ★ | **领域库最佳范例** | ① `-Dwarn.sorry=false`（开发期允许含 sorry 编译）；② `PhysLean/Meta/` 自定义 linter；③ `scripts/`（`lint-all.sh`、`check_file_imports.lean`）；④ 文件头规范 + 每定义带 docstring；⑤ `lake-cache.toml` |
| **`LeanProject` 模板**（blueprint-driven） | 重型项目模板 | `.github/workflows/{build-project,create-release,update,dependabot}.yml`；`.vscode/{extensions,settings}.json`；`Mathlib/` 存缺失声明；`customize_template.py`；`CONTRIBUTING.md` + Blueprint |

**官方最简骨架**（`lake new hello`）：
```
.lake/            # 构建产物（gitignore）
Hello/            # 库源文件，import Hello.* 可达
  Basic.lean
Hello.lean        # 根模块：import 库内的标准模块
Main.lean         # 可执行入口（纯库可删）
lakefile.toml     # 包配置
lean-toolchain    # Lean 版本
.gitignore
```

---

## 1.5 `leanprover-community/LeanProject` 模板评估（2026-10-02 老师问「有用吗」）

**它是什么**：**blueprint-driven formalization 项目模板** —— 面向「把一篇/一组**特定数学结果**形式化」的项目（FLT、PFR、Sphere Packing、Carleson… 都用它）。核心特色是 **Blueprint**（LaTeX 蓝图 + 依赖图 + 证明状态网站）、**upstreaming dashboard**（追踪哪些结果该回灌 Mathlib）。

**目录**：
```
.github/workflows/{build-project, deploy-pages, create-release, update}.yml
.vscode/{extensions,settings}.json
Project/            ← Lean 代码（Project 是占位名，靠 customize_template.py 改名）
  Mathlib/          ← ★ 存放「Mathlib 里还没有」的声明
  Example.lean
scripts/            ← 更新 Mathlib 的脚本
website/            ← Jekyll 首页 + upstreaming dashboard
CODE_OF_CONDUCT.md  CONTRIBUTING.md  lakefile.toml  lean-toolchain
```

**判断：部分有用 —— 取零件，不取整体。**

| 组件 | 处置 | 理由 |
|---|---|---|
| `.github/workflows/build-project.yml` | ✅ **取** | 最小 CI，直接可用 |
| `.vscode/{extensions,settings}.json`、`.gitignore` | ✅ **取** | 零成本 |
| **`Project/Mathlib/`（缺声明容器）** | ✅ **取**（改名为 `Phylo/Mathlib/` 或 `Phylo/Upstream/`） | ★ 正好落实 §3.1「接口包一层」：**Mathlib 没有的自建内容集中一层**，将来若想回灌也好搬 |
| `scripts/`（更新 Mathlib） | ✅ 取（简化版） | 与 `check_file_imports` 一起 |
| **Blueprint 体系**（`leanblueprint` + `deploy-pages` + `website/`） | 🔶 **暂缓，但留位置** | **★ 见下** |
| upstreaming dashboard | ❌ 不取 | 为「回灌 Mathlib」设计；独立库暂不需要 |
| Jekyll 首页 | ❌ 不取 | 初期过重 |

**★ Blueprint 对我们的特殊意义（值得单独记住）**：
Blueprint 的产物 = **「定义/定理/证明状态 + 依赖图」的可视化网站**。而**我们的 `CONCEPTS.md §4`（里程碑 + 引理树）与 `ROADMAP.md §4`（引理树）本质上就是「非正式版 Blueprint」**。
⇒ 对一个「**所有经典算法证明的库**」来说，**Blueprint 是天然的文档形态**（进度可视化 + 依赖可追溯）。等库积累到 20–30 个定理后，可以引入 `leanblueprint` 把现有 `.md` 结构升级成正式蓝图 —— **不必现在做，但设计文档的写法已经兼容它**。

> 一句话：**LeanProject 是「论文形式化」模板，我们是「库」——但它的「零件」（CI/缺声明层/蓝图工具）都可拆用。**

---

## 2. 选定骨架（对本库定制）

> ⚠️ **2026-10-02 改名（重要）**：原拟库名 **`Nj` 不可用** —— Windows 文件系统**大小写不敏感**（实测 `ls -d nj` 直接匹配到 `NJ/`），所以 `Nj/` 会与现有 `NJ/`（NJ 算法形式化）**撞同一个目录**。
> ⇒ 命名（2026-10-02 老师提议）：**仓库 / 包名 = `lean4phylo`**（双关：Lean **4** phylo / **lean for** phylo），**Lean 库名 = `Phylo`**（PascalCase，`import Phylo.Core` 才顺；也避免 `Lean4Phylo` 被误认为 Lean 官方组件）。**避开与 `NJ` 仅差大小写的任何名字。**


```
lean4phylo/                      ← 仓库根（包名 lean4phylo）
  .gitignore                     ← 忽略 .lake/ 等
  .vscode/
    extensions.json              ← 推荐扩展
    settings.json                ← 项目设置
  .github/workflows/
    build.yml                    ← lake build CI（可后置）
  lean-toolchain                 ← leanprover/lean4:v4.35.0-rc3
  lakefile.toml                  ← 见下
  Phylo.lean                        ← 根模块（按字母序 import 全部 Phylo/*）
  Phylo/                            ← 通用库（新）
    Core.lean                    ← M0+M1
    Split.lean                   ← M2
    Metric.lean                  ← M3
    Quartet.lean                 ← M4
    Algorithm/
      NJ.lean                    ← M5
      UPGMA.lean
      Compare.lean
  NJ/                            ← 现有 NJ 算法应用（保留）
    Cherry.lean
    CherryTree.lean
  NJ.lean                        ← 现有根模块（保留）
  scripts/
    check_file_imports.lean      ← 根模块与文件系统同步检查（从 PhysLib 借）
  *.md                           ← README / CONCEPTS / ROADMAP / MEMORY / SCAFFOLD
```

### `lakefile.toml`（建议）

```toml
name = "lean4phylo"
defaultTargets = ["Phylo", "NJ"]

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "master"          # 可固定到 tag（如 v4.35.0）以保稳定

[[lean_lib]]
name = "Phylo"
-- 开发期放宽 sorry 警告（PhysLib 做法）；交付前改回
moreLeanArgs = ["-Dwarn.sorry=false"]

[[lean_lib]]
name = "NJ"
```

> ⚠️ TOML 里 `moreLeanArgs` 的键名需按当前 Lake 版本核对（`lean_lib` 支持 `moreLeanArgs` / `weakLeanArgs`）。

---

## 3. 与现有项目的差距（需补齐）

现有只有 `lakefile.toml`（`name = "nj"` + `lean_lib NJ`）、`NJ.lean`、`NJ/`、若干 `.md`。

| 缺 | 说明 |
|---|---|
| `lean-toolchain` | **必需**。Windows 正本侧没有（构建在 WSL `~/nj-lean`）；建议两侧都放 |
| `.gitignore` | 至少忽略 `.lake/` |
| `.vscode/` | 推荐扩展（lean4）+ 设置 |
| `.github/workflows/build.yml` | CI |
| `scripts/check_file_imports.lean` | 防根模块与文件系统脱节 |

---

## 4. 四条关键实践（从 PhysLib 学，值得现在就立规矩）

1. **每个文件头三件套**：
   ```lean
   /- Copyright (c) 2026 ASTER LAB. All rights reserved.
      Released under Apache 2.0 license as described in the file LICENSE.
      Authors: ... -/
   import Mathlib.…
   /-! # 模块一句话描述 —— 文件级 docstring -/
   ```
2. **每个定义/定理带 docstring**（学术库的硬要求，也是文档站的数据源）。
3. **根模块按字母序 import**，且新增文件必须同步进根模块 —— 用 `check_file_imports` 自动化检查。
4. **`-Dwarn.sorry=false` 开发期开启**：让含 `sorry` 的库照常编译，用 **linter** 而非编译警告来盯 sorry（对应我们 M0 起就会有的阶段性 sorry）。

**暂不采纳**：Blueprint（过重）、PhysLib 的 informal/semiformal 追踪体系、双库（Alpha）结构 —— 待库成型后再议。

---

## 5. 建议执行顺序

1. 补 `lean-toolchain`（`leanprover/lean4:v4.35.0-rc3`，与 WSL 一致）+ `.gitignore`
2. 改 `lakefile.toml`：加 `[[lean_lib]] name = "Phylo"`
3. 建 `Phylo/Core.lean`（M0 载体）+ 根模块 `Phylo.lean`
4. 之后按 §4 的规矩写每个文件
5. `lake build` 双目标通过后，再加 `.github/workflows` 与 `scripts/`
