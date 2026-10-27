# lean4phylo

计算系统发生学（computational phylogenetics）经典算法的形式化库 —— 用 **Lean 4 + Mathlib**
建立**可机器检验**的证明。名字双关：**Lean 4** phylo ／ **lean for** phylo。

> 🚧 **under construction** —— 外部审计（W35–W38）结项后统一回填。
> 要准确数字请直接跑 `bash scripts/<对应脚本>`，不要引用本文件的旧数字。

## 结构

```
Phylo.lean     根模块（按字母序 import 全部子模块）
Phylo/
├── Core.lean          树载体 cladogram 与基础引理
├── Split.lean         分裂系统 · 相容性
├── Algorithm/         Cherry · NJ · NNI · RF · BinaryCount
├── Stat/              ASTRAL · CASTER · MSC · NJst · Parsimony · SVDQuartets
└── Mathlib/           Mathlib 尚未提供、本库自建的声明（便于将来回灌）
```

## 快速开始

```bash
lake exe cache get    # 首次必需：下载 Mathlib 预编译缓存（否则要编译数小时）
lake build
```

五条复跑命令（都只依赖仓库内脚本）：

| 想核什么 | 命令 |
|---|---|
| 规模（模块 / 行 / 声明 / job 数） | `bash scripts/measure.sh` |
| 缺口台账与七桶 | `bash scripts/list_gaps.sh` |
| 「空转缺口」的机械依据 | `bash scripts/check_vacuous.sh` |
| 「已证伪缺口」的源码层标记 | `bash scripts/check_refuted.sh` |
| **依赖版本锁是否一致** | `bash scripts/check_pins.sh` |

### 版本锁定（可复现性）

| 锁在哪 | 值 | 谁动 |
|---|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.35.0-rc3` | 换编译器才改 |
| `lakefile.toml`（mathlib `rev`） | 具体 commit `0f64d30a9a45…`（**不是** `master`） | 升级 mathlib 才改 |
| `lake-manifest.json`（mathlib `rev`） | 同上，必须与 lakefile **逐字相同** | 由 `lake update` 生成，改了就一起提交 |

⇒ 三者一致由 `bash scripts/check_pins.sh` 机器检查（CI 里也跑）。**不要**在不改 `lakefile.toml` 的情况下单独跑
`lake update` —— 那会让 manifest 漂到一个 lakefile 没声明过的 commit。

## 已形式化的内容

> 🚧 **under construction** —— 外部审计（W35–W38）结项后统一回填。
> 要准确数字请直接跑 `bash scripts/<对应脚本>`，不要引用本文件的旧数字。

## 规模

> 🚧 **under construction** —— 外部审计（W35–W38）结项后统一回填。
> 要准确数字请直接跑 `bash scripts/<对应脚本>`，不要引用本文件的旧数字。

## 缺口台账：七桶怎么读

> 🚧 **under construction** —— 外部审计（W35–W38）结项后统一回填。
> 要准确数字请直接跑 `bash scripts/<对应脚本>`，不要引用本文件的旧数字。

## 收录纪律（本仓库里到底有什么）

判据只有一条：**`git ls-files` 的输出必须与本节一致**。

- **项目成果**：`Phylo/**`、`Phylo.lean`、`README.md`、`LICENSE`、`scripts/`（四条护栏 ＋ `gap_ledger.py` ＋ `check_file_imports.sh` ＋ `measure.sh` ＋ `scripts/f84/`、`scripts/msc/` 的数据脚本）。
- **构建与 CI**：`lakefile.toml` · `lake-manifest.json` · `lean-toolchain` · `.gitattributes` · `.gitignore` · `.github/workflows/build.yml`。
- **仍在被证明引用的规格 / 发现记录（5 份，入库）**：`MSC_INSTANCE_SPEC.md` · `MSC_KINGMAN_SPEC.md` · `W10_COALESCENT_SPEC.md` · `CASTER_F84_PROPASPEC.md` · `CASTER_F84_FINDING.md`（以「`<文件名>` §x.y」被 docstring 指名引用，属证据链）。
- **不在库内**：工作日志 / 总结 / 卡点 / 交接文档、参考文献汇编（`references/`）、`MEMORY.md` / `HANDOVER.md`（由 `.gitignore` 挡住）—— 均在项目外维护，不在 GitHub 上。
