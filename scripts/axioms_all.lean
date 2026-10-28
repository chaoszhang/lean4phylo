/-
  axioms_all.lean —— 全库公理扫描（2026-10-28，外援 review_v2 #5 / audit_v2 建议 #1）

  ★ 为什么需要它：`axioms_snapshot.sh` 只抽查 10 条（人工挑的），而「没有偷偷引入信任公理」
    这件事应当**对全部收口定理**成立，不能靠抽样。
    本文件在 Lean 里遍历环境，把 **`Phylo.*` 模块里所有收口定理**（`_holds` / `_proved` /
    `_proof` / 含 `_vacuous_`）的公理依赖逐条打印出来，供 `scripts/check_axioms_all.sh` 逐字 diff。

  ★ 判据：每行 `全限定名 | 公理个数 | 公理名（逗号分隔，已排序）`。
    正常应当全是 `propext,Classical.choice,Quot.sound`（或子集）。
    出现 `sorryAx` / `Lean.ofReduceBool` / `Lean.trustCompiler` / 本库自定义公理 ⇒ 立即红灯。

  ★ 运行：`lake env lean scripts/axioms_all.lean`（需先 `lake build`，本文件 import 根模块）
  ★ 注意：`Lean.collectAxioms` 返回的是 **Array Name**（不是 NameSet），所以直接 map/sort 即可。
-/
import Phylo
open Lean

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let acc ← IO.mkRef (#[] : Array Name)
  env.constants.forM fun n _ => do
    match env.getModuleIdxFor? n with
    | some idx =>
      if (mods[idx]!).toString.startsWith "Phylo" then
        let s := n.toString
        -- 只取**具名声明**：排除编译器生成的内部辅助项（`…_proof_1_1` / `…_match_…` 等），
        -- 它们随证明体的写法变化，进快照只会制造假警报。
        let isInternal := s.contains "._proof_" || s.contains "._match_" || s.contains "._fun_"
          || s.contains "._cproof_"
        if !isInternal &&
           (s.endsWith "_holds" || s.endsWith "_proved" || s.endsWith "_proof"
            || s.contains "_vacuous_") then
          acc.modify (·.push n)
    | none => pure ()
  let ns := (← acc.get).qsort (fun a b => a.toString < b.toString)
  IO.println s!"# {ns.size} 条收口定理（Phylo.* 模块）"
  for n in ns do
    let ax ← Lean.collectAxioms n
    let xs := (ax.map (·.toString)).qsort (· < ·)
    IO.println s!"{n} | {xs.size} | {String.intercalate "," xs.toList}"
