# ComplexityReduction 项目参考

本文档记录 `archon-test` 对 ComplexityReduction 库的接入情况，与 Archon 打包数据中的
`complexity-reduction-library.md` 保持一致，并补充本项目当前需要的具体目标和导入策略。

## 本地依赖

- Lake 声明：`require ComplexityReduction from "../ComplexityReduction"`（见 `lakefile.lean`）。
- 源码路径：`../ComplexityReduction`，内层库目录为 `../ComplexityReduction/ComplexityReduction`。
- 工具链：`leanprover/lean4:v4.29.0`，mathlib `v4.29.0`。

## 导入策略

默认入口用聚合目标模块：

```lean
import ComplexityReduction.Targets
```

需要更宽的符号面时按需补充：

```lean
import ComplexityReduction.Core
import ComplexityReduction.SAT
import ComplexityReduction.CSP
import ComplexityReduction.Schaefer
import ComplexityReduction.Karp21
import ComplexityReduction.Bridges
import ComplexityReduction.Certificates
import ComplexityReduction.Templates
```

`Templates` 不在根导入内，使用归约模板时必须单独导入。

## 冒烟验证（已完成）

`ArchonTest/ComplexityReductionSmoke.lean` 已通过 `#check`：

- `ComplexityReduction.Targets.NPCTargetDescriptor : Type`
- `ComplexityReduction.Targets.threeSATDecisionProblem : ComplexityReduction.EncodedDecisionProblem`
- `ComplexityReduction.Targets.threeSATTarget : ComplexityReduction.Targets.NPCTargetDescriptor`
- `ComplexityReduction.Targets.localTargets : List ComplexityReduction.Targets.NPCTargetDescriptor`

构建命令：

```powershell
& 'C:\Users\14354\.elan\toolchains\leanprover--lean4---v4.29.0\bin\lake.exe' build ArchonTest.ComplexityReductionSmoke
```

## 当前目标

本项目暂未定义 ComplexityReduction 相关的证明目标。后续如需证明某问题 NP 完全，应：

1. 从 `Targets.localTargets` 选择目标描述符。
2. 优先复用 `CostedReduction.comp`、`Templates.*`、`NPCompleteEnc.transfer`、`composeTMKarp`。
3. 每个新声明必须编译通过且 axiom-clean，`#print axioms` 只允许 `propext`、`Classical.choice`、`Quot.sound`。

## 信任边界

默认可用的 Targets 子模块：`ThreeSAT`、`ThreeSATCompleteBoundary`、`NPCTargetCatalog`、
`Karp21Catalog`、`CountingCSP`、`FiniteDomainCSP`、`HColoringCatalog`、
`HColoringComplexityCatalog`、`NPCTransfer`。

需要 explicit opt-in 的外部 Schaefer bridge 模块：`Targets.Schaefer`、
`Targets.SchaeferFiniteDomain`。这些只记录边界元数据，不把外部定理搬运进本项目的
`EncodedDecisionProblem` 基础。注意 import 级差异：`Targets.Schaefer` 被
`NPCTargetCatalog` 间接导入（仅取字符串常量），其类型在作用域内但不含外部定理；
`Targets.SchaeferFiniteDomain` 不被任何默认模块导入。实质信任边界是数据级的：
`localTargets`/`initialTargets` 排除外部描述符，只有 `targetsWithExternalBridges` 才包含。

## 搜索库

Archon 打包了 `search_complexity_reduction.sh`，默认指向 `../ComplexityReduction/ComplexityReduction`。
也可直接用 `rg`：

```bash
rg -n "NPCompleteEnc" ../ComplexityReduction/ComplexityReduction/
rg -l "Schaefer" ../ComplexityReduction/ComplexityReduction/
```

## 详细符号表

完整符号表见 Archon 打包参考 `complexity-reduction-library.md`，此处不重复。本文件只记录项目级接入状态和本地验证结果。
