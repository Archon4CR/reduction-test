# ReductionTest — 归约证明测试项目

本项目使用 Archon 自动定理证明框架和 ComplexityReduction 库，完成了 3 道 NP 完全性归约问题的 Lean 4 形式化证明。全部证明 0 sorry、axiom-clean（仅依赖 propext、Classical.choice、Quot.sound），lake build 绿色。

## 证明概览

| 文件 | 归约 | CR 复用策略 |
|------|------|-------------|
| ReductionTest/NAE3SAT.lean | 3SAT -> NAE-3SAT | REUSE — 直接 re-export CR 库已有归约 |
| ReductionTest/DoubleSAT.lean | SAT -> DOUBLE-SAT | BUILD_NEW — 从零构建编码和归约 |
| ReductionTest/IndependentSet.lean | CLIQUE -> Independent Set | PARTIAL — 复用 CR 补图基础设施 |

## CR Advisor 报告

advisor-reports/ 目录包含 ComplexityReduction advisor 子代理在证明前生成的 3 份分析报告，分别判定每道题的复用策略（REUSE / BUILD_NEW / PARTIAL）并给出 CR 库 API 定位。最终证明策略与报告建议完全一致。

## 构建

```powershell
lake build ReductionTest
```

依赖 ComplexityReduction（本地路径 ../ComplexityReduction）和 mathlib（v4.29.0），lean-toolchain 为 leanprover/lean4:v4.29.0。

## Blueprint

blueprint/src/ 包含半形式化 LaTeX 文档，描述每道归约题的数学证明思路。
