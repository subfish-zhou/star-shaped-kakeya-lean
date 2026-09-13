# Lean 依赖图与顶层缺口

## 下界工程

项目：`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`

顶层定理已闭合：

```lean
theorem StarKakeyaLower.universal_strong_lower_bound :
    ∀ (E : Set Plane), StarShapedKakeya E →
      ENNReal.ofReal (Real.pi * 100 / 5599) < volume.toOuterMeasure E
```

公理足迹仅 `propext`、`Classical.choice`、`Quot.sound`。

### 构建目标

```bash
lake build                                       # 生产根，= lake build +StarKakeyaLower
lake build StarKakeyaLowerAudit                  # 审计目标（#print axioms 回执）
lake build StarKakeyaLower StarKakeyaLowerAudit  # 全库
```

生产根 `StarKakeyaLower.lean` 只 import `StarKakeyaLower.UniversalAssembly`，
不 import `Audit`；`Audit` 是独立 Lake target，只 import 它真正需要的三个根
（`UniversalAssembly`、独立的 `ArithmeticKernel`、仅供审计的 `NegativeControls`）。

### 模块依赖链（自底向上）

```text
ArithmeticKernel                独立的 π/56 有理 kernel（不在生产闭包内，仅审计目标可达）
NonIterativeKernel              旧候选的三分支 exact margins
AnalyticKernel -> AnalyticBranches   log / arctan / branch dominance / 积分 primitive
StrongerKernel                  100/5599 固定参数、exact margins、StrongParameterDomain
StarKakeyaSet -> TriangleArea -> Trichotomy   星形 Kakeya 谓词与 height/confined/exterior 三分支
CircleDilation -> QuotientCircle             任意族 quotient-circle dilation 定理（含 hybrid 开/闭版本）
LiGeometry                      support 坐标、polar trace、ClosedTraceDecomposition、FirstArcData、JGamma
                                以及 support 参数原语（由已删除的 LiEndpointFatality 迁入）
PolarOuterMeasure -> PolarProjectiveOuter -> CaseIAssemblyConditional
                                极坐标切片、二对一投影、radial integral、
                                FirstArcPointwiseHybridCriticalContainment
LiLemma23 -> StrongLiLemma25    exterior 面积演算与已证的 Li Lemma 2.5
CaseIEndpointAnalytic -> CaseIEndpointR1Analytic -> Figure5EndpointEnvelope
  -> Figure5LocalContact -> UniversalFirstArc -> UniversalEndpointClosure
                                三分支 g、R₁ endpoint envelope、Figure 5 基点几何、
                                pointwise local contact 与 Case-I endpoint 闭合
CaseIIGeometry -> CaseIISelection -> CaseIIAnalytic / ParametricCaseII
                                Case II 选择、minimax 与 strongCaseII_radius_branch
LiNeedleAdapter -> UniversalNeedleAdapter -> UniversalAssembly
                                raw/physical needle 适配与最终无条件装配
NegativeControls                仅审计可达的回归防护（exterior arcsine dispatch 反例）
Audit                           #print axioms 回执
```

### 已删除的历史脚手架

`LiEndpointFatality.lean`、`CaseIEndpointPointwise.lean`、
`UniversalSupportHeight.lean`、`QuotientCircleAudit.lean` 已删除；
`CaseIEndpointAnalytic` 与 `Figure5EndpointEnvelope` 中的 all-support graph /
extrema / `Actual*` / `Raw*` endpoint-law 子树亦已删除。它们都不在
`universal_strong_lower_bound` 的依赖闭包内；仍被使用的少量原语迁入 `LiGeometry`。

### 下界剩余开放项

不再是定理强度缺口，而是优化问题：参数族的全局最优、
cross-radius 与 Bellman 改进（见 `05-open-work/ROUND-5-...`）。

## 上界工程

项目：`upper-bound/03-lean`

### 根模块与构建目标

`StarKakeya.lean` 是最小 production root，只 import
`StarKakeya.FinalAreaTheorem`。条件式的 `StarKakeya.Targets`/E51 campaign API
仅通过显式模块或 `StarKakeyaAll` 提供，不进入已证明的 production endpoint。

```bash
lake build                    # production root +StarKakeya（默认目标）
lake build +StarKakeya.Audit  # command-only axiom 审计，不进入生产闭包
lake build StarKakeyaAll      # 整个 library
```

### 已编译层

```text
Definitions
  Plane、StarShapedAt、TurningNeedle、Admissible、area

RationalSeven
  literal E_100001 数据和 admissibility

RationalSevenProfiles + Signs
  profile 恒等式、导数、Bernstein/Sturm signs

RationalSevenRadial + Envelope
  contact equations、inverse、monotonicity、measurability、density identities

RationalSevenArea
  stationary 与 endpoint active interval 的积分换元

RationalSevenAcuteFold / AcuteTail / FiniteSineFactor / NewlyFeasibleEndpoint
  finite-n 分支分类与 uniform eta

RationalSevenGlobalGeometry / Reflection / ParallelContacts /
FundamentalInterior / FundamentalBoundary / GlobalPointwise
  cyclic + reflection 对称、任意角 reduction、全局 pointwise majorant

RationalSevenGlobalArea / FoldIntegral / PolarFoldBridge /
RationalSevenAreaErrorIntegration
  极坐标面积桥、fold 归一化、finite-lift 面积误差

SwitchCertificateInterval / Phase1Data / Phase2Data / Phase2Roots /
Phase3Data / Phase3
  生成的 switch 系统证书与其 Lean 侧 soundness

AreaPrimitiveCertificateData / AreaPrimitiveCertificate /
ContinuumDominanceData / ContinuumDominance / FinalAreaAssembly
  六段 primitive 证书、branch dominance 区间、六段积分装配

FinalAreaTheorem
  顶层无条件定理 area E_100001 < (77/851)π 及对经典上界的严格改进

SimpleBound
  77/851 与 Cunningham-Schoenberg radical 常数比较

Targets
  E_51 的 CandidateCertificate 接口（仍是显式假设）
```

### rational-seven 依赖链（已闭合）

```text
五个 switch 的 exact ordering 和 active label
  -> [0,1] 的六段 partition
  -> 每段 envelope 等于 endpoint 或 stationary branch
  -> 六段积分和等于 continuum area
  -> continuum area 小于冻结 rational threshold

finite branch completeness
  -> D >= 3 tail cutoff
  -> only shift-0 minus newly feasible
  -> global Lipschitz bound
  -> uniform eta_n
  -> finite area excess <= 2 eta_n + eta_n²

continuum gap + finite excess
  -> area E_100001 < 77π/851
  -> 顶层 unconditional theorem
```

该依赖链已全部闭合：switch partition 由 `SwitchCertificatePhase1..3` 与
`ContinuumDominance` 提供，六段积分由 `AreaPrimitiveCertificate` 与
`FinalAreaAssembly` 提供，有限 `n` 装配由 `RationalSevenFiniteSineFactor`、
`RationalSevenGlobalPointwise` 与 `RationalSevenAreaErrorIntegration` 提供，顶层
定理是 `FinalAreaTheorem.rationalSeven_area_lt_simpleArea`。`RationalSevenArea.lean`
本身仍只负责单个 active interval 的换元公式。

### `E_51` 缺失依赖链

```text
rational not-a-knot spline literal data
  -> spline interpolation/C²/not-a-knot/reflection
  -> profile signs
  -> odd-cycle endpoint motion
  -> finite event completeness
  -> Arb/integer certificate checker
  -> literal CandidateCertificate term
  -> candidate_strictly_improves_cs
```

`Targets.lean` 当前只证明：给定 `CandidateCertificate E51`，则 `E51` 严格改进经典常数。该 structure 没有 term，因此不是最终 theorem。

## 信任基线

每个新增模块必须：

1. 无 `sorry`、`admit`、自定义 `axiom`；
2. 最小模块 `lake build` 通过；
3. 最终 theorem 运行 `#print axioms`；
4. 允许的常见 Mathlib footprint 为 `propext`、`Classical.choice`、`Quot.sound`；
   使用 `native_decide` 的 certificate 定理额外带出生成的
   `_native.native_decide.ax_*`，必须显式记入信任基；
5. 计算证书必须以内化 checker 或可核验 theorem 接入，不能把结论包装成新的假设。
