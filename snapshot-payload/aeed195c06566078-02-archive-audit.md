# 归档审查与复现记录

审查日期：2026-08-01

## 1. 归档完整性

原始 ZIP：

```text
archive/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31.zip
SHA-256: 58f10154d927fb55514a11c0922468289ec8e5c6eb636a52026f9c5e32ee4c5f
```

内置深度验证器输出：

```text
DEEP_VERIFY_OK
entries=106
manifest_entries=105
required_paths=22
findings=0
```

解压后重新运行顶层 manifest 校验，无 hash mismatch。归档在传输和解压层面可信。

## 2. Python 证书

环境：项目 `.venv`，Python 3.12.11，`numpy 2.5.1`、`sympy 1.14.0`、`python-flint 0.9.0`。

下界脚本全部正常退出：

- `verify_pi56_noniterative_kernel.py`
- `verify_pi56_parametric_caseii_kernel.py`
- `verify_pi56_optimization_reduction.py`
- `verify_pi56_stronger_candidate.py`
- `interval_pi56_raw_family.py`

关键结果：

- 精确 Case I、Case II、height margins 均为正。
- 弱化 logarithmic tail 的 mutation 为负。
- 固定 Arb 候选点的三个分支都严格高于 `100/5599`。
- 把 `p=8329/10000` 改为 `8330/10000` 后，Case II mutation 严格低于目标。
- 全参数域仍是 `unresolved-domain`，所以没有证明 one-threshold family 的全局最优值。

上界脚本全部正常退出：

- `verify_showcase_spline_geometry.py`
- `certify_showcase_spline_finite_n.py`
- `audit_campaign_best_finite.py`
- `verify_elegant_rational_bracket.py`
- rational-seven 的 direction、continuum、finite lift 和 simple bound 四个 verifier

关键结果：

- `E_51` 的 exact spline algebra、Bernstein signs 和 reflection 通过。
- `area(E_51)/π < 0.09047481313467504`。
- `n=31` mutation 被拒绝。
- 重建的 campaign ranking JSON 与归档冻结版本逐字一致。
- rational-seven 的 continuum gap、finite lift 和 `n=80001` negative control 均按文档复现。

这些结果说明证书程序与冻结数据一致。它们不是独立证明，因为数学归约和验证代码来自同一项目。

## 3. Lean 复现

第一次同时冷构建上下界时，两个 Mathlib cache 解压进程触发 `No file descriptors available`。主机 shell 的软限制是 1024。改为串行执行并设置 `ulimit -n 65535` 后，两边构建成功。

下界：

```text
lake build
Build completed successfully (8322 jobs)
```

`Audit.lean` 报告的依赖仅为 Mathlib 常见的 `propext`、`Classical.choice`、`Quot.sound`。源码中未找到 `sorry`、`admit` 或自定义 `axiom`。

上界：

```text
lake build StarKakeya.RationalSevenArea
Build completed successfully (3346 jobs)
```

构建有大量 lint warning，但无 error。源码中未找到 `sorry`、`admit` 或自定义 `axiom`。

## 4. 当前 Lean 边界

### `E_51` 最强候选

`upper-bound/03-lean/StarKakeya/Targets.lean` 仍只提供条件式接口：
`CandidateCertificate E51` 没有构造出的 Lean term。因此 51-cell数值不是当前定理。

### rational-seven 上界

最终模块 `StarKakeya.FinalAreaTheorem` 现已无条件证明

```text
area E_100001 < ENNReal.ofReal ((77/851) * Real.pi)
```

以及对 Cunningham--Schoenberg常数的严格改进。生成式区间证书所用
`native_decide` reflection axioms在独立 Audit target中披露。

### `100π/5599` 下界

最终模块 `StarKakeyaLower.UniversalAssembly` 现已无条件证明：对每个星形
Kakeya集，二维Lebesgue外测度严格大于 `100π/5599`。quotient-circle、endpoint
geometry、Case II residual fan、outer-measure和最终assembly均已闭合；顶层
公理足迹仅为 `propext`、`Classical.choice`、`Quot.sound`.

## 5. 当前风险与边界

1. `E_51` 仍缺 event-completeness独立证明和 Lean certificate term，不能作为上界定理。
2. Upper rational-seven proof中的大型可判定证书通过 scoped `native_decide`检查；其 compiler/reflection信任边界必须与lower纯kernel路径区分披露。
3. 上下界虽已通过Lean与内部独立审查，仍未替代外部同行评审。
4. 文献检索未发现更强结果，不等于历史优先权已被证明。
5. Manifest是包内完整性记录，不提供作者身份、可信时间戳或优先权证明。
6. 当前源码清理后必须重生 nested/combined manifests、source maps和ZIP，旧归档哈希在重生前仅代表冻结快照。

## 6. 进一步独立审查结论

独立只读审查复跑了 `E_51`、campaign ranking、rational-seven continuum/lift/bracket 和下界固定参数 verifier，结论与本轮主审一致。它额外指出：

- `E_51` 的 event completeness 迁移自 `E_201` 的论证，并没有一份专门针对 spline profile 的独立成册证明。这是 strongest upper bound 与较透明的 rational-seven 备用上界之间最关键的审查差别。
- `E_201` JSON 中的 `open_gaps: []` 只适用于该证书内部定义的闭合范围，不能覆盖包外独立审计、完整 Lean 或全局最优性。
- manifest 是自签式完整性记录。它证明包内 payload 与清单一致，不证明作者身份、可信时间戳或历史优先权。
- campaign-best 只是在一个人工策展的三元素 registry 中最好，不是对所有构造的完备搜索。

## 7. 当前证据等级

| 主张 | 当前等级 |
|---|---|
| Li `π/98` 下界 | 已发表、可核验 |
| 归档完整性 | 已复现 |
| Python exact/interval 输出 | 已复现 |
| Production Lean builds | 已复现；上下界顶层 theorem均闭合 |
| `100π/5599` 通用下界 | 无条件 Lean theorem；仅标准三 axioms |
| rational-seven `77π/851` 上界 | 无条件 Lean theorem；native certificate边界已披露 |
| `E_51` 最强候选 | exact computation；event completeness与Lean certificate term仍缺 |
| 全局最优常数 | 开放 |
