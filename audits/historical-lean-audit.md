# 星形 Kakeya 历史 Lean 下界迁移核验（只读）

## 结论

**不能只搬公开仓库的 44 模块。** 真实入口 July-31 仍是 `100π/5599` 路线；更晚的历史源在 `kakeya-closeout`，含独立 annular `131π/6250`、N32 `141/2000`、N64 `3527/50000` 和完整长分数乘 π。它们的静态 import 闭包都不含 OneTenth，因此不是事后从 `1/10` 降格推出。此结论是源依赖事实，不是本次内核重验。

**本次零 Lean 构建、零依赖安装、未读取 .lake 内容、未改源代码或 Git。** 只写本报告及 `historical-lean-files.json`。证据分为：当前源代码形状、当时文档/原生收据、本次静态核验；没有把文件名、无 sorry 扫描或 Audit 指令源当成已执行证明。

## 路径别名与版本

- O = `/home/argustest/research/star-shaped-kakeya/materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`
- H = `/home/argustest/research/kakeya-closeout/materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`
- P = `/home/argustest/research/star-shaped-kakeya-lean`
- O Git HEAD = `a1a2243aa4af423611c7d5d5f0ff0f0c7f16a171`
- H Git HEAD = `2587e7eb9f379a5858fdf9a2e0f3e1dfcd6cc5ef`；工作树源逐文件 SHA-256 见 JSON，不能仅用 HEAD 代表本次文件字节。
- P Git HEAD = `d46da66b8147490b42d73f91464bd55a8010db47`

下文 `O/…:行` / `H/…:行` / `P/…:行` 均以这些绝对路径展开。

## 真正的共同假设

`O/StarKakeyaLower/StarKakeyaSet.lean:23–26,146–168,210–216`：
`Plane := EuclideanSpace ℝ (Fin 2)`，`Direction := AddCircle Real.pi`；单位针的两端距离 1，carrier 是**完整闭线段**；方向通过实数角 lift 与非零标量表达，允许反向。`StarKakeyaLower.StarShapedKakeya E` 的字段只有共同 `center`、从该点到 E 内各点的闭线段包含性 `star`、各无向方向存在整条单位针 `needle_exists`。

下列全局端点只要求这个结构；**不要求 E 可测、有界、闭，不要求原选针可测或连续**。内部存在 height/certificate/local-integral 参数不等于最终端点额外假设：必须看最终模块是否构造了参数。各版本结构源都保留在恢复映射中；公开旧原生 `OneTenthParentAudit.log:1–33` 还直接打印了输入与原始几何适配。

## 常数、完整名称、源证据、历史验收

### 1. π/56：只定位到独立算术路线，不冒充全局 endpoint

- `StarKakeyaLower.caseI_seven_strict`：`O/StarKakeyaLower/ArithmeticKernel.lean:105–110`，结论是 `1/56 < caseILower integralLower7`，不是面积。
- `StarKakeyaLower.alt_caseI_strict`：`O/StarKakeyaLower/NonIterativeKernel.lean:133–140`；`StarKakeyaLower.alt_height_strict`：同文件 `211–216`，结论 `π/56 < altA/2`，仍是数值层。
- 旧参数两套分别在 ArithmeticKernel `16–24` 与 NonIterativeKernel `18–26`。前者是带 `1-qLower` 分母的旧计算式，后者是非迭代候选；不能混成同一次全局证明。
- July-31 `CURRENT-STATE.md:187–191` 明说 ArithmeticKernel 仅 audit 可达；本次发现该模块单独只 import Mathlib。保留其源是保存真实旧路线，不是说当时已有独立 π/56 几何端点。
- `StarKakeyaLower.strong_target_strictly_improves_pi56` 在 StrongerKernel `116–118` 只比较系数。由已闭合的较强结果可得弱界，但不能反写为早期独立完成证明。

### 2. 严格 100π/5599（July-31）

- 完整名：`StarKakeyaLower.universal_strong_lower_bound`。
- `O/StarKakeyaLower/UniversalAssembly.lean:37–39` 定义 `UniversalStrongLowerBound := ∀ E, StarShapedKakeya E → ofReal (Real.pi * 100 / 5599) < volume.toOuterMeasure E`；`216–221` 最终无条件证明。
- `179–193` 中间 `strong_lower_bound_of_caseI` 仍要 endpoint 参数；`216–217` 用 `caseIEndpointPointwiseTheorem_proof` 消除它，因此不能停在条件层，也不能因“Conditional”文件名否认最终闭合。
- **旧文档收据**：`O/../00-status/AUDIT-RECEIPT.md:34–64` 列出三种构建通过并转录最终公理 `[propext, Classical.choice, Quot.sound]`；`/home/argustest/research/star-shaped-kakeya/notes/02-archive-audit.md:64–75` 转录 `Build completed successfully (8322 jobs)`。这不是本次运行，也不是本次所见原始终端日志。

### 3. 严格 131π/6250（annular，新独立路线）

- 完整名：`StarKakeyaLower.universal_annular_lower_bound`、`StarKakeyaLower.universal_annular_lower_bound_normalForm`。
- `H/StarKakeyaLower/AnnularKernel.lean:33`：`annTarget = 131/6250`；`H/StarKakeyaLower/AnnularAssembly.lean:194–195,228–247` 给出无条件几何结论和正常形式。
- 最终源先分 high 情况，否则把**同一个球**内外的实际外测度账合并，再用互补方向集的外测度之和至少 π；不是假设方向类可测或凭空把两次同面积相加。
- 只读路径历史定位 commit `b87c6a1b3f51e8569c3454a21467615d5d0cf489`（2026-08-02）。当前根含自身 33 模块；旧文档“32”是列出依赖不含 AnnularAssembly 自身，不能误报闭包变坏。
- **旧构建及公理收据**：H 所属仓库 `spikes/001-joint-inner-outer/LEAN-STATUS.md:1962–2022`（磁盘缺失，但 Git HEAD blob 可读取）；完整相关片段已嵌入本报告末节。含项目冷重建 2m35s 的历史自述、477 个 audit 输出的总结及该端点三公理转录；不是独立原始 log，也没有逐文件哈希绑定。

### 4. 严格 141/2000（N32）

- 完整名：`StarKakeyaLower.Witness141.universal_one_forty_one_over_two_thousand`；其 `_le` 弱化版本也在源中。
- `H/StarKakeyaLower/EndpointCapacityFinal141.lean:16–32`：量词 `∀ E, StarShapedKakeya E → ofReal (141/2000) < volume.toOuterMeasure E`；调用最终 assembly 并用 `common_mul_lowUnion_le_lintegral` 与 `common_mul_tsum_highClass_le_lintegral` 实例化两个本地付款参数。
- `EndpointCapacityFinalAssembly.lean:228–237` 本身仍有 `hlocal`；不能只把它认作完成。但 Final141 已给出两个生产者。
- 路径历史首个定位 commit `797a149f2b6a11ebf4b7c204f7033273059fb813`。`H/StarKakeyaLower/Audit.lean:390–391` 有相应打印指令。
- **缺证**：本轮限定检索未定位对应已执行原生构建及这两个端点的原始公理输出；仅源码和 Git 提交不等于原生验收。旧普通证明 `UNIVERSAL-141-OVER-2000.md:291–292` 仍写当时尚无 Lean，这是较早文档，不应抹掉后来完整源，也不能替代后来的执行收据。

### 5. N64：完整长分数乘 π，以及严格 3527/50000

- 完整名：`StarKakeyaLower.Witness3527.universal_certifiedCoefficient_mul_pi`。
- `H/StarKakeyaLower/EndpointCapacityWitness64Data.lean:10–24` 确认 namespace 及
  `certifiedCoefficient = 120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423 / 5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000`。
- `H/StarKakeyaLower/EndpointCapacityFinal3527.lean:16–28` 结论为 **`ofReal (certifiedCoefficient * Real.pi) ≤ volume.toOuterMeasure E`**，不是严格号。`31–43` 的
  `StarKakeyaLower.Witness3527.universal_three_five_two_seven_over_fifty_thousand`
  才是严格 `ofReal (3527/50000) < …`，并另有 `_le`。
- 同样从具体 low/high 积分付款生产者消除 hlocal；`EndpointCapacityFinalAssembly64.lean:302–311` 单独只是条件接口。
- 历史 commit `2f5dc62be87f8c71ea282dee57c8b801f433a9c7`（2026-08-04，N64），`97914ccad79766e8d1e16d727b72a0dae29684c6`（同日，完整系数乘 π）。
- `H/StarKakeyaLower/Audit.lean:453–455` 是打印指令；**与 N32 一样，已执行原生 build/最终 axioms 原始输出本次未定位，不能标作本次可信内核 endpoint**。保留完整源码闭包，以免搬机丢失真实独立历史。

### 6. 最终公开 1/10（仅作锚点，禁止重编）

- 完整名：`StarKakeyaLower.StarShapedKakeya.one_tenth_le_outerArea`，`P/StarKakeyaLower/OneTenth.lean:12–18`。
- 旧真实原生收据：`P/.closeout-build/run-ce9yb8h_/build.json:1–8` 为 `status=passed, exit_code=0`；完整收据记录 44 个源哈希。本次只是读取并重新计算源 SHA-256：**44 个比较，差异 0**。
- `…/environment.json:2–6` 记录 Lean 4.30.0-rc2、原生编译器 commit/摘要；`…/logs/StarKakeyaLower.OneTenthAudit.log:25` 与 `…/logs/StarKakeyaLower.OneTenthParentAudit.log` 的末两行记录最终端点与 raw_hypotheses 的三公理。
- 这些日志真实存在，已加入白名单；本次没有启动 Lean，也未重查依赖缓存或所有历史 oleans。

## 最小值得保存的闭包与锁

这里的“闭包”是**项目内 import 文件闭包**，不是 theorem-term 常量闭包，也不是展开整个 Mathlib 的源闭包。扫描去除了嵌套块注释/行注释，读取实际 import；每个项目 import 均解析到文件。没有调用 Lean 的原生 header parser，因此不将其等同于编译验收。

| 快照 | 根模块 | 模块数（含根） | 含 OneTenth |
|---|---|---:|---|
| july31 | `StarKakeyaLower.UniversalAssembly` | 32 | 否 |
| july31 | `StarKakeyaLower.Audit` | 35 | 否 |
| historical | `StarKakeyaLower.UniversalAssembly` | 39 | 否 |
| historical | `StarKakeyaLower.AnnularAssembly` | 33 | 否 |
| historical | `StarKakeyaLower.EndpointCapacityFinal141` | 39 | 否 |
| historical | `StarKakeyaLower.EndpointCapacityFinal3527` | 39 | 否 |
| historical | `StarKakeyaLower.Audit` | 87 | 否 |
| public_tenth | `StarKakeyaLower.OneTenth` | 42 | 是 |
| public_tenth | `StarKakeyaLower.OneTenthAudit` | 43 | 是 |
| public_tenth | `StarKakeyaLower.OneTenthParentAudit` | 43 | 是 |

建议保存三个逻辑快照：
1. O 的 UniversalAssembly + Audit（35 模块）及根/配置，保留 July-31 独立版本和两套 π/56 算术。
2. H 的历史 Audit 闭包（87 模块），覆盖 100π/5599、annular、N32、N64 及小型历史审计/反例；**不打包 H 中后来 OneTenth 分支、probe、.closeout-build 或全工作树**。只保存最终定理所需源时可以用 JSON 各 endpoint 闭包取并集；为了原 audit 可恢复，这次白名单额外保留它的小型控制模块。
3. P 的两个 audit 根的并集（44 模块）及现存成功原生收据/构建脚本，作为最终已验基准。

JSON `whitelist` 是绝对路径、按 SHA-256 内容去重后的实际载荷；`restore_map` 保存每个原逻辑路径到载荷路径的映射，**恢复各快照时必须按映射重建，不能直接把不同版本同名模块混在一起**。193 个逻辑文件映射到 161 个唯一内容文件，字节合计 2416042；只用于本附件范围，父任务另算整体净载荷。所有条目均为真实现存小文件；没有把 Git-only 虚构路径塞入白名单。

锁：O `lean-toolchain:1`，`lakefile.toml:18–21`，`lake-manifest.json:4–93`；P `dependencies.lock.json` 与 `lake-manifest.json` 锁同一组九个仓库（Mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`），Lean 均 4.30.0-rc2。**H 磁盘缺 lake-manifest.json**，只保留了 toolchain/lakefile；同版本 O/P 清单作为迁移恢复依赖锁保留，但不能声称是 H 原生验收时的完整依赖环境证据。Mathlib 中有 `import Mathlib`，不能把几十项目模块描述成脱离上游的自足证明。

不迁移 `.lake`、oleans、IR、共享依赖的每份重复树、原数值大 JSON、整个 Git 历史、ZIP、上界源或 PDF/TeX（父任务负责）。若要求离线恢复，另需单份**精确 pin 的共享依赖源/工具链**；本次不扫描也不打包它们。

## 明确的未完成证据与风险

- N32/N64 源端点及其完整本地 import 闭包已找到；已执行历史 native 和 axioms 原始收据尚缺。这是缺证，不是证明发现错误，也不应标为完整原生验收。
- π/56 的独立全局端点未找到；1/15、7/100 等旧普通数学常数在早期证明文件中出现，但本次定位到的实际独立 Lean 最终端点是上述 N32/N64。不得仅按常数或文件名扩充已 Lean 化列表。
- O/H 历史文档日志缺逐源摘要，不能断言本次文件与当时全部字节相同。只有 P 的既有 44 模块 build receipt 已逐源哈希核对。
- 原工具一次错误拦截了只读脚本（误判 gateway 操作）；改用 execute_code 的 Python 只读路径继续，没有重启/停止任何进程。
- 检索有明确边界：入口 O、同项目 notes/audit、H 相关历史源及短路径历史、P 收据；没有扫描全部数千 worktree，也不能以此声称所有其他历史端点均不存在。

## 内嵌 Git-only 历史收据（搬机时随本报告保存）

来源：`/home/argustest/research/kakeya-closeout`，commit `2587e7eb9f379a5858fdf9a2e0f3e1dfcd6cc5ef`，`spikes/001-joint-inner-outer/LEAN-STATUS.md`；完整 blob SHA-256 `ec35ee84ee817ac071ae41c1791907ed6991ea4ca703fbbc605cd4e963e711d6`。原磁盘文件缺失，以下为本次 `git show` 真正读到的行号转录，不是新运行结果。

```text
1962: ### 22.7 Builds
1963: 
1964: All green, from the worktree Lean root
1965: `materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`
1966: (toolchain `leanprover/lean4:v4.30.0-rc2`, Mathlib
1967: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`, both unchanged):
1968: 
1969: ```
1970: lake build StarKakeyaLower.AnnularAssembly        Build completed successfully (8345 jobs)
1971: lake build StarKakeyaLower                        Build completed successfully (8364 jobs)
1972: lake build StarKakeyaLowerAudit                   Build completed successfully (8367 jobs)
1973: lake build StarKakeyaLower StarKakeyaLowerAudit   Build completed successfully (8369 jobs)
1974: ```
1975: 
1976: A cold rebuild with all project oleans and IR deleted (Mathlib oleans kept)
1977: succeeded in `2m35s`, so no stale olean is involved.
1978: 
1979: `AnnularAssembly.lean` emits **zero** warnings — including zero style-linter
1980: warnings; the two deprecated aliases `mul_le_mul_right'` / `mul_le_mul_left'`
1981: that the first draft used were replaced by the current `mul_le_mul_left` /
1982: `mul_le_mul_right`.
1983: 
1984: ### 22.8 Axiom receipts
1985: 
1986: `lake build StarKakeyaLowerAudit` emits **477** `#print axioms` receipts. After
1987: normalising the line wrapping, the set of distinct axiom lists has exactly one
1988: element:
1989: 
1990: ```
1991: propext, Classical.choice, Quot.sound
1992: ```
1993: 
1994: No `sorryAx`, no `Lean.ofReduceBool`, no `Lean.ofReduceNat`, no
1995: `Lean.trustCompiler` occurs anywhere in the audit output. The seventeen new M7
1996: receipts (`Audit.lean:554`–`:570`) are
1997: 
1998: ```
1999: StarKakeyaLower.annCExt                                   [propext, Classical.choice, Quot.sound]
2000: StarKakeyaLower.annCExt_eq_literal                        [propext, Classical.choice, Quot.sound]
2001: StarKakeyaLower.annJointCoefficient                       [propext, Classical.choice, Quot.sound]
2002: StarKakeyaLower.annJointCoefficient_le_annILower          [propext, Classical.choice, Quot.sound]
2003: StarKakeyaLower.annJointCoefficient_le_annCExt            [propext, Classical.choice, Quot.sound]
2004: StarKakeyaLower.annTarget_lt_annCExt                      [propext, Classical.choice, Quot.sound]
2005: StarKakeyaLower.annTarget_lt_annJointCoefficient          [propext, Classical.choice, Quot.sound]
2006: StarKakeyaLower.annJointCoefficient_pos                   [propext, Classical.choice, Quot.sound]
2007: StarKakeyaLower.directionAngleOuter_le_pi                 [propext, Classical.choice, Quot.sound]
2008: StarKakeyaLower.pi_le_directionAngleOuter_add_compl       [propext, Classical.choice, Quot.sound]
2009: StarKakeyaLower.ann_target_lt_high_threshold              [propext, Classical.choice, Quot.sound]
2010: StarKakeyaLower.annular_joint_ledger                      [propext, Classical.choice, Quot.sound]
2011: StarKakeyaLower.annular_lower_bound                       [propext, Classical.choice, Quot.sound]
2012: StarKakeyaLower.UniversalAnnularLowerBound                [propext, Classical.choice, Quot.sound]
2013: StarKakeyaLower.universal_annular_lower_bound             [propext, Classical.choice, Quot.sound]
2014: StarKakeyaLower.pi_mul_annTarget_eq                       [propext, Classical.choice, Quot.sound]
2015: StarKakeyaLower.universal_annular_lower_bound_normalForm  [propext, Classical.choice, Quot.sound]
2016: ```
2017: 
2018: and the old final theorem is unchanged:
2019: 
2020: ```
2021: StarKakeyaLower.universal_strong_lower_bound              [propext, Classical.choice, Quot.sound]
2022: ```
```
