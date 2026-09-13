# 上界证据映射

本文件对应论文附录“形式化定理与证据接口”和上界章的固定输入层。路径相对于本文件；这些上界原件是历史来源快照。此次新编译对象是普适 1/10 下界，不能用它替代下面的上界证据。固定参数的支配关系也不扩张为所有放置或所有有限竞争体的关系。

## U-E1：固定多项式、反射与端值

- 数学对象：论文的 α_fr、s、p0=1/2+α_fr。源码中的 `a` 对应 α_fr，不是后面扰动后的高度 a。
- [Data.lean](sources/closeout-supplement/frozen-upper-code/Data.lean)：`aCoefficients`（43行）、`sCoefficients`（53行）、`s`（65行）、`s_reflect`（73行）、`s_zero`/`s_one`（83–87行）。完整有序元组保存在该源和正文中。
- `targetAbsoluteArea`（98行）是另一项命名目标；不将它识别为 c_fr、U 或某个具体有限体的面积。

## U-E2：严格符号与起始条件

- [Signs.lean](sources/closeout-supplement/frozen-upper-code/Signs.lean)，命名空间 `StarKakeya.CurrentRational`。
- `s_pos`（2042行）；`Hplus_mem_Ioo`/`Hminus_mem_Ioo`（2051–2064行）给出正臂长及开盒。
- `Hplus_sub_s_div_t_pos` 与 `Hminus_sub_s_div_one_sub_t_pos`（2085–2101行）：在实际开单位区间内给出两侧严格起始条件。
- `abs_HplusPrime_lt_one`/`abs_HminusPrime_lt_one`（2075–2083行）只有导数绝对值界，**不用它们推非递增性**。
- 这些声明的证明使用原固定系数及其精确语义，不是候选 winner 标签。

## U-E3：端点映射、导数与凹高度

- [EndpointEnvelope.lean](sources/closeout-supplement/frozen-upper-code/EndpointEnvelope.lean)。
- `endpointMapPlus`/`endpointMapMinus`（16–17行）、`Jplus_identity`/`Jminus_identity`（28–36行）。
- `hasDerivAt_s`、`hasDerivAt_sPrime`（52–64行）；`strictAntiOn_sPrime`（69–75行）、`s_le_smax`（92–100行）。
- `hasDerivAt_endpointMapPlus`/`Minus`（122–138行）；`endpointMapPlus_deriv_gt_one_div_256`/`Minus`（152行起）给出真实端点映射的严格导数下界。
- 这些是原固定输入的性质，不转移给未验证的新高度/纵向放置。

## U-E4：冻结放置的非递增与严格递减

- [Continuum/PhaseC3.lean](sources/monotonicity-closure/StarKakeya/CurrentRational/Continuum/PhaseC3.lean)，命名空间 `StarKakeya.CurrentRational.Continuum`。
- `deriv_a_nonpos`（167–191行）：左右半区分别调用实际 Bernstein 语义与已检查系数；`antitoneOn_a`（193–200行）将其提升到闭单位区间。
- `Hplus_eq_endpointRadius`（202–204行）：Hplus=1/2+a。
- 与 U-E1 的非常数多项式身份结合，得 p0 严格递减：若两点取同值，非递增迫使中间区间恒定，多项式遂全局恒定，与固定端值/系数矛盾。
- [UPPER_MONOTONICITY_CLOSURE.json](UPPER_MONOTONICITY_CLOSURE.json) 保存该模块及其全部本地导入的原路径、拷贝路径和 SHA-256。此次逐字保存整个本地闭包；并未重编译上界 Bernstein 证明或声称重新检查第三方依赖。

## U-E5：固定相位区间的真实支配

- [BAND_PROJECTION_STRICT_COMPARISON_ATTEMPT.md](sources/later/BAND_PROJECTION_STRICT_COMPARISON_ATTEMPT.md) §§2–7 与同目录最终 ADJUDICATION：实际 run00/run09 的源区间输入、四种投影排序、first-hit 唯一性及正面积缺片的应用链。
- [PhaseC4D.lean](sources/closeout-supplement/frozen-upper-code/Continuum/PhaseC4D.lean) 是原声明汇集接口。
- [DominanceC4DLiteralPlusRun08Cell60.lean](sources/closeout-supplement/frozen-upper-code/Continuum/Generated/DominanceC4DLiteralPlusRun08Cell60.lean) 中，命名空间为 `StarKakeya.CurrentRational.Continuum.Generated.DominanceC4DLiteralPlusRun08Chunk10.Cell60`。
- `main_critical_parameter_mem`（109–132行）和 `side_critical_parameter_mem`（134–157行）保留实际正分母、驻点等式及 y 所在闭区间；`main_critical_le_endpoint`（231–244行）、`side_critical_le_endpoint`（246–259行）、`continuumEnvelope_plus_le_endpoint_of_mem`（261–268行）只覆盖其各自声明的固定区间。
- Cell60 是尾部界所用的具体源包围接口，不以单个 Cell60 的存在替代整个 run00/run09 覆盖证明。原全生成面积/支配图本次没有重放。

## U-E6：端点门与移动尾部的隐藏

- [TAIL_HIDDEN_HEIGHT_VARIATION_ATTEMPT.md](sources/later/TAIL_HIDDEN_HEIGHT_VARIATION_ATTEMPT.md) §§2–6；[最终裁决](sources/later/TAIL_HIDDEN_HEIGHT_VARIATION_ADJUDICATION.md) 的已接受部分覆盖旧条件性页脚。
- [HEIGHT_ENDPOINT_EXACT_RESULT.json](sources/later/HEIGHT_ENDPOINT_EXACT_RESULT.json) 是历史精确端点回执；固定 d、T(1) 和 P 的比较以该回执和实际包围接口为输入。此次保存并读取，不重新运行旧标量程序。
- [POST_HEIGHT_LONGITUDINAL_TRANSFER_AUDIT.md](sources/later/POST_HEIGHT_LONGITUDINAL_TRANSFER_AUDIT.md) 和 [MICROSCALE_STABLE_CHORD_LENGTHENING_AUDIT.md](sources/later/MICROSCALE_STABLE_CHORD_LENGTHENING_AUDIT.md) 给出随后两个窗口与折叠屏蔽的解析证明。完整条带定位、每点单个非退化三角形内部见证及归一化法向误差均在正文保留。

## U-E7：历史面积基准与后续严格链

- [JOINT_SHARPNESS_SEQUENCE_ATTEMPT.md](sources/later/JOINT_SHARPNESS_SEQUENCE_ATTEMPT.md) §§2–5 和 [裁决](sources/later/JOINT_SHARPNESS_SEQUENCE_ADJUDICATION.md)：c_fr 的实际完整源面积极限及固定 n 后的有限常记录恢复。
- [BASELINE.md](sources/later/BASELINE.md) 的“Main sharp-value status”与“Accepted strict comparison”保存 c_fr<U 的历史接受状态，其中 U=0.284167531115949。该基准的完整历史生成面积证书在本次收尾中未重新构建；本次不把另一项目标面积或下界构建日志当成它的证明。
- 后续 c_new、c_r、c_height、c_hl、Γ_ms 与 Δ_coh 的原证明和允许的量词，由 [RESULTS_LEDGER.md](RESULTS_LEDGER.md) 的 R06–R14 以及 [SOURCE_MAP_SUPPLEMENT.json](SOURCE_MAP_SUPPLEMENT.json) 的相干补充逐项定位。
- Γ_ms、Δ_coh 均保留为已证明存在的固定正量；不求新小数、不比较二者、不相加，也不把这两个固定构造的改进量解释成任意近极小输入上的统一间隙。

## 读取与身份边界

原始 81 份来源见 [SOURCE_MAP.json](SOURCE_MAP.json)，相干与冻结输入补充见 [SOURCE_MAP_SUPPLEMENT.json](SOURCE_MAP_SUPPLEMENT.json)，补齐的单调性闭包单列。正文所在源快照可逐项核对；旧文件的“Lean 未闭合”描述是其当时的状态，现有下界定理由 `LEAN_PARENT_ACCEPTANCE.json` 和交付包的新构建回执单独证明。本映射不覆盖全稿形式化、不证明锐值，也不把来源保存等同于独立数学审查。
