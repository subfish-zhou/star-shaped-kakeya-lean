# Kakeya 收束论文：结论、依赖与原文证据账本

## 使用范围与当前可写结论

这是论文备料层的证据账本，不是论文正文，也不是新的数学审定。主证据为逐篇读取的完整证明与最终裁决；`SOURCE_MAP.json` 为每份原文记录原路径、完整副本路径、SHA-256、字节数、行数、读取范围和对应结论。`sources/` 中的副本逐字节保存，不修订旧状态、不截去失败过程。`CURRENT.md` 只读了前段当前状态／近期裁决索引，整份保存供定位；不能把其中历史的 running、PENDING 或旧数值口径当现状。

论文可以陈述的主下界是：任意关于共同一点星形、每个无向方向含完整闭单位线段的平面集合，其 Lebesgue 外面积至少为 `1/10`。这个结论不要求集合可测、有界、闭，也不要求原始选针规则连续或可测。现有普通数学证明已接受；其形式化工作属于另一交付线，本账本没有进行 Lean 构建，不能据此称为已闭合的 Lean 定理。

构造侧最强的已接受比较是

\[
 \frac1{10}\le A_*\le c_{\rm hl}-\Gamma_{\rm ms}
 <c_{\rm hl}<c_{\rm height}<c_r<c_{\rm fr}<U,
 \qquad U=0.284167531115949,\quad\Gamma_{\rm ms}>0.
\]

这里 `c_fr` 是指定冻结完整源的实际极限成本；`c_r`、`c_height`、`c_hl` 是后续固定构造成本；`Gamma_ms` 是未求值的正物理删除预算。独立分支 `A_*≤c_new<c_fr` 也成立，但没有与 `c_r`、`c_height`、`c_hl` 或 `c_hl−Gamma_ms` 排序。原数值上界 `U` 不因存在性下降而自动变成一个更小、已求值的小数；更不能把其中任一值指定为锐值。

**最重要的反向核验：有限扫掠普遍不达到性没有证明。** 已读原达到性证明、混合核心恢复及最终裁决，均保留混合紧扇区／有限异常三角形的缺口。后文 R21 只登记已经证明的分类和条件下降。

“独立审查”在本账本指项目中另一模型的普通解析审查，加父级解析核验；不能写作“人类同行评审”。旧文中的 human mathematical proof 是与程序／内核证据的区分，不构成人类作者或人类审稿身份的证据。历史算术日志只作历史证据；本次未重跑数学、数值、符号、系数或 Lean 程序。

## 对象、记号与依赖总图

- 原有限类：有限个闭方向区间 `I_i` 覆盖 `RP¹`，每条记录在其区间供应 `(b_i+[-1/2,1/2])u_q+h_i n_q`，并取所有完整原点三角形的真实无符号并。允许任意有限复杂度、任意纵向位置和有符号高度，允许跨记录完整弦。相邻闭缝的全部记录保留。
- `A_*`：该类的面积下确界；R02 证明它与任意有限外面积星形 Kakeya 集的外面积下确界相同。固定复杂度最优值是上逼近，不能用作全类下界。
- 物理角在长度 `2π` 的圆上，方向角在长度 `π` 的 `RP¹` 上；反向提升不是额外添加一份反足体。
- 原 1/10 的 `M,N` 是远／近**端点**半径；`N` 不是线段到原点的最小距离。
- 后来源类的 `s` 是高度轮廓，`p` 是一侧纵向臂长，另一侧为 `1−p`；`g=t−s/p`。这套反射、凹性、birth 假设只用于相应受限源类，不能赋给任意原有限输入。
- `B_s(t)=max_u (s(t)+s(u))/(t+u)`，端点连续延拓；`T_s(z)=max_u s(u)/(u+z)`，`z>0`。`L(s)` 是反射配对铰链的松弛下界，不是已知全局最优值。
- R14 的 `Q` 是依赖原记录和原尺度 `δ=π/n` 的规则，不能简写成“仅由身体 K 决定”的无来源算子。R18 中的 `Q` 则是任意连贯输出体，二者应在正文换符号以免冲突。

主要逻辑顺序：

```text
开包络 Borel 恢复 + 圆区间真实并引理
          ├─ R04 端点全圆锥核 ─ R05 eligible-anchor IL ─ R01 完整1/10
          └─ R02 原有限类同inf ─ R03 有理多边形全量词接口

R06 冻结全源实际成本/双级恢复 ─ R07 铰链 ─ R08 折返正余项 ─ R09 分片/补全
        ├─ R10 多项式接触非驻定 ─ c_new<c_fr （独立分支）
        └─ R11 严格band投影 ─ R12 固定height下降 ─ R13 固定纵向下降
                                                       └─ R14 Q整弦删除

R12 ─ R16 dense-short-axis手术 ─ R17 全位置空间运动障碍
R01 + R17 ─ R18 所有半径的强密度D反例
R02 + 竞争种子存在 ─ R19 固定FSC规则的原有限近inf失败序列
R20 JS：全弦/全尺度账有效；定性强型由旧halo已有

R02 ─ R26 半径截断 ─ R27 强面积完备性/Ekeland全Q交换
Körner模板 + 固定输入外邻域 ─ R22 稀疏整针生成 ─ R23 管增量支付
```

以下 R 编号也是 JSON 中的 claim ID。各条“来源”给出完整原文及精准章节，相关最终裁决均已在同一编号的 `claim_sources` 中列出。

## 主定理与全类接口

### R01　任意星形 Kakeya 集的完整 1/10 外面积下界

**状态：已接受普通数学证明；形式化不由本账本认证。**

精确命题：对任意 `E⊆R²`，存在 `o` 使每个 `x∈E` 都有 `[o,x]⊆E`，且每个无向方向有一条完整闭单位段包含于 `E`，则 `m₂*(E)≥1/10`。

证明承重链见 [THEOREM_01.md §§1–6](sources/one/THEOREM_01.md) 和 [完整端到端审查 §§2–6](sources/one/tenth-reviews/b2_universal_tenth_end_to_end_review.md)。在任意开包络中重新选 Borel 针族后，必须**重新**执行高度二分：存在 `|h|≥1/5` 时一条三角形已足够；否则全族进入低高度条件。方向按 `M<99/100`、`99/100≤M<8/5`、`m_n≤M<2m_n` 分区，`m_n=(8/5)2^n`。R05 负责低盘；R04 负责有限高层和首尾层；[baseline §§3,6](sources/one/baseline/PROOF.md) 负责所有后续尺度。测度 `dν=min(r,1)dr dθ≤dm₂`，径向银行彼此不交，低银行内部用互补价格，总物理密度至多一。对所有方向求和，再对开包络取下确界。

可写：“我们证明了无正则性附加条件的外面积下界 1/10。”不可写：“所有 source-once 方法失败”“只有 π/64 下界”“1/10 已经 sharp”“几何证明由算术程序完成”。审查记录的旧 commit/blob/SHA 是历史定位；当前副本身份以 JSON 的实测 SHA 为准。

### R02　精确单位的开包络有限扫掠恢复、下确界相等

**状态：已接受完整解析引理。** 对任意有限外面积原点星形完整单位体 `K` 和任意 `ε>0`，存在原有限闭角扫掠 `F`，满足 `|F|<m₂*(K)+ε`；更强地，可置于指定开包络 `O⊃K` 内。

[完整原文：精确引理、完整证明及下确界结论](sources/external/compact_approximation_review.md)。逐方向选原完整针，其整个原点三角形紧含于 `O`；先取安全闭旋转弧，再以较小开弧覆盖 `RP¹`，有限子覆盖给合法有限输出。此处无需原 selector 可测、无需对 `K` 取闭包。

这是 R14 输出恢复、R21 条件下降、R27 同 inf 的共同依赖。只给**面积上恢复**，不给 `F⊂K`、`K⊂F`、对称差近似、连续针运动、固定包数或无权极小者。原集合即便无界也可用；仅有长度 supremum≥1 而未取到单位时应另保留近单位缩放论证，不能偷选精确单位。

### R03　有理三角形并的无损 primal 与单侧可枚举性

**状态：已接受。** [rational_polygon_primal §§2–8](sources/later/rational_polygon_primal.md)，[独立复核 1–4](sources/later/review.md)。紧星形 `S⊂O` 可由有理网格径向化得 `S⊂P⊂O`，因此任意有限复杂度有理原点三角形并与原问题同下确界。

完整可行性是 `∀u∈S¹ ∃p ∀t∈[0,1] ∨_i M_i(p+tu)`。三角形所有者可随 `t` 改变；不能改成 `∃i∀t` 或端点可见。固定有理表的成员关系可由实闭域判定、真实并面积可由有理 arrangement 求得；穷举给递减有理上逼近，不给停止误差率、下逼近或固定 N 最优性。

依赖 R02 和同开包络网格包含。可放附录作“原有限对象没有表达能力缺口”，不能把理论可判定性说成执行过的算法或已完成优化。

### R04　全圆锥端点核，以及共同单远端方法的精确天花板

**状态：B1 Theorems 1–3 与受限方法天花板已接受。** [证明 §§1–8](sources/one/endpoint-geometry-b1/endpoint-domain/PROOF.md)，[独审](sources/one/tenth-reviews/b1_endpoint_independent_review.md)。

对 Borel 单位针族，`m≤M≤R`、`|h|≤H`、`0<H≤1/2`、`m≥1/2`、`R≥max(m,sqrt(1/4+H²))` 时，每个 Borel cut `V` 和 `0<r<m` 有
`|S_r(V)|≥min(K_(R,H),(m−r)/(m+r))|V|`，其中
`K_(R,H)=sqrt(R²−H²)/(sqrt(R²−H²)+2R²)`。

真正的圆截面包含基段之下的径向填充、外垂足的全锥截断、零高度 singleton；不能用线段与圆的交点代替三角形截面。低跨足源另有 Theorem 3 的更强锥 cap，是 R05 的依赖。

在“同一远端 base/anchor 的共同 extension ratio，再用一般混合符号因子 `1+2ρ`”的方法中，无论改锥 cap 或径向价格，低方向全圈系数至多 `π(3/8−(1/2)log2)<209/2268<1/10`。这是方法上限，不是实际星体面积上界，也不排除所有 far-only、符号细化或两端联合方法。旧正文的“1/10 OPEN”已由 R01 后续组合取代。

### R05　eligible-anchor 的 hereditary IL：1/10 的新增承重引理

**状态：几何、算术与全局组合分开接受。** [完整证明 §§1–4](sources/one/low-source-b2/integrated-low/PROOF.md)，[几何独审](sources/one/tenth-reviews/b2_IL_geometry_review.md)，[算术独审](sources/one/tenth-reviews/b2_IL_arithmetic_review.md)。

对 `|h|≤1/5,M<99/100` 的 Borel 族和每个 Borel `V`，令 `B={N≥2/5}`、`U=V\B`。选所有远理想锚，并只给 `B` 加近理想锚；理想 lifts 真正不交，实际 lobes／重复 cones 则**先合并**。一遍区间引理给
`|S_r(V)|≥min(2/3,(2/5−r)/(2/5+r))(|V|+|B|)`。

令
`C4=61/750−(8/25)log(5/4)`，`C5=87/800−(1/2)log(17/14)`，
`C6=93/800−(18/25)log(22/19)`，`D5=69/800−(1/2)log(20/17)`。
固定 `λ=C4/C6∈(0,1)`，有
`C*=2C4+C5+(1−λ)D5>637/20000>1/(10π)`，以及
`|W(V)∩B_(1/2)|≥C*|V|`。乘方向长度后的严格号只用于 `|V|>0`。

最后外银行的真实容量是 `λ1_W(U)+(1−λ)1_W(V)≤1_W(V)`，不是两个 full-price 相加。`λ=1` 的先驱证书失败只说明其系数不能支付平衡类；互补 `D5` 修复没有改变阈值。历史精确日志证明标量门，几何来自正文，不来自日志。依赖 R04、baseline 圆区间并引理。

## 完整源成本、受限比较与严格上构造

### R06　冻结奇数胞族的实际成本与两级有限恢复

**状态：构造成本／恢复接受；所谓 sharp pair 未形成，逐层下障碍 P 已反驳。** [证明 §§2–5](sources/later/JOINT_SHARPNESS_SEQUENCE_ATTEMPT.md)，[裁决的 ACCEPT 与 P 反例](sources/later/JOINT_SHARPNESS_SEQUENCE_ADJUDICATION.md)。

按原 `Data` 固定多项式，取 `p(y)=1/2+(−1)^j a(t)`、`m=1−p`、`A(y)=(−1)^(j+1)s(t)`，`y=j+t`。原完整段为 `x u_(δy)+δA(y)n_(δy)`，`−m≤x≤p`，`δ=π/n`，奇 `n`。正、负相位集合保留所有 `r≤x≤p/m` 的 `y±A(y)/x`，不是端点集合。实际角相位使用 `atan(δA/x)/δ`，半径使用平方根。

有限临界半径之外，激活域的连通分支及其完整相位区间双侧收敛；两物理片和端部 aliases 分开计数，径向支配收敛得
`c_fr=(π/2)∫r(|S_+(r)|+|S_−(r)|)dr=lim_(n odd)|E_n|`。
固定 n 同时冻结 `(b,h)`，三角形内点持续性给下极限，外邻域给上极限，故 `|K_(n,k)|→|E_n|`。不能由一般 Hausdorff 收敛直接得面积收敛。

`c_fr<U` 及原 source 符号证书是历史冻结上界审定的输入；本账本未重建全部 `CurrentRational` 内核依赖。不可把 `Data.targetAbsoluteArea`、U、c_fr、某个有限 n 面积混写。

父裁决以合法 `B_(1/2)` 反驳“任意 K 每个半径占用均不小于冻结图”：r>1/2 时圆盘截面空，而冻结图在一段这样的 r 上有正占用。它只否定逐层比较，保留积分型比较的可能性。

### R07　完整物理铰链恒等式、反射耦合下界及不可达例

**状态：受限类全 p 比较与反例接受。** [证明 §§1–6](sources/later/LONGITUDINAL_HINGE_COMPARISON_ATTEMPT.md)，[裁决](sources/later/LONGITUDINAL_HINGE_COMPARISON_ADJUDICATION.md)。

固定对称、零端值、严格凹 s；反射 C¹ 的 p 满足开盒、双 birth，且 `g=t−s/p` 有正导数下界。完整成本为
`C/π=∫T²+∫Φ_s(t,p(t))dt`，
`Φ_s(t,x)=(x−B)_+²+2(B−s′)(x−B)_+`。
反射配对 `Ψ_t(x)=Φ(t,x)+Φ(1−t,1−x)`。若 `B(t)+B(1−t)≥1`，极小集 `[1−B(1−t),B(t)]`、极小值零；否则唯一极小元为 `clamp(1/2+s′,[B,1−B_ref])`。因此每个合法 p 满足 `C≥L(s)`，没有交换 inf 与积分。

反例固定 `0<c<1/4` 和充分小 ε，取
`s(t)=c(sqrt(ε²+1/4)−sqrt(ε²+(t−1/2)²))`。
合法类含 `p=1/2`，但唯一点态极小元 `p*=1/2+s′` 在中点的 `J=p²−ps′+sp′` 为负。强凸性使逼近 L(s) 迫使 p 的 L² 收敛，从而 g 的 a.e. 极限与非减性冲突。故这个**固定 s、g 递增类**的 inf 严格大于 L(s)，未给差額。它不是任意原有限类反例，也不自动否定折返类匹配。

### R08　折返完整源：有序交叉对的非负余项

**状态：接受，保留 s''<0、birth、反射源类。** [完整证明 §§1–6](sources/later/FOLDED_COMPLETE_SOURCE_COMPARISON_ATTEMPT.md)，[最终裁决](sources/later/FOLDED_COMPLETE_SOURCE_COMPARISON_ADJUDICATION.md)。取消 g 单调条件，但不取消其余门。

`τ(z)=min{t:g(t)≥z}` 是真正完整源首次到达；凹性使后续合法半径严格递减。正则输出的根依次上穿、下穿、上穿，记 `w_i=max(p(t_i)²,T(z)²)`，则
`D_fold=π∫Σ_j(w_(2j)−w_(2j+1))dz≥0`，
`C_full−L(s)=π∫_(0,1/2)(Ψ_t(p)−min Ψ_t)dt+D_fold`。

精确零门：`D_fold=0` 当且仅当在活动开集 `{p>B_s}` 上 `g′≥0`。隐藏在 T 以下的折返可无代价。R07 的尖峰 p* 在扩大类里仍是合法整针源，但其活动下穿给 `D_fold>0`、实际 `C_full(p*,s)>L(s)`。不能把单个 p* 的正差额升级为扩大类 inf 的正差额；也没有无条件有限恢复任意 C¹ 源的统一结论。

### R09　有限分片恢复与参考补全，保留实际等号缺口

**状态：分片公式／真实恢复／补全 birth 已接受；指定选择的零 fold cost 未闭。** [分片证明 §§2,5–7](sources/later/MEDIAN_ACTIVE_FOLD_RECOVERY_ATTEMPT.md)，[相应裁决](sources/later/MEDIAN_ACTIVE_FOLD_RECOVERY_ADJUDICATION.md)，[补全证明 §§2–7](sources/later/REFERENCE_COMPLETED_HINGE_SELECTOR_ATTEMPT.md)，[补全裁决](sources/later/REFERENCE_COMPLETED_HINGE_SELECTOR_ADJUDICATION.md)。

原 median `p◇=median(B,1/2+s′,1−B_ref)` 的有限闭 C¹／Puiseux 分片及实际薄角、固定 n 常记录双侧恢复成立。fold 公式的该对象应用仍需其全内部 birth；其紧内部 birth 失败集没有判空。

新参考补全 q 在 `B+B_ref<1` 取点态极小元，在 `B+B_ref≥1` 取 `median(B,p0,1−B_ref)`。q 与全域 band 投影 r 均具有全内部严格 birth、反射、开盒、Lipschitz 有限分片及实际有限恢复。故对 q 可写 `C_phys(q,s)=L(s)+D_fold(q,s)`，其中 D 非负而尚未判零。不可把 q 的已证 birth 回写给旧 p◇，不可把 r 的 no-loss 或后续 strict gain 搬给 q。

旧 exact-median 裁决的端点 `d+B(1)<1` 未决状态后来已由 R12 的实际标量门支付；它不再是当前未知项。但这不关闭旧 median 全内部 birth 或 q 的活动折返门。

### R10　高次多项式接触刚性与真实非驻定下降

**状态：一般定理及实际冻结应用均接受。** [完整独审 §§1–7](sources/later/POLYNOMIAL_CONTACT_NONSTATIONARITY_AUDIT.md)，[最终裁决](sources/later/POLYNOMIAL_CONTACT_NONSTATIONARITY_ADJUDICATION.md)。

在 R07 的严格可行反射 C¹ 类中，若 p,s 为规定多项式且 `deg p>deg s′≥1`，p 不是实际完整成本的局部极小元。接触 `Q=B_s` 导出 `R=(s′−Q)/Q′−t`、`s′∘R=Q`；复有理极点排除与无穷远次数冲突禁止开区间接触。固定实际源为次数 19 对 15。

取真实配对导数 D 的反号作双零端值反射 bump；只在双活动 chamber 才可用 `4p−2−4s′`，单活动时是 `2(p−s′)>0`。固定幅度的完整差为 `π(εL+ε²Q0)<0`，而非仅形式负一阶导数。严格门保持和 R06 类双级恢复给 `A_*≤c_new<c_fr`，差额先于复杂度固定。可在论文保留一般接触定理，不应只报告一次很小的上界修补。

### R11　指定全域 band 投影的严格完整并比较

**状态：接受 `A_*≤c_r<c_fr`。** [证明 §§2–7](sources/later/BAND_PROJECTION_STRICT_COMPARISON_ATTEMPT.md)，[裁决](sources/later/BAND_PROJECTION_STRICT_COMPARISON_ADJUDICATION.md)。固定 `r=median(B_s,p0,1−B_s(1−t))` 与原 s。

依赖 R09 的四排序完整尾核 no-loss、R10 的接触刚性、原 run00/run09 的真实语义优势与整个指定源区间归属。first-hit 唯一性证明暴露端点仅有一个真正源；新扩张完整臂全藏共同尾核。截断于正半径的新并是紧像，故被删点有排除邻域，旧连续屋顶给**正面积**缺片。恢复保持固定差额。

证据不是 winner 标签或端点删失；原 Lean API 在证明中被解析应用，本次未重跑内核。c_r 与 c_new 未排序。

### R12　固定实际 r 的尾部隐藏高度下降

**状态：已实际接受，旧 CONDITIONAL 页脚被顶部后续验收覆盖。** [完整机制 §§2–6](sources/later/TAIL_HIDDEN_HEIGHT_VARIATION_ATTEMPT.md)，[最终验收顶部及条件机制核验](sources/later/TAIL_HIDDEN_HEIGHT_VARIATION_ADJUDICATION.md)，[历史端点精确回执](sources/later/HEIGHT_ENDPOINT_EXACT_RESULT.json)。

实际门为 `P=r(0)>d=s′(0)`。旧真实 main 源 enclosure 与 H 身份支付 `T(1)<4/25`；后来一次获准的精确零点核对支付 `d=107161751/128520000<21/25`，从而门闭。本账本只读回执，没有再次执行。

固定非负对称 C² 内部 bump `a=s+εh`，r 不动；全径向端点占用 G 下降。新增尾极大源只可能落在 bump 支撑，其半径进入预先受 G 严格遮蔽的窗口，因此有限 ε 的 moving-tail 增加全部隐藏；一个固定正宽未饱和径向带严格损失。保 birth／严格凹性及两级恢复得 `A_*≤c_height<c_r`。源片正高度端三角形保留；旧正文“端源只给射线”的简写须按最终裁决与 R13 恢复纠正解释，不能删正面积端源。

### R13　高度固定后的纵向严格下降

**状态：最终接受 `A_*≤c_hl<c_height`。** [首测 §§2–5](sources/later/POST_HEIGHT_LONGITUDINAL_TRANSFER_FIRST_TEST.md)，[完整对抗审查 §§2–7](sources/later/POST_HEIGHT_LONGITUDINAL_TRANSFER_AUDIT.md)，[最终验收](sources/later/POST_HEIGHT_LONGITUDINAL_TRANSFER_ADJUDICATION.md)。

固定 R12 的 a、支撑及幅度，取一次反射反对称 C¹ 有限分片纵向 v 和固定 η。穷尽 r 在既有支撑边界旁为 U_s 或 p0 的分支；A 分支缩露出长臂，互补新增臂在真实尾核；B 分支必须同时支付两个窗口的 first-hit。辅助 `q_η=p0+ηv` 控制早先另一扰动窗口，不能搬旧全域 g′ 证书给新输入。

完整改变底边条带及其径向填充都局限于两个固定相位窗口；所有两片／aliases 合并后真实屋顶为 `max(R,T_a)`。精确有限差为 `π(ηL+η²Q)<0`。首测区间文字以最终更正为准：非退化闭 `J⊂int(I)`、`w|J>0`。幅度、差额在 n,k 之前固定。旧 PROVISIONAL 状态已经被最终验收取代。

### R14　微尺度稳定整弦单位化：当前最强构造比较

**状态：最终接受；核心正文／附录均应保留。** [完整父定义 §§1–5](sources/later/MICROSCALE_STABLE_CHORD_LENGTHENING_PARENT.md)，[完整独审 §§3–10](sources/later/MICROSCALE_STABLE_CHORD_LENGTHENING_AUDIT.md)，[FINAL](sources/later/MICROSCALE_STABLE_CHORD_LENGTHENING_FINAL.md)。

固定原 `p_*,a,K_(n,k),δ=π/n`。对每条原闭记录 `N=[l,r]u_q+h n_q`，在 K 内的**完整**平行区间 `C=[L,U]u_q+Hn_q` 中最大化 `ℓ=U−L≥1`，条件为
`(L−l)²≤ℓ−1`、`(U−r)²≤ℓ−1`、`((H−h)/δ)²≤ℓ−1`。
保留全部最大化者，把整区间绕原点缩为 `C/ℓ`，取所有原点三角形和闭包，得到 S^Q。一次作用，无掩码、无迭代，不能连跨线截面孔洞。

存在固定 `Gamma_ms>0` 和奇数阈值 N，使每个充分大奇 n、随后每个充分细的**原** k 都有
`S^Q_(n,k)⊆K_(n,k)`、`|K_(n,k)\S^Q_(n,k)|≥Gamma_ms`，因此
`limsup_(n odd) limsup_k |S^Q_(n,k)|≤c_hl−Gamma_ms`。

主要付款：双活动 B 的两端延长不够，必须另证明唯一 fold `x=a′(t)` 在纵向改动后的实际身体中仍有严格三角形见证；非 fold、fold、端部共同覆盖整条位移弦。A／单活动 B 使用真实相接尾段。线性增益压过平方误差，得到各承载邻域的统一长度 floor。若任一新三角形或闭包补回旧暴露屋顶，则 `ℓ→1`，Q 强迫**除以原 δ 后**的法向误差也消失，于是原 carrier 落入已付长度邻域，矛盾。固定内条带计一次物理面积，正删除不随胞数消失。R02 最后给原有限输出。

可写“未求值的非消失严格构造改进”。不可写新小数、任意 diagonal、输出面积 limit 存在、全局最优或 repeated Q。旧同线 component 规则的 `ACTUAL_GAIN_OPEN` 没有被此不同规则追溯解决。

## 有用的失败路线与结构定理

### R15　每个方向的任意固定有限内点采样都不给正面积下界

**状态：父证明及独审加强均接受。** [FINITE_SAMPLE_CEILING 全文](sources/later/near_extremal_angular_organization/FINITE_SAMPLE_CEILING.md)，[独审 §§1–5](sources/later/near_extremal_angular_organization/FINITE_SAMPLE_REVIEW.md)。

对每个有限 `T⊂[0,1]`（可含 0,1）、H>0、ε>0，存在 `K⊂B_1` 为紧原点星形有限闭扇区并、`|K|<ε`，使**每个定向 q** 都有同一条该方向单位记录，其 T 中所有点属于 K；记录参数可在有限闭方向区间分片常值、`s∈(−1/4,1/4)`，高度可预先统一固定为任意 `h0∈(0,min(H,1/4))`。

小测度开稠密角集 A 配合样本角对 s 的非零导数，给有限个开稠密逆像的共同交；随后取从属的有限闭方向细分，而非取 closure(A)。所有样本 sectors 的真实并仍在 A 下。

取 ε<h0/2 时，没有一条所供整记录能完整包含在 K，因为其原点三角形面积为 h0/2。这里连续的方向量词已全部满足，缺的恰是**整段内部**。只否定固定有限成员测试的替代模型；不否定有统一误差的连续化、保整区间的自适应方法或所有涉及采样的证明。T 增大时 K 可以变化，不能宣称一个紧零面积 K 通过无限稠密共同记录测试。

### R16　稠密短轴手术、消失凸子集与 Beer 质量

**状态：D1–D4 已接受；竞争应用仅为已付 c_height 序列。** [完整父证明 §§1–6](sources/later/DENSE_RAY_CONVEXITY_DEGENERATION_PARENT.md)，[最终裁决](sources/later/DENSE_RAY_CONVEXITY_DEGENERATION_ADJUDICATION.md)。

输入为统一有界原有限全方向单位族，所有注册高度 `|h|≤Mδ_j`、δ_j→0、面积→c>0。固定 `γ_j=sqrt(δ_j)`、`m_j=floor(δ_j^(−1/4))`；删网格轴附近旧开方向窗，补每个闭窗的居中单位记录、高度 `tanγ_j`。保全部闭缝及其它补片回填。真实双侧矩形估计给 `|F_j△K_j|→0`，每条网格轴仅在 `B_(a_j)` 内被占据，a_j→0。

任何面积不消失的凸子集都有正面积凸 Hausdorff 极限及持续内盘，会被稠密短轴刺中而矛盾；故 `sup{|C|:C⊂F_j convex}→0`。D4 再使用 Balko–Jelínek–Valtr–Walczak, arXiv:1412.1769v2, Theorem 1.3 的 `b(S)≤180 smc(S)/|S|` 得 Beer index 和四维整段 incidence 质量均趋零。

D1–D3 为内部完整解析证明；D4 的原论文由历史审查取得，本次未重读其 PDF，不能新增文献首创性声明。不能推出平面 unit-cover 面积小，不能推 near-A* 的同样结论，不能用此序列把 c_hl/Gamma 输出的性质补齐。

### R17　实际完整单位位置空间的每个连通分量都缺方向

**状态：MB1–MB3 接受；反驳 same-body 自动连贯性。** [PARENT MB1–MB3](sources/later/unit-motion-barrier/PARENT.txt)，[完整独审](sources/later/unit-motion-barrier/REVIEW.md)，[裁决](sources/later/unit-motion-barrier/ADJUDICATION.md)。

若紧 `K⊂B_R`、R<1，m≥3 网格线只在 B_a 内遇 K，a<1−R，则实际整单位位置空间 `P(K)` 的每个连通分量都漏掉至少一个 RP¹ 方向。单位端点半径≥1−R，故端点不触网格；同扇区直径<1，端点必须有不同扇区标签。无序端点扇区对在整个 P(K) 上局部常值；一条网格线分开这对扇区，使此分量不能带平行于该线的单位。

R16 的**同一** c_height 有限序列，从闭区间臂长余量推出 R_*<1，晚项真正满足条件并面积<U。因此静态全方向覆盖不意味着在该身体内能连续半转整针。这里排除所有跨记录实际单位运动，不只是登记 selector。它不排除换成另一个不增面积身体的 FREE 归约。

### R18　所有半径、所有新针位置的强密度 D 被反驳

**状态：CSDA 六步完整证明接受，D=REFUTED。** [PARENT §§1–6](sources/later/coherent-strong-density-obstruction/PARENT.txt)，[完整独审](sources/later/coherent-strong-density-obstruction/REVIEW.md)，[最终裁决](sources/later/coherent-strong-density-obstruction/ADJUDICATION.md)。

固定一个 R17 供应的原有限竞争短轴 K，满足 `R0<1`、m≥3、`a<min(1−R0,1/2)`。存在 ε_K>0，使**每个**紧、共同原点星形、具有闭合连续完整单位中点截面的 Q 都有 `|Q\K|≥ε_K`，因此 `|Q△K|≥ε_K`。Q 没有共同外半径帽，针位置可以全部重选。

关键依赖不是机械合并逐帽障碍：低高度整方向窗的实际完整远尾形成同角孔内物理并；有限旋转后 R01 支付其固定正总面积，径向比例把一部分收进 K 外。单针成本 `|conv(0,N)\K|` 紧化两个纵向无穷端，保留所有伪径向零态；全纵向高度屏障与集体窗面积排除径向循环，再以真实／伪径向标签粘合和有限鲁棒邻域分离阻止连续截面。

可写“一个固定原有限竞争体的所有半径强面积密度失败”。**不可写 `A_coh>A_*`**：Q 可以删旧料抵消新增料；此定理不下界净面积。也没有随 K 变化或 near-A* 的统一 ε。原 CSD 的 DENSITY_OPEN 是历史状态，不是当前 D 状态。

### R19　固定 Farey 双剪切／最近垂足截单位规则，在原有限 near-inf 序列仍失败

**状态：REFUTED_C_FSC、ORIGINAL_FINITE_DELIVERY、NEAR_INFIMUM_FAILURE 均接受。** [完整算子及 §8A–8F](sources/later/farey-shear-clipping/PARENT.txt)，[独审 §§2–7](sources/later/farey-shear-clipping/RESULT.md)，[裁决](sources/later/farey-shear-clipping/ADJUDICATION.md)。

算子原样保留象限符号下两个 det=1 的 Aσ/Bσ 剪切、变长像段内距垂足最近的完整单位子段；坐标轴**两个 σ 都保留**。它保持完整单位与方向覆盖，几乎处处传播高度随欧几里得减法变薄，但这不给并面积符号。

非零高水平记录在轴上产生中心 `b+(2j−k)h`、j=0,…,k；真实同高单位区间并长为 `1+k min(2|h|,1)`，其星化面积为 `|h|/2` 乘该长度，随有限迭代无界增长。首次越过竞争种子面积的那一步给仍竞争的反例输入。

固定深度的有限半代数连续源分为恒零高／统一非零高片；同规则冻结保所有 singleton、轴缝及零高度，外邻域加非退化三角形内点持续性、半代数零测边界和零高径向到达量连续性，证明**输入和输出各自双向面积收敛**。故反例进入原有限输入类，输出不必仍为常记录语法。

从任意原有限近极小种子逐例旋转非零高源、取首次越界与充分细冻结，可得输入面积→A_*而每例同规则严格增面积的序列。各例差额可趋零；没有“全部近极小输入都失败”、统一正 gap、第一次就在 MB 种子上失败、或所有 FREE 替换都有内禀税。闭零测方向记录能携带正面积，是该固定规则的具体失败原因。

### R20　联合弦长／远端半径壳层 JS；定性强型去重

**状态：JS 及已付全尺度求和接受；定性强型不记新贡献。** [完整父证明 §§2–5](sources/later/intrinsic-chord-joint-shell/PARENT.txt)，[独审 §§2–8](sources/later/intrinsic-chord-joint-shell/RESULT.md)，[裁决](sources/later/intrinsic-chord-joint-shell/ADJUDICATION.md)。

原有限 K 中选真正最长**完整连通**弦，长度 L(q)，远端欧氏半径 R(q)，按 `t≤L<2t,M≤R<2M` 分箱 E_jm。半代数选择不用连续 winner。截取实际远端长度 t/32 子段只作收费见证，其完整原点三角形在 `M/4≤r≤M/2` 给真实角弧。普通区间平均极大函数弱型，加零高直接成员分支，得
`Mt|E_jm|≤C_JS |K∩{M/4≤|x|≤M/2}|`。

平方弦长账带 `t/M` 权重；先固定 M 对所有 t 求和，再对不交物理环带求和，得统一有限 `∫L_K²≤C_strong|K|`。旧 [全 Borel 加权逆平方 halo 参考](sources/external/direct-all-borel-weighted-interval-far-field.md) 已能推出定性强型；新直接线性壳层推导可保留，不能写“首次得到强型常数”。

外垂足校准的正确尺度为 `sqrt(R²+h²)/ell`（R 此处是纵向坐标）；只有 h/R 有界才是 R/ell 阶。JS 使用欧氏 M，因此证明不受该旧措辞影响。实际 MB 星体只落 t=1,M=1/2 箱，该银行只用 `1/8≤r≤1/4` 内环；其余半径、裁尾、halo、双片投影和几何级数均有损失。未优化 C、未证明改进 1/10、更无 sharp/matching。

### R21　有限达到性：只接受核心准则、恒长分类与若干排除

**状态：VERIFIED_PARTIAL；全体有限不达到仍 OPEN。** [TIGHT_CORE](sources/later/theoretical_infimum_attainment/TIGHT_CORE.md)，[完整分类 §§1–4](sources/later/theoretical_infimum_attainment/ATTAINMENT_ATTEMPT.md)，[该轮裁决](sources/later/theoretical_infimum_attainment/ADJUDICATION.json)，[混合核心恢复](sources/later/theoretical_infimum_mixed_core/MIXED_CORE_RECOVERY.md)，[最终裁决](sources/later/theoretical_infimum_mixed_core/FINAL_ADJUDICATION.json)。

紧半代数 K 取最长完整弦 L 的**下半连续包络** L_*，Z={L_*=1}。若存在闭图 selector 的紧方向核心 H⊂K 且 |H|<|K|，则 `λK∪H_δ` 给真实正面积下降，R02 恢复原有限输出。有限 Z 且有真正暴露同心圆弧时可用；不能以隐藏 primitive 圆弧充当暴露边界。

对于真实边界为有限同心圆弧、直段、奇点的 K，若 L=1 在开方向区间恒成立，则每个该方向有过原点最大单位段；去有限异常后相反径向半径为常数 r,s≥0、r+s=1。证明穷尽自由平移与固定顶点锁定，涵盖圆／直各端点型以及内部顶点接触。Z=全圆时面积≥π/4，另有更小合法体，因此这**个子类**不达到全局 inf。

混合核心恢复仅付自由槽／正面积缺口与全方向端点链恒等式 `∮Γdet(z,dz)=π/2+2M`。跳点连接可在 K 外、绕数可重叠，不能当无符号面积；拟议残差界消元后等价于原目标，没有独立控制。不能从“这条研究线 CLOSED”写成“定理 proved”；也不能把未证 rigidity 的必要条件写成对所有有限 K 的排除。

### R22　任意原有限输入附近的稀疏完整单位生成族

**状态：完整适配接受，明确导入 Körner 零测矩形模板。** [完整证明 §§1–4](sources/later/literal_primal_reassessment/UNIT_SKELETON_ATTEMPT.md)，[最终裁决](sources/later/literal_primal_reassessment/UNIT_SKELETON_ADJUDICATION.md)，[固定输入恢复](sources/later/literal_primal_reassessment/FIXED_INPUT_FINITE_RECOVERY.md)。

对原有限 `K=S(P)⊂B_R` 和任意 ε,η,τ>0，存在同语法有限 F=S(P_F)，满足 `|F|≤|K|+ε`、`|P_F|≤η`、`F⊂B_(R+τ)`、`d_H(F,K)<τ`。P_F 是**完整生成单位段的真实并**，不是有限样本。

将 Körner 的紧零测矩形模板横向压窄，放到每条实际原针中点附近；像段长≥1，截实际居中单位子段，得到正宽全方向窗。有限窗覆盖和全记录有限网给紧零底边族 P0；再在 P0 的已固定小外邻域内作原点旋转有限常记录恢复。先 K 的容差、后 P0、最后 P0 的邻域尺度，不能交换量词。

每个固定 η>0 的这种生成限制不改变**无半径帽**的 A_*。半径 1/2 圆盘说明 τ 松弛不可删除：不增半径则所有单位都只能是直径，底边并不能稀疏。它不给高度变薄、统一 N、|S(P)| 由 |P| 控制。原文出处／前次 PDF 获取在 [来源裁决](sources/later/literal_primal_reassessment/RELAXATION_SOURCE_ADJUDICATION.md)；本次没有重新核读外文 PDF。

### R23　共享物理管的星包增量估计

**状态：几何与分析两路合并后无条件接受。** [最终定理及依赖核验](sources/later/literal_primal_reassessment/TUBE_PAYMENT_ADJUDICATION.md)，[几何完整替换证明](sources/later/literal_primal_reassessment/TUBE_PERIMETER_REVIEW.md)，[分析完整替换证明](sources/later/literal_primal_reassessment/TUBE_GROWTH_REVIEW.md)，另有 [Crofton 父证明](sources/later/literal_primal_reassessment/TUBE_PERIMETER_PARENT.md) 与 [增长父证明](sources/later/literal_primal_reassessment/TUBE_PAYMENT_GROWTH_PARENT.md)。

对非空紧 `P⊂B_R`，每个点都在 P 中某条完整单位段上，令 `P_δ=P+B_δ`，则
`|S(P_δ)\S(P)|≤(R+2)|P_δ\P|`，0<δ<1。不要求覆盖所有方向，因而可用于紧单位族的有限整段逼近。

证明必须用已修正链：正则管物理分支直径≥1／周长≥2；径向星包周长由循环次序不重用边界弧或 Crofton 分量注入支付；Voronoi 平行体及 dyadic-λ 球分解给真正局部 Lipschitz；正厚度 regular-closed 半代数边界给外 Minkowski 内容；实际距离 coarea 在两个正半径间积分，再降至零，紧完整单位族亦在正厚度层先取极限。原稿“口袋自动配弧”“有限分层自动 Lipschitz”的简写不作为依赖。

R+2 对固定半径统一，不代表 P0 的管面积模数统一。它控制增量而非总星包面积；不能由零底边推出零星包、从该式给统一包数或新的 A_* 界。两单路审查的 CONDITIONAL 是分工状态，最终合并裁决已支付双方条件。

### R24　PL 的字面两宿主、正方向测度反例

**状态：完整解析反例，R01 端到端审查明确确认非依赖。** [COUNTEREXAMPLE §§1–4](sources/one/low-source-b2/paired-pointwise/COUNTEREXAMPLE.md)。

Borel 低针族 `|h|≤1/5,M<99/100` 存在 cut V，使 `|V|=43/1000`，但 `|S_(1/4)(V)|=1/50<(1/2)|V|`。两物理宿主各长 1/100；外侧族只有真实活动远 lobe，中央族的两个活动 lobes 都落回这两个宿主，完整几何与共同单位记录用三角恒等式和全区间有理余量证明。反驳的是 PL 的点态变系数到并集推断，不是 IL 或 1/10。

适合放在 R05 前后的方法附录：它具体说明为什么“每个源两个好系数”不能直接加成一个真实并下界，以及 IL 为什么改数不交理想锚而对物理目标只收费一次。原反例稿的 IL OPEN 是独立支线当时状态，当前由 R05、R01 覆盖。

### R25　固定纵向分配的物理半圆盘障碍与端点集中对照

**状态：A–C 辅助结论接受，实际有限极限等式只按各自范围。** [MECHANISM A–C](sources/later/sharpness_mechanism_endpoint_phase/MECHANISM.md)，[裁决](sources/later/sharpness_mechanism_endpoint_phase/ADJUDICATION.json)。

固定 p,m≥0、p+m=1，连续 h:[0,π]→R、h(0)=h(π)=0 的完整针族，正负端点角连续提升分别覆盖两个半圆，给 `|K|≥π(p²+m²)/2≥π/4`。这说明仅在**此连续固定分配类**内调高频 h 不足，不涵盖跳跃 selector 或可变 p，也不是“所有节省必来自可变 p”的普遍必要性定理。

完整周期端点塌缩对照 `p=y,m=1−y,A=y(1−y)` 的理想 roof 积分与反足化积分不同，旧稿给解析公式但只立即有上恢复。不能将该对照的未证下包含等式从 R06 的**另一个固定多项式族**借来。论文可用完整内部区间的存在说明完美端点聚焦仍有成本，不必把对照数值变成新竞争记录。

### R26　显式半径截断误差，不等于复杂度控制

**状态：全族几何／测度审查接受。** [定理及 §§1–5](sources/later/radius_truncation_theorem.md)，[测度与传递复核](sources/later/radius_measure_review.md)。

紧原点星形全方向单位 K，`|K|=A≤U`、`R≥4U+2`，存在 Borel 全方向单位 `F⊂B_R`，`|F|≤A(1+340/R)`。截断盘内的 bad 方向可测，以该方向居中单位补齐，成本 `|Bad_R|/4`。整远针角区间与普通平均 halo 给 `|Bad_R|≤1344A/R+32A/R²`，不是逐针面积和。

因此 `A_*≤A_R≤(1+340/R)A_*`；若半径 R+1 内**任意复杂度完整方向**有理竞争体统一下界为 c，则 `A_*≥c/(1+340/R)`。R+1 是恢复余量，不可删；没有统一有限 N，也没有修复有限方向采样。R27 使用的是该证明的 Borel halo 适配，不是直接把紧输入定理套给无界体。

### R27　强面积商空间完备性与无半径帽相对交换

**状态：SMQ 有帽和 GSQ 无帽均接受；GSQ 是可单独保留的全类结构成果。** [GSQ 完整父证明 A–E](sources/later/global-strong-measure-quasiminimality/PARENT.txt)，[完整独审 §§2–8](sources/later/global-strong-measure-quasiminimality/REVIEW.md)，[最终裁决](sources/later/global-strong-measure-quasiminimality/ADJUDICATION.md)；有帽前身 [SMQ](sources/later/strong-measure-quasiminimality/PARENT.txt) 及 [裁决](sources/later/strong-measure-quasiminimality/ADJUDICATION.md)。

X 为有限面积 Borel 原点星体的平面零集等价类，要求**存在**逐方向含实际完整闭单位的 Borel 代表；可无界。`d(F,G)=|F△G|` 下 X 完备，且 `inf_X|F|=A_*`。若 α>0、`|F|≤A_*+α²`，存在 G，使 `|G|≤|F|`、d(G,F)≤α，且对**全部** Q∈X
`|G|≤|Q|+αd(G,Q)`，等价 `(1−α)|G\Q|≤(1+α)|Q\G|`。

强 L¹ 径向平方极限不足以自动保零高整针：普通极大误差好方向与实际短角弧平均恢复双物理射线；非退化零缺额三角形的不可数并用可数紧分层、内部球基与密度定理恢复而不增面积。无帽新增步骤以显式 Borel 远 halo 控制 `∩_l liminf_n B_(R_l,n)`，几乎每个方向获得某个有限帽内无限复现的整针见证，不是共同半径或错误的 limsup 控制。最后用零测方向居中单位补齐，R02 给同 inf，Ekeland 给全 Q 交换。

0<α<1 时，同一个 G 精确最小化固定正 Borel 权重 `1−α`（G 内）／`1+α`（外）的面积；只是交换式等价，不是无权面积达到。不能推出强预紧性、连续 selector、锐值或有限恢复继承该交换律。SMQ 的“两重叠单位段精确实现轻微膨胀”还说明原 near-inf 序列可每个方向都有严格长度余量，因此对每个原 near-minimizer 强求精确 tight direction 不合法。

## 为什么这些成果尚未把全类下界推进到构造尺度

1. **完整单位信息不能缩成有限点。** R15 保持每个方向、同记录、共同正高度和紧星形性，仍把有限样本模型面积降到任意小；R24 在真正整针上又显示标签系数不能直接支付真实并。成功的 R05 恰是具体的合并后物理收费，不应被失败路线抹去。
2. **“合法操作”与“净面积节省”相隔一条真实不等式。** FSC 保完整单位、覆盖方向且几乎处处变薄，却因闭轴三角形增面积；R18 的新增面积税也不能禁止另一体删旧料抵消。任何归约都应写净账 `|Q\K|−|K\Q|`。
3. **受限函数类的完整积分不等于全类归约。** R07–R09 保留凹、反射和 birth 结构；fold 正余项解决了该类真正的交叉损失，但没有把任意高度／外垂足／非周期身体送入该类。固定模型优化与全类 lower/matching 仍是不同义务。
4. **固定输入可恢复，不等于跨复杂度有统一误差。** R02 的上恢复、R06 的实际双侧恢复、R22 的稀疏生成和 R23 的统一支付系数各有明确量词，均不能自动给统一包数。一般 Hausdorff 极限的面积下连续性不存在，不能用紧性掩盖这笔误差。
5. **同体运动、强密度、等下确界不同。** R17 否定同体连贯运动，R18 否定固定体强面积密度；`A_coh=A_*` 仍未证亦未反驳。不能把“有一个坏 selector”当“无好 selector”，也不能把所有半径的强密度反例扩大为成本 inf 分离。
6. **结构账可以完全正确而不锐。** JS 的几何级数付款通过但定性强型已有，且真实竞争输入只收费内环。GSQ 现在允许对择取 near-inf 体作全 Q 相对交换，但尚无把它转成统一锐面积下界的几何比较。非达到性即便将来解决，也不必先于 inf 的求值。

## 未决项、证据缺口与禁止升级清单

| 项目 | 现有状态与精确缺口 |
|---|---|
| 原全类 sharp/matching | 缺同一个值的任意有限复杂度统一下界与合法逼近配对；0.28 只是尺度。 |
| 已求值最强小数 | U 保持；c_new、c_r、c_height、c_hl、Gamma_ms 均未在这些后来证明中给新数值评估。 |
| 一般有限不达到 | R21 混合核心严格差／替代下降未付，不得在摘要写成定理。 |
| coherent 等 inf | D refuted 不推出 `A_coh>A_*`；等号也没有证明。 |
| 原 median／参考补全 q | 对象不同；R12 只支付后用的实际端点门，不自动支付旧 median 全 birth 或 q 的活动 J。 |
| Q 迭代、旧同线规则 | R14 只一次原 Q；旧同线 ACTUAL_GAIN_OPEN 保持。 |
| JS 贡献身份 | 线性联合壳层收据可写；定性强型须明示旧 halo 推论，不主张文献优先权。 |
| 原 1/10 形式化 | 与普通证明、历史精确算术分账；当前另线进行，本账本无 kernel replay。 |
| 冻结上界代码 | 解析后续依赖既有 Data/Signs/EndpointEnvelope/PhaseC4D 源定理；本次没有完整重读/重建全部原代码，不能制造新 axiom receipt。 |
| 外部文献 | R16 的 Beer Theorem 1.3、R22 的 Körner Theorem 2.3 按完整内部证明明确导入；本次未重新读取外部完整 PDF，论文公开引用应由文献线核权威正文。 |
| 加权 halo 基础 | 保存的完整 reference 包含全 Borel 扩展，但有限 exposed-endpoint 基础仍为引用；JS 的普通弱型直接证明不依赖补造该基础。 |
| 历史来源与首创性 | 本账本没有新增历史优先权、Cunningham 1974 原文取得或全面文献不存在性的断言。 |

本次有界选择已覆盖：主 1/10 链、当前最强严格上链及独立 c_new、受限完整成本／fold、主要全类恢复与强变分结构、明确点采样／运动／强密度／剪切反例、有限达到性真实 partial 状态。未逐任务盘点数千工作树；其它已停放的 Γ/G、joint averaging、FREE、D12、nonconcave-LCM、各有限操作或拓扑控制，若正文要新增定理／反例，须另读它们的实际完整证明和最终裁决，不能仅从 CURRENT 的名称或本段清单认证。

## 归档、来源与完成核验职责

- `SOURCE_MAP.json` 的 `claim_sources` 是每项 R 的完整源清单；`sources` 中每项给本次内容哈希及原绝对路径。文内链接均指向逐字节副本，而非重写摘要。
- 同名 `PARENT.txt`、`RESULT.md`、`ADJUDICATION.md` 保留目录，避免跨路线串证。原文含旧 PENDING／CONDITIONAL 时不删字，最终适用状态在本账本与 JSON 的 claim status 中解释。
- `CURRENT.md`、`BASELINE.md` 和 `SHARP_VALUE_TARGET.md` 作为目标／状态定位保存，不作为独立证明替代。
- 本次核验只包含完整文本读取、来源路径追踪、复制、SHA-256、文件／引用一致性；不包含重新执行原算术、重建 Lean、数值积分、优化、安装、Git 操作或新的研究派发。
- 本账本不修改父代理的论文文件、CLOSEOUT 或 LEAN_PROGRESS。完整论文写作时应按逻辑节次组织这些结果，而不按 R 编号、派发轮数或历史顺序逐条搬入正文。
