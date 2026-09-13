# 64 类有限有理 `C_FS` schedule

## 结论

本目录给出一个完全有限、index-closed 的有理 schedule。four-term rational
surrogate 的精确最小支付系数是

\[
q=\frac{120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423}
{5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000}.
\]

两套实现严格认证并由 Lean 顶层定理给出

\[
\boxed{C_{\rm FS}\ge q\pi\approx0.07054486807936307
       >\frac{141}{2000}=0.0705.}
\]

`3527/50000` 只是较短的 strict rational corollary，不再作为 headline。
使用真实 logarithm 直接评估 frozen schedule，隐式最小值数值为
`0.07054487627351847`（class 49）；这是 **NUMERIC**，尚未做 validated
transcendental enclosure，因此不冒充 Lean theorem。

## 证据边界

- **EXACT / CERTIFIED：** `frozen_schedule.json`、`exact_certificate.py` 和
  `independent_validator.py` 共同认证上述有理 witness。
- **NUMERIC：** `numeric_scout.json` 是 `N=64` 局部数值候选，数值目标
  `0.07054487649892019`；它只负责寻找 schedule，不用于证明全局最优，也不用于
  识别 `C_FS` 与 continuum BVP。
- 本目录没有把 BVP 当作定理，没有声称 `C_64` 全局最优，也没有给出
  `C_FS` 的上界或 validated decimal enclosure。

## 冻结 schedule

`frozen_schedule.json` 使用正确的闭合索引：

- `N=64`；`alpha` 恰有 65 项，`R` 恰有 64 项，`t` 恰有 65 项；
- `eta = 28217997/200000000 = 0.141089985`；
- `alpha_0=0 < ... < alpha_64=eta`；
- `R_0=1/2`，且 `R_j^2 <= 1/4 + alpha_j^2`；
- `t_0=alpha_1`、`t_1>=eta`、`t_{j+1}<=R_j`；
- `t_64 < eta+1/2`，所以 low schedule 与第一条 high ledger 严格分离。

所有浮点 `alpha/R/t/eta` 都以分母 `10^9` 保守有理化：半径用整数平方根向下取整，
terminal switch 再锁到向下取整后的末半径。证明只读取冻结后的有理数。

## Exact Fraction / logarithm certificate

`exact_certificate.py` 从 schedule 原子数据重新计算每个 class 的

\[
P_j=F_{1/2}(\alpha_{j+1},t_1)
    +\sum_{i=1}^j F_{R_i}(t_i,t_{i+1}).
\]

对每个 logarithm 使用正项展开

\[
\log y=2\sum_{h\ge0}\frac{z^{2h+1}}{2h+1},\qquad
z=\frac{y-1}{y+1},
\]

并强制 `log_terms=4`，在 4 项后加入完整有理尾界

\[
2\frac{z^9}{9(1-z^2)}.
\]

因此 primitive 中负号前的 log 得到向下安全的积分值。认证结果：

- common direction coefficient：`44909/2000000 = 0.0224545`；
- exact checker 最小 low payment：约 `0.0224551289291926`；
- low margin：约 `6.28929192588418e-7`；
- `pi > 333/106` 后 margin：`217/212000000`；
- height margin：`1997/400000000`；
- high-tail uniform payment lower bound：约 `0.0244654164047297`。

完整精确分数保存在 `exact_result.json`。

## 独立 validator 与 high-tail contract

`independent_validator.py` 不导入 optimizer 或 exact checker。它在全部 class caps
和 switches 处重新切分径向轴，共重建 127 个非空原子；对每个原子重新判定唯一 active
window 和完整 eligible-class union，再逐原子累加 payment。它检查：

1. class partition 无 gap，所有 64 个 class 完整覆盖 `[0,eta]`；
2. 每个 credited class 都满足完整 geometry eligibility；
3. pointwise low load 最大为 1；
4. low/high 严格径向分离；
5. 不读取或信任任何 cached per-class totals；
6. high tail 覆盖全部 `k>=0`，而非有限抽样。

无限尾的符号合同如下。令 `A=eta+k/2`、`B=A+1/2`，冻结有理数
`r0 < sqrt(1+eta^2)`，并置 `d0=r0-eta`。对所有实数 `A>=eta`，

\[
\sqrt{A^2-\eta^2}\ge d_0(A-\eta)
\]

由

\[
A+\eta-d_0^2(A-\eta)
=2\eta+(1-d_0^2)(A-\eta)\ge0
\]

得到；另外 `r0^2<1+eta^2` 等价于
`1-d0^2-2 eta d0>0`。把这两个不等式代入平方差可得
`R_eta(A)>=A+d0`；另一方面 `R_eta(A)<A+1`。所以每条 high
ledger 的 width 至少为 `d0-1/2`，且 kernel factor 至少为

\[
\frac{\eta+1/2}{2\eta+3/2}.
\]

所得统一三角积分严格超过 common coefficient，符号上覆盖整个无限 tail。

## Mutations 与复现

五项 load-bearing mutation 必须被同一个 production validator 拒绝；其中后两项也必须被 exact checker 拒绝：

- `radius_direction`：逆转一处半径方向；
- `missing_tail_band`：把 tail 起点从 `k=0` 改为 `k=1`；
- `radial_overlap`：制造相邻 switch 重合。
- `negative_log_terms`：把正项截断数改成 `-1`，攻击 log-tail 方向；
- `unsafe_pi_lower`：把已证下界 `333/106` 偷换成错误方向的 `22/7`。

两个 checker 都把 `log_terms=4` 与 `pi_lower=333/106` 作为冻结证明合同，而不是信任任意 JSON 参数。

从仓库根目录运行：

```bash
python3 spikes/007-cfs-rational-cert/exact_certificate.py
python3 spikes/007-cfs-rational-cert/independent_validator.py
python3 spikes/007-cfs-rational-cert/mutations.py
python3 -m unittest discover -s spikes/007-cfs-rational-cert/tests -v
```

重跑数值 scout 并重新冻结（需要 NumPy/SciPy）：

```bash
python3 spikes/007-cfs-rational-cert/optimizer.py --write-frozen
```

重新冻结后必须再次运行上述 exact、independent、mutation 和 test 四道 gate。
