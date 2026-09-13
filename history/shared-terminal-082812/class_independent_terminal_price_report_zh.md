# Class-independent terminal price / global-worst kernel

## 裁决

这个模型有两个不同口径，结论必须分开：

1. **若把所有无界 high scales 一次性放进同一个 terminal theorem，global-worst kernel 恒为零。** H–TC 的 angular expansion 常数含 `1/R`；对 `M` 无上界取最坏值即 `R=∞`，所以不能用一个全尺度 terminal price直接闭合 tail。
2. **若在有限 cutoff `R` 前使用一个 class-independent terminal radial price，`R` 后接 fresh dyadic tail，则 all-cut 合法，而且 FLOAT scout 可超过当前 `0.073920942372137638`。** 当前最好的稳定候选在 `M0=.99, H=.2, R=1.60`：
   \[
   c_{\rm scout}=0.02636003744959517,
   \qquad \pi c_{\rm scout}=0.08281250000000001.
   \]
   但该数值还不是 continuum/Arb certificate。
3. **该组合不可能达到 `0.1`。** low branch 在此模型中只由旧 low radial kernel支付；即使把全部 source capacity 都给 low，仍只有
   \[
   c\le C_{\rm low}^{\max}=0.027158431429849736,
   \qquad \pi c\le0.08532072866303807<0.1.
   \]
   因而 `.1` 不是优化精度问题，而是本 architecture 的严格 low-side ceiling。

## 1. 单一 terminal radial price 的 all-cut theorem

记
\[
d\nu=\min(r,1)\,dr\,d\theta,
\]
固定有限 high block
\[
V\subset\{q:m\le M(q)<R\},\qquad m=M_0,
\]
并取任意非负 Borel radial price `p_T(r)`。令
\[
H_{m,R}[p_T]
:=\frac1{\pi R}\int_0^\infty
p_T(r)\min(r,1)\min\{1/2,(m-r)_+\}\,dr.
\tag{1}
\]
则对任意 Borel cut `V`，
\[
\boxed{
H_{m,R}[p_T] |V|
\le \int_{W(V)}p_T(|y|)\,d\nu(y).}
\tag{2}
\]

证明：H–TC first-birth theorem 对统一 endpoint interval `[m,R)` 及任意递减 kernel给出
\[
\int K(\tau(\theta))d\theta
\ge \frac{|V|}{\pi R}\int_0^{1/2}K(t)dt.
\]
取
\[
K(t)=\int_0^{(m-t)_+}p_T(r)\min(r,1)dr.
\]
它非负递减。Tonelli 将右端改写为 (1)，左端不超过 literal union 上的 priced source mass，得到 (2)。这里只定义一次共同 `τ`、只应用一次 H–TC；没有把各 class 的 terminal receipts 相加，因此没有 owner conflict。

若 block 无上界，则 `1/(πR)→0`，(1) 退化为零。这解释了为什么 tail 必须另用尺度化 fresh radial bands，不能声称一个 terminal price覆盖所有 scales。

## 2. 与 low / class-global / tail 的合法组合

对 cutoff `R`：

- low directions使用一个 radial price `p_L(r)`；
- 全部 finite-high directions `M∈[M0,R)` 共用一个 `p_T(r)` 和 (2)；
- finite block 内可叠加 class-global positive-sheet 与 exact-pole columns；每列使用已审计的 radial kernel，pole 单列收费；
- `M≥R` 用 fresh dyadic classes `[2^nR,2^{n+1}R)`，第一条 source band为 `[R/2,R)`，以后按尺度放大，物理 bands 半开且不交。

点态 source load 是
\[
p_L+p_T+\sum_j(p_j^++p_j^{\rm pole})+p_{\rm tail,0}\le1
\tag{3}
\]
（后续 tail bands在自己的物理 radial atoms上另查 `≤1`）。每个 column 都先有独立 all-cut receipt；再由同一 literal union 上的 source-price bridge及 (3) 求和。因此该组合的 all-cut逻辑成立，不需要跨 class terminal owner。

## 3. 数值优化

### 固定旧 cutoff `R=2S_6`

若硬把七个 finite classes 全部塞入一个 global terminal block，分母变成
\[
R=13.67186718.
\]
FLOAT LP 得到
\[
c=0.0032413992537593875,
\qquad \pi c=0.01018315608296193.
\]
这里 global terminal 的满价理论上限也只有 `0.00330858154`。所以“七类共享一个 terminal price”本身极弱。

### 优化 cutoff

对旧 scale breakpoints 的 cutoff 扫描，最佳是最早 cutoff `R=1.45628085`，给
\[
\pi c=0.07574337205306786>0.073920942372137638.
\]
继续把 `R` 作为连续参数，在 `1.54–1.62` 细扫并把 finite-class参数约束加密到 `81×17`、holdout 到 `401×41`，最好的候选是
\[
\boxed{R=1.60,\,c=0.02636003744959517,\,\pi c=0.0828125.}
\]
此点 low 与第一 tail row同时 active；global terminal contribution约 `0.00792640`。候选超过当前约
\[
0.0828125-0.073920942372137638=0.00889155762786236.
\]

但邻近 `R` 的 LP/holdout 对接近 class seam 的 positive/pole rows较敏感；例如若训练参数网格过疏，会出现 LP 值高于 dense replay。故 `R=1.60` 只能称为 **FLOAT candidate**，不能直接宣传为新界。下一门禁必须是：

1. 用 interval boxes 覆盖 `M∈[.99,1.60)`、`h∈[0,.2]`，positive 与 exact pole分开；
2. source load outward `≤1`；
3. low、global terminal、首 tail及所有后续 dyadic tail都给 exact/outward lower；
4. 对 seam `M→R^-` 单独做闭包检查；
5. 最终只在严格下端仍高于 `0.073920942372137638/π` 时升级。

## 4. 为什么 `.1` 在本模型内不可能

对 low cut，terminal、finite class-global 和 high tail kernels都为零；只有旧 low radial column贡献。由 `p_L(r)≤1`，
\[
K_Lp_L\le K_L\mathbf1=C_{\rm low}^{\max}.
\]
已复算
\[
C_{\rm low}^{\max}=0.027158431429849736<0.1/\pi.
\]
所以无论怎样优化 `R`、finite class partition、global terminal price或 class-global prices，都有
\[
\pi c\le0.08532072866303807<0.1.
\]
要达到 `.1`，必须新增真正改善 low cut 的几何 receipt；只修 terminal owner conflict 不够。

## 5. 证据边界

- (2) 及 source-price组合是解析 all-cut论证。
- 所报 `0.0828125` 是 scipy/HiGHS + Gauss quadrature + dense holdout 的 FLOAT scout，不是严格 certificate，也不声称 continuum 最优。
- `.1` 的否定是该模型内部的 architecture ceiling，不是否定原几何问题存在更强方法。
