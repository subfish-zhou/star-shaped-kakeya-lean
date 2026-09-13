# H-TC provenance 链审计（2026-08-17）

## 裁决

**H-TC standalone PASS（附本文给出的两个测度论勘误）**。下列链足以支撑 `M0=0.99` radial-price high bins：

`terminal interval expansion → first-birth → radial-band kernel → half-open mixed scales`。

因此 `final_theorem_audit_M099_zh.md` 中“`H-TC proof artifact 未定位`”这一项可解除；**OPR 仍是独立 BLOCK，本审计不处理 OPR**。

## 固定证据

- `/tmp/low_scale_terminal_collar_c11a.md`  
  SHA-256 `669b1ddd3881140b7dec727b40ce8597791212e7f46bf0a51c2aeab594b64f95`
- `/tmp/continuous_collar_dc04.md`  
  SHA-256 `40d06f1b96035e46c25272d8bb7926075e7f17ccbca688ebe2bc5bc7e967adb9`
- `/tmp/high_literal_union_6e98.md`  
  SHA-256 `5dfeb008abe35f4438dd3b2ae4f1cfaca12fec571a909f23b4dc90f856f35b5a`
- `/home/argustest/high_scale_unified_theorem_zh.md`  
  SHA-256 `2164eef7ca1ba67d80bdc869fc58ceacdfead6a7d5b26b6bf02089a84b230952`

`/home/argustest/high_literal_union_all_cut_zh.md` 与第三项逐字同 hash。

## 逐桥核对

### 1. Terminal interval expansion

第一件 artifact 对任意 Borel cut `V` 和任意 collar depth `0<t<1/2` 的同一几何论证给出

\[
 |P_t(V)|\ge {t\over \pi R}|V|,
\]

只要求较远 endpoint 半径 `M(q)≤R`（half-open scale `M<R` 更强）。证明通过任意开外包处理退化 angular image、非闭 union 与 jump seams，不要求 selector 连续或单射。`t=0` 平凡，`t=1/2` 由单调极限取得。

若 class 另有 `M(q)≥m`，则 collar 上深度不超过 `t` 的点满足 `|x|≥m-t`；从原点到该 collar 点的线段逐字包含于 anchored triangle。故每个 `θ∈P_t(V)` 的 literal union 含径向段至 `m-t`。这正是 H-TC 的几何输入，没有 multiplicity-to-union 步骤。

### 2. First-birth（测度论勘误）

令 `P_t` 随 `t` 递增，并定义

\[
 \tau(\theta)=\inf\{t:\theta\in P_t\}.
\]

`continuous_collar_dc04.md` 写了 `|{τ≤t}|=|P_t|`；对仅 Borel、可跳跃的 selector，这个等号不必成立。所需且成立的是

\[
 P_t\subset\{\tau\le t\},\qquad
 F_\tau(t):=|\{\tau\le t\}|\ge |P_t|.
\]

因为 `P_t` 是 Borel relation 的投影，所以 analytic/Lebesgue measurable；`{τ<a}=⋃_{r<a,r∈Q}P_r`，故 `τ` 可测。若 `τ(θ)=u`，则对每个 `v>u` 有 `θ∈P_v`，从而 literal union 的该 radial fibre 含到 `m-u` 以下的所有半径；上端点是否取得对 `W` 无影响。

对任意递减、非负 kernel

\[
 K(t)=[G(\min\{b,m-t\})-G(a)]_+,
\]

Lebesgue–Stieltjes 分部积分（保留 `t=1/2` 的边界项；它在远尺度可非零）给出

\[
 \int K(\tau(\theta))d\theta
 \ge { |V|\over\pi R}\int_0^{1/2}K(t)dt.
\]

所以原文错误的分布函数等号不影响 H-TC；以上不等式是其严格修复。特别地，不可在远尺度照抄 `K(1/2)=0`，但完整边界项恰好恢复 `∫K`。

### 3. Radial bands

由上一节，对 Borel class `V⊂{m≤M<R}` 与半开物理带 `B=[a,b)`，

\[
 W(E_V\cap B)\ge {|V|\over\pi R}
 \int_0^{1/2}[G(\min\{b,m-t\})-G(a)]_+dt.
\]

这是 literal-union 收据：固定 `θ` 只按首次出现时间收费一次，固定 `(r,θ)` 只进入一次极坐标积分。

### 4. Mixed scales、Borel cuts 与 source-once

对 Borel selector，endpoint maps、`M(q)` 以及

\[
 U_j=U\cap\{s_j≤M<s_{j+1}\}
\]

均为 Borel；half-open 约定使 scale equality 唯一归属。`M0=0.99` 证书的 radial owners 为

- low `[0,a0)`；
- high finite `[a_j,a_{j+1})`；
- tail `[2^{n-1}s6,2^n s6)`。

它们首尾相接、两两不交并覆盖 `[0,∞)`；边界圆为二维零测，且 half-open 约定也给出字面唯一 owner。因此每个物理 atom 的总 price `≤1`，low/high、finite/tail、scale/scale 均无双重付款。

`high_scale_unified_theorem_zh.md` 的一般证明中写了
`W(E_U∩{|x|≥r0})=Σ_jW(E_U∩B_j)`；若一般的 `a_j` 有 gap 或有界，该等号应改为 `≥`。结论只需要该不等式，故统一定理及实际无-gap、无界证书均不受影响。

## 复算

- `check_high_literal_union_all_cut.py`：`HIGH_LITERAL_UNION_ALL_CUT_CHECK_PASS`；`c_H=0.0052344764864812685`。
- `radial_price_certificate.py`：`RADIAL_PRICE_EXACT_CERTIFICATE_OK`；high bins 的严格共同下端为 `0.023021150720250842`，pointwise total price 的精确上界为 `1`。
- `final_theorem_audit_check.py`：组装算术通过；其旧输出仍列 H-TC 为接口 BLOCK，是因为该旧文件未引用本次新定位的 proof chain，不是复算失败。

## 剩余边界

- 本 PASS 适用于 Borel selector / Borel cuts 的 H-TC 与 radial-price high-bin 组装。
- 从任意不可测 selector 恢复 Borel finite selector 的 OPR 不在这些 artifacts 中；故无条件 outer-measure 最终定理仍因 OPR 单独 BLOCK。
