# 有界 endpoint radius 的 weighted endpoint–interior Hall bound

## 结论

令 `Q⊂RP¹` 为 Borel 方向集（`RP¹` 取弧长测度，满质量为 `π`）。对每个 `q∈Q`，Borel 地选择一条单位弦

\[
[A_q,B_q],\qquad |A_q-B_q|=1,
\]

并令

\[
T_q=\operatorname{conv}(0,A_q,B_q),\qquad
M_q=\max(|A_q|,|B_q|)\le R.
\]

记

\[
E_U=\bigcup_{q\in U}T_q,
\qquad
W(F)=\int_F \min(1,|x|^{-1})\,dx .
\]

则对每个 Borel cut `U⊂Q`，都有

\[
\boxed{
W(E_U)\ge \frac{|U|}{108\pi R}.
}
\tag{1}
\]

因此完整低尺度族满足

\[
\boxed{
W(E_Q)\ge c(R)|Q|,
\qquad c(R)=\frac1{108\pi R}.
}
\]

特别地：

\[
M_q\le1:\quad c(1)=\frac1{108\pi},
\]

\[
M_q\le2:\quad c(2)=\frac1{216\pi}.
\]

若方向测度归一化为 `d q/π`，相应常数是 `1/(108R)`。

这是 literal all-cut bound；它不假设 selector 连续、单射或有限分片，允许任意 Borel jumps、endpoint-angle caustics、不同方向碰撞和完全重合。容量是物理 union 的 weighted area，未按 chord/source label 重复计算。

## 构造：far-endpoint collar 加 triangle interior

对每个 `q` Borel 地选较远 endpoint `F_q`；半径相等时用固定 Borel tie-break。另一 endpoint 记为 `N_q`。固定

\[
\ell=\frac16,
\qquad
a=\frac12-\ell=\frac13.
\]

取从 `F_q` 朝 `N_q` 的长度 `ell` terminal collar

\[
S_q=\{F_q-t(F_q-N_q):0\le t\le\ell\}.
\]

因为单位弦总有 `M_q≥1/2`，故

\[
\frac13=a\le |x|\le R
\qquad(x\in S_q).
\tag{2}
\]

令 `J_q⊂S¹` 为 `S_q` 从原点看到的 angular image（退化 radial collar 时允许它是单点）。由凸性，collar 下方的整块 radial interior 都属于 triangle：

\[
\Gamma_q:=\{r e_\phi:0\le r\le a,\ \phi\in J_q\}
\subset T_q.
\tag{3}
\]

这就是 endpoint+interior legal parcel：endpoint collar 决定 angular trace，triangle interior 提供从 `0` 到 `a` 的全部 weighted radial capacity。

## 每个 cut 的 angular Hall estimate

给定 `U⊂Q`，置

\[
P(U)=\bigcup_{q\in U}J_q.
\]

证明

\[
|U|\le \frac{\pi R}{\ell}|P(U)|
=6\pi R|P(U)|.
\tag{4}
\]

为避免 degenerate `J_q`、非闭 union 和 jump seam 的拓扑问题，取任意开集 `O⊃P(U)`。将 `O` 分成可数个圆周连通分支 `C`，长度记为 `L`。每个连通集 `J_q` 完全落在唯一一个 `C` 中（若 `O=S¹` 则结论平凡）。把该分支中心记为 `c`。

若

\[
L\ge\ell/R,
\]

则对应方向集在 `RP¹` 中至多长 `π`，所以

\[
|U_C|\le\pi\le(\pi R/\ell)L.
\]

若 `L<ell/R<π`，collar 两端都在半径不超过 `R`、角度属于 `C` 的扇形中。取相对中心射线的横向投影，得到

\[
\ell|\sin(q-c)|
\le2R\sin(L/2).
\tag{5}
\]

故 `RP¹` 中所有这些 `q` 的总长度至多

\[
2\arcsin\!\left(\frac{2R\sin(L/2)}\ell\right)
\le \frac{\pi R}{\ell}L.
\tag{6}
\]

这里当 arcsine 参数达到 `1` 时改用前一平凡分支；其余情形使用
`arcsin x≤πx/2` 和 `sin(L/2)≤L/2`。对 `O` 的各分支求和：

\[
|U|\le(\pi R/\ell)|O|.
\]

再对所有开集 `O⊃P(U)` 取下确界，得到 outer-measure 版本 (4)。对 Borel selector，相关 union/projection 是 analytic，从而在完成测度下可测；因此可直接写通常的测度。

## Weighted physical capacity

由 (3)，

\[
E_U\supset
\{r e_\phi:0\le r\le a,\ \phi\in P(U)\}.
\]

由于 `a=1/3<1`，权重在该 parcel 上等于 `1`，故

\[
W(E_U)
\ge \int_{P(U)}\int_0^a r\,dr\,d\phi
=\frac{a^2}{2}|P(U)|
=\frac1{18}|P(U)|.
\tag{7}
\]

结合 (4)：

\[
W(E_U)
\ge \frac1{18}\frac{\ell}{\pi R}|U|
=\frac{|U|}{108\pi R}.
\]

## 常数优化与 source-once 解释

一般取 `0<ell<1/2` 时，`a=1/2-ell`，同一论证给

\[
c_R(\ell)
=\frac{\ell(1/2-\ell)^2}{2\pi R}.
\]

其唯一内点最大值在 `ell=1/6`，即上面的 `1/(108πR)`。

关系 `q↦Gamma_q` 的 Hall 形式正是

\[
|U|\le108\pi R\,W\!\left(\bigcup_{q\in U}\Gamma_q\right)
\quad\text{for every Borel }U.
\]

在标准 Borel/analytic relation 的 Kellerer measurable-marriage 形式下，它给出一个容量至多 `108πR` 的可测 fractional routing。更重要的是，证明本身直接对 physical union 估计：同一点即使被任意多个 jumps/collisions 命中，也只贡献一次 `W`，所以 source-once 已内置，而不是事后按标签求和。

## 边界与诚实范围

- `M_q=1/2` 的 centered diameter 是最坏半径校准之一；构造仍有 `a=1/3`，不退化。
- radial terminal collar 的 `J_q` 可退化为点；开外包论证仍覆盖它，未假设正 angular width。
- `M_q=R` 用闭界即可；边界方向不需另行删除。
- 该常数是一个明确、稳健的 coarse low-scale bound，不声称 sharp。
- 本证明没有把 endpoint-only pushforward 当作容量；真正 legal source 是 collar 下方的二维 interior parcel。若删掉 interior，只保留 endpoint trace，二维 `W` 容量可为零，不能得到同类 Hall 定理。
