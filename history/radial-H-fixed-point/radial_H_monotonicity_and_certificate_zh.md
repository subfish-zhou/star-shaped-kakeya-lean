# `C_low` 对 `H` 的精确单调式与新有理证书候选

## 1. 固定 `M,A` 的精确公式

令
\[
m=1-M,\quad \alpha=2\arcsin\frac1{2M},\quad B(H)=\arctan\frac Hm,
\]
\[
c(H)=\frac{2\alpha}{\alpha+2B(H)},\qquad
\rho(H)=\frac{mB(H)}{\alpha+B(H)}.
\]
由于 `M<1` 时 `alpha>1` 且 `atan x<x`，对每个 `H>0` 都有 `rho(H)<H`；所以旧稿中的 `a=min(H,rho)` 实际恒为 `rho`（`H=0` 取极限）。定义
\[
P_m(r)=-r^2+4mr-4m^2\log(1+r/m),
\]
则 inner all-layer 项为
\[
C_{in}(M,H)=\frac{c(H)\rho(H)^2}{2}+P_m(m)-P_m(\rho(H)).
\]

对 one-sided extension，令
\[
k(H)=\frac{\alpha}{\alpha+2\arcsin(2H)},\quad
w(r)=\frac{1/2-r}{1/2+r},\quad
x(H)=\frac{\arcsin(2H)}{2(\alpha+\arcsin(2H))},
\]
并令
\[
Q(r)=-\frac{r^2}{2}+r-\frac12\log(1/2+r),\qquad
u(H)=\min\{A,H,x(H)\}.
\]
于是 owned outer band `[m,A)` 的精确统一式是
\[
C_{out}(M,H;A)=Q(A)-Q(m)
+\mathbf 1_{\nu>m}\left[\frac{k(H)}2(\nu^2-m^2)-Q(\nu)+Q(m)\right].
\]
因此
\[
\boxed{C_{low}(M,H;A)=C_{in}(M,H)+C_{out}(M,H;A).}
\]

## 2. 精确单调导数

在 `rho` 处有 `P_m'(rho)=c rho`，故移动交点项完全抵消：
\[
\boxed{\frac{dC_{in}}{dH}=\frac{\rho^2}{2}c'(H)
=-\frac{2\alpha m\rho^2}{(\alpha+2B)^2(m^2+H^2)}<0.}
\]
又
\[
k'(H)=-\frac{4\alpha}{\sqrt{1-4H^2}\,[\alpha+2\arcsin(2H)]^2}<0.
\]
outer 项分段导数为：

- 若 `nu=x`：`C_out' = k'(x^2-m^2)/2`；
- 若 `nu=A`：`C_out' = k'(A^2-m^2)/2`；
- 若 `nu=H`：`C_out' = k'(H^2-m^2)/2 + H[k-w(H)]`；
- 若 `nu<=m`：`C_out'=0`。

每个有效分支都非正；所以固定 `M,A` 时 `C_low` 随 `H` 严格下降（除 outer 已饱和部分外）。换言之，**降低 `H` 必定增强 low receipt**。

## 3. `H` 下降时 branch 的变化

1. inner merged/high-offset branch 只占 `0<r<rho(H)`；`H` 下降时 `rho` 下降、`c` 上升，该损失区缩小。
2. ordinary two-component branch 从 `rho(H)` 向左扩张，因而增强。
3. outer supplemental limiter 只占 `m<r<min(H,x(H),A)`；`H` 下降时 `k` 上升、`x` 下降。
4. 当
\[
H\le H_{van}:=\frac12\sin\frac{2m\alpha}{1-2m}
\]
时 `x(H)<=m`，outer supplemental branch 完全消失，`C_out=Q(A)-Q(m)`，以后再降 `H` 不再改善 outer 项。
5. 但全局 easy branch 是 `H/2`，随 `H` 下降线性恶化；最优值因此在 `H/2` 与 hard radial-price 值的固定点附近，而不是 `H->0`。

## 4. 新 exact-certificate 候选

取全部有限小数按精确十进制有理数解释：

- `M0=0.9999=9999/10000`；
- `H=0.14785=2957/20000`；
- scales
  `[0.9999,1.47501648,2.05059068,2.75723440,3.64393848,4.86253053,7.10984987]`；
- radial boundaries
  `[0.36294599,0.90963379,1.38479070,1.96023628,2.66629690,3.55037801,4.75757582,7.10984987]`。

纯 `Fraction` + 外向 `asin/atan/log/pi` 级数证书两阶段重放通过：

- low per-radian lower: `0.023529766753073680`；
- weakest finite high lower: `0.023529842794678962`；
- first dyadic tail: `0.038389664888901360`；
- easy area: `H/2=0.073925`；
- 直接组装的 minimum total-area lower:
  \[
  \boxed{0.073920942372137638>0.0739>0.072323077979923422.}
  \]

证书显式断言 `>0.0739`，严格余量 `0.000020942372137638`。这是可复算的新候选，但尚未经过独立 fail-closed proof-chain audit，不能替代当前正式 promoted 的 `0.072323077979923422`。

当前 7-bin architecture 的连续 scout 在 `M0->1`、`H≈0.14784237` 附近停在约 `0.07392118`；离 `0.1` 很远。达到 `0.1` 需要新 kernel/ownership 机制，而非只调 `H,M0`。