# 统一 high-scale theorem：half-open scales × disjoint radial bands

## 1. 输入与记号

固定 `1/2<M0<=3/4`，令 `r0=1-M0`，并假设已经证明 terminal-collar first-birth 输入：若方向 cut `U` 的 endpoint radii 落在 `[m,R)`，则对任意物理半开径向带 `[a,b)`，

\[
 W(E_U\cap\{a\le |x|<b\})\ge { |U|\over \pi R}
 H(m;a,b),
\]
\[
 H(m;a,b):=\int_0^{1/2}
 [G(\min\{b,m-t\})-G(a)]_+\,dt,
\quad
G(r)=\begin{cases}r^2/2&r\le1,\\r-1/2&r\ge1.\end{cases}
\]

这里 `W(F)=∫_F min(1,|x|^{-1})dx`。以下结论对 endpoint-radius map `M(q)>=M0` 的**任意 Borel distribution**成立；不假设密度、原子性或正则性。

## 2. 统一定理

取严格递增且趋于无穷的 scale boundaries
\[
 s_0=M_0<s_1<s_2<\cdots\uparrow\infty
\]
及递增 radial boundaries
\[
 a_0=r_0<a_1<a_2<\cdots,
 \qquad a_{j+1}\le s_j.
\]
用半开类与半开带
\[
 U_j=\{q:s_j\le M(q)<s_{j+1}\},\qquad B_j=[a_j,a_{j+1}).
\]
定义
\[
 c_j={H(s_j;a_j,a_{j+1})\over \pi s_{j+1}},
 \qquad c(\mathbf s,\mathbf a)=\inf_j c_j.
\]
则
\[
 \boxed{W(E_U\cap\{|x|\ge r_0\})\ge
 c(\mathbf s,\mathbf a)|U|.}
\]

证明只有两步：每个 `U_j` 应用 first-birth 输入；不同 `B_j` 物理不交，故可直接相加。半开约定使每个 endpoint 与每个 radial atom 唯一归属。该证明不使用 multiplicity、virtual seams 或 overlap rebates。

在有序不交带的优化类中可不失一般性取相邻带无 gap：若 `[l_j,b_j)` 前有 gap，把 `l_j` 降到上一带上端只会增大 kernel，且不破坏可达性 `b_j<=s_j`。

令
\[
 C_*(M_0)=\sup_{(\mathbf s,\mathbf a)}c(\mathbf s,\mathbf a).
\]
这就是该 half-open-scale/disjoint-band proof architecture 的最优最坏 all-cut coefficient。

## 3. 精确 Bellman / viability DP

状态为当前 class lower radius 与未用 radial frontier `(s,a)`。值函数满足
\[
 \boxed{V(s,a)=\sup_{a<b\le s,\ S>s}
 \min\left\{{H(s;a,b)\over\pi S},V(S,b)\right\}.}
\]
于是 `C_*(M0)=V(M0,r0)`。等价地，对试探值 `c>0`，一步可行当且仅当
\[
 a<b\le s,\qquad s<S\le {H(s;a,b)\over\pi c}.
\]
从 `(M0,r0)` 能沿这些边无限 escape 到 `s_j→∞`，当且仅当 `c<C_*`（端点值用闭包/极限解释）。这是适合 interval arithmetic 的严格 decision DP；不应把窄单尺度值直接当作 uniform 值。

正系数最优轨道除 slack/tail 外可 equalize：
\[
 s_{j+1}={H(s_j;a_j,a_{j+1})\over\pi c}.
\]

### 连续 ODE 的正确地位

真正问题是上述非局部 jump-DP，而不是普通 ODE。若强迫 mesh `s_{j+1}-s_j→0` 且 `a_{j+1}-a_j→0`，则
\[
 H(s;a,a+da)=\tfrac12\min(a,1)\,da+o(da),
\]
所以每类系数趋零；正 uniform coefficient 必须保留有限 jumps。形式连续松弛为
\[
 {da\over dn}={2\pi c\,s\over\min(a,1)},
\]
但它只可作 scouting，不等价于原问题。

在远区 `a>=1` 且 `s-b>=1/2` 时有精确线性式
\[
 H(s;a,b)=(b-a)/2,
\]
故 equalized tail 是离散控制方程
\[
 s_{j+1}={a_{j+1}-a_j\over2\pi c},\qquad a_{j+1}\le s_j.
\]
若用定比 ansatz `s_{j+1}=q s_j, a_j=\kappa s_j`，尾系数为
\[
 c_{tail}={\kappa(q-1)\over2\pi q},\qquad \kappa q\le1,
\]
其最大值 `1/(8π)` 在 `q=2, κ=1/2`；因此 `M0=.655` 的瓶颈必在早期过渡层，而非高尺度尾。

## 4. Rigorous upper / lower（M0=131/200）

### 一般严格上界

第一带满足 `a1<=M0`、`s1>M0`，故
\[
 C_*\le {H(M_0;r_0,M_0)\over\pi M_0}
 ={(2M_0-1)^2(2-M_0)\over6\pi M_0}
 =0.0104689529729\ldots.
\]
这是 narrow coefficient 的正确角色：**upper bound**，不是 uniform lower bound。用 `π>333/106` 可得完全有理上界
\[
 \boxed{C_*<13700977/1308690000<0.010469231.}
\]

### 显式严格下界

取以下十进制数（均按所写有限小数视为有理数）：

\[
\begin{aligned}
(s_0,\ldots,s_6)=&(0.655,0.89568,1.13330,1.38941,1.67087,1.98598,2.44343),\\
(a_0,\ldots,a_6)=&(0.345,0.61979,0.86850,1.10730,1.36355,1.64549,1.96300).
\end{aligned}
\]

前六类用 `[s_j,s_{j+1})×[a_j,a_{j+1})`。随后先用 class `[s6,2s6)`、band `[a6,s6)`；再接标准 dyadic tail：class `[2^k s6,2^{k+1}s6)` 配 band `[2^{k-1}s6,2^k s6)` (`k>=1`)。

把 kernel 在 breakpoints `t=s-b,s-a,s-1,0,1/2` 分段积分，且仅用 `π<355/113`，前七个严格下界依次为

\[
0.0075166981,
0.0075170634,
0.0075169096,
0.0075170894,
0.0075171760,
0.0075170280,
0.0075171018.
\]

第一项的有理证书为
\[
 {H(s_0;a_0,a_1)\over (355/113)s_1}
 ={7170172367700743\over953899200000000000}
 >0.00751669.
\]
其余六项均更大。dyadic tail 因 `s6>1` 满足
\[
 \pi c_k=1/8-1/(16m_k),\qquad m_k=2^k s_6,
\]
并随 `k` 增大，且首项远大于 `0.00751669`。因此
\[
 \boxed{0.00751669<C_*(0.655)<0.010469231.}
\]

浮点 DP equalization 给出 scouting 值 `0.00751675` 左右；这不是上界证书，不能把 bracket 偷换成数值等式。要把 upper 收紧到该水平，应对上面的 viability DP 做 outward-rounded interval branch-and-bound / Bellman supersolution。

## 5. Dyadic 是否远离最优

标准 dyadic source-once 值为
\[
 c_{dyad}={258509\over15720000\pi}=0.00523447648648\ldots.
\]
上述显式构造与它比较时 `π` 消去；最小层相对比为
\[
 {8312323718307941\over5788533528000000}>1.43599.
\]
故 dyadic 至少损失 `43.5%`（相对 dyadic），或相对新构造低约 `30.36%`。所以它在该 proof architecture 中**定量地远离最优**；但现有严格 bracket 尚不足以宣称 `0.00751675` 就是全局最优值。

## 6. 证明状态

以上统一定理条件于开头的 audited terminal-collar first-birth 输入。一旦该输入已在主文证明，所有 distribution-uniform、half-open、literal-union 与显式 lower/upper 结论均为严格结论；数值优化只负责发现候选，不承担证明。
