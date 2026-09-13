# High-\(M\) literal-union all-cut 系数（严格版）

## 0. 设定与唯一输入

令 \(M_0=131/200=0.655\)，并置
\[
r_0=1-M_0=69/200=0.345.
\]
对方向 cut \(U\)，令 \(M(q)\) 是所选单位弦的较远端点半径，且本节只处理 \(M(q)\ge M_0\)。记 \(E_U\) 为相应 anchored triangles 的**实际并集**，并使用
\[
W(F)=\int_F\min(1,|x|^{-1})\,dx
 =\int_{\mathbb S^1}\int_0^{\rho_F(\theta)}\min(r,1)\,dr\,d\theta.
\]
唯一几何输入是已审计的 terminal-collar interval expansion：若一个 cut \(V\) 满足 \(M(q)<R\)，则对 \(0\le t\le1/2\)，
\[
|P_t(V)|\ge \frac{t}{\pi R}|V|,
\tag{TC}
\]
且每个 \(\theta\in P_t(V)\) 的 triangle union 包含从原点到至少 \(m-t\) 的径向段，只要该 scale 中 \(M(q)\ge m\)。以下只用 first-birth，不使用 multiplicity action。

记
\[
G(s):=\int_0^s\min(r,1)\,dr=
\begin{cases}s^2/2,&0\le s\le1,\\ s-1/2,&s\ge1.\end{cases}
\]

## 1. 窄 threshold scale

先假设 \(M(q)\in[M_0,M_0+\varepsilon)\)，最后令 \(\varepsilon\downarrow0\)。只保留 outer band \([r_0,M_0)\)。首次在深度 \(t\) 出现的角度可获得一次且仅一次的容量
\[
K_0(t)=\bigl(G(M_0-t)-G(r_0)\bigr)_+.
\]
由 (TC) 与 Stieltjes first-birth 分部积分，
\[
W(E_U\cap\{r_0\le |x|<M_0\})
\ge \frac{|U|}{\pi(M_0+\varepsilon)}
\int_0^{1/2}K_0(t)\,dt.
\]
由于 \(M_0-r_0=2M_0-1=31/100<1/2\)，且整个 band 位于单位圆内，
\[
\int_0^{1/2}K_0(t)dt
=\frac{(M_0-r_0)^2(M_0+2r_0)}6.
\]
故窄尺度极限系数为
\[
\boxed{
c_{\rm nar}(M_0)
=\frac{(2M_0-1)^2(2-M_0)}{6\pi M_0}.}
\tag{1}
\]
在 \(M_0=131/200\) 时，
\[
\pi c_{\rm nar}=\frac{258509}{7860000},\qquad
c_{\rm nar}=0.0104689529729625\ldots.
\tag{2}
\]
这只是 infinitesimally narrow scale 的系数，不能直接宣称对全部 \(M\ge M_0\) uniform。

## 2. 连续 \(M\) 的 half-open dyadic 分层

定义
\[
m_j=2^jM_0,\qquad
U_j=\{q\in U:m_j\le M(q)<2m_j\},\quad j\ge0.
\]
这是对连续取值 \(M(q)\) 的 Borel half-open 分层；边界只归入一个类。给各类分配以下互不相交的**物理径向 bands**：
\[
B_0=[r_0,M_0),\qquad
B_j=[m_j/2,m_j)=[m_{j-1},m_j),\quad j\ge1.
\tag{3}
\]
于是 \(B_j\cap B_k=\varnothing\)（\(j\ne k\)），并且
\[
\bigcup_{j\ge0}B_j=[r_0,\infty).
\]
对第 \(j\) 类，(TC) 可取严格上端 \(R=2m_j\)（或先取 \(2m_j+\eta\) 再令 \(\eta\downarrow0\)）。其 first-birth kernel 为
\[
K_j(t)=
\begin{cases}
\bigl(G(M_0-t)-G(r_0)\bigr)_+,&j=0,\\
\bigl(G(m_j-t)-G(m_j/2)\bigr)_+,&j\ge1.
\end{cases}
\tag{4}
\]
因此，对每个 Borel cut \(V\subset U_j\)，
\[
W(E_V\cap B_j)\ge c_j|V|,
\qquad
c_j=\frac1{2\pi m_j}\int_0^{1/2}K_j(t)dt.
\tag{5}
\]
这里 (5) 是 literal-union 收据：每个角度只在其首次出现深度付一次；没有对 triangle multiplicity 收费。

## 3. 跨 scale 物理重叠的消除

虽然不同 \(U_j\) 的 triangles 可以在平面中任意碰撞、嵌套或重合，但我们只向第 \(j\) 类收取 \(B_j\) 内的质量。由 (3) 的物理不交性，
\[
\begin{aligned}
W(E_U\cap\{|x|\ge r_0\})
&=\sum_{j\ge0}W(E_U\cap B_j)\\
&\ge\sum_{j\ge0}W(E_{U_j}\cap B_j)\\
&\ge\sum_{j\ge0}c_j|U_j|\\
&\ge \left(\inf_{j\ge0}c_j\right)|U|.
\end{aligned}
\tag{6}
\]
第二行只用 \(E_{U_j}\subset E_U\)，第三行用各 scale 自己的 first-birth theorem。故 collisions 不产生 rebate，也无需任何未证的 multiplicity-to-union 原理。

定义严格 uniform 系数
\[
\boxed{c_H(M_0):=\inf_{j\ge0}c_j.}
\tag{7}
\]
这同时处理任意大的 \(M\) 和连续的 \(M(q)\) 取值；绝不能把不可数 singleton scales 的未截断 core 相加。

## 4. 在 \(M_0=0.655\) 的显式求值

第零类的 denominator 从窄尺度的 \(M_0\) 变为 dyadic class 上端 \(2M_0\)，故
\[
c_0=\frac12c_{\rm nar},
\qquad
\pi c_0=\frac{258509}{15720000}.
\tag{8}
\]
对 \(j=1\)，直接按 \(m_1-t=1\) 分段积分得
\[
\pi c_1=\frac{2086643}{31440000}=0.06636905216\ldots>
\pi c_0.
\tag{9}
\]
对 \(j\ge2\)，有 \(m_j/2\ge1\)，所以 \(G\) 在线性支上，
\[
\pi c_j=rac18-\frac1{16m_j}.
\tag{10}
\]
该式随 \(j\) 递增；其最小值在 \(j=2\)，为
\[
\pi c_2=\frac{53}{524}=0.1011450381\ldots>
\pi c_0.
\]
因此 (7) 的 infimum 确由第零类达到：
\[
\boxed{
c_H(0.655)=
\frac{258509}{15720000\pi}
=0.00523447648648127\ldots.}
\tag{11}
\]
最终对每个 high cut \(U\subset\{q:M(q)\ge0.655\}\)，
\[
\boxed{
W(E_U\cap\{|x|\ge0.345\})
\ge c_H(0.655)|U|.}
\tag{12}
\]

## 5. 证据边界

- (12) 依赖已审计的 (TC) 及其 Borel-cut/first-birth 版本。
- 本文没有使用 endpoint multiplicity action、merge-tree rebate、continuity of selector 或虚拟 jump connectors。
- \(c_{\rm nar}\approx0.010469\) 不是 uniform all-\(M\) 常数；严格 dyadic physical-band 去重后的已证 uniform 常数是其一半 \(c_H\approx0.00523448\)。
