### 结论

在现有 terminal-collar all-cut 引理下，连续 collar-depth 的最优 source-once 常数是

\[
\boxed{c_{\rm multi}(R)=\frac1{48\pi R}}.
\]

它相对单 collar 常数

\[
c_{\rm single}(R)=\frac1{108\pi R}
\]

只提高

\[
\frac{c_{\rm multi}}{c_{\rm single}}=\frac94,
\]

而不是目标的 \(15\) 倍。目标值 \(15/(108\pi R)=5/(36\pi R)\) 比该连续-collar上限还大 \(20/3\) 倍；因此仅靠这些 nested terminal sectors，无法得到十五倍改进。

---

### 推导

令 \(F_q\) 为较远端点，沿单位弦向内的深度为 \(s\)，并定义

\[
P_t(U)=
\bigcup_{q\in U}
\arg\{F_q-su_q:0\le s\le t\},
\qquad 0\le t\le \frac12.
\]

则 \(P_s(U)\subset P_t(U)\)。已有 angular collar 引理写成

\[
|P_t(U)|\ge \frac{t}{\pi R}|U|.
\tag{1}
\]

由于 \(|F_q|\ge1/2\)，深度不超过 \(t\) 的点半径至少为 \(1/2-t\)。故

\[
\{re^{i\theta}: \theta\in P_t(U),\ 0\le r\le \tfrac12-t\}
\subset E_U.
\tag{2}
\]

在半径不超过 \(1/2\) 的区域，inverse-radius 权重 \(W\) 就是普通面积。一个在深度 \(t\) 首次出现的角度所能获得的完整 source-once 容量为

\[
K(t)=\int_0^{1/2-t}r\,dr
=\frac12\left(\frac12-t\right)^2.
\tag{3}
\]

定义首次出现时间

\[
\tau(\theta)=\inf\{t:\theta\in P_t(U)\},
\]

以及分布函数

\[
m(t)=|\{\theta:\tau(\theta)\le t\}|=|P_t(U)|.
\]

只对首次出现的角度收费，得到严格的 source-once 收据

\[
W(E_U)\ge \int K(\tau(\theta))\,d\theta
=\int_{[0,1/2]}K(t)\,dm(t).
\tag{4}
\]

这里没有重复收费：每个角度只属于一个 birth layer；同一角度在更大的 \(t\) 中反复出现不产生新义务。由 Stieltjes 分部积分、\(K(1/2)=0\) 及 (1)，

\[
\begin{aligned}
\int K\,dm
&=-\int_0^{1/2}m(t)\,dK(t)\\
&\ge
\frac{|U|}{\pi R}
\left(-\int_0^{1/2}t\,dK(t)\right)\\
&=
\frac{|U|}{\pi R}
\int_0^{1/2}K(t)\,dt\\
&=
\frac{|U|}{\pi R}
\int_0^{1/2}
\frac12\left(\frac12-t\right)^2dt\\
&=\frac{|U|}{48\pi R}.
\end{aligned}
\]

因此

\[
\boxed{W(E_U)\ge \frac{|U|}{48\pi R}}
\qquad\text{对所有 measurable cuts }U.
\]

---

### 与单 collar 的核对

固定一个深度 \(t\) 只给出

\[
W(E_U)\ge
\frac{|U|}{\pi R}\,
tK(t)
=
\frac{|U|}{2\pi R}\,
t\left(\frac12-t\right)^2.
\]

该表达式在 \(t=1/6\) 取最大值：

\[
tK(t)=
\frac16\cdot\frac12\left(\frac13\right)^2
=\frac1{108},
\]

正好恢复已有的 \(1/(108\pi R)\)。

---

### nested sectors 的严格去重与最优性

不能把每个 \(P_t\) 的完整 sector 都相加；因为 \(P_s\subset P_t\)，同一物理 radial fibre 会被连续多个 \(t\) 重复收费。正确做法是：

- 只收费增量 \(dP_t\)，即首次在深度 \(t\) 出现的角度；
- 给该增量一次性分配 kernel \(K(t)\)；
- 后续更深 collar 对相同角度收费为零。

而且，仅从 (1)–(2) 出发，常数 \(1/48\) 已是最优的。抽象极端情形可取嵌套角区间满足

\[
|P_t|=\frac{|U|}{\pi R}t.
\]

其 birth density 恰为 \(|U|/(\pi R)\)，对应 sector union 的 \(W\)-质量正好是

\[
\frac{|U|}{\pi R}\int_0^{1/2}K(t)\,dt
=\frac{|U|}{48\pi R}.
\]

因此，更大的常数必须使用额外几何输入，例如 antipodal rigidity、非终端 radial occupancy，或独立于这些 nested sectors 的 source-resolved reserve；单纯“连续化 collar depth”不能实现十五倍目标。

- **文件修改：** 无。
- **问题：** 目标十五倍与现有 collar 信息不相容；得到的是严格的 \(9/4\) 倍改进及该方法的上限。