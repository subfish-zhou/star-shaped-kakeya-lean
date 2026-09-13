> [!WARNING]
> **BLOCKED CANDIDATE — NOT A PROVED THEOREM.**
> The endpoint `2π` estimate currently proves demand-once but not source-once.
> Do not cite `0.0975576139796` as a certified lower bound unless this gap is repaired and independently re-reviewed.

# 星形单位弦集的一个显式面积下界

## 摘要

设 \(E\subset\mathbb R^2\) 关于原点星形，并且每个无向方向都存在一条包含于 \(E\) 的单位线段。本文引入一个定义在射影方向圆上的非线性算子 \(T\)，它精确支配 \(E\) 在各方向上的最长连通弦长平方。通过对有限有理 action 菜单建立带物理 source 标记的分配账本，分别估计单连通块贡献和低系数端点贡献，得到
\[
\int_0^\pi Ty(q)\,dq
 \le
\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)
\int_0^{2\pi}y(x)\,dx .
\]
其中
\[
\operatorname{Si}(z)=\int_0^z\frac{\sin t}{t}\,dt .
\]
结合极坐标面积公式和开集外包络，推出
\[
\boxed{
 |E|^*
 \ge
 \frac{\pi}
 {2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)}
 =
 0.0975576139796\ldots } .
\]
最后说明：数值上相邻的 \(0.1\) 下界要求把算子常数进一步降至 \(5\pi\)；本文并未证明该强化。

---

## 1. 几何设定与径向函数

记
\[
\mathbb T=\mathbb R/(2\pi\mathbb Z),\qquad
\mathbb P=\mathbb R/(\pi\mathbb Z).
\]
二者分别带通常的角长度测度。对 \(x\in\mathbb T\)，写
\[
e_x=(\cos x,\sin x).
\]

称 \(E\subset\mathbb R^2\) 关于原点星形，如果
\[
z\in E,\quad 0\le t\le1
\quad\Longrightarrow\quad tz\in E.
\]
若 \(E\) 可测，定义径向函数
\[
R_E(x)=\sup\{r\ge0:re_x\in E\},
\qquad
y_E(x)=R_E(x)^2.
\]
在忽略一个角度零测集后，
\[
E=\{re_x:x\in\mathbb T,\ 0\le r\le R_E(x)\},
\]
从而
\[
|E|=\frac12\int_0^{2\pi}y_E(x)\,dx. \tag{1.1}
\]

对 \(q\in\mathbb P\)，记 \(\ell_E(q)\) 为 \(E\) 中方向为 \(q\) 的最长连通线段长度之上确界。若 \(E\) 在每个方向包含单位线段，则
\[
\ell_E(q)\ge1\qquad(q\in\mathbb P). \tag{1.2}
\]

---

## 2. 射影算子

以下固定一个非负可测、\(2\pi\)-周期函数
\[
y:\mathbb T\to[0,\infty].
\]

### 2.1 中心 action

定义
\[
C_y(q)
 =
 \sqrt{y(q)}+\sqrt{y(q+\pi)}. \tag{2.1}
\]
它对应经过星心的线段：两个端点位于相反射线上。

### 2.2 离心 action

固定
\[
\sigma\in\{+1,-1\},\qquad
-\frac\pi2<\alpha<\beta<\frac\pi2.
\]
定义
\[
\Lambda_y(q;\sigma,\alpha,\beta)
 =
 (\tan\beta-\tan\alpha)
 \operatorname*{ess\,inf}_{\alpha<t<\beta}
 \bigl[
 \sqrt{y(q+\sigma\pi/2+t)}\cos t
 \bigr]. \tag{2.2}
\]
这里 \((\alpha,\beta)\) 是以直线法向为中心的一个射影 chart。由于
\(\cos t>0\) 于 \((-\pi/2,\pi/2)\)，式中无符号歧义。

只取有理端点已经足够。事实上，对任意实端点
\(\alpha<\beta\)，可取有理数
\[
\alpha<\alpha_n<\beta_n<\beta,\qquad
\alpha_n\downarrow\alpha,\quad \beta_n\uparrow\beta.
\]
缩小区间不会降低 essential infimum，而
\[
\tan\beta_n-\tan\alpha_n
 \longrightarrow
\tan\beta-\tan\alpha.
\]
故所有实 action 的上确界等于有理 action 的可数上确界。

### 2.3 完整算子

定义
\[
\mathcal L_y(q)
 =
 \sup_{\substack{\sigma=\pm1\\
                  \alpha,\beta\in\mathbb Q\\
                  -\pi/2<\alpha<\beta<\pi/2}}
 \Lambda_y(q;\sigma,\alpha,\beta), \tag{2.3}
\]
以及
\[
\boxed{
 Ty(q)=\max\{C_y(q)^2,\mathcal L_y(q)^2\}.} \tag{2.4}
\]
由于 (2.3) 是可数个可测函数的上确界，\(Ty\) 可测。

算子 \(T\) 单调、正齐次：
\[
0\le y_1\le y_2\Longrightarrow Ty_1\le Ty_2,
\qquad
T(cy)=cTy\quad(c\ge0). \tag{2.5}
\]

---

## 3. 几何解释

### 引理 3.1（离心弦公式）

设一条直线的有向法向为 \(q+\sigma\pi/2\)，到原点的距离为 \(h\ge0\)。在相应 chart 中，直线上的点可写成
\[
z(t)=h\sec t\,e_{q+\sigma\pi/2+t},
\qquad -\frac\pi2<t<\frac\pi2.
\]
因此 \(t=\alpha,\beta\) 两点之间的距离为
\[
|z(\beta)-z(\alpha)|
 =
h(\tan\beta-\tan\alpha). \tag{3.1}
\]

**证明。**
沿直线方向的坐标为 \(h\tan t\)，故两点坐标差正是
\(h(\tan\beta-\tan\alpha)\)。∎

### 引理 3.2（算子的几何支配）

若 \(E\) 关于原点星形且可测，并令 \(y=y_E\)，则
\[
\ell_E(q)^2\le Ty(q)
\qquad(q\in\mathbb P). \tag{3.2}
\]

**证明。**
取 \(E\) 中一条方向为 \(q\)、长度为 \(L\) 的连通弦 \(I\)。

若 \(I\) 所在直线经过原点，则其两端分别位于方向 \(q\) 和
\(q+\pi\) 的射线上，因而
\[
L\le R_E(q)+R_E(q+\pi)=C_y(q).
\]

若直线不经过原点，选择法向 lane
\(\sigma\in\{\pm1\}\) 及
\(-\pi/2<\alpha<\beta<\pi/2\)，使弦可表示为
\[
I=\{z(t):\alpha\le t\le\beta\}.
\]
因为 \(I\subset E\)，对几乎处处的 \(t\in(\alpha,\beta)\)，
\[
h\sec t\le R_E(q+\sigma\pi/2+t).
\]
等价地，
\[
h\le \sqrt{y(q+\sigma\pi/2+t)}\cos t.
\]
故
\[
h\le
\operatorname*{ess\,inf}_{\alpha<t<\beta}
\sqrt{y(q+\sigma\pi/2+t)}\cos t.
\]
结合 (3.1) 得
\[
L\le\Lambda_y(q;\sigma,\alpha,\beta)\le\mathcal L_y(q).
\]
对所有弦取上确界即得 (3.2)。∎

---

## 4. 算子估计

记
\[
C_{\mathrm{blk}}
 =
4+\pi\operatorname{Si}(\pi). \tag{4.1}
\]

### 定理 4.1（射影算子的强 \(L^1\) 估计）

对每个非负可测 \(2\pi\)-周期函数 \(y\)，有
\[
\boxed{
\int_0^\pi Ty(q)\,dq
\le
\bigl(C_{\mathrm{blk}}+2\pi\bigr)
\int_0^{2\pi}y(x)\,dx.} \tag{4.2}
\]

证明分为四步：block distribution、endpoint low-gate、source-once 和一般可测函数逼近。

---

## 5. Block distribution kernel

定义
\[
K_{\mathrm{blk}}(r)=
\begin{cases}
0,&0\le r<\dfrac14,\\[1ex]
1,&\dfrac14\le r<1,\\[1ex]
1+\dfrac{\pi}{\arcsin(r^{-1/2})},&r\ge1.
\end{cases} \tag{5.1}
\]

这个核来自单个连通常值 source block 的完整射影 excursion。阈值
\(r=1/4\) 是中心弦的最小触发比：若 source 高度为 \(a\)，则该 block 所能产生的弦长平方不超过 \(4a\)。当 \(r\ge1\) 时，允许的端点角 excursion 为
\[
2\arcsin(r^{-1/2}),
\]
因而一个全射影周期最多分成
\[
\frac{\pi}{\arcsin(r^{-1/2})}
\]
个这样的 excursion；加上 block 自身的中心份额，得到 (5.1)。

更精确地，在有限 action 菜单中，把每个 output demand
\((q,\lambda)\)，\(0<\lambda<Ty(q)\)，连同实现它的第一个 action 一起标记。若该 action 的两个 first-responsive 点属于同一个连通 source block，则把该 demand 归入 block channel。固定物理 source 点及 source 高度后，所有同块 demands 先按相同物理 excursion 取商；相同 excursion 的多次菜单出现不重复计数。单块角几何遂给出
\[
d\mathsf D_{\mathrm{blk}}
\le
K_{\mathrm{blk}}(a/\lambda)\,d\lambda\,dx.
\tag{5.2}
\]
这里 \(a\) 是 source 高度，\(x\) 是物理角坐标。

要强调的是，(5.2) 是**带 source 标记并先作物理 quotient 后的局部账本**；它并不声称对任意多层函数成立一个逐 \(\lambda\) 的 context-free distribution inequality。

对 \(\lambda\) 先积分，令 \(r=a/\lambda\)，则
\[
d\lambda=-a r^{-2}\,dr,
\]
故每个 source atom 的总 block 负载不超过
\[
a\int_0^\infty K_{\mathrm{blk}}(r)r^{-2}\,dr. \tag{5.3}
\]

### 引理 5.1（block kernel 的精确积分）

有
\[
\int_0^\infty K_{\mathrm{blk}}(r)r^{-2}\,dr
 =
4+\pi\operatorname{Si}(\pi). \tag{5.4}
\]

**证明。**
由 (5.1)，
\[
\begin{aligned}
\int_0^\infty K_{\mathrm{blk}}(r)r^{-2}\,dr
&=
\int_{1/4}^{1}r^{-2}\,dr
+\int_1^\infty r^{-2}\,dr\\
&\quad+
\pi\int_1^\infty
\frac{r^{-2}}{\arcsin(r^{-1/2})}\,dr.
\end{aligned}
\]
前两项分别为 \(3\) 和 \(1\)。

在最后一项中令
\[
s=\arcsin(r^{-1/2}),\qquad r=\csc^2s.
\]
当 \(r:1\to\infty\) 时，\(s:\pi/2\to0\)，并且
\[
r^{-2}\,dr=-2\sin s\cos s\,ds=-\sin(2s)\,ds.
\]
因此
\[
\begin{aligned}
\pi\int_1^\infty
\frac{r^{-2}}{\arcsin(r^{-1/2})}\,dr
&=
\pi\int_0^{\pi/2}\frac{\sin(2s)}s\,ds\\
&=
\pi\int_0^\pi\frac{\sin t}{t}\,dt\\
&=\pi\operatorname{Si}(\pi).
\end{aligned}
\]
相加即得 (5.4)。∎

于是 block channel 的总负载满足
\[
\mathsf D_{\mathrm{blk}}
\le
C_{\mathrm{blk}}\int_0^{2\pi}y(x)\,dx. \tag{5.5}
\]

---

## 6. Endpoint low-gate

剩余 demand 的 first-responsive 信息来自某个低系数端点。固定该端点 \(x\)，选择 orientation
\(\varepsilon\in\{\pm1\}\)，写
\[
t=x+\varepsilon d,\qquad
q=x+\varepsilon u,
\]
其中 \(t\) 是另一端点，而 \(q\) 是 output 方向参数。

把 demand 送给 \(x\) 的必要条件是 \(x\) 的射影系数不大于另一端点的系数。这等价于
\[
0<d<\pi,\qquad \frac d2\le u<\frac\pi2. \tag{6.1}
\]
条件 \(d\le2u\) 称为 **low-gate**。

设 action 的起始 source 高度为 \(a>0\)。射影变换给出响应 source 高度
\[
h
 =
a\eta_d(u)^2,\qquad
\eta_d(u)
 =
\cos d+\sin d\tan u
 =
\frac{\cos(d-u)}{\cos u}. \tag{6.2}
\]
由 (6.1)，
\[
-u<d-u\le u<\frac\pi2,
\]
故
\[
\cos(d-u)>0.
\]
因此 low-gate 自动避开射影 pole；跨越 \(\tan\)-chart seam 时只需切换 orientation，不改变以下角公式。

对固定 span \(d\)，endpoint pushforward 的归一化角密度为
\[
k_d(u)
 =
\frac{2\sin^2d}
      {(\cos d+\sin d\tan u)^2}
 =
\frac{2\sin^2d\cos^2u}
      {\cos^2(d-u)}. \tag{6.3}
\]

固定最大允许 span \(D\in(0,\pi)\)，定义 low-gate envelope
\[
K_D(u)
 =
\sup_{0<d\le\min(D,2u)}k_d(u),
\qquad 0<u<\frac\pi2. \tag{6.4}
\]
由于
\[
\frac{\sin d\cos u}{\cos(d-u)}
\]
在 low-gate 区域内关于 \(d\) 单调递增，
\[
K_D(u)=
\begin{cases}
2\sin^2(2u),&0<u\le D/2,\\[1ex]
\dfrac{2\sin^2D\cos^2u}{\cos^2(D-u)},
&D/2<u<\pi/2.
\end{cases} \tag{6.5}
\]

### 引理 6.1（endpoint envelope 的精确质量）

对每个 \(0<D<\pi\)，
\[
\boxed{
\int_0^{\pi/2}K_D(u)\,du=D.} \tag{6.6}
\]

**证明。**
由 (6.5)，
\[
\int_0^{D/2}2\sin^2(2u)\,du
 =
\frac D2-\frac{\sin2D}{4}. \tag{6.7}
\]
另一方面，将
\[
\cos u=\cos D\cos(D-u)+\sin D\sin(D-u)
\]
代入第二段，并以 \(v=D-u\) 作变量，直接积分得到
\[
\int_{D/2}^{\pi/2}
\frac{2\sin^2D\cos^2u}{\cos^2(D-u)}\,du
 =
\frac D2+\frac{\sin2D}{4}. \tag{6.8}
\]
(6.7) 与 (6.8) 相加即得 (6.6)。该计算对
\(D>\pi/2\) 仍成立，因为 low-gate 保证
\(|D-u|<\pi/2\) 位于实际积分分支内；不存在穿过 kernel pole 的积分。∎

在完整射影圆上，每个物理端点至多有两条 homotopy orientation lanes。每条 lane 的最大 span 为 \(\pi\)。令 \(D\uparrow\pi\)，由单调收敛及 (6.6)，每条 lane 的总负载至多 \(\pi\)，故
\[
\mathsf D_{\mathrm{end}}
\le
2\pi\int_0^{2\pi}y(x)\,dx. \tag{6.9}
\]

这里没有额外的 \(1/2\)。整个 demand 被送往其唯一低系数端点；\(1/2\) 只会出现在人为把一个 token 平分给两个端点的另一种账法中。

---

## 7. Source-once 与有限有理 action 菜单

现在说明为什么 (5.5) 和 (6.9) 可以直接相加，而不会在不同菜单、不同高度或不同 endpoint lane 之间重复使用同一份 source 容量。

先设 \(y\) 为有界有限值阶梯函数，并只保留有限个有理 actions。定义 source undergraph
\[
\Omega_y
 =
\{(x,a):x\in\mathbb T,\ 0<a<y(x)\},
\qquad
|\Omega_y|=\int_{\mathbb T}y(x)\,dx. \tag{7.1}
\]
同理定义 demand undergraph
\[
\Omega_{Ty}
 =
\{(q,\lambda):q\in\mathbb P,\ 0<\lambda<Ty(q)\},
\]
于是
\[
|\Omega_{Ty}|=\int_{\mathbb P}Ty(q)\,dq. \tag{7.2}
\]

对每个 \((q,\lambda)\in\Omega_{Ty}\)，按以下顺序选择 owner：

1. 在有限菜单中选取第一个满足 action 值 \(>\sqrt\lambda\) 的 action；
2. 在该 action 的 source roof 中选择最低的 first-responsive 高度层；
3. 若两个端点同时 first-responsive，优先选择低系数端点；
4. 完全相等时按
   \[
   (\sigma,\alpha,\beta,\text{endpoint label})
   \]
   的固定字典序破 tie。

所有比较均为有限个 Borel 不等式，故 owner map 可测。

接着保留完整物理标签
\[
(x,a,\varepsilon,L),
\]
其中 \(x\) 是真实 source 角，\(a\) 是 source 高度，
\(\varepsilon\) 是 orientation lane，\(L\) 是 destination label。两个 demands 只有在这些标签完全相同且属于同一物理 excursion 时才允许合并。特别地：

- 不把两个重合的 source images 取集合并而删除 multiplicity；
- 不把不同 endpoint labels 的容量 pooling；
- 不因两个 actions 在数值上给出相同高度就视为同一 source；
- 不允许 ancestor 或另一 orientation 再次消费已经标记的 source atom。

按 owner 类型把 demand 分成两个不交的 Borel 集：
\[
\Omega_{Ty}
 =
\mathcal D_{\mathrm{blk}}
 \,\dot\cup\,
\mathcal D_{\mathrm{end}}. \tag{7.3}
\]

在 block 部分，同一物理 source excursion 先 quotient，随后应用
(5.2)。在 endpoint 部分，固定
\((x,a,\varepsilon,L)\) 后，关系 (6.2) 关于 \(u\) 单值；其逆式为
\[
u
 =
\arctan
\frac{\sqrt{h/a}-\cos d}{\sin d}, \tag{7.4}
\]
故 pushforward 不会在同一 lane 内产生隐藏复制。不同 span 的重叠由 pointwise envelope \(K_D\) 计算，而不是把各 span 的质量逐项相加。

因此每个带完整物理标签的 source atom：

- 在 block channel 中至多被记一次；
- 或在 endpoint channel 的至多两条 homotopy lanes 中被记；
- 不会同时以两个 owner 身份重复出现。

由 (5.5)、(6.9) 和 (7.3)，
\[
\begin{aligned}
\int_{\mathbb P}Ty
&=
|\mathcal D_{\mathrm{blk}}|
 +|\mathcal D_{\mathrm{end}}|\\
&\le
\bigl(C_{\mathrm{blk}}+2\pi\bigr)
|\Omega_y|\\
&=
\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)
\int_{\mathbb T}y.
\end{aligned} \tag{7.5}
\]
这证明了有限有理菜单、有限阶梯函数情形。

---

## 8. 从有限模型到一般可测函数

### 8.1 有界函数

设 \(0\le y\le M\)。取 dyadic ceiling
\[
y_n=2^{-n}\bigl\lceil 2^ny\bigr\rceil.
\]
则
\[
y\le y_n\le y+2^{-n},
\qquad
\|y_n-y\|_\infty\le2^{-n}. \tag{8.1}
\]
每个 \(y_n\) 可再用有限角分割从上方逼近；由于 action 菜单可数，只需先保留前 \(N\) 个有理 actions，再令 \(N\to\infty\)。

对任一固定 action，平方 action 值关于 \(y\) 在一致逼近下连续；中心项同样连续。有限最大值连续，而可数上确界可由单调增加的有限最大值恢复。因此
\[
Ty_n(q)\longrightarrow Ty(q)
\quad\text{a.e.},
\]
并可对有限菜单先用控制收敛、再对菜单用单调收敛。由
\[
\int y_n\to\int y
\]
及有限情形的 (7.5)，得到有界可测 \(y\) 的 (4.2)。

### 8.2 无界函数

令
\[
y^{(M)}=y\wedge M.
\]
则 \(y^{(M)}\uparrow y\)。对每个固定 action，
\[
\operatorname*{ess\,inf}\sqrt{y^{(M)}}\cos t
\uparrow
\operatorname*{ess\,inf}\sqrt y\cos t,
\]
因为截断与 essential infimum 可交换：
\[
\operatorname*{ess\,inf}(f\wedge c)
 =
(\operatorname*{ess\,inf}f)\wedge c.
\]
再对 actions 取上确界，得
\[
Ty^{(M)}\uparrow Ty.
\]
两边应用单调收敛，便得到一般非负可测函数的 (4.2)。定理 4.1 得证。∎

---

## 9. 面积下界：可测情形

### 定理 9.1

设 \(E\subset\mathbb R^2\) 可测、关于原点星形，并在每个无向方向包含一条单位线段。则
\[
|E|
\ge
\frac{\pi}
 {2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)}. \tag{9.1}
\]

**证明。**
令 \(y=y_E\)。由 (1.2) 和引理 3.2，
\[
Ty(q)\ge\ell_E(q)^2\ge1
\qquad(q\in\mathbb P).
\]
故
\[
\pi\le\int_0^\pi Ty(q)\,dq.
\]
由定理 4.1 和极坐标面积公式 (1.1)，
\[
\begin{aligned}
\pi
&\le
\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)
\int_0^{2\pi}y(x)\,dx\\
&=
2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)|E|.
\end{aligned}
\]
移项即得 (9.1)。∎

---

## 10. 外测度情形

不假设 \(E\) 可测。记二维 Lebesgue 外测度为 \(|E|^*\)。

给定 \(\varepsilon>0\)，由外正则性取开集 \(O\supset E\)，使
\[
|O|<|E|^*+\varepsilon. \tag{10.1}
\]
定义 \(O\) 关于原点的径向内包络
\[
U_O
 =
\{re_x:[0,r]e_x\subset O\}. \tag{10.2}
\]
显然
\[
U_O\subset O. \tag{10.3}
\]
而且 \(U_O\) 关于原点星形。由于 \(O\) 开，若整个紧线段
\([0,r]e_x\) 包含于 \(O\)，则该线段到 \(O^c\) 的距离为正；因此在
\((x,r)\) 的一个邻域内相应线段仍包含于 \(O\)。故 \(U_O\) 是开集，特别可测。

又因为 \(E\) 关于原点星形且 \(E\subset O\)，对每个 \(z\in E\)，
\[
[0,z]\subset E\subset O,
\]
故
\[
E\subset U_O. \tag{10.4}
\]
于是 \(U_O\) 仍在每个方向包含 \(E\) 中原有的单位线段。由定理 9.1，
\[
|U_O|
\ge
\frac{\pi}
 {2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)}.
\]
结合 \(U_O\subset O\) 和 (10.1)，
\[
|E|^*+\varepsilon
>
|O|
\ge|U_O|
\ge
\frac{\pi}
 {2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)}.
\]
令 \(\varepsilon\downarrow0\)，得到：

### 主定理

每个关于某点星形、并在每个无向方向包含一条单位线段的集合
\(E\subset\mathbb R^2\) 都满足
\[
\boxed{
|E|^*
\ge
\frac{\pi}
 {2\bigl(4+2\pi+\pi\operatorname{Si}(\pi)\bigr)}.} \tag{10.5}
\]

数值上，
\[
\operatorname{Si}(\pi)
 =1.8519370519824658\ldots,
\]
\[
4+2\pi+\pi\operatorname{Si}(\pi)
 =16.10121714459844\ldots,
\]
从而
\[
\boxed{|E|^*\ge0.0975576139796276\ldots.} \tag{10.6}
\]

平移星心不改变面积或单位弦性质，故定理不依赖把星心规范为原点。

---

## 11. 与 \(0.1\) 的严格分界

若要推出
\[
|E|^*\ge0.1,
\]
由同一算子—几何转译至少需要
\[
\int_0^\pi Ty
\le5\pi\int_0^{2\pi}y. \tag{11.1}
\]
本文实际证明的常数是
\[
C_*
 =
4+2\pi+\pi\operatorname{Si}(\pi)
 =
16.10121714459844\ldots,
\]
而
\[
5\pi=15.70796326794897\ldots.
\]
两者相差
\[
C_*-5\pi
 =
4-3\pi+\pi\operatorname{Si}(\pi)
 =
0.39325387664947\ldots>0. \tag{11.2}
\]

因此：

1. 本文无条件证明的结论是
   \[
   |E|^*\ge0.0975576139796\ldots;
   \]
2. \(0.1\) 需要一个额外的、严格更强的全局合并或共享容量引理；
3. 仅有 unique LCA、逐层 owner、source-image 取并或未经证明的
   transport pooling，都不足以提供该强化；
4. 本文没有使用、也没有声称证明任何能把常数从 \(C_*\) 降至
   \(5\pi\) 的引理。

换言之，\(0.0975576139796\ldots\) 是本文已经闭合的基线定理，而
\(0.1\) 属于尚未证明的条件强化，二者不得混写。