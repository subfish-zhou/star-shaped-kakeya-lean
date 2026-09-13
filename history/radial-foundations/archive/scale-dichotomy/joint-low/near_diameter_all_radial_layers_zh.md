# Near-diameter：积分全部 radial layers 的 circle-interval union bound

## 1. 设置与结论

令
\[
\frac12\le M<1,\qquad 0\le H,
\qquad m:=1-M>0.
\]
对每个 \(q\in U\subset\mathbb {RP}^1\)，Borel 地选一条单位弦
\[
[A_q,B_q],\qquad
A_q=(s_q-\tfrac12)u_q+h_qn_q,
\quad B_q=(s_q+\tfrac12)u_q+h_qn_q,
\]
满足
\[
\max(|A_q|,|B_q|)\le M,
\qquad |h_q|\le H.
\tag{1}
\]
记
\[
T_q=\operatorname{conv}(0,A_q,B_q),
\qquad E_U=\bigcup_{q\in U}T_q,
\]
以及半径 \(r\) 的 triangle angular fibre
\[
\mathcal A_q(r):=\{\phi\in\mathbb S^1:r u_\phi\in T_q\}.
\]

定义
\[
\alpha_M:=2\arcsin\frac1{2M},
\qquad B_{M,H}:=\arctan\frac{H}{m},
\]
\[
\Lambda_L(r):=\frac{m}{m-r},
\qquad
\Lambda_H:=1+\frac{B_{M,H}}{\alpha_M}
\qquad(0<r<m),
\]
并置
\[
\Lambda(r;M,H)=
\begin{cases}
\max\{\Lambda_L(r),\Lambda_H\},&0<r<H,\\
\Lambda_L(r),&H\le r<m,
\end{cases}
\tag{2}
\]
（当 \(H\ge m\) 时第二支为空）。令
\[
\boxed{
 g(r;M,H):=\frac{2}{2\Lambda(r;M,H)-1}
}
\qquad(0<r<m).
\tag{3}
\]

则每个 Borel cut \(U\) 和每个 \(0<r<m\) 都满足
\[
\boxed{
\left|\bigcup_{q\in U}\mathcal A_q(r)\right|
\ge g(r;M,H)|U|.
}
\tag{4}
\]
这里左边取 \(\mathbb S^1\) 弧长，右边取 \(\mathbb {RP}^1\) 弧长。特别地，若 \(r\ge H\)，每个 fibre 是两条 endpoint components（允许在 \(|h_q|=r\) 相接），且
\[
\boxed{
 g(r;M,H)=2\frac{m-r}{m+r}.
}
\tag{5}
\]

对全部 \(0<r<m\) 积分，polar Cavalieri 给出
\[
\boxed{
 |E_U|\ge C(M,H)|U|,
\qquad C(M,H):=\int_0^m r\,g(r;M,H)\,dr.
}
\tag{6}
\]
又因每个 endpoint 均在 \(B_M\)、\(M<1\)，故
\(E_U\subset B_M\)；在这里 inverse-radius 权重恒等于 \(1\)，所以
\[
\boxed{W(E_U)=|E_U|\ge C(M,H)|U|.}
\tag{6'}
\]
这不是挑一个最佳圆层，而是使用所有可统一保证的 radial layers。

## 2. 每个 endpoint 至少到达半径 \(m\)

写
\[
p_q=s_q+\frac12,
\qquad n_q=\frac12-s_q,
\qquad p_q+n_q=1.
\]
由 (1)，
\[
p_q,n_q\le\sqrt{M^2-h_q^2}\le M,
\]
所以
\[
p_q,n_q\ge1-\sqrt{M^2-h_q^2}\ge1-M=m.
\tag{7}
\]
因此两个 endpoint 的半径都至少为 \(m\)，故对每个 \(0<r<m\) 两端都能到达第 \(r\) 层。

## 3. 低 offset：两条真实 components

固定 \(q\)，先设 \(|h_q|<r\)。令
\[
a_q(r):=\arcsin\frac{|h_q|}{r},
\]
而正、负 endpoint 的角漂移分别为
\[
b_q^+:=\arctan\frac{|h_q|}{p_q},
\qquad
b_q^-:=\arctan\frac{|h_q|}{n_q}.
\]
由 (7) 及 \(r<m\)，有 \(a_q(r)>b_q^\pm\)。于是
\(\mathcal A_q(r)\) 恰有两条闭 components \(J_q^+(r),J_q^-(r)\)，长度分别是
\[
|J_q^\pm(r)|=a_q(r)-b_q^\pm.
\tag{8}
\]
它们位于两个 endpoint rays 与圆 \(S_r\) 的交点 rays 之间。

把 \(J_q^+\) 朝 ideal anchor \(q\) 扩成 \(K_q^+\)，把 \(J_q^-\) 朝 antipodal anchor \(q+\pi\) 扩成 \(K_q^-\)。则
\[
q\in K_q^+,
\qquad q+\pi\in K_q^-,
\qquad |K_q^\pm|=a_q(r).
\]
并且
\[
\frac{b_q^\pm}{a_q(r)}
\le
\frac{|h_q|/(p_q\text{ or }n_q)}{|h_q|/r}
\le\frac r m.
\]
因此
\[
|K_q^\pm|
\le \frac1{1-r/m}|J_q^\pm|
=\Lambda_L(r)|J_q^\pm|.
\tag{9}
\]
当 \(h_q=0\) 时，两 components 是 \(\{q\}\) 与 \(\{q+\pi\}\)，并令 \(K=J\)；没有丢掉 radial/pole fibres。当 \(|h_q|=r\) 时两闭 components 在切点相接，同一估计仍由极限成立。

## 4. 高 offset：同一真实 interval 的双向 expansion

若 \(|h_q|>r\)，整条 chord base 到原点的距离大于 \(r\)，故 \(\mathcal A_q(r)\) 是连接两个 endpoint rays 的完整闭 interval，记为 \(J_q\)。其长度是两个 endpoint vectors 的夹角。因为两 endpoint 半径不超过 \(M<1\)，余弦定律（夹角余弦分别对两个 endpoint 半径单调增加）给出
\[
|J_q|\ge\alpha_M=2\arcsin\frac1{2M}.
\tag{10}
\]
两个 ideal anchors \(q,q+\pi\) 到 \(J_q\) 两端的距离分别为 \(b_q^+,b_q^-\)，且
\[
b_q^\pm\le B_{M,H}:=\arctan(H/m).
\tag{11}
\]

此时把同一个物理 interval \(J_q\) 作为两张**重合 receipt**：一张向一端扩到 \(q\)，另一张向另一端扩到 \(q+\pi\)。这不重复计算物理 union；在下面的 union lemma 中，两张 receipt 的底集仍是同一个 \(J_q\)。由 (10)--(11)，每张 expansion 都满足
\[
|K_q^\pm|
\le\left(1+\frac{B_{M,H}}{\alpha_M}\right)|J_q|
=\Lambda_H|J_q|.
\tag{12}
\]
若 \(r\ge H\)，高-offset 类为空，这正是 (2) 第二支可删除 \(\Lambda_H\) 的原因。

## 5. Circle interval union expansion：open-patch / outer measure 版本

使用如下不要求参数连续性的引理。

> **引理。** 设 \(\{J_i\}\) 是圆周上的任意 interval 族（允许单点及重复），每个 \(K_i\) 从 \(J_i\) 向一端扩张，且
> \[
> |K_i|\le\Lambda |J_i|,\qquad \Lambda\ge1.
> \]
> 则
> \[
> m^*\!\left(\bigcup_iK_i\right)
> \le(2\Lambda-1)m^*\!\left(\bigcup_iJ_i\right).
> \tag{13}
> \]

**Open-patch 证明。** 取任意开集 \(O\supset\bigcup_iJ_i\)，把 \(O\) 分成可数个圆 interval components \(C\)。每个 \(J_i\) 落在唯一一个 \(C\) 中。若 \(|C|=L\)，属于它的每个 \(K_i\) 最多向左或向右伸出
\((\Lambda-1)|J_i|\le(\Lambda-1)L\)。故这些 \(K_i\) 的 union 落在 \(C\) 的双侧 enlargement 中，长度至多
\((2\Lambda-1)L\)（绕满圆时取与 \(2\pi\) 的最小值，仍不超过此前者）。对 components 求和，再对所有开外包 \(O\) 取下确界，即得 (13)。这一步没有使用 union 可测性，也没有使用 \(q\mapsto(A_q,B_q)\) 的连续性。

现在把第 3--4 节的全部 receipts 一起放入 (13)，取
\(\Lambda=\Lambda(r;M,H)\)。底 interval 的物理 union 包含于
\(\bigcup_q\mathcal A_q(r)\)；所有 expanded intervals 的 union 则包含 \(U\) 的一个半圆 lift 及其 antipodal copy。用两个可测半圆作 Carathéodory splitting（cut endpoints 是零测集），
\[
m^*\!\left(\widetilde U\cup(\widetilde U+\pi)\right)=2|U|.
\tag{14}
\]
所以
\[
2|U|
\le m^*\!\left(\bigcup K_i\right)
\le(2\Lambda-1)m^*\!\left(\bigcup J_i\right)
\le(2\Lambda-1)
 \left|\bigcup_{q\in U}\mathcal A_q(r)\right|,
\]
这正是 (4)。任意 Borel jumps、component reorder 和 endpoint-angle seam 都已包含在这个 outer-measure 论证中。

## 6. 显式积分

置
\[
c_H:=\frac{2\alpha_M}{\alpha_M+2B_{M,H}},
\qquad
r_0:=\frac{mB_{M,H}}{\alpha_M+B_{M,H}},
\qquad
a:=\min\{H,r_0\}.
\tag{15}
\]
\(r_0\) 是 \(\Lambda_L(r)=\Lambda_H\) 的交点。于是
\[
g(r;M,H)=
\begin{cases}
c_H,&0<r<a,\\
2(m-r)/(m+r),&a<r<m,
\end{cases}
\quad\text{a.e.}
\tag{16}
\]
注意若 \(H<r_0\)，在 \(r=H\) 处允许向上跳到 low-offset 公式；这不影响积分。

定义
\[
P_m(t):=-t^2+4mt-4m^2\log\left(1+\frac tm\right).
\]
由于
\[
P_m'(t)=2t\frac{m-t}{m+t},
\]
(6) 化为
\[
\boxed{
C(M,H)=\frac{c_Ha^2}{2}+P_m(m)-P_m(a),
\qquad
P_m(m)=m^2(3-4\log2).
}
\tag{17}
\]

对当前窗口
\[
M=0.655,\qquad H=0.2,
\]
有
\[
\alpha_M=1.7369936249043876,\quad
B_{M,H}=0.5253668738153163,
\]
\[
r_0=0.08011613161070329,
\qquad c_H=1.2461718043288088,
\]
最终
\[
\boxed{C(0.655,0.2)=0.026343529363489666.}
\tag{18}
\]
因此它严格超过旧界对应的精确 per-radian 门槛
\[
0.0224551315363533,
\]
余量为 \(0.0038883978271364\)，约 \(17.32\%\)。另一方面
\[
C(0.655,0.2)<0.1/\pi=0.0318309886183791,
\]
所以本构造已经足够 source-disjoint 超旧界，但尚未达到较强的 \(0.1/\pi\) 愿望值。

## 7. 可测性与诚实范围

- 对 Borel \(U\) 和 Borel chord selector，\(E_U\) 是 Borel 参数空间与紧 barycentric simplex 在 Borel 映射下的 analytic image，故 Lebesgue 可测；polar Tonelli/Cavalieri 可直接用于 (6)。
- 层上 interval union 即使只先知道为投影，也可始终保留 \(m^*\)；第 5 节的 open-patch 证明不需要 selector 连续、有限分片或有限 jump 数。
- 本定理估计 literal physical union。高-offset 情形把同一底 interval 写两次只用于证明 expanded union 覆盖两个 anchors；(13) 的右端仍是底 interval 的集合 union，未把重合容量算两次。
- 这里证明的是 near-diameter 子类自身的 all-cut 面积下界。若要与另一 schedule 相加，仍须另证两者使用的物理 radial/spatial capacity 不重叠；不能仅凭常数相加。