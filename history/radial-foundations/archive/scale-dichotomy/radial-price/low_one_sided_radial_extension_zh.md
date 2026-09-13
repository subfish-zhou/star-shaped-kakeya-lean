# Low class 的单侧全径向扩张：从 \(1-M_0\) 延伸到 \(M_0\)

## 0. 结论与口径

设 \(1/2<M_0<1\)、\(|h_q|\le H\)，且 low cut \(U\subset\mathbb {RP}^1\) 上每条单位弦满足
\[
M_q:=\max\{|A_q|,|B_q|\}\le M_0.
\]
写 \(m=1-M_0\)，并令 \(E_U=\bigcup_{q\in U}\operatorname{conv}(0,A_q,B_q)\)。以下构造在每个外层只选**较远 endpoint 的一个真实 component**，不再要求两侧 endpoint 同时到达该层。

对 \(m\le r<M_0\)、\(r<t\le M_0\)，定义 survival cut
\[
U_t:=\{q\in U:M_q\ge t\}.
\]
若 \(r\ge H\)，则有 literal-union circle kernel
\[
\boxed{
 m_{\mathbb S^1}\!\left(\bigcup_{q\in U}\mathcal A_q(r)\right)
 \ge
 \sup_{t\in(r,M_0]} {t-r\over t+r}\,|U_t| .
}
\tag{K}
\]
这里 \(\mathcal A_q(r)=\{\phi:r e^{i\phi}\in T_q\}\)。右端是 endpoint-radius survival function 的物理 coverage kernel；不是 multiplicity action，也没有给不同 \(t\) 重复收费。为保证可测性，sup 可只取有理 \(t\)，与全 sup 相同。

特别地，每条单位弦都有 \(M_q\ge1/2\)。因此当
\(m\le r<1/2\) 且 \(r\ge H\) 时，取 \(t=1/2\) 得到分布无关的层界
\[
\boxed{
 m_{\mathbb S^1}\!\left(\bigcup_{q\in U}\mathcal A_q(r)\right)
 \ge {\frac12-r\over\frac12+r}|U| .
}
\tag{U}
\]
这只使用固定 subband \([m,1/2)\)，因此不会消费整个 outer band \([m,M_0)\)：\([1/2,M_0)\) 仍未被这个 uniform receipt 占用。

---

## 1. 单侧 component 的精确角公式

固定 \(q\)，选一个较远 endpoint \(P_q\)，令 \(|P_q|=M_q\)。若两端等距，用固定 Borel tie rule。把该端的纵向坐标记为 \(x_q>0\)，则
\[
M_q^2=x_q^2+h_q^2.
\]
当 \(|h_q|\le r<M_q\) 时，半径 \(r\) 上靠近 \(P_q\) 的真实 component 为 \(J_q(r)\)。记
\[
a_q(r)=\arcsin {|h_q|\over r},
\qquad
b_q=\arctan {|h_q|\over x_q}
      =\arcsin {|h_q|\over M_q}.
\]
则
\[
|J_q(r)|=a_q(r)-b_q.
\]
把它向对应的 projective ideal anchor 扩张，得到 \(K_q(r)\)，且
\[
|K_q(r)|=a_q(r).
\]
函数 \(z\mapsto \arcsin z/z\) 在 \((0,1]\) 上递增，所以
\[
{b_q\over a_q(r)}
={\arcsin(|h_q|/M_q)\over\arcsin(|h_q|/r)}
\le {r\over M_q}.
\tag{1}
\]
若 \(M_q\ge t>r\)，则
\[
{|K_q(r)|\over|J_q(r)|}
\le {t\over t-r}=:\Lambda(r,t).
\tag{2}
\]
当 \(h_q=0\) 时，真实 fibre 就是 anchor radial ray；把它作为 \(J=K\) 的 singleton pole branch，不能用 essential-supremum 删除。
**切触边界。** 当 \(|h_q|=r\) 时，\(S_r\) 与 base chord 在法足相切；两侧 layer components 在该切点相接。所选 far component 仍是从 endpoint ray 到切点的闭弧，长度为 \(\arcsin(1)-b_q\)，所以 (1)--(2) 按字面成立。于是 low branch 取 \(|h_q|\le r\)，第 3 节 supplemental branch 取 \(|h_q|>r\)，两者穷尽且不重叠。


注意 (1) 直接使用 endpoint 半径 \(M_q\)，而不是较弱的纵向下界 \(x_q\)。因此即使 \(r>x_q\)，只要 \(r<M_q\)，公式仍有效。这正是扩张可一直写到 \(r<M_0\) 的关键。

---

## 2. 从 interval expansion 到物理 union

只对 \(U_t\) 的每个方向保留上述一个 component。所选 anchors 在 \(\mathbb S^1\) 上形成 \(U_t\) 的一个 Borel lift；圆到射影圆的投影在该 lift 上保弧长，故 anchor 集质量为 \(|U_t|\)。

使用 circle open-patch expansion lemma
\[
m^*(\cup K_i)\le(2\Lambda-1)m^*(\cup J_i)
\]
和 (2)，得到
\[
\left|\bigcup_{q\in U_t}J_q(r)\right|
\ge {1\over2\Lambda(r,t)-1}|U_t|
={t-r\over t+r}|U_t|.
\]
而 \(\cup_{q\in U_t}J_q(r)\subset\cup_{q\in U}\mathcal A_q(r)\)，故对 \(t\) 取 supremum 即得 (K)。整个证明只看底 intervals 的集合并；不同方向、不同 \(M_q\) 的 components 即使完全 collision 也只算一次。

这也是一个可截断的 **\(M\)-dependent collar**：在层 \(r\) 只启用满足 \(M_q-r\ge t-r\) 的 endpoints。参数 \(t-r\) 是所需 collar clearance；改变 \(t=t(r)\) 只改变 active survival cut，不建立额外 source copy。

---

## 3. \(r<H\) 时的补充分支

若需要处理 \(m<H\) 的一般参数，则在 \(|h_q|>r\) 时 fibre 是连接两 endpoint rays 的一个完整 interval。令
\[
\alpha_0=2\arcsin {1\over2M_0},
\qquad
k_H(t)={\alpha_0\over\alpha_0+2\arcsin(H/t)}
\quad(t>H).
\]
该 interval 长度至少 \(\alpha_0\)，较远 endpoint 的 ideal anchor 到其 endpoint ray 的距离至多 \(\arcsin(H/t)\)。与低-offset branch 合并后可用
\[
\boxed{
 k(r,t)=\min\left\{{t-r\over t+r},\,k_H(t)\right\}
}
\tag{3}
\]
替代 (K) 中的 \((t-r)/(t+r)\)。在当前 \(M_0=.655,H=.2\) 窗口，\(m=.345>H\)，所以整个新增 subband 都走 (K)，不需要 (3) 的损失。

---

## 4. 新的 uniform low 常数

把已有双侧 all-radial receipt 保留在 \(0<r<m\)，再把 (U) 用在
\([m,1/2)\)。两段 radial atoms 半开且物理不交，故可以直接相加：
\[
\boxed{
 C_L^{\rm one}(M_0,H)
 =C_L^{\rm old}(M_0,H)+D(M_0),
}
\tag{4}
\]
其中（当前假设 \(H\le m\)）
\[
D(M_0)=\int_m^{1/2}r{\frac12-r\over\frac12+r}\,dr.
\tag{5}
\]
令
\[
Q_a(r)=-{r^2\over2}+2ar-2a^2\log(a+r),
\]
则
\[
\boxed{D(M_0)=Q_{1/2}(1/2)-Q_{1/2}(1-M_0).}
\tag{6}
\]

在 \(M_0=.655,H=.2\) 时：
\[
D=0.005303174187518356,
\]
\[
\boxed{C_L^{\rm one}=0.03164670355100802.}
\]
相对旧值 \(0.026343529363489666\) 提高约 \(20.13\%\)，all-low 面积常数为
\[
\pi C_L^{\rm one}=0.09942105138618082.
\]
它仍比 \(0.1/\pi=0.0318309886183791\) 少
\(1.84285067371\times10^{-4}\)（约 \(0.579\%\)），所以不能把该机制表述成已经达到 \(0.1\)。

更精细、依赖 endpoint-radius 分布的版本是不丢弃 \(r>1/2\)，而直接积分 (K)：
\[
|E_U\cap\{m\le|x|<M_0\}|
\ge
\int_m^{M_0}r\,
\sup_{t\in(r,M_0]}{t-r\over t+r}|U_t|\,dr.
\tag{7}
\]
(7) 是所求的 full \([1-M_0,M_0]\) literal-union coverage kernel；(5) 只是它对任意 low cut 的分布无关 corollary。

---

## 5. source-once 与可组合性边界

1. (7) 在每个固定 \(r\) 只选择一个 threshold \(t\)；sup 是选择最佳 receipt，不是把所有 thresholds 相加。
2. uniform 改进 (5) 只占用 \([m,1/2)\)，明确留下 \([1/2,M_0)\)；因此不需要预先把整个 outer band 划给 low。
3. 若另一个 high theorem 也使用 \([m,1/2)\)，仍不能直接相加。合法 joint theorem 必须对共同 half-open radial atoms 指定唯一 owner，或证明共同 load \(\le1\)。“留下部分 band”降低冲突，但不会自动证明 low/high additivity。
4. 对 \(r>1/2\)，(7) 只有在 survival cut \(U_t\) 有质量时才付款；不存在正的分布无关层常数，因为合法 low family 可以全部满足 \(M_q=1/2\)。
5. 所有结论针对 Borel selector/cut；任意不可测 selector 仍需独立的 measurable-selection/open-envelope adapter。