# Contact/ridge candidates：合法 selector、保留结论与撤销项

## 0. 设置：先区分三种 contact

对每个 \(\theta\in\mathbb T_p=\mathbb R/\pi\mathbb Z\) 恰选一条完整单位弦 \(N_\theta\)，令 source reach

\[
q_\phi(\theta)=\max\bigl(\{r>0:re^{i\phi}\in N_\theta\}\cup\{0\}\bigr),
\qquad \rho(\phi)=\sup_{\theta\in\mathbb T_p}q_\phi(\theta).
\]

单条闭弦使 \(q_\phi(\theta)\) 的最大值 attained，但跨 source 的 \(\rho\) 未必 attained。必须分别定义：

- exact top set \(T_\phi=\{\theta:q_\phi(\theta)=\rho(\phi)>0\}\)；它可以为空；
- \(\tau\)-near set \(T_{\phi,\tau}=\{\theta:q_\phi(\theta)>\rho(\phi)-\tau\}\)；
- supremum-only 情形：\(T_\phi=\varnothing\)，但存在趋近 \(\rho\) 的 source 序列。

因此只有在 \(T_\phi\) 非空时才能谈“选一个 exact winner”。若 `top-two gap` 是用 source suprema 定义，连续 source 邻域常使 second supremum 等于 first，即使 exact top 唯一或不存在；它不是自动的离散 order statistic。

任意 selector 的这些集合还可能不可测。下面只对显式可测 selector 作解析计算；任何 universal 积分仍需 outer-measure/finite-schedule bridge。

## 1. 旧命题为何非法

旧族 \(h n_\theta+[-1/2,1/2]e_\theta\) 满足

\[
h n_{\theta+\pi}+[-1/2,1/2]e_{\theta+\pi}
=-h n_\theta+[-1/2,1/2]e_\theta,
\]

通常不是原弦。故它在同一 \([\theta]\in\mathbb T_p\) 上给两条弦。旧“命题 M”、圆盘等式、two-source top、`1/32` 和由它宣称的 (G)/(D) no-go 均不适用于目标 selector，现全部撤销。

## 2. 合法 alternating selector

取奇数 \(N\ge3\)、\(\ell=\pi/N\)，再取奇数 \(m<N-2\)，令

\[
a={m\ell\over2},\qquad h={1\over2}\tan a,
\qquad a+\ell<\pi/2.
\]

对规范代表 \(\theta\in[0,\pi)\)，定义

\[
\sigma_N(\theta)=(-1)^{\lfloor\theta/\ell\rfloor},
\qquad
N_\theta=\sigma_N(\theta)h n_\theta+[-1/2,1/2]e_\theta. \tag{A}
\]

这是每个 projective direction 恰一弦。若使用实数 lift，弦的有效法向符号必须定义成

\[
s(\theta+j\pi)=(-1)^j\sigma_N(\theta),\qquad 0\le\theta<\pi.
\]

因 \(N\) 为奇数，\(s\) 在整条实轴上每隔 \(\ell\) 交替；因 \(m\) 为奇数，

\[
s(u+2a)=s(u+m\ell)=-s(u). \tag{anti-shift}
\]

### 命题 A（容量夹逼）

令

\[
R=\sqrt{1/4+h^2},\qquad r_-={h\over\sin(a+\ell)}.
\]

则 (A) 的 star hull 满足

\[
\pi r_-^2\le \operatorname{Cap}_2\le\pi R^2. \tag{B}
\]

**证明。** 每个弦点 \(\sigma h n_\theta+t e_\theta\) 的模为 \(\sqrt{h^2+t^2}\le R\)，给上界。固定 oriented ray \(\phi\)，令 \(x=\phi-a\)。若需要正法向弦，可在 \(x\) 左侧距离不超过 \(\ell\) 找到 \(s=+1\) 的 source lift；若需要负法向弦，可在 \(x+2a\) 右侧距离不超过 \(\ell\) 找到 \(s=-1\) 的 source lift。严格小于在 cell 内成立，但奇数 cell 的半开边界可取等号。偏离理想 endpoint 角度 \(0\le d\le\ell\) 时交点半径为 \(h/\sin(a+d)\ge r_-\)，且 segment 参数不超过 \(1/2\)。两 source projectively 不同。故每条 ray 的 \(\rho\ge r_-\)，积分得下界。∎

### 命题 B（exact / near / unattained 分类）

- 若 \(s(x)=+1\)，则 sources \([x]\) 与 \([x+2a]\) 的 endpoints 都在半径 \(R\)；由 (B) 的 pointwise 上界，它们是两个 exact top sources。
- 这些 exact-tie rays 在 \(S^1\) 上总测度为 \(\pi\)。
- 对所有 rays、所有 \(\tau>R-r_-\)，\(T_{\phi,\tau}\) 至少含两个不同 projective sources。即使边界处一个构造 source 的 reach 仅为 \(r_-\)，严格的 \(\tau>R-r_-\) 仍保证它属于 near set；这里不要求 near supremum attained。
- 在负 cell 内通常没有半径 \(R\) 的 endpoint；在半开 cell 边界可出现 source 序列趋近 \(R\) 而对应分支不 attained。该零测度边界不能被误报为 exact top。

## 3. 严格保留的 no-go

### (W) winner variation

在命题 B 的正测度 exact-tie set 中，两条 physical sources 同时达到同一 \(\rho\)。在任一 tie interval 内把 winner 细分并交替选择，可令 switch count/total variation 任意大；弦族、\(\rho\) 与 \(\operatorname{Cap}_2\) 完全不变。因此任何

\[
\operatorname{Cap}_2\ge P+cV(w),\qquad c>0,
\]

只要 \(P\) 与任意 tie-breaking 无关，就被合法 selector 严格反驳。

### raw-label degree

复制同一 \([\theta]\) 的程序标签或把一条 contact branch 切成更多 cells，会改变 raw graph degree 而不改变弦族。这不是一个新 selector，而正说明 raw label count 不能作为 theorem input。此非不变量结论不依赖旧非法族。

## 4. 只对一个明确 excess 命题的反例

取一列参数满足

\[
N_j\to\infty,
\quad m_j\to\infty,
\quad m_j/N_j\to0,
\quad N_j,m_j\text{ odd}.
\]

则 \(a_j,h_j\to0\)、\(\ell_j/a_j=2/m_j\to0\)，所以 \(r_{-,j},R_j\to1/2\)。由 (B)，

\[
\operatorname{Cap}_{2,j}\to\pi/4.
\]

对固定 \(c>0\) 与固定 \(\tau>0\)，定义闭合命题 \(\mathrm{XG}(c,\tau)\)：对每个合法 selector 都有

\[
\operatorname{Cap}_2-\pi/4
\ge c\int_{S^1}
1_{\{|T_{\phi,\tau}|\ge2\}}\,d\phi. \tag{XG}
\]

则
\[
\forall c>0\;\forall\tau>0,\qquad \mathrm{XG}(c,\tau)\text{ 为假}.
\]
事实上先固定 \(c,\tau\)，再取充分大的 \(j\)。因为 \(R_j-r_{-,j}\to0\)，每条 ray 都有至少两个 \(\tau\)-near sources，右端 indicator 积分为 \(2\pi\)，而左端趋于零并由 \(\pi h_j^2\) 从上控制。另可选随族变化的 \(\tau_j>R_j-r_{-,j}\) 且 \(\tau_j\downarrow0\)，但这只是更强的序列诊断，不混入 \(\mathrm{XG}(c,\tau)\) 的量词。(XG) 只说明 near multiplicity 本身不控制“相对 diameter 的 excess capacity”。

## 5. 撤销 (G)/(D) no-go

原文候选

\[
\operatorname{Cap}_2\stackrel?\ge P_R+cG \tag{G}
\]

不能由 (XG) 严格否定：\(P_R\) 可能远低于 \(\pi/4\)，合法族留下的 baseline slack 足以吸收一个小 bonus。若没有指定 \(P_R\) 在该族上的值、residual layer 与固定 \(\tau\)，就不存在可检验的矛盾。因此旧 “(G) DEAD” 改为 **OPEN / underspecified**。

原 (D) 使用 \((d_\tau-1)_+\)，但在 continuum selector 中，严格 near contact 通常包含 source 的开区间，cardinality 不是有限实数。若 `degree` 指有限程序的 branch/label count，它又依赖离散表示。只有先给出 projective quotient 后的有限 measure/packing functional、source separation 权重和 overlap debit，(D) 才是定理形状。旧 “(D) DEAD” 改为 **NOT WELL-POSED AS WRITTEN；任何修正版 OPEN**。

当前不声称 source separation 必须二次、不声称任何 universal 系数上限，也不声称 contact correction 一定不能与 theorem R 组合。缺少的仍是一个真实 residual/crossing lemma；在它出现前，唯一可组合的已证 lower inequality仍是 R 本身，contact spike 不改善 `141/2000`。
