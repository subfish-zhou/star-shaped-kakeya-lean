# uniform dyadic cells 的最优值收敛：\(m_n\downarrow m\)

下面只使用已经证明的 **open-patch recovery**，不使用 Lipschitz 控制、a.e. 相等或 disagreement-set 面积估计。

## 1. 精确定义与所需 recovery 接口

令
\[
Q=\mathbb {RP}^{1}=\mathbb R/\pi\mathbb Z
\]
带圆周距离。对每个方向 \(q\in Q\)，令 \(A(q)\) 为该方向的合法 centers；若 \(a\in A(q)\)，记相应的 closed geometric patch 为 \(T(q,a)\subset\mathbb R^2\)。selector 是任意逐点合法映射
\[
c:Q\to\mathbb R^2,\qquad c(q)\in A(q),
\]
不假设它 Borel 或 Lebesgue 可测。置
\[
U(c):=\bigcup_{q\in Q}T(q,c(q)),
\qquad
m:=\inf_c |U(c)|^*,                                      \tag{1}
\]
其中 \(|\cdot|^*\) 是二维 Lebesgue outer measure。

使用如下已经通过的 open-patch recovery 形式：对任意 selector \(c\) 和任意开集 \(G\supset U(c)\)，存在有限组
\[
(V_i,a_i),\qquad i=1,\dots,r,                            \tag{2}
\]
使得

1. 每个 \(V_i\subset Q\) 开，且 \(Q=\bigcup_iV_i\)；
2. 对每个 \(q\in V_i\)，\(a_i\in A(q)\)，即同一 center \(a_i\) 在整个 open patch 上逐点合法；
3. 对每个 \(q\in V_i\)，\(T(q,a_i)\subset G\)。

等价地，有限 open-patch sweep
\[
\bigcup_{i=1}^r\bigcup_{q\in V_i}T(q,a_i)\subset G.      \tag{3}
\]
这正是 finite cyclic piecewise-constant recovery 中需要保留的 open-margin 版本。仅有某个半开分段函数 \(c'\) 满足 \(U(c')\subset G\)，而没有 (2)--(3) 的 open patches，并不足以移动其 seams；下证明确实使用 (2)--(3)。

## 2. 嵌套 uniform dyadic 类

对 \(n\ge0\)，令
\[
I_{n,k}=\left[k\pi2^{-n},(k+1)\pi2^{-n}\right),
\qquad 0\le k<2^n,                                      \tag{4}
\]
端点按模 \(\pi\) 解释；这是一个固定半开 cyclic convention。令 \(\mathcal D_n\) 为所有逐点合法且在每个 \(I_{n,k}\) 上常值的 selectors。每个 cell 的常值 center 可从完整中心空间任取；这里没有 center quantization。定义
\[
m_n:=\inf_{d\in\mathcal D_n}|U(d)|^*.                  \tag{5}
\]

由于每个 level-\(n\) cell 是两个 level-\((n+1)\) cells 的并，
\[
\mathcal D_n\subset\mathcal D_{n+1}.
\]
又因 \(\mathcal D_n\) 只是全部 selectors 的子类，故
\[
m\le m_{n+1}\le m_n.                                  \tag{6}
\]
所以 \(m_n\) 有下降极限 \(\ell\ge m\)。若用 cell 数作下标，则本结论是 \(m_{2^n}\downarrow m\)；对“不嵌套的每个整数 \(N\) 个等长 cells”不能直接声称逐项单调。

## 3. Lebesgue number 转移

固定 \(\varepsilon>0\)。若 \(m<\infty\)，由 infimum 定义可取一个完全任意、可能非 Borel 的 selector \(c\)，使
\[
|U(c)|^*<m+\varepsilon.                                 \tag{7}
\]
Lebesgue outer measure 的开正则性对任意集合成立，故存在开集 \(G\supset U(c)\) 使
\[
|G|<|U(c)|^*+\varepsilon<m+2\varepsilon.                \tag{8}
\]
这里没有对 \(c\) 或 \(U(c)\) 作可测性假设。

对 \((c,G)\) 应用 open-patch recovery，得到有限开覆盖 \(\{V_i\}_{i=1}^r\) 及 centers \(a_i\)。由于 \(Q\) 紧，有限开覆盖有 Lebesgue number \(\lambda>0\)：每个直径小于 \(\lambda\) 的 \(Q\) 的子集都包含于某个 \(V_i\)。取 \(n_0\) 使
\[
\pi2^{-n}<\lambda\qquad(n\ge n_0).                     \tag{9}
\]

固定 \(n\ge n_0\)。对每个 dyadic cell 取其在圆周中的 closed arc
\[
\overline I_{n,k}=
\left[k\pi2^{-n},(k+1)\pi2^{-n}\right].                \tag{10}
\]
其直径小于 \(\lambda\)，故可选 \(i(k)\) 使
\[
\overline I_{n,k}\subset V_{i(k)}.                     \tag{11}
\]
在半开 cell \(I_{n,k}\) 上定义
\[
d_n(q):=a_{i(k)}.                                      \tag{12}
\]

由 (11) 和 open-patch recovery 的第 2 条，\(d_n\) 在 cell 的每一点都合法，因而 \(d_n\in\mathcal D_n\)。这里 seams 不是 a.e. 忽略的：若 \(q_0\) 是相邻 cells 的公共端点，则
\[
q_0\in\overline I_{n,k}\cap\overline I_{n,k+1}
 \subset V_{i(k)}\cap V_{i(k+1)}.                       \tag{13}
\]
所以左右两个 trace centers 在 \(q_0\) 都逐点合法。半开 convention 决定 \(d_n(q_0)\) 取哪一个；若 finite geometry 同时保留两侧 closed-cell traces，则两条 seam patches 也都合法。证明没有在 seam 间插入任何 center，也没有生成 bridge。

同理由 recovery 的第 3 条，对每个 \(q\in I_{n,k}\)，
\[
T(q,d_n(q))=T(q,a_{i(k)})\subset G.
\]
甚至把每个 cell 当 closed cell、同时保留 seam 的双 traces，仍有
\[
\bigcup_k\bigcup_{q\in\overline I_{n,k}}T(q,a_{i(k)})
\subset G.                                               \tag{14}
\]
特别地
\[
U(d_n)\subset G,
\qquad |U(d_n)|^*\le |G|<m+2\varepsilon.                \tag{15}
\]
因此对所有 \(n\ge n_0\)，
\[
m_n\le m+2\varepsilon.                                \tag{16}
\]
令 \(n\to\infty\)，再令 \(\varepsilon\downarrow0\)，得到 \(\ell\le m\)。结合 (6)，
\[
\boxed{m_n\downarrow m}.                               \tag{17}
\]

若 \(m=\infty\)，由 \(m\le m_n\) 立即有每个 \(m_n=\infty\)，结论仍成立。若某个显式 selector（例如 centered selector）已给出有限值，则只需上面的 \(m<\infty\) 情形。

## 4. 证明中没有使用的东西

- 不要求原 selector \(c\) 可测或 Borel；只对任意集合 \(U(c)\) 使用 outer measure 与 open hull。
- 不比较 \(c\) 与 \(d_n\) 的 disagreement set，也不声称二者 a.e. 相等。
- 不需要 \(q\mapsto c(q)\) 的 Lipschitz、BV 或 jump 数控制。
- 不需要 \(|U(d_n)\triangle U(c')|\to0\)；唯一比较是严格的逐点集合包含 \(U(d_n)\subset G\)。
- dyadic cell centers 不作有限量化；每个 cell 直接选 open patch 所携带的任意合法 center \(a_i\)。
