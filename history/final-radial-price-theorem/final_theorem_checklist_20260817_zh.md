# 最终 theorem checklist（2026-08-17）

## Standalone 裁决

**PASS**（按本任务已给状态：H-TC provenance PASS、OPR PASS；本次独立 low 审计亦 PASS）。因此，对任意平面 star-shaped Kakeya 集 `E`（无需可测），

\[
\boxed{\mathcal L^{2,*}(E)\ge 0.072323077979923422.}
\]

本文只列实际读取并核验的 artifact；OPR 的 PASS 是本任务的已给前提，不虚构未提供的路径或引用。

## 1. 固定 bytes / hash

| artifact | SHA-256 | 核对 |
|---|---|---|
| Git-blob 导出的 `/tmp/low_one_sided_radial_extension_888f.md` | `1f9278b1b97af4244d75a8653b084f92785b3ff204befdefc38b9c7e0166e00c` | 与 workspace 文件逐 byte 相同 |
| `low_one_sided_radial_extension_zh.md` | `1f9278b1b97af4244d75a8653b084f92785b3ff204befdefc38b9c7e0166e00c` | PASS；canonical Git blob SHA-1 为 `4c5b867ba6ffd88383dd7b0428d5fa4171d75a0b` |
| `near_diameter_all_radial_layers_zh.md` | `eb620359a33999462e2818677f2cf3d7d601ba59ab0088d6662b61a415c6c1e7` | PASS |
| `radial_price_certificate.py` | `6acfa1bbf12b05ed0270f48ae9d8a09c34e955b66a43222e910665f632028b19` | 与 receipt 的 `verifier_sha256` 相同 |
| `radial_price_certificate_receipt.json` | `7ffad982d08648b41561e5b9ea32cf94dfa8a5e1ca17891bc621e952b6867642` | replay 逐字段一致 |
| `/tmp/low_scale_terminal_collar_c11a.md` | `669b1ddd3881140b7dec727b40ce8597791212e7f46bf0a51c2aeab594b64f95` | 与 H-TC ledger 相同 |
| `/tmp/continuous_collar_dc04.md` | `40d06f1b96035e46c25272d8bb7926075e7f17ccbca688ebe2bc5bc7e967adb9` | 与 H-TC ledger 相同 |
| `/tmp/high_literal_union_6e98.md` | `5dfeb008abe35f4438dd3b2ae4f1cfaca12fec571a909f23b4dc90f856f35b5a` | 与 workspace `high_literal_union_all_cut_zh.md` 相同 |
| `high_scale_unified_theorem_zh.md` | `2164eef7ca1ba67d80bdc869fc58ceacdfead6a7d5b26b6bf02089a84b230952` | 与 H-TC ledger 相同 |
| `h_tc_provenance_audit_20260817_zh.md` | `b319b15da1c3cf78a2ad5158bc8719ea1dc9f3667630e05e2afe8907d0c5ecfc` | PASS ledger |
| `dyadic_selector_value_convergence_zh.md` | `2fc9d6819619f44003b0be75df6d3e3fa3ce24f2b3e4d5744df893f98f212887` | OPR 后的 dyadic/outer 组装文本；不冒充 OPR 自身证明 |

## 2. Low one-sided Git blob 独立审计

**PASS。** 对 `M0=99/100`, `H=1/5`, `m=1/100`，证书实际需要 `r< a0=0.36434005 < 1/2` 的 low owner。

- 若 `|h|≤r`，较远 endpoint component 满足
  \[
  |K|/|J|\le t/(t-r),\qquad
  (2\Lambda-1)^{-1}=(t-r)/(t+r).
  \]
- 若 `|h|>r`，真实 fibre 是连接 endpoint rays 的完整 interval；其长度至少
  `alpha0=2 asin(1/(2M0))`，向较远 endpoint 的 ideal anchor 只需扩张至多
  `asin(H/t)`，故
  \[
  (2\Lambda-1)^{-1}\ge
  \frac{\alpha_0}{\alpha_0+2\arcsin(H/t)}=k_H(t).
  \]
- 混合两类只取共同较弱常数
  \[
  k(r,t)=\min\{(t-r)/(t+r),k_H(t)\};
  \]
  每个固定 `r` 只取一个 survival threshold，不叠加 sources。
- 每条单位弦都有 `M≥1/2`；取 `t=1/2` 对整个 low cut 有效。证书把旧 two-sided receipt 用在 `[0,m)`，把上述 one-sided receipt 用在 `[m,a0)`；两段 half-open 且物理不交。
- `radial_price_certificate.py` 中 `alpha=2 asin(50/99)`、`k_h=alpha/(alpha+2 asin(2/5))`、交点 `cross=(1/2)(1-k_h)/(1+k_h)` 正好是上述 `t=1/2` 分支；其积分 primitive 与 `r k(r,1/2)` 的两段公式一致。

因此 Git blob 的高-offset补充分支足以支撑 `M0=.99` 的 low coefficient；旧的随机脚本只覆盖 `.655` 窗口，未被当作 `.99` 几何证明。

## 3. Exact radial-price certificate

重放 `python3 radial_price_certificate.py` 成功：

```text
RADIAL_PRICE_EXACT_CERTIFICATE_OK
low lower    = 0.023021151022880283
finite min   = 0.023021150720250842   (high bin 1)
first tail   = 0.038333604032402981
common c_*   = 0.023021150720250842
pointwise total price upper = 1 (exact)
```

owner atoms 为 `[0,a0)`、`[a_j,a_{j+1})` 及 dyadic tail
`[2^(n-1)s6,2^n s6)`；`a7=s6`。它们 half-open、首尾相接、两两不交，故 low/high、finite/tail、scale/scale 均无重复付款。

## 4. Exhaustive theorem split

对 OPR 产生且 literal union `U(d)⊂G` 的 finite Borel selector `d` **重新执行**如下分支（不能把 recovery 前 selector 的 `h` 性质无说明地转移给 `d`）：

1. 若存在 `q` 使 `|h_d(q)|≥1/5`，则对应 anchored triangle 面积 `|h|/2≥1/10`，故 `|G|≥0.1`。
2. 否则每个方向均有 `|h_d(q)|<1/5`。再定义
   \[
   Q_L=\{M_d<99/100\},\qquad Q_H=\{M_d≥99/100\}.
   \]
   等号归 high，故二者 Borel、不交且穷尽 `RP^1`。low theorem 的假设 `M≤99/100` 对开 cut `M<99/100` 足够；high half-open bins 穷尽 `Q_H`。

射影方向圆按标准弧长归一化为
\[
|\mathbb{RP}^1|=\pi,
\]
所以 `|Q_L|+|Q_H|=pi`，共同 radial coefficient 给出
\[
W(U(d))\ge c_*|Q_L|+c_*|Q_H|=c_*\pi.
\]

## 5. `W≤area` 与 outer recovery

\[
W(F)=\int_F\min(1,|x|^{-1})\,dx,
\qquad 0<\min(1,|x|^{-1})≤1,
\]
故对可测 `F` 有 `W(F)≤|F|`。finite Borel selector 的 literal union 是 analytic，因而 Lebesgue 可测。于是
\[
|G|\ge |U(d)|\ge W(U(d))\ge c_*\pi.
\]
对任意开外包 `G⊃E` 取下确界，得到同一 outer-measure 下界。

## 6. 最终 outward decimal

使用证书的正数下端

\[
c_*=0.023021150720250842,
\qquad \pi>3.141592653589793238,
\]
精确有理乘积为

\[
\frac{18080769494980855642511650568851599}
{250000000000000000000000000000000000}
=0.072323077979923422570046602275406396.
\]

向下截到 18 位小数得到
`0.072323077979923422`；严格余量为
`5.70046602275406396e-19`。同时 easy 下端 `0.1` 更大。因此发布值是安全的 outward floor。

## 7. Replay 说明

以下现有检查均以 exit code 0 通过：

- `radial_price_certificate.py`: `RADIAL_PRICE_EXACT_CERTIFICATE_OK`；
- `check_high_literal_union_all_cut.py`: `HIGH_LITERAL_UNION_ALL_CUT_CHECK_PASS`；
- `check_low_one_sided_radial_extension.py`: `ONE_SIDED_LOW_RADIAL_EXTENSION_OK`（仅作 `.655` sanity check）；
- `final_theorem_audit_check.py`: `FINAL_THEOREM_ASSEMBLY_ARITHMETIC_OK`。

最后一个旧脚本仍打印 H-TC/OPR BLOCK 文案；这是旧 ledger 的静态提示，不是本轮 replay 失败，也不覆盖本任务已给的 H-TC/OPR PASS 状态。
