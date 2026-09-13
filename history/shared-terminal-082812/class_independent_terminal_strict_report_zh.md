# Class-independent terminal：strict Arb certificate

## 结果

固定有理参数

- `H = 1/5`
- `M0 = 99/100`
- `R = 8/5`
- strict target `πc > 41/500 = 0.082`

对固定有理 witness 的 192-bit python-flint/Arb outward replay 返回 `PASS`：

```text
c_lower  = 0.0263600110895488633333427875767739686...
πc_lower = 0.0828124171874721904389470081600785906...
```

所以严格得到 `πc > .082`，当然也严格 `> .08`。该 lower 与 FLOAT scout `.0828125` 的差仅来自统一 `0.999999` inward 缩放及价格向下有理化。

## verifier 覆盖

`class_independent_terminal_strict_arb.py` 不读取 generator 的 objective/kernel diagnostics，而从 JSON 有理数重新计算：

1. **low**：解析 primitive，所有 `asin/atan/log` 用 Arb outward rounding；transcendental breakpoints 保持为 Arb intervals。
2. **共同 terminal**：一次 H–TC global-worst kernel
   `∫p(r)min(r,1)min(1/2,M0-r)_+ dr/(πR)`，不按 class 重复收费。
3. **positive + M seam**：覆盖闭区间 `M∈[M0,R]`、`h∈[0,H]`。positive kernel 对 lower endpoint `N` 单调，且 `N(M,h)` 在矩形上的最大值由 `h=H` 及两个 M endpoints 给出；因此同一个 outward `N_upper` 严格覆盖内部和 `M→R−` seam。
4. **exact pole**：`h=0`, `N=|M-1|`，在 `[M0,1]` 与 `[1,R]` 上 pole integral 单调，严格检查 `M=M0,1,R`。
5. **tail**：首 class `[R,2R)` 用 witness 中同 source-load 的价格；之后所有 dyadic classes 使用互不相交 full fresh bands。对 `m_n=2^nR (n≥1)`，精确系数为 `(m_n/4-1/8)/(2πm_n)`，随 `m_n` 增加，故只需检查 `m_1=2R`。
6. **source load**：每个 physical radial atom逐项重算
   `low + terminal_global + positive + pole + tail_first ≤ 1`；最大 outward upper 为 `0.999999... < 1`。schema 封闭，额外/遗漏 family 均拒绝。

## 产物与复现

```bash
PY=/home/argustest/.venv-fullspan-cert/bin/python
$PY class_independent_terminal_strict_arb.py class_independent_terminal_strict_witness.json \
  --output class_independent_terminal_strict_receipt.run1.json
$PY -m unittest -v test_class_independent_terminal_strict_arb.py
```

两次完整 replay 的 receipt byte-identical；SHA-256 记录于 `class_independent_terminal_strict.sha256`。HiGHS generator 只用于产生候选，不属于证明 trust path。
