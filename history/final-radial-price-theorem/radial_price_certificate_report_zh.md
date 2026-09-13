# Radial-price 严格有理/外向区间证书

## 结论

`radial_price_certificate.py` 把原数值 witness 转成了不依赖浮点数、SciPy 或数值 quadrature 的可审计证书。所有断言最终都是 `fractions.Fraction` 的精确比较。

目标取题目要求的精确有理数

\[
T=0.0224552=28069/1250000.
\]

复算所得共同严格下界为

\[
c\ge 0.023021150720250842>T,
\qquad c-T\ge0.000565950720250842.
\]

## 证书机制

- `M0=99/100`、`H=1/5`，所有 scale/radial 小数断点均按十进制**精确有理数**解释；receipt 也将其列为退化的有理区间 `[q,q]`。
- high kernel 在 `1,s-1/2,s` 处分段，逐段是一次或二次多项式，积分保存为精确分数。
- high coefficient 中的 `pi` 用 Machin 恒等式
  `pi=16 atan(1/5)-4 atan(1/239)` 与交错级数余项产生外向有理区间；取 `pi` 上端点得到 coefficient 下界。
- low 中的 `asin` 用正项 Taylor 级数及几何尾界，`atan` 用交错尾界，`log` 用
  `log(x)=2 atanh((x-1)/(x+1))` 及几何尾界；其后全部通过有理区间四则运算外向传播。low 区间宽度小于 `1.9e-27`。
- finite ownership 是相接但不交的 half-open bands；dyadic tail 从 `S6` 开始并继续使用不交 half-open bands，所以逐点总 price 精确不超过 `1`。
- tail 在 scale `s>=2*S6` 时归一化 coefficient 精确为
  `1/(8*pi)-1/(16*pi*s)`，随 `s` 增大，故只需检查首个 tail bin。

## 实跑

```bash
python3 /home/argustest/radial_price_certificate.py --write
python3 /home/argustest/radial_price_certificate.py
```

第二条命令会重新计算全部有理不等式，并要求 receipt 与重算结果逐字段完全一致。成功标志：

```text
RADIAL_PRICE_EXACT_CERTIFICATE_OK
```

机器可读 receipt：`radial_price_certificate_receipt.json`。
