# Lean spike 日志

## 2026-08-01：AddCircle 单弧膨胀

### 目标

验证 Mathlib 的 `AddCircle.volume_closedBall` 是否足以支持 quotient-circle adapter 的基本测度公式。

### 初始错误陈述

最初只假设 `c ≥ 0`、`r ≥ 0` 和 dilated arc 未饱和：

```lean
2 * (c * r) ≤ T
```

Lean 化简后留下：

```text
ofReal (min T (2*(c*r))) = ofReal c * ofReal (min T (2*r))
```

这不是 tactic 缺口。若 `0 < c < 1`，dilated arc 未饱和并不推出原 arc 未饱和，线性测度公式一般不成立。

### 修正

Kakeya 应用使用膨胀，因此加入 `1 ≤ c`。由

```text
r ≥ 0
1 ≤ c
2*(c*r) ≤ T
```

推出 `2*r ≤ T`，两边的 `min` 都落在非饱和分支。随后用 `ENNReal.ofReal_mul` 得到：

```lean
example (x : AddCircle T) (hc : 1 ≤ c) (hr : 0 ≤ r)
    (hunsat : 2 * (c * r) ≤ T) :
    volume (Metric.closedBall x (c * r)) =
      ENNReal.ofReal c * volume (Metric.closedBall x r) := by
  rw [AddCircle.volume_closedBall, AddCircle.volume_closedBall]
  have hc0 : 0 ≤ c := by linarith
  have hr_unsat : 2 * r ≤ T := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) hr]
  rw [min_eq_right hunsat, min_eq_right hr_unsat]
  rw [← ENNReal.ofReal_mul hc0]
  congr 1
  ring
```

### 实际验证

命令：

```bash
ulimit -n 65535
lake env lean /tmp/StarKakeyaCircleSpike.lean
```

结果：exit code 0。`#print axioms circleBall_dilate` 输出：

```text
[propext, Classical.choice, Quot.sound]
```

### 结论

`AddCircle T` 已提供正确归一化的圆周体积和 fundamental-domain measure-preserving API。下一难点不是单弧测度，而是任意开弧并的 component decomposition、owner assignment 和 wrap/saturation containment。
