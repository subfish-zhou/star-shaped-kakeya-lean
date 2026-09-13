# Star-shaped Kakeya：普适下界1/10

**已完成：任意平面star-shaped Kakeya集E满足Lebesgue外面积|E|*≥1/10。** 不要求E可测、有界或闭；原始线段选择不必连续或可测；没有centered/equal-height、N=7或有限cardinality限制。

这是通过独立几何、算术和完整拼接审查的人工数学证明，**不是Lean形式化，不宣称最优性或历史优先权**。旧基线与已有Lean模块保留不动。

## 阅读顺序

1. [THEOREM_01.md](THEOREM_01.md)：完整定理、证明路线、四类方向及物理源预算。
2. [IL证明](low-source-b2/integrated-low/PROOF.md)：按近端点半径选择额外理想锚点，对真实圆弧统一取并集，再以互补价格消去类别付款差。
3. [高域核](endpoint-geometry-b1/endpoint-domain/PROOF.md)：完整圆截面与all-cut估计。
4. [baseline/PROOF.md](baseline/PROOF.md)：Borel恢复、圆区间并集引理及尾部核；最终证明不使用旧优化价格表。
5. [完整端到端审查](tenth-reviews/b2_universal_tenth_end_to_end_review.md)：`ACCEPT_UNIVERSAL_0P1`。另有[IL几何审查](tenth-reviews/b2_IL_geometry_review.md)与[独立算术审查](tenth-reviews/b2_IL_arithmetic_review.md)。

具体承重源、审查报告及哈希绑定见`theorem_01_acceptance.json`。原送审源中“待审/未证明”标签是历史记录，当前状态以本入口与验收记录为准。

## 重放

从任何工作目录运行本目录的绝对路径`run_one_tenth.sh`：

```sh
/home/argustest/research/star-kakeya-wt-01-short-integration/research/one-tenth/run_one_tenth.sh
```

依赖已安装python-flint的Python，可用`ARB_PYTHON`覆盖默认解释器。normal和`-O`分别运行原Fraction对数级数证书、独立Arb重建和5项系数回归。脚本任一步失败即退出，不写回证明或数据。其PASS证明固定系数核验成功，几何证明的认可来自上述独立审查，不能用代码PASS替代。

## 已否定但不影响主定理的路线

较强的逐半径PL有[真实正测度反例](low-source-b2/paired-pointwise/COUNTEREXAMPLE.md)：r=1/4、|V|=43/1000、真实角并集长度1/50。最终证明直接使用IL，完全不依赖PL。固定far-sign旁支也不是依赖，无需继续研究它来完成本目标。

## 保留的历史基线和短收尾

- 原普适下界0.082812499999972190及7段短证明仍正确，未被改写成新证明。
- [CLOSEOUT.md](CLOSEOUT.md)、`closeout.json`、`reviews/`和`run_all.sh`属于此前的短收尾：真实受限two-short C2+C5定理及34/441台账。该台账未变，不是当前普适0.1的证明或分母。
- `run_all.sh`重放上述历史包；**当前主定理入口是`run_one_tenth.sh`**。
- [DISPOSITION.md](DISPOSITION.md)保留旧路线勘误，不恢复scalar cells或N7归约。

全部本地提交；冻结formal worktree和0.25线未修改；未push。
