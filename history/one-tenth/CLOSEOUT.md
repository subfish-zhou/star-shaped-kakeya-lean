# 0.1线：短收尾验收

## 已完成

1. **普适基线短证明**：保留外测度下界`0.082812499999972190`；132格价格压缩为7个活跃区间；直接径向包含代替first-birth/Stieltjes。论文级几何+Arb算术，不是Lean新定理。
2. **统一separator定理**：centered、common-height的七弦族，两个short、五个long且至少两个separator正切>=3/7，满足`tau S-H>=Phi>1012129*h/15582000+delta1+delta2`（h>0）；h=0直接零面积。完整source-once、边界、碰撞、极点处理已独立审查。
3. **完整carrier到定理的映射**：对27个新增named roots，证明`actual root closure ⊆ weak carrier ⊆ theorem domain`，不是只检查代表点。

## 当前精确台账

- 新增27个root IDs；继承旧7个；**34/441 certified，407 residual**。
- 精确有序集合见`closeout.json`。这只是centered common-height C2+C5的named root域计数，不是几何体积比例。
- 旧7个按已有authority继承，未在此重证。
- 旧23个four-lower scalar faces对真实C2+C5为空，不提供额外root覆盖。
- 不推出任意参数N7、任意cardinality或continuum 0.1。

`rootmap/candidate.json`及其README原样保留送审状态（7/441、conditional34），供复现原审查对象；**本目录当前台账以本文件和closeout.json为准**，而非历史candidate字段。`verify_closeout.py`从原candidate重新派生集合，检查当前scope和已审字节；它不把审查报告文本转换为形式证明。

## 独立审查与整合

| 部分 | 独立审查的原提交 | 结论 |
|---|---|---|
| baseline | `69ceb8881cf3bf621afb5e1d58ec3d1214369abd` | ACCEPT |
| separator | `9b185ea96750d53fdbad42b79225bf073ee01346` | ACCEPT |
| rootmap | `cd8779e0bdb82f19bf8ed7c4fd2e162094c070c5` | ACCEPT，允许scoped34/441 |

完整审查在`reviews/`。父级已确认三个整合子树与这些提交逐字一致，重放normal/optimized及13个原始source hash。新台账位于独立整合层，没有改写历史candidate或旧receipt。

统一入口为`run_all.sh`：baseline7项、separator7项、rootmap12项及closeout5项。它执行两个模式，遇到任一失败立即停止，重放不改写工件。closeout四个负例经历实际RED→GREEN：漏root、误称0.1已证明、漏字节绑定、错误review commit均被拒绝。

## 研究交接

短收尾完成后，此channel转入0.1普适low-side几何。旧标量cell菜单不再是默认路线。任何新候选先陈述任意选择下的真实集合不等式，并经过对应的反例/量词/同一physical source审查；没有新几何就不扩大网格。

0.25线由用户另一channel负责，此处不写入、不派相关任务。旧规范化worktree和历史证据保持不变；本次提交均本地，未push。
