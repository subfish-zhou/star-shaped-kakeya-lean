# B1：已审定的新几何；0.1桥已由B2闭合

## 当前权威

三路研究产物均已父级normal/optimized重放，随后独立数学审查通过。主定理为人工数学证明，小脚本仅核对声明的固定算术；不是Lean证明。B1单独不更新下界；其Theorem2与B2的已审IL定理合用，现已证明普适0.1，见`../THEOREM_01.md`。

| 内容 | 原送审commit | 当前结论 |
|---|---|---|
| endpoint-domain Theorems1–3：完整圆截面、全锥角、low cap | `36d8bbbc1870ae16e3fc06f75122b9e30f12c541` | ACCEPT |
| coupled-arcs：联合长度/半径collar | `a20c61b2e1d8b593fafa91caecb23192ab260931` | ACCEPT，任意selector可用外角测度 |
| parent low-height collar | `13be67c5b3940d5f40f5ec11153b28c448e9825a` | ACCEPT，普通积分明确要求Borel selector |
| capacity-interface：尾部公式、有限菜单对偶 | `f8676e97712606e67216dd20c7687d0bbe97feeb` | ACCEPT，数值障碍仅限其指定旧kernel/预算 |

完整独立报告位于`/home/argustest/kakeya_astra_audit_20260905/b1_{endpoint,collar,capacity}_independent_review.md`。当前整合文本仅按审查建议补充scope，不改变已审公式。作者文件内的“待父级审查”段落与历史脚本输出属于送审时记录；当前状态以本入口为准。

## 禁止扩大解释的结论

- `pi(3/8-log(2)/2)<1/10`只封死指定far base、共同统一扩张比和因子`1+2rho`的方法；不排除非对称、符号分层、参数分层等其他far-only证明，也未声称取得锐的实际最优值。
- `R>=5/2`只对应旧transverse kernel在新鲜半带上的付款。新full-cone定理可消除它；不能继续把它当全局几何障碍。
- 任意原selector的外角测度结论不自动允许普通极坐标积分。必须通过已证明的开集/Borel恢复，并重新划分恢复后的方向类。
- 同一来源的两个核可取最大，不能直接相加。任意原切集的数据不由Borel恢复自动保留。

## 审查中顺带证明的加强

collar审查§4给出两条合法加强：

1. 一般transverse argument可取完整单位长度collar，得到`k_full=(1/pi)min(1/R,(1-r/m)_+)`。此处不要求停在垂足之前。
2. 低高度单侧扩张必须仍用半collar，但可保留变化的长度/半径比，得到`k_height_joint=c*a/(2-c*a)`，`a=min(1/(2R),(1-r/m)_+)`、`c=sqrt(1-H²/(m-1/2)²)`；要求`H<m-1/2`。

这些不是新的全局面积下界。本阶段0.1出口用的是endpoint-domain Theorem2，不需要继续优化collar变体。

## 精确研究出口

`CONDITIONAL_TENTH_BRIDGE.md`给出一个手选、源预算互不重叠的拼接：有限高、第一尾带及后续所有尾带已经有足够的已审几何估计。桥本身另行独立审查；固定系数已双模式核对。

B2已证明low银行内的积分下界IL，并通过独立几何、算术与全局拼接审查。更强的逐半径PL被真实反例否定且不参与最终证明。旧conditional文档保留原送审字节，其条件如今由已审IL消除；不恢复441-root或scalar cell campaign。

当前普适下界为1/10；旧0.082812499999972190基线保留。scoped34/441台账未改，也不是新证明的依赖。全部本地提交，无push，0.25线未动。
