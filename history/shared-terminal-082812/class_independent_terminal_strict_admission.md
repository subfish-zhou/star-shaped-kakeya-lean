# Numerical computation admission — strict class-independent terminal certificate

- campaign_id: `class-independent-terminal-global-worst-20260817`（延续 FLOAT scout）
- mode: proof
- target_statement_or_unknown: 对固定有理参数 `H=1/5, M0=99/100, R=8/5` 和固定有理 radial witness，严格验证 low、有限块 `M∈[M0,R)` 的 seam/positive/exact-pole、首 tail、所有后续 dyadic tail及逐 radial atom source load，并证明 `pi*c > 41/500 = .082`（最低 fallback `>2/25=.08`）。
- role_in_argument: 这是 class-independent terminal/global-worst theorem 的唯一数值闭包；解析 theorem 与 source-once bridge 已在 `class_independent_terminal_price_report_zh.md` 给出。
- current_theoretical_state: FLOAT optimum 在 `R≈1.60` 给 `pi*c≈.0828125`；尚缺 outward Arb continuum replay、seam 闭包、all-tail 解析检查与 rational witness。
- necessity_analysis: 参数域已严格化为 compact box `M∈[99/100,8/5]`, `h∈[0,1/5]`（pole 单独为 `h=0`），其余 rows 为有限 exact integrals 或单调 dyadic family；成功即闭合该固定 witness；上下游 theorem 已固定；不存在以手算替代数千 box 的现实路线；所有数值输入均为有理 JSON，Arb outward interval 独立重算。
- pure_theory_alternatives: positive kernel 含参数相关平方根端点，纯符号全域最小化较复杂；采用 interval branch-and-bound 是直接且可审计的固定 witness 证明出口。
- algorithm_or_solver: scipy/HiGHS 仅生成候选；截断成十进制有理并 inward 缩放。严格 verifier 用 python-flint Arb（192 bits），从有理输入重算 exact/piecewise primitives、box radius bounds、source load和 dyadic-tail单调下界；fail closed。
- cumulative_scale: FLOAT scout 已约十余个 LP；本轮最多 1 个 candidate LP、完整 Arb replay最多两次；branch-and-bound上限 1,000,000 boxes。
- elapsed_resources: 既有 FLOAT campaign约数分钟；本轮尚未开始。
- additional_budget: wall time 10 分钟；若 1,000,000 boxes 或两次 witness修整仍未 PASS 则停止。
- expected_wall_time: LP几十秒，Arb replay数秒至数分钟，依据现有 corrected Arb certifier。
- expected_information_gain: PASS 直接给严格 `.082` lower；FAIL 定位具体 seam/positive/pole/tail/load margin，不扩大搜索。
- success_stop: receipt `status=PASS`, `strict_gt_0p082=true`，并第二次运行 receipt byte-identical。
- failure_stop: box预算耗尽、严格 lower `≤.08`、或 source load无法通过有理 inward缩放。
- artifacts: `class_independent_terminal_strict_arb.py`, `class_independent_terminal_strict_witness.json`, strict receipt/hash、tests。
- proof_exit: 只把 full Arb PASS receipt称为严格证书；HiGHS输出继续标记为 candidate generator而非证明。
