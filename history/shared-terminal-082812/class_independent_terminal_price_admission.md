# Numerical computation admission — class-independent terminal price

- campaign_id: `class-independent-terminal-global-worst-20260817`
- mode: experiment
- target_statement_or_unknown: 在全体有限 high classes 共用一个 terminal radial price、并以共同区间 `[M0,2S6)` 的 global worst H–TC kernel 认证 all-cut 时，与 low、class-global full-chord、exact-pole、fresh dyadic tail 联合 LP 的最大 hard coefficient；是否超过当前 `0.073920942372137638/pi` 或 `0.1/pi`。
- role_in_argument: 判断“同一 terminal price 消除跨 class owner 冲突”是否有足够数值强度；输出只能是 FLOAT scout，all-cut 部分另写解析证明。
- current_theoretical_state: H–TC 已证明对任意 Borel cut、统一 endpoint 区间 `[m,R)` 与任意非负 radial price成立；class-global positive/pole kernel 已有解析式。跨 class 分别使用 terminal receipts 后相加不合法，故改用一次应用于所有 finite classes 的 global worst kernel。
- necessity_analysis: 未知量明确；仅需一个有限 LP 区分“超过当前/超过 .1/均不能”；已有 scipy LP 可复用；不扩大为全局最优证明。
- pure_theory_alternatives: 解析上可立即看出 global denominator `2S6` 很弱，但与 class-global kernel 的互补量需有限 LP 才能判断当前阈值；先做最小网格 scout。
- algorithm_or_solver: scipy HiGHS，radial mesh 0.05 加解析断点；32点 Gauss 单元积分；dense parameter replay。全局 terminal kernel采用 `H(M0;p)/(pi*2S6)`，只收一次 source load。
- cumulative_scale: 单次约数千变量、数千约束；不做随机多 seed 或大范围 sweep。
- elapsed_resources: 本 campaign 此前 0。
- additional_budget: 最多 3 个确定性 LP（baseline、去 terminal 对照、必要时细网格一次），总 wall time 5 分钟。
- expected_wall_time: 每个约数秒至一分钟，依据现有 corrected LP。
- expected_information_gain: 若超过阈值，定位最坏 class 并进入严格证书；若不超过，给该模型的 explicit feasible scout 与 global-terminal 边际/上界诊断，停止此路线。
- success_stop: dense replay 超过 `0.1/pi` 至少 `1e-4`，或超过当前至少 `1e-4` 且 terminal price 非零。
- failure_stop: 最优 LP 不超过当前，或 terminal price为零/仅数值噪声。
- artifacts: `/home/argustest/class_independent_terminal_price_lp.py`, witness JSON, 中文报告。
- proof_exit: 单独证明 global H–TC all-cut receipt；数值结果不冒充 continuum/Arb certificate。
