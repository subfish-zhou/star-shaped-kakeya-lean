## Numerical computation admission

- campaign_id: radial-price-H-M0-fixed-point-20260817
- mode: experiment
- target_statement_or_unknown: 在已审计 low/high radial kernels 内，寻找有理 H,M0 与有限有理 half-open schedule，使 min(H/2, π c_hard)>0.072323，尽量接近 0.1。
- role_in_argument: 只发现候选；最终必须由 Fraction + 外向超越函数区间证书闭合。
- current_theoretical_state: H=1/5,M0=99/100 的 exact certificate 给 0.072323077979923422；缺少 C_low 对 H 的解析单调式和更优自洽 easy/hard 固定点。
- necessity_analysis: 未知量明确；理论先给出精确分段公式和导数，数值仅优化有限 schedule；结果直接决定 exact-certificate 候选。
- pure_theory_alternatives: 已先解析化 C_low(H) 及 supplemental branch 阈值；high schedule 是有限非凸 equalization，暂无闭式全局解。
- algorithm_or_solver: scipy differential_evolution/SLSQP 小规模 scout；kernel 用解析分段积分；候选随后量化为有限十进制有理数并用现有 Fraction/outward verifier 改写验证。
- cumulative_scale: 本轮最多 30 个 (H,M0) 外点、每点至多 2e4 objective evaluations；不做大网格。
- elapsed_resources: 0。
- additional_budget: wall-clock 8 分钟，单机 CPU；若前三个候选均受 H/2 或同一 high bin 限制且无提升则停止。
- expected_wall_time: 2–6 分钟（现有 15 维 schedule 优化为秒至十秒级）。
- expected_information_gain: 成功给出可精确认证的新组合；失败则定位 H 下降由 easy branch 抵消 hard 增强的固定点上限。
- success_stop: 找到可量化候选总 bound>0.0723231，并完成独立 Fraction/outward replay；若达到 0.09 立即停止。
- failure_stop: 预算到期，或三轮不同初始化改善<1e-5。
- artifacts: /home/argustest/radial_H_optimization_admission.md；后续报告/脚本同前缀。
- proof_exit: 将候选 H,M0,S,A 固化为有理数，扩展 radial_price_certificate.py 的通用参数并验证所有严格不等式。
