# 英文历史稿事实／来源蕴含审查

## 总裁决

**BLOCK：第95行把有明确日期的「本地交付验收」写成了同日「public delivery」。重点数学解释总体 PASS；另有几处 MINOR，宜在翻译定稿前消除。**

审查对象：`history-en-draft.md`（本次读到的105行版本）。下列行号以此版本为准；同时提供原句，便于正文并行编辑后定位。仅审查指定重点及其证据接口，不重编证明、不做新数学研究。

已先读 `migration/history-source-audit.md` 与 `migration/historical-lean-audit.md`，再按 `preserve/RELOCATION.json` 的 `logical_entries` 定向查原件。以下来源路径均相对于 `/home/argustest/kakeya-storage-inventory/migration/preserve/`。证据分级：**P**＝实读保留的原始数学稿；**V**＝实读历史验收／审查声明（支持当时裁决，不等于本次重证）；**R**＝实读既有原生执行收据／日志（不是本次执行）；**G**＝保留的Git元数据（不等于发现或公开发表时间）；**A**＝迁移审计的既有静态结论（本次没有重做其全部检查）。

## BLOCK

### B1．最终日期混入没有随文证据的公开发布事件

- **原句（95）**：“The ordinary 1/10 proof was accepted on September 5; the final Lean closure and public delivery followed on September 13.”
- **实际来源**：
  - `COMMIT_CHRONOLOGY.json` 的 `commits[commit=2587e7eb9f379a5858fdf9a2e0f3e1dfcd6cc5ef]`：作者日期 `2026-09-05T02:30:16+00:00`，提交标题为接受普适外面积1/10；这是 G，和 T8 的实际接受裁决共同支持「9月5日已记录验收」。
  - `history/one-tenth/tenth-reviews/b2_universal_tenth_end_to_end_review.md:5–11`：接受普通数学证明，明确不是 Lean 定理。
  - `evidence/final/FINAL_ACCEPTANCE.json:2–4`：`CONTENT_ACCEPTED_FOR_LOCAL_DELIVERY`，`accepted_utc=2026-09-13T08:15:20.887050+00:00`，scope 明说不是公开发表；`:156–161` 的 `git_push`、`public_release` 等均为 false。
  - `evidence/final/FINAL_HANDOFF.md:5,10,14,36`：Lean闭合及44模块冷编译已达到本地交付门；末行明确没有自动 push／公开发布。
- **判断**：9月13日「截至验收已完成 Lean 闭合／本地交付」有证据；「public delivery on September 13」不能由这些证据推出。`final-public/README.md` 及迁移说明支持存在公开项目，但没有在所读来源中绑定该公开事件日期。不能把本地验收时间转成首次 kernel 闭合或公开日期。
- **最小修订**：改为 “The ordinary proof was recorded as accepted on September 5. By the local-delivery acceptance of September 13, the final Lean closure and cold-build checks had also been completed.” 若保留同日公开发布，必须另补确实绑定公开事件及日期的证据；本轮不联网追索。

## MINOR

### M1．IL段落需明确局部Borel前提的所在层，不能改变最终任意集量词

- **原句（79）**：“Split a direction cut V into B, where N≥2/5, and U, its complement.”；（83）的截面长度式随后直接使用 `|V|`、`|B|`。
- **实际来源**：T6 `history/one-tenth/low-source-b2/integrated-low/PROOF.md:10–20,24–29` 的局部定理要求 Borel 方向族、Borel 选弦和 Borel 子cut；T7 `history/one-tenth/THEOREM_01.md:7–19,33–41,104–110` 先在任意开外包中恢复 Borel 选择，最后回到任意 E 的外测度。
- **判断**：全文第7、67行已讲任意集和恢复，**没有把Borel错误加到最终E上**。但跨小节后直接说 “a direction cut” 容易被单段引用成任意不可测cut都满足普通长度公式。
- **最小修订**：在79行开头补 “Working with the recovered Borel selector inside an arbitrary open enclosure, take a Borel direction cut V …”。不得改成 “Assume E is Borel”。

### M2．后见结构解释宜和首次发生时间分开

- **原句（77）**：“It also exposed the remaining bottleneck.”（主语是9月5日短证明）；（57）：“it specifies what the next successful construction had to control.”
- **实际来源**：N14 `history/shared-terminal-082812/class_independent_terminal_price_report_zh.md:14–19,113–127` 已明确旧low核的模型内上限、仅调terminal不能达到0.1；这早于9月5日短整理。F1 `history/blocked-09755/STATUS_BLOCKED.md:19–33,45–47` 明确 source-capacity 缺口及转向决定，但没有完整记录后来每个价格构造的思想起因。
- **判断**：这些句子作为方法结构的回顾可成立，不宜读成「9月5日才首次发现瓶颈」或「反例／失败直接造成后面每个新想法」。第91行主动拒绝这种因果推断，值得保留。
- **最小修订**：77行改 “It also made the already documented low-direction bottleneck easier to see.”；57行可加 “In retrospect”。不需要改写成研究计划，也不需要补造心理过程。

### M3．H单调性缺少「其余参数固定」的限定

- **原句（69）**：“Lowering H improves the relevant low-height estimate, but weakens the easy branch, whose triangle only guarantees H/2.”
- **实际来源**：N13 `history/radial-H-fixed-point/radial_H_monotonicity_and_certificate_zh.md:3,43–61,63–73` 明说固定 `M,A` 的单调式；N12 `history/radial-H-fixed-point/CERTIFIED.md:3–11` 晋升固定 `H=2957/20000,M0=9999/10000` 的安全界。
- **判断**：竞争分支解释正确；不能理解成任意同时移动其他参数仍保证low改善。
- **最小修订**：加 “With the other low-kernel parameters fixed”。原文最后称candidate的旧状态不推翻后续CERTIFIED裁决。

### M4．[LI]、[LA] 没有按当前Source convention落到映射条目

- **原句（105）**：“Bracketed source IDs refer to retained primary project documents through the relocation map.”；第9行用 `[LI]`，第21、35、47、97行用 `[LA]`。
- **实际来源**：`RELOCATION.json` 的 `logical_entries` 有 `D8`（Li PDF）和诸 E/N/T/L/D 编号，没有 `LI` 或 `LA` 的 `source_id`；`historical-lean-audit.md` 是迁移审计，不是原生历史证明文件。
- **最小修订**：明确定义 `LI = history-sources/D8-li-2026-arxiv-2509.05711v2.pdf`、`LA = audits/historical-lean-audit.md`，并将source convention改成「原件及迁移审计」。LA不能因位于引文中就变成原始执行证据。
- Li段已经保留§4.1两项进一步数值陈述，也没有把π/98称为文献唯一最强界；这点符合任务给定的文献边界。本轮未额外读PDF，不将此标成新的原论文E1核验。

## PASS：重点数学解释与证据强度

### P1．0.0975576不是曾被接受的纪录（P/V）

- **原句（51–55）**：“Its arithmetic and several adapters survived review. Its central area estimate did not.”；“Unqueness for each output did not limit the total burden placed on that source.”（稿中实际拼写为 “Uniqueness”）。
- **定位**：F1 `history/blocked-09755/STATUS_BLOCKED.md:5,15–33`。
- **蕴含**：逐输出唯一witness／low endpoint只给 demand-once；不同输出与跨度仍可共用 `(endpoint,height)`，缺注入、有界重数或all-cut源容量定理。账单／付款人比喻准确传达此区别。稿件没有声称已经反驳该数值的所有可能证明，也没有当作合法上升后回落的纪录。8月16日来自 `COMMIT_CHRONOLOGY.json` 中 `0bbd492d…` 条目，仅是归档版本日期。

### P2．径向物理源ν与source-once解释准确（P/V）

- **原句（63–65）**：“dν = min(r,1) dr dθ”；“whose density relative to planar area is min(1,1/r) away from the origin. Thus ν never exceeds area.”
- **定位**：N11 `history/final-radial-price-theorem/final_theorem_checklist_20260817_zh.md:65–69,91–101`；N14 `history/shared-terminal-082812/class_independent_terminal_price_report_zh.md:23–26,59–73`；T7 `history/one-tenth/THEOREM_01.md:23–25` 也直接列出两种形式。
- **蕴含**：价格约束是在同一真实物理并集上，而不是各个标签各有独立完整容量。“away from the origin”避免了原点的记号奇性。此处是对原有公式的释义，未新算数值。
- **证据限定**：N11:5,11 把OPR PASS作为该审查的已给前提；本报告只确认稿件叙述与晋升链一致，不声称本次独立重验OPR。

### P3．任意集经开外包恢复，不偷加原选弦可测性（P/V）

- **原句（67）**：“This did not assume the original choice of needles was measurable. It constructed a new legal family where integration was available, reran the geometric split there, and finally took the infimum over open enclosures.”
- **定位**：N11上述文件:73–101；T7:13–19,104–110；T8 `history/one-tenth/tenth-reviews/b2_universal_tenth_end_to_end_review.md:9–11,54–66`。
- **蕴含**：新选择在G中，而非宣称仍属于原来不规则E；必须重做height split。稿件对此准确。最终非严格 `≥1/10` 没有把取下确界后的不等式夸成严格号。

### P4．shared-terminal v2是实际修复，不只是多算几位（P/V）

- **原句（71）**：“kept a finite cutoff and used fresh, disjoint dyadic radial bands for the tail”；（73）：“Version v2 split at every event where a sliding endpoint crossed the radial grid and used concavity between events … normalized the common price scale to one.”
- **定位**：N14上述文件:7–19,46–73；N15 `history/shared-terminal-082812/class_independent_terminal_strict_report_zh.md:23–32`；N16 `history/shared-terminal-082812/class_independent_terminal_strict_report_v2.md:3–5,24–28`；N17同目录 `CERTIFIED_PROMOTION.md:3–9`。
- **蕴含**：无界block的 `1/R` 最坏核退化；finite-high共享一次terminal，尾部新区域。v1三点pole reduction明确废止，v2按 `M` 或 `M−1` 穿网格事件及事件间凹性覆盖连续域，并将尺度从999999/1000000归一为1。稿件没有把float 0.0828125写成精确已证53/640。
- **证据限定**：本次阅读的是历史证明／晋升声明，没有重放Arb或任何测试。

### P5．IL anchors不是两倍标签收费（P/V）

- **原句（81）**：“These are two lifts on the physical circle of length 2π, not two different directions on the projective circle of length π.”；“The proof first takes their union …”；（83）列出 `k(r)(|V|+|B|)`。
- **定位**：T6 `history/one-tenth/low-source-b2/integrated-low/PROOF.md:18–20,33–41,50–120`。
- **蕴含**：N是近端点半径，不是线段内部的最短半径；每个V方向供远ideal lift，仅B供反向near lift。ideal lifts确实不交，不等于真实端点极角；重复全cone和跨标签lobe在真实并集里先合并，再用一次区间并集引理。稿件保留了这些承重区别，截面系数与原文相同。

### P6．IL complementary prices的数学含义准确（P/V）

- **原句（87–89）**：“A complete unit segment satisfies M+N≥1.”；“complementary weights λ and 1−λ keep the total charge at most one. The weights balance the coefficients for B and U …”
- **定位**：T6:124–157,169–205,216–235；T7:47–62,104–110。
- **蕴含**：U的N<2/5给M>3/5；最后同一个外bank里W(U)包含于W(V)，互补价格支付而非两个满价账相加。λ=C4/C6由类别系数相消得到，并非优化器输出。最终低系数超过1/(10π)，其余全局方向类在不同径向区域支付。稿件没有把低引理本身独立冒充全局定理。

### P7．PL反例是真弦连续族，且不反驳IL或1/10（P/V）

- **原句（91）**：“At radius 1/4, a direction cut of length 43/1000 occupies a physical angular union of length 1/50 …”; “The successful proof was accepted without importing the failed pointwise claim.”
- **定位**：T9 `history/one-tenth/low-source-b2/paired-pointwise/COUNTEREXAMPLE.md:3–13,25–62,261–291`；T8:9–11,68；T7:114–116。
- **蕴含**：实际完整单位弦、正测度Borel cut、同一物理并集，非离散样点／任意独立弧反例。T9单独写IL仍OPEN是其历史快照，后续T8接受的IL并不依赖PL。稿件拒绝从依赖关系推导全部思想发生因果，是正确的证据纪律。

### P8．四个旧Lean端点没有被冒充本轮kernel通过（A；N32/N64另有直接源码P）

- **原句（47）**：“four independent early Lean endpoints can be located … Their local import closures contain no OneTenth module.”；（97）：“It did not locate the original native execution logs for the N32 and N64 endpoints … This writing task has not rebuilt those projects.”
- **定位**：`audits/historical-lean-audit.md:37–77,81–103,109–111`；直接实读 `historical-lean-2026-08-04/StarKakeyaLower/EndpointCapacityFinal141.lean:18–32`、同目录 `EndpointCapacityFinal3527.lean:18–43`。
- **蕴含**：N32最终源码确实实例化本地付款producer；N64完整qπ用 `≤`，3527/50000是另一个严格corollary。迁移审计称四个旧本地闭包不含OneTenth，支持不是事后从最终1/10降格出来的源码路线；它不等于本轮编译验收，也不保证各路线完全不共享早期引理。正文后段对此有明确限制，当前无需BLOCK。
- **轻微措辞建议**：47行可用 “four early Lean source endpoints” 提前提示源码层，避免读者必须读到97行才看到证据分层。

### P9．最终1/10有既有原生执行证据，但源哈希核同是此前迁移审计的工作（R/A）

- **原句（97）**：“The final 1/10 project has retained native receipts whose recorded source hashes agree with all 44 current modules.”
- **定位**：`snapshot-payload/349eff3f670d44d9-build.json:2–6` 的passed、exit_code与两个audit roots；`snapshot-payload/b7518ca834a5bf8d-environment.json:2–6` 的工具链身份；`evidence/final/StarKakeyaLower.OneTenthAudit.log:25` 与 `StarKakeyaLower.OneTenthParentAudit.log:32–33` 的三公理原生输出；`audits/historical-lean-audit.md:74–77,111` 报告44源比较、差异0。
- **判断**：可保留，但最好写 “The migration audit reports that …” 明确哈希核对的执行主体。本轮只读收据与既有审计，没有重算44源、没有kernel执行。不能把纸面验收json、旧文档转录和这些原生log说成同一种证据。

## 范围与操作说明

- 唯一新写文件为本报告；没有改英文稿、原件、映射或历史审计。
- 没联网，没运行数值、Lean、Arb或证书；没读 `.lake` 文件或递归遍历大树。收据正文内出现 `.lake` 字符串只是旧路径记录，没有打开这些路径。
- 两次批量文本输出发生截断；承重缺失部分用更窄范围补读。不把被截掉的原文当作已读证据，不声称对长审查／build JSON全文逐行审核。
- 这是一份限定重点段落的来源蕴含审查，不是最终定理重证、不恢复全部历史构建，也不把尚缺N32/N64原始日志解释成证明有错。
