# Approach Portfolio

Campaign: Star-shaped Kakeya lower bound

Provider: `[Codex]`

## Portfolio policy

Routes are grouped by mechanism.  Exact arithmetic, geometric containment,
outer-measure iteration, global optimization, and Lean formalization are not
substitutes for one another.

Allowed gap strengths: `local`, `bridge`, `theorem-strength`,
`target-equivalent`.

Allowed statuses: `exploring`, `active`, `blocked`, `dead`, `proved`, `parked`.

Allowed independence classes: `blind`, `orthogonal-oracle`, `contaminated`,
`internal`.

## Route registry

| Route | Family | Representation / mechanism | Load-bearing gap | Gap strength | Decisive evidence or falsifier | Status | Reopen trigger | Independence |
|---|---|---|---|---|---|---|---|---|
| R1 | circle covering | Open-set components on \(\mathbb T_L\) and saturated same-centre dilation | Lean formalization remains; paper proof is closed | bridge | Full quotient-space proof or wrapped counterexample | proved | n/a | blind |
| R2 | Li geometry | Endpoint formulas for \(J_\Gamma\), \(q(\theta_\Gamma)\), and saturation on \(\mathbb T_\pi\) | Lean formalization remains; paper endpoint reconstruction is closed | theorem-strength | Coordinate derivation covering both cases and saturation | proved | n/a | blind |
| R3 | exact parameter chain | Rational, logarithmic, radical and inverse-trigonometric certificates | Remaining radical/arcsin links and final assembly in Lean | bridge | Symbolic proofs, mutations, and Lean analytic kernels | proved | n/a | internal |
| R4 | iteration audit | Scale-covariant star-shaped Kakeya subproblem and geometric recurrence | Direction-scope gap: confined family pays \(p\) times the baseline | theorem-strength | Full-direction repair or a valid corrected recurrence | blocked | A construction or theorem supplies the missing full-direction configuration | blind |
| R5 | non-iterative fallback | Alternate parameters with rational branch enclosures and exact margins | Paper proof closed; universal Lean assembly remains in R10 | bridge | Complete paper audit plus exact candidate certificate | proved | n/a | internal |
| R6 | four-parameter optimum | Interval branch-and-bound after analytic elimination of \(p\) | Finite global cover of curved domain and certified family ceiling | bridge | Reproducible interval B&B with boundary coverage | blocked | An analytic boundary atlas or finite interval cover | internal |
| R7 | nonlinear section geometry | Keep the exact \(J_\Gamma\)-to-\(\theta_\Gamma\) relation across radii | Uniform cross-radius incompatibility inequality with explicit positive gain | theorem-strength | Strict analytic improvement with global admissibility | blocked | An explicit dual weight or classified equality family | internal |
| R8 | multiscale/Bellman | Multiple thresholds, \(p(r)\), dual measures, or Bellman recursion | Outer-measure coupling that pays nesting without reusing direction mass | theorem-strength | New coercive inequality paying correlations | blocked | A Bellman functional with a closed limiting argument | blind |
| R9 | literature | Primary-source citations, corrections, later work and citation graph | Search misses cannot prove absence of later work | local | Statement-level anchors, not search misses | proved | A new citation or source version | orthogonal-oracle |
| R10 | Lean formalization | Five-layer Mathlib development | Circle, Li geometry, analytic remainders, and universal assembly remain | theorem-strength | `lake build` and `#print axioms` on the final theorem | active | n/a | internal |
| R11 | parametric Case II | Projective-angle separation, weighted greedy covering, and residual radial fan | Paper proof closed; Euclidean/measure formalization remains in R10 | theorem-strength | Complete selected-triangle proof with corrected \(\varepsilon\) bookkeeping | proved | n/a | blind |
| R12 | stronger fixed theorem | Exact rational \(100/5599\) certificate inside the corrected one-threshold framework | Universal Lean assembly remains in R10 | theorem-strength | Self-contained paper proof, exact/mutation gates, Arb witness, and fresh audit | proved | n/a | internal |

## Round log

| Date / round | Families advanced | Concrete result | Portfolio rebalance | Next decisive actions |
|---|---|---|---|---|
| 2026-07-31 / 1 | R1--R4, R9, R10 opened | Contract separates the circle lemma, Li same-centre geometry, exact constants, iteration, and Lean layers | Optimization and beyond-framework routes parked until the phase-one proof is audited | Blind geometry audit; exact arithmetic SSOT; compile first Lean kernel |
| 2026-07-31 / 1 checkpoint | R1--R5, R10 | Fresh-context audit confirms the factor-\(3\) removal after explicit mod-\(\pi\) typing; exact non-iterative parameters close both finite cases; Lean arithmetic and axiom audit compile | R4 blocked at its direction-scope gap; R5 becomes the sole phase-one assembly; R6--R8 remain parked | Audit Li Lemma 2.5/Theorem 3.5; formalize analytic remainder and circle-measure layers |
| 2026-07-31 / 2 | R3, R5, R10, R11 | Lemma 2.5 is scoped-confirmed on \(E_{\rm all}\); direct use of printed Theorem 3.5 at \(\rho>1/2\) is rejected, then replaced by a complete parametric projective-angle/greedy/fan proof; Lean log series compiles | R5 and R11 become paper-level proved; R6 activates; R10 remains the literal completion bottleneck | Compile Case II minimax and remaining analytic bridges; start rigorous family optimization without weakening the Lean gate |
| 2026-07-31 / 3--4 | R3, R6, R10, R12 | Numerical scout corrected and widened; exact and Arb rational witnesses exceed \(100/5599\); fresh audit closes the stronger paper theorem; Lean adds stronger arithmetic, atan branches, line dilation, and parametric minimax | R12 proved; R6 blocked only at global family coverage; R10 remains theorem-strength open | Freeze the stronger proof; identify the literal quotient-circle and Euclidean/measure Lean interfaces |
| 2026-07-31 / 5 | R7--R9 | Current primary-source audit finds Li Section 4.2 only proposes the double-integral route; cross-radius and Bellman routes are reduced to explicit missing lemmas | R7 and R8 blocked at theorem-strength coupling gaps; search-negative literature evidence remains dated | Reopen only with an explicit cross-radius dual or Bellman functional; otherwise advance the Lean adapter |

## Cross-pollination log

| Date | Source route | Receiving route | Shared object | Why independence is no longer required |
|---|---|---|---|---|
| 2026-07-31 | R1 | R2 | Same-centre dilation theorem | The blind R2 audit independently reconstructed the geometry before checking the R1 containment mechanism |
| 2026-07-31 | R2 | R5 | Correctly typed cross-section inequality on \(\mathbb T_\pi\) | The independent endpoint and quotient audit is complete; the object can now enter the non-iterative assembly |
| 2026-07-31 | R11 | R5 | Parametric Case II theorem for \(\rho>1/2\) | The blind route supplied a direct full-triangle proof after the printed source scope failed |
| 2026-07-31 | R6 | R12 | Rational parameters near the numerical basin | Exact and Arb certificates replaced the numerical candidate before the stronger theorem was accepted |
| 2026-07-31 | R12 | R10 | Stronger rational margins and analytic branch obligations | The paper theorem is frozen; Lean can now target its exact dependency DAG without changing the mathematics |
