# M6 numeric kernel — branch status (`research/m6-kernel`)

**Scope of this report.** Branch-local record of the *numeric* part of
milestone M6 for spike 001: `PROOF.md` Hypothesis B and the Hypothesis C gates
**C1, C3, C4** (plus `C_ext > 0` and the M4 numeric domain).  Baseline commit
`af20002`.  Nothing is committed or pushed by the work described here.

**Explicitly out of scope, and not attempted:**

* gate **C2**, the raw radial integral `I > T` (`AnnularCaseIIntegral`, the
  two-piece cut of `LEAN-PLAN.md` §M6);
* the endpoint containment geometry (`htrace` / `hcritical`, the deep
  parameterisation of `Figure5EndpointEnvelope` → `Figure5LocalContact` →
  `UniversalEndpointClosure`);
* the concrete `g`, `hg`, `hmeas` of M6 item 5 and the `∫⁻` form of item 6;
* any assembly (M7).

The M6 exit criterion of `LEAN-PLAN.md` is therefore **not** met; only its
item 1 (`annularParameterDomain` and the non-integral Hypothesis-C
comparisons) is closed.  The shared `LEAN-STATUS.md` and `LEAN-PLAN.md` are
deliberately **not** edited in this branch.

---

## 1. New modules

| file | lines | imports | closure |
|---|---|---|---|
| `StarKakeyaLower/AnnularKernel.lean` | 442 | `Mathlib` only | trivially CLEAN |
| `StarKakeyaLower/AnnularAnalytic.lean` | 213 | `AnnularKernel`, `AnnularGeometry` | CLEAN |

Transitive `StarKakeyaLower` closure of `AnnularAnalytic` (computed, not
asserted):

```
AnnularGeometry, AnnularKernel, CaseIIGeometry, CircleDilation, GreedyResidual,
LiGeometry, ParametricCaseII, PolarOuterMeasure, QuotientCircle, StarKakeyaSet,
TriangleArea, Trichotomy
```

Every entry is CLEAN in the `LEAN-STATUS.md` inventory.  In particular the
closure contains **no** `StrongerKernel`, **no** `CaseIIAnalytic`, and no
module carrying the frozen `100π/5599` witness constants.  `annularCExt` is
*reused* from the CLEAN `AnnularGeometry` (`:656`); its formula is not
duplicated.

The only other change is `StarKakeyaLower.lean` (production root): the two new
modules are added to the import list and to its doc-comment, exactly as the
M1–M5 sibling modules already were.

Token scan of both new files: no `sorry`, no `admit`, no `axiom`, no
`native_decide`, no `decide`, no `strong*` tuple constant.  (The strings
`StrongerKernel`, `CaseIIAnalytic`, `native_decide` occur only inside
doc-comments that say those things are *not* used.)

## 2. Definitions (exact production tuple)

`AnnularKernel.lean`, all in `namespace StarKakeyaLower`:

```lean
def annTarget          : ℝ := 131 / 6250
def annA               : ℝ := 13177 / 100000
def annRLambda         : ℝ := 10227 / 50000
def annR₀              : ℝ := 999 / 2000
def annEps             : ℝ := 1 / 10 ^ 10
def annM               : ℝ := 1 - annEps
def annLambda          : ℝ := 29496 / 36773
def annRadicand        : ℝ := 4 * annRLambda ^ 2 * (1 + annA ^ 2) - annA ^ 2
def annD               : ℝ := annA * (1 - Real.sqrt annRadicand) / (2 * (1 + annA ^ 2))
def annR₁Radicand      : ℝ := annRLambda ^ 2 - annD ^ 2
def annR₁Denominator   : ℝ := 1 - 2 * Real.sqrt annR₁Radicand
def annR₁              : ℝ := Real.sqrt (1 + 4 * annD ^ 2) / annR₁Denominator
def annRho             : ℝ := annR₁ - 1
```

`annM = 1 - annEps` and `annRho = annR₁ - 1` hold by `rfl`
(`annM_eq_one_sub_annEps`, `annRho_eq_annR₁_sub_one`), so the M4 interface
shape `(1 - eps)`, `(R₁ - 1)` is literally the same term.

Exact rational identity (kernel-checked, `ann_radicand_eq`):

```
annRadicand = 955555034740470041 / 6250000000000000000
```

## 3. Rational enclosures (all two-sided, all kernel-checked)

Every radical comparison is reduced to a *squared rational* comparison via
`Real.lt_sqrt` / `Real.sqrt_lt'` and closed by `norm_num`/`nlinarith` on
rationals.  No decimal or floating-point evaluation, no interval oracle and no
`native_decide` is involved anywhere.

| quantity | proved enclosure | theorems | certify.py Arb interval (evidence only) |
|---|---|---|---|
| `√Q` | `0.39100998140 < · < 0.39100998141` | `ann_sqrt_radicand_lower/_upper` | `Q = 0.15288880555847520656…` |
| `d` | `0.03943852316 < · < 0.03943852317` | `ann_d_lower`, `ann_d_upper` | `0.039438523168265103…` |
| `√(r_λ²−d²)` | `0.20070180490 < · < 0.20070180491` | `ann_sqrt_r₁_radicand_lower/_upper` | `r_λ²−d² = 0.040281214490306…` |
| `√(1+4d²)` | `1.00310597069 < · < 1.00310597070` | `ann_sqrt_numerator_lower/_upper` | — |
| `1 − 2√(r_λ²−d²)` | `0 < ·`, two-sided | `ann_r₁_denominator_pos/_lower/_upper` | `0.59859639019906053…` |
| `R₁` | `1.675763481 < · < 1.675763482` | `ann_r₁_lower`, `ann_r₁_upper` | `1.675763481231215108…` |
| `ρ` | `0.675763481 < · < 0.675763482` | `ann_rho_lower`, `ann_rho_upper` | `0.675763481231215108…` |

The Arb column is **outward evidence only**: it is reproduced from
`certificate.json` for cross-checking and is used by no proof.

## 4. Hypothesis B

```lean
structure AnnularParameterDomain where …   -- 34 fields
def annularParameterDomain : AnnularParameterDomain
```

`#check annularParameterDomain : AnnularParameterDomain`.

Field-by-field correspondence with `PROOF.md` Hypothesis B and the
`certify.py` `MANDATORY_GATES` list:

| `PROOF.md` / gate | field | note |
|---|---|---|
| `0 < h₀` (`domain_h0_positive`) | `a_pos` | |
| `h₀ ≤ r_λ` (`domain_order_h0_rlambda`) | `a_lt_rLambda` | strict, strengthens the note |
| `r_λ ≤ r₀` (`domain_order_rlambda_r0`) | `rLambda_lt_r₀` | strict |
| `r₀ < ½` (`domain_r0_below_half`) | `r₀_lt_half` | |
| `r₀ ≥ 3/20` | `r₀_ge_three_twentieths` | |
| `0 ≤ λ ≤ 1` | `lambda_pos`, `lambda_lt_one` | strict |
| `λh₀+(1−λ)r₀ = r_λ` | `affine_identity` | exact rational identity |
| `0 ≤ Q < 1` | `radicand_nonneg`, `radicand_lt_one` | |
| `0 < d < h₀/2` | `d_pos`, `d_lt_half_a` | |
| `r_λ²−d² ≥ 0` | `r₁_radicand_pos` | strict |
| `1−2√(r_λ²−d²) > 0` | `r₁_denominator_pos` | |
| `R₁ > 1` (`domain_R1_above_one`) | `one_lt_r₁` | |
| `ρ > r₀` | `rho_gt_r₀` | |
| `h₀ < mρ` | `a_lt_m_rho` | |
| `0 < h₀/ρ < 1` | `arg_rho_pos`, `arg_rho_lt_one` | |
| `0 < h₀/(mρ) < 1` | `arg_m_rho_pos`, `arg_m_rho_lt_one` | |

**Gates that the Python mandatory list leaves implicit and that are proved
here explicitly:** `target_pos : 0 < annTarget`, `eps_pos : 0 < annEps`,
`eps_lt_one : annEps < 1`, `m_pos : 0 < annM`, `m_lt_one : annM < 1`,
`r₀_pos : 0 < annR₀`, `r₁_pos : 0 < annR₁`, `rho_pos : 0 < annRho`, together
with the definitional bridges `m_eq`, `rho_eq` and the three rational
enclosure fields.

## 5. Hypothesis C, without C2 — exact signatures

```lean
theorem ann_gate_C1 : annTarget < annA / (2 * Real.pi)

theorem ann_gate_C3 : annTarget < annularCExt annA annR₀ annRho annM / 4

theorem ann_gate_C4 : annTarget < (annRho ^ 2 - annR₀ ^ 2) / 2

theorem ann_cExt_pos : 0 < annularCExt annA annR₀ annRho annM

theorem ann_gate_min_exterior :
    annTarget <
      min (annularCExt annA annR₀ annRho annM / 4) ((annRho ^ 2 - annR₀ ^ 2) / 2)
```

The exterior divisor is **literally `/ 4`** in the statements, matching the
`min (annularCExt … / 4) …` coefficient of
`annular_exterior_greedy_lower_bound` (`AnnularGreedyInfinite.lean:437`); no
`exterior_divisor` parameter and no rescaled variant is introduced.

The arcsine bound and its generic input:

```lean
theorem sin_ge_sub_cube_div_six {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x

def annArcsinArgUpper : ℝ := 1949945 / 10000000   -- rational upper bound for h₀/(mρ)
def annArcsinUpper    : ℝ := 196255 / 1000000     -- rational upper bound for H(h₀)

theorem ann_arcsin_arg_lt_upper : annA / (annM * annRho) < annArcsinArgUpper
theorem ann_arcsin_lt_upper : Real.arcsin (annA / (annM * annRho)) < annArcsinUpper
theorem ann_arcsin_pos : 0 < Real.arcsin (annA / (annM * annRho))
```

`sin_ge_sub_cube_div_six` is the generic cubic sine estimate, **reproved
locally** (monotonicity of `sin y − y + y³/6` on `Ici 0` via
`Real.one_sub_sq_div_two_le_cos`); the identical estimate in the frozen
`CaseIIAnalytic` is *not* imported, and the name differs so that both can
coexist in one environment.

Route of the arcsine gate (every step kernel-checked):
`h₀/(mρ) < annArcsinArgUpper` (from the rational lower bound `annRhoLower`
for `ρ`) `< U − U³/6 ≤ sin U`, hence `arcsin(h₀/(mρ)) < U` by
`Real.arcsin_lt_iff_lt_sin'`, with `U = annArcsinUpper` and
`U ∈ Ioc (−π/2) (π/2)` supplied by `Real.pi_gt_three`.

C1 uses `Real.pi_lt_d20` directly and nothing else transcendental.

### Proved margins (exact rationals)

| gate | proved rational lower bound of the left/right side | margin over `T = 131/6250` |
|---|---|---|
| C1 | `annA / (2 · 3.14159265358979323847)` | `23261237973708576043 / 1963495408493620774043750 ≈ +1.18468512·10⁻⁵` |
| C3 | `(annA/(2U) − m r₀²/2)/4` | `399170320329172537251 / 12560320000000000000000 ≈ +3.17802668·10⁻²` |
| C4 | `(annRhoLower² − r₀²)/2` | `165236032253237361 / 2000000000000000000 ≈ +8.26180161·10⁻²` |
| arcsine, cubic step | `U − U³/6 − annArcsinArgUpper` | `32300069749/48000000000000000 ≈ +6.7291812·10⁻⁷` |
| arcsine, argument step | `annArcsinArgUpper · m · annRhoLower − annA` | `≈ +1.6208268·10⁻⁷` |

For comparison (evidence only, `certificate.json`): `high = 0.0209718468512…`,
`exterior_rate = 0.0527417216910…`, `C_fan = 0.1035780162829…`,
`H(h₀) = 0.1962515979047…`.  Each proved bound is on the correct side of the
corresponding Arb interval, and the Lean margins are slightly smaller because
the rational enclosures are deliberately coarse.

## 6. Numeric domain of the M4 interface

```lean
theorem ann_m4_r₀_lt_rho : annR₀ < annR₁ - 1
theorem ann_m4_a_lt_scaled_rho : annA < (1 - annEps) * (annR₁ - 1)
theorem ann_m4_cExt_pos : 0 < annularCExt annA annR₀ (annR₁ - 1) (1 - annEps)

theorem ann_m4_exterior_domain :
    0 < annEps ∧ annEps < 1 ∧ 0 < annA ∧ 0 < annR₀ ∧ annR₀ < annR₁ - 1 ∧
      annA < (1 - annEps) * (annR₁ - 1) ∧
      0 < annularCExt annA annR₀ (annR₁ - 1) (1 - annEps)

theorem ann_m4_coefficient_gt_target :
    annTarget <
      min (annularCExt annA annR₀ (annR₁ - 1) (1 - annEps) / 4)
        (((annR₁ - 1) ^ 2 - annR₀ ^ 2) / 2)
```

`ann_m4_exterior_domain` is exactly the hypothesis list of
`annular_exterior_A_out_greedy_lower_bound` (`heps0`, `heps1`, `ha`, `hr0`,
`hlt`, `harhoScaled`, `hCext`) at the production tuple, in the literal
`eps / a / r₀ / R₁` shape; `ann_m4_coefficient_gt_target` is its conclusion's
coefficient.  No M4 theorem is instantiated here — that is assembly (M7).

## 7. Builds and receipts

Toolchain `leanprover/lean4:v4.30.0-rc2`, Mathlib rev
`5450b53e5ddc75d46418fabb605edbf36bd0beb6` (unchanged), in
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean`.

| command | result |
|---|---|
| `lake build StarKakeyaLower.AnnularKernel` | `Build completed successfully (8313 jobs)` |
| `lake build StarKakeyaLower.AnnularAnalytic` | `Build completed successfully (8325 jobs)` |
| `lake build` (production root) | `Build completed successfully (8354 jobs)` |
| `lake build StarKakeyaLowerAudit` | `Build completed successfully (8349 jobs)` |

No warning is emitted by either new module (checked on a clean replay of both
`.olean`s).

**Axiom receipts.** A temporary file importing both modules and issuing
`#print axioms` for **all 94 explicit source declarations** of the two modules was run
with `lake env lean`.  Every one reports exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

i.e. only the three standard Mathlib axioms; no `sorryAx`, no custom axiom, no
`Lean.ofReduceBool` (which would indicate `native_decide`).  `Audit.lean` was
not modified — the receipt file is temporary and outside the library, as
instructed.

**Diff.** Two new files plus a six-line import/doc change in
`StarKakeyaLower.lean`; no other tracked file is touched, nothing is committed
or pushed, and no other worktree is involved.

## 8. Evidence discipline

`certify.py` / `certificate.json` are quoted above **only** as outward
interval evidence that the Lean enclosures agree with the intended tuple.  They
are not inputs to any proof, and nothing in this branch claims that the Arb
certificate proves a Lean statement.  Conversely, the Lean theorems here prove
only the *numeric* content of Hypotheses B and C1/C3/C4 — no geometric or
measure-theoretic statement, and in particular **no lower bound on the area of
a star-shaped Kakeya set** — which still needs C2, the endpoint geometry and
M7.
