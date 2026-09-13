# Star-shaped Kakeya bounds

A planar set is a *star-shaped Kakeya set* if it is star-shaped about some point
and contains a closed unit segment in every unoriented direction. Let `A_*` be
the infimum of the two-dimensional Lebesgue **outer** measure over this class;
no measurability and no continuous motion is assumed. This repository contains
a proof of the certified window below.  Let `C_pair,64` be the exact implicit
constant of the frozen 65-atom paired schedule defined in the Results section:

```text
C_pair,64 = min { eta/2, π p_high, π p_N, π p_C, π p_1, ..., π p_63 }.
```

Its coefficients use the true logarithm and arcsine, not a rational surrogate.
Then the current headline window is

```text
C_pair,64 ≤ A_* < 77π/851,
```

with the fail-closed outward enclosure

```text
0.07054487627351847246750992457726307620733
≤ C_pair,64 ≤
0.07054487627351847251573589552953391541289.
```

For comparison, write

```text
q = 120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423
    / 5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000.
```

The previous `qπ` lower bound and the upper construction have Lean 4
developments; the stronger paired headline currently has a paper-level geometry
proof plus an exact/outward Python certificate and independent validator, but no
Lean formalization.  The headline lower inequality is non-strict for every
individual set.  The upper inequality is strict at the displayed constant because it
is the area of one explicit compact admissible set. The two bounds do not
determine `A_*`, and no optimality is claimed for either endpoint.

The lower endpoint is proved by the endpoint-capacity route: a 64-class finite
radial schedule refined into 65 arbitrary direction atoms, adaptive-cut paired
persistence on the new near-balanced atom, a nonmeasurable finite
fractional-cover argument, and disjoint high-radius ledgers.  Four retained Lean
lower bounds are kept in full.
The **baseline route** splits the direction circle by a mass proportion and
gives `100π/5599`.  The **additive confined/exterior refinement** splits the
plane by a measurable closed ball, charges confined directions only inside it
and escaping directions only outside it, and gives `131π/6250`.

## Results

**Lower bound (headline; exact implicit paired constant).**  Use the frozen
rational schedule arrays in `spikes/012-paired-cfs-exact-certificate/primary_data.json`
and put

```text
H = 931611/100000000,   q_pair = 51/100,   R_p = 49/100,
J = [alpha_1, alpha_1 + 3/500),
R_c = 250043391187/500000000000.
```

For `K(u,R)=u(R-u)/(R+u)` and `F_R(a,b)=integral_a^b K(u,R) du`, define

```text
P = integral_H^alpha_1
      2u(R_p-u)/(R_p+u) (1 - 2 asin(H/u)/π) du,
p_N = F_(1/2)(alpha_1,t_1) - F_(1/2)(J) + P,
p_C = F_(1/2)(alpha_1,t_1) - F_(1/2)(J) + F_(R_c)(J),
p_j = F_(1/2)(alpha_(j+1),t_1)
      + sum_(i=1)^j F_(R_i)(t_i,t_(i+1))    (1 ≤ j ≤ 63).
```

For the complete unchanged high tail, put

```text
A_k = eta + k/2,   B_k = A_k + 1/2,
R_eta(A) = sqrt(A^2 + 1 + 2 sqrt(A^2 - eta^2)),
p_high = inf_(k in N) F_(R_eta(A_k))(B_k,R_eta(A_k)).
```

The checker proves one uniform rational lower contract for every `k ≥ 0`; it
does not replace this infimum by a finite sample.

The exact headline is the full mechanism constant

```text
C_pair,64 = min { eta/2, π p_high, π p_N, π p_C, π p_1, ..., π p_63 },
A_* ≥ C_pair,64.
```

The paired-persistence theorem uses an adaptive projective cut on a measurable
hull, so it requires neither a measurable selector nor measurable direction
atoms.  Its inner payment lies on `[H,alpha_1)`, while `J` is a replacement
rather than a second same-shell action.  A refined finite Lovász–Choquet assembly
then applies to the 65 arbitrary atoms `N,C,D_1,...,D_63`.

The checker and independent radial re-atomizer prove the enclosure displayed at
the top of this README.  Both ends are exact rationals; the full lower witness
is retained in
`spikes/012-paired-cfs-exact-certificate/results/certificate.json`, with
canonical rational-string SHA-256
`903101dc87aa7bda85c82202e410b85a63a6dcf601f69eb73fbee2f2a946df9d`.
The active atom is `D49`.  Six real production fault families and three
binding/provenance attacks produce 13 fail-closed rejection assertions, and the
8-test suite passes both normally and under `python -O`.

This is a theorem for one frozen modified schedule, not a claim that the enlarged
paired family is globally optimized.  It is paper-level plus exact computation,
not yet Lean-formalized.  It also certifies the true-log value that was previously
only NUMERIC: the paired modification removes the old class-zero surrogate
bottleneck, but the final `D49` value equals the old frozen schedule's true-log
minimum.

**Lower bound (Lean-certified endpoint witness, retained).**
`StarKakeyaLower.Witness3527.universal_certifiedCoefficient_mul_pi` proves,
for an arbitrary star-shaped Kakeya set `E`,

```text
ENNReal.ofReal (q * π) ≤ volume.toOuterMeasure E.
```

The proof uses no measurability of `E` or of the arbitrary direction selector.
Here `q` is the full fraction displayed above, not the shorter internal
coefficient `common`.  Its final owner is
`StarKakeyaLower/EndpointCapacityFinal3527.lean`, and its axiom
footprint is `propext`, `Classical.choice`, `Quot.sound`.

The same module retains the strict rational corollary

```text
ENNReal.ofReal (3527 / 50000) < volume.toOuterMeasure E,
```

only as a compact Lean certificate.  The paired paper-level theorem and outward
certificate above now validate the frozen true-log value that older revisions
listed only as NUMERIC; this Lean module itself remains at `qπ`.

**Lower bound (additive refinement, retained).**
`StarKakeyaLower.universal_annular_lower_bound`
proves, for an arbitrary star-shaped Kakeya set `E`,

```text
ENNReal.ofReal (π * annTarget) < volume.toOuterMeasure E,   annTarget = 131 / 6250
```

and `StarKakeyaLower.universal_annular_lower_bound_normalForm` states the same
bound with the constant in normal form,

```text
ENNReal.ofReal (131 * π / 6250) < volume.toOuterMeasure E.
```

No measurability of `E`, and no measurability or continuity of the pointwise
needle choice, is required. The proof splits on triangle height, then splits the
plane by the measurable closed ball `closedBall 0 r̂₀`; the confined class pays
the raw radial integral inside that ball and the escaping class pays outside it,
through the exterior parts of greedily selected triangles kept disjoint by
one-sided angular shadows, plus the annular fan of the directions that survive
every deletion. Four numerical gates close the argument at one fixed rational
parameter tuple. The final source owner is
`StarKakeyaLower/AnnularAssembly.lean`. The top-level axiom footprint is
`propext`, `Classical.choice`, `Quot.sound`.

**Lower bound (baseline, unchanged).**
`StarKakeyaLower.universal_strong_lower_bound` proves

```text
ENNReal.ofReal (π * 100 / 5599) < volume.toOuterMeasure E
```

under the same hypotheses, by splitting on triangle height and then on a fixed
radius and closing the three resulting branches at a different fixed rational
tuple. This theorem is untouched by the refinement, still compiles, and carries
the same three-axiom footprint; its final source owner remains
`StarKakeyaLower/UniversalAssembly.lean`. These two retained theorems are
import-disjoint above their shared base.

**Comparison.** The headline
`C_pair,64 ≈ 0.07054487627351847251401006580736949` improves the retained
annular bound `131π/6250` by a factor of approximately `1.07133261152`.  It also
strictly improves the previous full `qπ` witness; the certified rational margin
is greater than `8.19415539625998221856e-9`.  The
annular bound in turn
improves the baseline `100π/5599` by `733469/625000 = 1.1735504` and Li's
published `π/98` by `6419/3125 = 2.05408`.  The ratio between the upper and
lower endpoints is approximately `4.02944805658`.
No optimality is claimed for any tuple.

**Endpoint-capacity proof-family ceiling.** The completed-graph Stieltjes
reformulation proves that finite radial schedules have the same closure as the
Stieltjes primal. A fail-closed outward dual certificate then gives

```text
qπ ≤ C_FS ≤ 71/1000.
```

The upper certificate covers 70 eta slabs, retains the graph tail above `u=1/2`,
and has worst checked dual bound
`0.07056837476844964729460395573054... < 0.071`. Its three load-bearing
mutations (dropping that tail, using an unenclosed radical, and subtracting two
upper prefixes) are all rejected. Relative to the shorter strict witness
`3527/50000`, the old proof family has headroom at most `23/50000 = 0.00046`;
relative to the retained `qπ` witness, the numerical gap is approximately
`0.000455131920636924`. This is a ceiling for the **old finite-schedule /
Stieltjes proof family**, not a geometric upper bound for `A_*`, and deterministic
simultaneous purification remains open.  The paired headline uses an enlarged
support-separated action and is not claimed to lie in that old family. Evidence lives in
`spikes/010-stieltjes-strong-duality/`.

**Structural unit-scale incidence theorem (paper-level, not Lean).** A genuinely
different selector-independent argument proves the following. Let `A` be any
set of projective directions, with one complete unit chord in each direction.
If every chord has an attained point at radius in `[r,2r]`, where `r ≥ 1`, and
`E_A` is the union of the corresponding origin triangles, then

```text
L^{2*}(E_A ∩ B(0,r/2)) ≥ r |A|* / (8(2 + 5π)).
```

The proof uses inward half-chord persistence, a projective interval-component
covering lemma, and open-cover polar Tonelli. It assumes neither a measurable
selector nor measurable direction classes. The far-common-centre family shows
that the linear `r|A|` scale has the correct power; the earlier `r²|A|` target is
false. The theorem and adversarial audit are in
`spikes/010-unit-scale-incidence/`. It has been independently mathematically
reviewed but is not yet formalized in Lean or assembled into a stronger numeric
headline for `A_*`.

**Endpoint-tail scope result.** On any column-closed relaxation that already
contains the same-shell ordinary `R=b` column, the endpoint-tail EP column is
redundant because `J(a,b)=F_b(a,b)` and its eligible state set is smaller. This
does **not** prove zero gain for `C_FS`: the replacement action may violate the
finite switch/cap architecture or overlap the high-tail ledger. The exact scope
and the explicit overlap regression are recorded in
`spikes/010-tail-augmented-schedule/`.

**Upper bound.** `StarKakeya.FinalAreaTheorem.rationalSeven_area_lt_simpleArea`
proves, for the explicit polynomial-profile set with 100001 cells,

```text
area E_100001 < 77π/851 < (5 - 2√2)π/24.
```

Its admissibility, including a continuous endpoint-reversing half-turn, is
formalized at that cell count. `RationalSeven` is an internal code name for the
explicit rational polynomial profile pair; it has no mathematical content.

## Headline evidence map

| Claim/evidence | Owner |
|---|---|
| adaptive-cut proportional paired persistence | `spikes/011-small-radius-paired-persistence/THEOREM.md` |
| exact 65-atom schedule and `C_pair,64` theorem | `spikes/012-paired-cfs-exact-certificate/THEOREM.md` |
| outward rational enclosure | `spikes/012-paired-cfs-exact-certificate/checker.py` |
| independent re-atomization and witness binding | `spikes/012-paired-cfs-exact-certificate/validator.py` |
| frozen primary schedule and paired controls | `spikes/012-paired-cfs-exact-certificate/primary_data.json` |

## Formal source map

Paths are relative to
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31`.

| Claim | Owning declaration | Module |
|---|---|---|
| `A_* ≥ qπ` | `Witness3527.universal_certifiedCoefficient_mul_pi` | `lower-bound/04-lean/StarKakeyaLower/EndpointCapacityFinal3527.lean` |
| `A_* ≥ 141/2000` (older) | `Witness141.universal_one_forty_one_over_two_thousand` | `lower-bound/04-lean/StarKakeyaLower/EndpointCapacityFinal141.lean` |
| `A_* ≥ 131π/6250` | `universal_annular_lower_bound`, `universal_annular_lower_bound_normalForm` | `lower-bound/04-lean/StarKakeyaLower/AnnularAssembly.lean` |
| `A_* ≥ 100π/5599` (baseline) | `universal_strong_lower_bound` | `lower-bound/04-lean/StarKakeyaLower/UniversalAssembly.lean` |
| `A_* < 77π/851` | `rationalSeven_area_lt_simpleArea` plus the explicit-set admissibility theorem | `upper-bound/03-lean/StarKakeya/FinalAreaTheorem.lean` |
| refinement tuple and enclosures | `annA`, `annRLambda`, `annR₀`, `annEps`, `annLambda`, `ann_rho_lower` | `…/StarKakeyaLower/AnnularKernel.lean` |
| four gates | `ann_gate_C1`, `ann_gate_C3`, `ann_gate_C4`, `annTarget_lt_annILower` | `…/AnnularAnalytic.lean`, `…/AnnularCaseIIntegral.lean` |
| one-sided annular geometry, exterior payment | `UnitNeedle.exists_arcSector_of_outside`, `UnitNeedle.annular_payment` | `…/AnnularGeometry.lean` |
| Carathéodory split and countable ledger | `outerMeasure_ge_add_of_inter_of_diff`, `tsum_outerMeasure_inter_le` | `…/BallSplit.lean` |
| exterior greedy budget | `annular_exterior_A_out_greedy_lower_bound` | `…/AnnularGreedyInfinite.lean` |
| confined contribution | `annular_confined_lower_bound` | `…/AnnularEndpoint.lean` |

The lower development is 87 modules under `StarKakeyaLower/`, totalling 33,034
lines, plus the 186-line aggregation root `StarKakeyaLower.lean`: 88 files and
33,220 lines in all. `paper/README.md` carries the manuscript claim-to-evidence
map; the endpoint-capacity spike README records the newer retained Lean theorem,
while the evidence map above owns the stronger non-Lean headline.

## Papers

- `paper/star_shaped_kakeya_bounds.tex` / `.pdf` — English manuscript.
- `paper/star_shaped_kakeya_bounds_zh.tex` / `.pdf` — Chinese counterpart.
- `paper/README.md`, `paper/README_zh.md` — build and alignment notes.

Both editions carry the same structure: problem and main theorem, common
geometry and the two proof pipelines, the upper design (Part I), the lower
design (Part II — the baseline route in Sections 6–8 and the additive
confined/exterior refinement in Sections 9–10), assembly, open problems, and
three appendices for exact constants, formalisation architecture, and
reproduction.

The Stieltjes closure/ceiling, unit-scale and multiscale incidence theorems,
paired-persistence theorem, paired exact certificate, and endpoint-tail scope
results in `spikes/009-*` through `spikes/012-*` postdate the manuscripts. They
are repository research results, not silently incorporated paper claims.

## Layout

- `materials/` — auditable package tree: Lean sources, computation scripts,
  theorem reports and manifests.
- `archive/` — deterministic combined ZIP of that package tree.
- `sources/` — primary literature and provenance notes.
- `notes/` — working notes on evidence boundaries and open directions.
- `spikes/001-joint-inner-outer/` — the additive refinement spike: the
  paper-level proof note `PROOF.md`, the Arb interval certificate `certify.py` /
  `certificate.json`, the falsification test `test_annular_geometry.py`, the
  numerical scout `scout.py` / `result.json`, and the Lean plan and status
  documents.
- `spikes/009-*` — Stieltjes completion, the continuum polar-box scale
  obstruction, and the sharp exterior endpoint-tail ledger/no-go.
- `spikes/010-*` — the outward `C_FS` family ceiling, the unit-scale incidence
  theorem, and the scoped endpoint-tail column-relaxation audit.
- `spikes/011-*` — the additive dyadic ledger, fixed-schedule hybrid audit, and
  adaptive-cut small-radius paired-persistence theorem.
- `spikes/012-paired-cfs-exact-certificate/` — the current headline schedule,
  outward checker, independent validator, mutations, and frozen receipts.
- `spikes/012-paired-cfs-reoptimization/` — local floating scouts and the
  first-cell complement-gain obstruction; not a certified headline.
- `scripts/reproduce-core.sh` — one-command core reproduction.
- `scripts/tex_structure_counts.py` — bilingual structure/literal comparison.
- `requirements-lock.txt` — pinned Python dependencies.

## Build

Papers:

```bash
cd paper
tectonic -X compile star_shaped_kakeya_bounds.tex
tectonic -X compile star_shaped_kakeya_bounds_zh.tex
```

Core reproduction (Python certificate generators, refinement evidence scripts,
and Lean targets):

```bash
bash scripts/reproduce-core.sh
```

The script creates the pinned environment from `requirements-lock.txt`, checks
the archive, runs the baseline exact/interval generators, reruns the refinement
Arb certificate and the annular falsification test, and builds all four Lean
targets. It fails closed at every step. The refinement certificate is executed
from a temporary copy of `certify.py`, so the tracked
`spikes/001-joint-inner-outer/certificate.json` is never written; the freshly
produced certificate is then compared with the tracked one field by field, with
only the wall-clock field `elapsed_seconds` allowed to differ.

Individual refinement evidence scripts, using the same environment:

```bash
.venv/bin/python spikes/001-joint-inner-outer/test_annular_geometry.py
cd "$(mktemp -d)" && cp <repo>/spikes/001-joint-inner-outer/certify.py . && \
  <repo>/.venv/bin/python certify.py
```

Current paired headline certificate and full fail-closed test suite:

```bash
bash spikes/012-paired-cfs-exact-certificate/run_all.sh
```

The full run executes 8 tests normally and under `python -O`; it is intentionally
slow.  Set `PAIRED_CFS_SKIP_TESTS=1` only for a quick checker/validator/mutation
replay, not for a release audit.

Lean, lower bound:

```bash
cd materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean
lake build +StarKakeyaLower
lake build StarKakeyaLowerAudit
```

Lean, upper bound:

```bash
cd materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/upper-bound/03-lean
lake build +StarKakeya
lake build +StarKakeya.Audit
```

Both developments pin the Lean toolchain `leanprover/lean4:v4.30.0-rc2` and the
Mathlib revision `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## Trust boundary

The two halves are not checked to the same standard, and the manuscript says so
explicitly.

- The retained Lean lower theorems — endpoint capacity `qπ` and `141/2000`, the
  additive refinement `131π/6250`, and the baseline `100π/5599` — are
  conventional Lean proofs over Mathlib and depend only on `propext`,
  `Classical.choice` and
  `Quot.sound`. The lower audit target emits 661 `#print axioms` receipts and the
  set of distinct axiom lists over all of them has exactly one element.
- The stronger `C_pair,64` headline uses an independently reviewed paper-level
  geometric/Choquet argument plus exact rational outward arithmetic and an
  independent validator.  It is theorem-level repository evidence, but not a
  kernel-checked Lean theorem; its trust base includes the reviewed prose bridge
  and the Python implementations named in the headline evidence map.
- The upper theorem additionally depends on reflection axioms generated by
  scoped `native_decide` evaluation of large decidable algebraic checks, so for
  those steps the practical trust base includes the Lean compiler and native
  runtime as well as the kernel.
- Generated certificate data are checked-in exact rational files consumed by
  Lean proofs; they are inputs, not oracles. Python generators expose byte-exact
  `--check` modes and fail-closed mutation tests.
- The refinement's Arb certificate and falsification test are of a different
  kind: they are *evidence about explicit real numbers*, and they are not
  consumed by the Lean proof or by the manuscript's exact-rational proof, both
  of which reprove every domain condition and every gate from scratch. They do
  discharge Hypotheses B and C of the paper-level proof note
  `spikes/001-joint-inner-outer/PROOF.md`, which is a conditional prose proof
  and is not machine checked; that chain must not be conflated with a
  kernel-checked proof.
- Neither development contains `sorry`, `admit`, or a project-defined `axiom`,
  and the lower development contains no `native_decide`.

A successful build is evidence about a formal artefact. It is not peer review,
and it establishes nothing about optimality or priority.
