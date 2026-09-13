# Star-shaped Kakeya bounds

A planar set is a *star-shaped Kakeya set* if it is star-shaped about some point
and contains a closed unit segment in every unoriented direction. Let `A_*` be
the infimum of the two-dimensional Lebesgue **outer** measure over this class;
no measurability and no continuous motion is assumed. This repository contains
a proof of the certified window below.  Write

```text
q = 120451837956416753429080037440388963415852081138854072730916985277243537437963483617721423
    / 5364112507936858236407997438019246365694885550022694534725778173308620348675781250000000000.
```

```text
qπ ≤ A_* < 77π/851
```

together with two Lean 4 developments and a bilingual manuscript.

The headline lower inequality is non-strict for every individual set; the
shorter `3527/50000` corollary is strict for every individual set.  The upper
inequality is strict at the displayed constant because it
is the area of one explicit compact admissible set. The two bounds do not
determine `A_*`, and no optimality is claimed for either endpoint.

The lower endpoint is proved by the endpoint-capacity route: a 64-class finite
radial schedule, a nonmeasurable finite fractional-cover argument, and disjoint
high-radius ledgers.  Two older independent Lean routes are retained in full.
The **baseline route** splits the direction circle by a mass proportion and
gives `100π/5599`.  The **additive confined/exterior refinement** splits the
plane by a measurable closed ball, charges confined directions only inside it
and escaping directions only outside it, and gives `131π/6250`.

## Results

**Lower bound (headline).**
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

only as a compact certificate.  Direct high-precision evaluation with the true
logarithm gives `0.07054487627351847` for the frozen schedule, but that value is
NUMERIC rather than a validated transcendental theorem.

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

**Comparison.** The headline `qπ ≈ 0.07054486807936307` improves the retained
annular bound `131π/6250` by a factor of approximately `1.07133248708`.  The
annular bound in turn
improves the baseline `100π/5599` by `733469/625000 = 1.1735504` and Li's
published `π/98` by `6419/3125 = 2.05408`.  With the new headline, the ratio
between the upper and lower endpoints is approximately `4.02944852462`.
No optimality is claimed for any tuple.

**Upper bound.** `StarKakeya.FinalAreaTheorem.rationalSeven_area_lt_simpleArea`
proves, for the explicit polynomial-profile set with 100001 cells,

```text
area E_100001 < 77π/851 < (5 - 2√2)π/24.
```

Its admissibility, including a continuous endpoint-reversing half-turn, is
formalized at that cell count. `RationalSeven` is an internal code name for the
explicit rational polynomial profile pair; it has no mathematical content.

## Formal source map

Paths are relative to
`materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31`.

| Claim | Owning declaration | Module |
|---|---|---|
| `A_* ≥ qπ` | `Witness3527.universal_certifiedCoefficient_mul_pi` | `lower-bound/04-lean/StarKakeyaLower/EndpointCapacityFinal3527.lean` |
| `A_* ≥ 141/2000` (older) | `Witness141.universal_one_forty_one_over_two_thousand` | `lower-bound/04-lean/StarKakeyaLower/EndpointCapacityFinal141.lean` |
| `A_* ≥ 131π/6250` | `universal_annular_lower_bound`, `universal_annular_lower_bound_normalForm` | `lower-bound/04-lean/StarKakeyaLower/AnnularAssembly.lean` |
| `A_* ≥ 100π/5599` (baseline) | `universal_strong_lower_bound` | `lower-bound/04-lean/StarKakeyaLower/UniversalAssembly.lean` |
| `A_* < 77π/851` | `rationalSeven_strictly_improves_cunninghamSchoenberg` | `upper-bound/03-lean/StarKakeya/FinalAreaTheorem.lean` |
| refinement tuple and enclosures | `annA`, `annRLambda`, `annR₀`, `annEps`, `annLambda`, `ann_rho_lower` | `…/StarKakeyaLower/AnnularKernel.lean` |
| four gates | `ann_gate_C1`, `ann_gate_C3`, `ann_gate_C4`, `annTarget_lt_annILower` | `…/AnnularAnalytic.lean`, `…/AnnularCaseIIntegral.lean` |
| one-sided annular geometry, exterior payment | `UnitNeedle.exists_arcSector_of_outside`, `UnitNeedle.annular_payment` | `…/AnnularGeometry.lean` |
| Carathéodory split and countable ledger | `outerMeasure_ge_add_of_inter_of_diff`, `tsum_outerMeasure_inter_le` | `…/BallSplit.lean` |
| exterior greedy budget | `annular_exterior_A_out_greedy_lower_bound` | `…/AnnularGreedyInfinite.lean` |
| confined contribution | `annular_confined_lower_bound` | `…/AnnularEndpoint.lean` |

The lower development is 87 modules under `StarKakeyaLower/`, totalling 33,034
lines, plus the 186-line aggregation root `StarKakeyaLower.lean`: 88 files and
33,220 lines in all. `paper/README.md` carries the manuscript claim-to-evidence
map; the endpoint-capacity spike README records the newer formal theorem.

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

- All three lower theorems — endpoint capacity `141/2000`, the additive
  refinement `131π/6250`, and the baseline `100π/5599` — are conventional Lean
  proofs over Mathlib and depend only on `propext`, `Classical.choice` and
  `Quot.sound`. The lower audit target emits 600 `#print axioms` receipts and the
  set of distinct axiom lists over all of them has exactly one element.
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
