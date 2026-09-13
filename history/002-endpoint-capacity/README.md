# Spike 002 — endpoint-paired radial capacity for arbitrary star-shaped Kakeya sets

Date: 2026-08-03 · branch `research/endpoint-capacity` · base `f5693b9`

---

## Result in one paragraph

The endpoint-paired dyadic **Hall–Carleson candidate is refuted**, but the
replacement radial-sliver covering theorem is proved and, after a finite shared
radial schedule plus disjoint high-radius ledgers, gives the unconditional
selector-independent bound

```text
L*(E) >= C_FS >= 141/2000 = 0.0705 > 7/100 > 131 pi / 6250
```

for every star-shaped Kakeya set, where `C_FS` is the exact variational supremum
over all admissible finite radial schedules defined in
`FINITE-SCHEDULE-VARIATIONAL.md`.  The rational numbers are explicit certified
witnesses, not proposed closed forms for `C_FS`.  Floating-point local
optimisation and a formal continuum BVP suggest a value near `0.0705668`, but
that decimal is not yet a validated enclosure or a proved approximation of
`C_FS`.

The current explicit certificate uses 32 closest-radius classes and the finite
Choquet-cover lemma, so it remains valid for arbitrary non-measurable selectors
without continuum Fubini.  The earlier `1/15`, `1717/25000`, and `7/100`
theorems remain independently certified intermediate results.  The explicit
32-segment assembly splits at height `eta=141046/10^6`:
a high needle pays through its single origin triangle.  Below that height, 32
low closest-radius classes share a finite radial schedule, while all larger
closest-radius classes use pairwise-disjoint high ledgers.  No direction class
is assumed measurable.  Independent reviews
found no BLOCK, including adversarial checks of layer boundaries, unbounded
centres, non-measurable partitions, and completely overlapping angular images.
The exact rational margin is checked by `certify_141_over_2000.py`.

The stronger class-scoped corollary also remains valid: if every selected
needle meets `B(O,r0)`, then

```text
L*(E) >= pi * int_{r0}^{1/2} r (1-2r)/(1+2r) dr,
```

which at `r0=0` is `0.0284264097... pi`.  The previously conjectured
two-sided-sliver figures `0.056852 pi` and `0.037902 pi` are refuted for this
mechanism by the foot-at-endpoint no-go theorem in `TWO-SIDED-NO-GO.md`.

**Go/no-go: GO for the radial-sliver programme, with exact variational headline
`C_FS` and certified witness `141/2000`; the earlier rational assemblies are
intermediate witnesses. NO-GO for endpoint-only Hall expansion.**

---

## Evidence boundary — read before quoting anything here

| Artefact | Evidence level | Establishes | Does **not** establish |
|---|---|---|---|
| `THEORY.md` §1–§3, §5, §6 | **paper-level proof**, self-contained | Theorem 1 (exact capacity identity), Lemma 2, Theorem 3 (`pi/4`, sharp), Lemma 7 (sharp covering), Theorem A + Corollary A1 | nothing machine checked; no Lean; constants not claimed sharp |
| `THEORY.md` §7 | paper-level proof, **unoptimised constants** | far-needle branch | the final universal constant |
| `UNIVERSAL-ONE-FIFTEENTH.md` | **paper-level proof; two independent reviews PASS** | unconditional intermediate `L*(E) >= 1/15` | Lean or peer-reviewed publication |
| `UNIVERSAL-OPTIMIZED.md` | **paper-level proof; two independent reviews PASS** | intermediate unconditional `L*(E) >= 1717/25000` | Lean or peer-reviewed publication |
| `UNIVERSAL-SEVEN-HUNDREDTHS.md` | **paper-level proof; three independent reviews PASS** | intermediate unconditional `L*(E) >= 7/100` for arbitrary selectors | Lean or peer-reviewed publication |
| `FINITE-SCHEDULE-VARIATIONAL.md` | **paper-level exact variational theorem; three reviews PASS** | `L*(E) >= C_FS`, with `C_FS` defined as a finite-schedule supremum | a closed form or validated decimal enclosure |
| `FIXED-PARTITION-WATERFILLING.md` | **paper-level exact inner-optimisation theorem; two reviews PASS** | global fixed-partition max--min via monotone water-level frontier; free-regime uniqueness | the discrete-to-continuum limit |
| `UNIVERSAL-141-OVER-2000.md` | **paper-level proof; three independent reviews PASS** | explicit certified witness `C_FS >= 141/2000` for arbitrary selectors | the exact value of `C_FS` |
| `StarKakeyaLower/EndpointCapacityFinal141.lean` and its imported endpoint-capacity modules | **Lean 4 proof; root/audit builds PASS; three independent release reviews** | unconditional `Witness141.universal_one_forty_one_over_two_thousand`: `ENNReal.ofReal (141/2000) < volume.toOuterMeasure E` for every `StarShapedKakeya E` | optimality, the exact value of `C_FS`, or peer-reviewed publication; axioms are exactly `propext`, `Classical.choice`, `Quot.sound` |
| `certify_141_over_2000.py`, `one_forty_one_over_two_thousand_certificate.json` | exact rational/log-tail certificate; independently recomputed | all 32 low payments, high schedule, and final `141/2000` margins | proof-assistant verification |
| `certify_seven_hundredths.py`, `seven_hundredths_certificate.json` | exact rational/log-tail certificate; independently recomputed | all frozen low/high schedule comparisons and final `7/100` margin | proof-assistant verification |
| `certify_one_fifteenth.py`, `one_fifteenth_certificate.json` | exact rational certificate + floating diagnostics | frozen comparisons for the intermediate theorem | proof-assistant verification |
| `certify_optimized_radial_bound.py`, `optimized_radial_bound_certificate.json` | exact rational certificate; mutation tested | every frozen comparison and margin for `1717/25000` | proof-assistant verification |
| `THEORY.md` §8 | **refutation** with an explicit legal family and closed forms | the endpoint Hall–Carleson candidate is dead | that no endpoint-based route whatsoever can work |
| `THEORY.md` §9 | historical conditional target, now superseded | records what constant-1 two-sided covering would have implied | a proved bound |
| `TWO-SIDED-NO-GO.md` | **paper-level universal refutation; two independent reviews** | side-vanishing embeds the one-sided sharp class; near-diameter naive separation fails but refined overlap bounds remain open | that restricted near-diameter gains are impossible |
| `ANTIPODAL-FLOOR-NO-GO.md` | **paper-level exact counterexample; independently reviewed** | pointwise/a.e./essinf/local-average antipodal floors have best constant zero | that the global capacity average vanishes |
| `two_sided_sliver_adversary.py`, `two_sided_sliver_results.json` | explicit periodic adversary + numerical refinement | convergence to the one-sided sharp density `1/(1+2mu)` | a proof by itself |
| `FATALITY.md` | counterexample catalogue with calculations | which lemmas die on which model | any positive statement |
| `benchmark_capacity.py`, `RESULTS.json` | numerical evidence + exact `Q(sqrt2)` reconstruction | independent agreement with the production upper certificate; spectra; mutation gates | nothing about star-shaped Kakeya sets by itself |

`benchmark_capacity.py` imports **no** production module and reads **no** cached
certificate or spectrum. The rational-seven profile pair is retyped from the
manuscript displays `eq:aprofile`/`eq:sprofile`/`eq:Apoly`/`eq:Bpoly`; every
downstream object (branch maps, switch points, densities, the radial function of
the literal finite-cell union) is rebuilt from scratch. Production numbers appear
only in the dictionary `COMPARISON_ANCHORS` and are used solely for a posterior
agreement report.

**Reporting rule honoured throughout:** no finite-grid value is reported as a
continuum lower bound. The only bracket claimed for the continuum envelope is a
left/right Riemann bracket that is valid because `R` is nonincreasing (both
branches are decreasing in `y`), and the monotonicity is itself re-checked on
the same grid and reported. Sampled radial functions are inward biased and are
labelled as lower bounds.

---

## Reproduce

```bash
cd /home/argustest/research/star-kakeya-wt-endpoint-capacity
python3 spikes/002-endpoint-capacity/certify_one_fifteenth.py
python3 spikes/002-endpoint-capacity/certify_optimized_radial_bound.py
python3 spikes/002-endpoint-capacity/certify_seven_hundredths.py
python3 spikes/002-endpoint-capacity/certify_141_over_2000.py
cd materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean
lake build StarKakeyaLower.EndpointCapacityFinal141
lake build StarKakeyaLowerAudit
cd ../../../..
python3 -m venv .venv                     # .venv is gitignored
.venv/bin/pip install -q numpy mpmath     # numpy is used only for the finite-cell reconstruction
.venv/bin/python spikes/002-endpoint-capacity/benchmark_capacity.py \
    --ns 51,101,201,401,801 \
    --out spikes/002-endpoint-capacity/RESULTS.json
/home/argustest/miniconda3/bin/python \
    spikes/002-endpoint-capacity/two_sided_sliver_adversary.py \
    --out /tmp/two_sided_sliver_results_reproduced.json
```

Environment actually used: Python `3.11.14`, `numpy 2.4.6`, `mpmath 1.3.0`
(the repository lock pins `numpy==2.5.1`, which is not published on this index;
the actual version is recorded in `RESULTS.json → meta`). Runtime `~512 s`.
Everything except the finite-cell reconstruction is standard library only
(`fractions.Fraction` and exact `Q(sqrt 2)` polynomial arithmetic).

Fast smoke run (`~55 s`):

```bash
.venv/bin/python spikes/002-endpoint-capacity/benchmark_capacity.py --quick --ns 51 --out /tmp/q.json
```

### Actual console output of the full run

```text
wrote spikes/002-endpoint-capacity/RESULTS.json (55296 bytes) in 511.6s

== reconstruction ==
  six-piece  int R^2 dy      = 0.0904778111246790  pattern=eseses
  bracket                    = [0.0904709089, 0.0904847186]
  production strict upper    = 0.0904778120
  paper reported decimal     = 0.0904778111246769545
  literal n=   51: normalised area (lower) = 0.090569  sup h = 1.318e-02
  literal n=  101: normalised area (lower) = 0.090509  sup h = 6.657e-03
  literal n=  201: normalised area (lower) = 0.090494  sup h = 3.345e-03
  literal n=  401: normalised area (lower) = 0.090490  sup h = 1.677e-03
  literal n=  801: normalised area (lower) = 0.090489  sup h = 8.394e-04
== ledger ==
  published lower  = 0.0209600000 * pi
  certified ceiling= 0.0904778120 * pi
  Theorem A (r0=0) = 0.0284264097 * pi   ratio 1.356x
  break-even r0    = 0.148742
```

(The byte count and runtime vary slightly between runs; all numeric fields are
deterministic except the randomised covering probe, which is seeded with
`20260803`.)

---

## What the reconstruction independently confirms about the production upper bound

* The **six-piece identity** value `int_0^1 R^2 dy = 0.0904778111246790` agrees
  with the manuscript's reported decimal `0.0904778111246769545` to `2.0e-15`,
  and lies strictly below the production strict rational certificate
  `90477812/10^9`.
* The **active branch pattern** recovered from scratch is `e s e s e s` with
  exactly `5` interior switches — the pattern printed in the manuscript's switch
  isolation lemma.
* The **shape inequalities** are satisfied with margins
  `min(-s'') = 0.913897`, `min H = 0.146447`, `min(-H') = 0.700104`,
  `min(H - s') = 0.011557` (at `t = 0`), `min J = 0.004857` (at `t = 0.0255`).
* The **literal finite-cell radial function**, computed by pure chord geometry
  with no branch classification whatsoever, converges to the same value from
  above: `0.090569 → 0.090489` for `n = 51 → 801`.

This is a genuinely independent reconstruction of the near-extremizer, which is
what licenses using it as an adversary in `FATALITY.md`.

---

## Target ledger

| quantity | value `/pi` | note |
|---|---|---|
| published lower bound | `0.020960` | `131/6250` |
| intermediate unconditional bound | `1/(15 pi) = 0.0212206591` | area bound `1/15` |
| intermediate optimized radial-ledger bound | `1717/(25000 pi) = 0.0218615230` | area bound `1717/25000` |
| intermediate finite-schedule bound | `7/(100 pi) = 0.0222816920` | area bound `7/100` |
| **exact finite-schedule variational constant** | **`C_FS` (implicit supremum)** | rigorous `C_FS >= 141/2000`; formal BVP candidate near `0.0705668` |
| explicit 32-segment witness | `141/(2000 pi) = 0.0224408470` | certified area bound `141/2000`; exact gain `1/2000` over `7/100` |
| certified upper ceiling | `0.0904778120` | production continuum certificate |
| reconstructed here | `0.0904778111246790` | six-piece, independent |
| head-room ratio | `4.0318x` | certified ceiling / explicit witness coefficient |
| **Theorem A at `r0 = 0`** | **`0.0284264097`** | `1.3562x` published, `31.4%` of the ceiling |
| Theorem A at `r0 = 1/8` | `0.0228106854` | `1.0883x` published |
| Theorem A break-even `r0` | `0.1487420408` | above this the route loses |
| ceiling of the uniform-radial-floor route | `0.0214976` | `+2.6%` only, and the route is false |
| pointwise antipodal-pair floor | best universal constant `0` | **refuted** by far common-centre radial support |
| ceiling of every endpoint-only route | `0` | dead (`kappa → 1` family) |
| universal two-sided sliver improvement | former envelopes `0.0568524` / `0.0379019` | **refuted for this mechanism** by foot-at-endpoint embedding |

Any universal constant above `0.0904778112` is automatically false. Anything
above `0.0214976` cannot be proved through a uniform radial floor. The certified
near-extremizer numerically permits larger constants, but the universal
two-sided covering route is dead.

---

## Adversarial mutations (all four visibly change or reject a check)

| mutation | quantity | before | after | flips |
|---|---|---|---|---|
| MUT-1 remove pairing | sharp constant of the `h ≡ 0` class | `0.250000` | `0.125000` | yes |
| MUT-2 remove interior contacts | capacity of the legal `kappa = 0.99` family, `n = 101` | `0.123122` | `0.004593` | yes (`pass → fail` against `0.020960`) |
| MUT-3 coarsen one scale | Hall expansion `lambda_m` on the near-extremizer | `0.0069533` (`m = 12`) | `0.143936` (`m = 1`) | yes (`fail → pass`, ratio `20.66`) |
| MUT-4 null-fibre a.e. relaxation | value of the relaxation | `0.0904778` / `0.25` | `0.000000` | yes |

---

## File map

```text
spikes/002-endpoint-capacity/
  README.md                 this file: commands, outputs, evidence boundary, ledger
  THEORY.md                 exact formulation, Theorems 1/3/A, Lemmas 2/7, the refuted
                            candidate, quantifier inventory, conditional statements
  UNIVERSAL-ONE-FIFTEENTH.md unconditional intermediate `L*(E) >= 1/15`
  UNIVERSAL-OPTIMIZED.md  intermediate unconditional `L*(E) >= 1717/25000`
  UNIVERSAL-SEVEN-HUNDREDTHS.md intermediate finite-schedule `L*(E) >= 7/100`
  FINITE-SCHEDULE-VARIATIONAL.md exact `C_FS` definition and universal theorem
  FIXED-PARTITION-WATERFILLING.md exact inner switch max--min theorem
  UNIVERSAL-141-OVER-2000.md explicit 32-segment witness `C_FS >= 141/2000`
  certify_141_over_2000.py exact 32-segment Fraction/atanh certificate
  one_forty_one_over_two_thousand_certificate.json generated current receipt
  certify_seven_hundredths.py exact intermediate finite-schedule certificate
  seven_hundredths_certificate.json generated intermediate receipt
  certify_one_fifteenth.py  exact rational coefficient and margin certificate
  one_fifteenth_certificate.json generated intermediate receipt
  certify_optimized_radial_bound.py exact optimized rational certificate
  optimized_radial_bound_certificate.json generated optimized receipt
  TWO-SIDED-NO-GO.md       exact universal side-vanishing refutation; near-diameter proof gap
  ANTIPODAL-FLOOR-NO-GO.md far common-centre pointwise/essinf/local-average refutation
  two_sided_sliver_adversary.py periodic microstructure adversary
  two_sided_sliver_results.json full adversarial refinement table
  FATALITY.md               F1..F10 adversarial models with calculations, mutation ledger
  benchmark_capacity.py     independent reconstruction + spectra + mutations + probes
  RESULTS.json              all numbers, with per-section `evidence` tags
```

Two independent falsification attempts on the new lemma are included and both
come back negative: an abstract greedy adversary against Lemma 7
(`sliver_covering_probe`, every continuum-feasible solution has density exactly
`1/(1+2mu)` for `mu ∈ {0.1, 0.25, 0.5, 1, 2}`), and a geometric adversary
against Theorem A itself with the rigid `arcsin` sliver shape
(`theorem_a_geometric_probe`, minimal feasible density exceeds the Theorem-A
density by `2.8%`–`10.1%` at `r ∈ {0.05, 0.1, 0.2, 0.3, 0.4}`).

`RESULTS.json` top-level keys: `meta`, `comparison_anchors`, `definitions`,
`profiles`, `shape_inequalities`, `envelope`, `continuum_refinement_table`,
`switch_structure`, `agreement_with_production_upper`, `near_extremizer_profile`,
`level_set_margins`, `spectra`, `finite_cell_reconstruction`,
`sliver_covering_probe`, `finite_schedule_seven_hundredths`,
`finite_schedule_141_over_2000`, `finite_schedule_variational`, `target_ledger`,
`adversary_endpoint_collapse`,
`adversary_astroid`, `adversary_far_needles`, `adversary_far_common_center`,
`adversary_zero_height`,
`mutations`, `candidate_margins`, `theorem_a_geometric_probe`, `verdict`.

---

## Known obstructions and what is *not* done

1. **The exact finite-schedule headline is `C_FS`.** It is the variational
   supremum over all admissible finite schedules and satisfies
   `C_FS >= 141/2000`.  The rational values `1/15`, `1717/25000`, `7/100`, and
   `141/2000` are explicit certified witnesses, not proposed closed forms.
   None of these results makes the stronger class-scoped `0.0284264 pi`
   constant universal.
2. **The universal two-sided covering improvement is refuted.** A legal chord
   whose perpendicular foot is an endpoint has one empty radial-window side and
   realizes every one-sided sharp microstructure.  Hence the sharp universal
   covering constant cannot improve on `1+2mu`.  See `TWO-SIDED-NO-GO.md`.
   The former figures `0.0568524 pi` and `0.0379019 pi` are not bounds from this
   mechanism.
3. **Pointwise and local antipodal floors are refuted.** The radial hull of a
   disk centred far from the star centre has support in an arbitrarily narrow
   cone, so an open projective interval has zero radial extent in both antipodal
   directions.  Full-circle averaging survives only as the capacity identity.
   See `ANTIPODAL-FLOOR-NO-GO.md`.
4. **No Lean.** Per the workflow instruction, formalisation was not started;
   §10 of `THEORY.md` lists the quantifier pattern that a formalisation would
   have to reproduce, and the proofs use only outer measures, Carathéodory
   splitting, convexity of `arcsin` and the component decomposition of a subset
   of `R` — no measurable selection, no compactness, no continuity.
