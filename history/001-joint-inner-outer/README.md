# Spike 001: joint inside/outside lower bound

Date: 2026-08-02

## Evidence boundary

Read this section before quoting anything from this directory. Five kinds of
evidence are present and they are **not** interchangeable.

| Artefact | Evidence level | What it establishes | What it does **not** establish |
|---|---|---|---|
| `scout.py`, `result.json` | numerical spike | a basin where the four coefficients are simultaneously large | nothing proved; no global optimality |
| `PROOF.md` | paper-level proof, **relative to quoted main-paper results** | Theorem 10.1: `L²*(E) > 131π/6250`, conditional on Hypothesis C | not self-contained, not machine checked |
| `certify.py`, `certificate.json` | Arb interval certificate | Hypotheses B and C for the fixed rational tuple | nothing about Kakeya sets; not a Lean proof |
| `test_annular_geometry.py` | falsification test | no counterexample found in the sampled region | not a proof |
| `LEAN-PLAN.md` | plan, now with executed milestones marked **[DONE]** | interfaces, reuse map, milestones M0–M7 | snippets still marked `-- SKETCH` are proposals, not code |
| `LEAN-STATUS.md` + `M6-*-STATUS.md` | **Lean proof** | milestones M1–M7: compiled modules, build output, `#print axioms` receipts | nothing about the paper text |

**`PROOF.md` is not self-contained.** It is a complete paper-level proof
*relative to* explicitly quoted results of `paper/star_shaped_kakeya_bounds.tex`
— the triangle reduction (Lemma 3.3, `lem:triangle`), the outer-measure polar
slicing lemma (Lemma 5.6, `lem:polar`) and the aggregate first-arc bound
(Proposition 5.3, `prop:endpoint`, with Lemma 5.4 `lem:dilation` and the
display `eq:section`). Those are used verbatim and are not reproved. Paper
Proposition 5.7 (`prop:li25`) is **deliberately not used**. Provenance of every
step is tabulated in `PROOF.md` §13.

**A Lean theorem now exists for this route** (added after this README was first
written). `StarKakeyaLower.universal_annular_lower_bound`
(`…/04-lean/StarKakeyaLower/AnnularAssembly.lean:233`) proves
`ENNReal.ofReal (Real.pi * (131/6250)) < volume.toOuterMeasure E` for every
star-shaped Kakeya set `E`, unconditionally, with axiom receipt
`[propext, Classical.choice, Quot.sound]`. It does **not** use `PROOF.md`,
`certify.py` or `certificate.json` as inputs: the Lean development reproves what
it needs from scratch, so the "not self-contained" caveat below applies to
`PROOF.md` only, not to the Lean theorem. The published
`100π/5599` (`universal_strong_lower_bound`) is unchanged and still compiles;
`131/6250 = 0.020 96` is the larger coefficient. Evidence: `LEAN-STATUS.md` §22.

---

## Question

For a star-shaped Kakeya set `E` with star centre `0`, split directions at a
radius `R1` into confined (`Δ_α ⊆ closedBall 0 R1`) and escaping. Can the
confined class pay only inside `B(0,r0)` and the escaping class only outside,
so that the two payments add by Carathéodory splitting instead of competing in
a minimax?

**Answer: yes**, at paper level. The chain (`PROOF.md`):

```text
outerMeasure(E)  = outerMeasure(E ∩ closedBall(0,r0))
                 + outerMeasure(E \ closedBall(0,r0))       (Caratheodory)
                 ≥ I·L_in + min(C_ext/4, C_fan)·L_out
                 ≥ π·min( h0/(2π), I, C_ext/4, C_fan ).
```

Two ingredients make it work:

* the **sharp one-sided angular width** of an escaping unit needle,
  `W_rho(delta) = asin(delta/rho) − atan(delta/(1+sqrt(rho²−delta²)))`,
  attained exactly at contact with `∂B(0,rho)` (Lemma 4.3), which
  Remark 4.6 shows is unimprovable; and
* the **exterior payment coefficient** `C_ext = h0/(2·H(h0)) − m·r0²/2` with
  `H(delta) = asin(delta/(m·rho))`, proved from two calculus facts only —
  `sin u / u` decreasing and `asin(m sin u) ≤ m u` (§5). No factor
  `κ = 2·asin(m)/π` is needed in this branch.

Only the weakening `A(s) ≤ asin(delta/rho)` of Lemma 4.3 is actually used in
Proposition 5.3; `W_ρ` itself is recorded but left unexploited.

---

## Fixed candidate parameters

```text
h0        = 13177/100000
r_lambda  = 10227/50000
r0        = 999/2000
eps_del   = 10^-10,   m = 1 - eps_del
lambda    = 29496/36773            (exact interpolation certificate)
T_joint   = 131/6250 = 0.02096
```

Parameter SHA-256 (canonical exact-rational JSON):
`57361ed6e8e023c2db769f42502a415d9b47cbf167818dada322d6ff779f12a5`

---

## Real runs

All three scripts exit `0` from a clean invocation. The outputs below are
copied from the runs recorded in `result.json` and `certificate.json`.

### 1. Direct-geometry falsification test

```bash
/usr/bin/python3 spikes/001-joint-inner-outer/test_annular_geometry.py
```

```text
exit 0
one_sidedness_lemma_4_1         PASS   105175 configurations scanned, 0 violations
exact_width_lemma_4_3           PASS   worst excess over W_rho    2.7755575615628914e-17
                                       sphere-contact error       2.7755575615628914e-17
                                       left/right mirror error    3.7470027081099033e-16
exterior_area_proposition_4_5   PASS   worst slack (sharp)       -6.938893903907228e-18
                                       worst slack (simplified)   0.0
                                       sector identity error      3.469446951953614e-18
payment_proposition_5_3         PASS   worst slack 0.0 at delta = 0, s = 0.675763481231215
                                       C_ext = 0.2109668867638871
adversarial_optimisation        PASS   worst min slack 0.0 over 6 DE runs
monte_carlo_cross_validation    PASS   worst error / tolerance    0.28850534140798717
falsification_power_control     PASS   240 counterexamples to a halved-sector
                                       over-claim; W_rho < 2·asin(delta/rho)
all_passed: true
```

`sector identity error` confirms `PROOF.md` Remark 4.6: for every legal
position the interior sector area equals `(r0²/2)·A(s)` exactly, so
Proposition 4.5 is sharp. `falsification_power_control` is a self-test showing
the suite can reject a statement stronger than the truth.

### 2. Numerical scout

```bash
/usr/bin/python3 spikes/001-joint-inner-outer/scout.py
```

```text
exit 0, 18.92 s, 12 seeds
best: a = 0.1317701853946747   r_lambda = 0.2042351438885795
      r0 = 0.4999999845500064  rho = 0.6739904564775159
      I = 0.020971876357697802     high = 0.020971876357697948
      C_ext = 0.20982467952138706  selected exterior = 0.052456169880346765
      residual annulus = 0.10213157543638181
      joint = 0.020971876357697802   bottleneck = inner
```

The optimum sits on the unattained boundary `r0 → 1/2`; the frozen rational
tuple above is a deliberate retreat from it.

### 3. Arb fixed-witness certificate

```bash
/home/argustest/research/star-shaped-kakeya/.venv/bin/python \
    spikes/001-joint-inner-outer/certify.py
```

```text
exit 0, 0.601 s, 256-bit Arb, 2^16 exact-rational integral cells, 26 gates
accepted: true
fixed_path_guard.passed: true          all_guard_controls_passed: true
all_mutation_controls_passed: true
production_decision: all mandatory gates present and passing
script_sha256: bc5577513472a4956dd960f4479859a6b6cccf501baad0e4c1d419615def6fad
```

Certified outward lower bounds (truncated lower endpoints of Arb enclosures):

| quantity | certified lower bound | margin above `T = 131/6250` |
|---|---|---|
| `rho` | `0.675763481231215108697315062628` | — |
| `C_ext` | `0.210966886763887251296480868157` | (positivity gate) |
| `h0/(2π)` | `0.0209718468512190483942658134996` | `1.18468512190483942658134995962e-5` |
| `I` | `0.0209706915542672869889884168515` | `1.06915542672869889884168514982e-5` |
| `C_ext/4` | `0.0527417216909718128241202170392` | `3.17817216909718128241202170392e-2` |
| `C_fan` | `0.103578016282865407239821215320` | `8.26180162828654072398212153200e-2` |
| joint | `0.0209706915542672869889884168515` | `1.06915542672869889884168514982e-5` |

Integral enclosure at `2^16` cells:
`[0.0209706915542672869889884168515, 0.0209724436266729562371749796735]`,
width `1.75207240566924818656282203938e-6`; only the lower endpoint enters
gate C2.

```text
outerMeasure(E) ≥ π·joint ≥ 0.0658813705275836316874410098839
                > π·T      ≤ 0.0658477820192420662781770053135
```

versus the published `100π/5599 = 0.0561098884370…`: a `17.36 %` relative
increase of the lower endpoint, and a displayed upper/lower ratio falling from
about `5.0661` to about `4.3169`.  The Lean theorem now exists, as recorded at
the start of this README and in `LEAN-STATUS.md` §22.

#### Mutation controls (4/4 rejected)

All are evaluated by the *same* `check_gates` production checker:

| mutation | expected failure | observed failed gates | rejected |
|---|---|---|---|
| `target_raised` (`T := 21/1000`) | C1, C2 | `gate_C1_high_above_target`, `gate_C2_integral_above_target` | yes |
| `h0_lowered` (`h0 := 3/25`) | C1 | `gate_C1_high_above_target` | yes |
| `exterior_coefficient_weakened` (`C_ext/4 → C_ext/40`) | C3 | `gate_C3_exterior_above_target` | yes |
| `r0_outside_domain` (`r0 := 7/10`) | domain | `domain_r0_below_half`, `domain_rho_above_r0`, `evaluation_completed` | yes (status `domain-abort`) |

#### Fixed-path exactness guard and its negative controls (5/5 rejected)

The previous text-token guard was **defective**: an independent reviewer
demonstrated that `harmless_binary_float = 1e-3` passed it, and re-running the
old guard confirmed that `1e-3`, `1/2` and `f = float; f(x)` were all accepted.
It has been replaced by an **AST and call-graph exactness regression guard**
(`fixed_path_guard`), which statically rejects:

* float or complex literals in any notation, including scientific notation;
* statically exact integer true divisions such as `1/2`, while allowing
  `arb(1)/2` and `Fraction(1,2)` (the divisor test is applied only when *both*
  operands are compile-time integer expressions);
* loads or aliases of `float`, `complex`, `round`, resolved through closure,
  module globals and builtins by object identity;
* dynamic escapes `eval`, `exec`, `compile`, `getattr`, `setattr`, `delattr`,
  `__import__`, `globals`, `locals`, `vars`;
* dunder names and dunder attribute access, imports, lambdas,
  `global`/`nonlocal`, and computed call targets;
* **any call to a function outside the inspected call graph** — the whitelist
  is fail-closed, so an unrecognised call target is a rejection, and a
  whitelisted name that has been rebound to another object is also a rejection.

Fixing the guard exposed a real hole: `_decimal` was being called from the
fixed path without being registered in `FIXED_PATH_FUNCTIONS`. It is now
registered and inspected.

Executable negative controls, each inspected by the *production* routine
against the *production* whitelists:

| control | construct | observed rejection kinds | rejected |
|---|---|---|---|
| `scientific_notation_float_literal` | `1e-3`, `0.5` | `float-or-complex-literal` | yes |
| `exact_int_true_division` | `1 / 2` | `exact-int-true-division` | yes |
| `float_constructor_alias` | `f = float; f(x)` | `forbidden-name`, `uninspected-call-target` | yes |
| `uninspected_helper` | call to a helper absent from `FIXED_PATH_FUNCTIONS` | `uninspected-call-target` | yes |
| `dynamic_escape_eval` | `eval("...")` | `forbidden-name`, `uninspected-call-target` | yes |

Re-running the reviewer's original bypass function under the new guard yields
`passed: false` with findings
`float-or-complex-literal -> 0.001`, `exact-int-true-division -> 1 / 2`,
`forbidden-name -> float`, `uninspected-call-target -> f`.

**Honest scope.** This is a *static regression guard, not a mathematical
proof*. It does not exclude bytecode rewriting, C-extension inexactness, or a
compromised `flint` build, and it does not attempt name resolution of division
operands, so a runtime `int/int` division through two variables would not be
caught statically. Both limitations are recorded in
`certificate.json → fixed_path_guard.known_limitations`. The mathematical
content of the certificate rests on Arb's outward rounding and on `PROOF.md`,
not on this function.

**Replacing the guard changed no numerical result.** All 26 gates, the
production decision, all four mutation controls and the parameter SHA-256 are
byte-identical to the pre-guard run; only `script_sha256`, `elapsed_seconds`
and the guard metadata differ.

---

## Fatality probes passed

* A connected unit needle cannot occupy both sides of the support
  perpendicular while avoiding `B(0,rho)`, whatever the value of
  `2·sqrt(rho²−delta²)` relative to the needle length (Lemma 4.1;
  105 175 scanned configurations, 0 violations).
* The width formula handles sphere contact, zero height, `delta → h0` and
  arbitrarily far needles, on both sides.
* Restricting pairwise-disjoint open triangles to the exterior region
  preserves disjointness; the ledger uses open shadow cones and the measurable
  complement, so no measurability of `E` or of the residual direction set is
  needed.
* Finite stop, summable infinite deletion and infinite-budget branches all have
  valid exterior analogues. The `B = ∞` branch uses the cone-only inequality
  (8.3a) and needs neither (B4) nor the residual fan (§8.6).
* The residual fan is measured through the explicit 2π cut adapter of
  Lemma 8.3: choose a cut point, note that removing one point does not change
  1-D outer measure, then apply the real-angle polar statement of Lemma 9.1.
  No lift is claimed to be an isometry.
* The planar split uses the measurable closed ball, so it is valid for
  arbitrary non-measurable `E`.
* Full selected triangle area is never added to the inner-disk contribution;
  only its exterior part is used.
* The escaping branch needs neither `rho > 1/2` nor `rho ≤ 1`, unlike the
  published Case II (Remark 8.2).

## Known limitations

* The mass split `p` and the affine balance lemma disappear; the new route uses
  only `π ≤ L_in + L_out`. `p`-dependent published material is therefore
  inapplicable, not merely unnecessary — in particular `strongCaseIQ` and its
  two mass lemmas bake in `π·strongP` and are not reusable as-is.
* `I` does not depend on `r_lambda` for this tuple (`PROOF.md` Remark 2.1;
  a single branch switch at `r = 0.2352988169…`, not two), so the published
  three-piece integral cut cannot be ported.
* Margins on gates C1 and C2 are only about `1.1e-5`.
* No global search of the legal parameter domain was performed or is claimed.
* `PROOF.md` inherits any defect in the quoted main-paper results.

---

## Remaining gates

Milestones are specified in `LEAN-PLAN.md`:

| M | Content |
|---|---|
| M0 | reproduce the existing Lean build and axiom receipts |
| M1 | closed-ball Carathéodory split (cheap, load-bearing, do first) |
| M2 | **fatal gate** — exterior triangle area, weak `asin(δ/ρ)` form only |
| M3 | finite restricted exterior greedy assembly |
| M4 | infinite / summable / `B = ∞` branches and the annular fan |
| M5 | restricted coordinate transport + variable `L_in` mass factorisation |
| M6 | deep parameterisation of the endpoint machinery; new kernel and gates |
| M7 | final assembly and axiom audit |

**All of M0–M7 are now complete** — see `LEAN-STATUS.md` (M1–M5 and §22 for M7)
and the four `M6-*-STATUS.md` files. The heading of this section is historical.

Plus: independent human review of `PROOF.md` before any paper edit.

The published paper is deliberately **not** edited, and the Lean work is left
uncommitted for independent final review. *(This paragraph originally read "no
Lean implementation was started"; that is superseded.)*

---

## Verdict: VALIDATED (paper proof relative to quoted results + fixed Arb certificate) — and now PROVED IN LEAN

*The original verdict heading read "Lean pending"; that is superseded.*

The geometric mechanism, its additive outer-measure bookkeeping and its
numerical gates hold up. `PROOF.md` is a complete conditional proof relative to
the quoted main-paper results, and `certificate.json` discharges its numerical
hypotheses with outward-rounded Arb intervals for the frozen rational tuple.
The improved constant `131π/6250` is a certified paper result for this route,
**and is now also a Lean theorem** (`universal_annular_lower_bound`,
`AnnularAssembly.lean:233`), proved independently of the Arb certificate and of
`PROOF.md`.
