# M6 — endpoint parameterisation: branch status

Branch `research/m6-endpoint`, worktree `star-kakeya-wt-m6-endpoint`, baseline
`af20002`. Nothing is committed; this report describes the working tree.

**Scope executed.** Generic endpoint parameterisation infrastructure and a
new-tuple-ready exit. *Not* executed, deliberately: `AnnularKernel` numerals,
the two-piece integral certificate, `hmeas`/`hI`, and M7 assembly.

**Result: green.** `lake build` (production root) and
`lake build StarKakeyaLowerAudit` both succeed. Every `#print axioms` receipt is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx`. No baseline declaration
name disappeared, and `universal_strong_lower_bound` is unchanged with an
unchanged receipt.

---

## 1. Why the old certificate could not be reused

`base_ray_frozen_analytic` (`CaseIEndpointR1Analytic.lean:124`) is a rational
polynomial certificate cut at `t = 7/100`. It is **false for the new `a`**, so
it may not be ported, generalised, or hidden inside a shared lemma. The final
geometry, by contrast, appeared valid, so the work was to *lift the geometry off
that leaf* rather than to reprove the geometry.

After this change `base_ray_frozen_analytic` has exactly **one** code call site in the
whole tree, `Figure5FrozenPackage.lean:68`, inside the construction of the
frozen tuple's analytic package. No generic declaration mentions it.

## 2. Architecture — core/facade split

A first attempt kept the historical *names* but changed their *kinds*
(`inductive` → `def`, `structure` → `abbrev`). That broke qualified explicit
pattern matching, the constructor and projection constants, and direct imports
of the historical modules. It has been replaced by a genuine core/facade split:
each historical module still exists, still declares the original `inductive` /
`structure`, and delegates all mathematics to a CLEAN parameterised core.

```
Figure5EndpointDomain             CLEAN (Mathlib only)  parameter interface + scalar layer
 └ SupportFirstArcSelector        CLEAN   selectedSupportFirstArc? (+ covariance)
    └ Figure5EndpointEnvelopeCore CLEAN   Figure5UpperGapSourceFor + gap_lt
       └ Figure5LocalContactCore  CLEAN   the 1480-line local-contact geometry
          └ UniversalFirstArc     CLEAN
             └ UniversalEndpointClosureCore CLEAN  endpointTraceFor / endpointCriticalFor
                ├ EndpointConfinedExit      CLEAN  feeds the M5 confined wrapper
                └ (facade tower, FROZEN)
                   Figure5FrozenPackage         strongFigure5Domain + …AnalyticPackage
                    └ Figure5EndpointEnvelope   inductive Figure5UpperGapSource
                       └ Figure5LocalContact    inductive Figure5SelectedGapGeometry,
                          │                     structures Certificate / TargetRelation
                          └ UniversalEndpointClosure  universalArcData, universalFamily, …
                             └ UniversalAssembly      (baseline import restored)
```

Each facade imports its core **and** the facade below it, so a single
`import StarKakeyaLower.UniversalEndpointClosure` reaches the entire pre-M6
endpoint API exactly as before. The generic consumers (`UniversalFirstArc`,
`UniversalEndpointClosureCore`, `EndpointConfinedExit`) import **cores only**.
`Figure5FrozenPackage` sits *below* the facades precisely so the facades can
name `strongFigure5Domain` without a cycle.

Verified mechanically: transitive import closures of `Figure5EndpointDomain`,
`SupportFirstArcSelector`, `Figure5EndpointEnvelopeCore`,
`Figure5LocalContactCore`, `UniversalFirstArc`,
`UniversalEndpointClosureCore`, `EndpointConfinedExit`, `AnnularCaseI` and
`SupportReflection` contain **no** `StrongerKernel`. `Figure5FrozenPackage`, the
three facades and `UniversalAssembly` do, as intended. No import cycles.

### 2.1 The clean domain (task item 1)

`StarKakeyaLower/Figure5EndpointDomain.lean` (new, CLEAN, `import Mathlib` only):

```lean
structure Figure5EndpointDomain where
  a  : ℝ
  r0 : ℝ
  R1 : ℝ
  g  : ℝ → ℝ
  a_pos      : 0 < a
  a_le_r0    : a ≤ r0
  r0_lt_half : r0 < 1 / 2
  R1_pos     : 0 < R1
```

with `Figure5EndpointDomain.radius_pos / radius_lt_half / radialInterval`.
There is **no `rLambda` field**: the frozen radius is an artefact of one choice
of `g` and belongs to the package that certifies `g`, not to the geometric API.

The same module hosts the parameter-free scalar layer, moved verbatim out of the
frozen chain so that the geometry could be built without it:
`strongInteriorRatio`, `strongLargeAngleRatio`, `strongEndpointPhi` and their
estimates (`interior_contact_strict_gap`, `arctan_lt_self_of_pos`,
`self_lt_arcsin_of_pos_of_lt_one`, `strongEndpointPhi_strictMonoOn_radius`,
`exists_strongEndpointPhi_eq`, `strongEndpointPhi_le_of_le`,
`strongEndpointPhi_le_of_mixedSpan`, …). These keep their historical `strong`
prefixes but mention no tuple; renaming them would have been pure churn.

### 2.2 The analytic package (task item 2)

```lean
structure Figure5EndpointAnalyticPackage (P : Figure5EndpointDomain) : Prop where
  one_lt_g        : ∀ {r}, r ∈ Icc P.a P.r0 → 1 < P.g r
  interior_le_g   : ∀ {r}, r ∈ Icc P.a P.r0 → strongInteriorRatio r ≤ P.g r
  largeAngle_le_g : ∀ {r}, r ∈ Icc P.a P.r0 → strongLargeAngleRatio r ≤ P.g r
  base_ray_gap    : ∀ {r t α}, r ∈ Icc P.a P.r0 → 0 < t →
      t < π/2 - arctan (2*r) → t/2 ≤ α → α ≤ π/2 → 0 ≤ sin t →
      sin α ≤ P.R1 * sin t → sin α * sin (α - t) ≤ P.a * sin t →
      2 * α - t < P.g r * t
```

These are *exactly* the load-bearing analytic gates, established by inspection of
every remaining tuple-specific step:

| gate | sole consumer |
|---|---|
| `one_lt_g` | `Figure5UpperGapSourceFor.gap_lt` (near branch); `universal_hybrid_containmentFor` (dilation of a degenerate target) |
| `interior_le_g` | `Figure5UpperGapSourceFor.gap_lt` (height-cutoff branch) |
| `largeAngle_le_g` | `Figure5EndpointAnalyticPackage.target_lt_top_of_not_saturated`, used once in `universalFamilyFor_positiveMember_mem_dilate` |
| `base_ray_gap` | `Figure5UpperGapSourceFor.gap_lt` (base-ray branch) |

No frozen ratio appears in the package or in any geometric statement:
`base_ray_gap` concludes against `P.g r` directly, so `strongFrozenRatio` never
leaks into the API. Helpers: `of_dominations` (derives `one_lt_g` from
`interior_le_g`, so a tuple only owes three facts), `one_le_g`, `g_pos`,
`target_lt_top_of_not_saturated`.

### 2.3 Generic `...For` layer (task item 3) — no duplicated geometry

`Figure5LocalContactCore.lean` is **1489 lines** (baseline 1480; a net increase
of nine lines from the generic parameter threading and documentation). The
geometry was *refactored in place*, not copied; the
`Figure5LocalContact` facade is 342 lines and contains **no proof of geometry** —
only the original datatype declarations, constructor relabelling, and
delegations. Generic names:

* `Figure5UpperGapSourceFor P` + `.gap_lt HP`
* `Figure5SelectedGapGeometryFor P` + `.toGapSource`
* `Figure5ActualSelectedTargetRelationFor P`, `Figure5LocalContactCertificateFor P`
* `figure5_easy_gapGeometry`, `figure5_hard_mixed_gapGeometry`,
  `figure5_hard_baseBase_gapGeometry` (`{P}` implicit — old call shapes unchanged)
* `figure5ActualSelectedTargetRelationFor_of_principal`,
  `figure5LocalContactCertificateFor_of_actualSelected HP`
* `universalArcDataFor`, `universalFamilyFor(_needle/_selected/_zeroHeight/…)`,
  `universalFamilyFor_positiveMember_mem_dilate P HP`,
  `universal_hybrid_containmentFor P HP`

Three lemmas turned out to need **no** parameter at all and were generalised to
free variables rather than to `P` (strictly weaker hypotheses, old uses unchanged):
`Figure5SelectedChangedLift.upper_selected` / `.lower_selected` and
`figure5_selected_strict_presentation_endpoints_active` (now `{a R₁ : ℝ}`),
`universalPositiveNeedle_triangle_subset_disk` (now `{R₁ : ℝ}`), and
`figure5_local_contact_pointwise` (now a free `gval` instead of `strongPaperG r`).

### 2.4 Preservation of the old API — original kinds, not aliases

The three facades **re-declare the original datatypes verbatim**, copied from
`git show af20002:…`:

* `Figure5EndpointEnvelope` — `inductive Figure5UpperGapSource` with
  `.nearHalf`, `.heightCutoff`, `.baseRayCutoff`, plus `.gap_lt` with its
  baseline statement.
* `Figure5LocalContact` — `inductive Figure5SelectedGapGeometry` with
  `.nearHalf`, `.height`, `.mixed`, `.baseBase`; `structure
  Figure5LocalContactCertificate` (`.mk`, `.q`, `.D`, `.A`, `.gamma`,
  `.support`, `.selectedLift`, `.gamma_direction`, `.upper_gap`, `.lower_gap`);
  `structure Figure5ActualSelectedTargetRelation` (`.mk`, `.target_eq`,
  `.upper`, `.lower`).
* `UniversalEndpointClosure` — `universalArcData`, `universalFamily` (with its
  baseline definitional unfolding), the five family lemmas,
  `universal_hybrid_containment`, `strongRadius_pos/_lt_half`.

These are genuine inductives/structures: `Figure5UpperGapSource.rec`,
`Figure5SelectedGapGeometry.rec`, `Figure5LocalContactCertificate.rec` and
`Figure5ActualSelectedTargetRelation.rec` all exist and are audited. Each is
tied to its generic counterpart by a pair of pure constructor-relabelling
conversions (`.toFor` / `.toStrong`), which is where the delegation happens.

Names whose type was generalised now carry a `...For` suffix in the core, and
the facade restores the **exact** baseline statement as a thin specialization:
`Figure5SelectedChangedLift.upper_selected` / `.lower_selected`,
`figure5_selected_strict_presentation_endpoints_active`,
`figure5_local_contact_pointwise`, `figure5_easy_gapGeometry`,
`figure5_hard_mixed_gapGeometry`, `figure5_hard_baseBase_gapGeometry`,
`figure5ActualSelectedTargetRelation_of_principal`,
`figure5LocalContactCertificate_of_actualSelected`,
`universalPositiveNeedle_triangle_subset_disk`.

**Mechanical receipts.** A script re-extracts every declaration of the three
historical modules from `af20002` and compares kind and normalised signature
text against the current tree: **77 declarations checked, 0 mismatches, 0 kind
changes**. Across the whole tree, **0** baseline declaration names are missing
and **0** changed kind.

**Probes** (`04-lean/probe/`, run with `lake env lean`, all exit 0). Each imports
*only one* historical module:

* `ProbeEnvelope.lean` — `#check` of the inductive, its `.rec` and all three
  constructors; **qualified** term-mode `match` on
  `Figure5UpperGapSource.nearHalf/.heightCutoff/.baseRayCutoff`; qualified `fun`
  pattern-match; `cases … with`; `induction … with`; `rcases` with anonymous
  patterns; baseline `gap_lt` signature; each constructor applied with its
  baseline argument shape.
* `ProbeLocalContact.lean` — same battery for all four
  `Figure5SelectedGapGeometry` constructors; `#check` of every listed structure
  constructor and projection, including `Figure5LocalContactCertificate.mk/.q`
  and `Figure5ActualSelectedTargetRelation.mk/.target_eq`; anonymous-constructor
  round trips; qualified `match` on `Figure5ActualSelectedTargetRelation.mk`;
  and nine baseline theorem signatures verbatim.
* `ProbeClosure.lean` — all seventeen baseline declarations of
  `UniversalEndpointClosure` stated verbatim, including `universalFamily … = 
  directionNeedleFamilyOfRaw … := rfl` (definitional unfolding unchanged), plus
  `#check`s confirming the envelope and local-contact APIs are still reachable
  transitively from this single import as before M6.

### 2.5 The requested exits (task item 4)

In `UniversalEndpointClosureCore.lean`:

```lean
def endpointTraceFor (P : Figure5EndpointDomain) (K : StarShapedKakeya E)
    (hhigh : ¬ ∃ theta : Direction, P.a ≤ (K.needleFamily theta).height K.center) :
    ∀ r ∈ Icc P.a P.r0, ∀ d, FirstArcData (universalPositiveNeedle K d).triangle r

theorem endpointCriticalFor (P : Figure5EndpointDomain)
    (HP : Figure5EndpointAnalyticPackage P) (K : StarShapedKakeya E) (hhigh) :
    ∀ (r : ℝ) (hr : r ∈ Icc P.a P.r0),
      FirstArcPointwiseHybridCriticalContainment
        (directionNeedleFamilyOfRaw (universalPositiveNeedle K)
          (endpointTraceFor P K hhigh r hr))
        (K.A_in_radius P.R1) (P.g r)

theorem endpointOneLeG (P) (HP) : ∀ r ∈ Icc P.a P.r0, 1 ≤ P.g r
```

`directionNeedleFamilyOfRaw_endpointTraceFor` records that the family built from
`endpointTraceFor` is *definitionally* `universalFamilyFor`.

That the signatures **directly feed the M5 wrapper** is not asserted but
compiled, in the new `StarKakeyaLower/EndpointConfinedExit.lean` (CLEAN, added to
the production root):

```lean
theorem confined_lower_bound_of_endpointDomain
    {E : Set Plane} (K : StarShapedKakeya E)
    (P : Figure5EndpointDomain) (HP : Figure5EndpointAnalyticPackage P)
    (hhigh : ¬ ∃ theta : Direction, P.a ≤ (K.needleFamily theta).height K.center)
    {I_lower : ℝ≥0∞}
    (hmeas : AEMeasurable (fun r => ENNReal.ofReal (r / P.g r))
      (volume.restrict (Icc P.a P.r0)))
    (hI : I_lower ≤ ∫⁻ r in Icc P.a P.r0, ENNReal.ofReal (r / P.g r)) :
    I_lower * directionAngleOuter (K.A_in_radius P.R1) ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center P.r0)
```

It discharges `htrace`, `hcritical`, `hg` and `hmass` of
`universal_positive_confined_lower_bound_of_trace_containment`
(`AnnularCaseI.lean:145`) — i.e. all of M6 item 4 and the `hg` half of item 5 —
leaving only the two scalar obligations `hmeas` and `hI` (M6 items 5b/6).

---

## 3. Exact package constructor obligations for the `ann` tuple

No `ann*` constant is defined here, and no package proof is faked. A sibling of
`Figure5FrozenPackage` must supply exactly the following, and nothing else, on
the geometric side:

```lean
def annFigure5Domain : Figure5EndpointDomain where
  a := annA;  r0 := annR₀;  R1 := annR₁;  g := annPaperG
  a_pos      := (0 : ℝ) < annA
  a_le_r0    := annA ≤ annR₀
  r0_lt_half := annR₀ < 1 / 2
  R1_pos     := (0 : ℝ) < annR₁

theorem annFigure5AnalyticPackage :
    Figure5EndpointAnalyticPackage annFigure5Domain :=
  Figure5EndpointAnalyticPackage.of_dominations
    -- (A) interior domination
    (fun {r} (hr : r ∈ Icc annA annR₀) => (strongInteriorRatio r ≤ annPaperG r))
    -- (B) large-angle domination
    (fun {r} (hr : r ∈ Icc annA annR₀) => (strongLargeAngleRatio r ≤ annPaperG r))
    -- (C) the base-ray gap, the only genuinely new analytic theorem
    (fun {r t α} (hr : r ∈ Icc annA annR₀) (ht0 : 0 < t)
         (htop : t < π/2 - arctan (2*r)) (hhalf : t/2 ≤ α) (hαtop : α ≤ π/2)
         (hsint : 0 ≤ sin t) (hR1 : sin α ≤ annR₁ * sin t)
         (hheight : sin α * sin (α - t) ≤ annA * sin t) =>
       (2 * α - t < annPaperG r * t))
```

Notes for whoever discharges these.

1. `one_lt_g` costs nothing: `of_dominations` derives it from (A).
2. (C) must be proved **directly against `annPaperG r`**. Do **not** route it
   through a frozen-radius ratio and do **not** reuse the `t = 7/100`
   polynomial split of `base_ray_frozen_analytic`; that certificate is false at
   the new `a`. The clean statement above is the whole contract — the geometry
   supplies `hR1` from the physical `R₁`-norm bound on the base endpoints and
   `hheight` from the one-chord identity, and asks for nothing else.
3. `LEAN-PLAN.md` records that for the new tuple the frozen branch
   `(1+2rλ)/(1-2rλ)` is dominated on all of `[annA, annR₀]` by the increasing
   large-angle branch, so `annPaperG` is expected to be
   `max (strongInteriorRatio r) (strongLargeAngleRatio r)` with a single switch.
   In that case (A) and (B) are `le_max_left`/`le_max_right` and the entire
   analytic cost of the endpoint branch is (C).
4. Nothing else about the tuple is consumed by the endpoint geometry — in
   particular no `rλ`, no `p`, no mass split, no integral.

Remaining M6 items after that, unchanged from `LEAN-PLAN.md` and untouched here:
the `AEMeasurable` side condition, the two-piece `∫⁻` certificate, and the
Hypothesis-B/C numeric kernel.

---

## 4. Scans

* **Import cycles** — none (DFS over all 47 modules).
* **Frozen dependencies** — the generic core is CLEAN, not merely "split": see
  §2. `Figure5FrozenPackage` is the only frozen package at the base of the endpoint facades.
* **Duplicate declarations** — 24 repeated top-level names in the tree, all
  pre-existing and all in `AnnularGreedy*`, `CaseII*`, `LiGeometry`,
  `PolarOuterMeasure`, `StarKakeyaSet` (namespaced/sectioned). **Zero** involve
  any module touched by this change; no new duplicate introduced.
* **EOF whitespace** — a scan for missing final newline, blank lines at EOF and
  trailing whitespace over every `.lean` file reports **0 issues** (one blank
  line at the end of `Figure5LocalContactCore.lean` was found and removed).
* **Old API** — 77/77 baseline declarations of the three historical modules
  match in kind and signature; all three direct-import probes compile.
* **Forbidden tokens** — `grep -rnE "\bsorry\b|\badmit\b|^axiom |native_decide|unsafe |partial def" StarKakeyaLower/ StarKakeyaLower.lean` → empty.
* **Axioms** — no `sorryAx` anywhere in the audit output; every receipt is the
  standard `[propext, Classical.choice, Quot.sound]`.
* **Diff** — see `git status`; 9 modified historical files plus 7 new modules
  (`Figure5EndpointDomain`, `SupportFirstArcSelector`,
  `Figure5EndpointEnvelopeCore`, `Figure5LocalContactCore`,
  `UniversalEndpointClosureCore`, `Figure5FrozenPackage`,
  `EndpointConfinedExit`) and the three probe files.

## 5. Reproduce

```
cd materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean
lake build
lake build StarKakeyaLowerAudit
```

Probes (not part of any lake target):

```
lake env lean probe/ProbeEnvelope.lean
lake env lean probe/ProbeLocalContact.lean
lake env lean probe/ProbeClosure.lean
```

New audit receipts: `Figure5EndpointDomain`, `Figure5EndpointAnalyticPackage`,
`Figure5EndpointAnalyticPackage.of_dominations`,
`Figure5EndpointAnalyticPackage.target_lt_top_of_not_saturated`,
`Figure5UpperGapSourceFor`, `Figure5UpperGapSourceFor.gap_lt`,
`Figure5SelectedGapGeometryFor.toGapSource`,
`figure5ActualSelectedTargetRelationFor_of_principal`,
`figure5LocalContactCertificateFor_of_actualSelected`, `universalArcDataFor`,
`universalFamilyFor_positiveMember_mem_dilate`, `universal_hybrid_containmentFor`,
`endpointTraceFor`, `endpointCriticalFor`, `endpointOneLeG`,
`confined_lower_bound_of_endpointDomain`, `strongFigure5Domain`,
`strongFigure5AnalyticPackage`, and — pinning that the historical names are
still real inductive/structure constants — `Figure5UpperGapSource.nearHalf/
.heightCutoff/.baseRayCutoff`, `Figure5SelectedGapGeometry` with its four
constructors, `Figure5LocalContactCertificate(.mk/.q)`,
`Figure5ActualSelectedTargetRelation(.mk/.target_eq)`, and the frozen
specializations `figure5_easy_gapGeometry`, `figure5_hard_mixed_gapGeometry`,
`figure5_hard_baseBase_gapGeometry`,
`figure5ActualSelectedTargetRelation_of_principal`,
`Figure5SelectedChangedLift.upper_selected/.lower_selected`,
`figure5_selected_strict_presentation_endpoints_active`,
`universalPositiveNeedle_triangle_subset_disk`.

## 6. Blockers

None for the scope of this task: nothing had to be abandoned, and there is no
theorem whose old proof could not be parameterised. Every step of the 1480-line
local-contact argument and of the universal endpoint closure went through
unchanged once the four package gates were factored out; the only genuinely
tuple-specific leaf is `base_ray_gap`, which is now an explicit package field —
correct behaviour per the scope decision, to be discharged by the kernel branch.

Nothing outside the Lean tree and this file was edited. `LEAN-STATUS.md`,
`LEAN-PLAN.md` and `PROOF.md` are untouched.
