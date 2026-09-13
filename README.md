# Star-shaped Kakeya sets: a one-tenth lower bound in Lean

A Lean 4 / Mathlib proof that every star-shaped subset of the Euclidean plane
containing a complete closed unit segment in every unoriented direction has
Lebesgue **outer measure at least 1/10**.

The set need not be measurable or bounded. Neither a regular needle selector
nor any auxiliary area inequality is an assumption of the public theorem.
This repository contains the lower-bound formalization only, not the separate
upper-bound constructions, manuscript, optimization experiments or model reviews.
It makes no claim that 1/10 is sharp or that a historical-priority audit is complete.

## Public theorem

```lean
import StarKakeyaLower.OneTenth

#check StarKakeyaLower.StarShapedKakeya.one_tenth_le_outerArea
#print axioms StarKakeyaLower.StarShapedKakeya.one_tenth_le_outerArea
```

Its type is:

```lean
theorem StarShapedKakeya.one_tenth_le_outerArea
    {E : Set Plane} (K : StarShapedKakeya E) :
    ENNReal.ofReal (1/10 : ℝ) ≤ volume.toOuterMeasure E
```

All these names are in `StarKakeyaLower`. Here
`Plane := EuclideanSpace ℝ (Fin 2)` and `Direction := AddCircle Real.pi`.
The input structure has exactly the following fields:

```lean
center : Plane
star : ∀ ⦃x⦄, x ∈ E → segment ℝ center x ⊆ E
needle_exists : ∀ θ : Direction, ∃ n : UnitNeedle,
  n.HasDirection θ ∧ n.carrier ⊆ E
```

A `UnitNeedle` has two endpoints at distance one; its carrier is their entire
closed segment, not just the two endpoints. `HasDirection` allows either
orientation of a real lift of the projective direction.

[`OneTenthParentAudit.lean`](StarKakeyaLower/OneTenthParentAudit.lean) constructs
this structure directly from the raw geometric assumptions and checks the
result through a fresh public import. [`OneTenthAudit.lean`](StarKakeyaLower/OneTenthAudit.lean)
also prints the axioms of the main assembly steps.

## Reproduce

Supported build route: Linux/WSL, Python 3, Git, Bash, curl, `/usr/bin/time`,
and [elan](https://github.com/leanprover/elan). The toolchain file selects
Lean **4.30.0-rc2**. Mathlib is pinned to
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`; all nine dependency revisions
are recorded in both `lake-manifest.json` and `dependencies.lock.json`.
The two files must agree. Do not run `lake update` to move these pins.

From a fresh clone:

```bash
git clone https://github.com/subfish-zhou/star-shaped-kakeya-lean.git
cd star-shaped-kakeya-lean
bash prepare.sh
python3 test_build_contract.py
python3 build.py --check
python3 build.py
```

`prepare.sh` fetches the public dependencies at the locked revisions. It builds
the small upstream cache bootstrap in explicit dependency order, one Lean module
at a time, then invokes Mathlib's own cache downloader. It does **not** build the
Mathlib or project library aggregate. Network access and substantial disk space
for the upstream cache are required; a failed download is a failure, not a proof
pass or an invitation to silently rebuild all of Mathlib.

`build.py` checks the dependency identities and compiler, resolves the complete
local import graph and compiles it sequentially with one `lean -j2` process at a
time. Both audit roots and every shipped local module are included. It rebuilds
the project sources rather than relying on earlier project objects. Build
objects, logs and receipts are local ignored outputs in `.closeout-build/run-*/`.
Only a fully successful run is atomically exposed at `.closeout-build/lib/lean`,
the import path configured for Lake; a failed run does not replace that snapshot.
After a successful local-dependency build, the public import can also be checked with:

```bash
lake env lean -j2 StarKakeyaLower/OneTenthParentAudit.lean
```

Do not run another Lean build concurrently. Bare `lake build` deliberately has
no default proof target; use the explicit command above for verification.

An existing **matching, clean, prebuilt** dependency project can instead be
used read-only, without `prepare.sh`:

```bash
export KAKEYA_DEPENDENCIES=/path/to/matching-dependency-project
# Optional if elan already resolves the pinned toolchain:
export KAKEYA_LEAN_SYSROOT=/path/to/lean-4.30.0-rc2
python3 test_build_contract.py
python3 build.py --check
python3 build.py
```

The external project must contain the locked `lake-manifest.json`, dependency
checkouts in `.lake/packages/`, and their compiled Mathlib objects. Its own
Kakeya objects are never imported. Do not set either variable to a different
Lean/Mathlib version and treat its cache as compatible.

## Proof organization

The 44 source modules are the complete import closure of the public and
raw-hypothesis audits; failed experiments and historical working directories
are excluded.

- **Literal geometry:** `StarKakeyaSet`, `TriangleArea`, `LiGeometry` and the
  circle/polar foundations define the actual Euclidean objects and measure.
- **Arbitrary-set recovery:** `OneTenthRecovery` recovers a finite Borel family
  inside an arbitrary open cover; this is not a measurability assumption on E.
- **Physical angular sections:** the circle, cap and lobe modules keep signed
  and zero heights, external feet, and both physical lifts of a direction.
- **One physical area account:** the open-bank and source modules partition
  actual direction sources and control the same physical radial sections.
- **Integration and assembly:** the section, fixed-height, kernel-integral and
  tail modules pay the source classes on disjoint radial supports;
  `OneTenthGlobalAssemblyClosed` closes the open-cover estimate.
- **Public arbitrary-set result:** `OneTenth` transfers that estimate to outer
  measure. The final caller supplies no section, price or area certificate.

Some internal lemmas have explicit geometric or analytic hypotheses. Their
actual uses discharge those hypotheses in the assembly; they are not new
axioms or additional fields of `StarShapedKakeya`.

## Trust and scope

The expected public theorem dependency list is:

```text
[propext, Classical.choice, Quot.sound]
```

The project uses no `sorry`, custom axiom or `native_decide` in this closure.
The printed axiom output and final build receipt are separate from source
inspection. Lean checks the formal statement, not the accuracy of an external
paper or the optimality of the constant. Mathlib and the selected Lean release
remain dependencies of the verification.

No repository-wide redistribution licence has been selected. Public visibility
alone is not a grant of an additional licence. Dependencies retain their upstream
licences; their source and build caches are not vendored here.
