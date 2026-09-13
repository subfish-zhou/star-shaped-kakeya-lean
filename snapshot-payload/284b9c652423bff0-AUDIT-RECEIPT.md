# Audit receipt

Provider: `[Codex]`

Snapshot date: 2026-07-31

## Mathematical review

The final fresh-context audit confirmed the stronger fixed theorem inside the
corrected Round-2 framework.  It separately checked the affine parameter
identity, the three `g`-branch regions, the positive logarithm tail, signed
radical enclosures, the arcsine direction, the fixed value of \(p\), and all
three exact margins.

The audit also confirmed that

\[
\frac{100}{5599}-\frac1{56}=\frac1{313544}>0.
\]

## Independent computation

The exact verifier returns `SYMBOLIC_PROOF_OK`.  Its weakened logarithmic-tail
mutation is strictly negative.

The independent Arb fixed witness gives the safe coefficient lower bound

\[
0.017866278155401827>\frac{100}{5599}.
\]

The one-step \(p\)-mutation fails, providing an independent negative control.

## Lean receipt

The lower-bound Lean source scan finds no `sorry`, `admit`, `by?`, `TODO`,
`unsafe`, `native_decide`, or custom `axiom`.

Build targets (all pass):

```bash
lake build                                       # production root, = lake build +StarKakeyaLower
lake build StarKakeyaLowerAudit                  # audit receipts
lake build StarKakeyaLower StarKakeyaLowerAudit  # full library
```

The production root `StarKakeyaLower.lean` imports `StarKakeyaLower.UniversalAssembly`
and nothing else, and does *not* import `Audit`; `StarKakeyaLower.Audit` is its
own Lake target whose imports are exactly the three roots it needs
(`UniversalAssembly`, the independent `ArithmeticKernel`, and the audit-only
`NegativeControls`).

`lake build StarKakeyaLowerAudit` prints, for the final theorem and for every
audited load-bearing component, the axiom set `propext, Classical.choice,
Quot.sound` and nothing else.  The receipt covers `GreedyResidual`,
`StrongParameterDomain`, the fixed stronger radical bounds, the quotient-circle
dilation kernel, the Li Lemma 2.3/2.5 layer, the Case-I endpoint closure, the
Figure-5 base-endpoint geometry, the Case-II radius branch, and

```lean
#print axioms universal_strong_lower_bound
-- 'StarKakeyaLower.universal_strong_lower_bound' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

The paper's stronger proof states its exact fixed-parameter trichotomy contract.
The Lean domain certificate `StrongParameterDomain` intentionally contains no
endpoint-containment field: that geometric bridge is proved separately, in
`CaseIEndpointAnalytic`/`Figure5LocalContact`/`UniversalEndpointClosure`, and is
assembled by `universal_strong_lower_bound`.

The universal theorem is **closed**: `universal_strong_lower_bound :
UniversalStrongLowerBound` is unconditional.  The universal assembly follows the
paper's radius split literally: it first performs `by_cases` on the high
alternative and, only under `no high`, splits outer direction mass between
`A_in_radius strongR₁` and `A_out_radius strongR₁`.  The high branch is
unconditional, the outer branch calls the proved `strongCaseII_radius_branch`,
and the inner branch is discharged by `caseIEndpointPointwiseTheorem_proof`
together with the proved `strongLiLemma25`.  No source-theorem parameter remains.
