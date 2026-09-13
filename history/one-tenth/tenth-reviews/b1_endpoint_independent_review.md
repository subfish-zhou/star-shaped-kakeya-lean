# Independent adversarial B1 endpoint-domain proof review

## Source and verdict

- Repository: `/home/argustest/research/star-kakeya-wt-01-b1-endpoint-domain`.
- Actual exact HEAD: `36d8bbbc1870ae16e3fc06f75122b9e30f12c541`.
- Reviewed the complete `research/one-tenth/endpoint-geometry-b1/endpoint-domain/PROOF.md` (432 lines) and its complete imported `research/one-tenth/baseline/PROOF.md` (408 lines).
- Initial repository status was clean. This review makes no repository changes and does not rerun the source checker or optimize any schedule.

**Overall: ACCEPT the geometric/all-cut inequalities, comparisons, source-once integration, and the explicitly restricted payment-method obstruction. No load-bearing mathematical defect found.** The ceiling is an exact-valued upper obstruction for the common-uniform extension-ratio construction with the generic mixed-sign interval factor. It is neither an impossibility theorem for every far-only strategy nor a proved sharp optimum of all such strategies.

| Claim | Verdict | Qualification |
|---|---|---|
| Joint endpoint identities and closest-segment radius, §§1–2 | ACCEPT | Endpoint minimum and closest-segment radius remain distinct. |
| Entire circular section and capped far base, (3)–(4) | ACCEPT | Includes radial filling below the segment and exterior-foot full cones. |
| Theorem 1: all-Borel-cut cap, (6) | ACCEPT | One physical far lift; one simultaneous mixed-sign interval argument. |
| Theorem 2: bounded-radius cap, (7) | ACCEPT | Valid explicit relaxation on the stated joint domain; not asserted sharp. |
| Strict terminal comparison (9), finite-high retention (10) | ACCEPT | Uses the additional low-height hypothesis; no additive double payment. |
| Theorem 3: stronger straddling cone cap, (11)–(12) | ACCEPT | Endpoint-maximum proof is valid for every stated H and variable selector. |
| Frozen-low comparison, §6 | ACCEPT | Dominates everywhere on support; strict exactly on the stated initial interval. |
| All-cut radial integration and price composition, §7 | ACCEPT | Under the inherited Borel recovery and total pointwise price-load condition. |
| Exact-valued ceiling (14)–(15), with degeneration (16) | ACCEPT, restricted scope | Common uniform ratio for this chosen far base/anchor, followed by factor 1+2ρ; cap-only improvements and radial prices cannot overcome it. |
| Extension of this ceiling to all asymmetric/sign-refined/class-refined far-only constructions | BLOCK | Not established and not implied by the single-label degeneration. |
| New universal area constant or area-1/10 result | NOT CLAIMED | No promotion is authorized by this review. |

## 1. Literal geometry and radial filling

After orienting toward a farther endpoint, the endpoints `(x-1,h),(x,h)` with `x>=1/2` give the stated M and N identities. Minimizing the distance to the horizontal unit segment yields `a_min=z` for `x<=1` and `a_min=N` for `x>1`, including the foot-at-endpoint boundary `x=1`.

For positive height in signed local coordinates, a ray in `[b,d]` meets the segment at distance `z/sin(phi)`. Its triangle contains the whole radial interval down to zero. Thus (3) follows from `r sin(phi)<=z`, rather than from an assumption that the segment itself intersects the radius-r circle. This gives the full cone at every `r<=a_min`. In particular, when `x>1` and `z<r<N`, `d<asin(z/r)`, so the far base is the full cone. At `r=N` the equality endpoint is retained.

For `z<r<M`, `b=asin(z/M)<asin(z/r)`, so the chosen far interval is nonempty and has precisely `min(gamma,a_r-b)` length. It is a real subinterval of the physical section even when a second lobe also exists. The cap by gamma is essential and is correctly retained. For `r<=z`, the selected whole cone is also physical. No reflected triangle is inserted.

At zero height, the far radial interval always reaches M=x. Its radius-r far anchor is an actual singleton for `r<M`; negative radial material is present only for `x<1`. The proof does not discard a potentially positive-measure set of zero-height directions.

## 2. All-cut union theorem and Borel accounting

In the partial-lobe case the ratio bound follows from the increasing function `asin(t)/t`. Because the base length is a minimum, its extension ratio is a maximum of the cone and lobe ratios. Therefore `rho=max(B,r/(m-r))` is the correct common bound, not a minimum. The baseline lemma's parameter is `Lambda=1+rho`, and its factor is `2Lambda-1=1+2rho`, exactly as used.

Mixed height signs reverse the direction of extension. Far-endpoint switches change the physical anchor by an antipodal choice. Both are covered by the same component-enlargement proof of the interval lemma. Applying it once to all labels prevents separate recharging of cone/lobe cases or signs. Singletons permit only zero extension, which is all the proof requests.

A Borel far-endpoint tie rule gives one Borel lift of each projective direction. Partition a standard projective chart according to the two possible choices: its two images on the ordinary circle are disjoint up to chart endpoints, and their lengths add to |V|, not 2|V|. The lifted-anchor map is injective over V. Thus the required lower bound on the extended union is valid without an assumed antipodal copy of W.

The triangle union over any Borel cut is a Borel image of the cut times a compact simplex, hence analytic. Fixed-radius sections and the interval unions used here admit analogous Borel parameterizations. Consequently their angular lengths are measurable; alternatively, the interval lemma already works with outer lengths. The constants are chosen on D before V. The open-cover selector recovery and rerun height dichotomy are correctly placed before the all-cut and outer-area arguments.

## 3. Joint-domain bounded-radius bound

For `x>=1/2`, all `t` in `[x-1,x]` satisfy `|t|<=x`. The integral expression for gamma therefore gives `gamma>=z/M^2`, and `b<=z/x` gives `b/gamma<=x+z^2/x`.

At fixed z, the last function has nonnegative derivative on `x>=1/2>=z`. The upper feasible x is `sqrt(R^2-z^2)`, producing `R^2/sqrt(R^2-z^2)`, which increases with z. The condition `R>=sqrt(1/4+H^2)` ensures the maximizing relaxed boundary at z=H remains feasible. The lower constraint M>=m causes no conflict because R>=m. This establishes (7) without decoupling the endpoints.

The simpler estimate `B_{R,H}<=R+2H^2` is justified by evaluating the same relaxed expression at that feasible boundary. At H=1/5, the strict lower bound for the new cap exceeds the old maximum cap `1/(2*pi*R)`; the rational branch separately exceeds `(m-r)/(pi*R)`. This proves (9) on the entire stated open radial support. Formula (10) is also correct, and monotonicity of the rational branch proves retention throughout the closed finite-high window.

## 4. Low cap and comparison

For positive z, put `c=atan(z/(1-x))` and `A=1+1/B_L`. The derivative of `F=c+A*b` has the sign of

`q(x)=x^2+z^2-A((1-x)^2+z^2)`.

Its derivative is `2x+2A(1-x)>0` in the interior of the relaxed interval. Thus the only possible interior turning point of F is a minimum. The maximum lies at x=1/2 or the limit x=1. Both endpoint inequalities follow directly from the two entries defining B_L and monotonicity in z. All denominators are positive for finite H>0. The relaxed endpoint x=1 does not presume an additional physical chord. Theorem 1 handles z=0 separately.

For H=1/5, each expression defining K_L exceeds 11/15, whereas both old cone caps are below 2/3. The cosine comparison for alpha<beta has the necessary positive squared guard. The proof of k<2/3 also has the needed angle range and strict bounds.

For `0<r<m0`, the new rational branch exceeds 49/51 and the old two-anchor minimum is at most c_H. For `m0<=r<1/2`, comparison reduces to replacing k by a larger K_L in the same minimum. Therefore strict improvement holds for `0<r<c_old` and equality for `c_old<=r<1/2`, exactly as stated. Neither the variable x nor variable z selector has been replaced by a centered or fixed-height assumption.

## 5. Integration and ceiling scope

Polar integration with density `min(r,1)` proves (13) from angular unions, not labelwise triangle areas. Nonnegative prices whose pointwise sum is at most one keep total physical source load at most one, even for overlapping classes. For infinitely many price terms this is the inherited monotone-convergence argument. The warnings against adding all-F and P/Z full-price bounds are appropriate.

The primitive and strict rational comparison in (14)–(15) are correct. The positive integrand also justifies multiplying the strict upper bound for pi by its positive integral. For every fixed `0<r<1/2`, centered positive-height chords tending to height zero are eventually legal low chords, have `z<r`, and have the uncapped partial far lobe selected by (4). Their first-order extension ratio tends to `r/(1/2-r)`. Accordingly, a common uniform ratio valid on the whole low domain cannot be smaller. Applying the stipulated generic factor `1+2rho` cannot yield a coefficient above the rational branch.

**Precise limitation:** this rules out cap sharpening and price optimization within that common-uniform-ratio construction. It does not prove that the interval-union inequality is saturated by realizable selector families. It does not rule out asymmetric extension estimates, sign-dependent arguments, endpoint/class-refined far strategies, or a different coupling of physical unions. Nor does (14) prove that its upper value is attainable by the unrelaxed full construction: it is an exact-valued ceiling after allowing the cone cap to become 1.

The proof's explicit qualifications at lines 396–403 adequately support the restricted result. The shorter introductory phrase “one-far-lobe construction” (lines 13–15), the §8 title, and “exact ceiling” language should be read through those qualifications, not as a broader theorem. **Recommended scope-only edit, not a mathematical repair:** replace the introductory shorthand by “the common-uniform extension-ratio proof using the bases (4) and the generic mixed-sign factor 1+2rho”; add after line 403: “This does not exclude asymmetric, sign-dependent, or class-refined far-only arguments, and the displayed upper ceiling is not claimed to be the attained optimum of the unrelaxed construction.” No change to any inequality is needed.

## 6. Independent arithmetic performed

One independent `python3 -B` / SymPy subprocess, under a 60-second timeout, completed successfully in approximately 0.385 seconds. No search, quadrature, parameter scan, schedule experiment, or source-checker replay was performed. These were tiny deterministic checks of already derived identities, not substitutes for the human proof review.

Actual output:

```text
low derivative numerator identity: 0
sign-polynomial derivative identity: 0
far ratio first-order limit: -2*r/(2*r - 1) ; difference: 0
radial primitive derivative residual: 0
integral: 3/8 - log(2)/2 ; rational ceiling: 209/2268 ; 1/10 minus ceiling: 89/11340
old alpha-beta squared guard: 9146830400/38519900001
finite-high cap positive guard after positive cross multiplication: 11127164
elapsed_seconds: 0.3845989820547402
```

The finite-high guard is `(1250^2)*63-9344^2>0`, equivalent to the required strict cap comparison after positive cross multiplication and squaring. The limit calculation checks the first-order quotient; its denominator is nonzero on the stated open radial interval. All remaining signs, domains, all-cut quantifiers, and measurability issues were reviewed analytically above.

**Disposition:** ACCEPT for the named theorems and restricted ceiling; BLOCK only the broader extrapolations explicitly separated above. No source changes or new-area promotion. Normal/optimized source-check execution remains the parent's separate verification task.
