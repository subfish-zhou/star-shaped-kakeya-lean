# ACCEPT — IL physical-union geometry and all-Borel-cut applicability

## Exact scope and provenance

**Verdict: ACCEPT.** At commit `ed84c269e743177aaf1d3776df6ec5eefa05a9f6`, the proof establishes the stated hereditary integrated-low inequality for every Borel direction cut of a fixed Borel unit-chord selector satisfying `M<99/100` and `|h|<=1/5`. I found no missing quantifier or physical double charge in that statement. This is acceptance of a human mathematical proof, not formal verification.

The accepted statement is

`area(W(V) ∩ disk(1/2)) >= C* |V|`,

where `C*=2C4+C5+(1-C4/C6)D5 > 637/20000 > 1/(10π)`. Strict comparisons after multiplication require `|V|>0`; null cuts have only the stated non-strict comparisons.

**No promotion of the universal star-Kakeya area-0.1 theorem is made.** The high-side assembly, arbitrary-selector recovery in its final application, and joint physical bank compatibility with that assembly remain outside this review. Nor does this result establish a prescribed measurable matching/transport or permission to add its conclusions over overlapping cuts.

Repository inspected read-only:

`/home/argustest/research/star-kakeya-wt-01-b2-integrated-low`.

HEAD was the exact requested commit and `git status --short` was empty. A subsequent `git diff --exit-code` against that commit was empty for the IL subtree and both mathematical prerequisites. I read the full IL `PROOF.md` (260 lines), the full baseline proof, the full B1 endpoint-domain proof, and the IL arithmetic checker/admission. The findings below are reconstructed from literal geometry, not inherited from a candidate's status declaration. PL is neither used nor inferred.

## 1. Literal sections and endpoint eligibility

Orient each segment toward a far endpoint, with a fixed Borel tie rule. In the resulting coordinates it is `[(x-1,h),(x,h)]`, where `x>=1/2`. Since `x<=M<99/100<1`, the two longitudinal endpoint coordinates have opposite signs. In particular, no exterior-foot chord is silently admitted to a lobe formula.

For `z=|h|>0`, put

`b=atan(z/x)`, `c=atan(z/(1-x))`, `γ=π-b-c`.

After transporting the local signed coordinates back to the original plane, the triangle's cone is `[b,π-c]`. A ray in this cone meets the segment at radius `z/sin φ`, and the anchored triangle contains every smaller radius on that ray. Consequently:

* For `0<r<=z`, the entire cone is present, regardless of whether the segment itself meets the circle.
* For `r>z`, set `a=asin(z/r)`. The section is the cone intersected with `[0,a] ∪ [π-a,π]`.
* Since the chord straddles its perpendicular foot, `b<π/2<π-c`. If a selected endpoint has radius `R>r`, its corresponding lobe is exactly `[b,a]` or `[π-a,π-c]`, rather than a spuriously extended partial lobe.

The far endpoint always has `M>=1/2`, by `M+N>=1` and `M>=N`. Thus for `0<r<2/5`, the far lobe is available on all of V, and the near lobe is available on `B(V)={q∈V:N(q)>=2/5}`. This uses the near **endpoint** radius, not the minimum radius of the segment.

For either eligible lobe, with `β=asin(z/R)`, monotonicity of `asin(t)/t` gives

`β/a <= r/R`, hence `β/(a-β) <= r/(R-r) <= r/(2/5-r)`.

The base is a literal subarc of the triangle section; the extension reaches the ideal chord-direction anchor. Nothing here charges the area of an individual triangle.

## 2. Full-cone caps independently reconstructed

The far-only cone cap is important: a near radius of at least `2/5` cannot be presumed on U. I checked the endpoint-maximum argument in B1 §5 and also obtained the precise cap needed by IL directly, without depending on its sharper numerical constant.

For fixed `0<z<=1/5`, let

`F(x)=atan(z/(1-x))+5 atan(z/x)` on `[1/2,1]`, with the endpoint limit at 1.

The sign of `F'(x)` is the sign of

`P(x)=x²+z²-5((1-x)²+z²)`.

Since `P'(x)=2x+10(1-x)>0` on this interval, F is monotone or decreases then increases. Its maximum is at an endpoint. The endpoint bounds are

`F(1/2)=6 atan(2z) <= 6 atan(2/5) < 12/5 < π`,

`F(1)=π/2+5 atan z <= π/2+5 atan(1/5) < π/2+1 < π`.

Therefore `c+5b<π`, or equivalently `b/γ<1/4`. This proves the needed far-only cap over the whole low straddling domain, including arbitrarily small near radius and arbitrary variation of x and h. The rational comparisons were independently tool-checked.

For a selected near endpoint, `N>=2/5`, `M>=N`, and `z<=1/5` imply `b,c<=π/6`. Thus `γ>=2π/3`, so `c/γ<=1/4`. This cap legitimately requires near eligibility and is used only there.

It follows that every selected full-cone extension is at most one quarter of its real base length. If both endpoints are eligible, the identical full cone is listed twice, with different extension sides. It must remain one physical base in the union, as the proof specifies.

## 3. Why the ideal anchor census is genuinely disjoint

Fix a half-open direction chart `[0,π)` and write E for the Borel set on which the far orientation agrees with that chart. The far ideal lift of V is

`F(V)=(V∩E) ∪ ((V\E)+π)`.

The opposite ideal lift of B is

`A(B)=((B∩E)+π) ∪ (B\E)`.

Each displayed branch is an isometric translation of its direction subset. The first union has physical angular measure `|V|`, the second has measure `|B|`, and they are disjoint. Indeed, equality of physical anchors forces equality of projective directions; for that direction the two selected anchors are antipodal. Equivalently, the four chart pieces above directly show disjointness, including the seam under half-open ownership.

This remains true if the far choice switches arbitrarily on a Borel set or on the far-tie stratum. It does **not** assert disjointness of real endpoint positions, real lobes, cones, or triangles.

## 4. One interval-union proof, not two labelled receipts

For completeness, the baseline interval lemma works for the uncountable family actually used here. Enclose the union of all real bases in an open circular set O. Each connected base lies in one component C. If its permitted one-sided extension is at most `ρ` times its base length, it is contained in C enlarged by `ρ|C|` on each side. Sum the resulting component lengths and take the infimum over O. The whole-circle case is immediate. This proves the outer-length estimate

`|union extended bases|* <= (1+2ρ)|union real bases|*`.

Repeated bases cost no extra measure. Arbitrarily many overlapping bases, opposite extension directions, and mixed local signs are already included. A singleton cannot acquire positive extension.

Apply this lemma **once** to every selected base, with

`ρ=max(1/4,r/(2/5-r))`.

Its extended union contains the two disjoint ideal lifts above. Its real union is contained in the actual section `S_r(V)`. Therefore

`|S_r(V)| >= (|V|+|B(V)|)/(1+2ρ)`

`              = min(2/3,(2/5-r)/(2/5+r)) (|V|+|B(V)|)`.

This proves IL equation (2) as a literal union inequality. Duplicate full cones and cross-label endpoint/lobe collisions have already been merged. There is no subsequent extra near-lobe payment. The doubled source coefficient on B is justified by distinct ideal anchors, not duplicate capacity.

## 5. Outer banks and pointwise capacity

On U, `N<2/5` and the unit-chord triangle inequality give `M>3/5`. On all of V, `M>=1/2`. At every `r>1/5`, all nonzero heights satisfy `z<r`; thus the same literal far-lobe argument gives the `k5` and `k6` receipts, without any cone case. Both estimates use one far anchor per direction and allow zero-height singleton rays.

The radial banks `(0,1/5)`, `[1/5,7/20)`, and `[7/20,1/2)` are disjoint except for harmless boundary circles. On the last bank, `W(U(V))⊆W(V)` and the density is exactly

`λ 1_{W(U(V))} + (1-λ) 1_{W(V)}`.

For `0<=λ<=1` this is 0 off W(V), `1-λ` on `W(V)\W(U(V))`, and 1 on W(U(V)). Thus no point is charged above unit physical area density. The overlaps are not being treated as fresh area.

The resulting coefficients of `b=|B(V)|` and `u=|U(V)|` are

`a_B=2C4+C5+(1-λ)D5`,

`a_U=C4+C5+λC6+(1-λ)D5`.

Their difference is `C4-λC6`. Setting the absolute constant `λ=C4/C6` cancels it without reference to V, b/u, q, h, or a selected physical point. The price is therefore cut-independent, not an adaptive choice hidden in the argument. These are physical area resource bounds; no stronger matching theorem is needed.

## 6. Adversarial strata and quantifier checks

| Potential defect | Finding |
|---|---|
| Mixed positive/negative h | Local reflection only describes the actual triangle; the single circular interval lemma allows both extension directions. No reflected W is added. |
| Positive-measure zero-height family | Retained as actual singleton anchors at every used radius below the corresponding endpoint radius. Such a family is not discarded as a null label set. |
| `r=z` tangency | Whole-cone branch includes equality. |
| `N=2/5` | Assigned to B; all eligible-anchor radii satisfy strict `r<2/5`, so the near base exists. |
| `|h|=1/5` | Included in cone bounds and in the first bank; the later receipts only need `r>1/5`. |
| Far ties `M=N` | Fixed Borel orientation; same-direction anchors still antipodal. No uniqueness of the farther endpoint is assumed. |
| Shared real endpoints / lobe collisions / duplicate cones | Interval lemma is applied to their physical union, not their labelled lengths. |
| Seam crossings | Circular components and half-open direction charts preserve the correct length and ownership. |
| Null/empty V, B, or U | No division by their masses; the coefficient cancellation and non-strict inequalities remain valid. |
| Arbitrary variation of s,h | Only Borel measurability and the stated pointwise bounds are needed. No continuity, centering, fixed sign, or finite-valuedness is used. |
| Radius-boundary circles | Have zero planar area and are not mistaken for null direction families. |
| Arbitrary Borel subcuts | Fix the selector/tie choice on L first and restrict it. B(V)=V∩B(L); U(V)=V∩U(L); all geometric constants and prices remain the same. |

The unions and sections are analytic images/projections of Borel parameter sets with a compact simplex parameter for the triangle. They are Lebesgue measurable. Their polar pullback is analytic and measurable as well, so polar integration with `r dr dθ` is legitimate. No unproved finite-family-to-Borel approximation is required.

**Missing quantifiers found: none within the stated IL interface.** The result is not stated or proved for a non-Borel original selector without recovery, independently chosen multiple presentations of the same direction, arbitrary prescribed output cuts of a transport relation, or sums of estimates for overlapping direction cuts. Those are different claims, not omitted cases of the theorem in IL §1.

## 7. Independent arithmetic support and execution boundary

The parent was assigned checker replay; I did not rerun the repository checker. I inspected its formulas and independently ran one tiny exact Fraction calculation using a **24-term Horner evaluation** of the positive atanh logarithm series, with a geometric remainder bound, on the four stated closed forms. It returned:

* `0<C4<C6`: PASS.
* `D5>0`: PASS.
* `C*>637/20000`: PASS.
* `637/20000>71/2230`: PASS; exact gap `51/4460000`.
* `0.031885183965119 < C* < 0.031885183965121`: PASS, with these decimals entered as exact rationals.
* Kernel switch `r=2/25`: PASS.
* Full-direction rational margin: exactly `51/1420000`.

The calculation reported `0.0006081988103687763` seconds of in-script time and exited 0. A second tiny exact rational control for the independent far-cone endpoint bounds, near-cone cap, and `2/3` cone kernel also passed and exited 0. Each command had timeout 60 seconds. No search, optimization, installation, geometry sweep, 0.25 work, Lean, or repository write was performed. The accepted classical lower bound `π>223/71` is the stated final transcendental comparison input; these arithmetic controls do not certify the continuum geometry.

## Final disposition

**ACCEPT the exact-commit IL theorem and its all-Borel-subcut physical-union proof.** The genuinely new eligible-anchor count survives the duplicate-cone and cross-sign tests, and the outer-bank repair is pointwise source-once at fixed complementary prices. The report does not accept PL, does not derive a transport theorem, and does not promote the global 0.1 theorem. Only this report file was created.
