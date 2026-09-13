# B2 independent audit: conditional IL → universal area 1/10

## Verdict

**ACCEPT CONDITIONAL.** The disjoint-bank implication is mathematically sound, with the accepted endpoint-domain Theorem 2 and baseline terminal/recovery interface. All displayed coefficients are correct. **IL remains an unproved premise; neither IL nor PL is proved or asserted by this audit.** Thus this is not an unconditional universal 0.1 result.

The exact remaining premise sufficient for this bridge is:

> For every Borel unit-chord selector on the projective direction circle with `|h(q)| ≤ 1/5`, put `L={q:M(q)<99/100}` and let `W(L)` be its literal anchored-triangle union. Then
> `area(W(L) ∩ B(0,1/2)) ≥ |L|/(10π)`.

Open versus closed disk makes no difference here. Equivalently the left side is `∫_0^(1/2) r |S_r(L)| dr`. Angular length on the physical circle is ordinary angular length, and `|RP¹|=π`.

## Immutable intake and scope

Repository: `/home/argustest/research/star-kakeya-wt-01-short-integration`.
Revision: `d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da`; live HEAD matched it.
The abbreviated task paths resolve beneath `research/one-tenth/`, not the repository root. Root-level reads failed; the exact Git tree then identified the intended files. All mathematical source reads thereafter used `git show` at the pinned revision.

Reviewed:

- `research/one-tenth/endpoint-geometry-b1/CONDITIONAL_TENTH_BRIDGE.md`
- `research/one-tenth/endpoint-geometry-b1/conditional_bridge_check.py`
- `research/one-tenth/endpoint-geometry-b1/endpoint-domain/PROOF.md`
- `research/one-tenth/baseline/PROOF.md`, including recovery and the complete terminal-tail formula.

SHA-256 of the first two pinned blobs, respectively:

```text
b0bebfd0cfccbe2b3a18dc800dec07088b970149a79c8bb0e9ba203b33ed1467
e221888e5e7422b6b68f28191ba0e79c34b9835ec4dbf4e6e902cee424f4676c
```

The endpoint-domain proof diff against original accepted revision `36d8bbbc1870ae16e3fc06f75122b9e30f12c541` contains only the specified clarification of the one-far-base method ceiling. Theorem 2's formula and domain are unchanged. Its earlier independent acceptance is an input here, not a claim of a new independent audit of every B1 theorem.

## 1. Bounded-radius theorem and finite-high bank

The applicable accepted kernel is precisely

`g(r)=min{ sqrt(R²-H²)/(sqrt(R²-H²)+2R²), (m-r)/(m+r) }`, for `0<r<m`.

For `F={99/100≤M<8/5}`, take `m=99/100`, `R=8/5`, `H=1/5`. The theorem's domain conditions hold, and all proposed bank radii are strictly below m. Its cap is

`K_F=5√63/(5√63+128)>7/30`.

The positive cross-square residual is `25·63·23²−(128·7)²=30359`; equivalently `63−(896/115)²=30359/13225>0`. No sign reversal is hidden in squaring.

The rational branch decreases in r. At right endpoints `3/5,7/10,4/5`, its differences from the proposed steps `7/30,29/169,19/179` are respectively `19/1590,0,0`. These steps also decrease, so each lies below the cone cap. Hence the three rows are valid for the whole F, including zero-height directions.

Independently evaluating the integral as nested constant layers, rather than reproducing the checker's row sum, gives

`I_F = (19/179)∫_[1/2,4/5]r dr`
`    + (29/169−19/179)∫_[1/2,7/10]r dr`
`    + (7/30−29/169)∫_[1/2,3/5]r dr`
`    = 446059/13962000`.

An independent 192-bit Arb comparison certified `π>223/71`, and exact rational arithmetic gives

`(223/71)I_F−1/10=340957/991302000>0`.

Thus `I_F|F| ≥ |F|/(10π)`. The terminology “area coefficient” `πI_F` denotes the normalized coefficient if the class had total direction length π; the actual receipt is `I_F|F|`, not `πI_F|F|`.

## 2. First and all later tail banks

For `D₀={8/5≤M<16/5}`, Theorem 2 applies with `m=8/5`, `R=16/5`, `H=1/5`. Its cap is `5√255/(5√255+512)>1/8`, because `35²·255−512²=50231>0`. On `[4/5,6/5]` the other branch is at least `1/7>1/8`.

The physical reference measure is weighted outside radius one. Accordingly the receipt is

`I₀=(1/8)∫_[4/5,6/5]min(r,1)dr=19/400`,

not the unweighted polar integral over the whole interval. Independently computing the bank measure as a length-2/5 rectangle minus a triangle of area `(1/2)(1/5)²` gives the same value. Already `3I₀−1/10=17/400>0`.

For `D_n={m_n≤M<2m_n}`, `m_n=(8/5)2^n`, `n≥1`, the accepted terminal theorem gives

`|S_r(D_n)| ≥ min(1/2,m_n−r)|D_n|/(2πm_n)`

on its fresh half-band `[m_n/2,m_n)`. Here `m_n≥16/5`, so the entire band is above radius one and contains the ramp breakpoint `m_n−1/2`. The integral is a constant-half-height rectangle minus its final triangular deficit:

`∫_[m_n/2,m_n]min(1/2,m_n−r)dr=m_n/4−1/8`.

Consequently

`C_n=1/(8π)−1/(16πm_n)`,
`πC_n ≥ 1/8−5/256=27/256=1/10+7/1280`.

This is monotone in m_n, with a positive dyadic increment `1/(32m_n)` in the normalized coefficient. It proves every later scale analytically, not by testing a finite list. No use is made of the old first-tail coefficient, and no charge is taken on `[6/5,8/5)`.

## 3. PL → IL is a valid conditional implication only

PL's proposed profile is `min(11/15,1−2r)`. Its crossing point is `a=2/15`. An independent evaluation starts with the uncapped parabola and subtracts the cap loss:

`∫_0^(1/2) r min(11/15,1−2r)dr`
`=1/24−∫_0^a 2r(a−r)dr`
`=1/24−a³/3=3311/81000`.

Since `3·3311/81000−1/10=611/27000>0`, π>3 gives the required IL rate. PL need only be used with V=L for this implication.

The displayed elementary two-endpoint identity in Section 2 is also correct. I checked its numerator by exact bivariate polynomial multiplication; the difference polynomial is identically zero. In the one-active-endpoint case, `M+N≥1` and `N<r` imply `M>1−r`, which supplies the asserted scalar bound by monotonicity. With both radii at least r, they can be decreased to sum one while staying at least r, so the factorized expression has the claimed nonnegative factors.

**These scalar facts do not establish PL.** Turning variable endpoint contributions into one physical-union bound is exactly the missing geometry; the note correctly refuses that inference. No attempt was made to prove PL or IL.

## 4. All-cut scope: what is and is not required

For the final scalar area implication, **IL for the whole low class L of every recovered low-height selector suffices**. The bridge never needs IL on a proper subcut of that particular L, nor a measurable allocation or Hall theorem. Likewise, the high and tail arguments only consume the full class receipts, although their accepted geometric theorems provide all-Borel-cut bounds.

This must not be weakened to a theorem solely for selectors whose *every* direction is low, i.e. `L=RP¹`. Recovery generally produces a mixed low/high family. Such a restricted whole-circle theorem does not directly pay the low subset here.

There is also no substantive distinction between the note's universal Borel-selector formulation of IL and its hereditary version on arbitrary Borel low cuts: given a Borel low selector on V, extend it on the complement by segments with endpoints `2u_q,3u_q` in a fixed Borel representative of each projective direction. These complement segments have height zero and far radius 3, so the extended selector has low class exactly V and preserves W(V). This is a logical clarification of the premise, not a proof of it. If one instead assumes IL only for the narrower class of actually recovered finite-valued-midpoint selectors, that premise still suffices for this final bridge, but the extension observation need not preserve that narrower class.

## 5. Recovery, disjoint physical capacity, and outer measure

Translate the star center to zero. For every open G containing E, each original anchored triangle lies in E by star-shapedness and is compactly contained in G. Keeping its midpoint fixed, nearby unit-segment directions vary continuously as unordered segments in Hausdorff distance; their triangles remain in G. A finite open cover of the compact projective direction circle, with first-neighborhood ownership, therefore yields a Borel finite-valued midpoint selector whose triangles all lie in G.

Crucially, **rerun the height dichotomy for this new selector**. If any new triangle has `|h|≥1/5`, its base-one area is at least 1/10 and already bounds |G| below. Otherwise all new heights are below 1/5, and the Borel functions M and |h| define the new exhaustive partition L,F,D₀,D₁,…. Original selector cuts or heights are not presumed preserved.

The parameterized triangle unions, and their joint polar incidence sets, are analytic and hence Lebesgue measurable. Thus ordinary polar integration on these recovered objects is legitimate even when E and its original selector are nonmeasurable. Individual zero-height triangles are not discarded; their union can have positive area.

Choose half-open banks

- L: `[0,1/2)`;
- F: `[1/2,4/5)`;
- D₀: `[4/5,6/5)`;
- D_n, n≥1: `[m_n/2,m_n)`.

They are pairwise disjoint; countably many boundary circles are null. Let A_j denote each class's literal triangle subunion restricted to its bank. Then pointwise `Σ_j 1_(A_j)≤1_W`. For `dν=min(1,1/|x|)dx`,

`Σ_j receipt_j ≤ Σ_j ν(A_j) ≤ ν(W) ≤ |W| ≤ |G|`.

On the low bank ν equals ordinary area, so IL is exactly the required low receipt. The finite-high rows charge different spatial annuli, not three independent copies of F. Direction-disjointness alone would not control overlap, but the bank disjointness does. No paired-lobe payment, P/Z split, or old terminal receipt is added on already spent radii.

Nonnegative monotone convergence justifies the countable sum, and the exhaustive Borel partition has total direction measure π. Therefore

`|G| ≥ (|L|+|F|+Σ_n|D_n|)/(10π)=1/10`.

In fact, for each recovered finite-valued-midpoint selector M is bounded, so only finitely many D_n are nonempty; the countable argument remains valid for general Borel selectors and needs no boundedness assumption on E. Infinite-area G is harmless. Infimizing the uniform inequality over open G gives `|E|*≥1/10`; it does not assert a strict lower bound for the infimum.

There is no centered-chord assumption, no equal-height hypothesis, no bound on the number of directions, no N=7 reduction, and no continuity assumption on the original choice of segments. A finite number of midpoint values is not a finite set of directions or triangles.

## 6. Executed evidence and limitations

I did not merely rerun the production checker (the parent already ran both modes). The independent in-memory reconstruction used

`/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python -B -c <independent code>`

through `subprocess.run`, with a 60-second timeout. It used exact Fraction arithmetic, a distinct nested-layer integral, rectangular-deficit tail integrals, a cap-loss PL integral, and direct polynomial multiplication. Arb was used only for the fixed π comparison. Exit status was 0, with:

```text
nested_step_F 446059/13962000
F_right_endpoint_slacks [19/1590, 0, 0]
F_cap_cross_square_residual 30359
F_cap_radical_residual 30359/13225
F_rational_pi_margin 340957/991302000
pi_223_over_71_certified True
D0_cap_cross_square_residual 50231
D0_raw 19/400 D0_pi3_margin 17/400
later_tail_min_area 27/256 margin 7/1280
PL_splice 2/15 PL_raw 3311/81000 PL_pi3_margin 611/27000
S_identity_difference_coefficients {}
INDEPENDENT_FIXED_ARITHMETIC_PASS; no PL or IL proof attempted
```

The arithmetic subprocess completed well under one second, within the requested cumulative budget. No optimization, numerical search, quadrature, repository writes, or pushes occurred. Only this requested report was written.

The production checker's `need` guards survive optimized Python, and its claims are appropriately limited to arithmetic. Its check `27/256>1/10` alone does not reconstruct the later-tail theorem or monotonicity; that analytical gap in *checker coverage* is supplied above, not a defect in the bridge. Likewise no arithmetic script proves Borel recovery, source-once accounting, or IL.

**Final disposition:** accept the full conditional implication as written. Keep the exact low integrated physical-union premise explicit. Do not promote the universal lower bound until that premise (or a different sufficient replacement) is proved.
