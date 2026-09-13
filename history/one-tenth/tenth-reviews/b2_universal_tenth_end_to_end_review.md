# Independent end-to-end review: IL and the universal one-tenth bound

## Verdict

**ACCEPT_UNIVERSAL_0P1.** The integrated-low proof at `ed84c269e743177aaf1d3776df6ec5eefa05a9f6` discharges the precise IL premise consumed by the disjoint-bank bridge at `d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da`. Independently reading the new source geometry, the baseline recovery/terminal proof, and B1 Theorems 1–3 reveals no remaining mathematical obligation in this composition.

The resulting statement is:

> For every subset E of the Euclidean plane, if there exists o such that [o,x] is contained in E for every x in E, and E contains a closed unit segment in every unoriented direction, then its Lebesgue outer area satisfies **|E|* ≥ 1/10**.

E need not be measurable, bounded, closed, or convex. Its original segment choices need not be measurable or continuous. Neither a centered/equal-height assumption nor any finite-direction/cardinality restriction is present. PL is not an input, and its refutation does not affect this proof. This is acceptance of a **human mathematical proof with checked exact arithmetic**, not a Lean theorem, a claim of sharpness, or a claim about historical priority.

## 1. Exact source identities and intake

All paths below are relative to their named repository. Both working trees were clean at intake. The mathematical files read from disk were checked against `git show` at the pinned revisions, byte for byte; their equality was verified, not presumed from a branch name.

### Integrated-low authority

Repository: `/home/argustest/research/star-kakeya-wt-01-b2-integrated-low`.

- Commit / live HEAD: `ed84c269e743177aaf1d3776df6ec5eefa05a9f6`.
- Root tree: `a0a42733458cbf477b0eb615f028334c8a3e681a`.
- `research/one-tenth/low-source-b2/integrated-low` tree: `a16f17169aa1b676933deef61eb8c80a0d362c2c`.
- Its `PROOF.md` blob: `4b22b923735e5cbb951652f5d69a0dffe21d96c5`.
- Its `PROOF.md` SHA-256: `5aa5785306678977117009c3abece49fda74b348230b592deaacd8bef2f0da84`.
- Its `check.py` SHA-256: `cca8e45b567b51ebd6bd6f3fd68a7cfea997d08d270a2865768f11481eb389db`.

### Conditional-assembly authority

Repository: `/home/argustest/research/star-kakeya-wt-01-short-integration`.

- Pinned commit: `d9a3f3c1b9718fd68b9f95cf10bb2cdd32bb16da`.
- Pinned root tree: `a6fa35b86b27c32a5267ba8116aa17f04ad0cab5`.
- Pinned `research/one-tenth/endpoint-geometry-b1` tree: `f0b4afea309e1e3a74c34744dcdb35bfddfc0c05`.
- `CONDITIONAL_TENTH_BRIDGE.md` blob: `ad6de4c574966560379e81fac8df74e662903fd4`.
- Its SHA-256: `b0bebfd0cfccbe2b3a18dc800dec07088b970149a79c8bb0e9ba203b33ed1467`.

The integration repository's observed live HEAD had advanced to `65982b57a1fbdd557ed0c185c445a521c2f08204`, root tree `48f8429617110b0519a5a6bc5e04ed570ef12a5a`. This is **not** substituted for the requested authority: `git diff` showed no changes between the pinned commit and live HEAD in the bridge, baseline proof, or endpoint-domain proof; the bridge bytes were additionally compared directly to the pinned blob.

### Common dependencies: exact identity across both pinned commits

| Dependency | Subtree identity | PROOF.md blob |
|---|---|---|
| `research/one-tenth/baseline` | `0e7fd0ec086e939d5b9a557c1331f8e987129471` | `d421e96d7e2092dfe18f49eaa696f30202ca7ecf` |
| `research/one-tenth/endpoint-geometry-b1/endpoint-domain` | `fcce0ecf4ec73acd2f4087a709fc2bd80e9f3d71` | `d7809d1f77c11a52d19bb2eed3117e1905a4fd85` |

SHA-256 values of those proofs are respectively:

- Baseline: `e7efd88757d39dd7f436d2f6993a652941ff4aa4c4c6a30baaece1d43fadc33c`.
- Endpoint-domain: `6aeb43ee26bda0d432f1af5b8778fdc89aed58d6ccdaa00d295674ca5e4913b4`.

Thus there is no incompatible-version splice in the imported recovery, interval lemma, cone geometry, or terminal receipt. I read both complete proof files, not just previous verdicts. The existing `b2_conditional_bridge_review.md` was read as contextual corroboration after the primary proofs; it was not used to replace the independent composition.

## 2. Trusted inputs and what was independently checked

The proof uses the following standard mathematical background: compactness of RP¹; continuity in Hausdorff distance of a segment and its anchored triangle under changes of direction at fixed midpoint; elementary Euclidean geometry/calculus; analytic images/projections of Borel parameter spaces and their Lebesgue measurability; polar integration, Tonelli/monotone convergence, and outer regularity of Lebesgue outer measure. The projective-to-physical angular covering is locally length preserving. These are the ordinary human-proof foundations, not machine-formalized inputs.

The source-specific dependencies were independently inspected as follows:

1. **Baseline §1:** open-cover Borel recovery, the post-recovery height dichotomy, and the analytic-union interface.
2. **Baseline §2:** the arbitrary-family circular interval-union lemma, including repeats and singletons.
3. **Endpoint-domain §§1–3:** joint endpoint coordinates, actual circular sections including radial filling, and one application of the interval lemma to the capped far bases.
4. **Endpoint-domain §4, Theorem 2:** the bounded-radius cone cap, with all domain guards checked at F and D₀.
5. **Endpoint-domain §§5–6, Theorem 3:** the low straddling far-cone cap used by IL, including its endpoint-maximization proof.
6. **Baseline §§3 and 6:** direct terminal collar inclusion and the exact increasing all-scale tail coefficient.
7. **New IL §§2–4:** eligible-anchor physical-union receipt, complementary prices, class cancellation, and exact integral constants.

Neither the old optimized seven-row schedule nor its decimal lower bound is needed. No transport/Hall theorem, finite N=7 reduction, PL, or unproved per-label additivity is trusted or used.

## 3. Independent review of IL's physical source geometry

Write a chord, oriented toward a Borel choice of far endpoint, as `(x−1,h),(x,h)`. Then `x≥1/2`, `z=|h|`, `M²=x²+z²`, and `N²=(1−x)²+z²`. For every low direction, `M<99/100` implies `x<1`, so the chord genuinely straddles its perpendicular foot. N is an endpoint radius, not the distance from the origin to the segment.

For z>0, let `b=atan(z/x)`, `c=atan(z/(1−x))`, and `γ=π−b−c`. On the actual side of the chord the cone is `[b,π−c]`. The radial roof on a ray of angle φ is `z/sin φ`. Therefore:

- At `0<r≤z`, the **whole cone** is present.
- At `z<r`, intersect the cone with `[0,a]∪[π−a,π]`, where `a=asin(z/r)`.

This is a statement about the filled triangle, not only its base segment. Changing the sign of h changes the physical side used to describe these intervals; it adds no reflected source.

### Eligible endpoints and extension bounds

For a Borel V in the low class, put `B={q∈V:N≥2/5}` and `U=V\B`. Select the far endpoint for every direction, and additionally select its near endpoint precisely on B. All selected radii are at least 2/5.

For `0<r<2/5`:

- In the cone case `r≤z`, the far extension/base ratio is at most B_L. The endpoint-domain proof establishes `1/(1+2B_L)>11/15>2/3`, hence this ratio is below 1/4. That proof is valid for arbitrary varying x,z: for `A=1+1/B_L`, the derivative sign of `atan(z/(1−x))+A atan(z/x)` has an increasing numerator, so its maximum is at x=1/2 or x=1, both controlled. This does not assume centered chords or a fixed height.
- A selected near endpoint has `z/N≤1/2`; also `z/M≤1/2`. Thus `b,c≤π/6`, `γ≥2π/3`, and its extension ratio `c/γ≤1/4`. **This near-endpoint hypothesis is not imposed on far-only directions.**
- In the lobe case `z<r<2/5`, the selected endpoint radius R satisfies `R≥2/5>r`. Because x<1, the complete far/near lobes are actually `[b,a]` and `[π−a,π−c]` whenever selected. For `β=asin(z/R)`, monotonicity of `asin(t)/t` gives `β/a≤r/R`, whence `β/(a−β)≤r/(R−r)≤r/(2/5−r)`.
- If z=0, every selected ideal anchor is an actual radial ray reaching beyond r. It is a singleton base with zero extension, not a discarded zero-area label.

Apply the interval-union lemma **once** to all of these bases, with `ρ=max(1/4,r/(2/5−r))`. Its proof encloses the union in an open angular set: a base in a component of length ℓ has its extension inside that component enlarged by at most ρℓ on each side. Summing component lengths and infimizing gives the factor `1+2ρ` for arbitrary families. Repeated full-cone bases are harmless because only their physical union is measured.

The extended union contains one ideal far lift of V and the opposite ideal near lift of B. These two Borel lift sets are disjoint: any equality of physical anchors implies equality of their projective directions, whereas for the same direction the two selected anchors are antipodal. A Borel single lift has physical angular length equal to projective direction length. Hence their total length is `|V|+|B|`, not `2|V|` and not a sum of actual triangle arc lengths.

It follows that

`|S_r(V)| ≥ min(2/3,(2/5−r)/(2/5+r)) (|V|+|B|)`.

**This is a valid new physical-union receipt.** The extra census concerns disjoint ideal anchors, while all actual bases have already been merged. It does not repeat the false variable-coefficient inference underlying PL.

### Outer receipts and overlap

On U, the unit-chord triangle inequality `M+N≥1` and `N<2/5` imply `M>3/5`. On all V, `M≥1/2`. For `1/5<r<1/2`, z<r for every label. Straddling guarantees that the far lobe is not truncated by an exterior-foot cone. The same single-family extension argument gives

`|S_r(V)|≥k5(r)|V|`, `k5(r)=(1/2−r)/(1/2+r)`,

`|S_r(U)|≥k6(r)|U|`, `k6(r)=(3/5−r)/(3/5+r)`.

The IL ledger uses eligible anchors only on `(0,1/5)`, all-far k5 on `[1/5,7/20)`, and on `[7/20,1/2)` uses k6 for U at price λ and k5 for V at price 1−λ. Since `W(U)⊆W(V)`, the last bank satisfies the literal pointwise capacity inequality

`λ 1_W(U)+(1−λ)1_W(V) ≤ 1_W(V)` for `0≤λ≤1`.

Thus the two bounds are not improperly added at full price. These interior IL banks together consume at most one unit of area density throughout the low disk, allowing that disk to be treated as one fully paid bank in the global assembly.

### Constant and hereditary scope

With C4,C5,C6,D5 as defined by the four integrals in IL §3, the physical receipt is

`C4(2|B|+|U|)+C5(|B|+|U|)+λ C6|U|+(1−λ)D5(|B|+|U|)`.

The exact guard `0<C4<C6` makes `λ=C4/C6` admissible. Both class coefficients then equal

`C*=2C4+C5+(1−C4/C6)D5`.

The exact checks below independently establish `C*>637/20000>71/2230>1/(10π)`. Therefore IL holds for **every Borel low subcut V**, and in particular for the low class of every mixed recovered selector. It is not merely an all-low/full-circle statement. Analytic triangle unions and joint polar incidence justify the integrations. Null cuts, tangency radii, radius endpoints, and zero-height directions are covered; countably many bank boundary circles can be assigned either way.

## 4. Recovery and the correct height dichotomy for arbitrary E

Translate o to zero. Let G be any open superset of E. If G has infinite area the desired inequality is immediate; otherwise the same construction below applies without needing E to be bounded.

For each direction choose an original unit segment. Its entire anchored triangle is contained in E: each point of the base segment lies in E, and the segments from zero to all those points fill the triangle. The triangle is compactly contained in G. Keeping its midpoint fixed while varying the unordered direction gives a Hausdorff-continuous family of triangles, so this midpoint works on an open neighborhood in RP¹. Finitely many neighborhoods cover RP¹. First-neighborhood ownership gives a finite-valued Borel midpoint selector whose **continuum of triangles** lies in G.

The selected endpoints can be ordered Borel-measurably using a Borel projective representative; endpoint reversal at seams does not affect the unordered segment or its triangle. The recovered W and all Borel subunions W(V) are Borel images of standard Borel direction/simplex parameter spaces, hence analytic and Lebesgue measurable. Their joint polar incidence sets are analytic as well. No measurability of E or of the original choices is asserted.

Now rerun the dichotomy on the **new selector**:

- If any recovered chord has `|h|≥1/5`, its base-one triangle has area `|h|/2≥1/10` and is contained in G. This already settles G.
- Otherwise **all recovered heights** satisfy `|h|<1/5`. Only now define the recovered Borel cuts L,F,D₀,D₁,…. All the IL/B1 height hypotheses permit this strict case through their weak bound `≤1/5`.

It would be incorrect to carry over the original heights or cuts without this step. The actual proof does not do so. Finite-valued midpoints are not finitely many directions, nor a seven-triangle hypothesis; the baseline's seven rows were prices in an older certificate.

## 5. High/tail receipts and their exact applicability

B1 Theorem 2 assumes `0<H≤1/2`, `m≥1/2`, `R≥max(m,sqrt(1/4+H²))`, and `m≤M≤R`, `|h|≤H`. Its all-cut kernel on `0<r<m` is

`min(K_R,H,(m−r)/(m+r))`, where `K_R,H=sqrt(R²−H²)/(sqrt(R²−H²)+2R²)`.

Its proof retains the actual capped far base for exterior-foot chords. For z>0,

`γ=∫_(x−1)^x z/(t²+z²)dt≥z/M²`, `b≤z/x`,

so `b/γ≤x+z²/x≤R²/sqrt(R²−H²)`. The monotonicity uses `x≥1/2≥z`, which is satisfied here. For z=0 the actual far ray supplies the singleton. Thus F and D₀ are not silently restricted to straddling chords or nonzero height.

Use `H=1/5` and the following receipts per radian of projective direction length:

| Class | Parameters / physical bank | Certified receipt coefficient |
|---|---|---|
| `L={M<99/100}` | IL on `[0,1/2)` | `C*>1/(10π)` |
| `F={99/100≤M<8/5}` | `m=99/100,R=8/5`, bank `[1/2,4/5)` | `I_F=446059/13962000>1/(10π)` |
| `D₀={8/5≤M<16/5}` | `m=8/5,R=16/5`, bank `[4/5,6/5)` | `I₀=19/400>1/(10π)` |
| `D_n={m_n≤M<2m_n}`, `m_n=(8/5)2^n`, n≥1 | Baseline terminal kernel, bank `[m_n/2,m_n)` | `C_n=1/(8π)−1/(16πm_n)≥27/(256π)>1/(10π)` |

All Theorem 2 parameter guards hold; all its charged radii are below m. Allowing `M≤R` covers the strict upper-radius cuts without any limit argument.

For F, `K_F=5√63/(5√63+128)>7/30`. The right-endpoint step bounds on `[1/2,3/5)`, `[3/5,7/10)`, `[7/10,4/5)` are respectively `7/30,29/169,19/179`. The rational branch decreases with r; the cap is above each step. Integrating r times these steps gives I_F. The receipt is `I_F|F|`, not `π I_F|F|`; multiplying by π is only the normalized full-direction comparison with 1/10.

For D₀, `K_D0=5√255/(5√255+512)>1/8`. The rational branch on `[4/5,6/5)` is at least 1/7. The relevant weight crosses r=1, so the correct coefficient is

`I₀=(1/8)(∫_(4/5)^1 r dr+∫_1^(6/5)1 dr)=19/400`.

For later D_n, the baseline collar argument requires only `m_n>1/2` and far endpoint radii at most `2m_n`. A far collar of length `t=min(1/2,m_n−r)` stays outside radius r; radial filling puts its angular image into S_r. The open-component projection argument bounds each component's associated projective directions and yields

`|S_r(D_n)|≥min(1/2,m_n−r)|D_n|/(2πm_n)`.

I checked the component proof, not just its quoted coefficient: short components of length ℓ give `t|sin(q−c)|≤2(2m_n)sin(ℓ/2)` and therefore projective length at most `π(2m_n)ℓ/t`; long components use the trivial projective length π. Radial collars and arbitrary Borel cuts are included.

Since `m_n≥16/5`, the entire later bank lies above one. Its integral is the half-height rectangle with final triangular deficit:

`∫_(m_n/2)^(m_n) min(1/2,m_n−r)dr=m_n/4−1/8`.

Dividing by `2πm_n` gives the displayed C_n. The normalized coefficient `1/8−1/(16m_n)` increases with m_n, with least value 27/256 at n=1. This proves the countable tail analytically; no finite-sample extrapolation is used. The first later bank is exactly `[8/5,16/5)=[1.6,3.2)`. The gap `[6/5,8/5)` remains unspent.

## 6. Final physical capacity and outer-measure passage

For each class j let A_j be its literal triangle subunion restricted to its designated bank. Choose half-open radial endpoints. The banks

`[0,1/2), [1/2,4/5), [4/5,6/5), [8/5,16/5), [16/5,32/5), …`

are pairwise disjoint. Consequently `Σ_j 1_Aj≤1_W` pointwise, even if the unrestricted triangle subunions overlap extensively. Direction-disjointness alone would not suffice; this proof uses physical radial disjointness. The IL disk already respects its own internal complementary-price capacity.

Use the same positive measure throughout:

`dν=min(r,1)dr dθ=min(1,1/|x|)dx` away from zero.

Its density with respect to ordinary area is at most one, so `ν(W)≤area(W)≤area(G)`. Inside the low disk ν is **exactly ordinary area**, matching IL. Nonnegative monotone convergence gives

`area(G) ≥ ν(W) ≥ Σ_j ν(A_j)`

`≥ C*|L|+I_F|F|+I₀|D₀|+Σ_(n≥1) C_n|D_n|`

`≥ (|L|+|F|+Σ_(n≥0)|D_n|)/(10π)=1/10`.

The direction cuts are exhaustive Borel sets: each recovered unit segment has finite endpoint radii, M≥1/2, and falls into exactly one class. The total projective direction length is π, while angular sections were always measured on the physical circle of length 2π. The normalization is consistent at every step. A particular finite-midpoint recovery actually has bounded M and only finitely many nonempty tail classes, but the countable proof is valid independently of that observation.

Every open G containing E is therefore large enough, either by its post-recovery high triangle or by this sum. Taking the infimum over open supersets yields `|E|*≥1/10`. There is no assertion that a strict inequality survives the infimum, and the high-triangle equality boundary is already handled by the non-strict target.

## 7. Executed exact arithmetic and verification limits

Only tiny deterministic fixed-constant checks were run. No search, parameter sweep, installation, optimization, source edits, or auxiliary output files were used. The independent reconstruction ran in memory via `python3 -B -c`, with a 60-second hard timeout, and completed with exit 0; its measured internal elapsed time was 0.016584 seconds.

For independence from the production log routine, I used the alternating expansion of `log(1+y)`, 60 terms, with the next-term rigorous bound (all required y lie strictly between zero and one), rather than the production atanh series. The integrals were reconstructed after the substitution `u=m+r`, whose integrand is `−u+3m−2m²/u`. For π I used the standard Machin identity and alternating arctangent bounds, not a floating approximation or a library decimal. The result certified `π>223/71`.

Selected actual output:

```text
Cstar exact bracket: 3188518396511/10^14 < Cstar < 3188518396513/10^14
price 0<C4<C6, 0<lambda<1; IL exact floor: PASS
Machin alternating-series pi>223/71: PASS
F per-radian 446059/13962000
F right endpoint slacks [19/1590, 0, 0]
F cap square residual 30359
D0 cap square residual 50231
F normalized rational margin 340957/991302000
D0 per-radian 19/400; pi>3 margin 17/400
Tail normalized minimum 27/256; margin 7/1280
Low rational normalized margin 51/1420000
INDEPENDENT_FIXED_ARITHMETIC_PASS
```

I also inspected and ran the pinned IL `check.py` bytes in memory in both normal and optimized Python, with `-B` and 60-second per-child timeouts. Both exited 0; their measured internal runtimes were 0.001890 and 0.001913 seconds. They verified all four displayed integral closed forms and returned:

```text
lambda=C4/C6 [0.928184585020938, 0.928184585020938]
Cstar uniform all-cut coefficient [0.031885183965120, 0.031885183965120]
EXACT: Cstar > 637/20000 > 71/2230 > 1/(10*pi)
EXACT rational full-direction margin over 1/10: 51/1420000
NEW MIXED CERTIFICATE PASSES; continuum proof requires independent review.
```

The printed equal decimal endpoints are diagnostic rounded displays, not exact singleton enclosures. The strict comparisons were rational interval comparisons. The same script's earlier `FIXED CERTIFICATE FAILS` message refers to its deliberately retained λ=1 precursor; it is not a failure of the final complementary-price certificate. No geometry is inferred merely from these arithmetic passes: Sections 3–6 above supply the independently read and checked human argument.

## 8. Disposition and issues

| Obligation | Disposition |
|---|---|
| IL geometry for arbitrary varying low chords and Borel cuts | ACCEPT |
| Near/far ideal-lift disjointness, actual-base union accounting | ACCEPT |
| Complementary low-bank prices and constant cancellation | ACCEPT |
| B1 Theorem 2 hypotheses on F and D₀, including poles/exterior feet | ACCEPT |
| Recovered height ≥1/5 branch and new low-height partition | ACCEPT |
| Fixed disjoint banks and ν≤ordinary area | ACCEPT |
| All later scales, minimum 27/256, countable sum | ACCEPT |
| Arbitrary-set outer-measure quantifiers | ACCEPT |
| Dependence on PL, centered/equal-height, or N=7 | NONE |
| Remaining missing mathematical obligation for ≥1/10 | NONE FOUND |

The older source headers saying the global target is open are status labels predating this completed composition, not additional hypotheses or an obstruction to the proof. I have not edited those headers. The advanced live integration HEAD was explicitly resolved to unchanged pinned proof bytes. No execution blocker or mathematical defect was encountered. A final read-only status check found a newly present untracked `research/one-tenth/THEOREM_01.md` in the integration repository, absent at intake; it was not created, read, modified, or relied upon by this review. The integrated-low repository remained clean. This concurrent artifact does not change any pinned authority or this verdict.

**Final disposition: ACCEPT_UNIVERSAL_0P1.** Only this requested review file was created; repository sources were not modified.
