# Universal lower-bound audit: mathematics and efficiency

Audited worktree: `/home/argustest/research/star-kakeya-wt-v2-normalized`.
Pinned HEAD: `80a350d22571e677193f1ce2b2a30384e954b5b5`; working tree clean before and after the read-only checks. This report is the only new file created by this audit. No campaign, optimizer, broad build, or repository modification was undertaken.

## Verdict

**The lower-bound work contains genuine mathematics, not merely a numerical schedule masquerading as a proof. I found no fatal mathematical defect in the audited universal proof spine.** In particular, arbitrary sets, direction choices, zero-height needles, physical-union accounting, and the infinite high tail have identifiable, credible treatments. The latest v2 numerical certificate independently reran with `PASS`.

**Its apparent complexity substantially exceeds its mathematical content.** The latest 132-cell witness is exactly a seven-interval price table with three nontrivial mixing coefficients and one common rounding slack. Its positive-parameter continuum and pole-event sweeps collapse to elementary support guards for this particular witness. The terminal “first-birth” machinery is replaceable by a direct fixed-radius inclusion. A separately evaluated seven-interval table with small rational prices already proves the nearly identical floor **207/2500 = 0.0828**, using the same geometric ingredients. This is a simplification check, not a new search campaign or a claim of optimality.

Evidence levels must remain separate:

* **Lean endpoint present:** `q*pi`, approximately `0.0705448680793630762`, with an unconditional source theorem. I inspected the relevant project-owned import closure but did **not** rebuild Lean or obtain a fresh kernel axiom receipt.
* **Latest stronger endpoint:** `0.082812499999972190`, supported by paper-level geometry plus an outward Arb computation, **not Lean-certified**.
* **No sharp universal constant is established.** The schedule optimizes a lossy collection of inequalities, not the original geometric variational problem.

### Citation abbreviations

All paths below are relative to the pinned worktree.

* `L/` = `materials/STAR-SHAPED-KAKEYA-UPPER-LOWER-COMBINED-2026-07-31/lower-bound/04-lean/StarKakeyaLower/`.
* `ST/` = `archive/shared-terminal-082812/`.
* `SD/` = `archive/scale-dichotomy/`.
* `FR/` = `archive/final-radial-price-theorem/`.

The prompt's combined path `notes/paper/archive/shared-terminal-082812` does not exist; these are separate top-level directories. The latest result is actually in `ST/`, not in the main paper's lower-bound theorem.

## 1. Literal problem and quantified objects

`L/StarKakeyaSet.lean:145–168,210–241` defines:

1. `Plane = EuclideanSpace R (Fin 2)` and unoriented directions `AddCircle pi` (`:22–28`).
2. A unit needle has two endpoints at distance exactly one; its carrier is their **closed** segment.
3. A star-shaped Kakeya set has one center `o`, contains `[o,x]` whenever `x` belongs to the set, and contains one unit needle in **every** projective direction.
4. Neither the set nor the choice of needles is assumed measurable, bounded, closed, convex, or continuously movable.
5. The selected triangle is the union of segments from `o` to the needle; star-shapedness puts the entire triangle inside the original set.

The target is planar Lebesgue **outer** measure. The projective circle has total angular mass pi; the ordinary oriented polar circle has mass 2*pi. An individual strict lower bound does not make the infimum over all sets strict.

After translating the center to zero, write a selected chord as

`A=(s-1/2)u_q+h n_q`, `B=(s+1/2)u_q+h n_q`, `T_q=conv(0,A,B)`.

Its area is `|h|/2`. For the latest theorem define `M=max(|A|,|B|)` and `N=min(|A|,|B|)`. **Do not confuse this N with the old endpoint-capacity route's minimum radius along the entire segment.** They are different when the perpendicular foot lies inside the chord.

## 2. What the retained Lean route actually proves

### Endpoints

* Original baseline: `L/UniversalAssembly.lean:35–39,143–185` proves `100*pi/5599 < outerArea(E)`. The once-conditional first-arc input is discharged at `:168–181`, not left in the final theorem's hypotheses.
* Additive annular refinement: the main paper's `paper/star_shaped_kakeya_bounds.tex:3350–3386` proves `131*pi/6250`, using a measurable ball to separate confined and exterior capacity. It does not merely add two bounds for the same set.
* Strongest retained Lean endpoint: `L/EndpointCapacityFinal3527.lean:18–28` proves
  `forall E, StarShapedKakeya E -> ofReal(certifiedCoefficient*pi) <= volume.toOuterMeasure E`.
  It explicitly supplies both local estimates needed by its assembly. The rational coefficient is literally defined in `L/EndpointCapacityWitness64Data.lean:20–24`.

Independent Arb evaluation of the source rationals gave:

```
100*pi/5599      = 0.0561098884370386361575753417...
131*pi/6250      = 0.0658477820192420662781770053...
certifiedCoefficient*pi
                  = 0.0705448680793630762058018972...
```

`README.md:36–40,118–140` correctly distinguishes this endpoint from the then-newer paired paper/Python bound. Its 0.070544876... headline is not the current HEAD's strongest claim. `notes/05-progress-verdict.md:3–25` is an older baseline record, not evidence against the later theorem.

### Mathematical spine

**Geometry.** If `a` is the minimum radius along a unit chord and `M` its maximum endpoint radius, then `M^2 >= a^2+1/4`. This follows immediately by projecting zero to the tangential interval `[s-1/2,s+1/2]`: if the foot is inside, one endpoint has tangential magnitude at least 1/2; if outside, the farther endpoint is one unit farther along the line. The actual Lean statement is `L/EndpointCapacityGeometry.lean:65–90`.

**Fixed window.** Eligible directions have minimum chord radius at most `r` and an endpoint at least `R`, with `0<r<R`. A physical angular sliver expands to cover the corresponding chord direction with ratio `(R+r)/(R-r)`. Consequently the angular radial-superlevel mass is at least

`((R-r)/(R+r))*outerLength(eligible directions)`.

See `L/EndpointCapacityFixedWindow.lean:18–43,45–112`. It treats zero, positive, and negative side cases and quantifies over arbitrary direction sets and arbitrary selectors; measurability is not hidden in a choice operation. The payment kernel is therefore `r(R-r)/(R+r)`, not a sum of individual triangle areas.

**Finite schedule and nonmeasurable atoms.** There are 64 direction atoms and 127 radial rows (`L/EndpointCapacityLowConcrete64.lean:13–30,57–64`). Each row bounds its eligible class union, then a finite fractional-cover theorem combines the rows. The exact theorem requires pairwise-disjoint atoms, finite ambient measure, and a per-label weight lower bound (`L/EndpointCapacityFractionalCover.lean:201–211`). These are genuine hypotheses, not a general assertion that arbitrary scalar bounds can be added.

The key outer-measure fact is valid: outer evaluation induced by a measure is strongly submodular. Enclose A and B in measurable hulls with unchanged outer measure; measure additivity on those hulls proves

`mu*(A union B)+mu*(A intersect B) <= mu*(A)+mu*(B)`.

That is exactly the proof at `L/EndpointCapacityFractionalCover.lean:24–42`. Greedy marginal increments are nonnegative, sum to the total outer mass, and are dominated by each class union (`:52–91,213–243`). This closes the finite weighted cover without nonmeasurable Fubini.

**Radial integration and high tail.** The selected triangle union is radially down-closed (`L/EndpointCapacityLayerCake.lean:21–59`), and radial superlevel mass is antitone. Its left limit differs only on a countable set; the actual bridge is `L/EndpointCapacityLeftLimit.lean:20–66`. Low and countably many high radial ledgers are disjoint, and their integrals are joined before area is charged (`L/EndpointCapacityFinalAssembly64.lean:91–173`). Directional coverage uses subadditivity, not equality of masses of possibly nonmeasurable classes (`:175–223`). The high tail is uniform in every integer scale (`L/EndpointCapacityHighConcrete64.lean:250–281`). The two final concrete local obligations are actually discharged at `L/EndpointCapacityLowConcrete64.lean:451–472` and `L/EndpointCapacityFinal3527.lean:25–28`.

**Trust boundary checked.** A read-only import traversal found 39 project-owned modules in this endpoint's closure, no missing project imports, and no uncommented `sorry`, `admit`, `axiom`, or `native_decide` tokens. `L/Audit.lean:455` requests the final axiom printout. This is source-level evidence, not a new kernel replay; the terminal `.olean` was absent in this checkout, and no expensive rebuild was attempted. The reported three-axiom footprint remains a prior report, not a freshly reproduced observation.

## 3. Latest shared-terminal proof, reconstructed without slogans

### 3.1 Outer-measure recovery is legitimate

For any open `G` containing the original set, each originally chosen compact triangle lies in G. Fix its midpoint and vary only its unoriented direction: the segment, and hence its anchored triangle, varies continuously in Hausdorff distance. Therefore the same midpoint works for all directions in an open neighborhood. Compactness of the projective circle yields finitely many such neighborhoods; first-index tie-breaking gives a finite-valued **Borel midpoint selector** whose entire triangle union lies in G.

This is not a measurable-selection theorem about the original arbitrary selector, and it is not a finite set of triangles: the directions remain a continuum. The recovered union is an analytic image of a standard Borel parameter space times a compact simplex, hence Lebesgue measurable. Most importantly, rerun the height dichotomy **after** recovery; do not transfer the old selector's height cap.

This is the actual useful content of `ST/shared_terminal_all_cut_and_opr.md:3–11`; the explicit easy/hard rerun is also in `FR/final_theorem_checklist_20260817_zh.md:73–101`. No compactness assumption on E is needed. Infimizing over open G returns the outer-measure statement.

### 3.2 Easy branch and source measure

A recovered chord with `|h|>=1/5` gives area at least `1/10`. Otherwise all heights are below `1/5`. Partition directions into low `M<99/100`, finite high `99/100<=M<8/5`, and dyadic tail classes. These are Borel and exhaustive.

The high-side proof uses

`dnu = min(r,1) dr dtheta = min(1,1/|x|) dx`,

so `nu(W)<=area(W)` for measurable W. This change of measure is a deliberate loss outside radius one, not an equality with area.

### 3.3 Terminal collar: valid, but first-birth is unnecessary

For a direction cut V with `m<=M<=R`, take the first t units of each chord from its far endpoint, `0<t<=1/2`. Let `P_t(V)` be the union of their angular images.

The load-bearing estimate is

`|P_t(V)| >= t |V|/(pi R)`.

The proof really exists in `SD/low_scale_weighted_hall_bound_zh.md:94–145,174–180`: enclose the angular union in an arbitrary open set. For a component of angular length L, transverse projection of the collar endpoints gives

`t |sin(q-c)| <= 2R sin(L/2)`.

If `L>=t/R`, use the trivial projective length bound pi. Otherwise use `2 asin(2R sin(L/2)/t) <= pi R L/t`. Sum over open components and take their outer infimum. Degenerate radial collars are not deleted. I checked the inequalities and the circle/projective normalization.

**Shorter derivation:** every collar point has radius at least `m-t`. Hence, at each radius `0<r<m`, set `t=min(1/2,m-r)`. Radial star-shapedness gives the direct inclusion

`P_t(V) subset angularSection_r(W(V))`.

Thus, directly,

`|angularSection_r(W(V))| >= |V| min(1/2,(m-r)_+)/(pi R)`.

Multiply by any nonnegative radial price p and `min(r,1)`, then integrate. This proves exactly the latest terminal kernel

`H_m,R[p] = (1/(pi R)) integral p(r) min(r,1) min(1/2,(m-r)_+) dr`.

No first-birth time, Stieltjes integration, Hall matching, or fractional routing is needed for this statement. The more elaborate derivation in `ST/class_independent_terminal_price_report_zh.md:21–55` is sound after its inherited corrections, but adds no strength.

For completeness, `FR/h_tc_provenance_audit_20260817_zh.md:46–68` already acknowledges that `|{tau<=t}|=|P_t|` need not hold and that the terminal boundary term cannot be dropped. Its replacements are mathematically adequate. The direct radius proof bypasses both issues altogether.

### 3.4 Low and finite-high angular estimates

The basic interval lemma is elementary: if each circular interval J is extended to one side by at most `(Lambda-1)|J|`, then

`outerLength(union K) <= (2 Lambda-1) outerLength(union J)`.

Enclose the J-union in open components; each component can extend by at most `(Lambda-1)` times its length on each side. This handles repeats, arbitrary overlap, and singleton poles. See `SD/final-gate/near_diameter_all_radial_layers_audited.md:176–210`.

For a far endpoint of radius M and `|h|<=r<M`, the real component length is

`asin(|h|/r)-asin(|h|/M)`.

Extending it to its ideal chord-direction anchor yields dilation at most `M/(M-r)`, since `asin(z)/z` is increasing. The union coefficient is `(M-r)/(M+r)`. This derivation is in `SD/radial-price/low_one_sided_radial_extension_zh.md:39–95`. At `h=0` retain the radial ray; at `|h|=r` keep the closed touching component.

For low directions, both tangential endpoint magnitudes are at least `m=1-M0`; the two-sided small-radius estimate has coefficient `2/(2Lambda-1)`. If `|h|>r`, the whole endpoint-angle interval has length at least `alpha=2 asin(1/(2M0))`, with controlled ideal-anchor extension. The same interval may appear twice as a *base*, but the interval lemma charges its physical union once. See `SD/final-gate/near_diameter_all_radial_layers_audited.md:93–173,195–249`. For larger radii take the far endpoint and the uniform threshold `M>=1/2`; the high-offset supplement uses `alpha/(alpha+2 asin(2H))` (`SD/radial-price/low_one_sided_radial_extension_zh.md:101–117`). These are precisely the branches integrated by `ST/class_independent_terminal_strict_arb_v2.py:60–74`.

For the finite-high positive-height class, orient the chord toward its far endpoint. Then

`N(M,h)^2 = M^2+1-2 sqrt(M^2-h^2)`.

N increases with |h|. As a function of M at fixed h, N squared decreases and then increases, so its maximum on a closed interval is at an endpoint. At `M0=99/100`, `R=8/5`, `H=1/5`, the certifier finds `Nmax<5/8`; independent squared-radical arithmetic confirmed the R-endpoint guard with residual `-89759/2560000<0`. The M0 endpoint is smaller. All positive-price support is within `[5/8,4/5]`, safely above N and below M0. Thus the one-sided component formula is legal uniformly, and `(M-r)/(M+r)>=(M0-r)/(M0+r)`.

For exact poles, `N=|M-1|<=3/5`, whereas the pole-price support is `[31/40,4/5]` and `M>=99/100`. **The entire pole-price support is active for every finite-high M.** Consequently the pole receipt is constant in M for the frozen witness. The v2 general sliding-window event correction is valid but irrelevant to certifying this particular support.

### 3.5 Source aggregation and the infinite tail

Each price column is fixed before selecting a Borel cut. Its class demand is bounded by its price-weighted mass on the corresponding physical union, which is a subset of the full union W. Therefore

`sum demands <= integral_W (sum prices) dnu <= nu(W)`.

This is ordinary nonnegative integration with a pointwise price-load bound. It does **not** add unweighted areas of overlapping subunions. In particular, the terminal price is applied **once** to the whole finite-high block. The claimed repair of class-relative terminal ownership is real (`ST/shared_terminal_all_cut_and_opr.md:5–9`; `ST/class_independent_terminal_price_report_zh.md:59–73`).

For high class `[m,2m)`, a fresh radial band `[m/2,m)` receives the terminal kernel with denominator `2*pi*m`. The first class uses m=8/5; all later m are at least 16/5 and their radial bands are disjoint. The later exact coefficient is

`1/(8*pi)-1/(16*pi*m)`,

which increases with m. There is no finite-sample extrapolation. This is the formula in `ST/class_independent_terminal_strict_arb_v2.py:148–151`. The first tail has a different integral because its band crosses radius one; independently integrating it gives

`integral_(4/5)^(8/5) min(r,1) min(1/2,8/5-r) dr = 53/200`,

hence **pi times its coefficient is exactly 53/640 = 0.0828125**. For the first later class the corresponding area coefficient is `27/256`, strictly larger.

## 4. What was actually rerun

Read-only command, with the installed `python-flint 0.9.0`, Python `-B`, and 192-bit Arb:

```
python3 -B -c "import runpy,json; from pathlib import Path;
ns=runpy.run_path('archive/shared-terminal-082812/class_independent_terminal_strict_arb_v2.py');
print(json.dumps(ns['run'](Path('archive/shared-terminal-082812/class_independent_terminal_strict_witness.json')),indent=2))"
```

It returned `PASS`, pointwise source load upper exactly 1, and the following coefficient lower endpoints:

```
low                         0.02636003744959481548203793368...
terminal alone              0.00827420696499770333104611862...
positive + terminal         0.02636003744959252194597389827...
pole + terminal             0.02636003744958631291965570723...
first tail                  0.02636003744959516498672137330...
remaining dyadic tail       0.03357174580844667238874891883...
pi * common lower           0.0828124999999721904111374192974978881751...
```

The active row is pole plus terminal; all five target comparisons pass. This reproduces the public conservative floor, not merely a rounded float. I called the verifier's pure `run` entry to avoid its default receipt-file writes; I did not run the packaging wrapper or test suite.

Separate symbolic checks gave zero derivative residual for both radial logarithm primitives. Independent rational integration gave the tail values above. A second, independently assembled Arb evaluation verified the small-rational simplification below, without importing the verifier's primitive functions. Every arithmetic probe had a 60-second cap and completed within it.

## 5. The large schedule can be replaced by a small analytic certificate

The JSON stores 133 grid endpoints and five 132-entry arrays (`ST/class_independent_terminal_strict_witness.json:8–813`). Run-length inspection shows only these seven relevant intervals:

| Radial interval | low | terminal | positive | pole | first tail |
|---|---:|---:|---:|---:|---:|
| `[0,17/40)` | 1 | 0 | 0 | 0 | 0 |
| `[17/40,9/20)` | x | 1-x-epsilon | 0 | 0 | 0 |
| `[9/20,19/40)` | y | 1-y-epsilon | 0 | 0 | 0 |
| `[19/40,5/8)` | 0 | 1 | 0 | 0 | 0 |
| `[5/8,31/40)` | 0 | 0 | 1 | 0 | 0 |
| `[31/40,4/5)` | 0 | 0 | z | 1-z-epsilon | 0 |
| `[4/5,8/5)` | 0 | 0 | 0 | 0 | 1 |

The frozen exact values are

```
x = 316269962741/999999000000
y = 96233328491/142857000000
z = 9039395633/111111000000
epsilon = 1/999999000000
```

All later bands have their own full-price owner. Exact rational inspection verified that each of the three mixed intervals has load `1-epsilon`; all other live intervals have load one. So there is no 132-dimensional mathematical certificate here: there are three mixtures, one harmless rounding slack, four finite branch integrals, and one explicit monotone tail.

For a much more readable bound, use **x=8/25, y=67/100, z=2/25, epsilon=0**. This is not an optimized replacement; it is a hand-picked simplification of the actual nonzero runs. Independent exact/outward evaluation gave:

```
pi * low                 > 0.0828158999474078065269759718563
pi * (terminal+positive) > 0.0828033393326420627948480268688
pi * (terminal+pole)     > 0.0828966672506451300316546282796
pi * first tail          = 53/640 = 0.0828125
```

All are strictly above **207/2500**. Source load is identically one on each listed interval. Useful independent exact receipts are

```
pi * terminal = 665461/25600000
pole radial mass = 1449/80000
```

The positive integral is just the difference of

`Q_m(r)=-r^2/2+2mr-2m^2 log(1+r/m)`, with m=99/100,

at four rational endpoints; the low integral uses the explicitly stated small-radius splice and the same primitive with m=1/2. Thus an analytic exposition needs only these formulas, a few outward comparisons, and the support guards—not an LP, a dense parameter mesh, or a pole census. An entirely rational hand-proof would still need explicit elementary bounds for its logarithms and inverse trigonometric constants; I have not written those rational enclosures here.

Retaining the last digits of the current headline can likewise use the seven-row table with the three original fractions and their common epsilon. One could also solve the three equal-payment equations in x,y,z directly, but I did not launch another optimization or claim a new exact optimum.

## 6. Information losses and research judgment

1. **Old radial-gap compression:** `M^2>=a^2+1/4` replaces complete endpoint placement by two scalar radii. It discards near/far correlations, endpoint phase, and most of the triangle.
2. **Interval union compression:** replacing variable extensions by their worst dilation loses placement information and correlation between the two endpoint lobes. It is a valid union inequality, not generally sharp on legal chord families.
3. **Latest low branch:** the uniform far-endpoint threshold 1/2 ignores actual larger endpoints, and its payment stops at radius 1/2. The fixed `M0=99/100,H=1/5` low-kernel full-price ceiling was independently evaluated as
   `0.0853207286630382065608659335857...` after multiplying by pi.
   No refinement of prices or high classes with this **same fixed low kernel** can reach 0.1. This is a method ceiling, not an upper bound on the geometric infimum, and not a ceiling for every possible choice of M0 or H.
4. **Terminal compression:** the same block uses the smallest endpoint radius m and the largest endpoint upper bound R, then the coarse transverse-projection constant pi. The all-unbounded-block version would give zero by R tending to infinity. Keeping fresh high-scale bands is essential; more computation cannot rescue an infinite global-worst denominator.
5. **Weighted area compression:** outside the unit disk, `dnu<=dx` spends only inverse-radius-weighted area. This makes a robust tail theorem but ignores substantial physical capacity.
6. **Scalar minimum compression:** the last step uses the worst branch payment. The current near-equality to 53/640 reflects a saturated first-tail receipt and nearly balanced artificial branch prices; it is not evidence of a star-shaped Kakeya extremizer near that area.
7. **Complexity without strength:** first-birth ownership, the generic pole-event sweep, and most grid cells are removable from the latest fixed-witness proof. They may be useful infrastructure for other witnesses, but they do not explain the quality of this bound.

## 7. Recommended next action and limits of this audit

**Do not resume the old schedule campaigns.** First replace the latest lower-bound exposition by a compact proof organized as: open-envelope Borel recovery; one interval-expansion lemma; direct radial terminal inclusion; seven-row price table; four integrals plus the monotone tail. State 207/2500 in the main theorem if readability is the priority, and keep the original three fractions as an optional sharper corollary. Formalizing that compact theorem would be more valuable than adding decimals to the existing price search.

For a genuinely stronger conceptual advance, demand a new geometric inequality retaining endpoint/phase or two-lobe correlation and prove its literal physical-union form before optimizing it. The inspected existing scalar mechanism is already near its fixed low-side ceiling; another large schedule is not the right default.

Scope limits:

* This is a source-and-mathematics audit plus bounded exact/outward checks, not a fresh end-to-end Lean kernel verification.
* I inspected the terminal Lean statement, its 39-module project-owned closure for proof-hole tokens, and the load-bearing geometric/aggregation interfaces; I did not line-audit every elementary proof in every imported module or mathlib.
* The latest positive-class estimate was re-derived on the actual active support; it was not accepted merely because a contract string called it “audited.” The same applies to terminal geometry and outer recovery.
* No upper-bound claim, literature priority claim, global optimality claim, or old failed campaign was assessed here.
* Some UTF-8 Markdown was classified as binary by the file reader; it was read successfully with Python. One attempt to use the archive's named external interpreter was blocked by the tool's path guard; the installed Python/flint environment successfully executed the same arithmetic at 192-bit precision. Neither issue invalidated or replaced a mathematical check.

**Bottom line:** retain the lower-bound theorem as credible, distinguish its formal and paper/computer-assisted levels honestly, and radically compress the proof. The main weakness found is mathematical inefficiency and severe information loss—not an uncovered fatal quantifier or source-capacity error.
