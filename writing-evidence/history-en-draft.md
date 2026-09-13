# From 0.03 to 0.1: a history of the star-shaped Kakeya lower bound

## The triangle that made the question tractable

Take a unit segment in a planar set and join every point of that segment to one common centre. Star-shapedness forces the whole resulting triangle into the set. If the segment lies at distance h from the centre, this triangle has area |h|/2. A single sufficiently distant segment therefore proves a lower bound immediately. The difficult configurations put all their segments close to the centre and let the triangles overlap.

Our question was about this difficult overlap, not about rotating one particular segment continuously. An admissible set contains a complete closed unit segment in every unoriented direction and is star-shaped about one point. It need not be measurable, bounded, or equipped with a continuous choice of segments. We measure it by Lebesgue outer area. Write A* for the infimum of these outer areas.

The external starting point used in the project was Li's π/98, approximately 0.032057. His article develops circular-section estimates and recalls Cunningham's earlier π/108. The same article also states the numerical refinements (0.01030…)π and (0.01050…)π in §4.1. Calling π/98 the starting point identifies the explicit baseline we used; it does not erase those further claims or certify their omitted decimal digits. The retained arXiv v2 copy carries the journal information on its first page. [LI]

To improve a section estimate is to show that a family of required directions must occupy more of a physical circle. Integrating suitable section bounds can then force more area. This connection remained useful throughout the project. What changed repeatedly was which geometric information the section estimate retained, and how different estimates were allowed to share the same material.

## A better covering estimate, and two repairs before it became a theorem

The July 31 records identify an early avoidable loss: a factor three introduced by a covering-selection argument. For a family of circular intervals, concentric dilation by a factor c≥1 can instead be controlled directly through the components of an open set enclosing their union. The enlarged union has outer length at most c times the original outer length. One does not first discard intervals to select a disjoint subfamily and then pay an additional covering factor. [E2, E4]

This improvement required geometric containment, not merely a comparison of individual interval lengths. It also required knowing which circle was being used. Physical angles range over a circle of length 2π; unoriented segment directions range over one of length π. An interval that fills one need not fill the other. These distinctions eventually became explicit obligations in the Lean development.

Removing the covering loss did not instantly produce a valid global theorem. An attempted iterative rescaling applied a full-direction conclusion to a family carrying only some of the directions. Rescaling did not restore the missing directions. The project therefore moved to a non-iterative argument. A second obstruction was a source-scope mismatch: the parameters required an auxiliary radius greater than 1/2, outside the range of the cited result in Li's argument. The repair was an independent projective-angle, greedy-selection and residual-fan proof, not a claim that the desired geometric conclusion was false. [E4, E5]

The corrected paper argument gave π/56. Parameter refinement within that framework then gave 100π/5599, approximately 0.056110. This was a useful improvement of a fixed proof mechanism, not a proof that the parameter family had been globally optimized. The distinction matters historically: the early arithmetic kernels were already working while geometric and outer-measure bridges remained unfinished. The eventual unconditional Lean endpoint for 100π/5599 arrived only after those bridges were supplied. The retained π/56 material includes a paper proof and arithmetic Lean modules, not a separately located unconditional geometric Lean endpoint. [E3, E6, E7, LA]

Formalizing the early endpoint geometry also forced a choice about what could legitimately vary continuously. The original needle selector was arbitrary; adding continuity to it would prove a different theorem. A proposed repair through a compact correspondence of all feasible supports was itself later retired. The working route proved contact and endpoint containment point by point, through `Figure5LocalContact` and `UniversalEndpointClosure`, without taking an extremum of the chosen family. The history records a failed route, a repair that was also abandoned, and then a simpler local proof. It is not adequately described as translating a settled argument into Lean. [E8]

## The first substantial change: add contributions from different places

The next question changed the structure of the calculation. Instead of asking which of two direction classes gives the better estimate on the entire set, could the confined class pay inside a ball and the escaping class pay outside the same ball?

Two lower bounds for one area can be combined by taking their maximum; they cannot simply be added. A bound for the material inside a measurable ball and another for the material outside it are different. If B is that ball, then outer measure satisfies

m*(E) = m*(E∩B) + m*(E∖B).

This identity remains available when E itself is not measurable. It turns a geometric separation of the payments into a legitimate addition. [N1]

The exterior argument still had work to do. It paid from exterior portions of selected triangles and from a residual radial fan, with the relevant overlap controlled. It could not count the same exterior material once as a triangle and again as part of the fan. The resulting annular route produced 131π/6250, approximately 0.065848.

A surviving proof note presents this result relative to previously established paper lemmas and a numerical hypothesis. The later Lean development constructs its own needed ingredients and discharges the hypotheses. These are different artefacts at different stages. Reading only the conditional note would miss the completed endpoint; reading only the endpoint would hide why the annular idea was new. [N1, LA]

## From one cut to a radial schedule

On August 3 the project developed a different way to use a unit segment. It tracked the segment's nearest and farthest distances from the centre and the radial slices that its star triangle must occupy. The nearest distance here is the minimum over the whole segment. Later, in the 1/10 proof, a symbol for a near endpoint means something different. Confusing the two would change the geometry.

The radial-sliver argument first gave 1/15. Adjusting the rational height threshold gave 1717/25000, or 0.06868, without changing the underlying geometry. A finite-cover argument and a more flexible radial allocation then gave 7/100 and 141/2000. The notes explicitly retain these intermediate results, and their addition commits support this order. They were not reconstructed by applying the final 1/10 theorem backwards. [N3–N7]

A radial schedule specifies which geometric class is paid on which radial intervals. It must pay every permitted class and stay within the capacity of the actual set. Its finite tables are not a finite sampling of the direction circle: each entry stands for an entire class of possible segments. The passage from finitely many classes to arbitrary direction choices is part of the proof.

The 32-class endpoint was followed by a 64-class schedule. The latter yielded qπ≈0.07054486807936307, where q is a specific long rational number retained in the source. Its strict corollary 3527/50000 is shorter to print but is not the full coefficient. Rational enclosures of logarithms made the schedule's payment provable; the optimizer's floating-point value was not the theorem. A subsequent paired construction supplied a separately certified, slightly larger implicit constant near 0.07054487627351847. The paired certificate and the qπ Lean theorem must remain separate entries. [N8, N9]

At this stage four independent early Lean endpoints can be located: 100π/5599, 131π/6250, 141/2000, and qπ. Their local import closures contain no OneTenth module. The source thus preserves distinct proof routes, not just several numerical corollaries of one final theorem. [LA]

## The tempting 0.0975576 that did not survive

A chronological account must now interrupt the ascending list of constants. On August 16 a candidate suggested approximately 0.0975576139796, already close to one tenth. Its arithmetic and several adapters survived review. Its central area estimate did not. [F1]

The proposed argument assigned each output a unique witness and a unique low endpoint. That sounded like counting each contribution once. But many different outputs could still use the same physical source atom, described by an endpoint and a height. Uniqueness for each output did not limit the total burden placed on that source.

Imagine several receipts, each with exactly one named payer. This tells us where each bill went; it does not tell us whether the payer has enough money for all the bills. The geometric equivalent required a source-capacity theorem. Without it, the proposed operator inequality, and hence the decimal lower bound, had not been established.

The retained decision is BLOCKED. This belongs in the history because it specifies what the next successful construction had to control. It does not justify a staircase that briefly rises to 0.0975576 and then falls back. The project never acquired that result as an accepted bound.

## Prices attached to one physical set

The August 17 route made the source constraint explicit. It used the weighted measure

dν = min(r,1) dr dθ,

whose density relative to planar area is min(1,1/r) away from the origin. Thus ν never exceeds area. Each estimate used a radial price pᵢ(r), and the combined prices had to sum to at most one at every physical point. Overlapping geometric families could now participate in one argument, but they had to share the same capacity rather than submit independent full-price claims. [N10, N11]

A repaired low-height estimate and the high-endpoint collar argument produced the safe lower bound 0.072323077979923422. The proof also recovered a finite-valued Borel midpoint selector inside an arbitrary open enclosure of the original set. This did not assume the original choice of needles was measurable. It constructed a new legal family where integration was available, reran the geometric split there, and finally took the infimum over open enclosures.

The height cutoff itself then became a meaningful variable. Lowering H improves the relevant low-height estimate, but weakens the easy branch, whose triangle only guarantees H/2. Consequently, lowering H indefinitely is not a global improvement. Balancing the branches at a fixed rational choice led to 0.073920942372137638. This step is worth retaining even though it reused the framework: its gain came from understanding a competing constraint, not simply asking an optimizer for more digits. [N12, N13]

The next change shared one terminal radial price across a finite block of high directions. Very distant scales could not be thrown into the same block: its uniform estimate deteriorates as the upper radius grows. The construction therefore kept a finite cutoff and used fresh, disjoint dyadic radial bands for the tail. This led to the shared-terminal bound. [N14]

Its certificate history contains a real repair. The older v1 used an inadequate three-point reduction on the zero-height parameter family. Version v2 split at every event where a sliding endpoint crossed the radial grid and used concavity between events to control the intervening continuum. It also normalized the common price scale to one. The retained reliable floor is 0.082812499999972190. The nearby float 0.0828125 is not a replacement exact theorem. [N15–N17]

## Why one tenth required a new low-direction estimate

The September 5 short proof reorganized the previous large table into seven effective rows and three mixed coefficients. It clarified why 0.082812499999972190 was true; it did not improve that bound. It also exposed the remaining bottleneck. In the shared-terminal model, low directions still relied on an old low-radius estimate. Optimizing the terminal price could not improve a direction class that received nothing from it. [A0, T1, T2, N14]

The final change returned to the two endpoints of one complete unit segment. In the low family, every selected segment has height at most 1/5 and far endpoint radius M<99/100. Let N be the radius of its near endpoint, not its nearest interior point. Split a direction cut V into B, where N≥2/5, and U, its complement.

Every direction contributes its far ideal angular anchor. This anchor records an orientation of the segment direction; it need not equal the endpoint's actual polar angle. A direction in B can contribute the opposite ideal anchor because its near endpoint also reaches far enough. These are two lifts on the physical circle of length 2π, not two different directions on the projective circle of length π. The actual circular arcs cannot simply be added: they may overlap or even be the same base with two labels. The proof first takes their union and controls how far they must be extended to reach the ideal anchors. Write W(V) for the union of the selected star triangles and Sᵣ(V) for its angular section at radius r. For 0<r<2/5 it obtains

|Sᵣ(V)| ≥ k(r)(|V|+|B|),  k(r)=min{2/3, (2/5−r)/(2/5+r)}.

Only eligible directions supply the second anchor; the estimate does not double all directions indiscriminately. [T6]

What pays for U? A complete unit segment satisfies M+N≥1. If N<2/5, its far endpoint must extend beyond 3/5. Those directions therefore support a stronger estimate on a later radial interval. The argument combines this compensation with the extra anchors available to B.

There is still only one set. Where the later payments overlap, complementary weights λ and 1−λ keep the total charge at most one. The weights balance the coefficients for B and U, so the final guarantee does not depend on how directions split between them. The resulting low-family integral coefficient exceeds 1/(10π). The other direction classes are paid on disjoint radial regions, completing the universal bound 1/10. [T6, T7]

A stronger pointwise paired estimate was investigated alongside this argument and refuted by an actual continuum of unit segments. At radius 1/4, a direction cut of length 43/1000 occupies a physical angular union of length 1/50, less than half the cut length. This disproves that proposed pointwise estimate. It does not disprove the compensated integral inequality or the global 1/10 theorem. The successful proof was accepted without importing the failed pointwise claim. The documents establish this dependency distinction; they do not establish that discovering the counterexample caused every subsequent idea. [T9, T8]

## What the history preserves

The ordinary 1/10 proof was accepted on September 5; the final Lean closure and public delivery followed on September 13. Folding these dates together would erase a substantial part of the work. Likewise, an exact scalar certificate, a source declaration, an executed axiom report, and a reviewed mathematical proof answer different questions.

The migration audit located full early Lean source closures and historical build/axiom transcriptions for the baseline and annular routes. It did not locate the original native execution logs for the N32 and N64 endpoints. The final 1/10 project has retained native receipts whose recorded source hashes agree with all 44 current modules. This writing task has not rebuilt those projects. Preserving the source and its version locks makes later checking possible without pretending that missing execution evidence has already been recovered. [LA]

The main mathematical movement is now visible. First the project tightened a covering estimate. Then it learned to add payments made in different physical regions. Finite radial schedules made that allocation more flexible. A failed near-one-tenth candidate showed why unique outputs were not enough; successful radial prices constrained the shared source instead. The final proof used the geometry of the neglected near endpoint to compensate the low-direction bottleneck.

This is more informative than either a list of improving decimals or the final proof alone. It preserves which information was discarded by each method, which later argument recovered it, and which tempting shortcut failed. It also preserves the distinction between discovery, repair, certification and formalization. The endpoint remains a lower bound: the exact infimum and a matching construction are still open. The broader upper-bound work is available in the final research paper; this account follows the lower-bound history selected for preservation.

## Source convention

Bracketed source IDs refer to retained primary project documents through the relocation map. Statements about chronology use dated round records and actual commit metadata, not file modification times. These dates locate documented versions rather than the first private thought or public priority. Here “we” names the project's shared mathematical work; the record is not sufficient to reconstruct individual or model credit from commit authors. Historical labels such as “human proof” are read as ordinary mathematics versus formal checking, not as evidence of human authorship. This account reconstructs the identified main line rather than asserting an exhaustive inventory of every abandoned branch.
