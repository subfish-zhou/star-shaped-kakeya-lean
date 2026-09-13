# Li endpoint fatality audit and formal spike

Date: 2026-08-01

## SUPERSEDED (2026-08-02)

This report is historical.  Its negative verdict on the *continuous
arbitrary-needle-selection* route stands, but the repair it proposed (a compact
closed all-support correspondence with extrema) was itself later abandoned: the
Case-I endpoint containment is now proved pointwise, with no graph and no
extremum, by `Figure5LocalContact` and `UniversalEndpointClosure`, and the
universal theorem `StarKakeyaLower.universal_strong_lower_bound` is
unconditional.

Accordingly `LiEndpointFatality.lean` has been deleted.  Its still-used
primitives (`SupportParameter`, `DirectedSupportParameter`,
`planeNormSq_supportPoint`,
`supportTraceFirstArcData?_zeroHeight_projectiveCenter_radius`) were moved into
`StarKakeyaLower/LiGeometry.lean`; the counterexample theorems cited below
(`zeroHeight_centered_trace_eq_two_singletons`,
`zeroHeight_centered_endpoints_not_on_radiusCircle`) were removed with the rest
of the graph scaffold, since the current proof no longer relies on the printed
contact classification they guarded.

Nothing below should be read as a statement about the current status of the
universal theorem.

## Verdict

**The continuous arbitrary-needle-selection route is invalid and must not be
used.  Li's printed `J_Γ` containment does not require that route.**

The source first makes an arbitrary choice of one needle per direction.  Its
later “critical directions” are not obtained by taking extrema of that chosen
family.  They are comparison directions in the larger finite-dimensional
space of **all geometrically feasible unit supports** producing the fixed arc.
Thus the containment argument can be repaired with a compact closed
all-support correspondence.  It cannot be repaired by adding endpoint
continuity fields to `SupportParameterFamily`.

This is not a claim that every geometric sentence in Lemmas 3.1--3.2 has now
been formalized.  The formal spike proves the topology that the valid route
needs and pointwise insertion of the actual chosen first arc.  A subsequent
audit found a missing boundary hypothesis in the printed contact
classification: `δ=0` is allowed by `δ<a`, but produces singleton traces rather
than the asserted nondegenerate isosceles/height/base alternatives.  See
`CASE-I-ENDPOINT-STOP.md` and the two compiled counterexample theorems in
`LiEndpointFatality.lean`.  Accordingly no unconditional fixed-radius
containment or mass theorem is claimed from the printed classification.

## Source and audit basis

The audited file is `sources/li-2026-arxiv-2509.05711v2.pdf`, SHA-256

```text
294b1f852eba222b4331d78fbe2a55617367f40e3b9e9da4737ba284448c87c8
```

The line references below are to a `pdftotext -layout` extraction used for this
audit.  They agree with the page references in the PDF.  Round 1's
same-centre reconstruction and Round 2's scope audit were also checked:

- `SUPERSEDED-ROUND-1-PI56-AUDIT.md`, especially lines 112--191;
- `ROUND-2-LI-THEOREM-AUDIT.md`, especially lines 29--39 and 243--290.

## Literal reconstruction of the `J_Γ` argument

1. **No rotating family is assumed.**  The introduction explicitly contrasts
   the present Kakeya property (“without requiring continuous rotation”) with
   Cunningham's rotating version (source lines 25--35).

2. **An arbitrary choice is made.**  In Theorem 2.1 the paper says that, by the
   Kakeya property, “we can associate each `α` with a needle `l_α ⊂ E`”
   (lines 190--203).  There is no continuity, measurability, uniqueness, or
   closed-graph statement.  Section 3 reuses these chosen triangles and names
   the two components of `Δ_α ∩ S_r` (lines 420--426).

3. **The Vitali selection uses only the already chosen arcs.**  Lines 443--483
   order all chosen trace arcs by length and select an almost-largest disjoint
   sequence.  This step uses suprema of lengths, not extrema in direction and
   not continuity in `α`.

4. **`J_Γ` is initially a set attached to the chosen family.**  At lines
   485--503, `Γ` is a fixed circle arc and
   `J_Γ = {α : Γ_{α,1} ⊂ Γ}`.  The covering identity
   `[0,π)=⋃_α J_{Γ_{α,1}}` follows pointwise because each selected first arc is
   contained in itself.  It does not imply `J_Γ` is closed.

5. **The words “attains its maximum” at lines 521--523 are a one-needle
   finite-dimensional statement.**  They concern the arc size as a support
   line moves with fixed radius/height/direction.  They do not assert that the
   arbitrary map `α ↦ l_α` is continuous.

6. **The critical supports are comparison supports, not selected-family
   extrema.**  For a fixed target arc, Case 1 classifies all lines that produce
   that arc and meet `B_r`; the boundary configurations are isosceles and give
   two directions `α₂<α₁` (lines 545--566).  Case 2 similarly considers all
   exterior supports and its height boundary `δ=a`, producing `β₂,β₁`
   (lines 587--627).  A chosen direction in `J_Γ` is then compared with these
   universal boundary supports.

7. **Boundedness is imposed before the final envelope.**  Lines 638--665
   introduce `R₁`, redefine `J_Γ` with `Δ_α⊂B(0,R₁)`, and show every chosen
   `β∈J_Γ` lies between explicit comparison endpoints.  Lemmas 3.1--3.2 then
   state the interval/length bound (lines 666--706).

8. **The measure step needs set containment only.**  Lines 710--739 take the
   union over chosen `α∈A` and invoke `J_{Γ_{α,1}}⊂g(r)θ_{α,1}`.  No limit in
   direction, selector continuity, or measurability of `J_Γ` is used; outer
   measure handles the arbitrary union.

Consequently, the valid quantifier pattern is

```text
for each chosen needle N at direction α satisfying the hypotheses,
N belongs to the all-support feasible set;
every member of that all-support set lies in the comparison envelope;
therefore the chosen J_Γ lies in the envelope.
```

It is **not**

```text
choose N(α); prove N(α) continuous; prove the chosen J_Γ closed;
take min/max of the chosen J_Γ.
```

## Why the blocked route is genuinely false

### Discontinuous choice counterexample

Take a bounded star-shaped set containing, in every direction, triangles from
two different unit support segments (for example two admissible tangential
centres `c₀≠c₁` with a common small height).  Select the `c₀` needle at rational
chart directions and the `c₁` needle at irrational chart directions.  This is
a legitimate Kakeya choice.  Its support centre, trace endpoints, and in
general first arc are discontinuous everywhere.  A target arc separating the
two trace configurations makes the pullback `J_Γ` a dense nonclosed set (up
to harmless boundary directions), so an endpoint-continuity proof and an
“attained extremum of the chosen `J_Γ`” proof both fail.

### Why putting `E` into the correspondence also fails

The theorem allows arbitrary, nonclosed `E`.  On one support line, let the
available unit bases have tangential intervals
`[c+1/n-1/2,c+1/n+1/2]`, and take the union of their triangles with the origin.
The limit base at centre `c` need not be contained: its left endpoint is
missing.  Add arbitrary star triangles supplying all other directions.  The
result remains star-shaped and Kakeya, but “needle is contained in `E`” is not
a closed condition on support parameters.

Therefore compactness must be proved for a **geometric ambient feasible set**
whose constraints are closed (direction chart, height cap, radius/endpoint
bounds, fixed-arc inequalities).  Membership in `E` is used only to place each
originally chosen needle inside that ambient set.  No closure of `E` is needed.

These counterexamples are fatal to the blocked proof architecture, but not to
Li's universal comparison architecture.  Hence this audit does not report an
A-class flaw in the endpoint containment itself.

## Correct compact correspondence

`StarKakeyaLower/LiEndpointFatality.lean` defines a support parameter
`p=(δ,c)` and directed parameter `(α,p)`.  The graph
`feasibleSupportGraph a b h R` contains **all** parameters satisfying

```text
α ∈ [a,b],  δ ∈ [0,h],  c ∈ [-R-1/2,R+1/2],
δ²+(c-1/2)² ≤ R²,  δ²+(c+1/2)² ≤ R².
```

The last two inequalities are precisely the squared-radius bounds for the two
endpoints of `supportNeedle α δ c`; rotation drops out of the squared norm.
The explicit centre interval is redundant when `R≥0`, but retaining it makes
the compact box syntactically manifest and does not exclude any endpoint-
bounded support.

The file proves:

- `isCompact_feasibleSupportGraph`;
- `isClosed_feasibleSupportGraph` (closed graph);
- `isCompact_feasibleSupportFiber` for every direction;
- compactness of `criticalSupportGraph`, obtained by adding the two closed
  fixed-target inequalities
  `γlo ≤ α+lo(p)` and `α+hi(p) ≤ γhi`;
- compactness and attained least/greatest elements of its projection
  `criticalDirections`.

Here `lo,hi` are continuous **relative endpoint formulae on the support
parameter space**.  They are not fields asserting continuity of endpoints of
an arbitrary direction-wise selection.

## Formal nontrivial critical contact

Two perturbative theorems are compiled:

- `greatestDirection_upperEndpoint_contact`: if `(α,p)` realizes the greatest
  projected feasible direction and `α<b`, then `α+hi(p)=γhi`;
- `leastDirection_lowerEndpoint_contact`: if `(α,p)` realizes the least
  projected feasible direction and `a<α`, then `α+lo(p)=γlo`.

The proof keeps the *same* support parameter `p` and perturbs only `α`.  All
endpoint-radius and height constraints remain unchanged.  If the relevant
target inequality were strict, a small explicit perturbation would produce a
larger/smaller feasible direction, contradicting extremality.  This is a real
critical-contact theorem, rather than contact stored in a structure.

## Chosen family inclusion and endpoint interval

The second spike closes the quantifier gap which motivated this audit.
`chosenJGammaLifts F Γ a b` contains chart lifts of the **actual** chosen
needles in `JΓ`; `chosenSupportParameter F α` is literally that needle's
height/centre pair.  For each lift separately,
`chosenFirstArc_mem_criticalSupportGraph` uses ambient feasibility, the two
actual first-arc endpoint formulae, and a faithful target chart only along that
one selected arc.  Carrier containment then implies both target endpoint
inequalities.  Therefore `chosenJGammaLifts_subset_criticalDirections` inserts
the chosen family pointwise into the universal envelope.  There is no
continuity hypothesis and no assertion that the chosen lift set is closed.

`criticalDirections_twoSided_endpointInterval` packages attained least and
greatest directions, actual support witnesses at both ends, containment in
their `Icc`, and the alternatives

```text
least:     left chart boundary or lower target contact;
greatest:  right chart boundary or upper target contact.
```

The projection/scaffold theorems map this interval to `directionsBetween` and
feed a proved balance identity and analytic ratio inequality into
`LiGeometry`'s same-centre dilation theorem.  Finally,
`jGammaCriticalContainment_of_allFeasibleSupports` and its pointwise-support
convenience form prove fixed-radius `JGammaCriticalContainment`: chosen lifts
enter the universal critical set and an independently established universal
envelope lies in the dilation of one fixed chosen target arc, hence in
`selectedDilatedUnion`.

## Exact completion boundary

The endpoint-fatality question is resolved as follows.

- **Rejected:** continuous arbitrary needle selection; closedness of the
  selected-family `J_Γ`; any `SupportParameterFamily` endpoint-continuity
  field.
- **Proved:** the replacement compact all-support topology, extrema, critical
  target contact, pointwise chosen `JΓ` inclusion, the two-sided critical
  endpoint interval, the endpoint-scaffold/analytic bridge, and fixed-radius
  `JGammaCriticalContainment` once the universal geometric envelope is proved.
- **Blocked at a missing source hypothesis:** specialize `lo,hi` to the actual one/two-component
  support-trace formulae through all tie regimes; refine chart-boundary/target-
  contact into Li's isosceles, height, and base-boundary alternatives; and
  discharge the full printed `g(r)` estimates.  The printed alternatives omit
  `δ=0`/zero-span traces, so these facts cannot be proved at the stated scope.
  They are not smuggled into a chosen-family continuity record or into the
  containment conclusion.

Thus the source containment does not need needle-family continuity.  Its safe
formalization must quantify over all feasible supports and use the chosen
family only through pointwise inclusion in that compact ambient graph.
