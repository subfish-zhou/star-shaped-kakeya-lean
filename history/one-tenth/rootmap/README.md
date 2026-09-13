# Candidate whole-carrier map: genuine two-short production roots

**CANDIDATE_WHOLE_CARRIER_INCLUSION_AWAITING_PARENT_AUDIT. No promotion.**

Exact reconstruction selects **27**, not 28, roots. Their entire weak carriers
imply the accepted separator theorem's domain. The old seven remain unchanged.
If this interface is independently accepted, the conditional union is **34/441**
and its ordered complement has **407** roots. Current preserved production
status remains **7/441**, with **zero new roots promoted here**.

## 1. Enumeration versus historical names

`check_rootmap.py` independently enumerates the source strict difference
constraints using integer Floyd–Warshall, without importing any old producer.
For normalized ordered positions, adjacent increments are positive, and pair
states 0, 1, 2 mean separation in `(0,1)`, `(1,2)`, `(2,infinity)`.
All bounds are strict integers. A simple cycle has at most five edges, and
positive integral total weight is at least one. Subtracting `1/6` per edge
therefore preserves strict feasibility; a nonpositive cycle is incompatible
with the strict system. Scaling by six gives edge bounds `-1,5,-7,11,-13`.
Negative-cycle detection yields **3 C2**, **273 oriented C5**, **147 reflected
C5**, hence **441 product** signatures.

Pair order: `C01; D01,D02,D03,D04,D12,D13,D14,D23,D24,D34`. Reflection fixes C01
and sends `Dij` to `D(4-j)(4-i)`; use the lexicographically smaller C5 signature.

**Names are a frozen lookup, not an exact recreation of a floating sort.**
`production_ids.tsv` is the complete ID/signature slice of the pinned
`c2c5_441_long_gap_census_lane1.json`, cross-checked against the stored risk
catalogue during extraction. Production assigned Rxxx by floating representative
ratios (`c2c5_25root_bernstein_campaign.py:107–118`). This package does not rerun
that ranking or use representative points as proof. It checks the lookup's byte
hash, all 441 unique ordered IDs, and equality with the independent universe.

## 2. Source-bound whole-carrier implication

### Actual source guards, not representative states

The cycle is
`C0-qC-C1-qL-D0-q1-D1-q2-D2-q3-D3-q4-D4-qR-C0`.
Every q is `tan(g/2)` for the actual **directed adjacent** projective gap,
not the tangent of a folded pairwise distance. The cube map is

`qC,q1,...,q4=(3/7)z; qL=3/7+(40/21)zL; h=zh/5`, with `z in [0,1]^7`.

For any path J, let `R_J+i I_J=product_J(1+i q)` using
`(R,I)->(R-Iq,I+Rq)`. Write R,I for the six free gaps. Retain the source cone

`I>=0`, `7R-3I>=0`, `7I-3R>=0`, and `qR=R/I`.

The exact source definitions are in
`verify_c2c5_closed_root_compiler.py:104–109,178–215`,
`c2c5_one_short_sixroot_compiler.py:218–233,242–259,283–308`, and
`verify_c2c5_r000_full7d.py:38–59`. In particular, the generic compiler explicitly
gives all three state rules, not just the R000 state-2 rule:

`A_J=2 I_J R_J-2h(R_J^2-I_J^2)`, `B_J=I_J-2h R_J`.

| State | Complete weak support condition |
|---|---|
| 0 | `A_J<=0` |
| 1 | `A_J>=0 and B_J<=0` |
| 2 | `B_J>=0` |

For C01, J is `[qC]`; for Dij, J is `[q(i+1),...,qj]`. Apply these rules to
**all eleven entries**, including nonadjacent entries. The local `PATHS`,
`support_values`, and `weak_state` reconstruct this recipe for every signature.

Let E_sigma denote the cube, closure cone, and these eleven weak conditions.
It is an intentionally enlarged closed carrier. Native direction-word guards
`7 I_J-3 R_J<=0` or `>=0` and pair-domain guards `R_J>0`, `R_J^2-I_J^2>0`
(or their weak limiting faces) only **shrink** E_sigma. We do not claim equality
with a union of native carriers, need an eight-word cover, or count newly
compiled native carrier instances. Proving the theorem throughout E_sigma
covers every actual carrier refinement without an omitted-word assumption.

### Closure is the physical branch, including all weak faces

`R^2+I^2=product(1+q^2)>0` and the cone force `I>0`, `R>0`.
Therefore `3/7<=qR<=7/3`, including endpoints: the eliminated denominator does
not vanish on the compact boundary.

Put `T=sum atan(q)` for the six free gaps. Since `3*(3/7)^2<1`,
`atan(3/7)<pi/6`; also `atan(7/3)<pi/2`. Thus
`0<T<5pi/6+pi/2=4pi/3<2pi`. Positive R,I put T in the first quadrant, not a
later winding. Hence `atan(qR)=pi/2-T`, so the seven actual gaps sum to pi.
The full product is `i(R^2+I^2)/I`, on precisely this physical branch.
Both separators are at least `3/7>2/5>=2h`; all seven q are at most `7/3`.

### The universal adjacent A/B implication

On a singleton physical path q, `R_J=1`, `I_J=q`, so

**`B=q-2h`, `A/2-B=h(1+q^2)>=0`.**

State 0 (`A<=0`) forces `B<=0`; state 1 includes `B<=0`; state 2 includes
`B>=0`. Each selected signature therefore has two designated adjacent shorts
in `[0,2h]`, three remaining internal longs in `[2h,3/7]`, and two separator
longs in `[3/7,7/3]`, with actual closure. This proves **every point of E_sigma**
lies in the accepted theorem's domain. Nonadjacent support guards restrict the
carrier but are not needed for this sufficient implication.

We use the accepted theorem in the pinned `n7.md` §§2–4 and
`separator_independent_audit.md` §§1–5, not unfinished sibling outputs:
for centered unit chords of common height `0<h<=1/5`, the above conditions give

`(1665/424)S-H >= Phi > (1012129/15582000)h + delta1 + delta2 > 0`.

The independent audit explicitly proves the extension requiring only two
separator-sized gaps, so internal graph-threshold walls need not retain exact
component sizes. At `h=0`, `S=H=0` directly. This lane proves the interface,
not the physical/scalar theorem again.

### Actual root closures and symmetry

The actual strict geometric roots have cube inverse
`z_internal=7q/3`, `zL=21(qL-3/7)/40`, `zh=5h`. Limits satisfy the corresponding
weak polynomial conditions by continuity. The inverse and closure denominator
remain valid. Thus each actual root closure is contained in E_sigma up to
relabeling/reflection, not merely at a representative point.

At `A=0` both states 0 and 1 may be incident; at `B=0` both states 1 and 2 may
be incident. Keep the root's original designation: a short or long at `2h`
remains a valid weak short or long. No equality face must be reassigned or
counted as a new root. Simultaneous walls, internal collisions `q=0`, separator
endpoints, and `h=0` are included. At zero height use finite unions of segments
having zero planar area, never a strict Phi claim or division by h.

Reflection sends `(qC,q1,q2,q3,q4,qL,qR)` to
`(qC,q4,q3,q2,q1,qR,qL)`, transporting the **whole** signature and exchanging
the separators. Relabeling permutes the literal union terms; reflection is an
area-preserving isometry. All reflected/labeled lifts are therefore covered.
No individual root nonemptiness or carrier/root equality theorem is claimed.

## 3. Explicit IDs and complements

Preserved old roots: **R000,R001,R002,R003,R005,R008,R009**. Their previous
certification is retained, not independently replayed here.

| Candidate ID | C2 | C5 (pair order above) | Designated short paths |
|---|---|---|---|
| R004 | 0 | 2222022222 | C01, D12 |
| R006 | 0 | 2222122222 | C01, D12 |
| R007 | 0 | 0222222222 | C01, D01 |
| R010 | 0 | 1222222222 | C01, D01 |
| R011 | 2 | 2222002022 | D12, D23 |
| R012 | 2 | 1222022222 | D01, D12 |
| R013 | 2 | 0222222022 | D01, D23 |
| R014 | 2 | 0222222122 | D01, D23 |
| R015 | 2 | 2222012122 | D12, D23 |
| R017 | 2 | 2222122122 | D12, D23 |
| R018 | 2 | 1222222022 | D01, D23 |
| R019 | 2 | 0222222220 | D01, D34 |
| R022 | 1 | 2222022222 | C01, D12 |
| R023 | 2 | 1222222122 | D01, D23 |
| R024 | 2 | 0022022222 | D01, D12 |
| R025 | 2 | 2222022122 | D12, D23 |
| R026 | 1 | 2222122222 | C01, D12 |
| R028 | 2 | 2222012022 | D12, D23 |
| R029 | 2 | 0222222221 | D01, D34 |
| R032 | 1 | 0222222222 | C01, D01 |
| R034 | 2 | 1122022222 | D01, D12 |
| R036 | 2 | 1222122222 | D01, D12 |
| R038 | 2 | 1222222221 | D01, D34 |
| R041 | 2 | 0122122222 | D01, D12 |
| R042 | 1 | 1222222222 | C01, D01 |
| R048 | 2 | 0222122222 | D01, D12 |
| R050 | 2 | 0122022222 | D01, D12 |

The ordered complement **after conditional acceptance**, preserving the old
seven, is this inclusive range notation:

**R016, R020–R021, R027, R030–R031, R033, R035, R037, R039–R040, R043–R047, R049, R051–R440**.

`candidate.json` lists all 407 IDs individually in order, the 34 conditional
union IDs, and separately all **434 current unpromoted** IDs. A consumer must
not replace current status by conditional status. Complement membership means
not covered by this whole-root test, not a counterexample or empty geometry.
Some complement roots may contain theorem-covered boundary subsets; no such
subset is promoted to whole-root coverage.

## 4. Four-long-lower faces and inherited issues

On a four-long-lower face, four longs and both shorts are at most
`2h<=2/5<3/7`. Only one remaining gap could separate components, whereas true
C2+C5 requires two cyclic component transitions, each with half-gap at least
`3/7`. These faces are **empty in true C2+C5**. The historically reported **23**
scalar faces give **zero new root coverage**; this lane does not recount them.

A source-label defect was found: `verify_c2c5_r000_full7d.py:52` attaches
`qR<=7/3` and `qR>=3/7` to the opposite cone expressions. The conjunction of
actual polynomials is correct. We use those polynomials, not their labels.
No original was changed. The separately audited cluster mixed-event coordinate
error is not imported into this proof chain either.

## 5. Artifacts, verification, trust boundary, omissions

- `check_rootmap.py`: exact independent enumeration, guard reconstruction,
  frozen naming, partition verification; deterministic read-only replay.
- `test_rootmap.py`: 12 discoverable exact tests, including omitted root,
  altered A/B/closure guard, false promotion, equality incidence, positive-height
  simultaneous long walls, all selected h=0 seam cases, and reflection.
  Point fixtures are regressions only; §2 supplies the whole-domain proof.
- `production_ids.tsv`: 441-row frozen ID lookup only.
- `candidate.json`: exact candidate signatures, guards, IDs, and both complements.
- `provenance.json`: SHA-256 pins for 13 explicitly needed original sources.
  They are **provenance, not default runtime dependencies**. Default replay
  requires only standard-library Python and this folder; `--provenance`
  additionally hashes the original files and verifies the extracted slice.

Exact verification commands (read-only; per-process budget 60 seconds):

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B /home/argustest/research/star-kakeya-wt-01-short-rootmap/research/one-tenth/rootmap/check_rootmap.py --provenance
PYTHONDONTWRITEBYTECODE=1 python3 -O -B /home/argustest/research/star-kakeya-wt-01-short-rootmap/research/one-tenth/rootmap/check_rootmap.py --provenance
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s /home/argustest/research/star-kakeya-wt-01-short-rootmap/research/one-tenth/rootmap -p 'test_*.py' -v
PYTHONDONTWRITEBYTECODE=1 python3 -O -B -m unittest discover -s /home/argustest/research/star-kakeya-wt-01-short-rootmap/research/one-tenth/rootmap -p 'test_*.py' -v
```

Observed verification: all four commands above passed; **12 tests passed in each
mode**. Normal and optimized checker stdout were byte-identical, all 13 original
source hashes matched, and hashing all six local files before/after confirmed
read-only replay. Returned candidate SHA-256:
`913b69a446381981c483068f5bf8ab4e89756349e9f1598ab4f053b7c21b97ec`.

Returned status:
`PASS_EXACT_ROOTMAP_CANDIDATE roots=441 candidates=27 old=7 conditional=34 complement=407 new_promotions=0`.

**Explicit omissions:** no old namespace imports, producer execution, floating
ranking replay, native direction-stratum census, scalar-face recount, old-seven
certificate replay, theorem reproof, or root nonemptiness/equality claim.
No new production certification before independent parent carrier-level audit.
No enlarged scalar theorem without separators, arbitrary offsets/unequal heights,
arbitrary-cardinality bridge, continuum 0.1 result, or 0.25 work. No scout,
solver, interval/Bernstein campaign, or Lean build. Existing universal lower
floor untouched. All old sources are read-only; local commit only, no push.
