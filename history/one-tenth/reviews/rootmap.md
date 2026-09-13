# Whole-carrier 27-root closeout review

## ACCEPT — exact scoped accounting is justified

**Reviewed authority:** commit `cd8779e0bdb82f19bf8ed7c4fd2e162094c070c5`, subtree `research/one-tenth/rootmap`, in `/home/argustest/research/star-kakeya-wt-01-short-rootmap`.

The whole-carrier implication is sound. The parent may replace the **conditional** union count by **exact scoped accounting of these 34 historical production root IDs out of 441**, consisting of the inherited seven and the independently accepted 27-root addition below. The ordered complement has 407 IDs. This is a count of certified named root domains, not a measure of configuration-space coverage and not a disjoint partition of geometric weak carriers.

This report does not itself modify production status. The reviewed `candidate.json` correctly remains non-promoting, with `new_promotions=0`. The old seven are inherited, not independently recertified here. Acceptance uses the restricted separator theorem already independently accepted in the pinned `separator_independent_audit.md`; the separately rewritten theorem at `9b185ea...` is outside this review.

## 1. Authority and executable evidence

- HEAD was the requested exact SHA both at intake and after verification; `git status --short` was empty and `git diff --quiet <SHA> -- research/one-tenth/rootmap` succeeded. No snapshot, old-code execution, geometry search, package regeneration, or promotion was performed.
- Both normal and optimized executions of `check_rootmap.py --provenance` passed. All **13 original source hashes matched**. Candidate SHA-256 was `913b69a446381981c483068f5bf8ab4e89756349e9f1598ab4f053b7c21b97ec`.
- Normal and optimized unittest discovery each ran **12 tests**, all passing. Recorded runtimes were 0.637s and 0.627s.
- Exact checker stdout in both modes:
  `PASS_EXACT_ROOTMAP_CANDIDATE roots=441 candidates=27 old=7 conditional=34 complement=407 new_promotions=0`.
- I additionally reconstructed the census by a different finite method, cross-checked the complete second historical risk catalogue, instantiated all 297 selected support conditions, and exercised independent rational closure/reflection probes. These checks imported neither the candidate checker nor any old producer.

The six reviewed Git blobs are:

| File | Blob |
|---|---|
| README.md | `b41d16da0520cd8ddf97f351f5f58264b6f1aceb` |
| candidate.json | `52860ca24ae4c392a0893f07b8b84a4e0825458d` |
| check_rootmap.py | `4af063f721c10c1a19b3d06f5acd4298fe96b0a8` |
| production_ids.tsv | `c4bc6799e8674147b50e5414556e1ab0ad2572c4` |
| provenance.json | `b788c04a3c7442437ff892c97cd66d535209d990` |
| test_rootmap.py | `8371f006219f54dd5da5e1067bcb58ae45bb9833` |

## 2. Independent census and frozen naming

The original source `c2c5_minimal_bnb_pilot.py:27–55` defines ordered strict difference constraints, normalized pair states below 1, between 1 and 2, and above 2, and the physical support tests. The candidate's integer Floyd–Warshall encoding correctly scales the epsilon=1/6 system to bounds `-1,5,-7,11,-13`. A feasible strict simple cycle has positive integral weight and at most five edges, so this fixed epsilon preserves feasibility; a nonpositive cycle cannot satisfy the strict original system.

For an independent enumeration, I instead enumerated positive integer adjacent increments from 1 through 13 on the scaled grid and discarded pair differences 6 and 12. This enumeration is complete: integral difference constraints admit integral potentials; any adjacent increment exceeding 13 can be clipped to 13 without changing a state, since every pair crossing that increment is state 2 both before and after clipping, while other pair differences are unchanged. Classifying the remaining pair differences produced:

```text
INDEPENDENT_GRID_ENUM 3 273 147 441 reflection_fixed 21
ADJACENT_SHORT_HISTOGRAM {0: 1, 1: 6, 2: 27, 3: 82, 4: 167, 5: 158}
FROZEN_NAMING_EQUALS_SECOND_RISK_CATALOGUE 441
PARTITION 34 407
```

Reflection was independently computed as `Dij -> D(4-j)(4-i)`, with lexicographically minimal representatives. The resulting product signature set equals the entire TSV, not just its cardinality.

`c2c5_25root_bernstein_campaign.py:107–118` genuinely assigns IDs by floating representative ranking. Thus the TSV is properly a **frozen naming authority**, not an exact rerun of that floating sort. Its full 441-entry mapping equals both `c2c5_441_long_gap_census_lane1.json` and the `risk_ranking` ID/signature mapping in `c2c5_441root_risk_pilot_receipt.json`. No representative score or point is used for whole-root certification.

## 3. Complete physical support crosswalk, not representative-only guards

I inspected the original generic recipes at:

- `verify_c2c5_closed_root_compiler.py:104–109,178–215`;
- `c2c5_one_short_sixroot_compiler.py:218–233,242–259,283–308`;
- `verify_c2c5_r000_full7d.py:38–59`;
- `c2c5_one_short_root_closure_coverage.py:126–150,178–222`.

They supply the actual cube, closure cone, path recurrence and **all three** weak-state rules. The argument does not extrapolate state 0/1 from an R000 state-2-only example.

With free coordinates `(qC,q1,q2,q3,q4,qL)`, the eleven physical paths are explicitly:

| Entry | Path | Free indices |
|---|---|---|
| C01 | qC | 0 |
| D01 | q1 | 1 |
| D02 | q1,q2 | 1,2 |
| D03 | q1,q2,q3 | 1,2,3 |
| D04 | q1,q2,q3,q4 | 1,2,3,4 |
| D12 | q2 | 2 |
| D13 | q2,q3 | 2,3 |
| D14 | q2,q3,q4 | 2,3,4 |
| D23 | q3 | 3 |
| D24 | q3,q4 | 3,4 |
| D34 | q4 | 4 |

For **each** row below, its C2 digit and ten C5 digits instantiate, in exactly this order, `0: A_J<=0`, `1: A_J>=0 and B_J<=0`, `2: B_J>=0`, where

`R_J+i I_J = product_J(1+i q)`,
`A_J=2 I_J R_J-2h(R_J^2-I_J^2)`, and `B_J=I_J-2h R_J`.

The candidate's `PATHS`, `support_values`, `weak_state`, and `carrier_point` actually evaluate these eleven predicates; they are not merely prose labels. My independent instantiation covered **27 × 11 = 297 support conditions**, including every nonadjacent path. On a genuine component path of angle d, the recurrence gives `A_J/(R_J^2+I_J^2)=sin(d)-2h cos(d)` and `B_J/R_J=tan(d/2)-2h`, agreeing with the original physical support tests. Two separating gaps leave each component span below pi/2: `tan(Delta)=21/20>1`, so `pi-2Delta<pi/2`. Thus the positive pair-domain convention is appropriate on actual roots, not an invented restriction.

Native direction-word signs and pair-denominator restrictions only shrink the all-support supercarrier. Their omission does not weaken the conclusion because the theorem is proved on that **larger** carrier. No native eight-word surjectivity, winner enumeration, or predecessor ownership-completion claim is needed or accepted.

## 4. Whole cube, physical closure, and theorem inclusion

Define E_sigma using the source cube

`qC,q1,...,q4=(3/7)z`, `qL=3/7+(40/21)zL`, `h=zh/5`,

all eleven weak support predicates, and the actual cone

`I>=0`, `7R-3I>=0`, `7I-3R>=0`,

where R+iI is the product of the six free factors.

**The cone selects the correct physical branch.** The exact norm identity gives `R^2+I^2=product(1+q^2)>0`. The cone forces R and I strictly positive, even on the compact weak boundary: I=0 would force R=0, and R=0 would force I=0. Therefore `qR=R/I` exists with `3/7<=qR<=7/3`.

This is more than a zero-real-product test. Let `T=sum atan(q)` over the six free gaps. The box gives `0<T<4pi/3<2pi`, using `3(3/7)^2=27/49<1`. Positive R,I therefore put T in the first quadrant, not a later winding. Consequently `atan(qR)=pi/2-T`; the seven directed gaps `2 atan(q)` sum to pi. The full product has imaginary part `(R^2+I^2)/I>0`. Large separator gaps are not incorrectly folded to shorter pairwise distances.

**Adjacent states imply exactly the needed designations.** On a singleton path,

`B=q-2h`, and **`A/2-B=h(1+q^2)>=0`**.

State 0 forces B<=0; state 1 already requires B<=0; state 2 requires B>=0. Every selected signature has exactly two non-state-2 adjacent internal entries and exactly three state-2 adjacent internal entries. Hence it supplies two designated shorts in `[0,2h]`, three internal longs in `[2h,3/7]`, and the two separator longs in `[3/7,7/3]`. The exact separator comparison is `3/7-2/5=1/35>0`.

This proves **E_sigma is contained in the previously accepted separator theorem's domain**, throughout the carrier, not at sampled points. Nonadjacent support guards can remove points but cannot invalidate this implication. The accepted audit explicitly permits internal threshold faces that change exact component sizes, provided the two separator inequalities and the short/long designations remain.

The reverse interface needed for production is only inclusion: an actual strict root maps into the cube with inverse `z_internal=7q/3`, `zL=21(qL-3/7)/40`, `zh=5h`; its limits satisfy the weak polynomial guards by continuity. The denominator remains positive. Thus **actual root closure ⊆ E_sigma ⊆ theorem domain**. No root/carrier equality or individual-root nonemptiness claim is needed.

For positive height the accepted theorem therefore supplies

`(1665/424)S-H >= Phi > (1012129/15582000)h + delta1 + delta2 > 0`.

At h=0 both finite physical unions have zero planar area; no division by h or strict positive margin is used.

## 5. Reflection, collisions and simultaneous weak walls

Reflection transports the full signature and sends

`(qC,q1,q2,q3,q4,qL,qR) -> (qC,q4,q3,q2,q1,qR,qL)`.

Reversing each path preserves its complex product, while reflection is an area-preserving isometry of the literal unions. Label permutations only permute those union terms. The exchanged separator is in the same box; re-elimination recovers the other separator. This covers reflected and labelled lifts, not merely an involution on digit strings.

At A=0 retain incident states 0/1; at B=0 retain incident states 1/2. The original short or long designation remains valid at q=2h. No boundary is reassigned to create another certified root. Collisions q=0, simultaneous walls, internal q=3/7 walls, separator endpoints, and h=0 are covered. Multiple E_sigma can overlap; no sum of geometric receipts across roots is taken.

Independent exact probes, without either checker implementation, returned:

```text
POSITIVE_HEIGHT_FULL_11_GUARD_CARRIERS ['R007']
ASYMMETRIC_REFLECTION_ALL_PATHS_AND_SECOND_CLOSURE 1 qR=704127/1304471
FREE_PRODUCT_R_I 704127/1250000 1304471/1250000
ZERO_HEIGHT_ALL_27_AT_BOTH_SEPARATOR_SEAMS 54
```

The positive-height fixture was `h=1/10`, free gaps `(1/100,1/100,1/5,1/5,1/5,1/2)`. It exercises three simultaneous internal long equalities, all eleven guards, a nontrivial reflected signature, and both elimination directions. These are regression witnesses; the preceding algebra establishes the whole-domain implication.

## 6. Exact ID accounting

| New ID | C2 | C5 | Designated short paths |
|---|---|---|---|
| R004 | 0 | 2222022222 | C01,D12 |
| R006 | 0 | 2222122222 | C01,D12 |
| R007 | 0 | 0222222222 | C01,D01 |
| R010 | 0 | 1222222222 | C01,D01 |
| R011 | 2 | 2222002022 | D12,D23 |
| R012 | 2 | 1222022222 | D01,D12 |
| R013 | 2 | 0222222022 | D01,D23 |
| R014 | 2 | 0222222122 | D01,D23 |
| R015 | 2 | 2222012122 | D12,D23 |
| R017 | 2 | 2222122122 | D12,D23 |
| R018 | 2 | 1222222022 | D01,D23 |
| R019 | 2 | 0222222220 | D01,D34 |
| R022 | 1 | 2222022222 | C01,D12 |
| R023 | 2 | 1222222122 | D01,D23 |
| R024 | 2 | 0022022222 | D01,D12 |
| R025 | 2 | 2222022122 | D12,D23 |
| R026 | 1 | 2222122222 | C01,D12 |
| R028 | 2 | 2222012022 | D12,D23 |
| R029 | 2 | 0222222221 | D01,D34 |
| R032 | 1 | 0222222222 | C01,D01 |
| R034 | 2 | 1122022222 | D01,D12 |
| R036 | 2 | 1222122222 | D01,D12 |
| R038 | 2 | 1222222221 | D01,D34 |
| R041 | 2 | 0122122222 | D01,D12 |
| R042 | 1 | 1222222222 | C01,D01 |
| R048 | 2 | 0222122222 | D01,D12 |
| R050 | 2 | 0122022222 | D01,D12 |

Inherited seven: **R000,R001,R002,R003,R005,R008,R009**.

These sets are disjoint; their union contains exactly 34 IDs. Its ordered complement is:

**R016, R020–R021, R027, R030–R031, R033, R035, R037, R039–R040, R043–R047, R049, R051–R440**.

The full 407-ID complement and 34-ID union in `candidate.json` were compared extensionally, including disjointness and union with the complete R000–R440 universe. The complement means “not certified by this combined whole-root accounting,” not counterexample, empty geometry, or absence of theorem-covered subsets.

## 7. Limitations and issues

- The original `verify_c2c5_r000_full7d.py:52` really swaps the verbal upper/lower labels of the two cone polynomials. Their conjunction is correct. The candidate uses the polynomials correctly; this is not a blocker.
- The inherited cluster mixed-event coordinate error is not imported as theorem authority. The pinned independent audit supplies the accepted physical proof instead.
- The historical **23** four-long-lower scalar faces contribute **zero additional root coverage**. Four lower longs and two shorts leave only one possible separator-sized gap, incompatible with true C2+C5. They were not recounted here.
- No old-seven certificate replay, floating ranking replay, native carrier equality, native ownership census, universal support-root theorem, arbitrary offsets/unequal heights, arbitrary cardinality, continuum 0.1, or 0.25 conclusion is licensed.
- One combined terminal probe was rejected by an overbroad gateway-safety filter before execution. The independent enumeration was rerun successfully in the in-memory Python tool, and the Git checks separately succeeded. No mathematical or verification blocker remains.

**Final allowable statement:** the restricted centered equal-height production ledger may count the inherited seven plus precisely these 27 complete root closures as **34/441**, with **407** named roots remaining outside this certified union. Keep the inherited status of the seven and the restricted physical theorem scope explicit. Do not represent this as full N7 or continuum closure.

Only this report was created. All reviewed repositories and original source artifacts remained read-only; no push or promotion was performed.
