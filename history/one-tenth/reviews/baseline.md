# ACCEPT — exact-commit seven-row baseline review

**Authority:** `69ceb8881cf3bf621afb5e1d58ec3d1214369abd`, repository `/home/argustest/research/star-kakeya-wt-01-short-baseline`, subtree `research/one-tenth/baseline`.

**Verdict:** ACCEPT for the rewritten human proof and its fixed-witness arithmetic verifier. The exact rational floor **0.082812499999972190** is retained. I found no blocking mathematical defect, dropped load-bearing assumption, wrong sign/factor, or application outside the exercised primitive/support domain. This is paper-level geometry plus outward arithmetic, **not Lean certification**, not a proof of 0.1, and not a sharpness claim.

All candidate source was read directly with `git show` at the named commit, not from mutable working-tree files. I inspected all seven package files. Only this report was written; no builds, installations, source edits, pushes, new research, or work in the 0.25 lane occurred. The package test runner is reserved to the parent reviewer; my executed checks are specified below and are not represented as a full package replay.

## Mathematical findings

Line references are to the named commit's `PROOF.md` unless another file is named.

1. **Arbitrary sets and Borel recovery: valid (25–72).** Compact individual anchored triangles have open-envelope clearance. Keeping midpoints fixed gives an open direction cover, from which a finite subcover and first-index rule produce a Borel midpoint selector. A Borel orientation chart suffices at the projective seam; no continuous global orientation is needed. Triangle unions over Borel cuts and their fixed-radius angular sections are analytic and Lebesgue measurable. The height dichotomy is correctly rerun *after* recovery. Nothing assumes measurability or boundedness of the original set. Infimizing over open supersets at 396–398 is legitimate.

2. **Interval lemma: valid for arbitrary families, overlaps, repeats and poles (76–90).** Each connected base lies in one open component; one-sided extensions are contained in that component enlarged on both sides by `(Lambda-1)` times its length. Countably many components give the stated factor `2 Lambda-1`. Singletons have no positive extension and are retained rather than discarded. Circular wrapping only reduces the enlargement's length.

3. **Low branch: geometry and splice agree with the implementation (92–159, 274–305; verifier.py:88–111).** Low chords straddle the perpendicular foot, with both tangential endpoint magnitudes at least `m=1/100`. The two-lift small-radius factor is correctly 2; the far-lift larger-radius factor is correctly 1. The lower bound on the full endpoint angle follows from the stated monotonicity of the cosine-law expression on endpoint radii below 1. The mixed height cases are combined within one interval-lemma application, not by adding overlapping union bounds. Zero-height rays and tangency arcs are explicitly retained. The splice equations give `a=m*beta/(alpha+beta)` and `c=(1-k)/(2(1+k))`, and the checker invokes the last primitive branch only at 17/40, 9/20 and 19/40, with zero separately handled. Thus its restricted primitive API is sufficient for every actual call; it is not being treated as a general evaluator at unchecked radii.

4. **Direct collar proof: valid (161–206).** All collar points have radius at least `m'-t>0`; convexity of the norm on the chord supplies the upper bound `R'`. The transverse-projection inequality has the correct `2R' sin(ell/2)` factor. In the small-component case its arcsine argument is below 1 because `ell<t/R'`; the large-component case uses projective total length pi. This proves the stated union estimate even for radial collars. With `t=min(1/2,m'-r)`, direct radial inclusion supplies exactly the terminal kernel, without any first-birth or attainment assumption.

5. **Positive-height and pole support: uniformly legal (208–244; verifier.py:80–87).** Choosing the far orientation makes its tangential coordinate at least 1/2. The formula `N^2=M^2+1-2 sqrt(M^2-h^2)` and the sign `1-1/sqrt(M^2-h^2)` of its M derivative are correct. Monotonicity in absolute height and the decrease-then-increase shape in M justify checking the two M endpoints. The exact positive support residuals `M^2-H^2-D^2` are respectively `1974350759/6400000000` and `89759/10240000`, both positive, and D is positive. Hence every positive-price radius lies strictly above N and below M. For poles, `N=|M-1|<=3/5` throughout the finite block, while the pole support starts at 31/40. The one-sided coefficient is `(M0-r)/(M0+r)`, with no reversed monotonicity or missing multiplicity factor.

6. **Fixed prices, source-once and infinite tail: valid (246–272, 348–398).** The three mixed rows have exact load `999998999999/999999000000`; all other rows have load 1. Terminal payment is issued once to the whole finite-high cut F, then algebraically combines with P or Z because `|F|=|P|+|Z|`. Spatial overlap between different subunions is paid by their fixed nonnegative prices against one common measure, not by adding gross unweighted areas. Later half-open radial bands are disjoint from the seven finite rows and one another. Monotone convergence handles their countable sum. The first tail gives `J=53/200` and area coefficient `53/640`; for every later scale the coefficient is `1/8-1/(16m_n)` after multiplying by pi, increasing for positive m_n and at least `27/256`. This is a proved infinite tail, not finite sampling.

## Actual bounded exact/Arb execution

Interpreter: `/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python`, with `-B`, 192-bit Arb, and a 60-second subprocess timeout. Source and JSON were obtained from immutable Git blobs and executed/read in memory. The verifier's `load()` was not used, so there was no mutable candidate witness read or bytecode output.

The source hash of the executed 131-line verifier was:

`cd8b281fef96b46ea8cb17c9bc913774b128bd1c562d4355a101ec0790c6cdba`

Its `receipts` followed by `certify` returned **True**, with all five branches strictly above the exact target. I separately reconstructed the three nontrivial scalar payments using the substituted primitive

`K_b(r)=-(r+b)^2/2+3b(r+b)-2b^2 log(r+b)`

instead of importing the verifier's `Q`, independently solved the low splice equations, and exposed the terminal-price breakpoint at `M0-1/2` in exact Fraction integration. Normal and `-O` runs both returned exit 0 and identical numerical output; the independent enclosures overlap the verifier's and prove the same strict target comparisons:

| Area coefficient | Independently reconstructed Arb enclosure |
|---|---|
| low | `0.0828124999999989019986541108470988439751316754864453582 +/- 3.17e-56` |
| positive + terminal | `0.0828124999999916966426045939450612653914920630003145462 +/- 7.37e-56` |
| pole + terminal | `0.0828124999999721904111374192974978881751268728506793320398 +/- 9.29e-59` |
| first tail | `0.0828125 +/- 3.19e-59` |
| later-tail minimum | exact `0.10546875` |

The independently computed splice values were approximately `a=0.005895362999788752149`, `m=0.01`, `c=0.139933847790607168195`, consistent with every asserted ordering and every actual primitive call. All three printed conservative decimal lower bounds in the proof lie below these certified enclosures.

## Original-witness equivalence and dependencies

I independently read the original witness at authority commit `80a350d22571e677193f1ce2b2a30384e954b5b5`, parsed all endpoints and five price columns as exact Fractions, and coalesced adjacent rows only when every price agreed. Both normal and optimized probes returned:

`PASS exact original 132 cells = seven rows + zero suffix; parameters and target preserved`

The suffix is exactly `[8/5,16/5)` with zero values in the five finite columns; it does not erase the separately proved later-tail rule. H, M0, R and the exact target also matched. The original witness SHA-256 reproduced the provenance claim:

`147bace20b933ac50febeb150ffff5a154a682d0c45cf3a9fb4c101ecd51b33a`

Source inspection confirms that `verifier.py` imports only Fraction, Path, json and flint. It imports no old producer, old verifier, optimizer or receipt namespace. The human proof reconstructs the geometric bridges rather than treating old PASS tokens as authority. README, proof and provenance correctly separate the paper/Arb result from Lean.

## Limitations and execution issue

* The parent's full package test/mutation replay remains separate; I did not run `run.py` or claim its seven-test PASS as my execution evidence. I did inspect its source and tests.
* The mathematical bridges above were independently reviewed as human proofs, not formalized or kernel-checked.
* The first terminal invocation of the named interpreter failed before execution with a tool lifecycle-scanner exception, `Could not determine home directory`. Calling the **same approved interpreter** through `execute_code`/`subprocess.run` succeeded immediately. No substitute interpreter, synthetic output or dependency installation was used.

**Closeout recommendation:** accept this exact baseline proof/verifier content, subject to the parent's separate package replay. No mathematical repair or additional numerical campaign is required for this baseline closeout.
