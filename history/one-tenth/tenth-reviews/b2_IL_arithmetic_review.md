# Independent IL arithmetic and source-class audit

**Verdict: ACCEPT — exact constants, scalar source-class cancellation, and complementary physical-bank price algebra.** This is **not acceptance of the continuum IL geometry or any global theorem**. Authority: `ed84c269e743177aaf1d3776df6ec5eefa05a9f6` in `/home/argustest/research/star-kakeya-wt-01-b2-integrated-low`.

Status: completed. No mathematical blocker found in the assigned arithmetic/algebra scope. Final authority renewal confirmed all four blobs unchanged, HEAD unchanged, and an empty `git status --porcelain`. Only this report was written.

## 1. Independently reconstructed constants and certified bound

Set `u=m+r`. Direct polynomial division gives

    r(m-r)/(m+r) = -u+3m-2m^2/u.

Hence a substituted primitive is

    G_m(r) = -(m+r)^2/2 + 3m(m+r) - 2m^2 log(m+r).

Its derivative is the integrand. This differs from the production primitive by a constant in r and was implemented independently using Arb logarithms, not by calling the supplied primitive or importing its checker. Solving `2/3=(m-r)/(m+r)` gives `r=m/5`, thus the first-bank switch is `2/25`. The constant-cap contribution is `(2/3)*(2/25)^2/2`.

Exact Fraction evaluation of the polynomial endpoint differences and log factors yielded:

| Bank | Definition | Exact result |
|---|---|---|
| C4 | `(2/3)*integral_0^(2/25) r dr + integral_(2/25)^(1/5) r(2/5-r)/(2/5+r) dr` | `61/750-(8/25)log(5/4)` |
| C5 | `integral_(1/5)^(7/20) r(1/2-r)/(1/2+r) dr` | `87/800-(1/2)log(17/14)` |
| C6 | `integral_(7/20)^(1/2) r(3/5-r)/(3/5+r) dr` | `93/800-(18/25)log(22/19)` |
| D5 | `integral_(7/20)^(1/2) r(1/2-r)/(1/2+r) dr` | `69/800-(1/2)log(20/17)` |

All four are positive. Both 192-bit and 256-bit Arb evaluations, in normal and optimized execution, independently proved

    0 < C4 < C6,
    0 < lambda=C4/C6 < 1,
    C*=2*C4+C5+(1-C4/C6)*D5 > 637/20000 > 71/2230 > 1/(10*pi).

They also proved the convenient outward **rational** enclosure

    31885183965119/10^15 < C* < 31885183965121/10^15.

The narrower certified 256-bit ball is retained in the real stdout below; its center begins `0.031885183965119974190978711856645823304121960240497380985321030932566551567` with displayed radius at most `7.13e-76`. The convenient enclosure is not presented as the full available precision. Arb also directly verified `pi>223/71`; the final comparison does not rest solely on an unexamined numerical pi approximation. The exact rational full-direction margin identity is `637/20000*(223/71)-1/10=51/1420000`.

## 2. Source-class cancellation and physical capacity

Writing `b=|B(V)|`, `u=|U(V)|`, the bank total is

    [2*C4+C5+(1-lambda)*D5] b
      + [C4+C5+lambda*C6+(1-lambda)*D5] u.

The coefficient difference is `C4-lambda*C6`. Since C6 is positive, the cut-independent choice `lambda=C4/C6` makes it identically zero, not approximately zero. Thus both coefficients equal C*, and `b+u=|V|` gives `C*|V|`. The production endpoint substitutions corroborate the implementation but are not by themselves a universal symbolic proof; the algebra displayed here supplies that proof.

On the only shared radial bank, `W(U(V)) subset W(V)`. The admissible indicator pairs `(1_W(U),1_W(V))` are `(0,0),(0,1),(1,1)`. Their charged densities are respectively `0,1-lambda,1`, bounded by `1_W(V)`. On the other two banks the radial supports are disjoint (boundary circles have zero area). This proves the proposed **scalar physical price domination**, conditional on the stated unions and receipts, and rules out full-price double charging. It is not a transport or all-cut Hall theorem. No sum of individual triangle areas is used.

If b or u is zero the same identity still holds. If both vanish, it yields the non-strict zero-mass conclusion only; `C*>637/20000` does not imply a strict area inequality after multiplication by zero. The submitted theorem correctly limits its strict conclusions to positive-mass cuts.

## 3. Positive-log certificate and every interval operation

For every actual positive rational argument x>1, put `t=(x-1)/(x+1)`, so `0<t<1`. Integrating the convergent geometric series gives

    log(x) = 2 sum_(j>=0) t^(2j+1)/(2j+1).

After terms j=0,...,39, the remainder satisfies

    0 < R = 2 sum_(j>=40) t^(2j+1)/(2j+1)
          <= (2/81) sum_(j>=40) t^(2j+1)
          = 2*t^81/[81*(1-t^2)].

Thus the script's exponent, denominator and positive-tail direction are all correct. For x=1, t=0 and the exact interval is `(0,0)`, tested in both execution modes. The reciprocal branch is mathematically sound for rational `0<x<1` by `log(x)=-log(1/x)` and endpoint reversal; it is unused in these bank evaluations. This helper is not safe as a general API for nonpositive x, but no such input is claimed or executed here.

The actual endpoint-log inputs are rational, exceed one, and have positive denominators. Every load-bearing operation uses Fraction; floating conversions occur only in `show`, whose rounded decimal endpoints are **not outward certificates**. In particular, equal printed lower/upper decimals do not mean an exact singleton enclosure.

- `primitive`: multiplying the log interval by the negative factor `-2*m*m` reverses its endpoints; implemented correctly.
- `integ`: subtracts the upper lower-endpoint primitive from the lower upper-endpoint primitive, and vice versa; dependency only widens the valid interval.
- `add`: endpointwise addition is valid without sign restrictions.
- `scale`: endpointwise multiplication is valid at the only actual coefficient, positive 2. It is not a general negative-scalar interval routine and is not used as one.
- First-bank cap: inserted as an exact singleton rational interval.
- Price division: the explicit guard gives `0<C4_lo<=C4_hi<C6_lo`; positive interval division yields `[C4_lo/C6_hi,C4_hi/C6_lo]`.
- Complement: `[1-lambda_hi,1-lambda_lo]` is correct and nonnegative.
- Bonus product: both complement and D5 are nonnegative, so multiplying corresponding endpoints is valid. D5 positivity follows analytically from its integrand (strictly positive in the interior); reviewer checks additionally verified `0<D5_lo<=D5_hi` in the production namespace. The production checker does not explicitly guard this sign, but its fixed-domain proof supplies it.
- C*: endpointwise addition encloses the true common coefficient despite repeated occurrences of C4; independence is not required for interval inclusion.
- Final strict comparison: it is the exact rational lower endpoint of C* that exceeds the rational floor and target upper endpoint. All required execution guards are `if`/`raise`, not removable asserts.

The independent Arb integrals prove the target directly. Optional cross-engine series checks report only non-disagreement, not an independent proof of the very narrow rational log intervals; their rigorous certification is the analytic remainder argument above.

## 4. Production replay, optimization, controls, and admission flags

Executed immutable `git show ed84c269e743177aaf1d3776df6ec5eefa05a9f6:research/one-tenth/low-source-b2/integrated-low/check.py` bytes via `exec(compile(source,...,'exec'), namespace)` inside the specified interpreter, separately from the independent reviewer. Subprocess command form was:

    /home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python -B [-O] -c <in-memory runner>

Working directory was `/home/argustest`; subprocess timeout 60 seconds; `OPENBLAS_NUM_THREADS=OMP_NUM_THREADS=MKL_NUM_THREADS=1`, `PYTHONDONTWRITEBYTECODE=1`. No dependencies were installed. Python-flint reported version 0.9.0. No parameter optimization, random input, geometric sampling, solver, grid, quadrature or broad enumeration was used.

Production normal and optimized runs each exited 0. All semantic stdout matched, omitting only elapsed-time telemetry, and agreed with the committed final receipts. Key real output:

    balanced: STRICTLY BELOW TARGET
    unbalanced: STRICTLY ABOVE TARGET
    FIXED CERTIFICATE FAILS; not a geometric IL counterexample; stop this candidate.
    four integral closed forms: EXACT PASS
    EXACT: Cstar > 637/20000 > 71/2230 > 1/(10*pi)
    EXACT rational full-direction margin over 1/10: 51/1420000
    NEW MIXED CERTIFICATE PASSES; continuum proof requires independent review.

The first failure is the deliberately retained retired pure-price control, not a failure of the mixed certificate. Independent Arb also verified its balanced coefficient below and unbalanced coefficient above the actual target. `-O` here means Python assert optimization; it is unrelated to mathematical optimization. The source contains no `assert` nodes, confirmed by AST inspection.

Six unique in-memory mutations per mode were required to fail at the corresponding explicit exception (12 rejections total):

1. Wrong expected switch `3/25` instead of `2/25`: cone/lobe switch guard.
2. Replace C6 by `(0,0)` before the price guard: rejected before division by zero.
3. Replace rational floor by 1: new-certificate inequality guard.
4. Replace cancellation check by `2*c4-(c4/c6)*c6`: class-mass cancellation guard.
5. Wrong expected margin `52/1420000`: rational pi-margin guard.
6. Positive but wrong first polynomial constant `62/750`: closed-form identity guard.

These are arithmetic guard tests, not tests capable of detecting an arbitrary false geometric proof. The source `distinct_controls=2; executions_this_run=1` fields describe the original fixed certificate, not this reviewer activity. This review used 5 arithmetic subprocesses total: two production processes (each one baseline plus six in-memory mutations), one stopped ancillary Arb check, and two successful independent processes. The successful independent processes each evaluated the same four integrals at both precisions; no witness was changed.

ADMISSION-LOCAL.md and CHECK-RESULT.txt consistently distinguish the failed pure-price precursor from the complementary-price repair, declare zero search/optimization, and retain the D5 typo correction to 69/800. The present audit verifies the fixed artifacts and new executions, not the historical wall-clock timing or whether historical admission text truly preceded every original launch.

## 5. Explicit unreviewed geometry / non-promotion boundary

This review did **not** independently certify the prerequisite interval-union lemma; its extension factor on arbitrary circular families; disjointness and measure preservation of Borel ideal-anchor lifts; far-only and near-eligible cone caps; literal lobe support and straddling; signed-height reflection and projective seams; analytic measurability/recovery of arbitrary unions; or the full arbitrary-Borel-cut physical receipt. The proof retains zero-height singleton rays rather than deleting them, but this audit did not independently certify their continuum union treatment. Null-mass scalar algebra was checked; it must not be confused with that zero-height geometric issue.

No high-side bank, high/low decomposition, normalization to the final global area bound, or theorem-level composition was audited. The conclusion is: **the exact constants and the conditional source-once scalar assembly are accepted; the parent must wait for independent geometric and global-composition reviews before declaring a theorem.**

## Prospective bounded verification record

- campaign_id: one-tenth-endpoint-geometry-20260905-b1 / independent IL arithmetic review.
- mode: tiny deterministic audit of a fixed analytic certificate; not search, optimization, numerical quadrature, or geometric sampling.
- target: independently reconstruct the four fixed integrals, the price range and cancellation, and `C*>637/20000>71/2230>1/(10*pi)`.
- role/current state: local arithmetic and physical price algebra only; continuum receipt geometry and global composition remain outside this review.
- necessity/pure-theory alternative: elementary symbolic integration and a positive-series remainder prove the identities; independent Arb evaluation checks the executed rational certificate by a different certified arithmetic engine and substituted primitive. No large computation is needed or admitted.
- algorithm: exact rational polynomial identities plus Arb logarithms at 192 and 256 bits, using `u=m+r` and primitive `-u^2/2+3*m*u-2*m^2*log(u)`. No checker import in the independent arithmetic process. Replay immutable checker source separately in normal and optimized Python; explicit-exception controls only.
- cumulative scale: inherited original lane records 2 fixed controls / 4 launches / 0.007017 in-script seconds, not reset or rerun as a search. This reviewer starts with 0 arithmetic launches; intended 4 processes (production normal/-O, independent normal/-O), only the same fixed constants and bounded guard controls.
- budget: each arithmetic subprocess <=60 seconds; reviewer cumulative subprocess wall <=120 seconds; sequential; single-thread environment; existing `/home/argustest/research/star-kakeya-wt-exact-ray-envelope/.venv/bin/python -B`; no installs or bytecode writes.
- expected time: under 5 seconds total for these tiny computations.
- information gain: ACCEPT/BLOCK the exact constants and source-class algebra, without promoting IL geometry or a global bound.
- success stop: both independent precisions prove the inequalities and both execution modes pass; no tuning.
- failure stop: timeout, budget exhaustion or contradiction stops certification; investigate only within the remaining fixed audit scope.
- checkpoints: after immutable source authentication; after production replay; after independent arithmetic; final source-hash renewal.
- artifacts: this report only; subprocess source passed in memory. Source tree read-only.
- proof exit: explicit antiderivative derivation, remainder proof, rational interval audit, independently certified enclosures, and typed scope verdict.

## Execution checkpoint (before independent replay correction)

Production normal and `-O` replay passed, including six exception-guard mutation controls per mode, in 0.088994 seconds total. The first independent Arb process stopped after 0.053390 seconds at an ancillary demand that the entire 192-bit Arb log ball lie strictly inside a 40-term rational-series interval. For argument 3/2 that interval is narrower than the working Arb resolution; this strict containment test is not a valid prerequisite for the requested certificate. The process had already passed all four primitive evaluations, price checks and target inequalities at 192 bits. No mathematical certificate or precision is being retuned. Corrective replay will retain 192/256 bits and the original target, replace the unnecessary strict cross-engine containment demand with non-disagreement, and prove the positive-series tail analytically. The independent target inequalities must still pass directly by strict Arb comparisons. Reviewer arithmetic wall consumed so far: 0.142384 seconds; 3 launches. Expected final total: 5 launches. This is a reviewer test-design limitation, not a production-checker failure.

## Intake

All four requested live files equal the exact commit blobs; HEAD is the requested commit and the worktree was clean. SHA-256:

| File | SHA-256 |
|---|---|
| PROOF.md | `5aa5785306678977117009c3abece49fda74b348230b592deaacd8bef2f0da84` |
| check.py | `cca8e45b567b51ebd6bd6f3fd68a7cfea997d08d270a2865768f11481eb389db` |
| ADMISSION-LOCAL.md | `0b2c9f5b3b69e7f4764d94390a65732d913d165ba0a33d9e0c620de5b4d89252` |
| CHECK-RESULT.txt | `c30e350324dd44df77143960af5d387db1a45219a5ff056b994b9e16d0c8a1d9` |


## Independent reviewer source (normal and optimized)

```python
from fractions import Fraction as Q
import flint
from flint import arb, ctx

def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def A(x):
    x=Q(x)
    return arb(x.numerator)/arb(x.denominator)
def P(m,u): return -u*u/2+3*m*u
def G(m,r):
    u=A(m+r)
    return -u*u/2+3*A(m)*u-2*A(m)**2*u.log()
rows=[
('C4',Q(2,5),Q(2,25),Q(1,5),Q(2,3)*Q(2,25)**2/2,Q(61,750),Q(8,25),Q(5,4)),
('C5',Q(1,2),Q(1,5),Q(7,20),Q(0),Q(87,800),Q(1,2),Q(17,14)),
('C6',Q(3,5),Q(7,20),Q(1,2),Q(0),Q(93,800),Q(18,25),Q(22,19)),
('D5',Q(1,2),Q(7,20),Q(1,2),Q(0),Q(69,800),Q(1,2),Q(20,17))]
require(Q(2,5)/5==Q(2,25),'switch')
arguments=set()
for name,m,a,b,cap,p,c,x in rows:
    require(cap+P(m,m+b)-P(m,m+a)==p,'polynomial '+name)
    require(2*m*m==c and (m+b)/(m+a)==x,'log factor '+name)
    arguments.update([1+a/m,1+b/m,x])
def series40(x):
    t=(x-1)/(x+1); power=t; s=Q(0)
    for j in range(40):
        s+=2*power/(2*j+1)
        power*=t*t
    return s,s+2*power/(81*(1-t*t))
print('python-flint version',flint.__version__)
for bits in (192,256):
    ctx.prec=bits
    vals={}
    for name,m,a,b,cap,p,c,x in rows:
        v=A(cap)+G(m,b)-G(m,a)
        closed=A(p)-A(c)*A(x).log()
        require(v.overlaps(closed),'closed disagreement '+name)
        require(v>0,'bank positivity '+name)
        vals[name]=v
    c4,c5,c6,d5=(vals[k] for k in ('C4','C5','C6','D5'))
    require(c6>c4>0,'price prerequisites')
    lam=c4/c6
    require(0<lam<1,'price range')
    star=2*c4+c5+(1-lam)*d5
    require(star>A(Q(637,20000))>A(Q(71,2230))>1/(10*arb.pi()),'strict target')
    require(arb.pi()>A(Q(223,71)),'pi lower bound')
    require(star>A(Q('0.031885183965119')) and star<A(Q('0.031885183965121')),'outward rational bounds')
    require(2*c4+c5<1/(10*arb.pi()),'retired balanced')
    require(c4+c5+c6>1/(10*arb.pi()),'retired unbalanced')
    for x in arguments:
        lo,hi=series40(x); v=A(x).log()
        require(not (v<A(lo)) and not (v>A(hi)),'series disagreement '+str(x))
    require(series40(Q(1))==(0,0),'zero series')
    require(Q(637,20000)*Q(223,71)-Q(1,10)==Q(51,1420000),'margin')
    print('PRECISION',bits)
    for k,v in vals.items(): print(k,v)
    print('lambda',lam); print('Cstar',star)
    print('Cstar-floor',star-A(Q(637,20000)))
    print('PASS: independent primitive; positive banks; price; target; zero log; retired control')
    print('PASS: series non-disagreement only; rigorous tail proved analytically')
print('PASS: 31885183965119/10^15 < Cstar < 31885183965121/10^15')
print('PASS: no checker imported; no assertions; no search')
```

## Independent real stdout (identical in both modes)

```text
python-flint version 0.9.0
PRECISION 192
C4 [0.00992739691278621148811890443418629225346098595797102496 +/- 3.48e-57]
C5 [0.01167199277952126713652512351411488106219092567818582764 +/- 3.61e-57]
C6 [0.01069549858184971670149324737447432192492403656104860022 +/- 8.16e-57]
D5 [0.00499053525111254340715552086529287995580069479835827857 +/- 3.02e-57]
lambda [0.928184585020938122469190785940745825032375836699586804 +/- 9.03e-55]
Cstar [0.0318851839651199741909787118566458233041219602404973810 +/- 2.40e-56]
Cstar-floor [3.51839651199741909787118566458233041219602404973810e-5 +/- 2.40e-56]
PASS: independent primitive; positive banks; price; target; zero log; retired control
PASS: series non-disagreement only; rigorous tail proved analytically
PRECISION 256
C4 [0.009927396912786211488118904434186292253460985957971024958521214137367975327 +/- 5.96e-76]
C5 [0.011671992779521267136525123514114881062190925678185827641416210774340454460 +/- 5.06e-76]
C6 [0.010695498581849716701493247374474321924924036561048600223073012805434328451 +/- 7.82e-76]
D5 [0.0049905352511125434071555208652928799558006947983582785716149137106631720770 +/- 9.62e-77]
lambda [0.9281845850209381224691907859407458250323758366995868043016273164019749885 +/- 8.61e-74]
Cstar [0.031885183965119974190978711856645823304121960240497380985321030932566551567 +/- 7.13e-76]
Cstar-floor [3.5183965119974190978711856645823304121960240497380985321030932566551567e-5 +/- 7.13e-76]
PASS: independent primitive; positive banks; price; target; zero log; retired control
PASS: series non-disagreement only; rigorous tail proved analytically
PASS: 31885183965119/10^15 < Cstar < 31885183965121/10^15
PASS: no checker imported; no assertions; no search
```

Corrected independent subprocess wall: 0.114767 seconds. Total arithmetic wall including first failed ancillary test: 0.257151 seconds, 5 subprocesses. A separate attempt to reuse an ephemeral tool script found it already removed; that attempt launched no arithmetic subprocess and changed no artifact.
