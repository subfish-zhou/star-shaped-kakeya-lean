# 012 — fail-closed exact/outward paired-CFS certificate

## Result

The frozen `N=64` CFS schedule is refined into the **65 arbitrary disjoint
Choquet atoms**

```text
N, C, D1, ..., D63.
```

For ownership, `N` owns the half-open paired inner annulus `[H,alpha1)`; on
`J=[alpha1,alpha1+3/500)`, `C` owns the `Rc` replacement and the old `R=1/2`
action is removed.  Every other radial atom is reconstructed from the frozen
`alpha,R,t` arrays.  The checker and an independent radial re-atomizer both
find the active refined atom `D49`.

All shared radial endpoints use the same half-open convention: `[left,right)`,
with the next atom owning `right`.  This gives exactly one owner at switches;
changing closed endpoints to half-open ones does not change any definite
integral.

The exact modified-schedule constant (defined in `THEOREM.md`, not asserted to
be a global optimizer) has the validated enclosure

```text
0.07054487627351847246750992457726307620733
<= C_pair,64 <=
0.07054487627351847251573589552953391541289.
```

The lower endpoint is the **exact rational witness** stored without denominator
prettification in `results/certificate.json` and `results/summary.json`.
`certificate.json` also stores its canonical rational-string SHA-256, which the
validator recomputes before accepting the artifact:

```text
903101dc87aa7bda85c82202e410b85a63a6dcf601f69eb73fbee2f2a946df9d
```

It satisfies, using an independently derived rational upper bound for `pi`,

```text
W - q_old*pi_upper
> 0.00000000819415539625998221856467191145889,
```

so this is a strict certified improvement over the previous strongest exported
`q_old*pi` witness, not merely over the shorter `common*pi` or pretty target.

## Frozen primary data

`primary_data.json` contains only the original 64-class schedule arrays and the
new rational controls:

```text
H = 931611/100000000
q = 51/100
paired reach = 49/100
J = [931611/50000000, 1231611/50000000]
Rc lower = 250043391187/500000000000
log terms = 14, asin terms = 80, paired subdivisions = 128.
```

No cached payment row is accepted as input.  The full `old_q` fraction is a
hard-coded trust anchor in both `checker.py` and `validator.py`; its provenance
is `spikes/007-cfs-rational-cert/README.md:9-10` (and the same value is recorded
in `exact_result.json` as `minimum_low_payment`).  A changed primary-data value
is rejected rather than weakening the comparison.

## Outward arithmetic

* `pi` is enclosed from Machin's identity with alternating rational series.
* each logarithm uses the positive atanh series; the explicit positive tail is
  used in the theorem-safe direction on both sides;
* `asin` uses rational Taylor bounds and the complementary-angle identity with
  rational square-root enclosures near `1`;
* the paired integral uses lower/upper monotone rectangles.  The checker proves
  `R^2-2Rb-b^2>0` on the frozen interval before using monotonicity;
* replacement integrals use directed exact log bounds;
* the high ledger proves one symbolic inequality for every real `A>=eta`, hence
  every band `k>=0`; it is not a finite sample.

## Independent validator

`validator.py` does not import `checker.py`.  It reads both `primary_data.json`
and the production `results/certificate.json`, sorts every class cap and switch,
reconstructs unique radial ownership and all 64 original low rows, then
independently builds `N,C,D1,...,D63`.  It requires the complete 65-atom list,
active lower/upper atoms, all original/refined interval enclosures, the claimed
`W <=` its independent lower bound, and the claimed upper `>=` its independent
upper bound.  It also recomputes the canonical rational-string SHA.  An injected
`cached_rows` field has no effect.

## Adversarial controls

There are **six fault families**, not twelve independent faults:

* three primary-geometry families (`paired_J_overlap`, `q_not_above_half`,
  `J_crosses_alpha2`), each rejected independently by checker and validator;
* three test-only production-tooth faults: the checker actually zeros the paired
  lower term, actually reverses the `asin` enclosure used by the lower
  integrand, or actually begins high-band ownership at `k=1`.  Detection is by
  checker failure or by the healthy validator rejecting the resulting artifact,
  never by inspecting a descriptive fault field.

The harness additionally performs coherent-`W`, SHA, and `old_q` binding/
provenance attacks.  In total it executes **13 rejection assertions** across the
six families and three extra attacks, plus a healthy baseline negative control.

## Run

```bash
./run_all.sh
```

This runs checker, validator, the adversarial harness, eight unit tests, and the
same eight tests under `python -O` so fail-closed behavior does not depend on
Python `assert` statements.
Expected statuses are `PAIRED_CFS_EXACT_CERTIFICATE_OK` and
`INDEPENDENT_VALIDATOR_OK`.

## Evidence boundary

This certifies one frozen modified finite schedule and the paper-level finite
Lovasz--Choquet assembly stated in `THEOREM.md`.  It does **not** prove that this
schedule globally optimizes the enlarged mechanism, identify the finite
supremum with a continuum BVP, or provide a Lean proof.
