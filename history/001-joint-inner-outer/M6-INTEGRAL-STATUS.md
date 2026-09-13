# M6 — analytic radial integral certificate (branch `research/m6-integral`)

Branch-local status note.  **Baseline `12c3f0f`** (`feat(lower): certify annular
numeric kernel`), the independently reviewed numeric-kernel commit of branch
`research/m6-kernel`, which is itself a direct child of `af20002`.  The integral
work was reconciled onto it by fast-forwarding this worktree's branch pointer to
`12c3f0f` and re-applying the integral files on top; **no commit was created and
nothing was pushed**, and the reconciled state is left uncommitted for
independent review.

`spikes/001-joint-inner-outer/LEAN-STATUS.md`, `LEAN-PLAN.md` and the reviewed
`M6-KERNEL-STATUS.md` were **not** edited, and no other worktree was touched.

**The authoritative kernel is merged.**  The temporary minimal `AnnularKernel`
that this branch carried while the kernel branch was under review has been
removed completely; `AnnularKernel.lean` and `AnnularAnalytic.lean` are now the
byte-identical files of `12c3f0f` (verified by `diff` against
`git show 12c3f0f:…`).  There is exactly **one** definition of each of
`annTarget`, `annA`, `annRLambda`, `annR₀`, `annEps`, `annM`, `annLambda`, and
it lives in the reviewed `AnnularKernel.lean`.  Nothing in this branch redefines
or shadows a kernel constant.

## 1. What is closed

The **analytic** half of M6 — item 5 (`g`, `hg`, `hmeas`) and item 6 (`hI` in
`∫⁻` form) of the M5 input contract — is closed unconditionally.  The geometric
half (item 4: `htrace` and `hcritical` at the new tuple, i.e. the deep
parameterisation of `Figure5LocalContact` / `UniversalEndpointClosure`) is
untouched and remains open; no endpoint work and no M7 assembly is in this
branch.

The wrapper-facing theorem is

```lean
theorem annILower_le_lintegral :
    ENNReal.ofReal annILower ≤
      ∫⁻ r in Set.Icc annA annR₀, ENNReal.ofReal (r / annPaperG r)
```

together with

```lean
theorem one_le_annPaperG_on_Icc : ∀ r ∈ Icc annA annR₀, 1 ≤ annPaperG r
theorem ann_aemeasurable_ofReal_radial :
    AEMeasurable (fun r => ENNReal.ofReal (r / annPaperG r))
      (volume.restrict (Icc annA annR₀))
theorem annTarget_lt_annILower : annTarget < annILower
```

These three plug into the closed M5 interface exactly as written.  This was
checked by elaborating a temporary file (`lake env lean`, then deleted, the
library was left unchanged) containing

```lean
theorem m6_feeds_m5_contract … :
    ENNReal.ofReal annILower * L_in ≤
      volume.toOuterMeasure (E ∩ Metric.closedBall K.center annR₀) :=
  universal_positive_confined_lower_bound_of_trace_containment K
    (by norm_num [annA]) (by norm_num [annR₀]) htrace
    one_le_annPaperG_on_Icc hmass hcritical
    ann_aemeasurable_ofReal_radial annILower_le_lintegral
```

which compiles with `htrace`/`hcritical`/`hmass` as hypotheses — i.e. the three
M6 analytic outputs are the *only* things the confined branch still needed from
the analytic side.

## 2. Files

| File | Lines | Status |
|---|---:|---|
| `StarKakeyaLower/AnnularKernel.lean` | 442 | **from `12c3f0f`, byte-identical** |
| `StarKakeyaLower/AnnularAnalytic.lean` | 213 | **from `12c3f0f`, byte-identical** |
| `StarKakeyaLower/AnnularCaseIIntegral.lean` | 849 | new — the certificate |
| `StarKakeyaLower/AnnularIntegralControls.lean` | 120 | new — audit-only controls |
| `StarKakeyaLower.lean` | +20/−3 vs `12c3f0f` | modified — one import + doc |
| `StarKakeyaLower/Audit.lean` | +53/−2 vs `12c3f0f` | modified — import + 32 receipts |

`StrongerKernel`, `AnalyticBranches`, `AnalyticKernel`, `CaseIStrongIntegral`,
`AnnularCaseI`, `CaseIRadialCore`, `AnnularKernel` and `AnnularAnalytic` were
**not** modified by this branch.

### How the two branches meet

* `AnnularCaseIIntegral` imports `AnnularKernel` and reads exactly four things
  from it — `annA`, `annR₀`, `annRLambda`, `annTarget`.  It uses no radical, no
  rational enclosure and no `AnnularParameterDomain` field, and it introduces no
  parameter of its own beyond the two rational branch cuts `annQL`, `annQR` and
  the stored segment bounds.  The reconciliation therefore required **no change
  to any proof**: only the module docstring and the root/audit wiring moved.
* The reviewed kernel already proves the order facts the wrapper needs
  (`annA_pos`, `annR₀_pos`), so the contract check below now consumes the
  kernel's own lemmas rather than local restatements.  The order lemmas the
  temporary kernel carried (`annA_le_annR₀` and friends) are gone with it and
  were used by nothing.
* Gate coverage is now complete on the analytic side: `AnnularAnalytic` supplies
  `PROOF.md` gates **C1**, **C3**, **C4** and `ann_gate_min_exterior`;
  `AnnularCaseIIntegral` supplies gate **C2** as
  `annTarget_lt_annILower : annTarget < annILower` together with the integral
  that justifies it.
* Receipt policy: the reviewed kernel branch deliberately left `Audit.lean`
  untouched and produced its 94 receipts from a temporary file outside the
  library (`M6-KERNEL-STATUS.md` §7).  That decision is preserved here — this
  branch adds receipts only for its own 32 integral declarations and restates
  or weakens none of the kernel's.

## 3. The definitions, as specified

```lean
annInteriorRatio r   = (1 + 2*r) / (1 - 2*r)
annFrozenRatio       = (1 + 2*annRLambda) / (1 - 2*annRLambda)   -- = 35227/14773
annLargeAngleRatio r = π / (π/2 - arctan (2*r))
annPaperG r          = max (annInteriorRatio r)
                         (max annFrozenRatio (annLargeAngleRatio r))
annILower            = 2097 / 100000
annQL                = 23529 / 100000
annQR                = 2353 / 10000
```

`annFrozenRatio_eq : annFrozenRatio = 35227/14773` is proved, not asserted.

## 4. Two active segments, and what is *not* claimed

* **The frozen branch is hidden.**  `ann_frozen_le_large : annA ≤ r →
  annFrozenRatio ≤ annLargeAngleRatio r`, proved by the strict comparison at
  `r = annA` (`2.384552… < 2.392472…`) plus monotonicity of `arctan`.  The
  audit-only strict form is `ann_frozen_lt_large_at_annA`.  No lemma of this
  branch assumes the frozen entry is active anywhere; the three-piece cut of
  `CaseIStrongIntegral` (`strongSwitchLeft`, `strongSwitchRight`) is **not**
  ported.
* **No re-crossing.**  The comparison function
  `annH x = π (6x-1)/(2 (1+2x)) - arctan (2x)` satisfies `annH r ≤ 0 ↔
  interior ≤ large` and `0 ≤ annH r ↔ large ≤ interior`
  (`ann_interior_le_large_of_H`, `ann_large_le_interior_of_H`), and
  `ann_H_monotoneOn : MonotoneOn annH (Ici 0)` is proved from
  `annH' x = 4π/(1+2x)^2 - 2/(1+4x^2) ≥ 0`.  With `ann_H_annQL_nonpos` and
  `ann_H_annQR_nonneg` this pins `annPaperG = large` on `[annA, annQL]`
  (`ann_paperG_eq_large`) and `annPaperG = interior` on `[annQR, annR₀]`
  (`ann_paperG_eq_interior`), and forbids a second crossing.
* **The gap is retained, not covered.**  `annILower_le_intervalIntegral` splits
  `[annA, annR₀]` into the *three* adjacent intervals `annA..annQL`,
  `annQL..annQR`, `annQR..annR₀` and discards the middle one by
  `intervalIntegral.integral_nonneg`.  There is no claim anywhere that the two
  active intervals cover `[annA, annR₀]`.  The cuts straddle the switch
  `0.2352988169…`; the audit control `ann_cuts_straddle_switch` records that the
  branch order really is opposite at the two cuts.

## 5. Primitives and FTC

| Segment | Integrand | Primitive |
|---|---|---|
| `[annA, annQL]` | `annLargeIntegrand r = r (π/2 - arctan 2r)/π` | `annLargePrimitive r = r²/4 - ((4r²+1)/8 · arctan 2r - r/4)/π` |
| `[annQR, annR₀]` | `annRightIntegrand r = r(1-2r)/(1+2r)` | `annRightPrimitive r = -r²/2 + r - log(1+2r)/2` |

`ann_hasDerivAt_largePrimitive` holds for **every** real `r`;
`ann_hasDerivAt_rightPrimitive` needs only `1 + 2r ≠ 0`.  Both segment integrals
are evaluated by `intervalIntegral.integral_eq_sub_of_hasDerivAt`
(`ann_left_interval_integral`, `ann_right_interval_integral`).

## 6. Outward rational enclosures

* `ann_atan_even_partial_lower` — Leibniz lower bound, reproved from
  `Real.hasSum_arctan` (the copy in `AnalyticBranches` sits over the frozen
  kernel and was **not** imported).  `annAtanLower6` is its six-term instance.
* `ann_arctan_quarter_turn` — `arctan x + arctan((1-x)/(1+x)) = π/4`, reproved
  from `Real.arctan_add`.  `ann_arctan_le_of_reflect` turns it into the upper
  bound used at both cuts.
* `π` — `annPiLower = 314159265358979323846/10^20 < π < annPiUpper =
  314159265358979323847/10^20`, from `Real.pi_gt_d20` / `Real.pi_lt_d20`.
* `log` — **strengthened tail.**  `ann_log_geom_upper` bounds the tail term
  `2/(2k+7) · z^{2k+7}` using `1/(2k+7) ≤ 1/7`, giving
  `annLogGeomUpper = 2z + 2z³/3 + 2z⁵/5 + 2z⁷/(7(1-z²))` at
  `z = annLogZ = 1321/8674`.

The crude `π/56` tail `2z⁷/(1-z²)` is **insufficient here** and this is proved,
not merely remarked: `ann_crude_log_tail_negative_control` shows the same two
segments then fall strictly below `annILower`.

## 7. The arithmetic, with margins

Left segment, after the two `arctan` enclosures and `π < annPiUpper`:

```
annILeftLower ≤ (annQL² - annA²)/4 + annLeftC/annPiUpper - annCoeffQL/4
```

with `annLeftC = annCoeffA · annAtanLower6 (2·annA) + (annQL - annA)/4
+ annCoeffQL · annAtanLower6 annYQL`, `annYQL = 26471/73529`.

| Quantity | Value | Stored bound | Slack |
|---|---|---|---|
| left segment | `0.0073263385855…` | `annILeftLower = 732633/10^8` | `8.59e-9` |
| right segment | `0.0136446311771…` | `annIRightLower = 136446/10^7` | `3.12e-8` |
| sum | `0.0209709697626…` | `annILower = 2097/100000` | **`9.30e-7`** |

The true value of the two retained integrals is `0.0209709770…`; the rational
enclosure loses `7.2e-9` and the rounding of the two stored constants a further
`4.0e-8`, leaving the positive kernel-checked margin `9.30e-7` above
`annILower`.  `annTarget = 131/6250 = 0.02096 < annILower` is also recorded.

Every closing step is an exact `norm_num` computation on rational literals; no
decimal literal, no floating point and no kernel-bypassing evaluation tactic is
used anywhere.  The gates are genuinely tight: raising `annILeftLower` from
`732633/10^8` to `7326339/10^9` makes `ann_gate_left` fail.

## 8. Tests / controls

Positive: `ann_certificate_sum_ge_target`.
Negative (audit-only, `AnnularIntegralControls`):

* `ann_crude_log_tail_negative_control` — the un-strengthened tail fails;
* `ann_target_2098_negative_control` — `0.02098` is *not* provable from this
  certificate, so the closing gate cannot silently over-claim;
* `ann_frozen_lt_large_at_annA`, `ann_cuts_straddle_switch` — the frozen branch
  is strictly hidden and the two cuts straddle the single switch.

## 9. Build and scans

All builds below were run *after* the reconciliation, with the oleans of
`AnnularKernel`, `AnnularAnalytic`, `AnnularCaseIIntegral`,
`AnnularIntegralControls`, `Audit` and the root removed first.

* `lake build StarKakeyaLower.AnnularKernel StarKakeyaLower.AnnularAnalytic
  StarKakeyaLower.AnnularCaseIIntegral StarKakeyaLower.AnnularIntegralControls`:
  **green**, `8327` jobs, `20s`, **zero warnings** from any of the four annular
  modules.
* `lake build` (production root): **green**, `8355` jobs.
* `lake build StarKakeyaLower StarKakeyaLowerAudit`: **green**, `8360` jobs.
* `#print axioms`: all `398` receipts of the audit target, including the `32`
  annular integral ones, depend on exactly
  `[propext, Classical.choice, Quot.sound]`.  `universal_strong_lower_bound` is
  unchanged and still shows the same three axioms.
* Wrapper contract re-checked after the merge (temporary file, `lake env lean`,
  then deleted): `m6_feeds_m5_contract_reconciled` elaborates, discharging
  `ha`/`hr₀` with the *kernel's* `annA_pos` and `annR₀_pos`, and closes with
  `[propext, Classical.choice, Quot.sound]`.  The same file re-checks
  `annA = 13177/100000`, `annR₀ = 999/2000`, `annRLambda = 10227/50000`,
  `annTarget = 131/6250` by `rfl` against the reviewed kernel, and re-derives
  `annularParameterDomain`, `ann_gate_C1`, `ann_gate_C4` alongside
  `annTarget_lt_annILower` to confirm the kernel exits are intact.
* Single-definition scan: each of `annTarget`, `annA`, `annRLambda`, `annR₀`,
  `annEps`, `annM`, `annLambda` has **exactly one** `def`, in
  `AnnularKernel.lean`.
* Byte-identity: `AnnularKernel.lean`, `AnnularAnalytic.lean` and
  `M6-KERNEL-STATUS.md` are `diff`-identical to `git show 12c3f0f:…`.
* CLEAN closure: import closure of `AnnularCaseIIntegral` is `{AnnularKernel}`
  + Mathlib.  Scan for `strongA`, `strongR₀`, `strongRLambda`, `strongR₁`,
  `strongRho`, `strongP`, `strongTarget`, `strongPaperG`, `altA`, `altTarget`,
  `altRLambda` across all four annular modules: **none**.
* Forbidden tokens `sorry` / `admit` / `native_decide` / `^axiom ` across
  `StarKakeyaLower/` and `StarKakeyaLower.lean`: **none** in code.  (The strings
  `native_decide` occur only inside the reviewed kernel's own prose docstrings,
  which are byte-identical to `12c3f0f` and were not edited.)
* Duplicate unqualified declaration names: `24`, all pre-existing; **none** of
  the `90` declarations of this branch's two modules collides with anything,
  and none collides with the `94` declarations of the kernel and analytic
  modules.
* `git diff --check`: clean.  Nothing committed, nothing pushed; `HEAD` is
  `12c3f0f` and the five reconciled paths are left in the working tree.

## 10. Open

* Item 4 of the M5 contract (`htrace`, `hcritical` at the annular tuple) — the
  deep parameterisation of `Figure5EndpointEnvelope` → `Figure5LocalContact` →
  `UniversalEndpointClosure`.  Not started here by design.
* M7 assembly: with the kernel merged, the confined branch now has all of
  `annularParameterDomain`, gates C1/C3/C4 (`AnnularAnalytic`), gate C2 and the
  three M5 analytic inputs (`AnnularCaseIIntegral`).  What M7 still needs beyond
  item 4 is the Carathéodory split plumbing and the mass addition, not further
  numeric or analytic certification.
* The target `annILower = 2097/100000` was **not** weakened; `annTarget =
  131/6250` is cleared with room to spare.
