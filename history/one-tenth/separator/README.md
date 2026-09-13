# Separator closeout package

Read **[THEOREM.md](THEOREM.md)** for the self-contained statement and proof.
It proves the restricted seven-chord, centered common-height theorem with
two designated short gaps, five designated long gaps and two actual separator
gaps. It does not promote any production root, change the old baseline,
or prove arbitrary-parameter, arbitrary-cardinality or continuum results.

## Files and trust boundary

| File | Role |
|---|---|
| `THEOREM.md` | Literal theorem, full geometric/scalar proof, boundary guards and errata |
| `verify.py` | Independent bounded exact reconstruction using installed SymPy |
| `test_verify.py` | Seven focused unittest cases, including four negative/boundary controls |
| `run.py` | Stable read-only runner: discovers nonzero tests and emits compact JSON |
| `README.md` | Scope, provenance, replay and execution evidence |

**Handwritten mathematics:** the literal radial roofs and area normalization;
physical core/block partition; short-block winner ordering; direct three-center
insertion cap; outsider exclusion; source branch eligibility and pole guards;
standard sine/cotangent/arctangent monotonicity; the graph-to-separator argument;
and null area at height zero. These are fully argued in the theorem, not
formally proved by Python. The accepted sources below support this proof
chain; acceptance of those sources is not a new independent audit of every
line of this rewritten artifact. Parent review remains appropriate.

**Executable algebra:** angle-addition pairs are built from
`(1+i*t)^2/(1+t^2)`, not from old event code. Cotangent primitives independently
produce F, A and E; the three-piece short integral produces B and delta.
The outsider identity is checked by coefficients. The reserve comes from
these primitives; its cleared numerator, constant term and cubic Bernstein
coefficients are reconstructed exactly, then compared with the printed table.
A nonnegative remainder identity links the separator minorant back to that
reserve. Exact multiplication gives the height product; differentiation and
substitution give the separator margin. Three fixed cyclic short-edge patterns
reconstruct blocks and half-incidences, checking one base charge per long and
the final symbolic ledger. No stored PASS receipt is an input.

**What regressions mean:**

- A positive but wrong Bernstein coefficient is rejected by equality with
  the coefficient derived from the reserve, not merely by a sign test.
- Supplying only one separator is rejected by the scalar budget interface.
  This interface assumes the geometric premises; it is not an actual-gap
  membership solver and it does not prove a separator-free counterexample.
- Height zero takes an explicit null-area, non-strict branch without any
  reciprocal/cotangent evaluation. The underlying nullity is handwritten.
- At `q=1/10`, feeding `tan(theta)` into the half-angle direction reconstruction
  produces `9401/10201`, not `99/101`, and the wrong value is rejected.

These checks **do not detect arbitrary changes to geometric theorem prose**.
The symbolic tables do not certify winner order, the insertion inequality,
closure branches, or omitted hypotheses in a different theorem. This is not
Lean, a geometry engine, an old-evaluator certification, or a root map.

## Bounded replay

This is the fixed exact replay admitted by the parent `../ADMISSION.md`:
six named algebra groups, three degree-three Bernstein intervals, three
seven-cycle incidence patterns, and one rational coordinate-error diagnostic.
No search, numerical optimization, subdivision, old producer, root traversal,
new dependency installation, or build is involved. Each process below was
bounded by a 60-second timeout. Only the standard library and installed SymPy
are runtime dependencies. All historical sources are provenance only and need
not exist at replay time. The runner neither reads nor writes them, and does
not generate or update a receipt file.

From any working directory, with `PACKAGE` set to this directory:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B "$PACKAGE/run.py"
PYTHONDONTWRITEBYTECODE=1 python3 -O -B "$PACKAGE/run.py"
```

In this worktree, `PACKAGE` is
`/home/argustest/research/star-kakeya-wt-01-short-separator/research/one-tenth/separator`.
`run.py` also disables bytecode writes itself. All checks use explicit
exceptions or unittest methods, never optimization-removable `assert`.

### Actual execution evidence

- Interpreter: `/home/argustest/.hermes/hermes-agent/venv/bin/python`
  (the `python3` command is the same environment), Python 3.11.15,
  installed SymPy 1.14.0.
- Dependency preflight found **no SymPy** in the parent-approved Arb
  environment. No Arb operation is needed here, so the existing SymPy
  environment was used instead; no environment was modified or installed.
  Direct invocation of the Arb interpreter through the terminal tool also
  encountered a tool lifecycle/home-directory error; a bounded subprocess
  preflight established the actual missing dependency.
- Normal runner from the package directory: exit 0; seven discovered tests,
  seven passes; `PASS_EXACT_SEPARATOR_ALGEBRA`.
- Optimized runner from `/home/argustest`: exit 0; the same seven passes and
  byte-identical JSON stdout. Timings printed by unittest are not part of
  the stable JSON.
- JSON stdout SHA-256:
  `ff034e6bf94e9e6e17958dc3837c278f0c65c6e2fe7f43e1cdad14fa64cb81cb`.
- Reconstructed results: 12 positive Bernstein coefficients;
  incidence topologies C/D1/D2; separator derivative `-228688/90895`;
  separator excess `1012129/31164000`; final margin coefficient
  `1012129/15582000`; coordinate-recipe difference `-598/10201`.
- TDD evidence: each of the seven test slices was first run failing for its
  missing behavior, then passed after implementation. The zero-height test
  first failed against the positive-height-only guard; the coefficient and
  recipe tests execute explicit wrong-input controls in the passing suite.

## Accepted-source provenance (read only)

Source section references are to these inspected files, not to unexecuted
historical receipts. Full SHA-256 pins were computed from the source bytes:

| Source | Accepted content used | SHA-256 |
|---|---|---|
| `/home/argustest/kakeya_astra_audit_20260905/n7.md` | §§1–4: literal setting, scalar definitions and separator proof | `a8851c54cad3ddeebfcc2ff89d84a5bf750732086a6f3c80721d030acb656e93` |
| `/home/argustest/kakeya_astra_audit_20260905/separator_independent_audit.md` | §§1–6: independent literal geometry, source accounting, weak walls, exact algebra and errata | `98bf528334a8c9327cc46f6aa311d61c007b341059d769bd389b854d841ae0c6` |

Starting worktree revision: `0af6ce6b8e0c4b6cb853337134329fa38997fcdc`.
All changes are confined to this `separator/` directory. No sibling lane,
admission file, original source, root map, production count or historical
artifact was edited. Local commit only; no push is authorized.
