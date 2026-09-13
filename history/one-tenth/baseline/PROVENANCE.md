# Fixed witness provenance (not a runtime dependency)

Authority commit: `80a350d22571e677193f1ce2b2a30384e954b5b5`.
This lane began clean at admission commit
`0af6ce6b8e0c4b6cb853337134329fa38997fcdc` on
`theorem/01-short-baseline-20260905`.

The accepted read-only audit is
`/home/argustest/kakeya_astra_audit_20260905/baseline.md`, especially §§3–5.
Its frozen normalized source tree is
`/home/argustest/research/star-kakeya-wt-v2-normalized`.
The proof here re-exposes that audited mathematical mechanism, replacing the
terminal first-birth presentation with direct radial inclusion. It does not
claim to discover or optimize the fixed prices.

## Exact coalescing check actually performed

Original path (relative to the authority commit):
`archive/shared-terminal-082812/class_independent_terminal_strict_witness.json`.

* Git blob: `8193302a744bf5b7fda57a3a0d390cf251242ecd`.
* Original bytes: 10101.
* Original SHA-256:
  `147bace20b933ac50febeb150ffff5a154a682d0c45cf3a9fb4c101ecd51b33a`.

The comparison used `git show <authority-commit>:<original-path>`, not a live
namespace snapshot or an old receipt. It parsed every radial endpoint and
price with `Fraction`, ordered columns as
`low, terminal_global, class_positive, class_pole, tail_first`, and merged
adjacent rows **only when all five rational prices were equal**. The resulting
list was compared for exact equality with `verifier.rows(verifier.load())`
followed by the all-zero row `[8/5,16/5)`. H, M0, R and the exact target were
also compared independently. Actual output:

```text
PASS: immutable original 132 cells = exact seven active rows + zero suffix [8/5,16/5)
```

In particular the coalesced original mixed prices are exactly

| Price | Original reduced fraction | Tiny-data identity |
|---|---|---|
| low, second row | 316269962741/999999000000 | x |
| terminal, second row | 113954839543/166666500000 | 1−x−ε |
| low, third row | 96233328491/142857000000 | y |
| terminal, third row | 1648311619/5050500000 | 1−y−ε |
| positive, sixth row | 9039395633/111111000000 | z |
| pole, sixth row | 459322219651/499999500000 | 1−z−ε |

The remaining dyadic full-price bands are the explicit mathematical tail
rule, not prices stored in that zero suffix. The suffix is discarded only
from the five finite columns; no tail class is discarded from the theorem.

## Source-byte pins

These hashes were recomputed from `git show` at the same immutable authority
commit. They identify inspected antecedents, not executable dependencies:

| Source | SHA-256 |
|---|---|
| `archive/shared-terminal-082812/class_independent_terminal_strict_arb_v2.py` | `1cd97e9b3afa38c834adafbe93fbdebbf038f7f4b54418690fe572a8ff2a0dc2` |
| `archive/scale-dichotomy/radial-price/low_one_sided_radial_extension_zh.md` | `69128b4661a4bb2325c5771f6102f223cd2aa59d6fdff3a1cc1f3ae1fc0479ed` |
| `archive/scale-dichotomy/final-gate/near_diameter_all_radial_layers_audited.md` | `eb620359a33999462e2818677f2cf3d7d601ba59ab0088d6662b61a415c6c1e7` |

Runtime is deliberately independent: it imports no original producer or
verifier and needs none of the archived grids, certificates or event sweeps.
It reconstructs the seven rows from the original three fractions and epsilon,
computes terminal integrals rationally, checks positive/pole support directly,
and evaluates the displayed logarithm and low splice formulas outwardly.

No earlier Lean endpoint is restated as a certification of this stronger floor.
No Lean build or kernel audit was attempted in this closeout.
