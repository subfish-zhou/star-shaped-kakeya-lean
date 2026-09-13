import StarKakeyaLower.UniversalAssembly

/-!
# `StarKakeyaLower` — production root

Importing this module gives the unconditional strong lower bound

`StarKakeyaLower.universal_strong_lower_bound : UniversalStrongLowerBound`

together with every declaration it depends on.  `UniversalAssembly` is the sole
import: it is the assembly module that closes the argument, and it transitively
re-exports the whole production dependency closure, so no further import is
needed here.

The `#print axioms` receipts live in `StarKakeyaLower.Audit`, which is a separate
build target on purpose so that auditing never becomes a production dependency.
-/
