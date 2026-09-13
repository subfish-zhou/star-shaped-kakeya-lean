# Status of the 0.0975576139796 candidate

## Verdict

**BLOCKED; not certified.**

The proposed constant is

\[
C_*=4+2\pi+\pi\operatorname{Si}(\pi),\qquad
rac{\pi}{2C_*}=0.0975576139796276\ldots.
\]

The arithmetic, unit-chord-to-operator bridge, finite-menu exhaustion, essential-infimum inner approximation, and open outer-envelope passage have survived review.

## First fatal gap

The endpoint estimate claims two orientation lanes of cost `π` each. Each output token has a unique witness and a unique low endpoint, but this establishes only **demand-once**. Different outputs and spans can map to the same physical source atom `(endpoint, height)`. No injectivity, bounded multiplicity, or all-cut/source-resolved capacity theorem has been proved.

Therefore the step

\[
|X_+|\le \pi\int y,\qquad |X_-|\le\pi\int y
\]

is not established. Consequently neither

\[
\int Ty\le C_*\int y
\]

nor the numerical lower bound `0.0975576139796` may be stated as a theorem.

## Certified status

The project-wide certified lower bound remains the pair certificate

\[
C_{\mathrm{pair},64}pprox0.07054487627351847.
\]

The direct Radon-ridge theorem is separately certified at approximately `0.03575887536`.

## Research decision

Do not continue incremental constant tuning on this blocked proof. Preserve it as a candidate architecture and move the main line to the literal primal obstacle-union framework.
