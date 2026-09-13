# Parent candidate: low-height far-collar interval estimate

Status: **ACCEPTED as a paper-level all-cut lemma after independent B1 collar review**; no universal0.1 promotion. The filename records its candidate origin. This is a parent theory note in campaign `one-tenth-endpoint-geometry-20260905-b1`, independent of the three worker subtrees. Only fixed scalar checks of the displayed constants are authorized here; no search or price optimization.

## Statement

Let the selected unit-chord family be Borel, and let V be any Borel direction cut, common star center0, far endpoint radius m<=M_q<=R, and |h_q|<=H<m-1/2, where m>1/2. Let S_r(V) be the literal circular section of the triangle union. Define

`c = sqrt(1-H^2/(m-1/2)^2)`, `t = min(1/2,(m-r)_+)`.

Candidate all-cut bound, in physical angular measure with |V| the projective direction measure:

`|S_r(V)| >= [c*t/(2R-c*t)] |V| >= [c*t/(2R)] |V|`.        (P)

The old terminal coefficient is `t/(pi R)`. Hence the linear part of(P) improves it uniformly wherever `pi*c>2`; no fixed prices or source banks are duplicated.

## Derivation requiring adversarial audit

1. Orient each chord toward its far endpoint. In its own orthonormal coordinates that endpoint is `(a,h)`, where `a=sqrt(M^2-h^2)>=1/2`. Take its length-t collar `(a-s,h)`, 0<=s<=t. All collar radii lie in `[M-t,M]` and therefore above r when r<m. Every collar ray at radius r is contained in the selected triangle. This is literal radial inclusion, not a marginal-area argument.

2. All collar radii are at least m-1/2>H and their longitudinal coordinates nonnegative. Along the collar, the radial derivative with respect to longitudinal coordinate is

`x/sqrt(x^2+h^2) = sqrt(1-h^2/(x^2+h^2)) >= c`.

If N_t is its inner-end radius, `M-N_t>=c*t`.

3. For h!=0 the collar image is an angular interval I from offset `beta=asin(|h|/M)` to `phi=asin(|h|/N_t)` on one side of the far ideal chord direction. Both offsets are below pi/2. Convexity of asin with f(0)=0 gives `beta/phi<=N_t/M`. Extending I from its near-angle endpoint toward the ideal direction therefore has length phi, at most

`lambda_q |I|`, where `lambda_q=phi/(phi-beta)<=M/(M-N_t)<=R/(c*t)`.

The extension actually contains the selected far ideal direction. The sign of h only chooses left versus right extension. No ideal direction is silently placed inside its original source interval.

4. For h=0 the image is already the singleton far ideal direction and needs no extension. The arbitrary-family circular interval lemma in baseline/PROOF.md permits such singleton bases and arbitrary mixtures of extension side. Use its common factor `lambda=R/(c*t)`: the union of extended intervals has measure at most `(2lambda-1)` times the union of base intervals.

5. The Borel chosen far directions form one lift of V into the physical circle, of measure |V|. Their union is contained in the extended intervals. Thus `|S_r(V)|>=|union I|>=|V|/(2lambda-1)`, which is(P). At r>=m use zero. At t=0 no division is used. Projective seam handled by the physical-circle interval lemma; no source symmetrization is introduced.

6. Integrate against a single fixed nonnegative radial price times min(r,1), as in the old terminal proof. Distinct cuts still require disjoint/shared-capacity price accounting. This statement alone does NOT permit giving the same radial price to multiple cuts and adding their payments.

## Why this might matter for0.1

- For the old finite-high cut m=99/100, R=8/5, H=1/5, `c=sqrt(2001)/49`. Relative to the old terminal payment, the linear bound gains `pi*sqrt(2001)/98`.
- For the old first-tail cut m=8/5, R=16/5, H=1/5, `c=sqrt(117)/11`. Its old full-price area coefficient53/640 would become at least `(53/640)*pi*sqrt(117)/22` if(P) is accepted.
- This exploits the low-height contradiction hypothesis, whereas the old coarse transverse collar bound did not. It does not require R=5/2 if the new lemma is valid; the capacity-interface worker is independently auditing the *old* tail obstruction.
- The old low-kernel ceiling is untouched. Even a successful tail improvement does not prove0.1; endpoint/low geometry remains essential.

Review targets: validity of the one-sided extension with variable radii and both signs; far-lift measurability; singleton/tie treatment; circular interval factor; no hidden simultaneous receipt summation. The bound is not to be entered into any optimized production schedule before independent review.
