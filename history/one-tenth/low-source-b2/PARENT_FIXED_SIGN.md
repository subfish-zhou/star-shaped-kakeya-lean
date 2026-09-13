# Parent lemma candidate: fixed far-height sign already supplies the paired target

Status: parent analytic derivation, pending independent review. No new global area claim. This is a narrower positive result, not a proof for mixtures of the two signs.

## Fixed-sign all-cut statement

For a Borel low selector, orient each chord toward a far endpoint, with a fixed Borel tie rule. Its local endpoints are(x-1,h),(x,h), x>=1/2, |h|<=1/5 and M<99/100. Let V be any Borel subcut on which this **far-oriented** h has one fixed sign; h=0 labels may be assigned to either side, once only.

Then the proposed sharper bound is

`|S_r(V)| >= min(11/13,1-2r)|V|`, 0<r<1/2.                 (FS)

It implies the stronger-than-needed fixed-sign version of PL, and an integrated coefficient `2189*pi/52728` on the low bank[0,1/2]. The condition concerns far-oriented height; it is not automatic from choosing a projective coordinate chart.

## Proof derivation

1. Use B1 endpoint-domain Theorem1's actual far bases J_r(q). For r<=|h| use the full cone. For r>|h| use the existing capped far lobe. Its additional extension toward the ideal far anchor has length b, and the proved ratio satisfies

`b/|J_r(q)| <= max(B_L,r/(1/2-r))`.

B1 Theorem3 supplies B_L with `1/(1+2B_L)>11/15`, hence `B_L<2/11`.

2. If all far-oriented h are positive, every extension goes in the same clockwise direction on the ordinary angular circle; if all are negative, every extension goes counterclockwise. It is important that these are physical-circle directions, not arbitrary independently reflected local drawings. At h=0 the base is the actual far singleton and extension is zero.

3. The usual open-component proof improves when extensions all have the same side. If each extension/base length is at mostlambda, bases in an open component C of lengthell stay inside C enlarged only on that fixed side by(lambda-1)ell. Thus the entire extended union has outer length at mostlambda times the base union, not(2lambda-1) times. Wrapping only reduces length; a full-circle component is trivial. The argument works for infinite families and singletons.

4. Apply this one-sided union lemma with `lambda=1+max(B_L,r/(1/2-r))`. The extended union contains one Borel far lift of V, of length|V|. Therefore

`|S_r(V)| >= min(1/(1+B_L),1-2r)|V| >= min(11/13,1-2r)|V|`.

The last bound is weakened to a rational cap, not optimized. Integrating the displayed profile against r on[0,1/2] gives

`integral r min(11/13,1-2r)dr = [1-(2/13)^3]/24 =2189/52728`.

The physical union is charged once throughout. Borel recovery and the height dichotomy precede applying this lemma to an arbitrary original star.

## Exact remaining difficulty

For mixed far signs, the two fixed-sign subunions can overlap. Their independently obtained payments can be maximized, not added. This note DOES NOT prove PL or IL for their union.

In particular the failure of the old common mixed-side factor is now localized to cross-sign source overlap, rather than to either fixed-sign population. Near-endpoint lobes remain a possible way to compensate that overlap; they have not been assigned a free second budget.

A simple conditional consequence of FS is that IL already holds if one sign occupies at least4/5 of the low direction mass, since `(4/5)*(2189*pi/52728)>1/10`. This follows by ignoring the minority source, not by charging it negatively. The fixed rational comparison with pi>223/71 is checked separately. Any remaining hard mixed case for this criterion has neither sign reaching4/5; this is not asserted to be the sharp imbalance threshold.
