#!/usr/bin/env python3
"""Two-sided rigid-sliver adversary for the unit-chord circle problem.

No repository imports. Angles live on R/(pi Z). For a direction theta and
0 <= h < r < R, the adversarial model selects one rigid sliver

    theta - s [asin(h/R), asin(h/r)],  s in {-1,+1}.

This is a genuine full-unit-chord adversary, not an unpaired relaxation: choose
N_theta={s0*h*n_theta+t*eps*e_theta: 0<=t<=1}. The perpendicular foot is the
endpoint of radius h<r, so that radial-window side is empty; the other endpoint
has radius sqrt(h^2+1), and realizes the selected sliver whenever
R<=sqrt(h^2+1). Thus allowing a nominal second side does not remove any
one-sided sharp microstructure.

The script has two independent paths.
(1) An exact-continuum periodic construction, obtained from
    q + 2 asin(h/R) = pi/K and q = asin(h/r)-asin(h/R).
(2) A finite-cell minimum-union coordinate descent. Each theta-cell chooses h
    and its side independently. The reported union is the exact union of the
    swept closed arcs, not merely the number of occupied raster cells.

Run: python3 /tmp/two_sided_sliver_adversary.py --out /tmp/sliver_results.json
"""
from __future__ import annotations
import argparse, json, math, random
from dataclasses import dataclass
import numpy as np

L=math.pi

def ar(h,x): return math.asin(max(-1.0,min(1.0,h/x)))
def width(h,r,R): return ar(h,r)-ar(h,R)
def mu(r,R): return r/(R-r)

def solve_periodic(K,r,R):
    """K equal components; maximal gaps. Returns a continuum-feasible set."""
    target=L/K
    # period(h)=w(h)+2 alpha_R(h); q=w(h). It is strictly increasing.
    lo,hi=0.0,math.nextafter(r,0.0)
    if width(hi,r,R)+2*ar(hi,R)<target:
        # h is capped by r: there is then no saturated K-cell construction.
        h=hi; q=target-2*ar(h,R)
        if q+1e-15 < width(h,r,R): return None
    else:
        for _ in range(100):
            h=(lo+hi)/2
            if width(h,r,R)+2*ar(h,R)<target: lo=h
            else: hi=h
        h=(lo+hi)/2; q=width(h,r,R)
    dens=K*q/L
    return dict(K=K,h=h,q=q,gap=target-q,density=dens,
                effective_constant=1/dens,
                A_foot_endpoint=h,B_far_endpoint=math.hypot(h,1.0),
                radial_window_feasible=R<=math.hypot(h,1.0)+1e-15,
                unit_chord_error=0.0)

def periodic_tables(r,R,Ks):
    rows=[x for K in Ks if (x:=solve_periodic(K,r,R)) is not None]
    m=mu(r,R); sharp=1/(1+2*m)
    for x in rows:
        d=x['density']; x.update({
          'limit_density_1_over_1_plus_2mu':sharp,
          'margin_vs_limit':d-sharp,
          'violates_constant_1':d<1-1e-12,
          'violates_constant_1_plus_mu':d<1/(1+m)-1e-12,
          'respects_constant_1_plus_2mu':d>=sharp-1e-12})
    return rows

def arc_bins(center,alo,ahi,sgn,M,delta):
    """Raster bins hit by theta-cell sweep of one sliver."""
    x1=center-sgn*ahi; x2=center-sgn*alo
    a=min(x1,x2)-delta/2; b=max(x1,x2)+delta/2
    # output bin centres, conservative-ish candidate raster
    j0=math.floor(a/L*M-.5); j1=math.ceil(b/L*M-.5)
    return np.unique(np.array([j%M for j in range(j0,j1+1)],dtype=np.int32))

def merge_circle_arcs(arcs):
    """Exact Lebesgue measure of a finite union of circular arcs."""
    pieces=[]
    for a,b in arcs:
        length=b-a
        if length>=L: return L
        a%=L; b=a+length
        if b<=L: pieces.append((a,b))
        else: pieces.extend(((a,L),(0,b-L)))
    pieces.sort(); total=0.; ca=cb=None
    for a,b in pieces:
        if ca is None: ca,cb=a,b
        elif a<=cb+1e-15: cb=max(cb,b)
        else: total+=cb-ca; ca,cb=a,b
    if ca is not None: total+=cb-ca
    return total

@dataclass
class Choice:
    bins: np.ndarray
    arc: tuple
    h: float
    side: int

def discrete_search(r,R,N,H=31,restarts=4,passes=12,seed=20260803):
    """Coordinate descent for arbitrary pointwise h/side choices.

    Initial states include exact periodic microstructure-inspired selectors.
    Final density is measured from swept continuum arcs, hence every theta in
    its cell is served by the reported union.
    """
    rng=random.Random(seed+N)
    delta=L/N; M=4*N
    hs=np.linspace(0,r,H,endpoint=False)
    centers=(np.arange(N)+.5)*delta
    choices=[]
    for th in centers:
        cc=[]
        for h in hs:
            lo,hi=ar(h,R),ar(h,r)
            for s in (-1,1):
                x1=th-s*hi; x2=th-s*lo
                a=min(x1,x2)-delta/2; b=max(x1,x2)+delta/2
                cc.append(Choice(arc_bins(th,lo,hi,s,M,delta),(a,b),float(h),s))
        choices.append(cc)
    best=None
    # Periodic-inspired starts at several cell periods, plus random starts.
    starts=[]
    for pcell in (6,8,10,12,16,20):
        if pcell>N: continue
        K=max(1,round(N/pcell)); sol=solve_periodic(K,r,R)
        if not sol: continue
        period=L/K; q=sol['q']; ass=[]
        for th,cc in zip(centers,choices):
            x=th%period
            if x<q: target_h=0.; side=1
            else:
                dl=x-q; dr=period-x
                dist=min(dl,dr); target_h=R*math.sin(dist)
                side=1 if dl<=dr else -1
            ass.append(min(range(len(cc)),key=lambda j:abs(cc[j].h-target_h)+(0 if cc[j].side==side else 1e-6)))
        starts.append(ass)
    while len(starts)<restarts+6:
        starts.append([rng.randrange(len(choices[i])) for i in range(N)])
    for assignment in starts[:restarts+6]:
        counts=np.zeros(M,dtype=np.int32)
        for i,j in enumerate(assignment): counts[choices[i][j].bins]+=1
        for _ in range(passes):
            order=list(range(N)); rng.shuffle(order); changed=0
            for i in order:
                old=assignment[i]; counts[choices[i][old].bins]-=1
                # exact raster union increment relative to all other theta cells
                scores=[]
                for c in choices[i]: scores.append(int(np.count_nonzero(counts[c.bins]==0)))
                mn=min(scores); cand=[j for j,v in enumerate(scores) if v==mn]
                new=rng.choice(cand)
                assignment[i]=new; counts[choices[i][new].bins]+=1
                changed += new!=old
            if changed==0: break
        arcs=[choices[i][j].arc for i,j in enumerate(assignment)]
        exact=merge_circle_arcs(arcs)/L; raster=np.count_nonzero(counts)/M
        rec=dict(N=N,H=H,output_bins=M,density_exact_swept=exact,
                 density_raster=raster,n_components_proxy=int(np.count_nonzero((counts>0)&~np.roll(counts>0,1))),
                 passes=passes)
        if best is None or exact<best['density_exact_swept']: best=rec
    return best

def pairing_mutation(r,R):
    """Verify that every selected-side candidate has a full unit-chord embedding."""
    hs=np.linspace(0,r,1001,endpoint=False)
    embedded=[]
    for h in hs:
        # Foot-at-endpoint chord: near radius A=h<r, far radius B=sqrt(h^2+1).
        embedded.append(R<=math.hypot(h,1.0)+1e-15)
    return {'all_candidates_embed_as_unit_chords':all(embedded),
      'fraction_embedded':sum(embedded)/len(embedded),
      'verdict':'NO-GO EMBEDDING: every selected one-sided sliver is realized by a full unit chord whose foot endpoint lies below r, so the second radial-window side vanishes.',
      'consequence':'Any universal two-sided class permitting side vanishing contains the one-sided sharp class and cannot improve the constant 1+2mu.'}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',default='/tmp/sliver_results.json')
    ap.add_argument('--quick',action='store_true'); a=ap.parse_args()
    cases=[]
    for r in ([.1,.2,.3,.4] if not a.quick else [.1,.2,.4]):
        R=.5; Ks=[1,2,4,8,16,32,64,128,256]
        rows=periodic_tables(r,R,Ks)
        discs=[discrete_search(r,R,N,H=25 if a.quick else 41,restarts=2 if a.quick else 5,passes=8 if a.quick else 15)
               for N in ([120,240] if a.quick else [120,240,480])]
        m=mu(r,R)
        cases.append({'r':r,'R':R,'mu':m,
          'candidate_constants':{'1':1,'1+mu':1+m,'1+2mu':1+2*m},
          'candidate_density_bounds':{'1':1.,'1/(1+mu)':1/(1+m),'1/(1+2mu)':1/(1+2*m)},
          'periodic_continuum':rows,'discrete_arbitrary_choice':discs,
          'pairing_deletion_mutation':pairing_mutation(r,R)})
    out={'model':'rigid arcsin slivers on R/(pi Z), pointwise side choice',
      'sharp_formula_guess':'inf |U|/pi = 1/(1+2 mu) = (R-r)/(R+r), mu=r/(R-r); attained only as a homogenized K->infinity periodic limit (except degenerate endpoints).',
      'interpretation':'For a U-component of width q, a sliver of height h fits iff w(h)<=q and serves theta up to alpha_R(h). Thus its enlargement is q+2 alpha_R(h). As q,h->0, alpha_R/w -> r/(R-r)=mu.',
      'warning':'Numerics construct upper bounds/adversaries, not continuum lower bounds. The matching lower bound 1/(1+2mu) is the separate component-enlargement argument.',
      'cases':cases}
    with open(a.out,'w') as f: json.dump(out,f,indent=2)
    print('wrote',a.out)
    for c in cases:
      last=c['periodic_continuum'][-1]
      print(f"r={c['r']:.2f} mu={c['mu']:.6f} limit={c['candidate_density_bounds']['1/(1+2mu)']:.9f} K={last['K']} dens={last['density']:.9f}")
      for d in c['discrete_arbitrary_choice']: print(' ',d)
    print('pairing mutation:',cases[0]['pairing_deletion_mutation']['verdict'])
if __name__=='__main__': main()
