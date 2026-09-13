#!/usr/bin/env python3
"""Strict Arb certifier for the class-independent finite terminal witness.

The verifier parses every number as an exact rational, recomputes all kernels
with Arb outward rounding, includes the closed seam M=R, and fails closed.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction
from pathlib import Path
from typing import Any
from flint import arb, ctx
ctx.prec=192
Z,O,T=arb(0),arb(1),arb(2); HALF=O/T; PI=arb.pi()
SCHEMA='class-independent-terminal-strict-witness-v1'
CANONICAL_GRID_SIZE=133
CANONICAL_GRID_SHA256='025f0f529ceebdea43e1179115ce8eee7f0766cdee196472f3e969fc249aa306'
EXPECTED_CONTRACTS={
 'finite_block':'one H-TC terminal receipt for all M in [M0,R), plus one class-global positive or separate exact-pole column',
 'source_load':'low+terminal_global+class_positive+class_pole+tail_first <= 1 on every radial atom',
 'remaining_scales':'fresh disjoint full-price bands [2^(n-1)R,2^n R), n>=1; first omitted high class is [2R,4R)',
 'numbers':'all JSON numerics consumed by verifier are exact rational strings',
}

class SchemaError(ValueError): pass
def F(x:Any)->Fraction:
 if isinstance(x,bool): raise SchemaError('boolean is not a rational numeric input')
 if isinstance(x,int): return Fraction(x)
 if isinstance(x,str): return Fraction(x)
 raise SchemaError('all numeric witness inputs must be integer or rational string')
def A(x:Any)->arb:
 q=F(x) if not isinstance(x,Fraction) else x
 return arb(q.numerator)/arb(q.denominator)
def lo(x): return str(arb(x).lower())
def hi(x): return str(arb(x).upper())
def positive(x): return arb(x).lower()>0

def p0(a,b):
 a,b=arb(a),arb(b)
 if b<=a:return Z
 if b<=O:return (b*b-a*a)/T
 if a>=O:return b-a
 return (O-a*a)/T+b-O
def p1(a,b):
 a,b=arb(a),arb(b)
 if b<=a:return Z
 if b<=O:return (b**3-a**3)/arb(3)
 if a>=O:return (b*b-a*a)/T
 return (O-a**3)/arb(3)+(b*b-O)/T

def h_integral(s,a,b):
 """Integral_a^b min(r,1) min(1/2,(s-r)_+) dr, exact Arb path."""
 s,a,b=map(arb,(s,a,b)); out=Z
 x0=a;x1=min(b,s-HALF)
 if x1>x0: out += HALF*p0(x0,x1)
 x0=max(a,s-HALF);x1=min(b,s)
 if x1>x0: out += s*p0(x0,x1)-p1(x0,x1)
 return out

def low_primitive(r,H,m):
 r=max(Z,min(arb(r),HALF)); alpha=T*(O/(T*(O-m))).asin(); beta=(H/m).atan()
 ch=T*alpha/(alpha+T*beta); r0=m*beta/(alpha+beta)
 def pp(x):return -x*x+arb(4)*m*x-arb(4)*m*m*(O+x/m).log()
 def pq(x):return -x*x/T+x-(HALF+x).log()/T
 aa=min(H,r0);u=min(r,m)
 total=ch*u*u/T if u<=aa else ch*aa*aa/T+pp(u)-pp(aa)
 if r<=m:return total
 kh=alpha/(alpha+T*(T*H).asin());cross=HALF*(O-kh)/(O+kh);v=min(r,HALF)
 if v>m:
  w=min(v,cross)
  if w>m:total+=kh*(w*w-m*m)/T
  q=max(m,cross)
  if v>q:total+=pq(v)-pq(q)
 return total

def pos_primitive(r,m):
 """Integral r*(m-r)/(m+r) dr (all support r<1)."""
 r=arb(r); return -r*r/T+T*m*r-T*m*m*(O+r/m).log()
def tiny_primitive(r):
 r=arb(r);return r*r/T-T*r**3/arb(3)
def positive_integral(a,b,m):
 a=max(Z,arb(a));b=min(arb(b),m)
 if b<=a:return Z
 seam=O-m;out=Z
 u=min(b,seam)
 if u>a:out+=tiny_primitive(u)-tiny_primitive(a)
 u=max(a,seam)
 if b>u:out+=pos_primitive(b,m)-pos_primitive(u,m)
 return out

def n_at(M,h):
 M,h=arb(M),arb(h);return (M*M+O-T*(M*M-h*h).sqrt()).sqrt()

def load(path:Path):
 raw=path.read_bytes();w=json.loads(raw,parse_float=str,parse_int=str)
 if w.get('schema')!=SCHEMA or w.get('status')!='FIXED_RATIONAL_CANDIDATE':raise SchemaError('schema/status mismatch')
 if w.get('contracts')!=EXPECTED_CONTRACTS:raise SchemaError('contracts mismatch')
 parameter_values={k:F(w[k]) for k in ('H','M0','R')}
 H,m,R=map(A,(parameter_values['H'],parameter_values['M0'],parameter_values['R']))
 if not (Z<H<=HALF and HALF<=m<O and O-m<H and O<=R and m<R):
  raise SchemaError('require 0<H<=1/2, 1/2<=M0<1, 0<1-M0<H, and 1<=R with M0<R')
 target_value=F(w['target_pi_times_coefficient']);target=A(target_value);rg=[F(x) for x in w['radial_grid']]
 grid_identity='\n'.join(f'{x.numerator}/{x.denominator}' for x in rg).encode()
 if len(rg)!=CANONICAL_GRID_SIZE or hashlib.sha256(grid_identity).hexdigest()!=CANONICAL_GRID_SHA256:
  raise SchemaError('canonical radial_grid identity mismatch')
 if any(y<=x for x,y in zip(rg,rg[1:])):raise SchemaError('radial_grid not increasing')
 keys={'low','terminal_global','class_positive','class_pole','tail_first'}
 if set(w.get('prices',{}))!=keys:raise SchemaError('price family mismatch')
 nr=len(rg)-1;p={}
 for k in keys:
  if not isinstance(w['prices'][k],list) or len(w['prices'][k])!=nr:raise SchemaError(f'{k} length mismatch')
  p[k]=[F(x) for x in w['prices'][k]]
  if any(x<0 for x in p[k]):raise SchemaError(f'{k} negative')
 return raw,{'H':H,'m':m,'R':R,'target':target,'rg':rg,'p':p,
             'parameters':{k:str(w[k]) for k in parameter_values},
             'target_label':str(w['target_pi_times_coefficient'])}

def dot_cells(price,rg,fn):
 return sum((A(q)*fn(A(a),A(b)) for q,a,b in zip(price,rg[:-1],rg[1:])),Z)
def source(d):
 best=Z;where=None;terms=None
 for i in range(len(d['rg'])-1):
  tt={k:A(v[i]) for k,v in d['p'].items()};q=sum(tt.values(),Z)
  if q.upper()>best.upper():best=q;where=i;terms=tt
 return {'upper':hi(best),'atom':where,'terms_upper':{k:hi(v) for k,v in terms.items()},'pass':best.upper()<=O}
def receipts(d):
 H,m,R,rg,p=d['H'],d['m'],d['R'],d['rg'],d['p']
 low=dot_cells(p['low'],rg,lambda a,b:low_primitive(b,H,O-m)-low_primitive(a,H,O-m))
 term=dot_cells(p['terminal_global'],rg,lambda a,b:h_integral(m,a,b))/(PI*R)
 tail=dot_cells(p['tail_first'],rg,lambda a,b:h_integral(R,a,b))/(PI*T*R)
 # For positive sheets N is maximized at an endpoint in M (derivative changes
 # sign at most once, from negative to positive), and at h=H.
 Nmax=max(n_at(m,H).upper(),n_at(R,H).upper())
 pos=term+dot_cells(p['class_positive'],rg,lambda a,b:positive_integral(max(a,Nmax),b,m))
 # Exact pole: for M<1 the receipt increases. For M>1 it is concave
 # between events where M or M-1 crosses a radial-grid endpoint, hence its
 # minimum is at an event endpoint. Duplicates in this list are harmless.
 pole_candidates=[m,O,R]
 for x in rg:
  ax=A(x)
  if O<=ax<=R:pole_candidates.append(ax)
  if O<=O+ax<=R:pole_candidates.append(O+ax)
 polevals=[]
 for M in sorted(pole_candidates,key=lambda x:x.lower()):
  N=abs(M-O)
  polevals.append((M,term+dot_cells(p['class_pole'],rg,lambda a,b:p0(max(a,N),min(b,M)))))
 pole=arb(min(v.lower() for _,v in polevals))
 # Remaining classes: m_n=2^n R, n>=1 after first [R,2R).
 # Full fresh band [m_n/2,m_n) gives (m_n/4-1/8)/(2*pi*m_n),
 # increasing in m_n, hence first omitted class m_1=2R is worst.
 nextM=T*R; later=(nextM/arb(4)-arb(1)/arb(8))/(T*PI*nextM)
 return {'low':low,'terminal_global':term,'positive_all_M_h':pos,'positive_N_upper':Nmax,
         'pole_closed_M_interval':pole,'pole_endpoint_values':[(M,v) for M,v in polevals],
         'tail_first':tail,'remaining_dyadic_tail_floor':later}
def stable(path,obj):
 raw=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode();path.write_bytes(raw);return hashlib.sha256(raw).hexdigest()
def run(wp:Path):
 raw,d=load(wp);src=source(d);rr=receipts(d);target=d['target']/PI
 checks={k:positive(v-target) for k,v in rr.items() if k not in {'terminal_global','positive_N_upper','pole_endpoint_values'}}
 # Explicit target comparisons avoid relying on a decimal rendering.
 total_lower=min(rr[k].lower() for k in checks)
 out={'schema':'class-independent-terminal-strict-arb-receipt-v1','witness':wp.name,
  'witness_sha256':hashlib.sha256(raw).hexdigest(),'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'arb_bits':ctx.prec,'parameters':d['parameters'],'source_load':src,
  'target':{'pi_times_coefficient':d['target_label'],'coefficient_upper':hi(target)},
  'receipts':{k:([{'M':str(M),'lower':lo(v)} for M,v in x] if k=='pole_endpoint_values' else lo(x)) for k,x in rr.items()},
  'checks':checks,'coefficient_lower':str(total_lower),'pi_times_coefficient_lower':lo(PI*arb(total_lower)),
  'strict_gt_0p08':positive(PI*arb(total_lower)-A('2/25')),
  'strict_gt_0p082':positive(PI*arb(total_lower)-A('41/500')),
  'coverage':['closed finite seam M in [M0,R]','positive h in [0,H]','separate exact pole h=0','first tail [R,2R)','all remaining dyadic scales by monotone exact formula','pointwise source load'],}
 out['status']='PASS' if src['pass'] and all(checks.values()) and out['strict_gt_0p082'] else 'FAIL'
 return out
def main():
 ap=argparse.ArgumentParser();ap.add_argument('witness',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args();out=a.output or a.witness.with_name(a.witness.stem+'_strict_receipt.json')
 try:r=run(a.witness)
 except Exception as e:r={'schema':'class-independent-terminal-strict-arb-receipt-v1','status':'ERROR','error':str(e)}
 h=stable(out,r);print(json.dumps({'status':r['status'],'receipt':str(out),'sha256':h,'pi_lower':r.get('pi_times_coefficient_lower')},indent=2))
 if r['status']!='PASS':raise SystemExit(2)
if __name__=='__main__':main()