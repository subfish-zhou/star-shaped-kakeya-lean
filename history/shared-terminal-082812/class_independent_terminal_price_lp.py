#!/usr/bin/env python3
"""FLOAT scout: one class-independent finite-high terminal radial price.

All finite high directions M in [M0,2*S6) are handled by ONE application of
H--TC with global worst interval [M0,2*S6).  Hence the terminal receipt is
source-once for arbitrary mixed-class cuts.  It is combined with radial low,
class-global positive/pole kernels, and a self-similar fresh-tail base price.
"""
from __future__ import annotations
import json, math, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

ROOT=Path('/home/argustest'); H=.2; M0=.99
S=np.array([.99,1.45628085,2.01689132,2.70060055,3.55177018,4.71011205,6.83593359])
NB=len(S); RMAX=2*S[-1]

def n_of_mh(M,h): return math.sqrt(max(0.,M*M+1-2*math.sqrt(max(0.,M*M-h*h))))
def G(x):
 x=max(0.,x); return .5*x*x if x<=1 else x-.5

def primitive_p(r,m): return -r*r+4*m*r-4*m*m*math.log1p(r/m)
def primitive_q(r): return -.5*r*r+r-.5*math.log(.5+r)
def low_cum(r):
 r=max(0.,min(r,.5));m=1-M0;alpha=2*math.asin(1/(2*M0));beta=math.atan(H/m);ch=2*alpha/(alpha+2*beta);r0=m*beta/(alpha+beta);aa=min(H,r0);u=min(r,m)
 z=ch*u*u/2 if u<=aa else ch*aa*aa/2+primitive_p(u,m)-primitive_p(aa,m)
 if r<=m:return z
 kh=alpha/(alpha+2*math.asin(2*H));cross=.5*(1-kh)/(1+kh);v=min(r,.5)
 if v>m:
  w=min(v,cross)
  if w>m:z+=kh*(w*w-m*m)/2
  qlo=max(m,cross)
  if v>qlo:z+=primitive_q(v)-primitive_q(qlo)
 return z

def p0_cells(lo,hi):
 lo=np.maximum(lo,0);hi=np.maximum(hi,lo)
 return np.where(hi<=1,(hi*hi-lo*lo)/2,np.where(lo>=1,hi-lo,(1-lo*lo)/2+hi-1))

def h_cells(s,rg):
 # ∫_cell min(r,1) ∫_0^.5 1_{r<s-t} dt dr
 x,w=np.polynomial.legendre.leggauss(48);lo=rg[:-1];hi=rg[1:];mid=(lo+hi)/2;half=(hi-lo)/2;r=mid[:,None]+half[:,None]*x
 return half*np.sum(w*np.minimum(r,1)*np.minimum(.5,np.maximum(0,s-r)),axis=1)

def class_cells(a,b,rg,lo_clip=None,hi_clip=None):
 x,w=np.polynomial.legendre.leggauss(48);lo=rg[:-1].copy();hi=rg[1:].copy()
 if lo_clip is not None:lo=np.maximum(lo,lo_clip)
 if hi_clip is not None:hi=np.minimum(hi,hi_clip)
 half=np.maximum(0,(hi-lo)/2);mid=(lo+hi)/2;r=mid[:,None]+half[:,None]*x
 m=np.maximum(np.maximum(a,r),1-r);active=m<np.minimum(b,1+r);g=np.where(active,(m-r)/(m+r),0.)
 return half*np.sum(w*np.minimum(r,1)*g,axis=1)

class Model:
 def __init__(self,dr=.05):
  pts=set(np.arange(0,RMAX+dr/2,dr).round(12));pts.update([0,.5,1,RMAX,M0,S[-1]])
  for a in S:pts.update([a,max(0,a-1),max(0,a-.5)])
  self.rg=np.array(sorted(x for x in pts if 0<=x<=RMAX));self.nr=len(self.rg)-1
  # columns: low, global terminal, pos[7], pole[7], tail-base
  self.ncol=2+2*NB+1;self.iz=self.ncol*self.nr;self.nv=self.iz+1
  self.low=np.array([low_cum(b)-low_cum(a) for a,b in zip(self.rg[:-1],self.rg[1:])])
  self.term=h_cells(M0,self.rg)/(math.pi*RMAX)
  self.tail=h_cells(2*S[-1],self.rg)/(math.pi*4*S[-1]);self.tail*=self.rg[:-1]>=S[-1]-1e-12
 def kernel(self,j,M,h,pole):
  N=n_of_mh(M,h);a=S[j];b=S[j+1] if j<NB-1 else RMAX
  if pole:
   aa=np.maximum(self.rg[:-1],N);bb=np.minimum(self.rg[1:],M);return p0_cells(aa,bb)*(bb>aa)
  return class_cells(a,b,self.rg,N,M)
 def rows(self,nm=25,nh=9):
  rows=[('low',None,{0:self.low}),('tail',None,{self.ncol-1:self.tail})]
  hs=np.unique(np.r_[1e-10,(np.linspace(0,1,nh)**2)*H])
  for j,a in enumerate(S):
   b=S[j+1] if j<NB-1 else RMAX
   for M in np.linspace(a,b,nm,endpoint=False):
    rows.append(('pole',(j,float(M),0.),{1:self.term,2+NB+j:self.kernel(j,M,0,True)}))
    for h in hs:
     rows.append(('positive',(j,float(M),float(h)),{1:self.term,2+j:self.kernel(j,M,h,False)}))
  return rows
 def solve(self,nm=25,nh=9,disable_terminal=False):
  rows=self.rows(nm,nh);A=lil_matrix((self.nr+len(rows)+(1 if disable_terminal else 0),self.nv));b=np.zeros(A.shape[0]);b[:self.nr]=1
  for c in range(self.ncol):
   for r in range(self.nr):A[r,c*self.nr+r]=1
  q=self.nr
  for _,_,parts in rows:
   for c,k in parts.items():A[q,c*self.nr:(c+1)*self.nr]=-k
   A[q,self.iz]=1;q+=1
  if disable_terminal:
   A[q,self.nr:2*self.nr]=1;b[q]=0
  c=np.zeros(self.nv);c[-1]=-1;res=linprog(c,A_ub=A.tocsr(),b_ub=b,bounds=[(0,None)]*self.nv,method='highs')
  if not res.success:raise RuntimeError(res.message)
  return res.x[:self.iz].reshape(self.ncol,self.nr),float(res.x[-1]),rows
 def receipt(self,kind,meta,P):
  if kind=='low':return float(P[0]@self.low)
  if kind=='tail':return float(P[-1]@self.tail)
  j,M,h=meta
  k=self.kernel(j,M,h,kind=='pole');c=(2+NB+j) if kind=='pole' else 2+j
  return float(P[1]@self.term+P[c]@k)
 def dense(self,P,nm=241,nh=31):
  worst=(math.inf,None);per=[];hs=np.unique(np.r_[1e-10,(np.linspace(0,1,nh)**2)*H])
  for j,a in enumerate(S):
   b=S[j+1] if j<NB-1 else RMAX;w=(math.inf,None)
   for M in np.linspace(a,b,nm,endpoint=False):
    for kind,h in [('pole',0.)]+[('positive',float(x)) for x in hs]:
     v=self.receipt(kind,(j,float(M),h),P)
     if v<w[0]:w=(v,(kind,j,float(M),h))
   per.append(w)
   if w[0]<worst[0]:worst=w
  return worst,per

def main():
 t=time.time();m=Model(.05);P,z,_=m.solve();worst,per=m.dense(P);P0,z0,_=m.solve(disable_terminal=True);worst0,_=m.dense(P0)
 load=P.sum(axis=0);target_cur=.073920942372137638/math.pi;target_1=.1/math.pi
 out={'schema':'class-independent-terminal-global-worst-float-scout-v1','status':'FLOAT64_SCOUT_NOT_CERTIFICATE','H':H,'M0':M0,'finite_high_range':[M0,RMAX],
 'all_cut_terminal_kernel':'ONE H-TC application to the entire finite-high cut with common [m,R)=[M0,2*S6): T_p=(pi*2*S6)^-1 int p(r) min(r,1) min(1/2,M0-r)_+ dr',
 'source_load':'p_low(r)+p_terminal_global(r)+sum_j(p_positive_j(r)+p_pole_j(r))+p_tail_base(r)<=1',
 'lp_z':z,'pi_lp_z':math.pi*z,'dense_min':worst[0],'pi_dense_min':math.pi*worst[0],'dense_worst':worst[1],
 'per_class_dense':[{'value':v,'point':p} for v,p in per],'no_terminal_lp_z':z0,'no_terminal_dense':worst0[0],
 'terminal_total_price_mass':float(P[1].sum()),'terminal_receipt':float(P[1]@m.term),'terminal_nonzero_atoms':int(np.count_nonzero(P[1]>1e-10)),
 'max_source_load':float(load.max()),'targets':{'current_per_rad':target_cur,'one_tenth_per_rad':target_1},
 'comparisons':{'dense_gt_current':worst[0]>target_cur,'dense_gt_one_tenth':worst[0]>target_1},
 'radial_grid':m.rg.tolist(),'prices':{'low':P[0].tolist(),'terminal_global':P[1].tolist(),'positive':P[2:2+NB].tolist(),'pole':P[2+NB:2+2*NB].tolist(),'tail_base':P[-1].tolist()},'elapsed_seconds':time.time()-t}
 (ROOT/'class_independent_terminal_price_witness.json').write_text(json.dumps(out,indent=2)+'\n');summary={k:v for k,v in out.items() if k not in ['prices','radial_grid']};(ROOT/'class_independent_terminal_price_receipt.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
