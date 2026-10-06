"""Certified pessimistic accounting for matched Poisson subsampling.

Each step has A=(1-q)N(0,sigma^2)+qN(1,sigma^2), B=N(0,sigma^2).
On each likelihood-ratio bin, replace the B-law by its mean-preserving endpoint
spread. The spread dominates the bin law in convex order, so its product is a
valid upper accountant. The omitted high tail is revealed perfectly.
"""
from pathlib import Path
from collections import defaultdict
from mpinterval import I,F,jd,version,decimal_up
from lattice import Law,atoms,mul,power,Score,inverse,SCALE,BITS
import json,sys,time
ROOT=Path(__file__).resolve().parent
R=F(10001,10000);Q=F(1,1000)

def prepare(sigma):
    logr=I(R).log();j0=((I(1-Q).log()/logr).lower()).__floor__()
    J=(((1-Q+Q*(I(10)/sigma-F(1,2*sigma*sigma)).exp()).log()/logr).upper()).__ceil__()
    a=1/(I(R)**(-j0));rr=I(R)
    def cumulative(t):
        if t.upper()<=1-Q:return I(0),I(0)
        assert t.lower()>1-Q
        z=sigma*(((t-(1-Q))/Q).log()+F(1,2*sigma*sigma))
        nq=z.cdf();np=(1-Q)*nq+Q*(z-F(1,sigma)).cdf()
        return np,nq
    prevp,prevq=cumulative(a);mp=defaultdict(int);mq=defaultdict(int)
    for j in range(j0,J):
        b=a*rr;pc,qc=cumulative(b);dp=pc-prevp;dq=qc-prevq
        wl=(b*dq-dp)/(b-a);wu=(dp-a*dq)/(b-a)
        # Mathematical endpoint probabilities are nonnegative. If an inclusion
        # interval crosses zero, zero is a conservative retained lower mass.
        il=max(F(0),wl.lower());iu=max(F(0),wu.lower())
        mp[j]+=max(0,(a*il).floor_scaled(BITS));mp[j+1]+=max(0,(b*iu).floor_scaled(BITS))
        mq[-j]+=max(0,I(il).floor_scaled(BITS));mq[-j-1]+=max(0,I(iu).floor_scaled(BITS))
        prevp=pc;prevq=qc;a=b
        if (j-j0)%5000==0:print('POISSON BINS',sigma,j,J,flush=True)
    laws=[atoms(mp),atoms(mq)]
    assert all(l.total()<=SCALE for l in laws)
    obj={'sigma':sigma,'q':jd(Q),'ratio':jd(R),'grid_indices':[j0,J],'MPFR':version(),
      'scope':'Pessimistic likelihood-ratio endpoint spread; omitted tails and rounding deficits charged at infinite privacy loss.',
      'laws':[l.obj() for l in laws],
      'genuine_high_tail_P_upper':jd((1-prevp).upper()),'genuine_high_tail_Q_upper':jd((1-prevq).upper())}
    (ROOT/f'poisson_input_sigma{sigma}.json').write_text(json.dumps(obj,separators=(',',':')))
    print('PREP POISSON',sigma,[(l.offset,len(l.masses),float(F(SCALE-l.total(),SCALE))) for l in laws],flush=True)
    return laws

def run(sigma):
    t=time.time();laws=prepare(sigma);cap=60000
    epoch=[]
    for i,l in enumerate(laws):
        pp=power(l,1000,cap);epoch.append(pp)
        print('POISSON EPOCH KERNEL',sigma,i,pp.offset,len(pp.masses),'missing',float(F(SCALE-pp.total(),SCALE)),'elapsed',round(time.time()-t,1),flush=True)
    powers=[{1:l} for l in epoch]
    for n in [2,4,8,16]:
        for pp in powers:pp[n]=mul(pp[n//2],pp[n//2],cap)
        print('POISSON POWER',sigma,n,flush=True)
    rows=[];delta=F(1,10**8)
    for e in [1,2,3,5,10,20]:
        cur=[]
        for pp in powers:
            v=Law(0,[SCALE])
            for n in [1,2,4,8,16]:
                if e&n:v=mul(v,pp[n],cap)
            cur.append(v)
        scores=[Score(v,R) for v in cur]
        ep,ds=inverse(scores,delta,True,1000)
        row={'epochs':e,'steps':1000*e,'epsilon_upper':jd(ep),'epsilon_upper_decimal':decimal_up(ep,3),
         'delta_upper':[jd(x) for x in ds],'delta_upper_decimal':[decimal_up(x,15) for x in ds],
         'missing':[jd(F(SCALE-v.total(),SCALE)) for v in cur]}
        rows.append(row)
        (ROOT/f'poisson_convolution_sigma{sigma}_epochs{e}.json').write_text(json.dumps({'laws':[l.obj() for l in cur]},separators=(',',':')))
        print('ACCEPT POISSON',sigma,e,row['epsilon_upper_decimal'],row['delta_upper_decimal'],'elapsed',round(time.time()-t,1),flush=True)
    (ROOT/f'poisson_results_sigma{sigma}.json').write_text(json.dumps({'sigma':sigma,'T':1000,'delta':jd(delta),'q':jd(Q),
       'ratio':jd(R),'scope':'Upper bound for the matched Poisson mechanism, not for fixed-size shuffling.','rows':rows},indent=2))
if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):run(s)
