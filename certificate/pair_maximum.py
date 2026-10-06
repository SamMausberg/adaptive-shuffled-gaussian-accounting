"""Attainable product-pair lower bounds from the per-epoch coordinate maximum.

The upper endpoints below refer to this binned statistic only. They are never
used as upper bounds on the continuous Chua pair or adaptive shuffling.
"""
from pathlib import Path
from collections import defaultdict
import json,sys,time
from mpinterval import I,F,jd,version
from lattice import Law,atoms,mul,power,Score,inverse,result_row,SCALE,BITS
ROOT=Path(__file__).resolve().parent
R=F(2001,2000)

def prepare(sigma):
    T=1000;logr=I(R).log();maps=[defaultdict(int) for _ in range(4)];audit=[]
    def cdf(c,a):
        return (I(c)/sigma).cdf()**(T-1)*((I(c)-a)/sigma).cdf()
    pp=I(0);qq=I(0)
    # Width .01 in standardized coordinates; the extreme tail is one bin.
    cuts=[F(sigma*j,100) for j in range(0,1201)]
    for idx,c in enumerate(cuts+[None]):
        p1=I(1) if c is None else cdf(c,2)
        q1=I(1) if c is None else cdf(c,1)
        p=p1-pp;q=q1-qq;pp=p1;qq=q1
        wp=max(0,p.floor_scaled(BITS));wq=max(0,q.floor_scaled(BITS))
        if not wp and not wq:continue
        assert p.lower()>0 and q.lower()>0
        loss=(p/q).log()/logr
        fl=loss.lower().__floor__();fu=loss.upper().__ceil__()
        rl=(-loss.upper()).__floor__();ru=(-loss.lower()).__ceil__()
        for m,j,w in zip(maps,[fl,rl,fu,ru],[wp,wq,wp,wq]):m[j]+=w
        audit.append({'right':None if c is None else jd(c),'P_lower':jd(p.lower()),'Q_lower':jd(q.lower()),
                      'loss_indices':[fl,rl,fu,ru]})
    laws=[atoms(m) for m in maps]
    assert all(l.total()<=SCALE for l in laws)
    obj={'sigma':sigma,'T':T,'r':jd(R),'scope':'Binned maximum of the attained Chua pair, independently repeated each epoch.',
         'MPFR':version(),'laws':[l.obj() for l in laws],'bin_audit':audit}
    (ROOT/f'pair_maximum_input_sigma{sigma}.json').write_text(json.dumps(obj,separators=(',',':')))
    print('PREP MAX',sigma,[(l.offset,len(l.masses),float(F(SCALE-l.total(),SCALE))) for l in laws],flush=True)
    return laws

def run(sigma):
    t=time.time();laws=prepare(sigma);powers=[{1:l} for l in laws]
    cap=100000
    for n in [2,4,8,16]:
        for pp in powers:pp[n]=mul(pp[n//2],pp[n//2],cap)
        print('MAX POWER',sigma,n,[(p[n].offset,len(p[n].masses)) for p in powers],flush=True)
    rows=[]
    for e in [1,2,3,5,10,20]:
        cur=[]
        for pp in powers:
            v=Law(0,[SCALE])
            for n in [1,2,4,8,16]:
                if e&n:v=mul(v,pp[n],cap)
            cur.append(v)
        row=result_row(e,*cur,R,F(1,10**8));rows.append(row)
        (ROOT/f'pair_maximum_convolution_sigma{sigma}_epochs{e}.json').write_text(json.dumps({'laws':[l.obj() for l in cur]},separators=(',',':')))
        print('ACCEPT MAX',sigma,e,row['epsilon_lower_decimal'],row['epsilon_upper_decimal'],row['delta_at_lower_decimal'],row['delta_at_upper_decimal'],'elapsed',round(time.time()-t,1),flush=True)
    (ROOT/f'pair_maximum_results_sigma{sigma}.json').write_text(json.dumps({'sigma':sigma,'T':1000,'delta':jd(F(1,10**8)),
      'scope':'Lower bounds for the full continuous product pair; upper endpoints apply ONLY to the binned maximum statistic.','r':jd(R),'rows':rows},indent=2))
if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):run(s)
