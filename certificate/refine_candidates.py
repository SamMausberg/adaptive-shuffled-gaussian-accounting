"""Certify improved epoch inequalities from conditional candidate sums.

Floating-point arithmetic is used only to select a clone parameter. The chosen
inequality is re-evaluated using directed MPFR intervals before acceptance.
"""
from mpinterval import I,F,jd,version
from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parent
OUT=1<<100

def gaussian(e,sigma,epochs=1):
    mu=I(epochs).sqrt()/sigma
    return (-e/mu+mu/2).cdf()-e.exp()*(-e/mu-mu/2).cdf()

def readvals(sigma):
    inp=json.loads((ROOT/f'candidate_inputs_sigma{sigma}.json').read_text());M=inp['M']
    fs=[[None]*M for _ in range(556)];rs=[[None]*M for _ in range(556)]
    with (ROOT/f'candidate_values_sigma{sigma}.txt').open() as f:
        assert f.readline().startswith('#');assert list(map(int,f.readline().split()))==[M,556]
        for line in f:
            m,j,a,b=line.split();m=int(m);j=int(j)
            fs[j][m-1]=F(float.fromhex(a))/m
            rs[j][m-1]=F(float.fromhex(b))/m
    assert all(x is not None for row in fs+rs for x in row)
    return inp,fs,rs

def refine(sigma):
    import numpy as np
    from scipy.special import ndtr
    from scipy.stats import binom
    inp,ff,rr=readvals(sigma);M=inp['M'];tau=F(*map(int,inp['tau_upper']))
    logk=I(F(51,50)).log();T=1000
    nums=list(range(140 if sigma==1 else 65,381 if sigma==1 else 241))
    hs=np.array(nums)/40;ps=np.exp(-hs)
    weights=binom.pmf(np.arange(M)[None,:],T-1,ps[:,None])
    tails=binom.sf(M-1,T-1,ps)
    betas=(T-1)*(ps*ndtr(-sigma*hs+1/(2*sigma))-ndtr(-sigma*hs-1/(2*sigma)))
    W={};B={};Tail={}
    def exact_weights(hnum):
        if hnum not in W:
            h=I(F(hnum,40));p=(-h).exp();q=1-p
            w=[q**(T-1)]
            for m in range(1,M):w.append(w[-1]*F(T-m,m)*p/q)
            total=sum(w,I(0));tail=I.between(0,max(F(0),(1-total).upper()))
            beta=(T-1)*(p*(-sigma*h+F(1,2*sigma)).cdf()-(-sigma*h-F(1,2*sigma)).cdf())
            assert beta.lower()>=0
            W[hnum]=w;B[hnum]=beta;Tail[hnum]=tail
        return W[hnum],B[hnum],Tail[hnum]
    rows=[];audit=[];wins=[0,0];beg=time.time()
    for j in range(556):
        k=I(F(51,50)**j);ep=j*logk;g=gaussian(ep,sigma)
        # Audit the scalar boundary independently of the numerical recurrence.
        assert I(ff[j][0]+tau).upper()>=g.lower(),('forward scalar check',sigma,j)
        assert (k*rr[j][0]).upper()>=g.lower(),('reverse scalar check',sigma,j)
        kval=float(F(51,50)**j);gv=float(g.upper())
        f=np.array([float(v+tau) for v in ff[j]]);r=kval*np.array([float(v) for v in rr[j]])
        f=np.minimum(f,gv);r=np.minimum(r,gv)
        bounds=[];witness=[]
        for di,(arr,vals) in enumerate([(f,ff[j]),(r,rr[j])]):
            opt=weights@arr+tails*gv+(1+kval)*betas
            hnum=nums[int(np.argmin(opt))]
            w,b,tail=exact_weights(hnum)
            terms=[]
            for m,v in enumerate(vals):
                vb=I(v+tau) if di==0 else k*v
                vv=min(vb.upper(),g.upper())
                terms.append(w[m]*vv)
            candidate=sum(terms,I(0))+tail*g+(1+k)*b
            if candidate.upper()<g.upper():out=candidate;kind='candidate';wins[di]+=1
            else:out=g;kind='gaussian'
            z=min(OUT,max(0,out.ceil_scaled(100)))
            bounds.append(z)
            witness.append({'kind':kind,'h':jd(F(hnum,40)), 'candidate_upper':jd(candidate.upper()),'tail_probability_upper':jd(tail.upper()),'beta_upper':jd(b.upper())})
        rows.append({'j':j,'forward_numerator':str(bounds[0]),'reverse_numerator':str(bounds[1])})
        audit.append({'j':j,'forward':witness[0],'reverse':witness[1]})
        if j%100==0:print('REFINE',sigma,j,'seconds',round(time.time()-beg,1),flush=True)
    spec={'sigma':sigma,'T':T,'ratio':['51','50'],'J':555,'denominator':str(OUT),'MPFR':version(),'rows':rows}
    (ROOT/f'profile_sigma{sigma}.json').write_text(json.dumps(spec,indent=2))
    (ROOT/f'candidate_audit_sigma{sigma}.json').write_text(json.dumps({'wins':wins,'rows':audit},indent=2))
    print('ACCEPT PROFILE',sigma,'candidate wins',wins,'seconds',round(time.time()-beg,1),flush=True)
if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):refine(s)
