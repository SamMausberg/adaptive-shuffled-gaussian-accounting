"""Verify one-epoch profile inequalities using exact dyadic intervals.
Proposal files select valid bounds; they are never trusted as numerical evidence.
"""
from intervals import I,D,BITS,log_fraction,ceildiv
from fractions import Fraction as F
from math import comb
from functools import lru_cache
from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parent
OUT_BITS=100
OUT_D=1<<OUT_BITS

def up100(x):
    assert x.hi>=0
    return min(OUT_D,ceildiv(x.hi,1<<(BITS-OUT_BITS)))

def gauss_profile(e,sigma,epochs=1):
    mu=I(epochs).sqrt()/sigma
    return (-e/mu+mu/2).cdf()-e.exp()*(-e/mu-mu/2).cdf()

class Moments:
    def __init__(self,sigma,T,orders):
        self.sigma=sigma;self.T=T;self.A=max(orders)
        amax=self.A;s2=2*sigma*sigma
        self.mu=[I(F(a*(a-1),s2)).exp() for a in range(amax+1)]
        cmu=[sum((self.mu[j]*(comb(a,j)*(-1)**(a-j)) for j in range(a+1)),I(0)) for a in range(amax+1)]
        cmu[0]=I(1);cmu[1]=I(0)
        def bell(mu):
            B=[[I(0) for _ in range(amax+1)] for _ in range(amax+1)];B[0][0]=I(1)
            for a in range(1,amax+1):
                for j in range(1,a+1):
                    B[a][j]=sum((comb(a-1,k-1)*mu[k]*B[a-k][j-1] for k in range(1,a-j+2)),I(0))
            return B
        B=bell(self.mu);C=bell(cmu)
        self.pos={};self.cen={};self.inv={}
        for a in sorted(orders):
            pos=[];cen=[];inv=[]
            for m in range(1,T+1):
                falling=1;ps=I(0);cs=I(0)
                for j in range(1,min(a,m)+1):
                    falling*=m-j+1;ps=ps+B[a][j]*falling;cs=cs+C[a][j]*falling
                pos.append(ps/(m**a));cen.append(cs/(m**a))
                inv.append(I(F(a-1,s2)+F((a-1)**2,s2*m)).exp())
            self.pos[a]=pos;self.cen[a]=cen;self.inv[a]=inv
            print('conditional moments',sigma,a,flush=True)
    @lru_cache(None)
    def weights(self,hnum):
        p=I(F(-hnum,20)).exp();q=1-p
        w=[q**(self.T-1)]
        for j in range(self.T-1):w.append(w[-1]*F(self.T-1-j,j+1)*p/q)
        total=sum(w,I(0))
        assert total.lo<=D<=total.hi and total.hi-total.lo<(1<<(BITS-160))
        h=I(F(hnum,20));s=self.sigma
        gamma=p*(-s*h+F(1,2*s)).cdf()-(-s*h-F(1,2*s)).cdf()
        assert gamma.lo>=0
        return w,(self.T-1)*gamma
    @lru_cache(None)
    def get(self,hnum,kind,a):
        w,_=self.weights(hnum)
        table={'positive':self.pos,'inverse':self.inv,'centered':self.cen}[kind][a]
        ans=sum((x*y for x,y in zip(w,table)),I(0))
        assert ans.lo>0 and ans.hi-ans.lo<max(1,ans.lo//(1<<140))
        return ans


def build(sigma):
    t=time.time();spec=json.loads((ROOT/f'witnesses_sigma{sigma}.json').read_text())
    assert sigma in (1,2) and spec['T']==1000 and spec['J']==555
    assert (spec['r_numerator'],spec['r_denominator'])==(51,50)
    assert [r['j'] for r in spec['records']]==list(range(556))
    orders={2}|{w['order'] for r in spec['records'] for w in (r['forward'],r['reverse']) if 'order'in w}
    M=Moments(sigma,spec['T'],orders)
    logr=log_fraction(F(spec['r_numerator'],spec['r_denominator']))
    rows=[];cert=[]
    for rec in spec['records']:
        j=rec['j'];k=I(F(51,50)**j);eps=j*logr;bounds=[]
        for direction in ['forward','reverse']:
            w=rec[direction];kind=w['kind']
            assert kind!='positive' or direction=='forward'
            assert kind!='inverse' or direction=='reverse'
            assert kind=='gaussian' or w['hnum']>0
            if kind=='gaussian':v=gauss_profile(eps,sigma)
            else:
                _,beta=M.weights(w['hnum'])
                a=w.get('order',2);r=a-1
                if kind in ('positive','inverse'):
                    mm=M.get(w['hnum'],kind,a)
                    v=F(r**r,a**a)*mm/(k**r)
                elif kind=='centered':
                    assert a%2==0 and j>0
                    mm=M.get(w['hnum'],kind,a)
                    v=F(r**r,a**a)*mm/((k-1)**r)
                    if direction=='reverse':v=v*k**a
                elif kind=='variance':
                    mm=M.get(w['hnum'],'centered',2)
                    if direction=='reverse':mm=mm*k*k
                    v=mm/(2*((mm+(k-1)**2).sqrt()+(k-1)))
                else:raise ValueError(kind)
                v=v+(1+k)*beta
            b=up100(v);bounds.append(b)
            cert.append({'j':j,'direction':direction,'witness':w,'upper_numerator':str(b),'upper_denominator':str(OUT_D),'interval_width_upper_2^-100':str(ceildiv(v.hi-v.lo,1<<(BITS-100)))})
        rows.append({'j':j,'forward_numerator':str(bounds[0]),'reverse_numerator':str(bounds[1])})
        if j%100==0:print('profile',sigma,j,'elapsed',round(time.time()-t,1),flush=True)
    out={'sigma':sigma,'T':spec['T'],'ratio':['51','50'],'J':spec['J'],'denominator':str(OUT_D),'interval_bits':BITS,'rows':rows}
    (ROOT/f'profile_sigma{sigma}.json').write_text(json.dumps(out,indent=2))
    (ROOT/f'profile_audit_sigma{sigma}.json').write_text(json.dumps(cert,indent=2))
    print('DONE',sigma,'seconds',round(time.time()-t,2),flush=True)
if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):build(s)
