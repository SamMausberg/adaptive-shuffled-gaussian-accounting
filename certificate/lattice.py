"""Exact submeasure convolutions and directed privacy-loss evaluation.

Arrays store masses multiplied by 2**72, at loss j*log(r). Neither mass rounding
nor cropping is renormalized. Upper profiles charge all deficits at infinite loss;
lower profiles discard them. Integer packing checks its coefficient-sum identity.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from mpinterval import I,jd,decimal_up,decimal_down
import json,time
BITS=72; SCALE=1<<BITS; PACK=24; FB=512; FS=1<<FB
@dataclass
class Law:
    offset:int
    masses:list
    def trimmed(self):
        a=self.masses;l=0;u=len(a)
        while l<u and a[l]==0:l+=1
        while u>l and a[u-1]==0:u-=1
        return Law(self.offset+l,a[l:u]) if u>l else Law(0,[])
    def total(self):return sum(self.masses)
    def obj(self):return {'offset':self.offset,'mass_bits':BITS,'masses':list(map(str,self.masses))}
    @classmethod
    def fromobj(cls,x):
        assert x['mass_bits']==BITS
        return cls(x['offset'],list(map(int,x['masses'])))

def atoms(d):
    d={j:w for j,w in d.items() if w};lo=min(d);hi=max(d)
    return Law(lo,[d.get(j,0) for j in range(lo,hi+1)])

def mul(a,b,cap=None):
    if not a.masses or not b.masses:return Law(0,[])
    assert a.total()<=SCALE and b.total()<=SCALE
    aa=int.from_bytes(b''.join(x.to_bytes(PACK,'little') for x in a.masses),'little')
    bb=int.from_bytes(b''.join(x.to_bytes(PACK,'little') for x in b.masses),'little')
    nn=len(a.masses)+len(b.masses)-1
    raw=(aa*bb).to_bytes(nn*PACK,'little');co=[];check=0
    for i in range(nn):
        v=int.from_bytes(raw[i*PACK:(i+1)*PACK],'little');check+=v
        assert 0<=v<=(SCALE*SCALE)
        co.append(v>>BITS)
    assert check==a.total()*b.total()
    off=a.offset+b.offset
    if cap is not None:
        l=max(0,-cap-off);u=min(len(co),cap-off+1)
        co=co[l:u];off+=l
    out=Law(off,co).trimmed();assert out.total()<=SCALE
    return out

def power(a,n,cap=None):
    ans=Law(0,[SCALE]);p=a
    while n:
        if n&1:ans=mul(ans,p,cap)
        n>>=1
        if n:p=mul(p,p,cap)
    return ans

class Score:
    def __init__(self,law,r):
        self.law=law;self.r=F(r);self.logr=I(r).log();self.total=law.total()
        self.prefix=[0]
        for w in law.masses:self.prefix.append(self.prefix[-1]+w)
        j=law.offset
        v=(I(r)**(-j)) if j<=0 else (1/(I(r)**j))
        down=v.floor_scaled(FB);up=v.ceil_scaled(FB)
        low=[];high=[];num=r.numerator;den=r.denominator
        for w in law.masses:
            low.append(w*down);high.append(w*up)
            down=down*den//num;up=-(-(up*den)//num)
        self.sd=[0]*(len(low)+1);self.su=self.sd.copy()
        for i in range(len(low)-1,-1,-1):
            self.sd[i]=self.sd[i+1]+low[i];self.su[i]=self.su[i+1]+high[i]
    def evaluate(self,epsilon,upper=True):
        z=I(epsilon)/self.logr
        l=z.lower().__floor__();u=z.upper().__floor__()
        assert l==u,('threshold falls exactly on uncertain lattice edge',epsilon,l,u)
        i=min(len(self.law.masses),max(0,l-self.law.offset+1));ex=I(epsilon).exp()
        den=SCALE*FS*FS
        if upper:
            num=(SCALE-self.prefix[i])*FS*FS-ex.floor_scaled(FB)*self.sd[i]
        else:
            num=(self.total-self.prefix[i])*FS*FS-ex.ceil_scaled(FB)*self.su[i]
        return max(F(0),min(F(1),F(num,den)))

def inverse(scores,delta,upper=True,scale=1000,maxeps=100):
    lo=0;hi=maxeps*scale
    def value(x):return max(s.evaluate(F(x,scale),upper) for s in scores)
    assert value(hi)<delta
    if value(0)<=delta:
        return F(0),[s.evaluate(0,upper) for s in scores]
    while hi-lo>1:
        m=(lo+hi)//2
        if value(m)<=delta:hi=m
        else:lo=m
    ep=F(hi if upper else lo,scale)
    ds=[s.evaluate(ep,upper) for s in scores]
    assert (max(ds)<delta) if upper else (max(ds)>delta)
    return ep,ds

def result_row(e,lp,lq,up,uq,r,delta,scale=1000):
    el,dl=inverse([Score(lp,r),Score(lq,r)],delta,False,scale)
    eu,du=inverse([Score(up,r),Score(uq,r)],delta,True,scale)
    return {'epochs':e,'epsilon_lower_open':jd(el),'epsilon_upper_closed':jd(eu),
      'epsilon_lower_decimal':decimal_down(el,3),'epsilon_upper_decimal':decimal_up(eu,3),
      'delta_at_lower':[jd(x) for x in dl],'delta_at_upper':[jd(x) for x in du],
      'delta_at_lower_decimal':[decimal_down(x,15) for x in dl],
      'delta_at_upper_decimal':[decimal_up(x,15) for x in du],
      'upper_missing_P':jd(F(SCALE-up.total(),SCALE)),
      'upper_missing_Q':jd(F(SCALE-uq.total(),SCALE))}
