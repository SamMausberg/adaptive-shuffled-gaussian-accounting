"""Dyadic inclusion intervals with elementary, rigorously bounded functions.
Only Python integer arithmetic is used. All endpoints are multiples of 2^-BITS.
"""
from fractions import Fraction as F
from math import isqrt
from functools import lru_cache
BITS=1024
D=1<<BITS

def ceildiv(a,b):
    assert b>0
    return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,x=0,hi=None,_raw=False):
        if _raw:
            self.lo=int(x);self.hi=int(hi)
        elif isinstance(x,I):self.lo=x.lo;self.hi=x.hi
        else:
            v=F(x);self.lo=v.numerator*D//v.denominator
            self.hi=ceildiv(v.numerator*D,v.denominator)
        assert self.lo<=self.hi
    @classmethod
    def raw(cls,l,u):return cls(l,u,_raw=True)
    def __add__(self,o):
        o=I(o);return I.raw(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I.raw(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        if isinstance(o,(int,F)):
            v=F(o);n,d=v.numerator,v.denominator
            if n>=0:return I.raw(self.lo*n//d,ceildiv(self.hi*n,d))
            return I.raw(self.hi*n//d,ceildiv(self.lo*n,d))
        o=I(o);ls=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I.raw(min(ls)//D,ceildiv(max(ls),D))
    __rmul__=__mul__
    def __truediv__(self,o):
        if isinstance(o,(int,F)):
            return self*(1/F(o))
        o=I(o)
        if o.hi<0:return (-self)/(-o)
        assert o.lo>0
        if self.lo>=0:return I.raw(self.lo*D//o.hi,ceildiv(self.hi*D,o.lo))
        if self.hi<=0:return I.raw(self.lo*D//o.lo,ceildiv(self.hi*D,o.hi))
        return I.raw(self.lo*D//o.lo,ceildiv(self.hi*D,o.lo))
    def __rtruediv__(self,o):return I(o)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=I(1);x=self
        while n:
            if n&1:out=out*x
            n>>=1
            if n:x=x*x
        return out
    def sqrt(self):
        assert self.lo>=0
        return I.raw(isqrt(self.lo*D),isqrt(self.hi*D)+1)
    def exp(self):
        return I.raw(exp_point(self.lo)[0],exp_point(self.hi)[1])
    def cdf(self):
        return I.raw(cdf_point(self.lo)[0],cdf_point(self.hi)[1])
    def upper(self):return F(self.hi,D)
    def lower(self):return F(self.lo,D)
    def width(self):return F(self.hi-self.lo,D)
    def __repr__(self):return f'I({float(self.lower())}, {float(self.upper())})'

@lru_cache(maxsize=40000)
def exp_point(x):
    if x<0:
        lo,hi=exp_point(-x)
        return D*D//hi,ceildiv(D*D,lo)
    # x/D reduced to at most 1/2, with outward rounding.
    q=max(0,(x*2).bit_length()-BITS)
    y=I.raw(x//(1<<q),ceildiv(x,1<<q))
    assert y.hi<=D
    term=I(1);s=I(1)
    N=180
    for j in range(1,N+1):
        term=term*y/j;s=s+term
    rem=term*y/(N+1)/(I(1)-y/(N+2))
    s=I.raw(s.lo,s.hi+rem.hi)
    for _ in range(q):s=s*s
    return s.lo,s.hi

def log_fraction(x):
    x=F(x);assert F(1,2)<=x<=2
    y=I((x-1)/(x+1));y2=y*y;term=y;s=I(0)
    N=256
    for j in range(N):
        s=s+term/(2*j+1);term=term*y2
    # Absolute tail bounded by |y|^(2N+1)/((2N+1)(1-y^2)).
    ay=I.raw(min(abs(y.lo),abs(y.hi)),max(abs(y.lo),abs(y.hi)))
    tail=ay**(2*N+1)/(2*N+1)/(1-ay*ay)
    return I.raw(2*s.lo-2*tail.hi,2*s.hi+2*tail.hi)

@lru_cache(None)
def pi():
    def atan(q):
        x=I(F(1,q));xx=x*x;term=x;s=I(0)
        N=256
        for j in range(N):
            s=s+(term/(2*j+1) if j%2==0 else -term/(2*j+1));term=term*xx
        nxt=term/(2*N+1)
        return I.raw(s.lo-nxt.hi,s.hi+nxt.hi)
    return 16*atan(5)-4*atan(239)

@lru_cache(None)
def normalizer():return 1/(2*pi()).sqrt()

@lru_cache(maxsize=10000)
def cdf_point(x):
    if x<0:
        lo,hi=cdf_point(-x);return D-hi,D-lo
    if x==0:return D//2,D//2
    t=I.raw(x,x)
    if x>=12*D:
        # Mills bound gives a cheap valid enclosure in a negligible tail.
        u=(normalizer()*(-t*t/2).exp()/t).hi
        return max(0,D-u),D
    # Integrate consecutive Taylor bounds for exp(-s^2/2).
    term=t;s=term;N=768
    for j in range(N):
        term=term*(-t*t)*F(2*j+1,2*(j+1)*(2*j+3))
        s=s+term
    nxt=term*(-t*t)*F(2*N+1,2*(N+1)*(2*N+3))
    # The integral lies between these consecutive partial sums, even when
    # early terms grow. This is Taylor's signed integral remainder.
    sp=s+nxt
    a=I.raw(min(s.lo,sp.lo),max(s.hi,sp.hi))
    ans=I(F(1,2))+a*normalizer()
    return max(0,ans.lo),min(D,ans.hi)

if __name__=='__main__':
    print('pi',pi(),'log(51/50)',log_fraction(F(51,50)))
    for x in [0,1,5,8,11,12]:print('Phi',x,I(x).cdf(),'width',float(I(x).cdf().width()))
