"""Directed MPFR intervals, exported as exact dyadic rational endpoints.

Requires the system GNU MPFR shared library (tested with 4.2.2).
Every primitive explicitly requests RNDD or RNDU. There is no nearest-rounding
transcendental call in a certificate path. The ctypes ABI uses the public MPFR
struct layout; a self-test is provided and refuses unexpected word sizes.
"""
import ctypes as C
import ctypes.util
from fractions import Fraction as F
from functools import lru_cache

PREC=256
DOWN=3
UP=2
assert C.sizeof(C.c_long)==8 and C.sizeof(C.c_void_p)==8
class MP(C.Structure):
    _fields_=[('prec',C.c_long),('sign',C.c_int),('exponent',C.c_long),('limbs',C.POINTER(C.c_ulong))]
lib=C.CDLL(C.util.find_library('mpfr') or 'libmpfr.so.6')
P=C.POINTER(MP)
def bind(name,args,res=C.c_int):
    fn=getattr(lib,'mpfr_'+name);fn.argtypes=args;fn.restype=res;return fn
init=bind('init2',[P,C.c_long],None);clear=bind('clear',[P],None)
setstr=bind('set_str',[P,C.c_char_p,C.c_int,C.c_int]);setmp=bind('set',[P,P,C.c_int])
getstr=bind('get_str',[C.c_void_p,C.POINTER(C.c_long),C.c_int,C.c_size_t,P,C.c_int],C.c_void_p)
free=bind('free_str',[C.c_void_p],None)
getd=bind('get_d',[P,C.c_int],C.c_double)
getversion=bind('get_version',[],C.c_char_p)
cmp=bind('cmp',[P,P]);cmpsi=bind('cmp_si',[P,C.c_long])
zero=bind('zero_p',[P]);finite=bind('number_p',[P])
BIN={n:bind(n,[P,P,P,C.c_int]) for n in ['add','sub','mul','div']}
UNI={n:bind(n,[P,P,C.c_int]) for n in ['neg','sqrt','exp','log','erfc']}
powui=bind('pow_ui',[P,P,C.c_ulong,C.c_int]);ldexp=bind('mul_2si',[P,P,C.c_long,C.c_int])
constpi=bind('const_pi',[P,C.c_int])

class Num:
    __slots__=('v',)
    def __init__(self,x=None,rnd=DOWN):
        self.v=MP();init(C.byref(self.v),PREC)
        if x is not None:
            if isinstance(x,Num):setmp(self.ptr,x.ptr,rnd)
            elif isinstance(x,(int,str)):assert setstr(self.ptr,str(x).encode(),10,rnd)==0
            else:raise TypeError(type(x))
    @property
    def ptr(self):return C.byref(self.v)
    def __del__(self):clear(C.byref(self.v))
    def rat(self):
        assert finite(self.ptr)
        if zero(self.ptr):return F(0)
        exponent=C.c_long();p=getstr(None,C.byref(exponent),2,0,self.ptr,DOWN)
        try:s=C.string_at(p).decode()
        finally:free(p)
        neg=s.startswith('-');digits=s[1:] if neg else s;n=int(digits,2)*(-1 if neg else 1);e=exponent.value-len(digits)
        return F(n<<e) if e>=0 else F(n,1<<(-e))
    def dbl(self,rnd=UP):return getd(self.ptr,rnd)

def op(n,a,b=None,r=DOWN):
    y=Num()
    if b is None:UNI[n](y.ptr,a.ptr,r)
    else:BIN[n](y.ptr,a.ptr,b.ptr,r)
    assert finite(y.ptr),n
    return y

def smallest(xs):return min(xs,key=lambda x:x.rat())
def largest(xs):return max(xs,key=lambda x:x.rat())

class I:
    __slots__=('a','b')
    def __init__(self,x=0):
        if isinstance(x,I):self.a=x.a;self.b=x.b;return
        if isinstance(x,Num):self.a=x;self.b=x;return
        f=F(x);na=Num(f.numerator,DOWN);nb=Num(f.numerator,UP);da=Num(f.denominator,DOWN);db=Num(f.denominator,UP)
        # Integers used by the experiments fit precision; support any larger
        # integer as well through conservative denominator choices.
        if f>=0:self.a=op('div',na,db,r=DOWN);self.b=op('div',nb,da,r=UP)
        else:self.a=op('div',na,da,r=DOWN);self.b=op('div',nb,db,r=UP)
    @classmethod
    def raw(cls,a,b):
        z=object.__new__(cls);z.a=a;z.b=b;assert cmp(a.ptr,b.ptr)<=0;return z
    @classmethod
    def between(cls,l,u):
        return cls.raw(I(l).a,I(u).b)
    def __add__(self,o):
        o=I(o);return I.raw(op('add',self.a,o.a,DOWN),op('add',self.b,o.b,UP))
    __radd__=__add__
    def __neg__(self):return I.raw(op('neg',self.b,r=DOWN),op('neg',self.a,r=UP))
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o)
        if cmpsi(self.a.ptr,0)>=0 and cmpsi(o.a.ptr,0)>=0:
            return I.raw(op('mul',self.a,o.a,DOWN),op('mul',self.b,o.b,UP))
        lo=[op('mul',x,y,DOWN) for x in (self.a,self.b) for y in (o.a,o.b)]
        hi=[op('mul',x,y,UP) for x in (self.a,self.b) for y in (o.a,o.b)]
        return I.raw(smallest(lo),largest(hi))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o);assert cmpsi(o.a.ptr,0)>0 or cmpsi(o.b.ptr,0)<0
        if cmpsi(o.b.ptr,0)<0:return (-self)/(-o)
        if cmpsi(self.a.ptr,0)>=0:return I.raw(op('div',self.a,o.b,DOWN),op('div',self.b,o.a,UP))
        if cmpsi(self.b.ptr,0)<=0:return I.raw(op('div',self.a,o.a,DOWN),op('div',self.b,o.b,UP))
        return I.raw(op('div',self.a,o.a,DOWN),op('div',self.b,o.a,UP))
    def __rtruediv__(self,o):return I(o)/self
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        if cmpsi(self.a.ptr,0)>=0:
            a=Num();b=Num();powui(a.ptr,self.a.ptr,n,DOWN);powui(b.ptr,self.b.ptr,n,UP);return I.raw(a,b)
        out=I(1);x=self
        while n:
            if n&1:out=out*x
            n>>=1
            if n:x=x*x
        return out
    def exp(self):return I.raw(op('exp',self.a,r=DOWN),op('exp',self.b,r=UP))
    def log(self):
        assert cmpsi(self.a.ptr,0)>0
        return I.raw(op('log',self.a,r=DOWN),op('log',self.b,r=UP))
    def sqrt(self):
        assert cmpsi(self.a.ptr,0)>=0
        return I.raw(op('sqrt',self.a,r=DOWN),op('sqrt',self.b,r=UP))
    def cdf(self):
        y=(-self)/sqrt2();return I.raw(op('erfc',y.b,r=DOWN),op('erfc',y.a,r=UP))/2
    def lower(self):return self.a.rat()
    def upper(self):return self.b.rat()
    def width(self):return self.upper()-self.lower()
    def floor_scaled(self,bits):
        r=self.lower();return (r.numerator<<bits)//r.denominator
    def ceil_scaled(self,bits):
        r=self.upper();return -((-(r.numerator<<bits))//r.denominator)
    def __repr__(self):return f'I({self.a.dbl(DOWN)}, {self.b.dbl(UP)})'

@lru_cache(None)
def sqrt2():return I(2).sqrt()
@lru_cache(None)
def pi():
    a=Num();b=Num();constpi(a.ptr,DOWN);constpi(b.ptr,UP);return I.raw(a,b)

def version():return getversion().decode()
def jd(x):
    x=F(x);return [str(x.numerator),str(x.denominator)]
def fromjd(x):return F(*map(int,x))
def decimal_up(x,n=12):
    x=F(x);k=-(-(x.numerator*10**n)//x.denominator)
    return f'{k//10**n}.{k%10**n:0{n}d}'
def decimal_down(x,n=12):
    x=F(x);k=x.numerator*10**n//x.denominator
    return f'{k//10**n}.{k%10**n:0{n}d}'

if __name__=='__main__':
    import sys,time
    print('MPFR',version(),'precision',PREC,'bits')
    assert I(3).lower()==3 and (I(-7)/3).lower()<=F(-7,3)<=(I(-7)/3).upper()
    assert I(2).sqrt().lower()**2<=2<=I(2).sqrt().upper()**2
    assert I(0).cdf().lower()==F(1,2)==I(0).cdf().upper()
    assert I(1).log().lower()==0==I(1).log().upper()
    from intervals import I as Old
    for x in [F(-12),F(-8),F(-1),F(0),F(1,7),F(5),F(11),F(12)]:
        for method in ['exp','cdf']:
            a=getattr(I(x),method)();b=getattr(Old(x),method)()
            assert max(a.lower(),b.lower())<=min(a.upper(),b.upper()),(x,method,a,b)
    t=time.time()
    for j in range(10000):v=I(F(j,1000)).cdf()
    print('SELFTEST OK; 10000 CDFs seconds',round(time.time()-t,3))
