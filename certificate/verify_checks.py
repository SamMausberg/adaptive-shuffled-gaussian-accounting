"""Independent arithmetic and boundary checks for the accepted constructions."""
from fractions import Fraction as F
from pathlib import Path
from random import Random
import json
from mpinterval import I,version
from lattice import Law,mul,Score,SCALE,FB
from refine_candidates import readvals
ROOT=Path(__file__).resolve().parent

def checks():
    from intervals import I as Rational
    for x in [F(-12),F(-8),F(-1),F(0),F(1,7),F(5),F(11),F(12)]:
        for name in ['cdf','exp']:
            a=getattr(I(x),name)();b=getattr(Rational(x),name)()
            assert max(a.lower(),b.lower())<=min(a.upper(),b.upper())
    rng=Random(61493)
    for _ in range(12):
        a=[rng.randrange(1<<40) for j in range(13)];b=[rng.randrange(1<<40) for j in range(17)]
        out=mul(Law(-6,a),Law(3,b));want=[0]*29
        for i,x in enumerate(a):
            for j,y in enumerate(b):want[i+j]+=x*y
        want=[v>>72 for v in want]
        ww=Law(-3,want).trimmed();assert out==ww
    r=F(51,50);a=Law(-3,[SCALE//16]*8);score=Score(a,r)
    for ep in [F(0),F(1,100),F(1,7),F(2)]:
        lo=I(0);hi=I(0);ex=I(ep).exp()
        # Direct finite expectation and complement, evaluated as intervals.
        d=I(0);good=I(0)
        for i,w in enumerate(a.masses):
            fac=ex/(r**(i+a.offset))
            d+=F(w,SCALE)*I.between(max(0,1-fac.upper()),max(0,1-fac.lower()))
            good+=F(w,SCALE)*I.between(min(1,fac.lower()),min(1,fac.upper()))
        assert score.evaluate(ep,False)<=d.upper()
        assert score.evaluate(ep,True)>=(1-good).lower()
    from candidate_prepare import check_plaintext
    for sigma in [1,2]:
        check_plaintext(sigma)
        inp,fs,rs=readvals(sigma);tau=F(*map(int,inp['tau_upper']));M=inp['M']
        for j in [0,1,10,50,100,200,400,555]:
            k=F(51,50)**j
            for m in sorted({1,2,8,32,M}):
                c=m*k-(m-1)
                ep=I(c).log()
                call=(-sigma*ep+F(1,2*sigma)).cdf()-c*(-sigma*ep-F(1,2*sigma)).cdf()
                assert fs[j][m-1]+tau>=call.lower()/m,('Jensen lower check',sigma,m,j)
        # Verify the exported values do not weaken any inherited grid bound.
        new=json.loads((ROOT/f'profile_sigma{sigma}.json').read_text())
        old=json.loads((ROOT/'baseline'/f'profile_sigma{sigma}.json').read_text())
        assert new['denominator']==old['denominator']
        assert all(int(n[f])<=int(o[f]) for n,o in zip(new['rows'],old['rows']) for f in ['forward_numerator','reverse_numerator'])
        # Poisson endpoint spreading preserves the call at the grid point 1.
        po=json.loads((ROOT/f'poisson_input_sigma{sigma}.json').read_text())
        pr=F(*map(int,po['ratio']));lp,lq=[Law.fromobj(x) for x in po['laws']]
        exact=F(1,1000)*(2*I(F(1,2*sigma)).cdf()-1)
        for law in [lp,lq]:
            v=Score(law,pr).evaluate(0,True)
            assert exact.lower()<=v<=exact.upper()+F(1,10**12)
    print('INDEPENDENT CHECKS PASSED; MPFR',version())
if __name__=='__main__':checks()
