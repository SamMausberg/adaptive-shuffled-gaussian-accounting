"""Algebraic sanity checks complementary to the inclusion-interval proof."""
from fractions import Fraction as F
from intervals import I,D,log_fraction
from compose import convolution_lower,profile_upper,S
from random import Random

def run():
    for x in [F(-7,3),F(-1,5),F(0),F(2,7),F(13,4)]:
        for y in [F(-9,5),F(1,3),F(8,7)]:
            for value,truth in [(I(x)+I(y),x+y),(I(x)-I(y),x-y),(I(x)*I(y),x*y),(I(x)/I(y),x/y)]:
                assert value.lower()<=truth<=value.upper()
    for x in [F(0),F(1,5),F(1),F(3)]:
        # An independent exact-rational Taylor sum and positive tail bound.
        term=F(1);total=term
        for j in range(1,241):term=term*x/j;total+=term
        rem=term*x/241/(1-x/242)
        got=I(x).exp()
        assert got.lower()<=total and total+rem<=got.upper()
    lr=log_fraction(F(51,50));er=lr.exp()
    assert er.lower()<=F(51,50)<=er.upper()
    rng=Random(72109)
    for _ in range(20):
        aa=[rng.randrange(1000) for _ in range(9)]
        bb=[rng.randrange(1000) for _ in range(7)]
        aa=[x*S//(2*sum(aa)) for x in aa]
        bb=[x*S//(2*sum(bb)) for x in bb]
        exact=[sum(aa[i]*bb[j] for i in range(len(aa)) for j in range(len(bb)) if i+j==k)//S for k in range(len(aa)+len(bb)-1)]
        assert convolution_lower(aa,bb)==exact
    coeff=[S//5,S//3,S//7]
    exact=1-sum(F(v,S)*min(F(1),F(51,50)**(-j)) for j,v in zip(range(-1,2),coeff))
    got=profile_upper(coeff,-1,F(51,50),F(0))
    assert got>=exact and got-exact<F(1,10**100)
    print('Algebraic self-tests passed.')

if __name__=='__main__':run()
