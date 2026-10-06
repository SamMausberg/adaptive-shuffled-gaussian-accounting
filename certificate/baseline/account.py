"""Query the certified T=1000 profiles. Run run_all.py before first use."""
import argparse,json,sys
from contextlib import redirect_stdout
from fractions import Fraction as F
from pathlib import Path
from intervals import I
from build_profile import gauss_profile
from compose import make_pair,convolution_lower,profile_upper,S,fj,ceil_decimal


def lower_power(base,jmin,epochs):
    out=[S];omin=0;n=epochs
    while n:
        if n&1:out=convolution_lower(out,base);omin+=jmin
        n//=2
        if n:base=convolution_lower(base,base);jmin*=2
    return out,omin

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sigma',type=int,choices=(1,2),required=True)
    ap.add_argument('--epochs',type=int,required=True)
    ap.add_argument('--delta',default='1e-8')
    ap.add_argument('--epsilon',default=None,help='Test this rational epsilon instead of searching the cent grid.')
    args=ap.parse_args()
    if not 1<=args.epochs<=100:ap.error('This command supports 1 through 100 epochs.')
    delta=F(args.delta)
    if not 0<delta<1:ap.error('delta must lie strictly between 0 and 1.')
    with redirect_stdout(sys.stderr):
        r,J,p,q,_=make_pair(args.sigma)
    pp,jmin=lower_power(p,-J,args.epochs)
    qq,jq=lower_power(q[::-1],-J,args.epochs)
    assert jmin==jq
    def test(e):
        a=profile_upper(pp,jmin,r,e);b=profile_upper(qq,jmin,r,e)
        gaussian=gauss_profile(I(e),args.sigma,args.epochs).upper()
        return min(a,gaussian),min(b,gaussian),a,b,gaussian
    if args.epsilon is not None:
        ep=F(args.epsilon)
        if ep<0:ap.error('epsilon must be nonnegative.')
    else:
        lo=-1;hi=100
        while max(test(F(hi,100))[:2])>delta:hi*=2
        while hi-lo>1:
            mid=(lo+hi)//2
            if max(test(F(mid,100))[:2])<=delta:hi=mid
            else:lo=mid
        ep=F(hi,100)
    a,b,aa,bb,g=test(ep)
    print(json.dumps({'sigma':args.sigma,'T':1000,'epochs':args.epochs,
         'epsilon':fj(ep),'epsilon_decimal':ceil_decimal(ep,8),'delta_target':fj(delta),
         'forward_delta_upper':fj(a),'reverse_delta_upper':fj(b),
         'forward_decimal_upper':ceil_decimal(a,18),'reverse_decimal_upper':ceil_decimal(b,18),
         'passes':max(a,b)<=delta,
         'scope':'Zero-out adjacency; all adaptive unit-ball queries; arbitrary batch size; fresh independent permutation each epoch; ideal Gaussian releases.',
         'method':'Finite dominating-pair convolution with Gaussian fallback; every omitted mass is charged.'},indent=2))

if __name__=='__main__':main()
