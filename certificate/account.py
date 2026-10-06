#!/usr/bin/env python3
"""Use the certified T=1000 profiles, with explicit sampler selection.

Examples:
  python account.py --sampler shuffle --sigma 1 --epochs 5 --delta 1e-8
  python account.py --sampler poisson --sigma 2 --epochs 5 --delta 1e-8
Run run_all.py to reconstruct the profile certificates rather than just recomposing
the supplied certified inputs. Queries may adapt within and between epochs.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,json,sys,hashlib
from mpinterval import I,jd,decimal_up
ROOT=Path(__file__).resolve().parent

def verify_manifest(names):
    p=ROOT/'manifest.json'
    if not p.exists():return
    expected=json.loads(p.read_text())['sha256']
    for name in names:
        if name in expected:
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected[name],f'Certificate file changed: {name}'

def clone_laws(sigma):
    from compose import S
    name=f'dominating_pair_sigma{sigma}.json';verify_manifest([name]);x=json.loads((ROOT/name).read_text())
    r=F(*map(int,x['ratio']));J=x['J'];p=[0]*(2*J+1);q=p.copy();pp=F(0);qq=F(0)
    for atom in x['finite_atoms']:
        j=atom['loss_index'];a=F(*map(int,atom['P']));b=F(*map(int,atom['Q']))
        assert a==r**j*b and min(a,b)>=0
        pp+=a;qq+=b;p[j+J]=int(a*S);q[j+J]=int(b*S)
    assert pp+F(*map(int,x['P_only']))==1 and qq+F(*map(int,x['Q_only']))==1
    return r,J,p,q

def run(args):
    if args.T!=1000:raise ValueError('The supplied certified profiles require T=1000. Regenerate profiles for a different T.')
    if not 1<=args.epochs<=100:raise ValueError('Supported epoch count: 1 through 100.')
    delta=F(args.delta)
    if not F(1,10**12)<=delta<F(1,2):raise ValueError('This interface supports 1e-12 <= delta < 1/2.')
    if args.sampler=='shuffle':
        from compose import convolution_lower,profile_upper,S
        r,J,p,q=clone_laws(args.sigma)
        def power(a,n):
            out=[S]
            while n:
                if n&1:out=convolution_lower(out,a)
                n>>=1
                if n:a=convolution_lower(a,a)
            return out
        a=power(p,args.epochs);b=power(q,args.epochs)[::-1];offset=-J*args.epochs
        def eval_at(ep):
            f=profile_upper(a,offset,r,ep);v=profile_upper(b,offset,r,ep)
            # Deterministic batching is also a valid fallback for shuffling.
            mu=I(args.epochs).sqrt()/args.sigma
            g=(-I(ep)/mu+mu/2).cdf()-I(ep).exp()*(-I(ep)/mu-mu/2).cdf()
            return min(f,g.upper()),min(v,g.upper())
    else:
        from lattice import Law,power,Score
        name=f'poisson_input_sigma{args.sigma}.json';verify_manifest([name]);x=json.loads((ROOT/name).read_text())
        r=F(*map(int,x['ratio']));laws=[Law.fromobj(y) for y in x['laws']]
        scores=[Score(power(law,1000*args.epochs,60000),r) for law in laws]
        def eval_at(ep):return tuple(s.evaluate(ep,True) for s in scores)
    if args.epsilon is not None:
        ep=F(args.epsilon)
        if not 0<=ep<=200:raise ValueError('Require 0 <= epsilon <= 200.')
    else:
        lo=0;hi=20000
        assert max(eval_at(F(hi,100)))<delta,'No certified cent-grid value within the supported epsilon range.'
        if max(eval_at(0))<=delta:hi=0
        else:
            while hi-lo>1:
                mid=(lo+hi)//2
                if max(eval_at(F(mid,100)))<=delta:hi=mid
                else:lo=mid
        ep=F(hi,100)
    f,v=eval_at(ep)
    answer={'sampler':args.sampler,'T':args.T,'sigma':args.sigma,'epochs':args.epochs,
      'target_delta':jd(delta),'epsilon':jd(ep),'epsilon_decimal':decimal_up(ep,3),
      'forward_delta_upper':jd(f),'reverse_delta_upper':jd(v),
      'forward_delta_upper_decimal':decimal_up(f,15),'reverse_delta_upper_decimal':decimal_up(v,15),
      'certified':max(f,v)<=delta,
      'scope':'Zero-out adjacency and ideal Gaussian transcript; fresh independent reshuffling.' if args.sampler=='shuffle' else 'Independent Poisson inclusions q=1/1000; matched sum noise; 1000*epochs steps.'}
    print(json.dumps(answer,indent=2))
    return 0 if answer['certified'] else 2
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--sampler',choices=['shuffle','poisson'],default='shuffle');p.add_argument('--sigma',type=int,choices=[1,2],required=True)
    p.add_argument('--T',type=int,default=1000);p.add_argument('--epochs',type=int,required=True)
    p.add_argument('--delta',default='1e-8');p.add_argument('--epsilon')
    try:sys.exit(run(p.parse_args()))
    except (ValueError,AssertionError,ArithmeticError) as e:
        print(f'Certificate not produced: {e}',file=sys.stderr);sys.exit(1)
