"""Certified reverse-profile refinement by a bounded lognormal Laplace transform.

Monotone Gaussian-bin bounds include both infinite tails. A proposed h and s
only select a valid inequality; no proposed numerical integral is trusted.
"""
from fractions import Fraction as F
from intervals import I,D,BITS,ceildiv
from pathlib import Path
import json,sys,time
ROOT=Path(__file__).resolve().parent
OUT_BITS=100
OUT_D=1<<OUT_BITS


def bounded_negative_exp(x):
    assert x.hi<=0
    if x.hi<=-BITS*D:
        # e>2 implies exp(-BITS)<2^-BITS.
        return I.raw(0,1)
    return x.exp()


def refine(sigma):
    start=time.time()
    path=ROOT/f'profile_sigma{sigma}.json'
    prof=json.loads(path.read_text())
    assert not prof.get('laplace_refinement',False)
    (ROOT/f'moment_profile_sigma{sigma}.json').write_text(json.dumps(prof,indent=2))
    prop=json.loads((ROOT/f'laplace_witnesses_sigma{sigma}.json').read_text())
    assert prop['sigma']==sigma
    ws=prop['replacement_witnesses'];assert len(ws)==prof['J']+1
    ss=sorted({F(w['snum'],w['sden']) for w in ws if w is not None})
    zs=[F(j,32) for j in range(-256,257)]
    cdfs=[I(z).cdf() for z in zs]
    masses=[cdfs[j+1]-cdfs[j] for j in range(len(zs)-1)]
    assert all(m.lo>0 for m in masses)
    xs=[I(z/sigma-F(1,2*sigma*sigma)).exp() for z in zs]
    lap={};laudit=[]
    for s in ss:
        value=cdfs[0]+(1-cdfs[-1])*bounded_negative_exp(-s*xs[-1])
        for prob,x in zip(masses,xs[:-1]):
            value=value+prob*bounded_negative_exp(-s*x)
        assert 0<value.lo<=value.hi<D
        lap[s]=value
        laudit.append({'s':[str(s.numerator),str(s.denominator)],'upper_numerator':str(ceildiv(value.hi,1<<(BITS-OUT_BITS))),'denominator':str(OUT_D)})
        print('Laplace',sigma,str(s),'elapsed',round(time.time()-start,1),flush=True)
    recs=[];gamma_cache={}
    for row,w in zip(prof['rows'],ws):
        if w is None:continue
        assert w['kind']=='laplace' and w['hnum']>0
        j=row['j'];k=I(F(51,50)**j);s=F(w['snum'],w['sden'])
        h=F(w['hnum'],20)
        if h not in gamma_cache:
            p=I(-h).exp()
            gamma=p*I(-sigma*h+F(1,2*sigma)).cdf()-I(-sigma*h-F(1,2*sigma)).cdf()
            assert 0<gamma.lo and 0<p.lo<=p.hi<D
            gamma_cache[h]=(p,gamma)
        p,gamma=gamma_cache[h]
        theta=s/k
        base=1-p+p*theta.exp()*lap[s]
        assert base.lo>0
        value=base**prof['T']/(I(1).exp()*theta*prof['T']*p)+(1+k)*(prof['T']-1)*gamma
        up=min(OUT_D,ceildiv(value.hi,1<<(BITS-OUT_BITS)))
        previous=int(row['reverse_numerator'])
        row['reverse_numerator']=str(min(previous,up))
        recs.append({'j':j,'h':[str(h.numerator),str(h.denominator)],'s':[str(s.numerator),str(s.denominator)],'new_upper_numerator':str(up),'accepted':up<previous})
    prof['laplace_refinement']=True
    path.write_text(json.dumps(prof,indent=2))
    (ROOT/f'laplace_audit_sigma{sigma}.json').write_text(json.dumps({'bin_left':'-8','bin_right':'8','bin_width':'1/32','interval_bits':BITS,'denominator':str(OUT_D),'Laplace_bounds':laudit,'profile_refinements':recs},indent=2))
    print('REFINED',sigma,'accepted',sum(r['accepted'] for r in recs),'seconds',round(time.time()-start,2),flush=True)

if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):refine(s)
