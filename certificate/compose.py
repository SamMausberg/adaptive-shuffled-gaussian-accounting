"""Build a rational dominating pair and certify its adaptive product accountant.

The exact pair is the slope measure of the upper envelope of testing inequalities.
Dyadic convolution arrays are lower submeasures, not approximations silently
renormalized to probability one. Every omitted atom is charged at infinite loss.
"""
from fractions import Fraction as F
from pathlib import Path
from intervals import I,D,ceildiv
from build_profile import gauss_profile
import json,sys,time,hashlib
from bisect import bisect_left
ROOT=Path(__file__).resolve().parent
MASS_BITS=56
S=1<<MASS_BITS
PACK_BITS=128
PACK_BYTES=PACK_BITS//8


def fj(x):return [str(x.numerator),str(x.denominator)]

def make_pair(sigma):
    spec=json.loads((ROOT/f'profile_sigma{sigma}.json').read_text())
    r=F(*map(int,spec['ratio']));den=int(spec['denominator']);J=spec['J']
    by_slope={F(0):(F(0),None)}
    def add(m,b,j):
        if m not in by_slope or b>by_slope[m][0]:by_slope[m]=(b,j)
    for row in spec['rows']:
        j=row['j'];k=r**j
        add(-k,1-F(int(row['forward_numerator']),den),j)
        add(-1/k,(1-F(int(row['reverse_numerator']),den))/k,-j)
    hull=[]
    for m,(b,j) in sorted(by_slope.items()):
        start=None
        while hull:
            pm,pb,pj,px=hull[-1]
            start=(pb-b)/(m-pm)
            if px is not None and start<=px:hull.pop()
            else:break
        if not hull:start=None
        hull.append((m,b,j,start))
    p=[F(0) for _ in range(2*J+1)];q=p.copy();segments=[]
    f0=max(b for m,(b,j) in by_slope.items())
    assert 0<=f0<=1
    p_only=1-f0;q_only=F(0)
    for i,(m,b,j,start) in enumerate(hull):
        l=F(0) if start is None else max(F(0),start)
        stop=F(1) if i+1==len(hull) else hull[i+1][3]
        u=min(F(1),stop)
        if u<=l:continue
        # Convex envelope validation at both endpoints against every input line.
        for x in (l,u):
            fx=m*x+b
            assert 0<=fx<=1-x

        mass=u-l
        if j is None:
            assert m==0 and b==0;q_only+=mass
        else:
            assert m==-(r**j)
            q[j+J]+=mass;p[j+J]+=-m*mass
        segments.append({'left':fj(l),'right':fj(u),'slope':fj(m),'intercept':fj(b),'loss_index':j})
    # Check every input line at a global minimizer of f(x)-line(x). Since
    # envelope slopes are increasing, the minimizer is found by binary search.
    slopes=[F(*map(int,seg['slope'])) for seg in segments]
    for mm,(bb,jj) in by_slope.items():
        ii=bisect_left(slopes,mm)
        if ii==len(segments):ii-=1;x=F(1)
        else:x=F(*map(int,segments[ii]['left']))
        seg=segments[ii];fm=F(*map(int,seg['slope']));fb=F(*map(int,seg['intercept']))
        assert fm*x+fb>=mm*x+bb
    assert sum(q)+q_only==1 and sum(p)+p_only==1
    assert all(a>=0 for a in p+q)
    for j,(a,b) in enumerate(zip(p,q)):
        assert a==r**(j-J)*b
    exact={'sigma':sigma,'T':spec['T'],'ratio':spec['ratio'],'J':J,
           'P_only':fj(p_only),'Q_only':fj(q_only),'segments':segments,
           'finite_atoms':[{'loss_index':j-J,'P':fj(a),'Q':fj(b)} for j,(a,b) in enumerate(zip(p,q)) if b]}
    (ROOT/f'dominating_pair_sigma{sigma}.json').write_text(json.dumps(exact,indent=2))
    # Independent lower submeasures retain their exact loss locations. Their
    # deficits, including genuine singular mass, are paid at +infinity later.
    pp=[a.numerator*S//a.denominator for a in p]
    qq=[a.numerator*S//a.denominator for a in q]
    assert sum(pp)<=S and sum(qq)<=S
    print('pair',sigma,'segments',len(segments),'singular fractions',fj(p_only),fj(q_only),flush=True)
    return r,J,pp,qq,exact


def convolution_lower(a,b):
    assert all(0<=x<=S for x in a+b) and sum(a)<=S and sum(b)<=S
    # Every exact coefficient is <= S^2 < 2^128, so the packed integer product
    # has no carry between coefficients. Python integers cannot overflow.
    aa=int.from_bytes(b''.join(x.to_bytes(PACK_BYTES,'little') for x in a),'little')
    bb=int.from_bytes(b''.join(x.to_bytes(PACK_BYTES,'little') for x in b),'little')
    nn=len(a)+len(b)-1
    raw=(aa*bb).to_bytes(nn*PACK_BYTES,'little')
    c=[];pre_sum=0
    for i in range(nn):
        exact=int.from_bytes(raw[i*PACK_BYTES:(i+1)*PACK_BYTES],'little')
        assert exact<=S*S
        pre_sum+=exact;c.append(exact>>MASS_BITS)
    assert pre_sum==sum(a)*sum(b) # also checks packing and absence of carry
    assert sum(c)<=S
    return c


def profile_upper(coeff,jmin,r,epsilon):
    ep=I(epsilon).exp().lo
    init=F(ep,1)*(r**(-jmin))
    factor=init.numerator//init.denominator
    nr,dr=r.numerator,r.denominator
    good=0
    for mass in coeff:
        good+=mass*min(D,factor)
        factor=factor*dr//nr
    assert 0<=good<=S*D
    return F(S*D-good,S*D)


def ceil_decimal(x,places=12):
    scale=10**places;v=ceildiv(x.numerator*scale,x.denominator)
    return f'{v//scale}.{v%scale:0{places}d}'


def deterministic_bracket(sigma,epochs,delta):
    # Integer bisection gives rational endpoints 10^-5 apart; each decision
    # uses a certified Gaussian inclusion interval, never a float.
    scale=100000;lo=0;hi=100*scale
    while hi-lo>1:
        mid=(lo+hi)//2;v=gauss_profile(I(F(mid,scale)),sigma,epochs)
        if v.upper()<delta:hi=mid
        elif v.lower()>delta:lo=mid
        else:raise ArithmeticError('insufficient Gaussian enclosure precision')
    assert gauss_profile(I(F(lo,scale)),sigma,epochs).lower()>delta
    assert gauss_profile(I(F(hi,scale)),sigma,epochs).upper()<delta
    return F(lo,scale),F(hi,scale)


def run(sigma):
    begin=time.time();r,J,p,q,exact=make_pair(sigma)
    delta=F(1,100000000);curp=[S];curq=[S]
    result=[];epochs_to_record={1,2,3,5,10,20}
    for e in range(1,21):
        curp=convolution_lower(curp,p);curq=convolution_lower(curq,q)
        assert len(curp)==2*e*J+1
        if e not in epochs_to_record:continue
        rev=curq[::-1];jmin=-e*J
        # Certify a cent-grid inverse upper bound. The preceding failing grid
        # point is not a lower bound on the original experiment.
        lo=0;hi=5000
        while hi-lo>1:
            mid=(lo+hi)//2;ep=F(mid,100)
            fu=profile_upper(curp,jmin,r,ep);ru=profile_upper(rev,jmin,r,ep)
            if max(fu,ru)<=delta:hi=mid
            else:lo=mid
        ep=F(hi,100)
        fu=profile_upper(curp,jmin,r,ep);ru=profile_upper(rev,jmin,r,ep)
        assert max(fu,ru)<delta
        dl,du=deterministic_bracket(sigma,e,delta)
        lower_missing_p=F(S-sum(curp),S);lower_missing_q=F(S-sum(curq),S)
        row={'epochs':e,'epsilon_upper':fj(ep),'epsilon_upper_decimal':ceil_decimal(ep,2),
             'forward_delta_upper':fj(fu),'reverse_delta_upper':fj(ru),
             'forward_delta_upper_decimal':ceil_decimal(fu,15),'reverse_delta_upper_decimal':ceil_decimal(ru,15),
             'deterministic_epsilon_lower':fj(dl),'deterministic_epsilon_upper':fj(du),
             'deterministic_epsilon_lower_decimal':ceil_decimal(dl,5),'deterministic_epsilon_upper_decimal':ceil_decimal(du,5),
             'lower_submeasure_P_missing':fj(lower_missing_p),'lower_submeasure_Q_missing':fj(lower_missing_q)}
        result.append(row)
        # Hash and save the actual integer convolution arrays for an optional
        # fast endpoint-only check; recomputation remains the primary verifier.
        pack={'sigma':sigma,'epochs':e,'J':J,'mass_bits':MASS_BITS,'P':list(map(str,curp)),'Q':list(map(str,curq))}
        name=ROOT/f'convolution_sigma{sigma}_epochs{e}.json'
        name.write_text(json.dumps(pack,separators=(',',':')))
        row['convolution_sha256']=hashlib.sha256(name.read_bytes()).hexdigest()
        print('ACCEPT',sigma,e,ceil_decimal(ep,2),'delta+',ceil_decimal(fu,15),'delta-',ceil_decimal(ru,15),'det',ceil_decimal(dl,5),ceil_decimal(du,5),'elapsed',round(time.time()-begin,1),flush=True)
    obj={'sigma':sigma,'T':1000,'delta':fj(delta),'scope':'All unit-ball adaptive queries; heterogeneous records; every batch size; fresh independent permutation in each epoch; ideal Gaussian releases.','ratio':fj(r),'likelihood_J':J,'mass_bits':MASS_BITS,'rows':result}
    (ROOT/f'results_sigma{sigma}.json').write_text(json.dumps(obj,indent=2))
    lines=['epochs clone deterministic']
    for row in result:lines.append(f"{row['epochs']} {row['epsilon_upper_decimal']} {row['deterministic_epsilon_upper_decimal']}")
    (ROOT/f'epochs_sigma{sigma}.dat').write_text('\n'.join(lines)+'\n')
    print('COMPLETE',sigma,'seconds',round(time.time()-begin,2),flush=True)

if __name__=='__main__':
    for sigma in map(int,sys.argv[1:] or ['1','2']):run(sigma)
