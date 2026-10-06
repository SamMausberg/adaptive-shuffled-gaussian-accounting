"""Exact/MPFR preparation for convex candidate-sum enclosures."""
from mpinterval import I,F,jd,version
from pathlib import Path
from collections import defaultdict
import json,sys
ROOT=Path(__file__).resolve().parent
XB=30; PB=72

def prepare(sigma, M=None, bins=50, grid_den=400):
    # bins per unit standard-normal input: default width .02.
    M=M or (64 if sigma==1 else 160)
    weights=defaultdict(int)
    prevz=F(-10);prevp=I(prevz).cdf();prevx=(I(prevz)/sigma-F(1,2*sigma*sigma)).exp()
    weights[0]+=prevp.floor_scaled(PB)
    for jj in range(-10*bins,10*bins):
        z0=F(jj,bins);z1=F(jj+1,bins)
        c1=I(z1).cdf();px=c1-prevp
        x1=(I(z1)/sigma-F(1,2*sigma*sigma)).exp()
        lower=prevx.floor_scaled(XB);upper=x1.ceil_scaled(XB)
        lo=F(lower,1<<XB);hi=F(upper,1<<XB)
        mm=(I(z1)-F(1,sigma)).cdf()-(I(z0)-F(1,sigma)).cdf()
        wl=(hi*px-mm)/(hi-lo);wh=(mm-lo*px)/(hi-lo)
        assert wl.lower()>0 and wh.lower()>0
        weights[lower]+=max(0,wl.floor_scaled(PB));weights[upper]+=max(0,wh.floor_scaled(PB))
        prevp=c1;prevx=x1
    cap=prevx.floor_scaled(XB);weights[cap]+=(1-prevp).floor_scaled(PB)
    total=sum(weights.values());assert total<=(1<<PB)
    miss=(1<<PB)-total
    fwd=dict(weights);rev=dict(weights)
    largest=max(weights);fwd[largest]=fwd.get(largest,0)+miss;rev[0]+=miss
    assert sum(fwd.values())==sum(rev.values())==(1<<PB)
    tau=(I(-10)-F(1,sigma)).cdf()+(I(F(1,sigma))-10).cdf()-F(cap,1<<XB)*I(-10).cdf()
    assert tau.lower()>0
    def grid(maximum):
        # Exact dyadic nodes with geometrically increasing spacing. Spacing is
        # an accuracy choice only: the chord enclosure holds on any such grid.
        arr=[0,1];step=1
        while arr[-1]<maximum:
            step=max(1,arr[-1]//grid_den)
            arr.append(min(maximum,arr[-1]+step))
        return arr
    gf=grid(M*largest);gr=grid(M*(1<<XB))
    k=I(1);r=I(F(51,50));evals=[]
    for j in range(556):
        if j:k=k*r
        evals.append([[int((k*m).floor_scaled(XB)),int((I(m)/k).ceil_scaled(XB))] for m in range(1,M+1)])
    out={'sigma':sigma,'T':1000,'M':M,'XB':XB,'PB':PB,'bins_per_unit':bins,'grid_den':grid_den,
         'kernel_forward':[[x,str(p)] for x,p in sorted(fwd.items()) if p],
         'kernel_reverse':[[x,str(p)] for x,p in sorted(rev.items()) if p],
         'grid_forward':gf,'grid_reverse':gr,'thresholds':evals,'tau_upper':jd(tau.upper()),'MPFR':version()}
    path=ROOT/f'candidate_inputs_sigma{sigma}.json';path.write_text(json.dumps(out,separators=(',',':')))
    # Plain text is separately checked against JSON by the driver.
    lines=[f'{M} {XB} {PB} {len(gf)} {len(gr)} {len(fwd)} {len(rev)}']
    # The text file lists the same positive-mass atoms as the JSON.
    ff=out['kernel_forward'];rr=out['kernel_reverse']
    lines=[f'{M} {XB} {PB} {len(gf)} {len(gr)} {len(ff)} {len(rr)}']
    lines+=[' '.join(map(str,gf)),' '.join(map(str,gr))]
    lines += [f'{x} {p}' for x,p in ff+rr]
    for j in range(556):lines.append(' '.join(str(v) for pair in evals[j] for v in pair))
    (ROOT/f'candidate_inputs_sigma{sigma}.txt').write_text('\n'.join(lines)+'\n')
    print('PREPARED',sigma,'M',M,'grids',len(gf),len(gr),'atoms',len(ff),'tau',tau,'missing mass',float(F(miss,1<<PB)),flush=True)
def check_plaintext(sigma):
    z=json.loads((ROOT/f'candidate_inputs_sigma{sigma}.json').read_text())
    ff=z['kernel_forward'];rr=z['kernel_reverse'];gf=z['grid_forward'];gr=z['grid_reverse']
    lines=[f"{z['M']} {z['XB']} {z['PB']} {len(gf)} {len(gr)} {len(ff)} {len(rr)}"]
    lines+=[' '.join(map(str,gf)),' '.join(map(str,gr))]
    lines+=[f'{x} {p}' for x,p in ff+rr]
    for vals in z['thresholds']:lines.append(' '.join(str(v) for pair in vals for v in pair))
    assert (ROOT/f'candidate_inputs_sigma{sigma}.txt').read_text()=='\n'.join(lines)+'\n'

if __name__=='__main__':
    for s in map(int,sys.argv[1:] or ['1','2']):prepare(s)
