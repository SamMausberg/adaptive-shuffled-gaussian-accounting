"""Collect only accepted rational endpoints; generate tables and plot data."""
from pathlib import Path
from fractions import Fraction as F
import json,hashlib
from mpinterval import jd,decimal_up,decimal_down
ROOT=Path(__file__).resolve().parent

def collect():
    allrows=[];paper=ROOT.parent/'paper';paper.mkdir(exist_ok=True)
    for s in [1,2]:
        upper=json.loads((ROOT/f'results_sigma{s}.json').read_text())
        lower=json.loads((ROOT/f'pair_maximum_results_sigma{s}.json').read_text())
        pois=json.loads((ROOT/f'poisson_results_sigma{s}.json').read_text())
        old=json.loads((ROOT/'baseline'/f'results_sigma{s}.json').read_text())
        lines=['epochs pair_lower new_upper previous_upper deterministic poisson']
        for a,b,c,d in zip(upper['rows'],lower['rows'],pois['rows'],old['rows']):
            assert a['epochs']==b['epochs']==c['epochs']==d['epochs']
            e=a['epochs'];L=F(*map(int,b['epsilon_lower_open']));U=F(*map(int,a['epsilon_upper']));V=F(*map(int,c['epsilon_upper']))
            O=F(*map(int,d['epsilon_upper']));D=F(*map(int,a['deterministic_epsilon_upper']));Dl=F(*map(int,a['deterministic_epsilon_lower']))
            assert max(F(*map(int,x)) for x in b['delta_at_lower'])>F(1,10**8)
            assert max(F(*map(int,a[x])) for x in ['forward_delta_upper','reverse_delta_upper'])<F(1,10**8)
            assert max(F(*map(int,x)) for x in c['delta_upper'])<F(1,10**8)
            row={'sigma':s,'T':1000,'epochs':e,'delta':jd(F(1,10**8)),
                'continuous_pair_epsilon_strict_lower':jd(L),'shuffled_adaptive_epsilon_upper':jd(U),
                'poisson_epsilon_upper':jd(V),'deterministic_epsilon_interval':[jd(Dl),jd(D)],
                'pair_statistic':b,'shuffled_certificate':a,'poisson_certificate':c,
                'previous_upper':jd(O),'certified_upper_to_pair_ratio_upper':jd(U/L),
                'certified_shuffle_to_poisson_ratio_strict_lower':jd(L/V),
                'bracket_width_reduction_fraction':jd((O-U)/(O-L)),
                'deterministic_reduction_fraction_strict_lower':jd(1-U/Dl)}
            allrows.append(row)
            lines.append(f'{e} {decimal_down(L,3)} {decimal_up(U,2)} {decimal_up(O,2)} {decimal_up(D,5)} {decimal_up(V,3)}')
        (ROOT/f'comparison_sigma{s}.dat').write_text('\n'.join(lines)+'\n')
        (paper/f'comparison_sigma{s}.dat').write_text('\n'.join(lines)+'\n')
    obj={'status':'Certified upper accountant with attainable product-pair lower brackets and matched Poisson upper accounting.',
        'scope':'Fresh independent reshuffling each epoch; zero-out item adjacency; ideal Gaussian releases; full adaptive query transcript; all batch sizes and dimensions.',
        'lower_scope':'The lower bound is obtained by coarsening the full continuous Chua product pair to per-epoch maximum bins. It is not asserted to be its exact epsilon.',
        'poisson_scope':'A different sampler: q=1/1000, 1000*epochs independent subsampled releases, matched noise and expected batch size.',
        'rows':allrows}
    (ROOT/'verified_results.json').write_text(json.dumps(obj,indent=2))
    print('COLLECTED',len(allrows),'certified comparison rows')
    for row in allrows:
        if row['epochs']==5:
            print(row['sigma'],'ratio to pair <=',float(F(*map(int,row['certified_upper_to_pair_ratio_upper']))),
                  'gap closure >',float(F(*map(int,row['bracket_width_reduction_fraction']))),
                  'Poisson separation >',float(F(*map(int,row['certified_shuffle_to_poisson_ratio_strict_lower']))))
if __name__=='__main__':collect()
