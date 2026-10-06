#!/usr/bin/env python3
"""Check every number quoted in the paper against the certificate outputs.

Run after run_all.py. The script reads only JSON and .dat files written by the
certificate programs and compares them with the decimal values printed in the
abstract, Table I, the figures and the text. All comparisons use exact rationals.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
EPOCHS = [1, 2, 3, 5, 10, 20]

# Values as printed in Table I: (pair L, shuffle U, Poisson U, deterministic U).
TABLE = {
    1: {1: ('5.106', '5.64', '0.306', '5.77610'), 2: ('5.538', '6.49', '0.363', '8.53379'),
        3: ('5.885', '7.11', '0.414', '10.77586'), 5: ('6.423', '7.97', '0.507', '14.55021'),
        10: ('7.354', '9.46', '0.697', '22.17344'), 20: ('8.646', '11.68', '0.982', '34.45138')},
    2: {1: ('0.257', '0.47', '0.081', '2.70761'), 2: ('0.289', '0.54', '0.114', '3.94247'),
        3: ('0.310', '0.60', '0.140', '4.92507'), 5: ('0.338', '0.71', '0.182', '6.54266'),
        10: ('0.383', '0.93', '0.260', '9.69785'), 20: ('0.438', '1.29', '0.372', '14.55021')},
}
# Moment/Laplace baseline at five epochs (introduction and the ablation paragraph).
BASELINE_FIVE = {1: '9.21', 2: '0.83'}
# Exact endpoint certificates at five epochs, numerators over 10^15.
UPPER_CERT = {1: (9856064, 3805278), 2: (8525892, 5244378)}
LOWER_CERT = {1: 10011846, 2: 10201901}
# Inverse of the binned maximum statistic at five epochs.
BINNED = {1: ('6.423', '6.426'), 2: ('0.338', '0.342')}
# Thresholds (forward, reverse) at which the candidate-count bound beats the baseline.
STRICT = {1: (411, 431), 2: (247, 288)}


def frac(pair):
    return F(int(pair[0]), int(pair[1]))


def load(name):
    return json.loads((ROOT / name).read_text())


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)
    print('ok', msg)


def main():
    delta = F(1, 10**8)
    rows = {(r['sigma'], r['epochs']): r for r in load('verified_results.json')['rows']}
    check(sorted(rows) == [(s, e) for s in (1, 2) for e in EPOCHS], 'twelve rows')
    for s in (1, 2):
        dat = (ROOT / f'comparison_sigma{s}.dat').read_text().split('\n')
        head = dat[0].split()
        dat_rows = {int(x.split()[0]): dict(zip(head, x.split())) for x in dat[1:] if x}
        base = {r['epochs']: r for r in load(f'baseline/results_sigma{s}.json')['rows']}
        for e in EPOCHS:
            r = rows[(s, e)]
            check(r['T'] == 1000 and frac(r['delta']) == delta, f'sigma={s} E={e}: T and delta')
            lo, up, po, de = TABLE[s][e]
            check(frac(r['continuous_pair_epsilon_strict_lower']) == F(lo), f'sigma={s} E={e}: pair lower {lo}')
            check(frac(r['shuffled_adaptive_epsilon_upper']) == F(up), f'sigma={s} E={e}: shuffle upper {up}')
            check(frac(r['poisson_epsilon_upper']) == F(po), f'sigma={s} E={e}: Poisson upper {po}')
            dl, du = map(frac, r['deterministic_epsilon_interval'])
            check(du == F(de) and du - dl == F(1, 10**5), f'sigma={s} E={e}: deterministic {de}, width 1e-5')
            sc = r['shuffled_certificate']
            check(frac(sc['forward_delta_upper']) < delta and frac(sc['reverse_delta_upper']) < delta,
                  f'sigma={s} E={e}: both directions below delta')
            ps = r['pair_statistic']
            check(frac(ps['delta_at_lower'][0]) > delta, f'sigma={s} E={e}: pair forward lower bound exceeds delta')
            check(frac(r['poisson_certificate']['delta_upper'][0]) < delta
                  and frac(r['poisson_certificate']['delta_upper'][1]) < delta
                  and r['poisson_certificate']['steps'] == 1000 * e, f'sigma={s} E={e}: Poisson both directions, 1000E steps')
            d = dat_rows[e]
            check((d['pair_lower'], d['new_upper'], d['poisson'], d['deterministic']) == (lo, up, po, de),
                  f'sigma={s} E={e}: figure table matches Table I')
            check(F(d['previous_upper']) == frac(base[e]['epsilon_upper'])
                  and frac(r['previous_upper']) == frac(base[e]['epsilon_upper']),
                  f'sigma={s} E={e}: baseline upper {d["previous_upper"]}')
        r5 = rows[(s, 5)]
        check(F(BASELINE_FIVE[s]) == frac(base[5]['epsilon_upper']), f'sigma={s}: baseline five-epoch {BASELINE_FIVE[s]}')
        fw, rv = UPPER_CERT[s]
        sc = r5['shuffled_certificate']
        for name, num in (('forward', fw), ('reverse', rv)):
            v = frac(sc[f'{name}_delta_upper'])
            check(v <= F(num, 10**15) and v > F(num - 1, 10**15), f'sigma={s}: {name} certificate <= {num}/10^15 (tight)')
        v = frac(r5['pair_statistic']['delta_at_lower'][0])
        check(v >= F(LOWER_CERT[s], 10**15) and v < F(LOWER_CERT[s] + 1, 10**15),
              f'sigma={s}: lower certificate >= {LOWER_CERT[s]}/10^15 (tight)')
        blo, bup = BINNED[s]
        check(frac(r5['pair_statistic']['epsilon_lower_open']) == F(blo)
              and frac(r5['pair_statistic']['epsilon_upper_closed']) == F(bup), f'sigma={s}: binned inverse ({blo},{bup}]')

    # Ratios and percentages quoted in the text.
    t = TABLE
    check(F(t[1][5][0]) / F(t[1][5][2]) > F('12.6') and F(t[2][5][0]) / F(t[2][5][2]) > F('1.85'), 'Poisson separation factors')
    for s, pct in ((1, '0.444'), (2, '0.243')):
        b, u, l = F(BASELINE_FIVE[s]), F(t[s][5][1]), F(t[s][5][0])
        check((b - u) / (b - l) > F(pct), f'sigma={s}: bracket closure > {pct}')
    check(F(t[1][1][1]) / F(t[1][1][0]) < F('1.105'), 'one-epoch ratio < 1.105')
    check(F(t[1][2][1]) / F(t[1][2][0]) < F('1.172'), 'two-epoch ratio < 1.172')
    check(F(t[1][5][1]) / F(t[1][5][0]) < F('1.241'), 'five-epoch ratio < 1.241 at sigma=1')
    check(F(t[2][5][1]) / F(t[2][5][0]) < F('2.101'), 'five-epoch ratio < 2.101 at sigma=2')
    check(F(t[1][1][1]) < F(t[1][1][3]) and F(TABLE[1][1][3]) < F(load('baseline/results_sigma1.json')['rows'][0]['epsilon_upper_decimal']),
          'sigma=1 one epoch: new upper below deterministic, baseline above it')

    # Parameters quoted in the text and appendix.
    for s, M, hr in ((1, 64, (140, 380)), (2, 160, (65, 240))):
        inp = load(f'candidate_inputs_sigma{s}.json')
        check(inp['M'] == M and inp['XB'] == 30 and inp['PB'] == 72 and inp['bins_per_unit'] == 50
              and inp['grid_den'] == 400, f'sigma={s}: M={M}, 2^-30 support, 2^-72 masses, bins 1/50, grid 1/400')
        prof = load(f'profile_sigma{s}.json')
        check(prof['ratio'] == ['51', '50'] and prof['J'] == 555 and len(prof['rows']) == 556
              and int(prof['denominator']) == 2**100, f'sigma={s}: thresholds (51/50)^j, 0<=j<=555, 2^-100 rounding')
        aud = load(f'candidate_audit_sigma{s}.json')
        hs = {frac(w[d]['h']) for w in aud['rows'] for d in ('forward', 'reverse')}
        check(all(h * 40 == int(h * 40) and hr[0] <= h * 40 <= hr[1] for h in hs),
              f'sigma={s}: selected h in {{{hr[0]},...,{hr[1]}}}/40')
        old = {x['j']: x for x in load(f'baseline/profile_sigma{s}.json')['rows']}
        D = int(prof['denominator'])
        assert int(load(f'baseline/profile_sigma{s}.json')['denominator']) == D
        for k, n in zip(('forward_numerator', 'reverse_numerator'), STRICT[s]):
            new_b = [int(x[k]) for x in prof['rows']]
            old_b = [int(old[x['j']][k]) for x in prof['rows']]
            check(all(a <= b for a, b in zip(new_b, old_b))
                  and sum(a < b for a, b in zip(new_b, old_b)) == n,
                  f'sigma={s} {k[:7]}: no threshold bound worse than the baseline, {n} of 556 strictly better')
        pair = load(f'dominating_pair_sigma{s}.json')
        check(pair['ratio'] == ['51', '50'] and all(-555 <= a['loss_index'] <= 555 for a in pair['finite_atoms']),
              f'sigma={s}: finite losses on j log(51/50)')
    for s in (1, 2):
        pm = load(f'pair_maximum_results_sigma{s}.json')
        po = load(f'poisson_results_sigma{s}.json')
        check(pm['r'] == ['2001', '2000'] and po['ratio'] == ['10001', '10000'] and po['q'] == ['1', '1000'],
              f'sigma={s}: mesh ratios 2001/2000 and 10001/10000, q = 1/1000')
    print('ALL PAPER NUMBERS CHECKED')


if __name__ == '__main__':
    main()
