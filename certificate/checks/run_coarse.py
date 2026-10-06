#!/usr/bin/env python3
"""Rebuild the coarse second evaluation recorded in coarse_results_sigma*.json.

It repeats the upper accountant with 25 normal bins per unit (width 1/25) and
threshold-grid denominator 200, half the resolution of the accepted run. The work
is done in a temporary copy so that the accepted inputs are not overwritten.
"""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile
CHECKS=Path(__file__).resolve().parent;ROOT=CHECKS.parent
FILES=['candidate_prepare.py','candidate_dp.cpp','refine_candidates.py','compose.py','mpinterval.py','intervals.py','build_profile.py']
def main():
    with tempfile.TemporaryDirectory() as d:
        d=Path(d)
        for f in FILES:shutil.copy(ROOT/f,d/f)
        subprocess.run(['g++','-O2','-std=c++17','-frounding-math','-ffp-contract=off','-fno-fast-math','candidate_dp.cpp','-o','candidate_dp'],cwd=d,check=True)
        prep='import candidate_prepare as c\nfor s in (1,2):c.prepare(s,bins=25,grid_den=200);c.check_plaintext(s)'
        subprocess.run([sys.executable,'-c',prep],cwd=d,check=True)
        for s in (1,2):subprocess.run([str(d/'candidate_dp'),f'candidate_inputs_sigma{s}.txt',f'candidate_values_sigma{s}.txt'],cwd=d,check=True)
        subprocess.run([sys.executable,'refine_candidates.py','1','2'],cwd=d,check=True)
        subprocess.run([sys.executable,'compose.py','1','2'],cwd=d,check=True)
        for s in (1,2):
            new=json.loads((d/f'results_sigma{s}.json').read_text())
            (CHECKS/f'coarse_results_sigma{s}.json').write_text(json.dumps(new,indent=2))
            print('COARSE',s,[r['epsilon_upper_decimal'] for r in new['rows']])
if __name__=='__main__':main()
