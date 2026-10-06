#!/usr/bin/env python3
"""Rebuild all claimed numerical results from directed primitive arithmetic."""
from pathlib import Path
import subprocess,sys,json,hashlib,time,os
ROOT=Path(__file__).resolve().parent
os.environ['OPENBLAS_NUM_THREADS']='1'
def call(*args):subprocess.run(args,cwd=ROOT,check=True)
def main():
    t=time.time()
    call('g++','-O2','-std=c++17','-frounding-math','-ffp-contract=off','-fno-fast-math','candidate_dp.cpp','-o','candidate_dp')
    call(sys.executable,'candidate_prepare.py','1','2')
    from candidate_prepare import check_plaintext
    for s in [1,2]:
        check_plaintext(s)
        call(str(ROOT/'candidate_dp'),f'candidate_inputs_sigma{s}.txt',f'candidate_values_sigma{s}.txt')
    call(sys.executable,'refine_candidates.py','1','2')
    call(sys.executable,'compose.py','1','2')
    call(sys.executable,'pair_maximum.py','1','2')
    call(sys.executable,'poisson_account.py','1','2')
    call(sys.executable,'verify_checks.py')
    call(sys.executable,'collect_results.py')
    keep={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.iterdir() if p.is_file() and p.suffix in ['.py','.cpp','.json','.dat','.txt'] and p.name!='manifest.json'}
    (ROOT/'manifest.json').write_text(json.dumps({'sha256':keep,'description':'Checksums of source and numerical certificate files. Rebuild with run_all.py for mathematical verification.'},indent=2))
    print('FULL REPRODUCTION PASSED; elapsed seconds',round(time.time()-t,3))
if __name__=='__main__':main()
