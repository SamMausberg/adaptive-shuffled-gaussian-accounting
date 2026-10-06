"""Recreate the complete certificate using only the Python standard library."""
from pathlib import Path
import subprocess,sys,json,hashlib
ROOT=Path(__file__).resolve().parent
for script in ('selftest.py','build_profile.py','refine_laplace.py','compose.py'):
    subprocess.run([sys.executable,str(ROOT/script)],check=True,cwd=ROOT)
accepted={}
for sigma in (1,2):
    obj=json.loads((ROOT/f'results_sigma{sigma}.json').read_text())
    for row in obj['rows']:
        from fractions import Fraction as F
        bound=max(F(*map(int,row[x])) for x in ('forward_delta_upper','reverse_delta_upper'))
        assert bound<F(1,100000000)
    accepted[f'sigma{sigma}']=obj
(ROOT/'verified_results.json').write_text(json.dumps(accepted,indent=2))
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ROOT.iterdir()) if p.suffix in ('.py','.json','.dat') and p.name!='manifest.json'}
(ROOT/'manifest.json').write_text(json.dumps(manifest,indent=2))
print('All numerical endpoints are certified in both directions.')
