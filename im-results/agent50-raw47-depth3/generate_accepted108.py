"""Build the 108 accepted-cover consumer without rerunning any machine search."""
import base64, hashlib, subprocess, sys
from pathlib import Path
here = Path(__file__).resolve().parent
out = Path(sys.argv[1]).resolve()
out.mkdir(parents=True, exist_ok=True)
raw = (here/'raw47-depth3.open').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
mask = base64.b64decode((here/'broad-far-parents.b64').read_text())
assert len(mask)==1212 and sum(mask)==674 and set(mask)=={0,1}
far = [i for i,v in enumerate(mask) if v][1::8]
pump = [29,97,109,116,171,176,216,237,260,303,351,517,597,933,1039,1050,1060,16,418,739,913,984,1047]
assert len(far)==85 and len(pump)==23 and len(set(far+pump))==108
assert all(not mask[i] for i in pump)
empty = out/'empty-bank.txt'
empty.write_text('')
subprocess.run([sys.executable,str(here/'generate_depth3_far.py'),str(empty),str(out/'Raw47Depth3Cut.lean')],check=True)
imports = ['Raw47D3FAR'+str(i) for i in far]+['Raw47D3P'+str(i) for i in pump]
for name in imports:
    assert (out/(name+'.lean')).is_file(), name
entries = []
for i in far:
    n=f'BB6.Agent50.Raw47D3FAR{i}'
    entries.append(f'  ⟨{n}.p, {n}.all_quotient⟩')
for i in pump:
    n=f'BB6.Agent50.Raw47D3P{i}'
    entries.append(f'  ⟨{n}.p, quotientSafe {n}.root {n}.bound⟩')
header = '\n'.join('import '+name for name in ['Raw47Depth3Cut']+imports)
body = (here/'Raw47Accepted108.template').read_text()
(out/'Raw47Accepted108.lean').write_text(header+'\n'+body.replace('@@ENTRIES@@',',\n'.join(entries)))
print('108 disjoint accepted proof modules selected; exact membership is checked in Lean.')
