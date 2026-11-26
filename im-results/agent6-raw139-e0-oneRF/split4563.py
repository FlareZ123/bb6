"""Partition the generated RF4563 base and independent trace checks.

All generated mathematical statements are unchanged. Only module boundaries
are adjusted so the exact kernel checker can run on independent proof cuts.
"""
from pathlib import Path
import sys,re,json
work=Path(sys.argv[1]);out=work/'imports'
f=out/'RF4563Base.lean';s=f.read_text()
i=s.index('def p : PartialMachine');j=s.index('def r0d : Rule');k=s.index('def periodStart : State')
header=s[:i];end='end BB6.Agent6RF4563\n'
(out/'RF4563Table.lean').write_text(header+s[i:j]+end)
rules=re.findall(r'^def [rs]\d+d : (?:Rule|Sweep) := [^\n]+\n^def [rs]\d+ : C[RS] p := [^\n]+\n',s[j:k],re.M)
assert ''.join(rules)==s[j:k], 'unexpected rule source format'
mods=[]
for n in range(0,len(rules),32):
    name=f'RF4563Rules{n//32:04d}';mods.append(name)
    (out/(name+'.lean')).write_text(header.replace('import SymTrace','import RF4563Table')+''.join(rules[n:n+32])+end)
f.write_text('import RF4563Table\n'+''.join('import '+m+'\n' for m in mods)+header[header.index('set_option'):]+s[k:])
# Balance independent checks by source byte size. Each still imports the same
# exact common base; no chunk is omitted or merged by approximation.
traces=sorted([*out.glob('RF4563Period[0-9]*.lean'),*out.glob('RF4563Seed[0-9]*.lean')],key=lambda f:(-f.stat().st_size,f.name))
assert traces
n=min(16,len(traces));groups=[[] for _ in range(n)];sizes=[0]*n
for f in traces:
    g=min(range(n),key=lambda i:sizes[i]);groups[g].append(f.name);sizes[g]+=f.stat().st_size
(work/'groups').mkdir(exist_ok=True)
for i,group in enumerate(groups):
    (work/'groups'/f'{i:02d}.txt').write_text(''.join(x+'\n' for x in sorted(group)))
assert sorted(x for g in groups for x in g)==sorted(f.name for f in traces)
(work/'matrix.json').write_text(json.dumps({'group':[f'{i:02d}' for i in range(n)]}))
print('Exact source cuts:',len(mods),'rule batches,',len(traces),'trace modules,',n,'groups',flush=True)
