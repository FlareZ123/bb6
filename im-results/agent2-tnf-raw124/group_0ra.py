"""Group independent leaf proofs under each split into a single module."""
from pathlib import Path
import sys,re
root=Path(sys.argv[1]);order=Path(sys.argv[2]);mods=order.read_text().splitlines();
# Child modules that have only the base import can share the parent group.
by_parent={};renames={};
for m in mods:
 p=root/(m+'.lean');s=p.read_text();imports=re.findall(r'^import (\w+)',s,re.M)
 if len(imports)==1 and '_' in m:
  par=m.rsplit('_',1)[0];by_parent.setdefault(par,[]).append(m)
for par,ms in by_parent.items():
 # Preserve order, limit groups to 8 small proofs to bound peak memory.
 for i in range(0,len(ms),8):
  group=ms[i:i+8]
  if len(group)<2:continue
  gn=par+f'Group{i//8:02}'
  header=(root/(group[0]+'.lean')).read_text().split('\ndef kid',1)[0]
  body=[]
  for m in group:
   s=(root/(m+'.lean')).read_text();body.append('\ndef kid'+s.split('\ndef kid',1)[1].rsplit('\nend BB6.Agent2Raw124ZeroLF0RA',1)[0]);renames[m]=gn
  (root/(gn+'.lean')).write_text(header+'\n'+''.join(body)+'\nend BB6.Agent2Raw124ZeroLF0RA\n')
# Rewrite imports, and use topological order with groups in the position of their first member.
new=[]
for m in mods:
 if m in renames:
  g=renames[m]
  if g not in new:new.append(g)
  continue
 p=root/(m+'.lean');s=p.read_text();seen=set()
 def subst(mt):
  a=renames.get(mt[1],mt[1])
  if a in seen:return ''
  seen.add(a);return f'import {a}\n'
 s=re.sub(r'^import (\w+)\n',subst,s,flags=re.M);p.write_text(s);new.append(m)
order.with_suffix('.grouped').write_text('\n'.join(new)+'\n');print(len(mods),'->',len(new))
