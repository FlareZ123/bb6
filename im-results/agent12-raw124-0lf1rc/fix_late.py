from pathlib import Path
import re
for i in [77,81,91,94]:
    p=Path(f'core/Agent12LateRCM{i}.lean')
    s='import LateRCBridge\n'+p.read_text()
    t=re.search(r'knownRun table (\d+)',s).group(1)
    a=s.index('theorem bound_all');b=s.index('#print axioms first_query',a)
    s=s[:a]+f'''theorem bound_all : ∀ m, compatible table m → WeightedBound 108667 m :=
  bounded_of_query 108667 table {t} (1,true) (by decide) first_query (by decide) (by decide) (by decide)
'''+s[b:]
    s=s.replace('theorem prefix1','attribute [local irreducible] prun knownRun\ntheorem prefix1',1)
    prev=2000;lines=[]
    for l in s.splitlines():
        m=re.fullmatch(r'theorem prefix(\d+) : prun table (\d+) ⟨0,0,0⟩ = some z\d+ := joinP prefix(\d+) seg(\d+)',l)
        if m:
            j,n,k,seg=map(int,m.groups())
            l=f'''theorem prefix{j} : prun table {n} ⟨0,0,0⟩ = some z{j} := by
  have h := joinP (p := table) (n := {prev}) (k := {n-prev}) (a := ⟨0,0,0⟩) (b := z{k}) (c := z{j}) prefix{k} seg{seg}
  exact h'''
            prev=n
        lines.append(l)
    p.write_text('\n'.join(lines)+'\n')
