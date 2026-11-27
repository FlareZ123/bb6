"""Emit untrusted Lean data and proof modules from m19569_certificate.py JSON."""
import json, sys
from collections import defaultdict
from pathlib import Path
from contextlib import redirect_stdout

def lean_list(xs): return '[' + ','.join(map(str,xs)) + ']'
def pair_list(xs): return '[' + ','.join(f'({a},{b})' for a,b in xs) + ']'
def stack(edges):
    n=1+max(max(t,s) for t,x,s in edges)
    rev=[[] for _ in range(n)]; fwd=[[] for _ in range(n)]
    for t,x,s in edges: rev[t].append((x,s)); fwd[s].append((x,t))
    return rev, fwd
def emit(cert):
    print('import RunStack\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent4M19569\nopen BB6Coverage BB6Coverage.Agent31Pump BB6.Agent4RunStack')
    print('def p : PartialMachine := fun (q,b) =>\n  match q.val,b with')
    raw='1RB0LE_1RC---_0RD1RA_1LD1LE_1RF1LC_0RD0RA'.replace('_','')
    for k in range(12):
        s=raw[3*k:3*k+3]; val='none' if s=='---' else f'some (some ⟨{str(s[0]=="1").lower()},{str(s[1]=="R").lower()},{ord(s[2])-65}⟩)'
        print(f'  | {k//2},{str(k%2==1).lower()} => {val}')
    print('  | _,_ => none')
    def balanced(names, lo, hi):
        if hi-lo==1: return names[lo]
        mid=(lo+hi)//2
        return f'(if i < {mid} then {balanced(names,lo,mid)} else {balanced(names,mid,hi)})'
    for i,s in enumerate(cert['edges']):
        names=[]
        for d,tab in enumerate(stack(s)):
            name=f'st{i}_{d}'
            print(f'def {name} (i : Nat) : List (Nat × Nat) := if i < {len(tab)} then '+balanced([pair_list(row) for row in tab],0,len(tab))+' else []')
            names.append(name)
        print(f'def st{i} : Stack := ⟨{names[0]},{names[1]}⟩')
    rows=defaultdict(list)
    assert len(cert['sections'])==len(cert['rules'])
    for (i,j),(lp,rp,k,lo,ro) in zip(cert['sections'],cert['rules']):
        rows[i].append(f'({j},⟨{lean_list(lp)},{lean_list(rp)},{lean_list(lo)},{lean_list(ro)},{k}⟩)')
    n=1+max(rows)
    for i in range(n): print(f'def row{i} : List (Nat × Rule) := ['+',\n'.join(rows[i])+']')
    print(f'def rows (i : Nat) : List (Nat × Rule) := '+balanced(['row'+str(i) for i in range(n)],0,n))
    print(f'def cert : Cert := ⟨st0,st1,{n},rows⟩')
    print('end BB6.Agent4M19569')
    return n

def modules(cert, out):
    out.mkdir(parents=True,exist_ok=True)
    with (out/'M19569Data.lean').open('w',encoding='utf-8') as f, redirect_stdout(f):
        n=emit(cert)
    preamble = '''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4M19569
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent4RunStack
'''
    for i in range(n):
        (out/f'M19569Check{i}.lean').write_text('import M19569Data\n'+preamble+f'theorem row_ok_{i} : cert.checkRow p {i} = true := by rfl\nend BB6.Agent4M19569\n',encoding='utf-8')
    final = ''.join(f'import M19569Check{i}\n' for i in range(n))+preamble+'''theorem checked : cert.check p = true := by
  change ('''+lean_list(range(n))+''' : List Nat).all (cert.checkRow p) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, '''+', '.join(f'row_ok_{i}' for i in range(n))+''']
def entryZ : Z0 := ⟨0,[false,false,true],[false,true,true,true]⟩
theorem entry : run0 p 34 ⟨0,[],[]⟩ = some entryZ := by rfl
theorem entry_eq : ZEq entryZ (sec [1] [259]) := ⟨rfl, trim_eq (by rfl), trim_eq (by rfl)⟩
theorem entryInv : cert.Inv entryZ := Cert.entryInv entry_eq (by rfl)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := Cert.never checked entry entryInv m hm
#print axioms never
theorem cover_never : Cover NeverHalts p := Cover.leaf p never
#print axioms cover_never
end BB6.Agent4M19569
'''
    (out/'M19569Final.lean').write_text(final,encoding='utf-8')

if __name__=='__main__':
    modules(json.loads(Path(sys.argv[1]).read_text()),Path(sys.argv[2]) if len(sys.argv)>2 else Path('.'))
