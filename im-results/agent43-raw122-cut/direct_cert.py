#!/usr/bin/env python3
"""Generate and kernel-check fixed-cost recurrent tape families.
Usage: python direct_cert.py direct_certificates.json WORK [IDS...]
LEAN_PATH must contain the original SweepPumping.olean dependency closure.
No simulation success is accepted as a theorem; every trace block is checked by rfl.
"""
from dataclasses import dataclass
from pathlib import Path
import json, os, subprocess, sys

NS = 'BB6Coverage.Agent31Pump.Raw122DirectGrowth'
CHUNK = 256
GROUP = 5

@dataclass(frozen=True)
class Word:
    pre: str = ''
    rep: str = ''
    suf: str = ''
    def head(self):
        if self.pre: return self.pre[0]
        assert not self.rep and not self.suf, 'opaque read'
        return '0'
    def tail(self):
        if self.pre: return Word(self.pre[1:],self.rep,self.suf)
        assert not self.rep and not self.suf, 'opaque tail'
        return self
    def cons(self,b): return Word(b+self.pre,self.rep,self.suf)
    def zero(self): return Word(self.pre+self.suf)
    def inc(self): return Word(self.pre+self.rep,self.rep,self.suf)

def step(p,c):
    q,l,r=c
    a=p[2*q+int(l.head())]
    assert a != '---', 'unassigned transition'
    q,w=ord(a[2])-65,a[0]
    if a[1]=='R': return q,l.tail().cons(w).cons(r.head()),r.tail()
    return q,l.tail(),r.cons(w)

def bits(s): return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
def word(w):
    return ' ++ '.join(x for x in (bits(w.pre),f'rep {bits(w.rep)} n' if w.rep else '[]',bits(w.suf)) if x!='[]') or '[]'
def cfg(c): return f'⟨{c[0]},{word(c[1])},{word(c[2])}⟩'
def table(p):
    lines=['def table : PartialMachine := fun s => match s.1.val,s.2 with']
    for i,a in enumerate(p):
        if a!='---': lines.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)')
    return '\n'.join(lines+['  | _,_ => none'])

def generate(a,work):
    i=a['id'];s=a['table'];s0=s.replace('_','');p=[s0[j:j+3] for j in range(0,36,3)]
    assert len(s0)==36
    t,k=a['entry'],a['cost'];q=a['q'];l,r=Word(*a['l']),Word(*a['r'])
    assert k>0
    prefix=f'Raw122D{i}'
    header=f'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace {NS}\nopen BB6Coverage BB6Coverage.Agent31Pump\nnamespace M{i}\n'
    footer=f'\nend M{i}\nend {NS}\n'
    base=[f'-- {s}',table(p),f'def family (n : Nat) : Z0 := {cfg((q,l,r))}']
    proofs=[];joins=[];final=[]
    def blocks(label,num,start,goal,sym):
        assert num>0
        cur=start;states=[start];lengths=[]
        for j in range(num):
            cur=step(p,cur)
            if (j+1)%CHUNK==0 or j+1==num:
                states.append(cur);lengths.append(j+1-sum(lengths))
        assert cur==goal,(i,label,'incorrect endpoint')
        binder=' (n : Nat)' if sym else ''
        arg=' n' if sym else ''
        for j,c in enumerate(states):
            if j==0:rhs='family n' if sym else '⟨0,[],[]⟩'
            elif j==len(states)-1:rhs='family (n+1)' if sym else 'family 0'
            else:rhs=cfg(c)
            base.append(f'def {label}C{j}{binder} : Z0 := {rhs}')
        total=0
        for j,n in enumerate(lengths):
            c0,c1,c2=(f'({label}C{v}{arg})' for v in (0,j,j+1))
            proofs.append(f'theorem {label}S{j}{binder} : run0 table {n} {c1} = some {c2} := by rfl')
            h=f'{label}S0{arg}' if j==0 else f'@join0 table {total} {n} {c0} {c1} {c2} ({label}J{j-1}{arg}) ({label}S{j}{arg})'
            total+=n
            joins.append(f'theorem {label}J{j}{binder} : run0 table {total} {c0} = some {c2} := {h}')
        target='(family n) = some (family (n+1))' if sym else '⟨0,[],[]⟩ = some (family 0)'
        final.append(f'theorem {label}{binder} : run0 table {num} {target} := {label}J{len(lengths)-1}{arg}')
    blocks('entry',t,(0,Word(),Word()),(q,l.zero(),r.zero()),False)
    blocks('growth',k,(q,l,r),(q,l.inc(),r.inc()),True)
    final.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {t} (fun _ => {k}) entry (by intro n; decide) growth m hm')
    final.append('#print axioms never')
    modules=[]
    def emit(name,imports,decls):
        (work/(name+'.lean')).write_text('\n'.join(f'import {m}' for m in imports)+'\n'+header+'\n\n'.join(decls)+footer,encoding='utf-8');modules.append(name)
    emit(prefix+'Base',['SweepPumping'],base)
    ss=[]
    for j in range(0,len(proofs),GROUP):
        name=f'{prefix}S{j//GROUP:02}';emit(name,[prefix+'Base'],proofs[j:j+GROUP]);ss.append(name)
    emit(prefix+'Join',ss,joins)
    emit(f'Raw122Direct{i}',[prefix+'Join'],final)
    return modules

def main():
    certs=json.loads(Path(sys.argv[1]).read_text());work=Path(sys.argv[2]).resolve();work.mkdir(parents=True,exist_ok=True)
    ids=set(map(int,sys.argv[3:])) if len(sys.argv)>3 else {a['id'] for a in certs}
    env=dict(os.environ,LEAN_PATH=str(work)+os.pathsep+os.environ['LEAN_PATH'])
    for a in certs:
        if a['id'] not in ids:continue
        modules=generate(a,work)
        for m in modules:
            p=subprocess.run(['lean','-o',m+'.olean',m+'.lean'],cwd=work,env=env,text=True,capture_output=True,check=True)
            print(m,p.stdout,end='\n',flush=True)
            assert 'sorryAx' not in p.stdout and 'Lean.ofReduceBool' not in p.stdout

if __name__=='__main__':main()
