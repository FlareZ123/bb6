#!/usr/bin/env python3
"""Specialize the source-checked width-8 sparse block proof to widths 5 and 6.
Reuse agent1's source archive and exact witness construction. The Lean kernel
checks all generated code and finite certificate data; no discovery assertion
is imported as a theorem.
"""
import sys,pathlib,tarfile,json,base64,zlib,re,os
from pathlib import Path
repo=Path.cwd()
here=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
out.mkdir(parents=True,exist_ok=True)
archive=repo/'im-results/agent1-raw139-e0-oneRD/wide-source.tar.gz'
with tarfile.open(archive) as a:
    files={n:a.extractfile(n).read().decode() for n in ('WideBlock.lean','WideSparse.lean','widegraph.py','emit_wide.py')}
manifest=json.loads(Path(sys.argv[2]).read_text())
ids=sorted(manifest)
def make_block(w):
    A=2**w;N=f'BB6.Agent3OneLBWide{w}';src=files['WideBlock.lean']
    s=src.split('structure Sym where')[0]
    s+='structure Sym where\n'+''.join(f'  b{i} : Bool\n' for i in range(w))+'  deriving DecidableEq, Repr\n\n'
    s+='def Sym.zero : Sym := ⟨'+','.join(['false']*w)+'⟩\n\n'
    s+='def Sym.code (s : Sym) : Nat := '+' + '.join(f'{2**i}*s.b{i}.toNat' for i in range(w))+'\n\n'
    s+='def Sym.ofCode (n : Nat) : Sym := ⟨'+','.join(f'n/{2**i}%2 == 1' for i in range(w))+'⟩\n\n'
    s+=f'def symbols : List Sym := (List.range {A}).map Sym.ofCode\n\n'
    bounds=''.join(f'  have hb{i} : s.b{i}.toNat ≤ 1 := by cases s.b{i} <;> decide\n' for i in range(w))
    s+=f'theorem code_lt (s : Sym) : s.code < {A} := by\n'+bounds+'  unfold Sym.code\n  omega\n\n'
    s+='theorem ofCode_code (s : Sym) : Sym.ofCode s.code = s := by\n'+bounds
    for i in range(w):
        s+=f'''  have h{i} : (s.code / {2**i} % 2 == 1) = s.b{i} := by
    have he : s.code / {2**i} % 2 = s.b{i}.toNat := by
      unfold Sym.code
      omega
    rw [he]
    cases s.b{i} <;> rfl
'''
    s+='  cases s\n  simp only [Sym.ofCode,Sym.mk.injEq]\n  exact ⟨'+','.join(f'h{i}' for i in range(w))+'⟩\n\n'
    s+='theorem symbols_complete (s : Sym) : s ∈ symbols := by\n  exact List.mem_map.mpr ⟨s.code,List.mem_range.mpr (code_lt s),ofCode_code s⟩\n\n'
    s+='inductive Pos where '+' '.join(f'| p{i}' for i in range(w))+'\n  deriving DecidableEq, Repr\n\n'
    s+='def Sym.read (s : Sym) : Pos → Bool\n'+''.join(f'  | .p{i} => s.b{i}\n' for i in range(w))+'\n'
    s+='def Sym.write (s : Sym) (p : Pos) (w : Bool) : Sym :=\n  match p with\n'
    for i in range(w):
        s+=f'  | .p{i} => ⟨'+','.join('w' if i==j else f's.b{j}' for j in range(w))+'⟩\n'
    def ray(xs,tail):
        for x in reversed(list(xs)):tail=f'cons {x} ({tail})'
        return tail
    for side,idx in [('left',list(reversed(range(w)))),('right',list(range(w)))]:
        s+=f'\ndef {side}Ray : List Sym → Ray\n  | [] => blankRay\n  | a::r => '+ray([f'a.b{i}' for i in idx],f'{side}Ray r')+'\n'
        s+=f'\ntheorem {side}Ray_unfold (l : List Sym) :\n    {side}Ray l = '+ray([f'(l.headD Sym.zero).b{i}' for i in idx],f'{side}Ray l.tail')+f' := by\n  cases l with\n  | nil => simp [{side}Ray,Sym.zero,blank_cons]\n  | cons a r => rfl\n'
    s+='\ndef render (q : Q) (p : Pos) (a : Sym) (l r : List Sym) : Prim :=\n  match p with\n'
    for i in range(w):
        s+=f'  | .p{i} => ⟨q,'+ray([f'a.b{j}' for j in reversed(range(i))],'leftRay l')+','+ray([f'a.b{j}' for j in range(i,w)],'rightRay r')+'⟩\n'
    body='structure BlockConfig where'+src.split('structure BlockConfig where',1)[1]
    body=body.replace('else .p7','else .p'+str(w-1))
    # Restrict the transition function to its exact width.
    a,b=body.split('    match p,mv.right with\n',1)
    _,rest=b.split('\ndef blockExit',1)
    a+='    match p,mv.right with\n'
    for i in range(w):
        a+=f'    | .p{i},false => '+('return ⟨1,mv.next,false,w⟩' if i==0 else f'more .p{i-1}')+'\n'
        a+=f'    | .p{i},true => '+('return ⟨1,mv.next,true,w⟩' if i==w-1 else f'more .p{i+1}')+'\n'
    body=a+'\ndef blockExit'+rest
    a,b=body.split('        simp [Sym.read] at hm\n',1)
    cases,rest=b.split('\ntheorem macro_sound',1)
    cases=re.split(r'(?m)^      · ',cases)[1:]
    assert len(cases)==16
    body=a+'        simp [Sym.read] at hm\n'+''.join('      · '+x for x in cases[:2*w-1]+cases[-1:])+'\ntheorem macro_sound'+rest
    body=body.replace('12289',str(6*w*A+1))
    (out/f'OneLBWideBlock{w}.lean').write_text((s+'\n'+body).replace('BB6.Agent1WideBlock',N))
    sparse=files['WideSparse.lean'].replace('BB6.Agent1WideBlock',N).replace('import WideBlock',f'import OneLBWideBlock{w}')
    sparse=re.sub(r'\b1536\b',str(6*A),sparse)
    sparse=re.sub(r'\b256\b',str(A),sparse)
    (out/f'OneLBWideSparse{w}.lean').write_text(sparse)

for w in sorted({manifest[k][1][1] for k in ids}):make_block(w)
# Generate each witness with the original sparse emitter, making explicit only
# the table, width, search recipe, namespaces, and reflection orientation.
(out/'widegraph.py').write_text(files['widegraph.py'])
os.chdir(out)
sys.path.insert(0,str(out))
for k in ids:
    T,(_,w,cap,mod,runs,flip,phase)=manifest[k]
    A=2**w;name='OneLBWide'+k
    e=files['emit_wide.py']
    e=re.sub(r'^T=.*$',f'T={T}',e,flags=re.M)
    e=e.replace('generate(T,8,1,2,3,True,100000,True)',f'generate(T,{w},{cap},{mod},{runs},{flip},100000,{phase})')
    e=e.replace('BB6.Agent1WideBlock.',f'BB6.Agent3OneLBWide{w}.')
    e=e.replace("name='E0OneRD4267'",f"name='{name}'")
    e=e.replace('import WideSparse',f'import OneLBWideSparse{w}')
    e=re.sub(r'\b256\b',str(A),e)
    # Push/auxiliary keys fit A, but control keys are 2*q+d (0..11).
    # Use an independent pair radix K >= 12; otherwise w=2,3
    # silently alias control keys and corrupt packed rows.
    K=max(A,16)
    e=e.replace(f'A={A};K={A}',f'A={A};K={K}')
    e=e.replace(f'(x%{A},x/{A})',f'(x%{K},x/{K})')
    e=e.replace('pairbits=8+',f'pairbits={max(w,4)}+').replace('ebits=8+',f'ebits={w}+')
    assert f'A={A};K={K}' in e and f'(x%{K},x/{K})' in e
    if not flip:
        e=e.replace('BB6Coverage.FAR.reflectPartial ctr =','ctr =')
        e=e.replace('BB6Coverage.FAR.reflectNever m (BB6BlockFAR.transfer_never machine _ (by simpa only [← same] using BB6Coverage.FAR.reflectCompatible ctr m hm) forever)','BB6BlockFAR.transfer_never machine m (by simpa only [← same] using hm) forever')
    exec(compile(e,f'<emit {k}>','exec'),{'__name__':'__main__'})
