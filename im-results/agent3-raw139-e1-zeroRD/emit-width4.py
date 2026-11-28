#!/usr/bin/env python3
"""Specialize the original width-three block certificate checker to width four.

Supply a directory containing the original BlockMacro.lean, BlockFAR.lean,
BlockFARBridge.lean sources (e.g. the verified artifact 15175093456 build).
The emitted theorems are elaborated by Lean, with no extra axioms.
"""
from pathlib import Path
import re
import sys
src,out=map(Path,sys.argv[1:]);out.mkdir(parents=True,exist_ok=True)
base=(src/'BlockMacro.lean').read_text()
assert 'macroRun M 145' in base and 'structure Sym where' in base
pos=['p0','p1','p2','p3'];fields=['a','b','c','d']
def nest(bits,tail):
    for bit in reversed(bits):tail=f'cons {bit} ({tail})'
    return tail
sym='structure Sym where\n'+''.join(f'  {f} : Bool\n' for f in fields)+'  deriving DecidableEq, Repr\n\n'
sym+='def Sym.zero : Sym := ⟨false,false,false,false⟩\n\n'
sym+='def Sym.code (s : Sym) : Nat := '+' + '.join(f'{2**i}*s.{f}.toNat' for i,f in enumerate(fields))+'\n\n'
sym+='def Sym.ofCode (n : Nat) : Sym := ⟨'+','.join(f'n/{2**i}%2 == 1' for i in range(4))+'⟩\n\n'
sym+='def symbols : List Sym := (List.range 16).map Sym.ofCode\n\n'
sym+='theorem symbols_complete (s : Sym) : s ∈ symbols := by\n  rcases s with ⟨a,b,c,d⟩\n  cases a <;> cases b <;> cases c <;> cases d <;> decide\n\n'
sym+='inductive Pos where '+' '.join('| '+p for p in pos)+'\n  deriving DecidableEq, Repr\n\n'
sym+='def Sym.read (s : Sym) : Pos → Bool\n'+''.join(f'  | .{p} => s.{f}\n' for p,f in zip(pos,fields))+'\n'
sym+='def Sym.write (s : Sym) (p : Pos) (w : Bool) : Sym :=\n  match p with\n'+''.join(f'  | .{p} => ⟨'+','.join('w' if i==j else 's.'+f for j,f in enumerate(fields))+'⟩\n' for i,p in enumerate(pos))+'\n'
start=base.index('structure Sym where');end=base.index('structure Move where');base=base[:start]+sym+base[end:]
start=base.index('def leftRay');end=base.index('structure BlockConfig')
rays=''
for side,fs in [('left',fields[::-1]),('right',fields)]:
    rays+=f'def {side}Ray : List Sym → Ray\n  | [] => blankRay\n  | a::r => '+nest(['a.'+f for f in fs],side+'Ray r')+'\n\n'
    rays+=f'theorem {side}Ray_unfold (l : List Sym) :\n    {side}Ray l = '+nest(['(l.headD Sym.zero).'+f for f in fs],f'{side}Ray l.tail')+' := by\n  cases l with\n  | nil => simp ['+side+'Ray,Sym.zero,blank_cons]\n  | cons a r => rfl\n\n'
rays+='def render (q : Q) (p : Pos) (a : Sym) (l r : List Sym) : Prim :=\n  match p with\n'
for i,p in enumerate(pos):rays+=f'  | .{p} => ⟨q,'+nest(['a.'+f for f in fields[:i][::-1]],'leftRay l')+','+nest(['a.'+f for f in fields[i:]],'rightRay r')+'⟩\n'
base=base[:start]+rays+'\n'+base[end:]
base=base.replace('if dir then .lo else .hi','if dir then .p0 else .p3')
start=base.index('    match p,mv.right with');end=base.index('\ndef blockExit',start)
steps='    match p,mv.right with\n'
for i,p in enumerate(pos):
    steps+=f'    | .{p},false => '+('return ⟨1,mv.next,false,w⟩' if i==0 else f'more .{pos[i-1]}')+'\n'
    steps+=f'    | .{p},true => '+('return ⟨1,mv.next,true,w⟩' if i==3 else f'more .{pos[i+1]}')+'\n'
base=base[:start]+steps+base[end:]
base=base.replace('145','385') # 6 states * 4 positions * 16 contents + 1
start=base.index('      · subst e',base.index('theorem macroRun_sound'));end=base.index('\ntheorem macro_sound',start)
proof='''      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd]
          rw [leftRay_unfold l]
          cases l <;> simp [rightRay]
'''
for i,p in enumerate(pos):
    for right in [False,True]:
        j=i+(1 if right else -1)
        if not 0<=j<4:continue
        proof+=f'''      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .{pos[j]} (a.write .{p} mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
'''
proof+='''      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd,leftRay]
          rw [rightRay_unfold r]
          cases r <;> rfl
'''
base=base[:start]+proof+base[end:]
(out/'D0LF1BlockMacro4.lean').write_text(base.replace('BB6BlockFAR','BB6BlockFAR4'))
far=(src/'BlockFAR.lean').read_text().replace('import BlockMacro','import D0LF1BlockMacro4').replace('BB6BlockFAR','BB6BlockFAR4')
far=re.sub(r'(?<!\d)48\*l.val\+8\*q.val','96*l.val+16*q.val',far)
far=far.replace('(8*l.val','(16*l.val').replace('x/8','x/16').replace('x%8','x%16').replace('(8*v.val','(16*v.val')
(out/'D0LF1BlockFAR4.lean').write_text(far)
bridge=(src/'BlockFARBridge.lean').read_text().replace('import BlockFAR','import D0LF1BlockFAR4').replace('BB6BlockFAR','BB6BlockFAR4')
(out/'D0LF1BlockFARBridge4.lean').write_text(bridge)
