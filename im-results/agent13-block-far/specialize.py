from pathlib import Path
import sys,re
root=Path(__file__).resolve().parent
for n in map(int,sys.argv[1:]):
    fs=[f'b{i}' for i in range(n)]; ps=[f'p{i}' for i in range(n)]; k=2**n; ns=f'BB6BlockFAR{n}'
    def vec(x):return '⟨'+','.join(x)+'⟩'
    def ray(bits,tail):
        for b in reversed(bits):tail=f'cons {b} ({tail})'
        return tail
    s=(root/'BlockMacro.lean').read_text(); a=s.index('structure Sym'); z=s.index('structure Move')
    t='structure Sym where\n'+''.join(f'  {f} : Bool\n' for f in fs)+'  deriving DecidableEq, Repr\n\n'
    t+='def Sym.zero : Sym := '+vec(['false']*n)+'\n\n'
    t+='def Sym.code (s : Sym) : Nat := '+' + '.join(f'{2**i}*s.{f}.toNat' for i,f in enumerate(fs))+'\n\n'
    t+='def Sym.ofCode (n : Nat) : Sym := '+vec([f'n/{2**i}%2 == 1' for i in range(n)])+'\n\n'
    t+=f'def symbols : List Sym := (List.range {k}).map Sym.ofCode\n\n'
    if n < 8:
        t+='theorem symbols_complete (s : Sym) : s ∈ symbols := by\n  rcases s with '+vec(fs)+'\n  '+' <;> '.join('cases '+f for f in fs)+' <;> decide\n\n'
    else:
        # Symbolic binary digit inversion: avoid 2^n Boolean case branches
        # and linear list-membership reduction in each branch.
        bounds=''.join(f'  have hb{i} : s.{f}.toNat ≤ 1 := by cases s.{f} <;> decide\n' for i,f in enumerate(fs))
        t+=f'theorem code_lt (s : Sym) : s.code < {k} := by\n'+bounds+'  unfold Sym.code\n  omega\n\n'
        t+='theorem ofCode_code (s : Sym) : Sym.ofCode s.code = s := by\n'+bounds
        for i,f in enumerate(fs):
            t+=f'  have h{i} : (s.code / {2**i} % 2 == 1) = s.{f} := by\n    have he : s.code / {2**i} % 2 = s.{f}.toNat := by\n      unfold Sym.code\n      omega\n    rw [he]\n    cases s.{f} <;> rfl\n'
        t+='  cases s\n  simp only [Sym.ofCode,Sym.mk.injEq]\n  exact '+vec([f'h{i}' for i in range(n)])+'\n\n'
        t+='theorem symbols_complete (s : Sym) : s ∈ symbols := by\n  exact List.mem_map.mpr ⟨s.code,List.mem_range.mpr (code_lt s),ofCode_code s⟩\n\n'
    t+='inductive Pos where '+' '.join('| '+p for p in ps)+'\n  deriving DecidableEq, Repr\n\n'
    t+='def Sym.read (s : Sym) : Pos → Bool\n'+''.join(f'  | .{p} => s.{f}\n' for p,f in zip(ps,fs))+'\n'
    t+='def Sym.write (s : Sym) (p : Pos) (w : Bool) : Sym :=\n  match p with\n'+''.join(f'  | .{p} => '+vec(['w' if j==i else 's.'+f for j,f in enumerate(fs)])+'\n' for i,p in enumerate(ps))+'\n'
    s=s[:a]+t+s[z:];a=s.index('def leftRay');z=s.index('structure BlockConfig')
    t=''
    for direction,fields,x in [('left',fs[::-1],'l'),('right',fs,'r')]:
        t+=f'def {direction}Ray : List Sym → Ray\n  | [] => blankRay\n  | a::r => '+ray(['a.'+f for f in fields],f'{direction}Ray r')+'\n\n'
    for direction,fields,x in [('left',fs[::-1],'l'),('right',fs,'r')]:
        t+=f'theorem {direction}Ray_unfold ({x} : List Sym) :\n    {direction}Ray {x} = '+ray([f'({x}.headD Sym.zero).{f}' for f in fields],f'{direction}Ray {x}.tail')+f' := by\n  cases {x} with\n  | nil => simp [{direction}Ray,Sym.zero,blank_cons]\n  | cons a r => rfl\n\n'
    t+='def render (q : Q) (p : Pos) (a : Sym) (l r : List Sym) : Prim :=\n  match p with\n'
    for i,p in enumerate(ps):t+=f'  | .{p} => ⟨q,'+ray(['a.'+f for f in fs[:i][::-1]],'leftRay l')+','+ray(['a.'+f for f in fs[i:]],'rightRay r')+'⟩\n'
    s=s[:a]+t+'\n'+s[z:];s=s.replace('if dir then .lo else .hi',f'if dir then .p0 else .p{n-1}')
    a=s.index('    match p,mv.right with');z=s.index('\ndef blockExit',a)
    t='    match p,mv.right with\n'
    for i,p in enumerate(ps):
        for d in [False,True]:
            j=i+(1 if d else -1);ds=str(d).lower();t+=f'    | .{p},{ds} => '+(f'return ⟨1,mv.next,{ds},w⟩' if j<0 or j>=n else f'more .p{j}')+'\n'
    s=s[:a]+t+s[z:];a=s.index('      · subst e',s.index('theorem macroRun_sound'));z=s.index('\ntheorem macro_sound',a)
    t=''
    for i,p in enumerate(ps):
        for d in [False,True]:
            j=i+(1 if d else -1)
            if j<0:t+='''      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd]
          rw [leftRay_unfold l]
          cases l <;> simp [rightRay]
'''
            elif j>=n:t+='''      · subst e
        constructor
        · simp
        · simp [run,primStep,render,Sym.write,EntryPos,hm,hd,leftRay]
          rw [rightRay_unfold r]
          cases r <;> rfl
'''
            else:t+=f'''      · obtain ⟨e',he',rfl⟩ := h
        obtain ⟨hpos,hrun⟩ := ih mv.next .p{j} (a.write .{p} mv.write) e' he'
        refine ⟨by simp,?_⟩
        simpa [run,primStep,render,Sym.write,hm,hd] using hrun
'''
    s=s[:a]+t+s[z:];s=s.replace('145',str(6*n*k+1)).replace('BB6BlockFAR',ns).replace('3-cell',f'{n}-cell');(root/f'BlockMacro{n}.lean').write_text(s)
    s=(root/'BlockFAR.lean').read_text().replace('import BlockMacro',f'import BlockMacro{n}').replace('BB6BlockFAR',ns);s=re.sub(r'\b48\b',str(6*k),s);s=re.sub(r'\b8\b',str(k),s);(root/f'BlockFAR{n}.lean').write_text(s)
    for name in ['RangeCheck','BlockFARBridge']:
        s=(root/f'{name}.lean').read_text().replace('import BlockFAR',f'import BlockFAR{n}').replace('BB6BlockFAR',ns);(root/f'{name}{n}.lean').write_text(s)
