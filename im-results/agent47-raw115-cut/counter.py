"""Generate explicit Lean certificates for the six counter-return holdouts."""
from pathlib import Path
import sys
from functools import lru_cache
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent31-three-hole-tnf'))
sys.path.insert(0,str(ROOT.parent/'agent47-raw114-cut'))
import generate_sweeps as pump
import multi_sweep as m
pump.local=lru_cache(maxsize=200000)(pump.local)
R=m.Rep; W=m.Word.of; C=m.Config
SIMP='List.append_assoc,List.cons_append,List.nil_append,List.append_nil'
def bits(s):
    assert set(s)<=set('01')
    return '['+','.join('true' if b=='1' else 'false' for b in s)+']'
def app(*xs):
    return ' ++ '.join('('+x+')' for x in xs if x!='[]') or '[]'
def literal(s):
    if 'X' in s:
        assert s.endswith('X') and s.count('X')==1
        return app(bits(s[:-1]),'X')
    return bits(s)
def word(w):
    return app(*(f'rep {bits(x.word)} n' if isinstance(x,R) else literal(x) for x in w.parts))
def cfg(c):return f'⟨{c.q},{word(c.l)},{word(c.r)}⟩'
def eqword(name,a,b,params):
    aa,s=a.normalize();bb,t=b.normalize();assert aa==bb
    while s and t and s[-1]==t[-1]:s.pop();t.pop()
    ls=[f'theorem {name} {params} : {word(a)} = {word(b)} := by','  calc']
    for _,v,pre,suf,z,P in s:
        ls.append(f'    _ = {word(v)} := by simpa only [{SIMP}] using congrArg (fun w : List Bool => {app(word(pre),"w",word(suf))}) (rotate {str(z=="1").lower()} {bits(P)} n)')
    for v,_,pre,suf,z,P in reversed(t):
        ls.append(f'    _ = {word(v)} := by symm; simpa only [{SIMP}] using congrArg (fun w : List Bool => {app(word(pre),"w",word(suf))}) (rotate {str(z=="1").lower()} {bits(P)} n)')
    return '\n'.join(ls)
def macro(p, name, st, target, opaque, expected):
    res=m.execute(p,st,target,1000);assert res
    hist,last=res;seg=[];j=0
    while j<len(hist):
        x=hist[j]
        if x[0]=='step':
            k=j+1
            while k<len(hist) and hist[k][0]=='step':k+=1
            seg.append(('fixed',x[1],hist[k-1][2],k-j));j=k
        else:seg.append(x);j+=1
    a=sum(x[3] for x in seg if x[0]=='fixed');b=sum(x[3] for x in seg if x[0]=='loop');assert (a,b)==expected,(a,b,expected)
    params='(n : Nat)'+(' (X : List Bool)' if opaque else '')
    args='n X' if opaque else 'n'
    ls=[];costs=[]
    for j,x in enumerate(seg):
        typ,c,d,k=x[:4];phase=f'{name}Phase{j}'
        if typ=='fixed':
            ls.append(f'theorem {phase} {params} : run0 table {k} {cfg(c)} = some {cfg(d)} := by rfl');costs.append(str(k));continue
        _,_,_,k,side,I,O,pre,op,tail,ot=x
        if side=='L':
            lp,rp=pre,op;L,RR=tail,ot
            src=f'⟨{c.q},{app(bits(lp),bits(I),"L")},{app(bits(rp),"RR")}⟩'
            dst=f'⟨{c.q},{app(bits(lp),"L")},{app(bits(rp),bits(O),"RR")}⟩'
        else:
            lp,rp=op,pre;L,RR=ot,tail
            src=f'⟨{c.q},{app(bits(lp),"L")},{app(bits(rp),bits(I),"RR")}⟩'
            dst=f'⟨{c.q},{app(bits(lp),bits(O),"L")},{app(bits(rp),"RR")}⟩'
        local=f'{name}Local{j}'
        ls.append(f'theorem {local} (L RR : List Bool) : run0 table {k} {src} = some {dst} := by rfl')
        ls.append(f'theorem {phase} {params} : run0 table ({k}*n) {cfg(c)} = some {cfg(d)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {k} {local} n ({word(L)}) ({word(RR)})')
        costs.append(f'{k}*n')
    join=f'({name}Phase0 {args})'
    for j in range(1,len(seg)):join=f'(join0 {join} ({name}Phase{j} {args}))'
    proof=[f'theorem {name} {params} : run0 table ({a}+{b}*n) {cfg(st)} = some {cfg(target)} := by',f'  have H := {join}']
    for suff,x,y in [('L',last.l,target.l),('R',last.r,target.r)]:
        if x!=y:
            nm=name+'Final'+suff;ls.append(eqword(nm,x,y,params));proof.append(f'  rw [{nm} {args}] at H')
    proof.append(f"  rw [show {'+'.join(costs)}={a}+{b}*n by omega] at H")
    proof.append('  exact H');ls.append('\n'.join(proof));return '\n\n'.join(ls)

def generate(i,p):
    header='import Raw115CounterBase\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nnamespace BB6Coverage.Agent31Pump.Raw115Counter'+str(i)+'\nopen BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase\n'
    ls=[header,pump.tab(p)]
    if i!=9:
        k=3 if i in (2,3) else 1;e='1' if i in (5,6) else '';end={2:8,3:8,4:8,5:11,6:13}[i];seed={2:1,3:1,4:1,5:5,6:4}[i];entry={2:3,3:3,4:3,5:58,6:39}[i]
        rc={2:(27,32),3:(21,24),4:(21,8),5:(26,8),6:(49,16)}[i]
        st=C(3,W('001010',R('1010'),'11X'),W());ta=C(3,W('0010101010',R('1010'),'X'),W())
        ls.append(macro(p,'transferSucc',st,ta,True,(22,8)))
        st=C(3,W('001010',R('1010'*k),e),W());ta=C(3,W('00'+'1'*(end-len(e)),R('1'*(4*k)),e),W())
        ls.append(macro(p,'resetCore',st,ta,False,rc))
        ls.append(f'''def state (a b : Nat) : Z0 := ⟨3,[false,false] ++ rep [true,false,true,false] a ++ rep [true,true] b ++ {bits(e)},[]⟩
theorem transfer (a b : Nat) : run0 table (14+8*a) (state a (b+1)) = some (state (a+1) b) := by
  cases a with
  | zero => rfl
  | succ n =>
    have H := transferSucc n (rep [true,true] b ++ {bits(e)})
    rw [show 14+8*(n+1)=22+8*n by omega]
    simpa only [state,rep,{SIMP}] using H
''')
        ls.append(f'''theorem reset (n : Nat) : run0 table ({rc[0]}+{rc[1]}*n) (state ({k}*n+1) 0) = some (state 0 ({2*k}*n+{end//2})) := by
  have H := resetCore n
  have hL := rep_group [true,false,true,false] {k} n
  have hR := rep_group [true,true] {2*k} n
  change rep {bits('1010'*k)} n = rep [true,false,true,false] ({k}*n) at hL
  change rep {bits('1'*(4*k))} n = rep [true,true] ({2*k}*n) at hR
  rw [hL,hR] at H
  unfold state
  rw [Nat.add_comm ({2*k}*n) {end//2},rep_add [true,true] {end//2} ({2*k}*n)]
  simpa only [state,rep,{SIMP}] using H
''')
        ls.append(f'''theorem drain (a b : Nat) : ∃ t, run0 table t (state a b) = some (state (a+b) 0) := by
  induction b generalizing a with
  | zero => exact ⟨0, by simp [run0]⟩
  | succ b ih =>
    obtain ⟨t, ht⟩ := ih (a+1)
    exact ⟨14+8*a+t, by simpa only [Nat.add_assoc,Nat.add_comm 1 b] using join0 (transfer a b) ht⟩
''')
        good='0 < b ∧ b % 3 = 1' if k==3 else '0 < b'
        arg='b/3' if k==3 else 'b-1'
        ls.append(f'''def good (b : Nat) : Prop := {good}
theorem returnStep (b : Nat) (hb : good b) : ∃ b' t, good b' ∧ 0<t ∧ run0 table t (state 0 b) = some (state 0 b') := by
  obtain ⟨t, ht⟩ := drain 0 b
  simp only [Nat.zero_add] at ht
  unfold good at hb
  have he : b = {k}*({arg})+1 := by omega
  have hd : run0 table t (state 0 b) = some (state ({k}*({arg})+1) 0) := by rw [← he]; exact ht
  exact ⟨{2*k}*({arg})+{end//2},t+({rc[0]}+{rc[1]}*({arg})),by unfold good; omega,by omega,join0 hd (reset ({arg}))⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table (state 0) good {seed} (by unfold good; decide) {entry} (by rfl) returnStep m hm
#print axioms never
''')
    else:
        st=C(1,W('0'+'1'*6,R('1'*6),'01X'),W());ta=C(1,W('0'+'1'*12,R('1'*6),'X'),W())
        ls.append(macro(p,'transferCore',st,ta,True,(32,12)))
        st=C(1,W('0'+'1'*6,R('1'*6)),W());ta=C(1,W('0'+'1'*6+'01'*6,R('01'*3)),W())
        ls.append(macro(p,'resetCore',st,ta,False,(121,36)))
        ls.append(f'''def state (a b : Nat) : Z0 := ⟨1,[false] ++ rep [true,true,true,true,true,true] (a+1) ++ rep [false,true] b,[]⟩
theorem transfer (a b : Nat) : run0 table (32+12*a) (state a (b+1)) = some (state (a+1) b) := by
  simpa only [state,rep,{SIMP}] using transferCore a (rep [false,true] b)
theorem reset (n : Nat) : run0 table (121+36*n) (state n 0) = some (state 0 (3*n+6)) := by
  have H := resetCore n
  have hR := rep_group [false,true] 3 n
  change rep {bits('01'*3)} n = rep [false,true] (3*n) at hR
  rw [hR] at H
  unfold state
  rw [Nat.add_comm (3*n) 6,rep_add [false,true] 6 (3*n)]
  simpa only [state,rep,{SIMP}] using H
theorem drain (a b : Nat) : ∃ t, run0 table t (state a b) = some (state (a+b) 0) := by
  induction b generalizing a with
  | zero => exact ⟨0, by simp [run0]⟩
  | succ b ih =>
    obtain ⟨t, ht⟩ := ih (a+1)
    exact ⟨32+12*a+t, by simpa only [Nat.add_assoc,Nat.add_comm 1 b] using join0 (transfer a b) ht⟩
def good (b : Nat) : Prop := 0 < b
theorem returnStep (b : Nat) (hb : good b) : ∃ b' t, good b' ∧ 0<t ∧ run0 table t (state 0 b) = some (state 0 b') := by
  obtain ⟨t, ht⟩ := drain 0 b
  simp only [Nat.zero_add] at ht
  exact ⟨3*b+6,t+(121+36*b),by unfold good; omega,by omega,join0 ht (reset b)⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table (state 0) good 1 (by unfold good; decide) 50 (by rfl) returnStep m hm
#print axioms never
''')
    ls.append('end BB6Coverage.Agent31Pump.Raw115Counter'+str(i))
    return '\n\n'.join(x for x in ls if x)+'\n'

def main():
    for i,row in enumerate((ROOT/'hard.txt').read_text().splitlines()):
        if i in (2,3,4,5,6,9):
            (ROOT/f'Raw115Counter{i}.lean').write_text(generate(i,pump.parse(row)))

if __name__=='__main__':
    main()
