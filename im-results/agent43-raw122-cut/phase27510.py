"""Generate a proof of a three-phase recurrent family (untrusted discovery,
Lean checks all local steps and universal sweeps)."""
from pathlib import Path
from functools import lru_cache
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/"agent31-three-hole-tnf"))
import generate_sweeps as pump
pump.local=lru_cache(maxsize=200000)(pump.local)
sys.path.insert(0,str(ROOT.parent/"agent47-raw114-cut"))
import multi_sweep as m

ROW="1RB0LA_1RC---_0RD0RF_1LD1RE_1LA0LF_1RA1RE"
p=pump.parse(ROW)
ps=['0110'+'1'*19+'0','0110'+'1'*11+'0'+'1'*7+'0','0110'+'1'*7+'0'+'1'*13+'0']
D=[3,2,4]
ns='BB6Coverage.Agent31Pump.Raw122Phases27510'
def bits(w):return '['+','.join('true' if x=='1' else 'false' for x in w)+']'
def word(w,n='n'):return ' ++ '.join(f'rep {bits(x.word)} ({n})' if isinstance(x,m.Rep) else bits(x) for x in w.parts) or '[]'
def cfg(c,n='n'):return f'⟨{c.q},{word(c.l,n)},{word(c.r,n)}⟩'
def cf(q,l,r):return f'⟨{q},{l},{r}⟩'
def app(*a):return ' ++ '.join(a)
def w(s,k=0):return m.Word.of(s+'111110'*k,m.Rep('111110'),'1111')
def tab(p):return 'def table : PartialMachine := fun s => match s.1.val,s.2 with\n'+ '\n'.join(f'  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)' for i,a in enumerate(p) if a!='---')+'\n  | _,_ => none'
SIMP='List.append_assoc,List.nil_append,List.append_nil,List.cons_append'
def generate(output=ROOT/'Raw122Phases27510.lean'):
    ls=['import Raw122Counter3708','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper',tab(p)]
    for i in range(3):
        ls.append(f'def family{i} (n : Nat) : Z0 := {cfg(m.Config(1,w(ps[i]),m.Word()))}')
    t,k=15250,21
    ls.append(f'theorem entry : run0 table {t} ⟨0,[],[]⟩ = some (family0 {k}) := by rfl')
    for i,d in enumerate(D):
        st=m.Config(1,w(ps[i]),m.Word());tg=m.Config(1,w(ps[(i+1)%3],d),m.Word())
        hist,last=m.execute(p,st,tg,3000)
        seg=[];j=0
        while j<len(hist):
            h=hist[j]
            if h[0]=='step':
                l=j+1
                while l<len(hist) and hist[l][0]=='step':l+=1
                seg.append(('fixed',h[1],hist[l-1][2],l-j));j=l
            else:seg.append(h);j+=1
        costs=[]
        for j,h in enumerate(seg):
            typ,c,e,v=h[:4];name=f'p{i}_{j}'
            if typ=='fixed':
                ls.append(f'theorem {name} (n : Nat) : run0 table {v} {cfg(c)} = some {cfg(e)} := by rfl')
                costs.append(str(v));continue
            _,_,_,v,side,I,O,pre,op,L,R=h
            if side=='L':
                lp,rp=pre,op;src=cf(c.q,app(bits(lp),bits(I),'L'),app(bits(rp),'R'));dst=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(O),'R'))
            else:
                lp,rp=op,pre;L,R=R,L;src=cf(c.q,app(bits(lp),'L'),app(bits(rp),bits(I),'R'));dst=cf(c.q,app(bits(lp),bits(O),'L'),app(bits(rp),'R'))
            ls.append(f'theorem local{i}_{j} (L R : List Bool) : run0 table {v} {src} = some {dst} := by rfl')
            ls.append(f'theorem {name} (n : Nat) : run0 table ({v}*n) {cfg(c)} = some {cfg(e)} := by\n  simpa only [{SIMP}] using sweep{side} table {c.q} {bits(lp)} {bits(rp)} {bits(I)} {bits(O)} {v} local{i}_{j} n ({word(L)}) ({word(R)})')
            costs.append(f'{v}*n')
        cur=last.l
        ls.append(f'theorem finish{i} (n : Nat) : {word(cur)} = {word(tg.l)} := by\n  calc')
        for a,b,pre,suf,ch,block in cur.normalize()[1]:
            ls.append(f'    {word(a)} = {word(b)} := by\n      simpa only [{SIMP}] using moveCut {word(pre)} {word(suf)} {bits(block)} {str(ch=="1").lower()} n')
            if b==tg.l:break
        else:raise RuntimeError('missing cut')
        A=sum(h[3] for h in seg if h[0]=='fixed');B=sum(h[3] for h in seg if h[0]=='loop')
        assert (A,B)==[(738,156),(466,104),(1102,208)][i]
        proof=f'theorem phase{i} (n : Nat) : run0 table ({A}+{B}*n) (family{i} n) = some (family{(i+1)%3} (n+{d})) := by\n'
        proof+=f'  have h0 := p{i}_0 n\n'
        for j in range(1,len(seg)):proof+=f'  have h{j} := join0 h{j-1} (p{i}_{j} n)\n'
        proof+=f'  rw [finish{i} n] at h{len(seg)-1}\n  rw [show {"+".join(costs)} = {A}+{B}*n by omega] at h{len(seg)-1}\n  simpa only [family{i},family{(i+1)%3},rep,{SIMP}] using h{len(seg)-1}'
        ls.append(proof)
    ls.append(f'''theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply Raw122Counter3708.never_of_recurrent table (fun z => ∃ n, z = family0 n ∨ z = family1 n ∨ z = family2 n) {t} (family0 {k}) entry ⟨{k},Or.inl rfl⟩ _ m hm
  intro z hz
  obtain ⟨n,h⟩ := hz
  rcases h with rfl | rfl | rfl
  · exact ⟨738+156*n,family1 (n+3),by omega,phase0 n,n+3,Or.inr (Or.inl rfl)⟩
  · exact ⟨466+104*n,family2 (n+2),by omega,phase1 n,n+2,Or.inr (Or.inr rfl)⟩
  · exact ⟨1102+208*n,family0 (n+4),by omega,phase2 n,n+4,Or.inl rfl⟩
#print axioms never
end {ns}
''')
    output.write_text('\n\n'.join(ls))
    return output
if __name__=='__main__':generate()
