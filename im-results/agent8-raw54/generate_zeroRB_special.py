"""Emit the two extended counter proofs for frozen ZeroRB misses 162 and 393."""
from generate_digit_sections import M,C,w,find,prove
from pathlib import Path

def head(M0,i,imports,extra=''):
 ns=f'BB6.Agent8Raw54.ZeroRB.M{i}'
 s=[f'import {imports}','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6Coverage.Agent31Pump'+extra,'def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
 for j,a in enumerate(M0.a):
  if a=='---':continue
  b,r,q=a;s.append(f'  | {j//2},{str(bool(j%2)).lower()} => some (some ⟨{str(b=="1").lower()},{str(r=="R").lower()},{ord(q)-65}⟩)')
 s.append('  | _,_ => none')
 return s

def emit162(rows,out):
 M0=M(rows[162]);L,m='010111010','011';d=['0000000','1110000','0000011','1110011']
 s=head(M0,162,'Raw54RAClosedCore')
 for j in range(3):
  a=C(4,L,m+'V'+d[j]+'X',d[3]);b=C(4,L,m+'V'+d[j+1]+'X',d[0]);s.append(prove(f'stop{j}',a,b,find(M0,a,b),True))
 for j,(e,o) in enumerate([('', '111'),('111',d[2])]):
  a=C(4,L,m+'V'+e,d[3]);b=C(4,L,m+'V'+o,d[0]);s.append(prove(f'over{j}',a,b,find(M0,a,b),False))
 s.append('''inductive D where
  | z | o | t | h
  deriving DecidableEq

def digit : D → List Bool
  | .z => '''+w(d[0])+'''
  | .o => '''+w(d[1])+'''
  | .t => '''+w(d[2])+'''
  | .h => '''+w(d[3])+'''

def enc : List D → List Bool
  | [] => []
  | x::xs => digit x ++ enc xs

def ending : Bool → List Bool
  | false => []
  | true => [true,true,true]

def advance : List D → Bool → List D × Bool
  | [], false => ([],true)
  | [], true => ([.t],false)
  | .z::xs, e => (.o::xs,e)
  | .o::xs, e => (.t::xs,e)
  | .t::xs, e => (.h::xs,e)
  | .h::xs, e => let p := advance xs e; (.z::p.1,p.2)

def cost : Nat → List D → Bool → Nat
  | k, [], false => 14*k+18
  | k, [], true => 14*k+26
  | k, .z::_, _ => 14*k+18
  | k, .o::_, _ => 14*k+26
  | k, .t::_, _ => 14*k+18
  | k, .h::xs, e => cost (k+1) xs e

def frame (r : List Bool) : Z0 := ⟨4,'''+w(L)+''','''+w(m)+''' ++ r⟩

theorem carry (k : Nat) (xs : List D) (e : Bool) :
    run0 table (cost k xs e) (frame (rep (digit .h) k ++ enc xs ++ ending e)) =
    some (frame (rep (digit .z) k ++ enc (advance xs e).1 ++ ending (advance xs e).2)) := by
  induction xs generalizing k with
  | nil =>
    cases e
    · simpa only [cost,frame,digit,enc,ending,advance,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using over0 k
    · simpa only [cost,frame,digit,enc,ending,advance,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using over1 k
  | cons x xs ih =>
    cases x
    · simpa only [cost,frame,digit,enc,advance,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using stop0 k (enc xs ++ ending e)
    · simpa only [cost,frame,digit,enc,advance,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using stop1 k (enc xs ++ ending e)
    · simpa only [cost,frame,digit,enc,advance,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using stop2 k (enc xs ++ ending e)
    · have H := ih (k+1)
      simpa only [cost,advance,enc,rep,← rep_snoc (digit .h) k,← rep_snoc (digit .z) k,List.append_assoc] using H

theorem cost_pos (k : Nat) (xs : List D) (e : Bool) : 0 < cost k xs e := by
  induction xs generalizing k with
  | nil => cases e <;> simp only [cost] <;> omega
  | cons x xs ih => cases x <;> simp only [cost]; omega; omega; omega; exact ih (k+1)

def sec (p : List D × Bool) : Z0 := frame (enc p.1 ++ ending p.2)

theorem never (M : Machine) (hm : compatible table M) : NeverHalts M := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection table (List D × Bool) sec ([],false) 47 (by rfl) _ M hm
  intro p
  refine ⟨cost 0 p.1 p.2, advance p.1 p.2, cost_pos 0 p.1 p.2, ?_⟩
  simpa only [sec,rep,List.nil_append] using carry 0 p.1 p.2
#print axioms never
end BB6.Agent8Raw54.ZeroRB.M162''')
 out.joinpath('Raw54ZeroRB162.lean').write_text('\n'.join(s)+'\n')

def emit393(rows,out):
 M0=M(rows[393]);L,m,z,o='010','011','0000','0011'
 s=head(M0,393,'Raw54BinaryShape',' BB6.Agent8Raw54.DigitSection BB6.Agent8Raw54.BinaryShape')
 for name,a,b,tail in [('stop','V'+z+'X','V'+o+'X',True),('over1','V001','V000011',False),('over0succ',o+'V11',o+'V001',False)]:
  a=C(4,L,m+a,o);b=C(4,L,m+b,z);s.append(prove(name,a,b,find(M0,a,b),tail))
 s.append('''def z : List Bool := [false,false,false,false]
def o : List Bool := [false,false,true,true]
def tail : Bool → List Bool
  | false => [true,true]
  | true => [false,false,true]
def sec (p : List Bool × Bool) : Z0 := ⟨4,[false,true,false],[false,true,true] ++ enc z o p.1 ++ tail p.2⟩

theorem closed (p : List Bool × Bool) : ∃ t p', 0 < t ∧ run0 table t (sec p) = some (sec p') := by
  rcases p with ⟨xs,e⟩
  rcases shape xs with ⟨k,ys,rfl⟩ | ⟨k,rfl⟩
  · refine ⟨8*k+20,(rep [false] k ++ true::ys,e),by omega,?_⟩
    simpa only [sec,enc_append,enc_ones,enc_zeros,enc,z,o,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using stop k (enc z o ys ++ tail e)
  · cases e
    · cases k with
      | zero => exact ⟨65,([false],false),by decide,by rfl⟩
      | succ k =>
        refine ⟨8*k+69,(true::rep [false] k,true),by omega,?_⟩
        simpa only [sec,enc_ones,enc_zeros,enc,z,o,tail,rep,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using over0succ k
    · refine ⟨8*k+24,(rep [false] (k+1),false),by omega,?_⟩
      simp only [sec,enc_ones,enc_zeros,z,o,tail]
      have H := over1 k
      simpa only [rep,← rep_snoc [false,false,false,false] k,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using H

theorem never (M : Machine) (hm : compatible table M) : NeverHalts M :=
  BB6.Agent8Raw54.RAClosed.neverOfSection table (List Bool × Bool) sec ([],false) 27 (by rfl) closed M hm
#print axioms never
end BB6.Agent8Raw54.ZeroRB.M393''')
 out.joinpath('Raw54ZeroRB393.lean').write_text('\n'.join(s)+'\n')

def emit(rows,out):
 emit162(rows,out)
 emit393(rows,out)
