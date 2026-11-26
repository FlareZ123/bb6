import Raw54RAClosedCore
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent8Raw54.ZeroLFBinary
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent8Raw54.RAClosed
inductive V | m35 | m37 | m38 | m40 | m41 | m42 | m59
def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => none
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => match v with
    | .m35 => some (some ⟨false,false,5⟩)
    | .m37 => some (some ⟨false,true,0⟩)
    | .m38 => some (some ⟨true,false,5⟩)
    | .m40 => some (some ⟨true,true,0⟩)
    | .m41 => some (some ⟨true,true,4⟩)
    | .m42 => some (some ⟨true,true,5⟩)
    | .m59 => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => match v with
    | .m35 => some (some ⟨false,true,0⟩)
    | .m37 => some (some ⟨false,true,0⟩)
    | .m38 => some (some ⟨false,true,0⟩)
    | .m40 => some (some ⟨false,true,0⟩)
    | .m41 => some (some ⟨false,true,0⟩)
    | .m42 => some (some ⟨false,true,0⟩)
    | .m59 => some (some ⟨true,false,0⟩)
  | 5,true => match v with
    | .m35 => some (some ⟨true,true,5⟩)
    | .m37 => some (some ⟨true,true,5⟩)
    | .m38 => some (some ⟨true,true,5⟩)
    | .m40 => some (some ⟨true,true,5⟩)
    | .m41 => some (some ⟨true,true,5⟩)
    | .m42 => some (some ⟨true,true,5⟩)
    | .m59 => some (some ⟨false,true,5⟩)
  | _,_ => none
def anchor (v : V) : List Bool := match v with
  | .m35 => [false,true,false,true,true,false]
  | .m37 => [false,true,false,true,true,false]
  | .m38 => [false,true,true,false,true,true,false]
  | .m40 => [false,true,true,false]
  | .m41 => [false,true,true,false,true,true,false]
  | .m42 => [false,true,true,false,true,true,false]
  | .m59 => [false,true,false,true,true,false,true]
def entryTime (v : V) : Nat := match v with
  | .m35 => 30
  | .m37 => 28
  | .m38 => 31
  | .m40 => 30
  | .m41 => 31
  | .m42 => 29
  | .m59 => 34
def exitCost (v : V) : Nat := match v with
  | .m35 => 3
  | .m37 => 3
  | .m38 => 3
  | .m40 => 3
  | .m41 => 3
  | .m42 => 3
  | .m59 => 5
def z (n : Nat) : List Bool := rep [false] n
def o (n : Nat) : List Bool := rep [true] n
def enc : List Bool → List Bool
  | [] => []
  | b::bs => [b,b] ++ enc bs

def A (v : V) (bs : List Bool) : Z0 := ⟨0,false::anchor v,false::enc bs⟩
def C (v : V) (n : Nat) (bs : List Bool) : Z0 := match bs with
  | [] => ⟨2,false::(o (2*n+2) ++ anchor v),[]⟩
  | b::cs => ⟨2,b::(o (2*n+2) ++ anchor v),b::enc cs⟩
def init (v : V) : List Bool := match v with | .m40 => [false,true] | _ => [true]
theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (A v (init v)) := by cases v <;> rfl

theorem enter (v : V) (bs : List Bool) : run0 (table v) 2 (A v bs) = some (C v 0 bs) := by
  cases v <;> cases bs <;> rfl

theorem transfer (v : V) (n : Nat) (bs : List Bool) : run0 (table v) 2 (C v n (true::bs)) = some (C v (n+1) bs) := by
  have hn : 2*(n+1)+2 = 2*n+2+2 := by omega
  cases bs <;> simp only [C,enc,hn,show 2*n+2+2=2+ (2*n+2) by omega,o,rep,List.cons_append,List.nil_append] <;> cases v <;> rfl

theorem cBlank (v : V) (L : List Bool) :
    run0 (table v) 4 ⟨2,[false,true,true] ++ L,[]⟩ = some ⟨4,[true] ++ L,[false,true,true]⟩ := by cases v <;> rfl

theorem cZero (v : V) (L T : List Bool) :
    run0 (table v) 4 ⟨2,[false,true,true] ++ L,false::T⟩ = some ⟨4,[true] ++ L,[false,true,true] ++ T⟩ := by cases v <;> rfl

theorem eraseOne (v : V) (L R : List Bool) :
    run0 (table v) 1 ⟨4,true::L,R⟩ = some ⟨4,L,false::R⟩ := by cases v <;> rfl

theorem exit (v : V) (T : List Bool) :
    run0 (table v) (exitCost v) ⟨4,anchor v,[false,false] ++ T⟩ = some ⟨0,false::anchor v,false::T⟩ := by cases v <;> rfl

theorem z_add (a b : Nat) : z (a+b) = z a ++ z b := by
  unfold z
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add,rep,rep,ih,List.append_assoc]

theorem finish (v : V) (n : Nat) (T : List Bool) :
    run0 (table v) (2*n+1+exitCost v) ⟨4,o (2*n+1) ++ anchor v,[false,true,true] ++ T⟩ =
      some ⟨0,false::anchor v,z (2*n+1) ++ [true,true] ++ T⟩ := by
  have h := sweepL (table v) 4 [] [] [true] [false] 1 (by
    intro L R; simpa only [List.nil_append,List.cons_append] using eraseOne v L R) (2*n+1) (anchor v) ([false,true,true] ++ T)
  have h' : run0 (table v) (2*n+1) ⟨4,o (2*n+1) ++ anchor v,[false,true,true] ++ T⟩ =
      some ⟨4,anchor v,[false,false] ++ (z (2*n) ++ [true,true] ++ T)⟩ := by
    have h0 : z (2*n+1) ++ ([false,true,true] ++ T) = [false,false] ++ (z (2*n) ++ [true,true] ++ T) := by
      have h1 : z (2*n+1) ++ [false] = z (2*n+2) := by change z (2*n+1) ++ z 1 = z (2*n+2); rw [← z_add]
      rw [show [false,true,true] ++ T = [false] ++ ([true,true] ++ T) by rfl,← List.append_assoc,h1,show 2*n+2=2+2*n by omega,z_add]
      simp only [List.append_assoc]; rfl
    have hh : run0 (table v) (2*n+1) ⟨4,o (2*n+1) ++ anchor v,[false,true,true] ++ T⟩ = some ⟨4,anchor v,z (2*n+1) ++ ([false,true,true] ++ T)⟩ := by
      simpa only [Nat.one_mul,List.nil_append,o,z] using h
    rw [h0] at hh
    exact hh
  have he := exit v (z (2*n) ++ [true,true] ++ T)
  have hh := join0 h' he
  simpa only [z,show 2*n+1=1+2*n by omega,rep,List.cons_append,List.nil_append] using hh

theorem zeros_enc (n : Nat) : enc (List.replicate n false) = z (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,enc,ih,show 2*(n+1)=2+2*n by omega,z_add]; rfl

theorem enc_append (a b : List Bool) : enc (a++b)=enc a++enc b := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [enc,ih,List.append_assoc]

theorem resetBlank (v : V) (n : Nat) : run0 (table v) (4+(2*n+1+exitCost v)) (C v n []) = some (A v (List.replicate n false ++ [true])) := by
  have h := cBlank v (o (2*n) ++ anchor v)
  have h' : run0 (table v) 4 (C v n []) = some ⟨4,o (2*n+1) ++ anchor v,[false,true,true]⟩ := by
    simpa only [C,o,show 2*n+2=2+2*n by omega,show 2*n+1=1+2*n by omega,rep,List.cons_append,List.nil_append] using h
  have he := finish v n []
  have hh := join0 h' he
  simpa only [A,enc_append,zeros_enc,enc,z,show 2*n+1=1+2*n by omega,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hh

theorem resetZero (v : V) (n : Nat) (bs : List Bool) : run0 (table v) (4+(2*n+1+exitCost v)) (C v n (false::bs)) = some (A v (List.replicate n false ++ true::bs)) := by
  have h := cZero v (o (2*n) ++ anchor v) (enc bs)
  have h' : run0 (table v) 4 (C v n (false::bs)) = some ⟨4,o (2*n+1) ++ anchor v,[false,true,true] ++ enc bs⟩ := by
    simpa only [C,o,show 2*n+2=2+2*n by omega,show 2*n+1=1+2*n by omega,rep,List.cons_append,List.nil_append] using h
  have he := finish v n (enc bs)
  have hh := join0 h' he
  simpa only [A,enc_append,zeros_enc,enc,z,show 2*n+1=1+2*n by omega,rep,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using hh

theorem carry (v : V) (bs : List Bool) (n : Nat) : ∃ t out, 0 < t ∧ run0 (table v) t (C v n bs) = some (A v out) := by
  induction bs generalizing n with
  | nil => exact ⟨_,_,by omega,resetBlank v n⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨_,_,by omega,resetZero v n bs⟩
    | true =>
      obtain ⟨t,out,ht,h⟩ := ih (n+1)
      exact ⟨2+t,out,by omega,join0 (transfer v n bs) h⟩

theorem closed (v : V) (bs : List Bool) : ∃ t out, 0 < t ∧ run0 (table v) t (A v bs) = some (A v out) := by
  obtain ⟨t,out,ht,h⟩ := carry v bs 0
  exact ⟨2+t,out,by omega,join0 (enter v bs) h⟩
theorem never (v : V) (M : Machine) (h : compatible (table v) M) : NeverHalts M :=
  neverOfSection (table v) (List Bool) (A v) (init v) (entryTime v) (entry v) (closed v) M h
#print axioms never
end BB6.Agent8Raw54.ZeroLFBinary
