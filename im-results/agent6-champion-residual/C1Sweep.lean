import FastFAR
import SweepPumping
import WeightedTNF

namespace BB6.Agent6C1Sweep
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

def hard : PartialMachine := FAR.fromCodes [7,21,11,24,14,8,3,16,12,11,14,1]
def cfg (n : Nat) : Z0 := ⟨0,[true,true],List.replicate n false ++ [true]⟩

theorem rep_single (b : Bool) (n : Nat) : rep [b] n = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,List.replicate_succ,ih]

theorem fill_one (L R : List Bool) :
    run0 hard 3 ⟨0,[true]++L,[]++[false]++R⟩ =
      some ⟨0,[true]++[true]++L,[]++R⟩ := rfl

theorem erase_one (L R : List Bool) :
    run0 hard 1 ⟨2,[]++[true]++L,[]++R⟩ =
      some ⟨2,[]++L,[]++[false]++R⟩ := rfl

theorem turn (L : List Bool) :
    run0 hard 13 ⟨0,true::L,[true]⟩ =
      some ⟨2,[true,true,true,true]++L,[true]⟩ := rfl

theorem restart (R : List Bool) :
    run0 hard 2 ⟨2,[],R⟩ = some ⟨0,[true,true],R⟩ := rfl

theorem repl_add (a b : Nat) (v : Bool) :
    List.replicate (a+b) v = List.replicate a v ++ List.replicate b v := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a+1+b=a+b+1 by omega, List.replicate_succ, List.replicate_succ, ih]; rfl

theorem cycle (n : Nat) : run0 hard (4*n+20) (cfg n) = some (cfg (n+5)) := by
  have h1 := sweepR hard 0 [true] [] [false] [true] 3 fill_one n [true] [true]
  have h1' : run0 hard (3*n) (cfg n) =
      some ⟨0,true::(List.replicate n true++[true]),[true]⟩ := by
    simpa only [cfg,rep_single,List.nil_append,List.cons_append] using h1
  have h2 := turn (List.replicate n true++[true])
  have h2' : run0 hard 13 ⟨0,true::(List.replicate n true++[true]),[true]⟩ =
      some ⟨2,List.replicate (n+5) true,[true]⟩ := by
    rw [show n+5=4+n+1 by omega, repl_add, repl_add]
    rw [List.append_assoc]
    exact h2
  have h3 := sweepL hard 2 [] [] [true] [false] 1 erase_one (n+5) [] [true]
  have h3' : run0 hard (n+5) ⟨2,List.replicate (n+5) true,[true]⟩ =
      some ⟨2,[],List.replicate (n+5) false++[true]⟩ := by
    simpa only [rep_single,List.nil_append,List.append_nil,Nat.one_mul] using h3
  have H := join0 (join0 (join0 h1' h2') h3') (restart (List.replicate (n+5) false++[true]))
  rw [show 3*n+13+(n+5)+2=4*n+20 by omega] at H
  exact H

theorem entry : run0 hard 17 ⟨0,[],[]⟩ = some (cfg 4) := rfl

def family (k : Nat) : Z0 := cfg (4+5*k)

theorem growth (k : Nat) : run0 hard (4*(4+5*k)+20) (family k) = some (family (k+1)) := by
  unfold family
  rw [show 4+5*(k+1)=4+5*k+5 by omega]
  exact cycle _

theorem never (m : Machine) (hm : compatible hard m) : NeverHalts m :=
  never_of_growth hard family 17 (fun k => 4*(4+5*k)+20) entry
    (fun k => by omega) growth m hm

theorem cover (B : Nat) : Cover (WeightedBound B) hard :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))

#print axioms cycle
#print axioms entry
#print axioms never
#print axioms cover
end BB6.Agent6C1Sweep
