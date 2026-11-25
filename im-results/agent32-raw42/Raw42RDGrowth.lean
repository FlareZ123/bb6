import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RD
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,3⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def ones (n : Nat) := rep [true] n

def family (n : Nat) : Z0 := ⟨1, [], false :: ones (2*n+3)⟩

theorem first : run0 p 9 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem stepR (L R : List Bool) :
    run0 p 3 ⟨1,false::L,false::true::R⟩ = some ⟨1,false::true::L,false::R⟩ := by
  rfl

theorem startR (R : List Bool) :
    run0 p 3 ⟨1,[],false::true::R⟩ = some ⟨1,[false,true],false::R⟩ := by rfl

theorem turn (L : List Bool) :
    run0 p 5 ⟨1,false::L,[false]⟩ = some ⟨1,L,[false,true,true]⟩ := by rfl

theorem stepL (L R : List Bool) :
    run0 p 3 ⟨1,true::L,false::R⟩ = some ⟨1,L,false::true::R⟩ := by rfl

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones,rep]
  | succ a ih =>
    rw [show a+1+b = a+b+1 by omega]
    simp only [ones,rep,List.cons_append,List.nil_append] at *
    rw [ih]

theorem grow (n : Nat) : run0 p (6*(2*n+3)+5) (family n) = some (family (n+1)) := by
  let k := 2*n+2
  have h0 := startR (ones k)
  have h1 := sweepR p 1 [false] [false] [true] [true] 3 stepR k [true] []
  have h2 := turn (ones (k+1))
  have h3 := sweepL p 1 [] [false] [true] [true] 3 stepL (k+1) [] [true,true]
  have h1' : run0 p (3*k) ⟨1,[false,true],false::ones k⟩ =
      some ⟨1,false::ones (k+1),[false]⟩ := by
    simpa [ones,rep_snoc [true] k,rep,List.append_assoc] using h1
  have h3' : run0 p (3*(k+1)) ⟨1,ones (k+1),[false,true,true]⟩ =
      some ⟨1,[],false::ones (k+3)⟩ := by
    rw [ones_add (k+1) 2]
    simpa [ones,rep,List.append_assoc] using h3
  have h := join0 (join0 (join0 h0 h1') h2) h3'
  have hk : 3 + 3*k + 5 + 3*(k+1) = 6*(2*n+3)+5 := by dsimp [k] <;> omega
  rw [hk] at h
  have hn : k+1 = 2*n+3 := by dsimp [k] <;> omega
  have hn' : k+3 = 2*(n+1)+3 := by dsimp [k] <;> omega
  unfold family
  rw [← hn, ← hn']
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 9 (fun n => 6*(2*n+3)+5) first (by omega) grow
#print axioms never
end BB6.Agent32Raw42RD
