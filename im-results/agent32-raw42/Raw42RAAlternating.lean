import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RAAlternating
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | (4,false) => some (some ⟨false,false,3⟩)
  | _ => none

def ones (n : Nat) := rep [true] n
def family (n : Nat) : Z0 := ⟨0,[false,false],ones (2*n+2)⟩

theorem first : run0 p 7 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem entry (R : List Bool) :
    run0 p 10 ⟨0,[false,false],true::true::R⟩ = some ⟨1,[],false::true::true::true::R⟩ := by rfl

theorem startR (R : List Bool) :
    run0 p 3 ⟨1,[],false::true::R⟩ = some ⟨1,[false,true],false::R⟩ := by rfl

theorem stepR (L R : List Bool) :
    run0 p 3 ⟨1,false::L,false::true::R⟩ = some ⟨1,false::true::L,false::R⟩ := by rfl

theorem turn (L : List Bool) :
    run0 p 6 ⟨1,false::true::L,[false]⟩ = some ⟨0,false::false::L,[true,true]⟩ := by rfl

theorem stepL (L R : List Bool) :
    run0 p 11 ⟨0,false::false::true::L,true::true::R⟩ = some ⟨0,false::false::L,true::true::true::R⟩ := by rfl

theorem grow (n : Nat) : run0 p (14*(2*n+2)+19) (family n) = some (family (n+1)) := by
  let k := 2*n+2
  have h0 : run0 p 10 (family n) = some ⟨1,[],false::true::ones k⟩ := by
    simpa only [family,ones,k,rep,List.singleton_append] using entry (ones (2*n))
  have h1 := startR (ones k)
  have h2 := sweepR p 1 [false] [false] [true] [true] 3 stepR k [true] []
  have h2' : run0 p (3*k) ⟨1,[false,true],false::ones k⟩ =
      some ⟨1,false::true::ones k,[false]⟩ := by
    simpa only [ones,List.singleton_append,List.append_nil,List.nil_append,rep_snoc [true] k,rep,List.cons_append] using h2
  have h3 := turn (ones k)
  have h4 := sweepL p 0 [false,false] [true,true] [true] [true] 11 stepL k [] []
  have h4' : run0 p (11*k) ⟨0,false::false::ones k,[true,true]⟩ =
      some ⟨0,[false,false],true::true::ones k⟩ := by
    simpa only [ones,List.cons_append,List.nil_append,List.append_nil] using h4
  have h := join0 (join0 (join0 (join0 h0 h1) h2') h3) h4'
  rw [show 10+3+3*k+6+11*k = 14*k+19 by omega] at h
  have hk : 2*(n+1)+2 = k+2 := by dsimp [k]; omega
  unfold family at h ⊢
  rw [hk]
  exact h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 7 (fun n => 14*(2*n+2)+19) first (by omega) grow
#print axioms never
end BB6.Agent32Raw42RAAlternating
