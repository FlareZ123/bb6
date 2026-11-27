import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RAUnary
open BB6Coverage BB6Coverage.Agent31Pump

def p : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,1⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,2⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨false,false,1⟩)
  | _ => none

def zeros (n : Nat) := rep [false] n
def ones (n : Nat) := rep [true] n
def family (n : Nat) : Z0 := ⟨0,zeros (n+2),ones (n+2)⟩

theorem first : run0 p 7 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem entry (L R : List Bool) :
    run0 p 4 ⟨0,false::L,true::true::R⟩ = some ⟨2,true::true::true::L,R⟩ := by rfl

theorem right_one (L R : List Bool) :
    run0 p 1 ⟨2,true::L,true::R⟩ = some ⟨2,true::false::L,R⟩ := by rfl

theorem turn (L : List Bool) :
    run0 p 2 ⟨2,true::L,[]⟩ = some ⟨3,false::false::false::L,[]⟩ := by rfl

theorem left_one (L R : List Bool) :
    run0 p 1 ⟨3,false::L,R⟩ = some ⟨3,L,true::R⟩ := by rfl

theorem finish (L R : List Bool) :
    run0 p 2 ⟨3,true::true::L,R⟩ = some ⟨0,false::false::L,R⟩ := by rfl

theorem grow (n : Nat) : run0 p (2*n+11) (family n) = some (family (n+1)) := by
  have h0 := entry (zeros (n+1)) (ones n)
  have h1 := sweepR p 2 [true] [] [true] [false] 1 right_one n (true::true::zeros (n+1)) []
  have h2 := turn (zeros n ++ true::true::zeros (n+1))
  have h3 := sweepL p 3 [] [] [false] [true] 1 left_one (n+3) (true::true::zeros (n+1)) []
  have h4 := finish (zeros (n+1)) (ones (n+3))
  simp only [family,zeros,ones,rep,List.singleton_append] at h0 ⊢
  have h1' : run0 p n ⟨2,true::true::true::zeros (n+1),ones n⟩ =
    some ⟨2,true::(zeros n ++ true::true::zeros (n+1)),[]⟩ := by
      simpa only [Nat.one_mul,List.singleton_append,List.nil_append,List.append_nil,List.cons_append,zeros,ones] using h1
  have h3' : run0 p (n+3) ⟨3,false::false::false::(zeros n ++ true::true::zeros (n+1)),[]⟩ =
    some ⟨3,true::true::zeros (n+1),ones (n+3)⟩ := by
      simpa only [Nat.one_mul,List.nil_append,List.append_nil,zeros,ones,rep,List.singleton_append,List.cons_append] using h3
  have h := join0 (join0 (join0 (join0 h0 h1') h2) h3') h4
  rw [show 4+n+2+(n+3)+2 = 2*n+11 by omega] at h
  simpa only [zeros,ones,rep,List.singleton_append] using h

theorem never : ∀ m, compatible p m → NeverHalts m :=
  never_of_growth p family 7 (fun n => 2*n+11) first (by omega) grow
#print axioms never
end BB6.Agent32Raw42RAUnary
