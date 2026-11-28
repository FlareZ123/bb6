import Raw14037DPhase
import Raw140Framed
namespace Raw14037DTerm
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem scanFourAny (a : Nat) (X Y : List Sym) :
    Reach base (boundary 2 true (S 4::X) (U 4 a ++ S 4::Y))
      (boundary 2 true (S 4::(U 5 a ++ X)) (S 4::Y)) := by
  induction a generalizing X with
  | zero => exact Reach.refl base _
  | succ a ih =>
    cases a with
    | zero => exact ⟨_,Raw140Double.forward4_4 X Y⟩
    | succ a =>
      have h0 := Raw140Double.forward4_4 X (U 4 a ++ S 4::Y)
      have h1 := ih (S 5::X)
      simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using Reach.trans ⟨_,h0⟩ h1

theorem forwardEnd (X Y : List Sym) :
    run base 17 (boundary 2 true (S 4::X) (S 4::Y)) = some (boundary 4 true (S 0::S 5::X) Y) := by
  exact Raw140Framed.execute_sound base true true 5 17
    ⟨2,true,[S 4],[S 4]⟩ ⟨4,true,[S 0,S 5],[]⟩ X Y (by decide +kernel)

theorem frontAny (a : Nat) (X Y : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ Y))
      (boundary 4 true (S 0::(U 5 (a+1) ++ X)) Y) := by
  have hR : U 4 (a+1) ++ Y=U 4 a ++ S 4::Y := by simp only [U,List.replicate_succ',List.append_assoc,List.singleton_append]
  have h0 := Raw140Double.lift_4 X (U 4 a ++ Y)
  have h1 := scanFourAny a X Y
  have h2 := forwardEnd (U 5 a ++ X) Y
  rw [←hR] at h1
  exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩

structure Rule where
  src : List Sym
  extra5 : Nat
  extra4 : Nat
  dst : List Sym
  fuel : Nat
  time : Nat
  deriving DecidableEq, Repr

def Rule.valid (r : Rule) : Prop :=
  Raw140Framed.execute base true false r.fuel ⟨4,true,[S 0],r.src⟩ =
    some (r.time,⟨3,false,U 5 r.extra5,U 4 r.extra4 ++ r.dst⟩)
instance (r : Rule) : Decidable r.valid := inferInstanceAs (Decidable (_ = _))

theorem Rule.sound (r : Rule) (hr : r.valid) (a : Nat) (X : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ r.src))
      (boundary 3 false X (U 4 (a+1+r.extra5+r.extra4) ++ r.dst)) := by
  have h0 := frontAny a X r.src
  have h1 := Raw140Framed.execute_sound base true false r.fuel r.time
    ⟨4,true,[S 0],r.src⟩ ⟨3,false,U 5 r.extra5,U 4 r.extra4 ++ r.dst⟩ (U 5 (a+1) ++ X) [] hr
  simp only [Raw140Framed.prim,List.cons_append,List.nil_append,List.append_nil,ite_true,ite_false,Bool.false_eq_true] at h1
  rw [merge] at h1
  have h2 := sweepL base 3 (S 5) (S 4) 3 (r.extra5+(a+1)) X (U 4 r.extra4 ++ r.dst) (by rfl)
  rw [merge,show r.extra5+(a+1)+r.extra4=a+1+r.extra5+r.extra4 by omega] at h2
  exact Reach.trans (Reach.trans h0 ⟨_,h1⟩) ⟨_,h2⟩

def rules : List Rule := [
  ⟨[S 2,S 3,S 2],3,0,[S 0,S 5],27,77⟩,
  ⟨[S 2,S 3,S 1,S 5],4,1,[],20,58⟩,
  ⟨[S 2,S 3,S 2,S 5],4,0,[S 2,S 2,S 1],36,102⟩,
  ⟨[S 2,S 3,S 2,S 4,S 2],3,1,[S 2,S 2,S 1],33,93⟩,
  ⟨[S 2,S 3,S 5,S 2,S 2,S 1],5,0,[S 2,S 1],25,71⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 1],5,0,[S 2,S 2],45,127⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 2],5,0,[S 2,S 1,S 5],53,149⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 1,S 5],5,0,[S 2,S 2,S 5],45,127⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 2,S 5],5,0,[S 2,S 2,S 4,S 2],55,151⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 2,S 4,S 2],5,0,[S 2,S 5,S 2,S 2,S 1],59,165⟩,
  ⟨[S 2,S 3,S 2,S 2,S 3,S 5,S 2,S 2,S 1],5,0,[S 2,S 2,S 2,S 3,S 1],49,137⟩,
  ⟨[S 0,S 5],0,0,[S 2,S 5,S 4,S 2],16,44⟩,
  ⟨[],0,0,[S 2,S 2,S 1],10,28⟩,
  ⟨[S 2,S 2,S 1],2,0,[S 2,S 1],8,22⟩,
  ⟨[S 2,S 1],1,0,[S 0,S 5],9,27⟩,
  ⟨[S 2,S 2],2,0,[S 2],8,22⟩,
  ⟨[S 2,S 1,S 5],1,0,[S 0,S 5,S 5],9,27⟩,
  ⟨[S 2,S 2,S 5],2,0,[S 2,S 5],8,22⟩,
  ⟨[S 2,S 2,S 4,S 2],2,0,[S 2,S 4,S 2],8,22⟩,
  ⟨[S 2,S 5,S 2,S 2,S 1],1,1,[S 2,S 2,S 3,S 1],15,43⟩,
  ⟨[S 2,S 2,S 2,S 3,S 1],2,0,[S 2,S 2,S 3,S 1],8,22⟩,
  ⟨[S 2,S 5,S 4,S 2],1,2,[S 6,S 2],13,35⟩,
  ⟨[S 2],2,0,[],8,22⟩,
  ⟨[S 0,S 5,S 5],0,0,[S 2,S 1,S 1,S 1,S 1],22,66⟩,
  ⟨[S 2,S 5],1,2,[S 2],13,35⟩,
  ⟨[S 2,S 4,S 2],2,1,[S 2],8,22⟩,
  ⟨[S 2,S 2,S 3,S 1],2,0,[S 2,S 3,S 1],8,22⟩,
  ⟨[S 4,S 4,S 6,S 2],3,0,[S 6,S 4],31,85⟩]

theorem validRules : ∀ r ∈ rules, r.valid := by decide +kernel

theorem soundRule (r : Rule) (hr : r ∈ rules) (a : Nat) (X : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ r.src))
      (boundary 3 false X (U 4 (a+1+r.extra5+r.extra4) ++ r.dst)) :=
  r.sound (validRules r hr) a X

#print axioms soundRule
end Raw14037DTerm
