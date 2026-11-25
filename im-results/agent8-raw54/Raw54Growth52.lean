import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Growth52
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def triple0 : List Bool := [false,false,false]
def triple1 : List Bool := [true,true,true]
def frame : List Bool := [true,false,false]
def cfg (j n : Nat) : Z0 := ⟨0,frame ++ rep triple0 j ++ rep [true] (n+1),[]⟩

theorem startPhase (j n : Nat) : run0 table 2 (cfg j n) = some ⟨3,[false,false,false,false,false] ++ rep triple0 j ++ rep [true] (n+1),[]⟩ := by rfl

theorem afterFive (j n : Nat) : run0 table 5 ⟨3,[false,false,false,false,false] ++ rep triple0 j ++ rep [true] (n+1),[]⟩ = some ⟨3,rep triple0 j ++ rep [true] (n+1),[true,true,true,true,true]⟩ := by rfl

theorem hrot (j : Nat) : rep triple1 j ++ [true,true,true,true,true] = [true,true] ++ rep triple1 (j+1) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [rep,List.append_assoc] at ih ⊢; rw [ih]; rfl

theorem phase (j n : Nat) : ∃ t, 0<t ∧ run0 table t (cfg j n) = some ⟨0,frame ++ rep [true] (n+2),rep triple1 (j+1)⟩ := by
  have a := join0 (startPhase j n) (afterFive j n)
  have b := sweepL table 3 [] [] triple0 triple1 3 (by intro L R; rfl) j (rep [true] (n+1)) [true,true,true,true,true]
  have c : run0 table 1 ⟨3,rep [true] (n+1),rep triple1 j ++ [true,true,true,true,true]⟩ = some ⟨4,rep [true] n,false :: (rep triple1 j ++ [true,true,true,true,true])⟩ := by rfl
  have d := sweepL table 4 [] [] [true] [false] 1 (by intro L R; rfl) n [] (false :: (rep triple1 j ++ [true,true,true,true,true]))
  have e : run0 table 2 ⟨4,[],rep [false] n ++ (false :: (rep triple1 j ++ [true,true,true,true,true]))⟩ = some ⟨2,[true,true],rep [false] (n+1) ++ (rep triple1 j ++ [true,true,true,true,true])⟩ := by
    have h := rep_snoc [false] n
    change _ = some (⟨2,[true,true],([false] ++ rep [false] n) ++ (rep triple1 j ++ [true,true,true,true,true])⟩ : Z0)
    rw [← h]
    simp only [List.append_assoc]; rfl
  have f := sweepR table 2 [true,true] [] [false] [true] 3 (by intro L R; rfl) (n+1) [] (rep triple1 j ++ [true,true,true,true,true])
  have g : run0 table 2 ⟨2,[true,true] ++ rep [true] (n+1),rep triple1 j ++ [true,true,true,true,true]⟩ = some ⟨0,frame ++ rep [true] (n+2),rep triple1 (j+1)⟩ := by
    rw [hrot j]; rfl
  simp only [List.nil_append,List.append_nil,Nat.one_mul] at b d f
  have H := join0 (join0 (join0 (join0 (join0 (join0 a b) c) d) e) f) g
  exact ⟨_,by omega,H⟩

theorem drain (j n : Nat) : run0 table (3*(j+1)) ⟨0,frame ++ rep [true] (n+2),rep triple1 (j+1)⟩ = some (cfg (j+1) (n+1)) := by
  have h := sweepR table 0 frame [] triple1 triple0 3 (by intro L R; rfl) (j+1) (rep [true] (n+2)) []
  simpa only [cfg,List.nil_append,List.append_nil] using h

def family (k : Nat) : Z0 := cfg k (k+2)
theorem first : run0 table 17 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem next (k : Nat) : ∃ t, 0<t ∧ run0 table t (family k) = some (family (k+1)) := by
  obtain ⟨t,ht,h⟩ := phase k (k+2)
  have H := join0 h (drain k (k+2))
  refine ⟨t+3*(k+1),by omega,?_⟩
  unfold family
  rw [show k+1+2=k+2+1 by omega]
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 17 first next m hm
#print axioms never
end BB6.Agent8Raw54.Growth52
