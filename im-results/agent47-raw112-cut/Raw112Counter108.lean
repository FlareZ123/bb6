import Raw115CounterBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112Counter108
open BB6Coverage BB6Coverage.Agent31Pump.Raw115CounterBase

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
abbrev P (n : Nat) := rep [true,true] n

def F (n : Nat) (X : List Bool) : Z0 := ⟨5,[false],P (n+1) ++ X⟩
def A (n : Nat) (X : List Bool) : Z0 := ⟨0,[true,true] ++ P n ++ [false],X⟩
def C (n : Nat) (X : List Bool) : Z0 := ⟨2,P (n+1) ++ [false],X⟩
def B (n : Nat) (X : List Bool) : Z0 := ⟨1,[false,true] ++ P n ++ [false],X⟩

def Exhaust (n : Nat) (out : Nat → List Bool → Z0) : Prop :=
  ∀ X, ∃ t, 0<t ∧ run0 table t (F n X) = some (out n X)

theorem FPair (L R : List Bool) : run0 table 2 ⟨5,[true,true] ++ L,R⟩ = some ⟨5,L,[true,true] ++ R⟩ := by rfl

theorem sweep (n : Nat) (X : List Bool) : run0 table (2*n) ⟨5,P n ++ [false],X⟩ = some ⟨5,[false],P n ++ X⟩ := by
  simpa only [List.nil_append] using sweepL table 5 [] [] [true,true] [true,true] 2 (by simpa using FPair) n [false] X

theorem FNext (n : Nat) (X : List Bool) : F (n+1) X = F n ([true,true] ++ X) := by
  unfold F P
  rw [rep_add [true,true] (n+1) 1]
  simp only [rep,List.append_nil,List.append_assoc]

theorem resetA (n : Nat) (X : List Bool) : run0 table (2+2*(n+1)) (A n ([true,true] ++ X)) = some (F n ([false,true] ++ X)) := by
  have first : run0 table 2 (A n ([true,true] ++ X)) = some ⟨5,P (n+1) ++ [false],[false,true] ++ X⟩ := by rfl
  exact join0 first (sweep (n+1) ([false,true] ++ X))

theorem resetC (n : Nat) (X : List Bool) : run0 table (3+3+2*n) (C n ([true,true] ++ X)) = some (F n ([true,false] ++ X)) := by
  have first : run0 table 3 (C n ([true,true] ++ X)) = some ⟨5,[true,true,true] ++ P n ++ [false],[false] ++ X⟩ := by rfl
  have h : run0 table 3 ⟨5,[true,true,true] ++ P n ++ [false],[false] ++ X⟩ = some ⟨5,P n ++ [false],[true,true,true,false] ++ X⟩ := by rfl
  have g := join0 (join0 first h) (sweep n ([true,true,true,false] ++ X))
  unfold F P
  rw [rep_add [true,true] n 1]
  simpa only [rep,List.append_assoc,List.append_nil,List.nil_append,List.cons_append] using g

theorem exitAC (n : Nat) (X : List Bool) : run0 table 2 (A n ([false,true] ++ X)) = some (C (n+1) X) := by rfl
theorem exitCB (n : Nat) (X : List Bool) : run0 table 2 (C n ([true,false] ++ X)) = some (B (n+1) X) := by rfl
theorem exitBA (n : Nat) (X : List Bool) : run0 table 2 (B n ([true,true] ++ X)) = some (A (n+1) X) := by rfl

theorem advanceAC (n : Nat) (h : Exhaust n A) : Exhaust (n+1) C := by
  intro X
  obtain ⟨a,ha,h1⟩ := h ([true,true] ++ X)
  obtain ⟨b,hb,h2⟩ := h ([false,true] ++ X)
  refine ⟨a+(2+2*(n+1))+b+2,by omega,?_⟩
  rw [FNext]
  exact join0 (join0 (join0 h1 (resetA n X)) h2) (exitAC n X)

theorem advanceCB (n : Nat) (h : Exhaust n C) : Exhaust (n+1) B := by
  intro X
  obtain ⟨a,ha,h1⟩ := h ([true,true] ++ X)
  obtain ⟨b,hb,h2⟩ := h ([true,false] ++ X)
  refine ⟨a+(3+3+2*n)+b+2,by omega,?_⟩
  rw [FNext]
  exact join0 (join0 (join0 h1 (resetC n X)) h2) (exitCB n X)

theorem advanceBA (n : Nat) (h : Exhaust n B) : Exhaust (n+1) A := by
  intro X
  obtain ⟨a,ha,h1⟩ := h ([true,true] ++ X)
  refine ⟨a+2,by omega,?_⟩
  rw [FNext]
  exact join0 h1 (exitBA n X)

theorem exhaustA (m : Nat) : Exhaust (3*m) A := by
  induction m with
  | zero =>
    intro X
    exact ⟨6,by decide,by rfl⟩
  | succ m ih =>
    have h := advanceBA _ (advanceCB _ (advanceAC _ ih))
    simpa only [show 3*(m+1)=3*m+1+1+1 by omega] using h

theorem exhaustC (m : Nat) : Exhaust (3*m+1) C := advanceAC _ (exhaustA m)
theorem exhaustB (m : Nat) : Exhaust (3*m+2) B := advanceCB _ (exhaustC m)

def oddFam (m : Nat) : Z0 := ⟨3,[false,false,true,true,true] ++ P (3*m) ++ [false],[]⟩
def evenFam (m : Nat) : Z0 := ⟨3,[false,false,true,true,true,true,true,true] ++ P (3*m) ++ [false],[]⟩

theorem oddPrefix (m : Nat) : run0 table 7 (oddFam m) = some ⟨5,[true,true,true,true] ++ P (3*m) ++ [false],[false]⟩ := by rfl

theorem evenPrefix (m : Nat) : run0 table 7 (evenFam m) = some ⟨5,[true,true,true,true,true,true,true] ++ P (3*m) ++ [false],[false]⟩ := by rfl

theorem oddSweep (m : Nat) : run0 table (2*(3*m+2)) ⟨5,[true,true,true,true] ++ P (3*m) ++ [false],[false]⟩ = some (F (3*m+1) [false]) := by
  simpa only [F,P,rep,List.append_assoc,List.cons_append,List.nil_append] using sweep (3*m+2) [false]

theorem evenSweep (m : Nat) : run0 table (1+2*(3*m+3)) ⟨5,[true,true,true,true,true,true,true] ++ P (3*m) ++ [false],[false]⟩ = some (F (3*m+2) [true,false]) := by
  have first : run0 table 1 ⟨5,[true,true,true,true,true,true,true] ++ P (3*m) ++ [false],[false]⟩ = some ⟨5,P (3*m+3) ++ [false],[true,false]⟩ := by rfl
  exact join0 first (sweep (3*m+3) [true,false])

theorem oddFinish (m : Nat) : run0 table 4 (C (3*m+1) [false]) = some (evenFam m) := by rfl

theorem evenFinish (m : Nat) : run0 table 5 (B (3*m+2) [true,false]) = some (oddFam (m+1)) := by
  unfold oddFam
  rw [show 3*(m+1)=3*m+3 by omega]
  rfl

theorem growth (m : Nat) : ∃ t, 0<t ∧ run0 table t (oddFam m) = some (oddFam (m+1)) := by
  obtain ⟨a,ha,h1⟩ := exhaustC m [false]
  obtain ⟨b,hb,h2⟩ := exhaustB m [true,false]
  have h3 := join0 (join0 (join0 (oddPrefix m) (oddSweep m)) h1) (oddFinish m)
  have h4 := join0 (join0 (join0 (evenPrefix m) (evenSweep m)) h2) (evenFinish m)
  exact ⟨_,by omega,join0 h3 h4⟩

theorem entry : run0 table 32 ⟨0,[],[]⟩ = some (oddFam 0) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table oddFam (fun _ => True) 0 trivial 32 entry
    (fun n _ => by obtain ⟨t,ht,h⟩ := growth n; exact ⟨n+1,t,trivial,ht,h⟩) m hm
end BB6Coverage.Agent31Pump.Raw112Counter108
