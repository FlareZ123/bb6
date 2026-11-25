import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Word41
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none

def zL : List Bool := [false,true]
def oL : List Bool := [true,true]
def pL : List Bool := [false,true,true,true]
def pR : List Bool := [false,true,true,true]
def marker : List Bool := [false,true]
def cPayload : List Bool := [false,true,false,false,false,false,false]
def dPayload : List Bool := [false,true,false,false,true,true,false,true,false,false,false,true,true]
def enc : List Bool → List Bool
  | [] => []
  | b::bs => b::b::enc bs

def aCfg (k : Nat) (r : List Bool) : Z0 := ⟨0,zL ++ rep pL k,r⟩
def bCfg (k : Nat) (r : List Bool) : Z0 := ⟨0,oL ++ rep pL k,r⟩
def cCfg (k : Nat) (w : List Bool) : Z0 := aCfg 0 (marker ++ rep pR (k+1) ++ cPayload ++ enc w)
def dCfg (k : Nat) (w : List Bool) : Z0 := aCfg 0 (marker ++ rep pR k ++ dPayload ++ enc w)

theorem pushOne (k : Nat) (r : List Bool) : run0 table 6 (aCfg k (marker ++ pR ++ r)) = some (aCfg (k+1) (marker ++ r)) := by rfl

theorem pushAll (n k : Nat) (r : List Bool) : run0 table (6*n) (aCfg k (marker ++ rep pR n ++ r)) = some (aCfg (k+n) (marker ++ r)) := by
  induction n generalizing k with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h := join0 (pushOne k (rep pR n ++ r)) (ih (k+1))
    simp only [rep,List.append_assoc] at h ⊢
    rw [show 6*(n+1)=6+6*n by omega,show k+(n+1)=k+1+n by omega]
    exact h

theorem drainOne (k : Nat) (r : List Bool) : run0 table 4 (bCfg (k+1) r) = some (bCfg k (pR ++ r)) := by rfl

theorem drain (k : Nat) (r : List Bool) : run0 table (4*k+6) (bCfg k r) = some (aCfg 0 (marker ++ rep pR k ++ r)) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have H := join0 (drainOne k r) (ih (pR ++ r))
    rw [show 4*(k+1)+6=4+(4*k+6) by omega]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep pR k) pR r,rep_snoc pR k] using H

theorem cCore (k : Nat) (r : List Bool) : run0 table 34 (aCfg (k+1) (marker ++ cPayload ++ r)) = some (bCfg k (dPayload ++ r)) := by rfl

theorem cToD (k : Nat) (w : List Bool) : ∃ t,0<t ∧ run0 table t (cCfg k w) = some (dCfg k w) := by
  have a := pushAll (k+1) 0 (cPayload ++ enc w)
  have b := cCore k (enc w)
  have c := drain k (dPayload ++ enc w)
  simp only [Nat.zero_add,List.append_assoc] at a b c
  have H := join0 (join0 a b) c
  exact ⟨6*(k+1)+34+(4*k+6),by omega,by simpa only [cCfg,dCfg,Nat.zero_add,List.append_assoc] using H⟩

def growCfg (j m : Nat) (w : List Bool) : Z0 := ⟨0,zL ++ rep oL (m+1) ++ rep pL (j+1),false::enc w⟩
theorem dCore (k : Nat) (w : List Bool) : run0 table 34 (aCfg k (marker ++ dPayload ++ enc w)) = some (growCfg (k+2) 0 w) := by rfl

theorem growTrue (j m : Nat) (w : List Bool) : run0 table 4 (growCfg j m (true::w)) = some (growCfg j (m+1) w) := by rfl

def growWord (m : Nat) : List Bool → List Bool
  | [] => List.replicate m false ++ [true]
  | false::w => List.replicate m false ++ true::w
  | true::w => growWord (m+1) w

theorem encZeros (m : Nat) (w : List Bool) : enc (List.replicate m false ++ w) = rep [false,false] m ++ enc w := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih]; rfl

theorem growResetCore (j m : Nat) (w : List Bool) : run0 table 6 (growCfg j m (false::w)) = some ⟨4,rep oL (m+2) ++ rep pL (j+1),[false,true,true] ++ enc w⟩ := by rfl

theorem growResetEmpty (j m : Nat) : run0 table 6 (growCfg j m []) = some ⟨4,rep oL (m+2) ++ rep pL (j+1),[false,true,true]⟩ := by rfl

theorem rot (m : Nat) : rep [false,false] m ++ [false] = [false] ++ rep [false,false] m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [rep,List.append_assoc]; rw [ih]; rfl

theorem finishReset (j m : Nat) (w : List Bool) : ∃ t,0<t ∧ run0 table t ⟨4,rep oL (m+2) ++ rep pL (j+1),[false,true,true] ++ enc w⟩ = some (aCfg 0 (marker ++ rep pR j ++ cPayload ++ enc (List.replicate m false ++ true::w))) := by
  have a := sweepL table 4 [] [] oL [false,false] 2 (by intro L R; rfl) (m+2) (rep pL (j+1)) ([false,true,true] ++ enc w)
  have b : run0 table 2 ⟨4,rep pL (j+1),rep [false,false] (m+2) ++ ([false,true,true] ++ enc w)⟩ = some (bCfg j (marker ++ (rep [false,false] (m+2) ++ ([false,true,true] ++ enc w)))) := by rfl
  have c := drain j (marker ++ (rep [false,false] (m+2) ++ ([false,true,true] ++ enc w)))
  simp only [List.nil_append] at a
  have H := join0 (join0 a b) c
  refine ⟨2*(m+2)+2+(4*j+6),by omega,?_⟩
  rw [encZeros]
  have hr : rep [false,false] m ++ ([false,true,true] ++ enc w) = false :: (rep [false,false] m ++ (true::true::enc w)) := by
    change rep [false,false] m ++ ([false] ++ (true::true::enc w)) = _
    rw [← List.append_assoc,rot]
    rfl
  simp only [rep,List.append_assoc] at H ⊢
  rw [hr] at H
  exact H

theorem grow (j m : Nat) (w : List Bool) : ∃ t,0<t ∧ run0 table t (growCfg j m w) = some (aCfg 0 (marker ++ rep pR j ++ cPayload ++ enc (growWord m w))) := by
  induction w generalizing m with
  | nil =>
    obtain ⟨t,ht,h⟩ := finishReset j m []
    exact ⟨6+t,by omega,join0 (growResetEmpty j m) h⟩
  | cons b w ih =>
    cases b
    · obtain ⟨t,ht,h⟩ := finishReset j m w
      exact ⟨6+t,by omega,join0 (growResetCore j m w) h⟩
    · obtain ⟨t,ht,h⟩ := ih (m+1)
      exact ⟨4+t,by omega,join0 (growTrue j m w) h⟩

theorem dToC (k : Nat) (w : List Bool) : ∃ t,0<t ∧ run0 table t (dCfg k w) = some (cCfg (k+1) (growWord 0 w)) := by
  have a := pushAll k 0 (dPayload ++ enc w)
  have b := dCore k w
  obtain ⟨t,ht,c⟩ := grow (k+2) 0 w
  simp only [Nat.zero_add,List.append_assoc] at a b c
  have H := join0 (join0 a b) c
  exact ⟨6*k+34+t,by omega,by simpa only [dCfg,cCfg,Nat.zero_add,List.append_assoc] using H⟩

def orbit : Nat → List Bool
  | 0 => [true]
  | n+1 => growWord 0 (orbit n)
def family (n : Nat) : Z0 := cCfg n (orbit n)
theorem first : run0 table 101 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  obtain ⟨t,ht,h⟩ := cToD n (orbit n)
  obtain ⟨s,hs,g⟩ := dToC n (orbit n)
  exact ⟨t+s,by omega,join0 h g⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 101 first next m hm
#print axioms never
end BB6.Agent8Raw54.Word41
