import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw110UnarySweep
open BB6Coverage BB6Coverage.Agent31Pump
-- 1RB1RF_1RC0LB_0RD1LF_1LD1RE_---0LC_1RA0RB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
abbrev O (n : Nat) := List.replicate n true
def Reaches (a b : Z0) : Prop := ∃ t, run0 table t a = some b
theorem trans {a b c : Z0} : Reaches a b → Reaches b c → Reaches a c := by
  rintro ⟨t,h⟩ ⟨u,g⟩
  exact ⟨t+u,join0 h g⟩
theorem rep_ones (a n : Nat) : rep (O a) n = O (a*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,List.replicate_append_replicate,Nat.mul_succ,Nat.add_comm a]
theorem leftOne (L R : List Bool) : run0 table 9 ⟨5,[true]++L,[true,false]++R⟩ = some ⟨5,L,[true,false]++[true]++R⟩ := by rfl
theorem leftEpoch (n : Nat) : Reaches ⟨5,false::O (n+1),[]⟩ ⟨5,[],[true,false]++O (n+4)⟩ := by
  have h1 : run0 table 9 ⟨5,false::O (n+1),[]⟩ = some ⟨5,O (n+3),[true,false,true]⟩ := by rfl
  have h2 := sweepL table 5 [] [true,false] [true] [true] 9 leftOne (n+3) [] [true]
  change run0 table (9*(n+3)) ⟨5,rep (O 1) (n+3)++[],[true,false,true]⟩ = some ⟨5,[],[true,false]++(rep (O 1) (n+3)++[true])⟩ at h2
  simp only [rep_ones,Nat.one_mul,List.append_nil] at h2
  change run0 table (9*(n+3)) ⟨5,O (n+3),[true,false,true]⟩ = some ⟨5,[],[true,false]++(O (n+3)++O 1)⟩ at h2
  rw [List.replicate_append_replicate] at h2
  exact ⟨_,join0 h1 h2⟩
theorem rightFive (L R : List Bool) : run0 table 11 ⟨5,[false]++L,[true,false]++O 5++R⟩ = some ⟨5,[false]++O 5++L,[true,false]++R⟩ := by rfl
theorem rightEpoch (k : Nat) (R : List Bool) : Reaches ⟨5,[],[true,false]++O (5*(k+1))++R⟩ ⟨5,false::O (5*(k+1)),[true,false]++R⟩ := by
  have heq : O (5*(k+1)) = O 5 ++ O (5*k) := by rw [List.replicate_append_replicate,Nat.mul_succ,Nat.add_comm 5]
  have h1 : run0 table 11 ⟨5,[],[true,false]++O (5*(k+1))++R⟩ = some ⟨5,false::O 5,[true,false]++O (5*k)++R⟩ := by
    rw [heq]; rfl
  have h2 := sweepR table 5 [false] [true,false] (O 5) (O 5) 11 rightFive k (O 5) R
  simp only [rep_ones,List.append_assoc] at h2
  change run0 table (11*k) ⟨5,false::O 5,[true,false]++O (5*k)++R⟩ = some ⟨5,false::(O (5*k)++O 5),[true,false]++R⟩ at h2
  rw [List.replicate_append_replicate,← Nat.mul_succ] at h2
  exact ⟨_,join0 h1 h2⟩
theorem finish1 (n : Nat) : run0 table 4 ⟨5,false::O n,[true,false,true]⟩ = some ⟨5,false::O (n+4),[]⟩ := by rfl
theorem finish2 (n : Nat) : run0 table 16 ⟨5,false::O (n+1),[true,false,true,true]⟩ = some ⟨5,false::O (n+9),[]⟩ := by rfl
def family (n : Nat) : Z0 := ⟨5,false::O (15*n+8),[]⟩
theorem entry : run0 table 33 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem grow (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have a := leftEpoch (15*n+7)
  have b := rightEpoch (3*n+1) [true]
  rw [show 5*(3*n+1+1)=15*n+10 by omega] at b
  change Reaches ⟨5,[],[true,false]++O (15*n+10)++[true]⟩ ⟨5,false::O (15*n+10),[true,false,true]⟩ at b
  change Reaches ⟨5,[],[true,false]++O (15*n+10)++O 1⟩ _ at b
  rw [List.append_assoc,List.replicate_append_replicate] at b
  have c := finish1 (15*n+10)
  have d := leftEpoch (15*n+13)
  have e := rightEpoch (3*n+2) [true,true]
  rw [show 5*(3*n+2+1)=15*n+15 by omega] at e
  change Reaches ⟨5,[],[true,false]++O (15*n+15)++O 2⟩ _ at e
  rw [List.append_assoc,List.replicate_append_replicate] at e
  have f := finish2 (15*n+14)
  obtain ⟨t,h⟩ := trans (trans (trans (trans a b) ⟨4,c⟩) d) e
  change ∃ t, 0<t ∧ run0 table t ⟨5,false::O (15*n+8),[]⟩ = some ⟨5,false::O (15*(n+1)+8),[]⟩
  rw [show 15*(n+1)+8=15*n+23 by omega]
  exact ⟨t+16,by omega,join0 h f⟩
noncomputable def cost (n : Nat) : Nat := (grow n).choose
theorem cost_pos (n : Nat) : 0 < cost n := (grow n).choose_spec.1
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (grow n).choose_spec.2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never_of_growth table family 33 cost entry cost_pos growth m hm
#print axioms never
end BB6.Agent7Raw110UnarySweep
