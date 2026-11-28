import OrdinaryBulk
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (pre_append b)

inductive Op where
  | loc (r : Rule)
  | epoch (t : Terminal)
  deriving Repr

def opOK : Op → Bool | .loc r => ruleOK r | .epoch t => epochOK t

def applyOp : Op → Nat → Word → Option (Nat × Word)
  | .loc r => applyRule r
  | .epoch t => applyEpoch t

theorem op_sound (o : Op) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hok : opOK o = true) (ha : applyOp o n w = some (n',w')) : ReachPos (state n w l) (state n' w' l) := by
  cases o with
  | loc r => exact apply_sound r n n' w w' l hl hok ha
  | epoch t => exact applyEpoch_sound t n n' w w' l hl hok ha

def applyOps (ops : List Op) (n : Nat) (w : Word) : Option (Nat × Word) :=
  match ops with
  | [] => some (n,w)
  | o::os => do
    let (n',w') ← applyOp o n w
    applyOps os n' w'

theorem ops_sound (os : List Op) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hok : os.all opOK = true) (ha : applyOps os n w = some (n',w')) : Reach (state n w l) (state n' w' l) := by
  induction os generalizing n w with
  | nil => simp [applyOps] at ha; obtain ⟨rfl,rfl⟩ := ha; exact reach_refl _
  | cons o os ih =>
    simp only [List.all_cons,Bool.and_eq_true] at hok
    simp only [applyOps] at ha
    cases hh : applyOp o n w with
    | none => simp [hh] at ha
    | some v =>
      rcases v with ⟨m,z⟩
      simp [hh] at ha
      exact reach_trans (reach_of_pos (op_sound o n m w z l hl hok.1 hh)) (ih m z hok.2 ha)

theorem ops_pos (os : List Op) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hne : os ≠ []) (hok : os.all opOK = true) (ha : applyOps os n w = some (n',w')) : ReachPos (state n w l) (state n' w' l) := by
  cases os with
  | nil => contradiction
  | cons o os =>
    simp only [List.all_cons,Bool.and_eq_true] at hok
    simp only [applyOps] at ha
    cases hh : applyOp o n w with
    | none => simp [hh] at ha
    | some v =>
      rcases v with ⟨m,z⟩
      simp [hh] at ha
      exact reach_pos_trans (op_sound o n m w z l hl hok.1 hh) (ops_sound os m n' z w' l hl hok.2 ha)

def LB := enc "AATAAATAUJTT"
def OUT := enc "TAATAAATAATTAAATUJTTAATAAATAUJTT"
def Head := enc "JTAATAAATATAATAATAATAATAATTATAATAATTAATTAAATAUJTT"
def START := Head++flat LB 35

theorem kpow_eq (n : Nat) (l : Tape) : Agent2EpochMarker.kpow n l = rep K n l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Agent2EpochMarker.kpow,rep]; rw [ih]; rfl

theorem blockpow_eq (n : Nat) (l : Tape) : Agent2EpochMarker.blockpow n l = rep LB n l := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Agent2EpochMarker.blockpow,rep]; rw [ih]; rfl

theorem marker11 (k : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state (2*(2*k+2)+1) (M++enc "TATJ") l) (state 0 OUT (rep LB k (pre (enc "T") l))) := by
  have h1 := descend_many (2*k+2) 1 (pre (enc "TATJ") l) (by rfl)
  have h2 := Agent2EpochMarker.bulk11 k l hl
  rw [kpow_eq,blockpow_eq] at h2
  have hs : Agent2EpochMarker.source l = pre (enc "TATJ") l := by rfl
  have ht : Agent2EpochMarker.t l = pre (enc "T") l := by rfl
  rw [hs,ht] at h2
  have he (z : Tape) : Agent2EpochMarker.ent1 z = rep P 1 (pre M z) := by
    change Agent2EpochMarker.ent1 z = pre P (pre M z)
    rw [← pre_append]
    rfl
  have ho (z : Tape) : Agent2EpochMarker.out1g2 z = pre OUT z := by rfl
  have hin : b (Agent2EpochMarker.ent1 (rep K (2*k+2) (pre (enc "TATJ") l))) (pre [true] blank) =
      state 1 M (rep K (2*k+2) (pre (enc "TATJ") l)) := by rw [he]; rfl
  have hout : b (Agent2EpochMarker.out1g2 (rep LB k (pre (enc "T") l))) (pre [true] blank) =
      state 0 OUT (rep LB k (pre (enc "T") l)) := by rw [ho]; rfl
  rw [hin,hout] at h2
  have h3 := reach_trans h1 (show Reach (state 1 M (rep K (2*k+2) (pre (enc "TATJ") l)))
    (state 0 OUT (rep LB k (pre (enc "T") l))) from ⟨_,h2⟩)
  simpa only [state,pre_append] using h3

/-- A uniformly positive self-embedding into a cylinder rules out every finite halt. -/
theorem cylinder_live (n : Nat) (w : Word) (f : Tape → Tape)
    (hf : ∀ l : Tape, l 0 = true → f l 0 = true)
    (hloop : ∀ l : Tape, l 0 = true → ReachPos (state n w l) (state n w (f l)))
    (l : Tape) (hl : l 0 = true) : ∀ t, run t (state n w l) ≠ none := by
  have hlong (k : Nat) : ∀ l : Tape, l 0 = true → ∃ t ≥ k, ∃ c, run t (state n w l) = some c := by
    induction k with
    | zero => intro l hl; exact ⟨0,by decide,_,rfl⟩
    | succ k ih =>
      intro l hl
      obtain ⟨a,ha,h1⟩ := hloop l hl
      obtain ⟨t,ht,c,h2⟩ := ih (f l) (hf l hl)
      exact ⟨a+t,by omega,c,Agent2EpochMarker.compose h1 h2⟩
  intro t h
  obtain ⟨a,ha,c,hc⟩ := hlong t l hl
  rw [show a=t+(a-t) by omega,run_add,h] at hc
  contradiction

#print axioms marker11
#print axioms cylinder_live
end F197.Agent2Self
