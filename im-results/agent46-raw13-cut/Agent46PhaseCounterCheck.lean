import Agent46CounterCheck
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.PhaseCounter
open BB6Coverage Agent31Pump Auto Counter Agent50Zipper

/-- A finite controller chooses the frame on either side of the same
little-endian binary word. Overflow may change phase and extend the word;
ordinary increments preserve the phase. Unlike the earlier positive-width
checker, the symbolic macro directly quantifies over all carry lengths. -/
structure Phase where
  q : Fin 6
  left pre post : List Bool

structure Shape (n : Nat) where
  zero one : List Bool
  phase : Fin n → Phase
  successor : Fin n → Fin n
  extension : Fin n → List Bool

def base {n : Nat} (s : Shape n) : Counter.Shape :=
  ⟨0,[],[],s.zero,s.one,[],[]⟩
def enc {n : Nat} (s : Shape n) := Counter.encode (base s)
def frame {n : Nat} (s : Shape n) (i : Fin n) (bs : List Bool) : Z0 :=
  ⟨(s.phase i).q,(s.phase i).left,(s.phase i).pre++enc s bs++(s.phase i).post⟩
def param {n : Nat} (s : Shape n) (i : Fin n) (block tail : List Bool) : PZ :=
  ⟨(s.phase i).q,.lit (s.phase i).left,.periodic (s.phase i).pre block (.lit tail)⟩
def normalIn {n : Nat} (s : Shape n) (i : Fin n) := param s i s.one s.zero
def normalOut {n : Nat} (s : Shape n) (i : Fin n) := param s i s.zero s.one
def overIn {n : Nat} (s : Shape n) (i : Fin n) := param s i s.one (s.phase i).post
def overOut {n : Nat} (s : Shape n) (i : Fin n) :=
  param s (s.successor i) s.zero (enc s (s.extension i)++(s.phase (s.successor i)).post)

structure Cert (n : Nat) where
  shape : Shape n
  entry : Nat
  start : Fin n
  seed : List Bool
  normal : Fin n → Macro
  overflow : Fin n → Macro

structure Checked {n : Nat} (p : PartialMachine) (c : Cert n) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape c.start c.seed)
  normal : ∀ i, checkOpen p (normalIn c.shape i) (normalOut c.shape i) (c.normal i) = true
  overflow : ∀ i, checkClosed p (overIn c.shape i) (overOut c.shape i) (c.overflow i) = true

theorem live {n : Nat} (p : PartialMachine) (c : Cert n) (hc : Checked p c)
    (i : Fin n) (bs : List Bool) :
    ∃ t j ds, 0<t ∧ run0 p t (frame c.shape i bs) = some (frame c.shape j ds) := by
  obtain ⟨k,h⟩ := split_next (c.shape.extension i) bs
  rcases h with ⟨hb,_⟩ | ⟨rest,hb,_⟩
  · subst bs
    obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (hc.overflow i) k
    exact ⟨_,c.shape.successor i,rep [false] k++c.shape.extension i,ht,by
      simpa [overIn,overOut,param,frame,PZ.eval,Word.eval,enc,base,encode_append,encode_rep,List.append_assoc] using hr⟩
  · subst bs
    obtain ⟨ht,hr⟩ := open_sound p _ _ _ (hc.normal i) k (enc c.shape rest++(c.shape.phase i).post)
    exact ⟨_,i,rep [false] k++true::rest,ht,by
      simpa [normalIn,normalOut,param,frame,OpenRight.attachZ_eval,Word.eval,enc,base,encode_append,encode_rep,encode,List.append_assoc] using hr⟩

theorem never {n : Nat} (p : PartialMachine) (c : Cert n) (hc : Checked p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t i bs, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape i bs) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,c.start,c.seed,by omega,hc.seed⟩
    | succ k ih =>
      obtain ⟨t,i,bs,ht,hr⟩ := ih
      obtain ⟨d,j,ds,hd,hs⟩ := live p c hc i bs
      exact ⟨t+d,j,ds,by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,i,bs,ht,hr⟩ := arbitrary n
  have hz : (zrun p t Agent31Pump.start).map project = some (frame c.shape i bs) :=
    (run_project p t Agent31Pump.start).trans hr
  cases h : zrun p t Agent31Pump.start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t Agent31Pump.start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms live
#print axioms never
end BB6Coverage.Agent31Pump.Auto.PhaseCounter
