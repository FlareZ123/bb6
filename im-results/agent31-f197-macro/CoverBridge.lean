import Macro
import Frontier

namespace F197.CoverBridge
open BB6Coverage (Move Machine PartialMachine compatible NeverHalts)
open F197 (Q)

def code : Q → Fin 6
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def table : PartialMachine := fun (s,b) =>
  match s.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def Related (c : BB6Coverage.Config) (v : F197.Config) : Prop :=
  c.state = code v.q ∧
  (∀ n : Nat, c.tape (c.head - ((n : Int) + 1)) = v.l n) ∧
  (∀ n : Nat, c.tape (c.head + (n : Int)) = v.r n)

theorem blank_related : Related BB6Coverage.blank ⟨.A,F197.blank,F197.blank⟩ := by
  exact ⟨rfl,fun _ => rfl,fun _ => rfl⟩

theorem right_related (c : BB6Coverage.Config) (v : F197.Config) (q : Q) (b : Bool)
    (h : Related c v) :
    Related (BB6Coverage.applyMove c ⟨b,true,code q⟩) (F197.moveR q b v.l v.r) := by
  rcases h with ⟨_,hl,hr⟩
  refine ⟨rfl,?_,?_⟩
  · intro n
    cases n with
    | zero => simp [BB6Coverage.applyMove,F197.moveR,F197.cons]
    | succ n =>
      change (if c.head + 1 - (((n+1 : Nat) : Int) + 1) = c.head then b else c.tape (c.head + 1 - (((n+1 : Nat) : Int) + 1))) = v.l n
      rw [if_neg (by omega),show c.head + 1 - (((n+1 : Nat) : Int) + 1) = c.head - ((n : Int) + 1) by omega]
      exact hl n
  · intro n
    change (if c.head + 1 + (n : Int) = c.head then b else c.tape (c.head + 1 + (n : Int))) = v.r (n+1)
    rw [if_neg (by omega),show c.head + 1 + (n : Int) = c.head + ((n+1 : Nat) : Int) by omega]
    exact hr (n+1)

theorem left_related (c : BB6Coverage.Config) (v : F197.Config) (q : Q) (b : Bool)
    (h : Related c v) :
    Related (BB6Coverage.applyMove c ⟨b,false,code q⟩) (F197.moveL q b v.l v.r) := by
  rcases h with ⟨_,hl,hr⟩
  refine ⟨rfl,?_,?_⟩
  · intro n
    change (if c.head + (-1) - ((n : Int) + 1) = c.head then b else c.tape (c.head + (-1) - ((n : Int) + 1))) = v.l (n+1)
    rw [if_neg (by omega),show c.head + (-1) - ((n : Int) + 1) = c.head - (((n+1 : Nat) : Int) + 1) by omega]
    exact hl (n+1)
  · intro n
    cases n with
    | zero =>
      change (if c.head + (-1) + (0 : Int) = c.head then b else c.tape (c.head + (-1) + (0 : Int))) = v.l 0
      rw [if_neg (by omega),show c.head + (-1) + (0 : Int) = c.head - ((0 : Int) + 1) by omega]
      exact hl 0
    | succ n =>
      cases n with
      | zero => simp [BB6Coverage.applyMove,F197.moveL,F197.cons,show c.head + -1 + 1 = c.head by omega]
      | succ n =>
        change (if c.head + (-1) + ((n+1+1 : Nat) : Int) = c.head then b else c.tape (c.head + (-1) + ((n+1+1 : Nat) : Int))) = v.r (n+1)
        rw [if_neg (by omega),show c.head + (-1) + ((n+1+1 : Nat) : Int) = c.head + ((n+1 : Nat) : Int) by omega]
        exact hr (n+1)

theorem right_step (m : Machine) (c : BB6Coverage.Config) (v : F197.Config) (q : Q) (b : Bool)
    (h : Related c v) (hm : m (BB6Coverage.readSlot c) = some ⟨b,true,code q⟩) :
    ∃ c', BB6Coverage.rawStep m c = some c' ∧ Related c' (F197.moveR q b v.l v.r) := by
  exact ⟨_,by simp [BB6Coverage.rawStep,hm],right_related c v q b h⟩

theorem left_step (m : Machine) (c : BB6Coverage.Config) (v : F197.Config) (q : Q) (b : Bool)
    (h : Related c v) (hm : m (BB6Coverage.readSlot c) = some ⟨b,false,code q⟩) :
    ∃ c', BB6Coverage.rawStep m c = some c' ∧ Related c' (F197.moveL q b v.l v.r) := by
  exact ⟨_,by simp [BB6Coverage.rawStep,hm],left_related c v q b h⟩

theorem step_related (m : Machine) (hm : compatible table m) (c : BB6Coverage.Config)
    (v v' : F197.Config) (h : Related c v) (hs : F197.step v = some v') :
    ∃ c', BB6Coverage.rawStep m c = some c' ∧ Related c' v' := by
  have hread : BB6Coverage.readSlot c = (code v.q,v.r 0) := by
    have hr := h.2.2 0
    simp at hr
    exact Prod.ext h.1 hr
  rcases v with ⟨q,l,r⟩
  cases q <;> cases hb : r 0 <;> simp [F197.step,hb] at hs <;> subst v' <;>
    first
    | apply right_step m c _ _ _ h; rw [hread]; exact hm _ _ (by simp only [hb]; rfl)
    | apply left_step m c _ _ _ h; rw [hread]; exact hm _ _ (by simp only [hb]; rfl)

theorem source_run_cons (m : Machine) (n : Nat) (c : BB6Coverage.Config) :
    BB6Coverage.run m (n+1) c = (BB6Coverage.rawStep m c).bind (BB6Coverage.run m n) := by
  induction n with
  | zero => simp [BB6Coverage.run]
  | succ n ih =>
    rw [BB6Coverage.run,ih]
    cases BB6Coverage.rawStep m c <;> rfl

theorem run_related (m : Machine) (hm : compatible table m) (n : Nat)
    (c : BB6Coverage.Config) (v v' : F197.Config) (h : Related c v)
    (hs : F197.run n v = some v') :
    ∃ c', BB6Coverage.run m n c = some c' ∧ Related c' v' := by
  induction n generalizing c v v' with
  | zero =>
    have he : v = v' := Option.some.inj hs
    subst v'
    exact ⟨c,rfl,h⟩
  | succ n ih =>
    simp only [F197.run] at hs
    cases hv : F197.step v with
    | none => simp [hv] at hs
    | some u =>
      obtain ⟨d,hd,hr⟩ := step_related m hm c v u h hv
      obtain ⟨e,he,hr'⟩ := ih d u v' hr (by simpa [hv] using hs)
      exact ⟨e,by rw [source_run_cons,hd]; exact he,hr'⟩

/-- No behavior of the unspecified C1 transition is assumed. -/
theorem never_of_stream_live (h : ∀ n, F197.run n ⟨.A,F197.blank,F197.blank⟩ ≠ none)
    (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  cases hs : F197.run n ⟨.A,F197.blank,F197.blank⟩ with
  | none => exact False.elim (h n hs)
  | some v =>
    obtain ⟨c,hc,_⟩ := run_related m hm n BB6Coverage.blank _ v blank_related hs
    simp [hc]

#print axioms never_of_stream_live
end F197.CoverBridge
