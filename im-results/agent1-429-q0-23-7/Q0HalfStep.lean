import Q0DoubleBarrier

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 4000000

def bit (d : Bool) : Nat := if d then 1 else 0
/-- False = A (even rank), true = B (odd rank). -/
def len (s d : Bool) : Nat := if s then (if d then 3 else 1) else (if d then 9 else 5)
def off (s d : Bool) : Nat := if d then (if s then 4 else 12) else 0

def numerator (s d : Bool) (p y : Nat) := y + bit d*p + off s d

def valid (s : Bool) (p : Nat) : Prop := p%2=bit s

def phase (s : Bool) (w : List Bool) : Bool := if w.length%2=0 then s else !s

theorem phase_cons (s d : Bool) (w : List Bool) : phase s (d::w)=phase (!s) w := by
  cases s <;> simp only [phase,List.length_cons,Bool.not_false,Bool.not_true] <;> split <;> split <;> simp_all <;> omega

theorem phase_append (s : Bool) (w v : List Bool) : phase s (w++v)=phase (phase s w) v := by
  induction w generalizing s with
  | nil => simp [phase]
  | cons d w ih => simp only [List.cons_append,phase_cons]; exact ih (!s)

inductive Trace : Bool → List Bool → Nat → Nat → Nat → Nat → Prop where
  | nil (s : Bool) (p y : Nat) : Trace s [] p y p y
  | cons (s d : Bool) {w : List Bool} {p y P Y : Nat}
      (h : numerator s d p y % 4=0)
      (tail : Trace (!s) w (p+len s d) (numerator s d p y/4) P Y) :
      Trace s (d::w) p y P Y

theorem strict_step (s d : Bool) (p y : Nat) (hy : 0<y) (hp : 3*y<p)
    (h : numerator s d p y%4=0) :
    0<numerator s d p y/4 ∧ 3*(numerator s d p y/4)<p+len s d := by
  cases s <;> cases d <;> simp [numerator,bit,len,off] at * <;> omega

theorem valid_step (s d : Bool) (p : Nat) (h : valid s p) : valid (!s) (p+len s d) := by
  cases s <;> cases d <;> simp [valid,bit,len] at * <;> omega

theorem unique_B (p y : Nat) (hp : valid true p) (h : numerator true false p y%4=0) :
    numerator true true p y%4≠0 := by
  simp [valid,bit,numerator,off] at *; omega

theorem pair_contraction (s : Bool) (p y : Nat) (hp : 3*y≤p) :
    (numerator s false p y%4=0 ∧
    numerator s true p y%4=0) ↔ y%4=0 ∧ (p-3*y)%4=0 := by
  cases s <;> simp [numerator,bit,off] <;> omega

/-- Exact macro factorization into two base-four digits. -/
def low (d : Digit) : Bool := match d with | .zero | .four => false | _ => true
def high (d : Digit) : Bool := match d with | .zero | .one => false | _ => true

theorem pair_of_macro (d : Digit) (p y : Nat) (h : num d p y%16=0) :
    Trace false [low d,high d] (2*p) (2*y) (2*nextP d p) (2*nextY d p y) := by
  have hd : 4 ∣ numerator false (low d) (2*p) (2*y) := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,low] at * <;> omega
  have h₁ : numerator false (low d) (2*p) (2*y)%4=0 := Nat.mod_eq_zero_of_dvd hd
  refine Trace.cons false (low d) h₁ ?_
  have h₂ : numerator true (high d) (2*p+len false (low d)) (numerator false (low d) (2*p) (2*y)/4)%4=0 := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,len,low,high] at * <;> omega
  refine Trace.cons true (high d) h₂ ?_
  have hp : 2*p+len false (low d)+len true (high d)=2*nextP d p := by
    cases d <;> simp [nextP,cost,len,low,high] <;> omega
  have hy : numerator true (high d) (2*p+len false (low d)) (numerator false (low d) (2*p) (2*y)/4)/4=2*nextY d p y := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,len,low,high,nextY] at * <;> omega
  rw [hp,hy]
  exact Trace.nil false _ _

theorem append {s w v p y Q F P Y} (h : Trace s w p y Q F) (t : Trace (phase s w) v Q F P Y) : Trace s (w++v) p y P Y := by
  induction h with
  | nil => simpa [phase] using t
  | cons s d h tail ih =>
    rw [phase_cons] at t
    exact Trace.cons s d h (ih t)

def expand : List Digit → List Bool
  | [] => []
  | d::w => low d::high d::expand w

theorem expand_len (w : List Digit) : (expand w).length=2*w.length := by
  induction w with
  | nil => rfl
  | cons d w ih => simp [expand,ih]; omega

theorem expand_trace {w p y P Y} (h : RankBarrier.Trace w p y P Y) :
    Trace false (expand w) (2*p) (2*y) (2*P) (2*Y) := by
  induction h with
  | nil => exact Trace.nil false _ _
  | cons d h tail ih =>
    apply append (pair_of_macro d _ _ h)
    simpa [phase] using ih

theorem trace_rank {s w p y P Y} (h : Trace s w p y P Y) : p+w.length≤P ∧ P≤p+9*w.length := by
  induction h with
  | nil => simp
  | cons s d h tail ih => cases s <;> cases d <;> simp [len] at * <;> omega

theorem trace_strict {s w p y P Y} (h : Trace s w p y P Y) (hy : 0<y) (hp : 3*y<p) : 0<Y ∧ 3*Y<P := by
  induction h with
  | nil => exact ⟨hy,hp⟩
  | cons s d h tail ih => exact ih (strict_step s d _ _ hy hp h).1 (strict_step s d _ _ hy hp h).2

theorem trace_valid {s w p y P Y} (h : Trace s w p y P Y) (hp : valid s p) : valid (phase s w) P := by
  induction h with
  | nil => simpa [phase] using hp
  | cons s d h tail ih => rw [phase_cons]; exact ih (valid_step s d _ hp)

theorem trace_split {s w p y P Y} (h : Trace s w p y P Y) (n : Nat) :
    ∃ Q F, Trace s (w.take n) p y Q F ∧ Trace (phase s (w.take n)) (w.drop n) Q F P Y := by
  induction n generalizing s w p y with
  | zero => exact ⟨p,y,by simp; exact Trace.nil s _ _,by simpa [phase] using h⟩
  | succ n ih =>
    cases h with
    | nil => exact ⟨_,_,by simp; exact Trace.nil _ _ _,by simp [phase]; exact Trace.nil _ _ _⟩
    | @cons s d w p y P Y hd tail =>
      obtain ⟨Q,F,h₁,h₂⟩ := ih tail
      exact ⟨Q,F,Trace.cons s d hd h₁,by simpa only [List.take_succ_cons,List.drop_succ_cons,phase_cons] using h₂⟩

#print axioms pair_of_macro
#print axioms expand_trace
#print axioms trace_split
end BB429Q0Macro.HalfStep
