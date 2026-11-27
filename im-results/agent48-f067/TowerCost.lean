import Lean

namespace F067Cost

def shift (c : Nat) : List Nat → List Nat
  | [] => []
  | k :: ks => (k+c) :: shift (4*c) ks

def tick := shift 2

structure Summary where
  g : Nat
  h : Nat
  d : Nat
  e : Nat
  deriving Repr, DecidableEq

def summarize : List Nat → Summary
  | [] => ⟨14, 0, 0, 0⟩
  | k :: ks =>
    let a := summarize ks
    ⟨28*k+390+4*a.g+6*a.d, 5*k+136+a.g+a.h+a.e,
      56+16*a.d, 10+4*a.d+4*a.e⟩

def g (ks : List Nat) := (summarize ks).g
def h (ks : List Nat) := (summarize ks).h
def d (ks : List Nat) := (summarize ks).d
def e (ks : List Nat) := (summarize ks).e

theorem shift_add (a b : Nat) (ks : List Nat) :
    shift a (shift b ks) = shift (a+b) ks := by
  induction ks generalizing a b with
  | nil => rfl
  | cons k ks ih =>
    simp only [shift, ih]
    rw [show k + b + a = k + (a+b) by omega, show 4*a+4*b = 4*(a+b) by omega]

theorem shift_length (a : Nat) (ks : List Nat) : (shift a ks).length = ks.length := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih => simp [shift, ih]

theorem shift_ne_nil (a : Nat) {ks : List Nat} (hne : ks ≠ []) : shift a ks ≠ [] := by
  cases ks <;> simp_all [shift]

theorem d_shift (a : Nat) (ks : List Nat) : d (shift a ks) = d ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    change 56+16*d (shift (4*a) ks) = 56+16*d ks
    rw [ih]

theorem e_shift (a : Nat) (ks : List Nat) : e (shift a ks) = e ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih =>
    change 10+4*d (shift (4*a) ks)+4*e (shift (4*a) ks) = 10+4*d ks+4*e ks
    rw [d_shift, ih]

theorem g_shift (a : Nat) (ks : List Nat) : g (shift (2*a) ks) = g ks + a*d ks := by
  induction ks generalizing a with
  | nil => simp [g,d,shift,summarize]
  | cons k ks ih =>
    change 28*(k+2*a)+390+4*g (shift (4*(2*a)) ks)+6*d (shift (4*(2*a)) ks) =
      28*k+390+4*g ks+6*d ks+a*(56+16*d ks)
    rw [show 4*(2*a) = 2*(4*a) by omega, ih, d_shift]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm a 16] 
    rw [Nat.mul_assoc 4 a (d ks)]
    omega

theorem h_shift (a : Nat) (ks : List Nat) : h (shift (2*a) ks) = h ks + a*e ks := by
  induction ks generalizing a with
  | nil => simp [h,e,shift,summarize]
  | cons k ks ih =>
    change 5*(k+2*a)+136+g (shift (4*(2*a)) ks)+h (shift (4*(2*a)) ks)+e (shift (4*(2*a)) ks) =
      5*k+136+g ks+h ks+e ks+a*(10+4*d ks+4*e ks)
    rw [show 4*(2*a) = 2*(4*a) by omega, g_shift, ih, e_shift]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm a 4 (d ks), Nat.mul_left_comm a 4 (e ks)]
    rw [Nat.mul_assoc 4 a (d ks), Nat.mul_assoc 4 a (e ks)]
    omega

theorem g_tick (ks : List Nat) : g (tick ks) = g ks+d ks := by
  simpa [tick] using g_shift 1 ks

theorem h_tick (ks : List Nat) : h (tick ks) = h ks+e ks := by
  simpa [tick] using h_shift 1 ks

theorem g_unroll (k : Nat) (ks : List Nat) :
    g (k::ks) = 56+g ks+(14*k+132)+g (tick ks)+56+g (tick (tick ks))+
      (14*(k+1)+132)+g (tick (tick (tick ks))) := by
  have dt (xs : List Nat) : d (tick xs) = d xs := d_shift 2 xs
  simp only [g_tick, dt]
  change 28*k+390+4*g ks+6*d ks = _
  omega

theorem h_unroll (k : Nat) (ks : List Nat) :
    h (k::ks) = 56+g ks+(5*k+80)+h (tick ks) := by
  rw [h_tick]
  change 5*k+136+g ks+h ks+e ks = _
  omega

theorem tick_four (ks : List Nat) : tick (tick (tick (tick ks))) = shift 8 ks := by
  simp [tick, shift_add]

theorem g_singleton (k : Nat) : g [k] = 28*k+446 := by
  change 28*k+390+4*14+6*0 = _
  omega

theorem h_singleton (k : Nat) : h [k] = 5*k+150 := by
  change 5*k+136+14+0+0 = _
  omega

-- Exact compositional abstraction of the six separator rules.
structure Algebra (S : Type) where
  A3 : Nat → S → S
  A0 : Nat → S → S
  B3 : Nat → S → S
  B0 : Nat → S → S
  Sub : Nat → S → S → Prop
  Top : Nat → S → S → Prop
  SubHalt : Nat → S → Prop
  TopHalt : Nat → S → Prop
  top_trans : ∀ {a b s t u}, Top a s t → Top b t u → Top (a+b) s u
  top_halt_trans : ∀ {a b s t}, Top a s t → TopHalt b t → TopHalt (a+b) s
  subA3 : ∀ k s, Sub 56 (A3 k s) (B3 k s)
  subA0 : ∀ k s, Sub 56 (A0 k s) (B0 k s)
  subB0 : ∀ k s, Sub (14*k+132) (B0 k s) (A3 (k+1) s)
  subB3 : ∀ k {c s t}, Sub c s t → Sub (c+14*k+132) (B3 k s) (A0 (k+1) t)
  topA0 : ∀ k s, Top (14*k+216) (A0 k s) (A3 (k+1) s)
  topA3 : ∀ k {c s t}, Sub c s t → Top (c+14*k+216) (A3 k s) (A0 (k+1) t)
  sub_haltB3 : ∀ k {c s}, SubHalt c s → SubHalt (c+5*k+80) (B3 k s)
  top_haltA3 : ∀ k {c s}, SubHalt c s → TopHalt (c+5*k+150) (A3 k s)

variable {S : Type} (M : Algebra S)

def tower : List Nat → S → S
  | [], s => s
  | k::ks, s => tower ks (M.A3 k s)

theorem tower_step_len (n : Nat) (ks : List Nat) (hlen : ks.length = n+1)
    {c : Nat} {s t : S} (hc : M.Sub c s t) :
    M.Top (c+g ks) (tower M ks s) (tower M (tick ks) t) := by
  induction n generalizing ks c s t with
  | zero =>
    cases ks with
    | nil => simp at hlen
    | cons k rest =>
      cases rest with
      | nil =>
        have q := M.top_trans (M.topA3 k hc) (M.topA0 (k+1) t)
        change M.Top (c+g [k]) (M.A3 k s) (M.A3 (k+2) t)
        rw [g_singleton]
        rw [show c + (28*k+446) = c+14*k+216+(14*(k+1)+216) by omega]
        exact q
      | cons l ls => simp at hlen
  | succ n ih =>
    cases ks with
    | nil => simp at hlen
    | cons k rest =>
      have hr : rest.length = n+1 := by simp at hlen; omega
      have ht (xs : List Nat) : (tick xs).length = xs.length := shift_length 2 xs
      have h1 := ih rest hr (M.subA3 k s)
      have h2 := ih (tick rest) (by rw [ht]; exact hr) (M.subB3 k hc)
      have h3 := ih (tick (tick rest)) (by rw [ht,ht]; exact hr) (M.subA0 (k+1) t)
      have h4 := ih (tick (tick (tick rest))) (by rw [ht,ht,ht]; exact hr) (M.subB0 (k+1) t)
      have q := M.top_trans h1 (M.top_trans h2 (M.top_trans h3 h4))
      rw [tick_four] at q
      change M.Top (c+g (k::rest)) (tower M rest (M.A3 k s)) (tower M (shift 8 rest) (M.A3 (k+2) t))
      rw [g_unroll]
      rw [show c + (56+g rest+(14*k+132)+g (tick rest)+56+g (tick (tick rest))+(14*(k+1)+132)+g (tick (tick (tick rest)))) = (56+g rest)+((c+14*k+132+g (tick rest))+((56+g (tick (tick rest)))+(14*(k+1)+132+g (tick (tick (tick rest)))))) by omega]
      exact q

theorem tower_step (ks : List Nat) (hne : ks ≠ []) {c : Nat} {s t : S} (hc : M.Sub c s t) :
    M.Top (c+g ks) (tower M ks s) (tower M (tick ks) t) := by
  cases hn : ks.length with
  | zero => exact False.elim (hne (List.eq_nil_of_length_eq_zero hn))
  | succ n => exact tower_step_len M n ks hn hc

theorem tower_halt_len (n : Nat) (ks : List Nat) (hlen : ks.length = n+1)
    {c : Nat} {s : S} (hc : M.SubHalt c s) : M.TopHalt (c+h ks) (tower M ks s) := by
  induction n generalizing ks c s with
  | zero =>
    cases ks with
    | nil => simp at hlen
    | cons k rest =>
      cases rest with
      | nil =>
        change M.TopHalt (c+h [k]) (M.A3 k s)
        rw [h_singleton]
        rw [show c + (5*k+150) = c+5*k+150 by omega]
        exact M.top_haltA3 k hc
      | cons l ls => simp at hlen
  | succ n ih =>
    cases ks with
    | nil => simp at hlen
    | cons k rest =>
      have hr : rest.length = n+1 := by simp at hlen; omega
      have h1 := tower_step_len M n rest hr (M.subA3 k s)
      have h2 := ih (tick rest) (by rw [show (tick rest).length = rest.length from shift_length 2 rest]; exact hr) (M.sub_haltB3 k hc)
      have q := M.top_halt_trans h1 h2
      change M.TopHalt (c+h (k::rest)) (tower M rest (M.A3 k s))
      rw [h_unroll]
      rw [show c + (56+g rest+(5*k+80)+h (tick rest)) = (56+g rest)+(c+5*k+80+h (tick rest)) by omega]
      exact q

theorem tower_halt (ks : List Nat) (hne : ks ≠ []) {c : Nat} {s : S} (hc : M.SubHalt c s) :
    M.TopHalt (c+h ks) (tower M ks s) := by
  cases hn : ks.length with
  | zero => exact False.elim (hne (List.eq_nil_of_length_eq_zero hn))
  | succ n => exact tower_halt_len M n ks hn hc

def absorb (k : Nat) (ks : List Nat) : List Nat := (k+1)::tick (tick ks)
def absorbCost (k : Nat) (ks : List Nat) : Nat :=
  match ks with
  | [] => 14*k+216
  | _::_ => 56+g ks+(14*k+132)+g (tick ks)

theorem tower_absorb (k : Nat) (ks : List Nat) (s : S) :
    M.Top (absorbCost k ks) (tower M ks (M.A0 k s)) (tower M (absorb k ks) s) := by
  cases ks with
  | nil => exact M.topA0 k s
  | cons j js =>
    have hne : j::js ≠ [] := by simp
    have ht : tick (j::js) ≠ [] := shift_ne_nil 2 hne
    have h1 := tower_step M (j::js) hne (M.subA0 k s)
    have h2 := tower_step M (tick (j::js)) ht (M.subB0 k s)
    change M.Top (56+g (j::js)+(14*k+132)+g (tick (j::js))) _ _
    rw [show 56+g (j::js)+(14*k+132)+g (tick (j::js)) = (56+g (j::js))+(14*k+132+g (tick (j::js))) by omega]
    exact M.top_trans h1 h2

#print axioms tower_step
#print axioms tower_halt
#print axioms tower_absorb
end F067Cost
