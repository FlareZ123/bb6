import Std

namespace BB6.HaltingFunnel

def G (k c : Nat) : Nat × Nat :=
  if h : c < 2*k then
    G (k - (c/2 + 1)) (2*c + 3)
  else if c ≤ 2*k+1 then
    (0, 2*c+3)
  else
    (4*k+4, c-(2*k+2))
termination_by k
decreasing_by omega

def T (a c : Nat) : Option (Nat × Nat) :=
  if c = 0 then some (2, a+1)
  else if c = 1 then some (a+2, 0)
  else if a % 2 = 0 then some (a+3, c-2)
  else if c = 2 then none
  else if c = 3 then some (G (a/2) 1)
  else some (G (a/2 + 1) (c-2))

/-- The even \`a\`-coordinates encountered in the halting funnel. -/
def E : Nat → Nat
  | 0 => 2
  | j+1 => 2*E j+12

/-- The \`c\`-coordinate with \`n\` more doubling stages remaining. -/
def C (j : Nat) : Nat → Nat
  | 0 => 4
  | n+1 => C (j+1) n + E j + 10

theorem E_even (j : Nat) : E j % 2 = 0 := by
  induction j with
  | zero => decide
  | succ j ih => simp [E]

theorem C_ge_four (j n : Nat) : 4 ≤ C j n := by
  induction n generalizing j with
  | zero => simp [C]
  | succ n ih => simp only [C]; have h := ih (j+1); omega

theorem E_closed (j : Nat) : E j + 12 = 14*2^j := by
  induction j with
  | zero => decide
  | succ j ih =>
    simp only [E, Nat.pow_succ]
    omega

theorem C_closed (j n : Nat) :
    C j n + 14*2^j + 2*n = 14*2^(j+n)+4 := by
  induction n generalizing j with
  | zero => simp only [C, Nat.mul_zero, Nat.add_zero]; omega
  | succ n ih =>
    have h := ih (j+1)
    have he := E_closed j
    have hp : 14*2^(j+1) = 2*(14*2^j) := by
      rw [Nat.pow_succ]
      omega
    have hr : 2^(j+(n+1)) = 2^((j+1)+n) := by
      congr 1
      omega
    simp only [C]
    rw [hr]
    rw [hp] at h
    omega

theorem A_closed (n : Nat) :
    (C 0 n-1) + 2*n + 11 = 14*2^n := by
  have hc := C_closed 0 n
  have hp := C_ge_four 0 n
  simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hc
  omega

theorem G_big (k c : Nat) (h : 2*k+2 ≤ c) :
    G k c = (4*k+4, c-(2*k+2)) := by
  rw [G]
  simp [show ¬c < 2*k by omega, show ¬c ≤ 2*k+1 by omega]

theorem T_even (a c : Nat) (ha : a % 2 = 0) (hc : 2 ≤ c) :
    T a c = some (a+3, c-2) := by
  simp [T, show c ≠ 0 by omega, show c ≠ 1 by omega, ha]

theorem T_gate (a : Nat) (ha : a % 2 = 0) :
    T (a+3) 2 = none := by
  unfold T
  simp [show (a+3)%2 ≠ 0 by omega]

/-- The two accelerated steps of one doubling stage. -/
theorem T_stage (j n : Nat) :
    T (E j) (C j (n+1)) = some (E j+3, C j (n+1)-2) ∧
    T (E j+3) (C j (n+1)-2) = some (E (j+1), C (j+1) n) := by
  have ce : 4 ≤ C (j+1) n := C_ge_four (j+1) n
  have ee : E j % 2 = 0 := E_even j
  have hc : C j (n+1) = C (j+1) n + E j + 10 := rfl
  constructor
  · exact T_even _ _ ee (by omega)
  · have hpar : (E j+3) % 2 ≠ 0 := by omega
    have h2 : C j (n+1)-2 ≠ 0 := by omega
    have h1 : C j (n+1)-2 ≠ 1 := by omega
    have hsmall : C j (n+1)-2 ≠ 2 := by omega
    have hthree : C j (n+1)-2 ≠ 3 := by omega
    have hk : (E j+3)/2+1 = E j/2+2 := by omega
    have hbound : 2*((E j+3)/2+1)+2 ≤ C j (n+1)-4 := by omega
    simp only [T, if_neg h2, if_neg h1, if_neg hpar,
      if_neg hsmall, if_neg hthree]
    have hsub : C j (n+1)-2-2 = C j (n+1)-4 := by omega
    rw [hsub, G_big _ _ hbound]
    simp only [Option.some.injEq]
    have hev : E j = 2*(E j/2) := by omega
    change (4*((E j+3)/2+1)+4,
            (C j (n+1)-2)-2-(2*((E j+3)/2+1)+2)) =
           (2*E j+12, C (j+1) n)
    apply Prod.ext <;> omega

inductive Halts : Nat → Nat → Prop where
  | now (a c : Nat) : T a c = none → Halts a c
  | next (a c a' c' : Nat) : T a c = some (a', c') → Halts a' c' → Halts a c

/-- Every member of the explicit doubling family halts under the accelerated map. -/
theorem halts_family (j n : Nat) : Halts (E j) (C j n) := by
  induction n generalizing j with
  | zero =>
    have h1 := T_even (E j) 4 (E_even j) (by omega)
    have h2 := T_gate (E j) (E_even j)
    exact Halts.next (E j) 4 (E j+3) 2 h1 (Halts.now _ _ h2)
  | succ n ih =>
    obtain ⟨h1,h2⟩ := T_stage j n
    exact Halts.next _ _ _ _ h1 (Halts.next _ _ _ _ h2 (ih (j+1)))

/-- Infinitely many explicit (synthetic) \`P1(a,0)\` states are halting. -/
theorem halts_from_zero (n : Nat) : Halts (C 0 n-1) 0 := by
  have hc := C_ge_four 0 n
  have ht : T (C 0 n-1) 0 = some (2, C 0 n) := by
    simp only [T, ite_true]
    have h : C 0 n - 1 + 1 = C 0 n := by omega
    rw [h]
  exact Halts.next _ _ _ _ ht (halts_family 0 n)

inductive HaltsIn : Nat → Nat → Nat → Prop where
  | now (a c : Nat) : T a c = none → HaltsIn 1 a c
  | next (steps a c a' c' : Nat) :
      T a c = some (a', c') → HaltsIn steps a' c' →
      HaltsIn (steps+1) a c

/-- Exactly \`2*n+2\` calls to \`T\`, counting the final halting call. -/
theorem halts_family_exact (j n : Nat) :
    HaltsIn (2*n+2) (E j) (C j n) := by
  induction n generalizing j with
  | zero =>
    have h1 := T_even (E j) 4 (E_even j) (by omega)
    have h2 := T_gate (E j) (E_even j)
    exact HaltsIn.next 1 _ _ _ _ h1 (HaltsIn.now _ _ h2)
  | succ n ih =>
    obtain ⟨h1,h2⟩ := T_stage j n
    have hr := HaltsIn.next (2*n+2) _ _ _ _ h2 (ih (j+1))
    have hrs := HaltsIn.next (2*n+3) _ _ _ _ h1 hr
    have he : 2*(n+1)+2 = 2*n+3+1 := by omega
    rw [he]
    exact hrs

/-- Exact accelerated halting time from every member of the \`a,0\` family. -/
theorem halts_from_zero_exact (n : Nat) :
    HaltsIn (2*n+3) (C 0 n-1) 0 := by
  have hc := C_ge_four 0 n
  have ht : T (C 0 n-1) 0 = some (2, C 0 n) := by
    simp only [T, ite_true]
    have h : C 0 n - 1 + 1 = C 0 n := by omega
    rw [h]
  exact HaltsIn.next (2*n+2) _ _ _ _ ht (halts_family_exact 0 n)

#print axioms BB6.HaltingFunnel.halts_from_zero_exact
#print axioms BB6.HaltingFunnel.halts_from_zero
end BB6.HaltingFunnel
