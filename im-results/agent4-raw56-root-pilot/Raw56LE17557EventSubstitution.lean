import Raw56LE17557TimeCocycle

/-!
  Full parameterized ABA/BBA event substitution for Raw56 leaf 17557.
  The synthetic event sequence has the EXACT algebraic all-rank clock,
  but connecting it to the actual infinite blank orbit is still open.
  No claim of actual-machine nonhalting is made by this module.
-/

namespace BB6.Agent4Raw56LE17557EventSubstitution
open BB6.Agent4Raw56LE17557TimeCocycle

def expand : Triad → List Triad
  | .aNormal a b c last =>
      let ch := 2*c + lastBit last
      [.aNormal (2*a+2) (2*b+3) ch last,
       .b 2 (ch+5) last, .aCarry 2 (ch+8) 0 last]
  | .aCarry a c d last =>
      let ch := 2*c + lastBit last
      [.aNormal (2*a+2) 13 ch last,
       .b 2 (ch+5) last,
       .aCarry 2 (ch+8) (2*a+2*d+4) last]
  | .b a b last =>
      [.b (2*a+2) (2*b+3+lastBit last) last,
       .b 2 5 false, .aCarry 2 8 0 false]

def expandWord (xs : List Triad) : List Triad := xs.flatMap expand

theorem expand_time (e : Triad) :
    ((expand e).map lowTime).sum = highTime e := by
  cases e with
  | aNormal a b c last =>
      cases last <;>
        simp [expand, highTime, lowTime, aNormalCost, aCarryCost,
          bCost, lastBit] <;> omega
  | aCarry a c d last =>
      cases last <;>
        simp [expand, highTime, lowTime, aNormalCost, aCarryCost,
          bCost, lastBit] <;> omega
  | b a b last =>
      cases last <;>
        simp [expand, highTime, lowTime, aNormalCost, aCarryCost,
          bCost, lastBit] <;> omega

theorem expand_A (e : Triad) :
    ((expand e).map isA).sum = 2*isA e + isB e := by
  cases e <;> simp [expand, isA, isB]

theorem expand_B (e : Triad) :
    ((expand e).map isB).sum = isA e + 2*isB e := by
  cases e <;> simp [expand, isA, isB]

theorem expand_FA (e : Triad) :
    ((expand e).map finalA).sum = 2*finalA e := by
  cases e with
  | aNormal a b c last =>
      cases last <;> simp [expand, finalA, lastBit]
  | aCarry a c d last =>
      cases last <;> simp [expand, finalA, lastBit]
  | b a b last =>
      cases last <;> simp [expand, finalA, lastBit]

theorem expand_FB (e : Triad) :
    ((expand e).map finalB).sum = finalA e + finalB e := by
  cases e with
  | aNormal a b c last =>
      cases last <;> simp [expand, finalA, finalB, lastBit]
  | aCarry a c d last =>
      cases last <;> simp [expand, finalA, finalB, lastBit]
  | b a b last =>
      cases last <;> simp [expand, finalA, finalB, lastBit]

theorem expand_C (e : Triad) :
    ((expand e).map thirdRun).sum =
      4*thirdRun e + 2*finalA e + 8*(isA e+isB e) := by
  cases e with
  | aNormal a b c last =>
      cases last <;>
        simp [expand, thirdRun, finalA, isA, isB, lastBit] <;> omega
  | aCarry a c d last =>
      cases last <;>
        simp [expand, thirdRun, finalA, isA, isB, lastBit] <;> omega
  | b a b last =>
      cases last <;>
        simp [expand, thirdRun, finalA, isA, isB, lastBit] <;> omega

def A (xs : List Triad) : Nat := (xs.map isA).sum
def B (xs : List Triad) : Nat := (xs.map isB).sum
def C (xs : List Triad) : Nat := (xs.map thirdRun).sum
def FA (xs : List Triad) : Nat := (xs.map finalA).sum
def FB (xs : List Triad) : Nat := (xs.map finalB).sum
def clock (xs : List Triad) : Nat := (xs.map lowTime).sum

theorem transport_A (xs : List Triad) :
    A (expandWord xs) = 2*A xs + B xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map isA).sum =
        2*(isA e + (es.map isA).sum) +
        (isB e + (es.map isB).sum)
      rw [List.map_append, List.sum_append, expand_A]
      simp only [A, B] at ih
      omega

theorem transport_B (xs : List Triad) :
    B (expandWord xs) = A xs + 2*B xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map isB).sum =
        (isA e + (es.map isA).sum) +
        2*(isB e + (es.map isB).sum)
      rw [List.map_append, List.sum_append, expand_B]
      simp only [A, B] at ih
      omega

theorem transport_FA (xs : List Triad) :
    FA (expandWord xs) = 2*FA xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map finalA).sum =
        2*(finalA e + (es.map finalA).sum)
      rw [List.map_append, List.sum_append, expand_FA]
      simp only [FA] at ih
      omega

theorem transport_FB (xs : List Triad) :
    FB (expandWord xs) = FA xs + FB xs := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map finalB).sum =
        (finalA e + (es.map finalA).sum) +
        (finalB e + (es.map finalB).sum)
      rw [List.map_append, List.sum_append, expand_FB]
      simp only [FA, FB] at ih
      omega

theorem transport_C (xs : List Triad) :
    C (expandWord xs) =
      4*C xs + 2*FA xs + 8*(A xs + B xs) := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map thirdRun).sum =
        4*(thirdRun e + (es.map thirdRun).sum) +
        2*(finalA e + (es.map finalA).sum) +
        8*(isA e + (es.map isA).sum +
           (isB e + (es.map isB).sum))
      rw [List.map_append, List.sum_append, expand_C]
      simp only [A, B, C, FA] at ih
      omega

theorem transport_clock (xs : List Triad) :
    clock (expandWord xs) = (xs.map highTime).sum := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      change ((expand e ++ expandWord es).map lowTime).sum =
        highTime e + (es.map highTime).sum
      rw [List.map_append, List.sum_append, expand_time]
      change clock (expandWord es) = (es.map highTime).sum at ih
      simpa [clock] using ih

theorem transport_clock_balanced (xs : List Triad)
    (hbal : A xs = B xs) :
    clock (expandWord xs) =
      2*clock xs + 152*A xs + 8*C xs + 6*FA xs + 2*FB xs := by
  rw [transport_clock, balanced_word_cocycle]
  · rfl
  · exact hbal

def baseEvents : List Triad :=
  [.aCarry 2 7 0 true, .b 6 12 true,
   .b 2 5 false, .aCarry 2 8 0 false]

theorem base_observables :
    A baseEvents = 2 ∧ B baseEvents = 2 ∧
    FA baseEvents = 1 ∧ FB baseEvents = 1 ∧
    C baseEvents = 15 ∧ clock baseEvents = 212 := by decide

/-- Abstract all-rank epochs, NOT a claim about the original blank orbit. -/
def epochs : Nat → List Triad
  | 0 => baseEvents
  | n+1 => expandWord (epochs n)

theorem epoch_observables (n : Nat) :
    A (epochs n) = 2*3^n ∧
    B (epochs n) = 2*3^n ∧
    FA (epochs n) = 2^n ∧
    FB (epochs n) = 2^n ∧
    C (epochs n) + 32*3^n + 2^n = 48*4^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rcases ih with ⟨ha, hb, hfa, hfb, hc⟩
      change A (expandWord (epochs n)) = 2*3^(n+1) ∧
        B (expandWord (epochs n)) = 2*3^(n+1) ∧
        FA (expandWord (epochs n)) = 2^(n+1) ∧
        FB (expandWord (epochs n)) = 2^(n+1) ∧
        C (expandWord (epochs n)) + 32*3^(n+1) +
          2^(n+1) = 48*4^(n+1)
      rw [transport_A, transport_B, transport_FA, transport_FB,
          transport_C, ha, hb, hfa, hfb]
      simp only [Nat.pow_succ]
      omega

theorem epoch_clock (n : Nat) :
    clock (epochs n) + 28*2^n = 192*4^n + 48*3^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rcases epoch_observables n with ⟨ha,hb,hfa,hfb,hc⟩
      have hbal : A (epochs n) = B (epochs n) := ha.trans hb.symm
      change clock (expandWord (epochs n)) + 28*2^(n+1) =
        192*4^(n+1) + 48*3^(n+1)
      rw [transport_clock_balanced _ hbal, ha, hfa, hfb]
      simp only [Nat.pow_succ]
      omega

#print axioms expand_time
#print axioms expand_C
#print axioms transport_A
#print axioms transport_C
#print axioms epoch_observables
#print axioms epoch_clock
end BB6.Agent4Raw56LE17557EventSubstitution
