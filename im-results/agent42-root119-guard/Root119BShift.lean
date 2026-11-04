import Root119Gate
namespace BB6Root119

@[simp] theorem sub_sub_int (x y z : Int) : x - y - z = x - (y+z) := by omega
@[simp] theorem sub_add_int (x y z : Int) : x - y + z = x - (y-z) := by omega

def run : Nat → Conf → Option Conf
  | 0, c => some c
  | n+1, c => (next c).bind (run n)

def shiftTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit t (h-4) true) (h-2) false) (h-1) false) h true

def shifted (c : Conf) : Conf := ⟨.B, c.h-2, shiftTape c.tape c.h⟩

-- Conditions: left tape ends in 10 111, head is B/0.
def valid (c : Conf) : Prop :=
  c.q = .B ∧ c.tape c.h = false ∧
  c.tape (c.h-1) = true ∧ c.tape (c.h-2) = true ∧
  c.tape (c.h-3) = true ∧ c.tape (c.h-4) = false ∧
  c.tape (c.h-5) = true

theorem ten_step (c : Conf) (hv : valid c) : run 10 c = some (shifted c) := by
  rcases c with ⟨q,h,t⟩
  obtain ⟨hq,h0,h1,h2,h3,h4,h5⟩ := hv
  cases q <;> try contradiction
  change t h = false at h0
  change t (h-1) = true at h1
  change t (h-2) = true at h2
  change t (h-3) = true at h3
  change t (h-4) = false at h4
  change t (h-5) = true at h5
  have a1 : h-1 ≠ h := by omega
  have a2 : h-2 ≠ h := by omega
  have a3 : h-3 ≠ h := by omega
  have a4 : h-4 ≠ h := by omega
  have a5 : h-5 ≠ h := by omega
  have b21 : h-2 ≠ h-1 := by omega
  have b31 : h-3 ≠ h-1 := by omega
  have b32 : h-3 ≠ h-2 := by omega
  have b41 : h-4 ≠ h-1 := by omega
  have b42 : h-4 ≠ h-2 := by omega
  have b43 : h-4 ≠ h-3 := by omega
  have b51 : h-5 ≠ h-1 := by omega
  have b52 : h-5 ≠ h-2 := by omega
  have b53 : h-5 ≠ h-3 := by omega
  have b54 : h-5 ≠ h-4 := by omega
  simp (disch := omega) [run, next, shiftTape, shifted, setBit, h0,h1,h2,h3,h4,h5,
    a1,a2,a3,a4,a5,b21,b31,b32,b41,b42,b43,b51,b52,b53,b54]
  funext x
  simp only [setBit]
  by_cases hx0 : x = h <;>
    by_cases hx1 : x = h-1 <;>
    by_cases hx2 : x = h-2 <;>
    by_cases hx3 : x = h-3 <;>
    by_cases hx4 : x = h-4 <;>
    by_cases hx5 : x = h-5 <;>
    simp_all <;> omega

theorem run_add (m n : Nat) (c : Conf) :
    run (m+n) c = (run m c).bind (run n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    have heq : m+1+n = (m+n)+1 := by omega
    rw [heq]
    simp only [run, Option.bind_assoc]
    congr 1
    funext y
    exact ih y

theorem shiftTape_left (t : Int → Bool) (h x : Int)
    (hx : x ≤ h - 5) : shiftTape t h x = t x := by
  have h0 : x ≠ h := by omega
  have h1 : x ≠ h-1 := by omega
  have h2 : x ≠ h-2 := by omega
  have h4 : x ≠ h-4 := by omega
  simp [shiftTape, setBit, h0,h1,h2,h4]

/-- At B/0 the left tape ends in (10)^n 111, from farther left to the head. -/
def extended (n : Nat) (c : Conf) : Prop :=
  c.q = .B ∧ c.tape c.h = false ∧
  c.tape (c.h-1) = true ∧ c.tape (c.h-2) = true ∧
  c.tape (c.h-3) = true ∧
  (∀ i : Nat, i < n →
    c.tape (c.h-5-2*(i:Int)) = true ∧
    c.tape (c.h-4-2*(i:Int)) = false)

theorem extended_valid {n : Nat} (c : Conf) (hv : extended (n+1) c) :
    valid c := by
  obtain ⟨hq,h0,h1,h2,h3,hrest⟩ := hv
  obtain ⟨h5,h4⟩ := hrest 0 (by omega)
  exact ⟨hq,h0,h1,h2,h3,by simpa using h4,by simpa using h5⟩

theorem shifted_extended {n : Nat} (c : Conf)
    (hv : extended (n+1) c) : extended n (shifted c) := by
  rcases c with ⟨q,h,t⟩
  obtain ⟨hq,h0,h1,h2,h3,hrest⟩ := hv
  change t h = false at h0
  change t (h-1) = true at h1
  change t (h-2) = true at h2
  change t (h-3) = true at h3
  change ∀ i : Nat, i < n+1 →
    t (h-5-2*(i:Int)) = true ∧ t (h-4-2*(i:Int)) = false at hrest
  have h5 : t (h-5) = true := by simpa using (hrest 0 (by omega)).1
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · change shiftTape t h (h-2) = false
    simp [shiftTape,setBit,show h-2 ≠ h by omega,
      show h-2 ≠ h-1 by omega]
  · change shiftTape t h (h-2-1) = true
    have heq : h-2-1 = h-3 := by omega
    rw [heq]
    simp [shiftTape,setBit, h3, show h-3 ≠ h by omega,
      show h-3 ≠ h-1 by omega, show h-3 ≠ h-2 by omega,
      show h-3 ≠ h-4 by omega]
  · change shiftTape t h (h-2-2) = true
    have heq : h-2-2 = h-4 := by omega
    rw [heq]
    simp [shiftTape,setBit,show h-4≠h by omega,
      show h-4≠h-1 by omega,show h-4≠h-2 by omega]
  · change shiftTape t h (h-2-3) = true
    have heq : h-2-3 = h-5 := by omega
    rw [heq,shiftTape_left t h (h-5) (by omega),h5]
  · intro i hi
    have old := hrest (i+1) (by omega)
    have heqL : h-2-5-2*(i:Int) = h-5-2*((i+1:Int)) := by omega
    have heqR : h-2-4-2*(i:Int) = h-4-2*((i+1:Int)) := by omega
    constructor
    · change shiftTape t h (h-2-5-2*(i:Int)) = true
      rw [heqL,shiftTape_left t h (h-5-2*((i+1:Int))) (by omega)]
      exact old.1
    · change shiftTape t h (h-2-4-2*(i:Int)) = false
      rw [heqR,shiftTape_left t h (h-4-2*((i+1:Int))) (by omega)]
      exact old.2

def shiftMany : Nat → Conf → Conf
  | 0, c => c
  | n+1, c => shiftMany n (shifted c)

theorem ten_n_steps (n : Nat) (c : Conf) (hc : extended n c) :
    run (10*n) c = some (shiftMany n c) := by
  induction n generalizing c with
  | zero => simp [run,shiftMany]
  | succ n ih =>
    have hv : valid c := extended_valid c hc
    have hn : extended n (shifted c) := shifted_extended c hc
    have hten := ten_step c hv
    have hmany := ih (shifted c) hn
    have heq : 10*(n+1) = 10 + 10*n := by omega
    rw [heq,run_add,hten]
    simpa [shiftMany] using hmany

#print axioms BB6Root119.ten_step
#print axioms BB6Root119.ten_n_steps
end BB6Root119
