import Packet

namespace BB6.Agent7
open BB6.P1Reduction

/-- Fuelled, kernel-reducible version of G. k recursive calls always suffice. -/
def Gfuel : Nat → Nat → Nat → Nat × Nat
  | 0, k, c => if c ≤ 2*k+1 then (0,2*c+3) else (4*k+4,c-(2*k+2))
  | f+1, k, c =>
      if c<2*k then Gfuel f (k-(c/2+1)) (2*c+3)
      else if c≤2*k+1 then (0,2*c+3)
      else (4*k+4,c-(2*k+2))

def Gfast (k c : Nat) := Gfuel k k c

theorem Gfuel_correct (f k c : Nat) (hf : k ≤ f) :
    Gfuel f k c = G k c := by
  induction f generalizing k c with
  | zero =>
    have hk : k=0 := by omega
    subst k
    simp [Gfuel,G]
  | succ f ih =>
    by_cases h : c<2*k
    · have hk' : k-(c/2+1) ≤ f := by omega
      simp only [Gfuel, h, ite_true]
      rw [G]
      simp only [h, dite_true]
      exact ih _ _ hk'
    · rw [G]
      simp only [h, dite_false]
      by_cases h2 : c ≤ 2*k+1
      · simp [Gfuel,h,h2]
      · simp [Gfuel,h,h2]

theorem Gfast_correct (k c : Nat) : Gfast k c = G k c :=
  Gfuel_correct k k c (Nat.le_refl _)

def Tfast (a c : Nat) : Option (Nat × Nat) :=
  if c = 0 then some (2,a+1)
  else if c = 1 then some (a+2,0)
  else if a%2=0 then some (a+3,c-2)
  else if c=2 then none
  else if c=3 then some (Gfast (a/2) 1)
  else some (Gfast (a/2+1) (c-2))

theorem Tfast_correct (a c : Nat) : Tfast a c = T a c := by
  simp only [Tfast,T,Gfast_correct]

def mass (s : Nat × Nat) : Nat := s.1+s.2

def iterFast : Nat → Nat × Nat → Option (Nat × Nat)
  | 0,s => some s
  | n+1,s => (Tfast s.1 s.2).bind (iterFast n)

theorem iterFast_correct (n : Nat) (s : Nat × Nat) :
    iterFast n s = iterT n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [iterFast,iterT,Tfast_correct]
    cases h : T s.1 s.2 with
    | none => simp [h]
    | some t => simp [h,ih]

theorem iterT_mass_mono (n : Nat) (s t : Nat × Nat)
    (h : iterT n s = some t) : mass s ≤ mass t := by
  induction n generalizing s with
  | zero =>
    simp [iterT] at h
    subst t
    omega
  | succ n ih =>
    simp only [iterT] at h
    cases ht : T s.1 s.2 with
    | none => simp [ht] at h
    | some u =>
      simp only [ht, Option.bind_some] at h
      have hh := T_mass_increases s.1 s.2 u.1 u.2 ht
      have hi := ih u h
      simp [mass] at *
      omega

theorem iterT_add (m n : Nat) (s : Nat × Nat) :
    iterT (m+n) s = (iterT m s).bind (iterT n) := by
  induction m generalizing s with
  | zero => simp [iterT]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [iterT]
    cases hs : T s.1 s.2 with
    | none => simp [hs]
    | some u => simp [hs,ih]

theorem iterT_mass_strict (n : Nat) (s t : Nat × Nat)
    (h : iterT (n+1) s = some t) : mass s < mass t := by
  simp only [iterT] at h
  cases hs : T s.1 s.2 with
  | none => simp [hs] at h
  | some u =>
    simp only [hs,Option.bind_some] at h
    have hstep := T_mass_increases s.1 s.2 u.1 u.2 hs
    have htail := iterT_mass_mono n u t h
    simp only [mass] at *
    omega

/-- Exactly two consecutive computed states bracket a target mass;
    this excludes that particular state from all times. -/
theorem no_target_bracket (k : Nat) (p q target : Nat × Nat)
    (hp : iterT k (2,1) = some p)
    (hstep : T p.1 p.2 = some q)
    (hlo : mass p < mass target)
    (hhi : mass target ≤ mass q)
    (hne : q ≠ target) :
    ∀ n, iterT n (2,1) ≠ some target := by
  have hq : iterT (k+1) (2,1) = some q := by
    rw [iterT_add]
    simp [hp,iterT,hstep]
  intro n htarget
  by_cases hn : n ≤ k
  · have hre : iterT (n+(k-n)) (2,1) = some p := by
      simpa [Nat.add_sub_of_le hn] using hp
    rw [iterT_add] at hre
    rw [htarget] at hre
    simp only [Option.bind_some] at hre
    have hm := iterT_mass_mono (k-n) target p hre
    omega
  · by_cases he : n=k+1
    · rw [he,hq] at htarget
      exact hne (Option.some.inj htarget)
    · have hn2 : k+1 < n := by omega
      have hs : iterT ((k+1)+(n-(k+1))) (2,1) = some target := by
        simpa [Nat.add_sub_of_le (show k+1 ≤ n by omega)] using htarget
      rw [iterT_add,hq] at hs
      simp only [Option.bind_some] at hs
      have hpositive : n-(k+1) = (n-k-2)+1 := by omega
      rw [hpositive] at hs
      have hmass := iterT_mass_strict (n-k-2) q target hs
      omega

def critical (n : Nat) : Nat := 14*2^n-2*n-10

set_option maxRecDepth 32768
set_option maxHeartbeats 0

end BB6.Agent7
