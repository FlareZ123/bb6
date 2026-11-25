import Lean
namespace BB6.Agent45ReverseBlock

/-- Target digits in reverse chronological order. -/
def digits : List Nat → Nat
  | [] => 0
  | y::ys => 2*digits ys+y

/-- Correction to the static modulus due to the unit clock decrement. -/
def corr : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,B => 2*corr k (B/2)+(k+1)*(B%2)

/-- Every adjacent correction increases by at most the last clock decrement. -/
theorem corr_adjacent (k B : Nat) : corr k (B+1) ≤ corr k B+k := by
  induction k generalizing B with
  | zero => simp [corr]
  | succ k ih =>
    by_cases h : B%2=0
    · have h1 : (B+1)%2=1 := by omega
      have h2 : (B+1)/2=B/2 := by omega
      simp [corr,h,h1,h2]
    · have h0 : B%2=1 := by omega
      have h1 : (B+1)%2=0 := by omega
      have h2 : (B+1)/2=B/2+1 := by omega
      have hi := ih (B/2)
      simp only [corr,h0,h1,h2,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
      omega

theorem corr_bound (k B : Nat) : corr k B+k+2≤2^(k+1) := by
  induction k generalizing B with
  | zero => simp [corr]
  | succ k ih =>
    have h := ih (B/2)
    have hb : B%2=0 ∨ B%2=1 := by omega
    simp only [corr,Nat.pow_succ] at *
    rcases hb with hb|hb <;> simp [hb] <;> omega

/-- Rewinding from the terminal clock F. The current modulus is F-k-1.
    The source carry guard is strict: a second wrap is illegal. -/
inductive Walk (F z : Nat) : List Nat → Nat → Prop
  | nil (hz : z<F) : Walk F z [] z
  | step (ys : List Nat) (c y b r : Nat)
      (h : Walk F z ys c) (hy : y≤1) (hb : b≤1)
      (hc : c<F-(ys.length+1)) (hr : r<F-(ys.length+1))
      (he : 2*c+y=r+(F-(ys.length+1))*b) : Walk F z (y::ys) r

theorem walk_bound {F z ys r} (h : Walk F z ys r) : r<F-ys.length := by
  cases h with
  | nil hz => simpa using hz
  | step ys c y b r h hy hb hc hr he => simpa using hr

theorem eq_of_walk {F z ys r} (h : Walk F z ys r) :
    ∃ B, B<2^ys.length ∧
      2^ys.length*z+digits ys+corr ys.length B=F*B+r := by
  induction h with
  | nil hz => exact ⟨0,by simp,by simp [digits,corr]⟩
  | step ys c y b r h hy hb hc hr he ih =>
    obtain ⟨B,hB,hEq⟩ := ih
    refine ⟨2*B+b,?_,?_⟩
    · simp only [List.length_cons,Nat.pow_succ]; omega
    have hd : (2*B+b)/2=B := by omega
    have hm : (2*B+b)%2=b := by omega
    have hF : F*(2*B+b)=2*(F*B)+F*b := by rw [Nat.mul_add]; ac_rfl
    have hp : 2^(ys.length+1)*z=2*(2^ys.length*z) := by rw [Nat.pow_succ]; ac_rfl
    have hclock : F=F-(ys.length+1)+(ys.length+1) := by omega
    have hprod : F*b=(F-(ys.length+1))*b+(ys.length+1)*b := by
      calc
        _ = (F-(ys.length+1)+(ys.length+1))*b := congrArg (· * b) hclock
        _ = _ := Nat.add_mul _ _ _
    simp only [List.length_cons,digits,corr,hd,hm]
    rw [hp,hF,hprod]
    omega

/-- Final range alone suffices to certify every internal guard of the chosen word. -/
theorem walk_of_eq (F z : Nat) (ys : List Nat) (B r : Nat)
    (hys : ∀ y∈ys, y≤1) (hB : B<2^ys.length) (hr : r<F-ys.length)
    (he : 2^ys.length*z+digits ys+corr ys.length B=F*B+r) : Walk F z ys r := by
  induction ys generalizing B r with
  | nil =>
    have h0 : B=0 := by simpa using hB
    subst B
    simp [digits,corr] at he
    subst r
    exact Walk.nil (by simpa using hr)
  | cons y ys ih =>
    let k := ys.length
    let C := B/2
    let b := B%2
    let q := F-(k+1)
    let T := 2^k*z+digits ys+corr k C
    let U := F*C
    have hy : y≤1 := hys y (by simp)
    have hb : b≤1 := by dsimp [b]; omega
    have hC : C<2^k := by simp only [List.length_cons,Nat.pow_succ] at hB; dsimp [C,k]; omega
    have hq : r<q := by simpa [q,k] using hr
    have hBC : B=2*C+b := by dsimp [C,b]; omega
    have hF : F*B=2*U+F*b := by rw [hBC,Nat.mul_add]; dsimp [U]; ac_rfl
    have hp : 2^(ys.length+1)*z=2*(2^k*z) := by rw [Nat.pow_succ]; dsimp [k]; ac_rfl
    have hclock : F=q+(k+1) := by dsimp [q]; omega
    have hprod : F*b=q*b+(k+1)*b := by
      calc
        _ = (q+(k+1))*b := congrArg (· * b) hclock
        _ = _ := Nat.add_mul _ _ _
    simp only [List.length_cons,digits,corr] at he
    change 2^(ys.length+1)*z+(2*digits ys+y)+(2*corr k C+(k+1)*b)=F*B+r at he
    rw [hp,hF,hprod] at he
    have he' : 2*T+y=2*U+q*b+r := by dsimp [T,U] at *; omega
    have hTU : U≤T := by omega
    let p := T-U
    have hpre : T=U+p := by dsimp [p]; omega
    have hstep : 2*p+y=r+q*b := by omega
    have hprod' : q*b≤q := by rcases (show b=0 ∨ b=1 by omega) with h|h <;> simp [h]
    have hplt : p<q := by omega
    have hwalk : Walk F z ys p := ih C p (fun d hd => hys d (by simp [hd])) hC (by dsimp [q,k] at hplt; omega) hpre
    exact Walk.step ys p y b r hwalk hy hb hplt hq hstep

/-- Any legal wrap word lies within one above the static quotient. -/
theorem word_near (F k X B r : Nat) (hF : 0<F) (hfit : 2^(k+1)≤F)
    (hr : r<F-k) (he : X+corr k B=F*B+r) : X/F≤B ∧ B≤X/F+1 := by
  have hc := corr_bound k B
  have hlow : X<F*(B+1) := by rw [Nat.mul_add]; simp; omega
  have hhigh : F*B<X+F := by omega
  have hdiv := Nat.div_add_mod X F
  have hrem := Nat.mod_lt X hF
  have hhigh' : F*B<F*(X/F+2) := by rw [Nat.mul_add]; omega
  have hh := (Nat.div_lt_iff_lt_mul hF).2 (by simpa [Nat.mul_comm] using hlow)
  have hh' : B<X/F+2 := Nat.lt_of_mul_lt_mul_left hhigh'
  omega

/-- Adjacent valid wrap words cannot share the same input. -/
theorem adjacent_impossible (F k X B r t : Nat) (hr : r<F-k) (_ht : t<F-k)
    (h1 : X+corr k B=F*B+r) (h2 : X+corr k (B+1)=F*(B+1)+t) : False := by
  have h := corr_adjacent k B
  rw [Nat.mul_add,Nat.mul_one] at h2
  omega

/-- Candidate validation uses only the final corrected remainder and the word length. -/
def candidate (F k X B : Nat) : Option Nat :=
  if B<2^k ∧ F*B≤X+corr k B ∧ X+corr k B-F*B<F-k then
    some (X+corr k B-F*B) else none

theorem candidate_iff (F k X B r : Nat) : candidate F k X B=some r ↔
    B<2^k ∧ r<F-k ∧ X+corr k B=F*B+r := by
  unfold candidate
  split <;> rename_i h
  · simp only [Option.some.injEq]; constructor
    · intro he; exact ⟨h.1,by omega,by omega⟩
    · intro he; omega
  · constructor
    · intro he; contradiction
    · intro he; exact False.elim (h ⟨he.1,by omega,by omega⟩)

def fast (F k X : Nat) : Option Nat :=
  match candidate F k X (X/F) with
  | some r => some r
  | none => candidate F k X (X/F+1)

theorem fast_eq_some {F z ys r} (h : Walk F z ys r) (hfit : 2^(ys.length+1)≤F) :
    fast F ys.length (2^ys.length*z+digits ys)=some r := by
  let k := ys.length
  let X := 2^k*z+digits ys
  obtain ⟨B,hB,he⟩ := eq_of_walk h
  have hr := walk_bound h
  have hnear := word_near F k X B r (by have := Nat.two_pow_pos (k+1); omega) hfit hr he
  have hc := (candidate_iff F k X B r).2 ⟨hB,hr,he⟩
  change fast F k X=some r
  by_cases hB0 : B=X/F
  · rw [hB0] at hc; simp [fast,hc]
  · have hB1 : B=X/F+1 := by omega
    rw [hB1] at hc he
    cases hfirst : candidate F k X (X/F) with
    | none => simp [fast,hfirst,hc]
    | some t =>
      have ht := (candidate_iff F k X (X/F) t).1 hfirst
      exact False.elim (adjacent_impossible F k X (X/F) t r ht.2.1 hr ht.2.2 he)

theorem walk_of_fast {F z ys r} (hys : ∀ y∈ys, y≤1)
    (h : fast F ys.length (2^ys.length*z+digits ys)=some r) : Walk F z ys r := by
  unfold fast at h
  split at h <;> rename_i he
  · simp only [Option.some.injEq] at h
    subst r
    have hc := (candidate_iff _ _ _ _ _).1 he
    exact walk_of_eq _ _ _ _ _ hys hc.1 hc.2.1 hc.2.2
  · have hc := (candidate_iff _ _ _ _ _).1 h
    exact walk_of_eq _ _ _ _ _ hys hc.1 hc.2.1 hc.2.2

/-- The exact fixed-bit reverse block relation, with no hidden intermediate guard. -/
theorem fast_iff_walk (F z : Nat) (ys : List Nat) (r : Nat)
    (hys : ∀ y∈ys, y≤1) (hfit : 2^(ys.length+1)≤F) :
    fast F ys.length (2^ys.length*z+digits ys)=some r ↔ Walk F z ys r :=
  ⟨walk_of_fast hys,fun h => fast_eq_some h hfit⟩

#print axioms corr_adjacent
#print axioms eq_of_walk
#print axioms walk_of_eq
#print axioms fast_iff_walk
end BB6.Agent45ReverseBlock
