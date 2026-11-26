import C9PairConjugacy
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
namespace C9Pair
set_option linter.unusedSimpArgs false

def rep (b : Bool) (n : Nat) (t : Stream) : Stream := fun k => if k<n then b else t (k-n)
def alt (n : Nat) (t : Stream) : Stream := fun k => if k<2*n then k%2==0 else t (k-2*n)
def zero : Stream := fun _ => false
@[simp] theorem rep_zero (b : Bool) (t : Stream) : rep b 0 t = t := by funext k; simp [rep]
@[simp] theorem rep_succ (b : Bool) (n : Nat) (t : Stream) : rep b (n+1) t = push b (rep b n t) := by
  funext k
  cases k with
  | zero => simp [rep,push]
  | succ k => simp only [rep,push]; split <;> split <;> first | rfl | omega | congr 1 <;> omega
@[simp] theorem alt_zero (t : Stream) : alt 0 t = t := by funext k; simp [alt]
@[simp] theorem alt_succ (n : Nat) (t : Stream) : alt (n+1) t = push true (push false (alt n t)) := by
  funext k
  cases k with
  | zero => simp [alt,push] <;> omega
  | succ k =>
    cases k with
    | zero => simp [alt,push] <;> omega
    | succ k =>
      simp only [alt,push]; split <;> split <;> first | rfl | omega | congr 1 <;> omega

theorem rep_one (b : Bool) (t : Stream) : rep b 1 t = push b t := by rw [show 1=0+1 by rfl, rep_succ,rep_zero]
theorem rep_two (b : Bool) (t : Stream) : rep b 2 t = push b (push b t) := by rw [show 2=1+1 by rfl, rep_succ,rep_one]
theorem alt_one (t : Stream) : alt 1 t = push true (push false t) := by rw [show 1=0+1 by rfl, alt_succ,alt_zero]

theorem rep_append (b : Bool) (n m : Nat) (t : Stream) :
    rep b n (rep b m t) = rep b (n+m) t := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.succ_add,ih]

theorem alt_append (n m : Nat) (t : Stream) : alt n (alt m t) = alt (n+m) t := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.succ_add,ih]

@[simp] theorem push_zero_blank : push false zero = zero := by funext n; cases n <;> rfl
@[simp] theorem rep_zero_blank (n : Nat) : rep false n zero = zero := by
  induction n <;> simp [*]

def atL (q : Q) (l r : Stream) : Config := ⟨q,pop l,l 0,r⟩
def atR (q : Q) (l r : Stream) : Config := ⟨q,l,r 0,pop r⟩
def B0 (l r : Stream) : Config := ⟨.B,l,false,r⟩
def Y (a : Nat) (w r : Stream) : Config := B0 (rep true a (push false (push false w))) r

def extra (short : Bool) : Nat := if short then 0 else 2

theorem join {short : Bool} {n k : Nat} {a b c : Config}
    (h : run short n a = some b) (g : run short k b = some c) :
    run short (n+k) a = some c := by rw [run_add,h]; exact g

theorem join_none {short : Bool} {n k : Nat} {a b : Config}
    (h : run short n a = some b) (g : run short k b = none) :
    run short (n+k) a = none := by rw [run_add,h]; exact g

theorem c_sweep (short : Bool) (n : Nat) (l r : Stream) :
    run short n (atL .C (rep true n l) r) =
      some (atL .C l (rep false n r)) := by
  induction n generalizing l r with
  | zero => simp only [rep_zero,alt_zero,Nat.mul_zero,run] <;> rfl
  | succ n ih =>
    have h1 : run short 1 (atL .C (rep true (n+1) l) r) =
        some (atL .C (rep true n l) (rep false 1 r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
    have h := join h1 (ih l (rep false 1 r))
    rwa [rep_append,show 1+n=n+1 by omega] at h

theorem e_sweep (short : Bool) (n : Nat) (l r : Stream) :
    run short n (atR .E l (rep false n r)) =
      some (atR .E (rep true n l) r) := by
  induction n generalizing l r with
  | zero => simp only [rep_zero,alt_zero,Nat.mul_zero,run] <;> rfl
  | succ n ih =>
    have h1 : run short 1 (atR .E l (rep false (n+1) r)) =
        some (atR .E (rep true 1 l) (rep false n r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
    have h := join h1 (ih (rep true 1 l) r)
    rwa [rep_append,show 1+n=n+1 by omega] at h

-- At the B0 entry the scanned zero is not in either stream.
theorem y_to_e (short : Bool) (a : Nat) (w r : Stream) :
    run short (2*a+4) (Y a w r) = some (atR .E (rep true (a+2) w) (push true r)) := by
  have h1 : run short 1 (Y a w r) = some (atL .C (rep true a (push false (push false w))) (push true r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
  have h2 := c_sweep short a (push false (push false w)) (push true r)
  have h3 : run short 1 (atL .C (push false (push false w)) (rep false a (push true r))) =
      some (atR .E w (rep false (a+2) (push true r))) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
  have h4 := e_sweep short (a+2) w (push true r)
  have h := join (join (join h1 h2) h3) h4
  rwa [show 1+a+1+(a+2)=2*a+4 by omega] at h

theorem e_pair (short : Bool) (l r : Stream) :
    run short 4 (atR .E l (push true (push true (push true r)))) =
      some (atR .E (alt 1 l) (push true r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem e_pairs (short : Bool) (k : Nat) (l r : Stream) :
    run short (4*k) (atR .E l (rep true (2*k) (push true r))) =
      some (atR .E (alt k l) (push true r)) := by
  induction k generalizing l r with
  | zero => simp only [rep_zero,alt_zero,Nat.mul_zero,run] <;> rfl
  | succ k ih =>
    -- Use the final pair after the preceding k pairs, avoiding a large reduction.
    have h2 := ih l (push true (push true r))
    have h3 := e_pair short (alt k l) r
    have h := join h2 h3
    rw [show 4*k+4=4*(k+1) by omega] at h
    have hleft : rep true (2*k) (push true (push true (push true r))) =
        rep true (2*(k+1)) (push true r) := by
      rw [← rep_two true (push true r)]
      rw [rep_append,show 2*k+2=2*(k+1) by omega]
    have hright : alt 1 (alt k l) = alt (k+1) l := by
      rw [alt_append, Nat.add_comm]
    rwa [hleft,hright] at h

theorem e_odd_double (short : Bool) (l z : Stream) :
    run short 2 (atR .E l (push true (push false (push false z)))) =
      some (B0 (alt 1 l) z) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem e_odd_single (short : Bool) (l z : Stream) :
    run short 4 (atR .E l (push true (push false (push true z)))) =
      some (B0 l (rep true 2 z)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem e_even_double (short : Bool) (l z : Stream) :
    run short (5+extra short) (atR .E l (push true (push true (push false (push false z))))) =
      some (B0 (push false l) (rep true 2 z)) := by cases short <;> first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem e_even_single_live (short : Bool) (l z : Stream) :
    run short 3 (atR .E l (push true (push true (push false (push true z))))) =
      some ⟨.F,push short (push false (push false l)),true,z⟩ := by cases short <;> first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem e_even_single_halt (short : Bool) (l z : Stream) :
    run short 4 (atR .E l (push true (push true (push false (push true z))))) = none := by
  cases short <;> first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem x0 (short : Bool) (l r : Stream) :
    run short 6 (B0 (push false (push true l)) r) =
      some (B0 l (rep true 2 r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl

theorem x_pos (short : Bool) (a : Nat) (l r : Stream) :
    run short (a+5) (B0 (rep true (a+1) (push false (push true l))) r) =
      some (B0 (alt 1 l) (rep false a (push true r))) := by
  have h1 : run short 1 (B0 (rep true (a+1) (push false (push true l))) r) =
      some (atL .C (rep true (a+1) (push false (push true l))) (push true r)) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
  have h2 := c_sweep short (a+1) (push false (push true l)) (push true r)
  have h3 : run short 3 (atL .C (push false (push true l)) (rep false (a+1) (push true r))) =
      some (B0 (alt 1 l) (rep false a (push true r))) := by first | rfl | simp only [rep_zero,alt_zero,rep_succ,rep_one,rep_two,alt_succ,alt_one] <;> rfl
  have h := join (join h1 h2) h3
  rwa [show 1+(a+1)+3=a+5 by omega] at h

theorem x0_pairs (short : Bool) (k : Nat) (l r : Stream) :
    run short (6*k) (B0 (push false (alt k l)) r) =
      some (B0 (push false l) (rep true (2*k) r)) := by
  induction k generalizing r with
  | zero => simp only [rep_zero,alt_zero,Nat.mul_zero,run] <;> rfl
  | succ k ih =>
    have h1 := x0 short (push false (alt k l)) r
    have h2 := ih (rep true 2 r)
    have h := join h1 h2
    rw [rep_append,show 2*k+2=2*(k+1) by omega] at h
    rw [show 6+6*k=6*(k+1) by omega] at h
    simpa only [alt_succ] using h

theorem x1_run (short : Bool) (v : Nat) (l r : Stream) :
    run short (5*v) (B0 (alt 1 (rep true v l)) r) =
      some (B0 (alt 1 l) (rep true v r)) := by
  induction v generalizing r with
  | zero => simp only [rep_zero,alt_zero,Nat.mul_zero,run] <;> rfl
  | succ v ih =>
    have h1 := x_pos short 0 (rep true v l) r
    have h2 := ih (push true r)
    have h := join h1 h2
    simp only [Nat.zero_add,rep_one,rep_zero] at h
    rw [← rep_one true r,rep_append,show 5+5*v=5*(v+1) by omega] at h
    simpa only [alt_one,rep_succ] using h

#print axioms y_to_e
#print axioms e_pairs
#print axioms x_pos
#print axioms x1_run
end C9Pair
