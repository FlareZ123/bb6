import Lean.Elab.Tactic.Omega
import PacketPaths

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace BB6.Agent31PacketShift
open BB6.Agent31PacketPaths

def shift (s : State) (d : Nat) : State := ⟨s.a+d,s.q,s.p⟩

private theorem quad (k p c : Nat) :
    12*(k+p)*(k+p)+49*(k+p)+c =
      (12*k*k+49*k+c)+(24*k+49)*p+12*p*p := by
  have h : p*k=k*p := Nat.mul_comm p k
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc]
  omega

/-- The B/E packet edges are equivariant under unary +3r to +8r; exact
    primitive cost grows quadratically, independently of q,p and binary tail. -/
theorem edge_shift_all {s dst : State} {cost : Nat} (h : Edge s cost dst) :
    ∃ ℓ : Nat, ∀ r : Nat,
       Edge (shift s (3*r)) (cost+ℓ*r+12*r*r) (shift dst (8*r)) := by
  cases h with
  | b k q p =>
      refine ⟨24*k+49, ?_⟩
      intro r
      have hi : shift (⟨3*k+2,q+1,p⟩ : State) (3*r) =
          (⟨3*(k+r)+2,q+1,p⟩ : State) := by
        simp only [shift]
        congr 1 <;> omega
      have ho : shift (⟨8*k+10,q,p⟩ : State) (8*r) =
          (⟨8*(k+r)+10,q,p⟩ : State) := by
        simp only [shift]
        congr 1 <;> omega
      have ht : 12*(k+r)*(k+r)+49*(k+r)+40 =
          (12*k*k+49*k+40)+(24*k+49)*r+12*r*r := quad k r 40
      rw [hi,ho]
      change Edge (⟨3*(k+r)+2,q+1,p⟩ : State)
        ((12*k*k+49*k+40)+(24*k+49)*r+12*r*r)
        (⟨8*(k+r)+10,q,p⟩ : State)
      rw [←ht]
      exact Edge.b (k+r) q p
  | e k q p =>
      refine ⟨24*k+49, ?_⟩
      intro r
      have hi : shift (⟨3*k+4,q,p+3⟩ : State) (3*r) =
          (⟨3*(k+r)+4,q,p+3⟩ : State) := by
        simp only [shift]
        congr 1 <;> omega
      have ho : shift (⟨8*k+9,q+2,p⟩ : State) (8*r) =
          (⟨8*(k+r)+9,q+2,p⟩ : State) := by
        simp only [shift]
        congr 1 <;> omega
      have ht : 12*(k+r)*(k+r)+49*(k+r)+58+6*q =
          (12*k*k+49*k+58+6*q)+(24*k+49)*r+12*r*r := by
        have hx := quad k r (58+6*q)
        omega
      rw [hi,ho]
      change Edge (⟨3*(k+r)+4,q,p+3⟩ : State)
        ((12*k*k+49*k+58+6*q)+(24*k+49)*r+12*r*r)
        (⟨8*(k+r)+9,q+2,p⟩ : State)
      rw [←ht]
      exact Edge.e (k+r) q p

def quadratic : Nat → Nat
  | 0 => 0
  | n+1 => 12*3^n*3^n + 64*quadratic n

private theorem join (D E S U L Q p : Nat) :
    (D + S*(E*p) + 12*(E*p)*(E*p)) +
    (U + L*(8*p) + Q*(8*p)*(8*p)) =
    (D+U)+(E*S+8*L)*p+(12*E*E+64*Q)*p*p := by
  have h1 : S*(E*p)=(E*S)*p := by ac_rfl
  have h2 : 12*(E*p)*(E*p)=(12*E*E)*p*p := by ac_rfl
  have h3 : L*(8*p)=(8*L)*p := by ac_rfl
  have h4 : Q*(8*p)*(8*p)=(64*Q)*p*p := by
    calc
      Q*(8*p)*(8*p)=(8*8*Q)*p*p := by ac_rfl
      _=(64*Q)*p*p := by rfl
  rw [h1,h2,h3,h4]
  simp only [Nat.add_mul,Nat.mul_assoc]
  omega

/-- Every source-certified chain of n guarded packet B/E returns is
    equivariant under input +3^n*x and output +8^n*x, with a universal
    quadratic primitive-time coefficient independent of the path or tail. -/
theorem path_shift {s dst : State} {n cost : Nat}
    (h : Path s n cost dst) :
    ∃ linear : Nat, ∀ x : Nat, ∃ cost' : Nat,
      Path (shift s (3^n*x)) n cost' (shift dst (8^n*x)) ∧
      cost' = cost + linear*x + quadratic n*x*x := by
  induction h with
  | nil s =>
      refine ⟨0, ?_⟩
      intro x
      refine ⟨0, ?_, ?_⟩
      · simpa using (Path.nil (shift s x))
      · simp [quadratic]
  | cons h hs ih =>
      rename_i s0 mid dst0 D n0 c0
      obtain ⟨L, hL⟩ := ih
      obtain ⟨S, hS⟩ := edge_shift_all h
      refine ⟨3^n0*S+8*L, ?_⟩
      intro x
      obtain ⟨C, hchain, hcost⟩ := hL (8*x)
      let r := 3^n0*x
      have hmid : shift mid (8*r) = shift mid (3^n0*(8*x)) := by
        congr 1
        dsimp [r]
        ac_rfl
      have hsrc : 3^(n0+1)*x = 3*r := by
        dsimp [r]
        simp only [Nat.pow_succ]
        ac_rfl
      have hdst : 8^n0*(8*x) = 8^(n0+1)*x := by
        simp only [Nat.pow_succ]
        ac_rfl
      have hed := hS r
      rw [hmid] at hed
      have hnew :
          Path (shift s0 (3^(n0+1)*x)) (n0+1)
            ((D+S*r+12*r*r)+C) (shift dst0 (8^(n0+1)*x)) := by
        rw [hsrc, ←hdst]
        exact Path.cons hed hchain
      refine ⟨(D+S*r+12*r*r)+C, hnew, ?_⟩
      calc
        (D+S*r+12*r*r)+C =
          (D+S*r+12*r*r)+
            (c0+L*(8*x)+quadratic n0*(8*x)*(8*x)) := by rw [hcost]
        _ = (D+c0)+(3^n0*S+8*L)*x+
              (12*3^n0*3^n0+64*quadratic n0)*x*x := by
          dsimp [r]
          exact join D (3^n0) S c0 L (quadratic n0) x
        _ = (D+c0)+(3^n0*S+8*L)*x+quadratic (n0+1)*x*x := by rfl

private theorem three_square (n : Nat) : 3^n*3^n=9^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      3^(n+1)*3^(n+1) = (3^n*3^n)*(3*3) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = 9^(n+1) := by rw [ih]; simp only [Nat.pow_succ]

/-- Universal quadratic coefficient independent of the entire B/E path. -/
theorem quadratic_closed (n : Nat) :
    55*quadratic n+12*9^n=12*64^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hthree : 12*3^n*3^n=12*9^n := by
      calc
        12*3^n*3^n=12*(3^n*3^n) := by ac_rfl
        _=12*9^n := by rw [three_square]
    have hrec : quadratic (n+1)=12*9^n+64*quadratic n := by
      change 12*3^n*3^n+64*quadratic n=_
      rw [hthree]
    calc
      55*quadratic (n+1)+12*9^(n+1) =
          64*(55*quadratic n+12*9^n) := by
        rw [hrec]
        simp only [Nat.pow_succ]
        simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
        omega
      _ = 64*(12*64^n) := by rw [ih]
      _ = 12*64^(n+1) := by simp only [Nat.pow_succ]; ac_rfl

/-- The shifted packet path remains an EXACT source six-state execution,
    with unchanged arbitrary tail and an explicit quadratic elapsed time.
    Uses the original-source PacketPaths.path_sound theorem. -/
theorem source_path_shift {s dst : State} {n cost : Nat}
    (h : Path s n cost dst) (ys : List Bool) :
    ∃ linear : Nat, ∀ x : Nat, ∃ cost' : Nat,
      CryptidBoundary.run cost'
        (physical (shift s (3^n*x)) ys) =
        physical (shift dst (8^n*x)) ys ∧
      cost' = cost+linear*x+quadratic n*x*x := by
  obtain ⟨L,hL⟩ := path_shift h
  refine ⟨L, ?_⟩
  intro x
  obtain ⟨C,hshift,hcost⟩ := hL x
  exact ⟨C, BB6.Agent31PacketPaths.path_sound hshift ys, hcost⟩

#print axioms quadratic_closed
#print axioms source_path_shift
#print axioms edge_shift_all
#print axioms path_shift
end BB6.Agent31PacketShift
