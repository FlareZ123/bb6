import Lean.Elab.Tactic.Omega

/-!
A coefficient-free arithmetic certificate for the 2-adic inverse-word bound.
It is parametrized over the exact three high-output inverse equations of the
BB429 section map; original-machine acceptance additionally needs the source
inverse bridge and rooted high-prefix argument.
-/
namespace BB429InverseWord

inductive Move where
  | F | S | E
  deriving DecidableEq, Repr

def cost : Move → Nat
  | .F => 3
  | .S => 11
  | .E => 7

def Edge : Move → Nat → Nat → Nat → Nat → Prop
  | .F, a, b, x, y => a = 2*x+3 ∧ y = b+a
  | .S, a, b, x, y => 4*x+26 = 4*a+b ∧ 2*y=b+4
  | .E, a, b, x, y => 4*x+14 = 4*a+b ∧ 2*y=b

theorem edge_cost (m : Move) (a b x y : Nat) (h : Edge m a b x y) :
    2*x+y+cost m=2*a+b := by
  cases m <;> simp only [Edge, cost] at h ⊢ <;> omega

theorem edge_even_b (m : Move) (a b x y : Nat) (h : Edge m a b x y)
    (hm : m ≠ .F) : b % 2 = 0 := by
  cases m <;> simp only [Edge] at h <;> try contradiction
  all_goals rcases h with ⟨h1,h2⟩; omega

theorem edge_even_b4 (m : Move) (a b x y : Nat) (h : Edge m a b x y)
    (hm : m ≠ .F) : b % 4 = 2 := by
  cases m <;> simp only [Edge] at h <;> try contradiction
  all_goals rcases h with ⟨h1,h2⟩; omega

-- Source inverse branch selection additionally enforces parity of the target.
def Legit (m : Move) (a b x y : Nat) : Prop :=
  Edge m a b x y ∧
  match m with
  | .F => a%2=1
  | .S => a%2=1
  | .E => a%2=0

theorem legit_cost (m : Move) (a b x y : Nat) (h : Legit m a b x y) :
    2*x+y+cost m=2*a+b := edge_cost m a b x y h.1

theorem legit_rank_odd_forces_F (m : Move) (a b x y : Nat)
    (h : Legit m a b x y) (hR : (2*a+b)%2=1) : m=.F := by
  cases m with
  | F => rfl
  | S =>
      have hb:=edge_even_b .S a b x y h.1 (by decide)
      omega
  | E =>
      have hb:=edge_even_b .E a b x y h.1 (by decide)
      omega

theorem legit_rank0_notE (m : Move) (a b x y : Nat)
    (h : Legit m a b x y) (hR : (2*a+b)%4=0) : m≠.E := by
  intro he
  subst he
  have hb:=edge_even_b4 .E a b x y h.1 (by decide)
  have ha:=h.2
  simp only at ha
  omega

theorem legit_rank2_notS (m : Move) (a b x y : Nat)
    (h : Legit m a b x y) (hR : (2*a+b)%4=2) : m≠.S := by
  intro he
  subst he
  have hb:=edge_even_b4 .S a b x y h.1 (by decide)
  have ha:=h.2
  simp only at ha
  omega

theorem pair_rank_balance (C a b a' b' x x' r s : Nat)
    (hR: 2*a+b+4*s = 2*a'+b'+4*r)
    (hx:4*x+C=4*a+b)
    (hy:4*x'+C=4*a'+b') :
    2*x+a'+2*s = 2*x'+a+2*r := by
  omega

theorem pair_F (j m a a' x x' r s : Nat)
    (ha:a=2*x+3) (hb:a'=2*x'+3)
    (h: 2^j*a + m*s = 2^j*a' + m*r):
    2^(j+1)*x + m*s = 2^(j+1)*x' + m*r := by
  rw [ha, hb] at h
  simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc] at *
  omega

theorem pair_nonF (j m a b a' b' x x' r s C : Nat)
    (hR: 2*a+b+4*s = 2*a'+b'+4*r)
    (hx:4*x+C=4*a+b)
    (hy:4*x'+C=4*a'+b')
    (h: 2^j*a + m*s = 2^j*a' + m*r):
    2^(j+1)*x + (m+2^(j+1))*s = 2^(j+1)*x' + (m+2^(j+1))*r := by
  have hb := pair_rank_balance C a b a' b' x x' r s hR hx hy
  have hscaled := congrArg (fun z : Nat => 2^j * z) hb
  simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_mul] at *
  omega

inductive Twin (a b a' b' : Nat) : List Move → Nat → Nat → Nat → Nat → Prop
  | nil : Twin a b a' b' [] a b a' b'
  | snoc {ws x y x' y' u v u' v'} (m: Move) :
      Twin a b a' b' ws x y x' y' →
      Legit m x y u v →
      Legit m x' y' u' v' →
      Twin a b a' b' (ws ++ [m]) u v u' v'

theorem twin_invariant (c a b a' b' : Nat)
    (hb : b+c=2*a) (hb' : b'+c=2*a')
    {ws : List Move} {x y x' y' : Nat}
    (h : Twin a b a' b' ws x y x' y') :
    ∃ M : Nat,
      M%2=1 ∧
      2^(ws.length)*x + M*a' = 2^(ws.length)*x' + M*a ∧
      2*x+y+4*a' = 2*x'+y'+4*a := by
  induction h with
  | nil =>
      refine ⟨1, by decide, ?_, ?_⟩
      · simp [Nat.add_comm]
      · omega
  | @snoc ws x y x' y' u v u' v' m hp he he' ih =>
      obtain ⟨M, hodd, hfirst, hbal⟩ := ih
      have hnewR : 2*u+v+4*a' = 2*u'+v'+4*a := by
        have hc := legit_cost m x y u v he
        have hc' := legit_cost m x' y' u' v' he'
        omega
      have hlen : (ws ++ [m]).length = ws.length+1 := by simp
      cases m with
      | F =>
          refine ⟨M, hodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_F ws.length M x x' u u' a a' he.1.1 he'.1.1 hfirst
      | S =>
          let P := 2^(ws.length+1)
          have hP : P%2=0 := by
            dsimp [P]
            rw [Nat.pow_succ]
            omega
          have hmodd : (M+P)%2=1 := by omega
          refine ⟨M+P, hmodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_nonF ws.length M x y x' y' u u' a a' 26
            hbal he.1.1 he'.1.1 hfirst
      | E =>
          let P := 2^(ws.length+1)
          have hP : P%2=0 := by
            dsimp [P]
            rw [Nat.pow_succ]
            omega
          have hmodd : (M+P)%2=1 := by omega
          refine ⟨M+P, hmodd, ?_, hnewR⟩
          rw [hlen]
          exact pair_nonF ws.length M x y x' y' u u' a a' 14
            hbal he.1.1 he'.1.1 hfirst

theorem odd_coprime_two (A : Nat) (hA:A%2=1) : Nat.Coprime 2 A := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  rw [Nat.gcd_rec, hA]
  decide

theorem paired_linear_congruence (k A a a' x x' : Nat)
    (hodd : A%2=1) (ha : a'≤a)
    (heq : 2^k*x + A*a' = 2^k*x' + A*a) :
    2^k ∣ (a-a') := by
  have hAprod : A*a' ≤ A*a := Nat.mul_le_mul_left A ha
  have horder : 2^k*x' ≤ 2^k*x := by omega
  have hmul : 2^k ∣ A*(a-a') := by
    have hs : (2^k*x)-(2^k*x') = A*a - A*a' := by omega
    have he : A*(a-a') = 2^k*(x-x') := by
      calc
        A*(a-a') = A*a - A*a' := Nat.mul_sub_left_distrib _ _ _
        _ = 2^k*x-2^k*x' := hs.symm
        _ = 2^k*(x-x') := (Nat.mul_sub_left_distrib _ _ _).symm
    exact ⟨x-x', he⟩
  have hc : Nat.Coprime (2^k) A := (odd_coprime_two A hodd).pow_left k
  exact hc.dvd_of_dvd_mul_left hmul

/-- Two diagonal-ray targets with the same length-k legitimate inverse word
must be congruent modulo 2^k; quantified, not a finite depth check. -/
theorem twin_residue_unique (c a b a' b' : Nat)
    (hb:b+c=2*a) (hb':b'+c=2*a')
    (haa' : a'≤a)
    {ws : List Move} {x y x' y' : Nat}
    (h : Twin a b a' b' ws x y x' y') :
    2^(ws.length) ∣ a-a' := by
  obtain ⟨M,hodd,hfirst,_⟩ := twin_invariant c a b a' b' hb hb' h
  exact paired_linear_congruence ws.length M a a' x x' hodd haa' hfirst

/-- Rank phase on the b+13=2a ray, independently of the branch word. -/
theorem twin_rank_phase (a b a' b' : Nat)
    (hb:b+13=2*a)
    {ws : List Move} {x y x' y' : Nat}
    (h:Twin a b a' b' ws x y x' y') :
    (2*x+y)%4 = (3+ws.length)%4 := by
  induction h with
  | nil =>
      change (2*a+b)%4=3
      omega
  | @snoc ws x y x' y' u v u' v' m hp he he' ih =>
      have hc := legit_cost m x y u v he
      have hw : (ws++[m]).length=ws.length+1 := by simp
      rw [hw]
      cases m <;> simp only [cost] at hc <;> omega

/-- At even inverse depths F is forced; odd depths admit at most two letters. -/
theorem next_letter_restriction (a b a' b' : Nat)
    (hb:b+13=2*a)
    {ws : List Move} {x y x' y' u v : Nat}
    (h:Twin a b a' b' ws x y x' y')
    (m : Move) (he:Legit m x y u v) :
    (ws.length%2=0 → m=.F) ∧
    (ws.length%4=1 → m≠.E) ∧
    (ws.length%4=3 → m≠.S) := by
  have hp := twin_rank_phase a b a' b' hb h
  constructor
  · intro hj
    have hR : (2*x+y)%2=1 := by omega
    exact legit_rank_odd_forces_F m x y u v he hR
  constructor
  · intro hj
    have hR : (2*x+y)%4=0 := by omega
    exact legit_rank0_notE m x y u v he hR
  · intro hj
    have hR : (2*x+y)%4=2 := by omega
    exact legit_rank2_notS m x y u v he hR

#print axioms twin_residue_unique
#print axioms twin_rank_phase
#print axioms next_letter_restriction
#print axioms twin_invariant

end BB429InverseWord
