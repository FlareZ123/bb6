import BB429DyadicStarts
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 1000000
namespace BB429Five

def power (u n : Nat) : Nat := 4*(u+3)*2^n
def correction (u n : Nat) : Nat := 2*u+3*n+13
def syntheticW (u n : Nat) : Nat := power u n - correction u n

private theorem two_pow_ge (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

private theorem power_ge (u n : Nat) (hn : 1 ≤ n) :
    correction u n ≤ power u n := by
  have hp := two_pow_ge n
  have hpos : 1 ≤ 2^n := by omega
  have h1 : (4*u)*1 ≤ (4*u)*2^n := Nat.mul_le_mul_left (4*u) hpos
  have h2 : 12*(n+1) ≤ 12*2^n := Nat.mul_le_mul_left 12 hp
  have heq : power u n = (4*u)*2^n +12*2^n := by
    simp only [power]
    have hh : 4*(u+3)=4*u+12 := by omega
    rw [hh, Nat.add_mul]
  have h1a : 2*u ≤ 4*u*2^n := by omega
  rw [heq]
  unfold correction
  omega

private theorem W_eq (u n : Nat) (hn : 1 ≤ n) :
    syntheticW u n + correction u n = power u n := by
  unfold syntheticW
  have h:=power_ge u n hn
  omega

private theorem power_four (u n : Nat) :
    power u (n+4) = 16*power u n := by
  simp only [power, Nat.pow_add]
  rw [show (2 : Nat)^4 = 16 by decide]
  ac_rfl

private theorem W_four (u n : Nat) (hn : 1 ≤ n) :
    syntheticW u (n+4)+12 = syntheticW u n + 15*power u n := by
  have h1:=W_eq u n hn
  have h2:=W_eq u (n+4) (by omega)
  rw [power_four] at h2
  dsimp [correction] at h1 h2
  omega

private theorem W_four_mod5 (u n : Nat) (hn : 1 ≤ n) :
    syntheticW u (n+4)%5 = (syntheticW u n + 3)%5 := by
  have h:=W_four u n hn
  omega

private theorem W_progression (u n t : Nat) (hn : 1 ≤ n) :
    syntheticW u (n+4*t)%5 = (syntheticW u n+3*t)%5 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htime : n+4*(t+1) = (n+4*t)+4 := by omega
    rw [htime, W_four_mod5 u (n+4*t) (by omega)]
    omega

private theorem mod_five_cover (x r : Nat) (hr : r < 5) :
    ∃ t, t < 5 ∧ (x+3*t)%5 = r := by
  let t := (2*(r+5-x%5))%5
  have ht : t < 5 := Nat.mod_lt _ (by decide)
  refine ⟨t,ht,?_⟩
  dsimp [t]
  omega

private theorem W_ge (u n w : Nat) (hn : w+1 ≤ n) :
    w ≤ syntheticW u n := by
  have hp := two_pow_ge n
  have hpos : 1 ≤ 2^n := by omega
  have h1 : (4*u)*1 ≤ (4*u)*2^n := Nat.mul_le_mul_left (4*u) hpos
  have h2 : 12*(n+1) ≤ 12*2^n := Nat.mul_le_mul_left 12 hp
  have h3 := W_eq u n (by omega)
  have heq : power u n = (4*u)*2^n +12*2^n := by
    simp only [power]
    have hh : 4*(u+3)=4*u+12 := by omega
    rw [hh, Nat.add_mul]
  rw [heq] at h3
  unfold correction at h3
  omega

theorem all_five (u n w : Nat) (hn : 1 ≤ n) :
    ∃ t, t < 5 ∧ syntheticW u (n+4*t)%5 = w%5 := by
  obtain ⟨t,ht,hh⟩ :=
    mod_five_cover (syntheticW u n) (w%5) (Nat.mod_lt _ (by decide))
  refine ⟨t,ht,?_⟩
  rw [W_progression u n t hn]
  exact hh

/-- All first-counter residues and all second-counter residues mod five
    contain a *synthetic*, eventually halting accelerated input. -/
theorem synthetic_halt_mod5 (u w : Nat) :
    ∃ W0 n a b,
      W0 % 5 = w % 5 ∧ w ≤ W0 ∧
      BB429.run n (u,W0) = some (a,b) ∧ BB429.next (a,b) = none := by
  obtain ⟨t,ht,hres⟩ := all_five u (w+1) w (by omega)
  let n0 := w+1+4*t
  have hn : 1 ≤ n0 := by dsimp [n0]; omega
  have hw : w ≤ syntheticW u n0 :=
    W_ge u n0 w (by dsimp [n0]; omega)
  have he : 2*u+syntheticW u n0+3*n0+13 = 4*((u+3)*2^n0) := by
    have hi := W_eq u n0 hn
    unfold correction power at hi
    rw [←Nat.mul_assoc]
    omega
  obtain ⟨m,a,b,hr,hg⟩ :=
    (BB429Burst.burst_gateway_iff u (syntheticW u n0)).mpr ⟨n0,he⟩
  refine ⟨syntheticW u n0,m,a,b,?_,hw,
    BB429DyadicStarts.first_prefix_is_source _ _ _ hr,
    (BB429.next_none_iff_halt_line a b).mpr hg⟩
  exact hres

/-- An invariant of the complete #429 map determined only by both
    counter residues modulo five cannot be nonempty and halt-free. -/
theorem no_nonempty_mod5_haltfree_invariant
    (u w : Nat) (P : Nat × Nat → Prop)
    (hmod : ∀ x y, x.1%5=y.1%5 → x.2%5=y.2%5 → P x → P y)
    (hinit : P (u,w))
    (hstep : ∀ x y, P x → BB429.next x = some y → P y)
    (hhalt : ∀ x, P x → BB429.next x ≠ none) : False := by
  obtain ⟨W0,n,a,b,heq,_,hr,hn⟩ := synthetic_halt_mod5 u w
  have hseed : P (u,W0) := by
    apply hmod (u,w) (u,W0)
    · simp
    · exact heq.symm
    · exact hinit
  have hrun : ∀ (m : Nat) (s t : Nat × Nat), P s →
      BB429.run m s = some t → P t := by
    intro m
    induction m with
    | zero =>
        intro s t hs ht
        simp [BB429.run] at ht
        simpa [ht] using hs
    | succ m ih =>
        intro s t hs ht
        simp only [BB429.run] at ht
        cases hp : BB429.run m s with
        | none => simp [hp] at ht
        | some p =>
            simp only [hp, Option.bind_some] at ht
            exact hstep p t (ih s p hs hp) ht
  exact hhalt (a,b) (hrun n (u,W0) (a,b) hseed hr) hn

#print axioms synthetic_halt_mod5
#print axioms no_nonempty_mod5_haltfree_invariant
#print axioms all_five
end BB429Five
