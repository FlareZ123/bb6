import Lean.Elab.Tactic.Omega
namespace BB6.Agent27ThreeStepStripArithmetic

def strip (u v n : Nat) : Prop :=
  let m := min u v
  let L := max u v
  let E := 35*n+93
  (L ≤ 13*m+E ∧ 13*m ≤ L+E) ∨
  (4*L ≤ 7*m+E ∧ 7*m ≤ 4*L+E)

theorem scale_growth (n : Nat) (hn : 10 ≤ n) : 100*n+500 ≤ 3^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 3^(10+(k+1)) = 3 * 3^(10+k) := by
        rw [← Nat.add_assoc, Nat.pow_succ]
        omega
      omega

theorem scale_growth9 (n : Nat) (hn : 9 ≤ n) : 100*n+403 ≤ 3^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 3^(9+(k+1)) = 3 * 3^(9+k) := by
        rw [← Nat.add_assoc, Nat.pow_succ]
        omega
      omega

theorem band_growth (n m : Nat) (hn : 10 ≤ n)
    (hm : 3^(n-1)-3 ≤ m) : 100*n+300 ≤ m := by
  have h := scale_growth9 (n-1) (by omega)
  omega

theorem terminal_scale (n m x y : Nat) (hn : 10 ≤ n)
    (hm : m+3 < 3^n) (hy : y ≤ 3*m+6*n+9)
    (hx : x ≤ 16*y+68) :
    y+3 < 3^(n+2) ∧ 2*(x+y+x+y+10+3*(n+2))+5 < 3^(n+5) := by
  have h := scale_growth n hn
  have h2 : 3^(n+2) = 9*3^n := by rw [Nat.pow_add]; omega
  have h5 : 3^(n+5) = 243*3^n := by rw [Nat.pow_add]; omega
  omega

/-- The far-oriented previous branch needs no ordering transfer. -/
theorem far_cancel (n u v x y : Nat) (huv : v ≤ u)
    (hleft : -(26*n+46 : Int) ≤ (x:Int)-4*(y:Int)-5-((u:Int)-13*(v:Int)) ∧
      (x:Int)-4*(y:Int)-5-((u:Int)-13*(v:Int)) ≤ (26*n+46 : Int))
    (hright : -(26*n+46 : Int) ≤ (y:Int)-4*(x:Int)-1-(7*(v:Int)-4*(u:Int)) ∧
      (y:Int)-4*(x:Int)-1-(7*(v:Int)-4*(u:Int)) ≤ (26*n+46 : Int))
    (hterm : (4*y ≤ x+9*n+38 ∧ x ≤ 4*y+9*n+38) ∨
      (4*x ≤ y+9*n+38 ∧ y ≤ 4*x+9*n+38)) : strip u v n := by
  unfold strip
  simp only [Nat.min_eq_right huv,Nat.max_eq_left huv]
  rcases hterm with h | h
  · left; omega
  · right; omega

/-- The near branch can cross the diagonal by up to four. The scale lower
bound forces the intended ordering once either cancellation occurs. -/
theorem near_cancel (n u v x y : Nat) (hn : 10 ≤ n)
    (hm : 3^(n-1)-3 ≤ min u v)
    (hleft : -(26*n+46 : Int) ≤ (x:Int)-4*(y:Int)-5-((v:Int)-13*(u:Int)) ∧
      (x:Int)-4*(y:Int)-5-((v:Int)-13*(u:Int)) ≤ (26*n+46 : Int))
    (hright : -(26*n+46 : Int) ≤ (y:Int)-4*(x:Int)-1-(7*(u:Int)-4*(v:Int)) ∧
      (y:Int)-4*(x:Int)-1-(7*(u:Int)-4*(v:Int)) ≤ (26*n+46 : Int))
    (hterm : (4*y ≤ x+9*n+38 ∧ x ≤ 4*y+9*n+38) ∨
      (4*x ≤ y+9*n+38 ∧ y ≤ 4*x+9*n+38)) : strip u v n := by
  have hg := band_growth n (min u v) hn hm
  have huv : u ≤ v := by
    by_cases h : u ≤ v
    · exact h
    · have h' : v ≤ u := by omega
      rw [Nat.min_eq_right h'] at hg
      rcases hterm with h | h <;> omega
  unfold strip
  simp only [Nat.min_eq_left huv,Nat.max_eq_right huv]
  rcases hterm with h | h
  · left; omega
  · right; omega

#print axioms terminal_scale
#print axioms far_cancel
#print axioms near_cancel
theorem pow3_gt_self (k : Nat) : k < 3^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

theorem scale_exists_aux (k m : Nat) (h : m+3 < 3^k) :
    ∃ n, 1≤n ∧ 3^(n-1)≤m+3 ∧ m+3<3^n := by
  induction k with
  | zero => simp at h
  | succ k ih =>
      by_cases hp : m+3<3^k
      · exact ih hp
      · refine ⟨k+1,by omega,?_,h⟩
        simpa using (Nat.le_of_not_gt hp)

theorem scale_exists (m : Nat) (hm : 19680≤m) :
    ∃ n, 10≤n ∧ 3^(n-1)-3≤m ∧ m+3<3^n := by
  obtain ⟨n,hn,hl,hh⟩ := scale_exists_aux (m+3) m (pow3_gt_self (m+3))
  have hn10 : 10≤n := by
    by_cases h : 10≤n
    · exact h
    · have hp := Nat.pow_le_pow_right (by decide : 0<3) (by omega : n≤9)
      have he : 3^9=19683 := by decide
      omega
  exact ⟨n,hn10,by omega,hh⟩

/-- Any finite failure of an option iteration with two initial surviving steps
has a three-step terminal chain. -/
theorem terminal_chain {S : Type} (F : S → Option S) (run : Nat → Option S)
    (hstep : ∀ t, run (t+1) = (run t).bind F)
    (h0 : ∃ s, run 0 = some s) (h1 : ∃ s, run 1 = some s)
    (h2 : ∃ s, run 2 = some s)
    (k : Nat) (hk : run k = none) :
    ∃ t q p r, run t = some q ∧ F q = some p ∧ F p = some r ∧ F r = none := by
  induction k with
  | zero => obtain ⟨s,hs⟩ := h0; rw [hs] at hk; contradiction
  | succ k ih =>
      cases hr : run k with
      | none => exact ih hr
      | some r =>
          have hhalt : F r = none := by simpa [hstep,hr] using hk
          have hge : 2≤k := by
            by_cases h : 2≤k
            · exact h
            · have hk' : k=0 ∨ k=1 := by omega
              rcases hk' with rfl|rfl
              · obtain ⟨s,hs⟩ := h1; rw [hs] at hk; contradiction
              · obtain ⟨s,hs⟩ := h2; rw [hs] at hk; contradiction
          let t := k-2
          have he : t+2=k := by dsimp [t]; omega
          have hr2 : run (t+2)=some r := by rwa [he]
          cases hp : run (t+1) with
          | none =>
              have hbad := hstep (t+1)
              rw [hp] at hbad
              change run (t+1+1)=none at hbad
              rw [show t+1+1=t+2 by omega,hr2] at hbad
              contradiction
          | some p =>
              have hpr : F p=some r := by
                rw [show t+2=t+1+1 by omega,hstep,hp] at hr2
                exact hr2
              cases hq : run t with
              | none => rw [hstep,hq] at hp; contradiction
              | some q =>
                  have hqp : F q=some p := by rw [hstep,hq] at hp; exact hp
                  exact ⟨t,q,p,r,hq,hqp,hpr,hhalt⟩

#print axioms scale_exists
#print axioms terminal_chain

end BB6.Agent27ThreeStepStripArithmetic
