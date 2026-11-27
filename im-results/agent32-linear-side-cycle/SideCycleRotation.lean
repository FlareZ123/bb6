import SideCycle

set_option maxHeartbeats 0
namespace BB6Coverage.Agent32SideRotation
open BB6Coverage Agent50SideCycle

theorem side_trans' (r : Bool) (a b c : Int)
    (hab : side r a b) (hbc : side r b c) : side r a c := by
  cases r <;> simp [side] at * <;> omega

theorem side_total (r : Bool) (a b : Int) : side r a b ∨ side r b a := by
  cases r <;> simp [side] <;> omega

theorem side_refl' (r : Bool) (a : Int) : side r a a := by
  cases r <;> simp [side]

theorem run_prefix_exists (m : Machine) (c d : Config) (n k : Nat)
    (hr : run m n c = some d) (hk : k ≤ n) : ∃ e, run m k c = some e := by
  rw [show n = k+(n-k) by omega,run_append] at hr
  cases h : run m k c with
  | none => simp [h] at hr
  | some e => exact ⟨e,rfl⟩

/-- Every positive live segment has an attained oriented extremum among its
queried heads (the endpoint is deliberately excluded). -/
theorem extremal_prefix (m : Machine) (r : Bool) (c d : Config) (n : Nat)
    (hn : 0 < n) (hr : run m n c = some d) :
    ∃ j < n, ∃ e, run m j c = some e ∧
      ∀ k < n, ∀ f, run m k c = some f → side r e.head f.head := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    by_cases hn' : n = 0
    · subst n
      refine ⟨0,by omega,c,rfl,?_⟩
      intro k hk f hf
      have h0 : k=0 := by omega
      subst k
      have he : c=f := Option.some.inj hf
      subst f
      exact side_refl' r c.head
    · obtain ⟨a,ha⟩ := run_prefix_exists m c d (n+1) n hr (by omega)
      obtain ⟨j,hj,e,he,hmin⟩ := ih a (by omega) ha
      rcases side_total r e.head a.head with h | h
      · refine ⟨j,by omega,e,he,?_⟩
        intro k hk f hf
        by_cases hkn : k=n
        · subst k
          rw [ha] at hf
          have haf := Option.some.inj hf
          subst f
          exact h
        · exact hmin k (by omega) f hf
      · refine ⟨n,by omega,a,ha,?_⟩
        intro k hk f hf
        by_cases hkn : k=n
        · subst k
          rw [ha] at hf
          have haf := Option.some.inj hf
          subst f
          exact side_refl' r a.head
        · exact side_trans' r a.head e.head f.head h (hmin k (by omega) f hf)

/-- Any side-cycle can be rotated to a cycle whose retained half-line starts
at the head of its first configuration. This removes arbitrary boundary search.
The new entry is before the old endpoint and the period is unchanged. -/
theorem rotate_at_extremum (m : Machine) (r : Bool) (b δ : Int)
    (c d e : Config) (n j : Nat) (hj : j < n)
    (hδ : side r 0 δ)
    (hwin : ∀ k < n, ∀ f, run m k c = some f → side r b f.head)
    (hloop : run m n c = some d)
    (hrel : TailRel r b δ c d)
    (he : run m j c = some e)
    (hmin : ∀ k < n, ∀ f, run m k c = some f → side r e.head f.head) :
    ∃ f, run m n e = some f ∧ TailRel r e.head δ e f ∧
      ∀ k < n, ∀ g, run m k e = some g → side r e.head g.head := by
  obtain ⟨f,hf,hef⟩ := tailRel_run m r b δ c d hrel j
    (fun k hk => hwin k (by omega)) e he
  have htotal : run m (n+j) c = some f := by rw [run_append,hloop]; exact hf
  have hrot : run m n e = some f := by
    rw [Nat.add_comm n j,run_append,he] at htotal
    exact htotal
  have hbe := hwin j hj e he
  refine ⟨f,hrot,⟨hef.1,hef.2.1,fun x hx => hef.2.2 x
    (side_trans' r b e.head x hbe hx)⟩,?_⟩
  intro k hk g hg
  have hrun : run m (j+k) c = some g := by rw [run_append,he]; exact hg
  by_cases hlt : j+k < n
  · exact hmin (j+k) hlt g hrun
  · let t := j+k-n
    have ht : t<n := by dsimp [t]; omega
    have hde : run m t d = some g := by
      rw [show j+k=n+t by dsimp [t]; omega,run_append,hloop] at hrun
      exact hrun
    obtain ⟨a,ha⟩ := run_prefix_exists m c d n t hloop (by omega)
    obtain ⟨g',hg',hag⟩ := tailRel_run m r b δ c d hrel t
      (fun l hl => hwin l (by omega)) a ha
    rw [hde] at hg'
    have hgg : g=g' := Option.some.inj hg'
    subst g'
    rw [hag.2.1]
    exact side_add r e.head a.head δ (hmin t ht a ha) hδ

theorem rotate_sideCycle (m : Machine) (r : Bool) (b δ : Int)
    (c d : Config) (n : Nat) (hn : 0<n)
    (hδ : side r 0 δ)
    (hwin : ∀ k < n, ∀ f, run m k c = some f → side r b f.head)
    (hloop : run m n c = some d)
    (hrel : TailRel r b δ c d) :
    ∃ j < n, ∃ e f, run m j c = some e ∧ run m n e = some f ∧
      TailRel r e.head δ e f ∧
      ∀ k < n, ∀ g, run m k e = some g → side r e.head g.head := by
  obtain ⟨j,hj,e,he,hmin⟩ := extremal_prefix m r c d n hn hloop
  obtain ⟨f,hf,hrel',hwin'⟩ := rotate_at_extremum m r b δ c d e n j hj hδ hwin hloop hrel he hmin
  exact ⟨j,hj,e,f,he,hf,hrel',hwin'⟩

#print axioms rotate_sideCycle
end BB6Coverage.Agent32SideRotation
