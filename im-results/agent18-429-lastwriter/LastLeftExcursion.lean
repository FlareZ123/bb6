import LastLeftWrite
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

/-- A marked cell strictly to the right has a last left-writing departure,
with the head strictly to the left of that marked boundary at *every* later
successful time up to the observed configuration. -/
theorem right_marked_has_left_excursion (m : Machine) (n : Nat) (c : Config) (y : Int)
    (hr : run m n blank = some c) (hpos : c.head < y) (hone : c.tape y = true) :
    ∃ k d t, k < n ∧ run m k blank = some d ∧ d.head = y ∧
      m (readSlot d) = some t ∧ t.write = true ∧ t.right = false ∧
      (∀ j e, k < j → j ≤ n → run m j blank = some e → e.head < y) := by
  induction n generalizing c with
  | zero =>
      have hc : c = blank := by simpa [run] using hr.symm
      subst c
      simp [blank] at hone
  | succ n ih =>
      cases hp : run m n blank with
      | none => simp [run,hp] at hr
      | some d =>
          cases hm : m (readSlot d) with
          | none => simp [run,hp,rawStep,hm] at hr
          | some t =>
              have hc : c = applyMove d t := by
                simpa [run,hp,rawStep,hm] using hr.symm
              by_cases hy : d.head = y
              · have hw : t.write = true := by
                  rw [hc] at hone
                  simpa [applyMove,hy] using hone
                have hl : t.right = false := by
                  rw [hc] at hpos
                  cases hright : t.right with
                  | false => rfl
                  | true => simp [applyMove,hright] at hpos; omega
                refine ⟨n,d,t,Nat.lt_succ_self n,hp,hy,hm,hw,hl,?_⟩
                intro j e hj hle he
                have hjeq : j=n+1 := by omega
                subst j
                have hce : e=c := by
                  have heq : some e = some c := he.symm.trans hr
                  exact Option.some.inj heq
                simpa [hce] using hpos
              · have hdp : d.head < y := by
                  rw [hc] at hpos
                  cases hright : t.right <;> simp [applyMove,hright] at hpos <;> omega
                have hdmark : d.tape y = true := by
                  rw [hc] at hone
                  simpa [applyMove,Ne.symm hy] using hone
                obtain ⟨k,e,v,hk,he,hxy,ha,hw,hl,hall⟩ := ih d hp hdp hdmark
                refine ⟨k,e,v,Nat.lt_trans hk (Nat.lt_succ_self n),he,hxy,ha,hw,hl,?_⟩
                intro j f hj hle hjf
                by_cases hjn : j≤n
                · exact hall j f hj hjn hjf
                · have hjeq : j=n+1 := by omega
                  subst j
                  have hce : f=c := by
                    have heq : some f = some c := hjf.symm.trans hr
                    exact Option.some.inj heq
                  simpa [hce] using hpos

#print axioms right_marked_has_left_excursion
end BB6Coverage
