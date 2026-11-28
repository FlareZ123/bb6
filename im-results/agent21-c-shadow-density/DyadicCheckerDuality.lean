import DyadicOpenRecurrence
import DyadicAllowedHigh
import DyadicResidueOpen
import DyadicBad
import DyadicValuation

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- Exact, all-bit inverse-word duality for the executable signed
    modular-cone checker. The general proof works for *any* fuel
    budget covering the precision, and both completed and pending
    inverse words are handled. No machine-specific reachability
    assumption is used. -/
theorem check_open_duality (b f : Nat) (s : Pair) (hf : b≤f) :
    check f b s=true ↔
      ¬OpenAt (signedS s.x s.y) (signedZ s.x s.y) b := by
  induction b using Nat.strongRecOn generalizing f s with
  | ind b ih =>
      by_cases hb2 : 2≤b
      · cases f with
        | zero => omega
        | succ f' =>
            have child_iff (c : Nat) (hc : c<b) (hfc : c≤f')
                (p : Pair) :
                check f' c (residue c p)=true ↔
                  ¬OpenAt (signedS p.x p.y) (signedZ p.x p.y) c := by
              have hi := ih c hc f' (residue c p) hfc
              constructor
              · intro h ho
                have hres := (signed_open_residue c p).mpr ho
                exact hi.mp h hres
              · intro h
                apply hi.mpr
                intro hres
                exact h ((signed_open_residue c p).mp hres)
            by_cases hbad : Bad s
            · have hn := bad_implies_not_open b s hb2 hbad
              constructor
              · intro _; exact hn
              · intro _; simpa [check,hb2,hbad]
            · let v : Nat := valuation b (q s)
              by_cases hv : ValValid b s v
              · have hbool :
                    check (f'+1) b s=true ↔
                    ((s.y%2=0 →
                      ¬OpenAt (signedS (direct s).x (direct s).y)
                        (signedZ (direct s).x (direct s).y) (b-1)) ∧
                      (∀ n : Nat, Allowed s v n →
                        ¬OpenAt (signedS (high s n).x (high s n).y)
                          (signedZ (high s n).x (high s n).y) (b-(n+2)))) := by
                  have hfirst :
                      check (f'+1) b s=true ↔
                      (if s.y%2=0 then
                        check f' (b-1) (residue (b-1) (direct s))
                        else true)=true ∧
                      (List.range (v+1)).all (fun n =>
                        if Allowed s v n then
                          decide (HighValid s n) &&
                            check f' (b-(n+2))
                              (residue (b-(n+2)) (high s n))
                        else true)=true := by
                    simp only [check,hb2,ite_true,hbad,ite_false,
                      show valuation b (q s)=v by rfl,hv,Bool.and_eq_true]
                  have hdirect :
                      (if s.y%2=0 then
                        check f' (b-1) (residue (b-1) (direct s))
                       else true)=true ↔
                      (s.y%2=0 →
                        ¬OpenAt (signedS (direct s).x (direct s).y)
                          (signedZ (direct s).x (direct s).y) (b-1)) := by
                    by_cases hy : s.y%2=0
                    · simp only [hy,ite_true,true_implies]
                      exact child_iff (b-1) (by omega) (by omega) (direct s)
                    · simp only [hy,ite_false]
                      constructor
                      · intro _ hyn
                        exact False.elim (hy hyn)
                      · intro _
                        rfl
                  have hhigh :
                      (List.range (v+1)).all (fun n =>
                        if Allowed s v n then
                          decide (HighValid s n) &&
                            check f' (b-(n+2))
                              (residue (b-(n+2)) (high s n))
                        else true)=true ↔
                        (∀ n : Nat, Allowed s v n →
                          ¬OpenAt (signedS (high s n).x (high s n).y)
                            (signedZ (high s n).x (high s n).y) (b-(n+2))) := by
                    constructor
                    · intro hall n ha
                      have hn : n∈List.range (v+1) :=
                        List.mem_range.mpr (by have hh := ha.1; omega)
                      have hh := List.all_eq_true.mp hall n hn
                      simp only [ha,ite_true,Bool.and_eq_true,
                        decide_eq_true_eq] at hh
                      exact (child_iff (b-(n+2))
                        (by have h1 := ha.1; have h2 := hv.1; omega)
                        (by have h1 := ha.1; have h2 := hv.1; omega)
                        (high s n)).mp hh.2
                    · intro hall
                      apply List.all_eq_true.mpr
                      intro n hn
                      by_cases ha : Allowed s v n
                      · simp only [ha,ite_true,Bool.and_eq_true,
                          decide_eq_true_eq]
                        exact ⟨allowed_high_valid b v n s hv ha,
                          (child_iff (b-(n+2))
                            (by have h1 := ha.1; have h2 := hv.1; omega)
                            (by have h1 := ha.1; have h2 := hv.1; omega)
                            (high s n)).mpr (hall n ha)⟩
                      · simp [ha]
                  constructor
                  · intro hc
                    obtain ⟨hd,hh⟩ := hfirst.mp hc
                    exact ⟨hdirect.mp hd,hhigh.mp hh⟩
                  · intro ⟨hd,hh⟩
                    exact hfirst.mpr ⟨hdirect.mpr hd,hhigh.mpr hh⟩
                constructor
                · intro hc ho
                  obtain ⟨hd,hh⟩ := hbool.mp hc
                  rcases (open_iff_children b v s hv).mp ho with
                    ⟨hy,hdirect⟩|⟨n,ha,hhigh⟩
                  · exact hd hy hdirect
                  · exact hh n ha hhigh
                · intro hno
                  apply hbool.mpr
                  constructor
                  · intro hy hchild
                    exact hno ((open_iff_children b v s hv).mpr
                      (Or.inl ⟨hy,hchild⟩))
                  · intro n ha hchild
                    exact hno ((open_iff_children b v s hv).mpr
                      (Or.inr ⟨n,ha,hchild⟩))
              · have hdiv : I b∣q s := by
                  by_contra hn
                  have hval := (valvalid_iff_not_divisible b s).mpr hn
                  exact hv (by simpa [v] using hval)
                have hQ : P b∣s.x+s.y+(s.x+s.y)%2 := by
                  have hp : P b=I b := by
                    simp [P,I,BB6.Agent42ModularCone.P]
                  rw [hp]
                  exact hdiv
                have hopen : OpenAt (signedS s.x s.y) (signedZ s.x s.y) b :=
                  signed_open_if_divisible s.x s.y b (by omega) hQ
                have hbad' : ¬Bad s := hbad
                have hv' : ¬ValValid b s (valuation b (q s)) := by
                  simpa [v] using hv
                have hcheck : check (f'+1) b s=false := by
                  simp [check,hb2,hbad',hv']
                constructor
                · intro hc
                  rw [hcheck] at hc
                  cases hc
                · intro hn
                  exact False.elim (hn hopen)
      · have hb : b=0 ∨ b=1 := by omega
        rcases hb with h0|h1
        · subst b
          have hc : check f 0 s=false := by
            cases f <;> simp [check]
          constructor
          · intro h
            rw [hc] at h
            cases h
          · intro hn
            exact False.elim (hn (open_zero _ _))
        · subst b
          have hc : check f 1 s=false := by
            cases f <;> simp [check]
          constructor
          · intro h
            rw [hc] at h
            cases h
          · intro hn
            exact False.elim (hn (signed_open_one s.x s.y))

/-- The source-certified executable checker is exactly the complement
    of the finite inverse-word feasibility language, at *every*
    precision and on *every* signed residue pair. -/
theorem excluded_open_duality (b : Nat) (s : Pair) :
    excluded b s=true ↔
      ¬OpenAt (signedS s.x s.y) (signedZ s.x s.y) b := by
  unfold excluded
  have h := check_open_duality b b (residue b s) (Nat.le_refl b)
  exact h.trans (not_congr (signed_open_residue b s))

#print axioms check_open_duality
#print axioms excluded_open_duality
end BB6.Agent21Duality
