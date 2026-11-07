import BubblePrefix
import Lean.Elab.Tactic.Omega

namespace BB6BCFuture
open BB6Coverage BB6Bubble

def C : Fin 6 := ⟨2,by decide⟩

theorem bc_two (m : Machine) (c : Config)
    (hC : m (C,true)=some ⟨false,true,B⟩)
    (hB : m (B,false)=some ⟨true,true,C⟩)
    (hs : c.state=C) (h0 : c.tape c.head=true)
    (h1 : c.tape (c.head+1)=false) :
    ∃ d, run m 2 c=some d ∧ d.state=C ∧ d.head=c.head+2 ∧
      (∀ x : Int, c.head+2 ≤ x → d.tape x=c.tape x) := by
  let ca : Move := ⟨false,true,B⟩
  let ba : Move := ⟨true,true,C⟩
  let c1 := applyMove c ca
  let c2 := applyMove c1 ba
  have hcslot : readSlot c=(C,true) := by
    change (c.state,c.tape c.head)=(C,true)
    exact Prod.ext hs h0
  have hcraw : rawStep m c=some c1 := by
    simp [rawStep,hcslot,hC,c1,ca]
  have hdslot : readSlot c1=(B,false) := by
    change (c1.state,c1.tape c1.head)=(B,false)
    apply Prod.ext
    · rfl
    · change (if c.head+1 = c.head then false else c.tape (c.head+1)) = false
      have hn : c.head+1≠c.head := by omega
      simp [hn,h1]
  have hbraw : rawStep m c1=some c2 := by
    simp [rawStep,hdslot,hB,c2,ba]
  have hr : run m 2 c=some c2 := by
    change (rawStep m c).bind (rawStep m)=some c2
    rw [hcraw]
    simpa only [Option.bind_some] using hbraw
  refine ⟨c2,hr,?_,?_,?_⟩
  · rfl
  · change c.head+1+1=c.head+2
    omega
  · intro x hx
    have hca : x≠c.head := by omega
    have hba : x≠c.head+1 := by omega
    change (if x=c.head+1 then true else (if x=c.head then false else c.tape x))=c.tape x
    simp [hca,hba]

/-- Any length of the C/1, B/0 alternating right sweep preserves all future
    tape cells while moving the head 2k steps right. -/
theorem bc_future_sweep (m : Machine) (k : Nat) (c : Config) (t : Int → Bool)
    (hC : m (C,true)=some ⟨false,true,B⟩)
    (hB : m (B,false)=some ⟨true,true,C⟩)
    (hs : c.state=C)
    (hf : ∀ x : Int, c.head ≤ x → c.tape x=t x)
    (hpair : ∀ i : Nat, i<k →
      t (c.head+2*(i:Int))=true ∧ t (c.head+2*(i:Int)+1)=false) :
    ∃ d, run m (2*k) c=some d ∧ d.state=C ∧ d.head=c.head+2*(k:Int) ∧
      ∀ x : Int, c.head+2*(k:Int) ≤ x → d.tape x=t x := by
  induction k generalizing c with
  | zero =>
      refine ⟨c,by rfl,hs,by omega,?_⟩
      intro x hx
      exact hf x (by simpa using hx)
  | succ k ih =>
      have hzero : c.tape c.head=true := by
        rw [hf c.head (by omega)]
        simpa using (hpair 0 (by omega)).1
      have hone : c.tape (c.head+1)=false := by
        rw [hf (c.head+1) (by omega)]
        simpa using (hpair 0 (by omega)).2
      obtain ⟨d,h2,hsd,hd,hdf⟩ := bc_two m c hC hB hs hzero hone
      have hfuture : ∀ x, d.head ≤ x → d.tape x=t x := by
        intro x hx
        rw [hdf x (by omega)]
        apply hf x
        omega
      have hrest : ∀ i : Nat, i<k → t (d.head+2*(i:Int))=true ∧
           t (d.head+2*(i:Int)+1)=false := by
        intro i hi
        have hi' := hpair (i+1) (by omega)
        constructor
        · have hx : d.head+2*(i:Int) = c.head+2*((i+1:Nat):Int) := by
            rw [hd]
            omega
          rw [hx]
          exact hi'.1
        · have hx : d.head+2*(i:Int)+1 = c.head+2*((i+1:Nat):Int)+1 := by
            rw [hd]
            omega
          rw [hx]
          exact hi'.2
      obtain ⟨e,he,hse,hhe,hfe⟩ := ih d hsd hfuture hrest
      have hlen : 2*(k+1)=2+2*k := by omega
      have hrun : run m (2*(k+1)) c=some e := by
        rw [hlen,run_add',h2]
        simpa using he
      refine ⟨e,hrun,hse,?_,?_⟩
      · rw [hhe,hd]
        omega
      · intro x hx
        exact hfe x (by rw [hd]; omega)

#print axioms bc_two
#print axioms bc_future_sweep
end BB6BCFuture
