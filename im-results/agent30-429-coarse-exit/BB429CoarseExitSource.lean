import BB429Rank
import BB429CoarseExit

namespace BB429.CoarseExit

def Uc (p : State) : Int := 6*(p.1:Int)+18
def Vc (p : State) : Int := 6*(p.1:Int)+3*(p.2:Int)
def isSection (p : State) : Prop := p.1=0 ∨ p.1=11

theorem ordinary_odd (p q : State) (h : next p=some q) (hp : p.2%2=1) (hq : ¬isSection q) :
    q.2%2=0 ∧ ((Uc q=2*Uc p ∧ Vc q=Vc p+9) ∨
      (Uc q=2*Uc p-Vc p+27 ∧ Vc q=Vc p+33) ∨
      (Uc q=2*Uc p-Vc p+3 ∧ Vc q=Vc p+21)) := by
  obtain ⟨u,w⟩ := p
  obtain ⟨v,z⟩ := q
  simp only [next] at h
  simp only [isSection,Prod.fst] at hq
  simp only [Prod.snd] at hp ⊢
  repeat' split at h
  all_goals simp_all [Uc,Vc]
  all_goals omega

theorem ordinary_even (p q : State) (h : next p=some q) (hp : p.2%2=0) (hq : ¬isSection q) :
    q.2%2=1 ∧ Uc q=2*Uc p ∧ Vc q=Vc p+9 := by
  obtain ⟨u,w⟩ := p
  obtain ⟨v,z⟩ := q
  simp only [next] at h
  simp only [isSection,Prod.fst] at hq
  simp only [Prod.snd] at hp ⊢
  repeat' split at h
  all_goals simp_all [Uc,Vc]
  all_goals omega

theorem odd_block (p q t : State) (h : next p=some q) (g : next q=some t)
    (hp : p.2%2=1) (hq : ¬isSection q) (ht : ¬isSection t) :
    t.2%2=1 ∧ ∃ e : Bool, ∃ c δ : Int, 0≤c ∧ c≤54 ∧ 0≤δ ∧ δ≤42 ∧
      Uc t=4*Uc p-(if e then 2*Vc p else 0)+c ∧ Vc t=Vc p+δ := by
  obtain ⟨he,hh⟩ := ordinary_odd p q h hp hq
  obtain ⟨ho,hu,hv⟩ := ordinary_even q t g he ht
  refine ⟨ho,?_⟩
  rcases hh with hh|hh|hh
  · exact ⟨false,0,18,by decide,by decide,by decide,by decide,by simp; omega,by omega⟩
  · exact ⟨true,54,42,by decide,by decide,by decide,by decide,by simp; omega,by omega⟩
  · exact ⟨true,6,30,by decide,by decide,by decide,by decide,by simp; omega,by omega⟩

theorem next_odd_to_even (p q : State) (h : next p=some q) (hp : p.2%2=1) (hq : ¬isSection q) : q.2%2=0 :=
  (ordinary_odd p q h hp hq).1

def trace (p : State) (k : Nat) : State := (run k p).getD (0,0)
def good (p : State) (n : Nat) : Prop := ∀ k, k≤n → run k p=some (trace p k)

theorem good_zero (p : State) : good p 0 := by
  intro k hk
  have : k=0 := by omega
  subst k
  rfl

theorem good_next (p : State) (n : Nat) (hg : good p n) (hn : next (trace p n)≠none) : good p (n+1) := by
  intro k hk
  by_cases h : k≤n
  · exact hg k h
  · have he : k=n+1 := by omega
    subst k
    cases hstep : next (trace p n) with
    | none => exact False.elim (hn hstep)
    | some q =>
      have hrun : run (n+1) p=some q := by simp [run,hg n (by omega),hstep]
      simp [trace,hrun]

theorem good_step (p : State) (n k : Nat) (hg : good p n) (hk : k+1≤n) : next (trace p k)=some (trace p (k+1)) := by
  have h := hg (k+1) hk
  simpa [run,hg k (by omega)] using h

def avoid (p : State) (N : Nat) : Prop := ∀ k, 0<k → k≤N → ¬isSection (trace p k)

theorem tracePrefix (p : State) (n N : Nat) (hodd : p.2%2=1) (hgood : good p (2*n))
    (hav : avoid p N) (hN : 2*n≤N) :
    (∀ i, i≤n → (trace p (2*i)).2%2=1) ∧
    ∃ e : Nat → Bool, Blocks (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e n := by
  have pair (i : Nat) (hi : i<n) (ho : (trace p (2*i)).2%2=1) :=
    odd_block (trace p (2*i)) (trace p (2*i+1)) (trace p (2*(i+1)))
      (good_step p (2*n) (2*i) hgood (by omega))
      (by have hh := good_step p (2*n) (2*i+1) hgood (by omega); simpa only [show 2*i+1+1=2*(i+1) by omega] using hh)
      ho (hav _ (by omega) (by omega)) (hav _ (by omega) (by omega))
  have odd (i : Nat) (hi : i≤n) : (trace p (2*i)).2%2=1 := by
    induction i with
    | zero => simpa [trace,run] using hodd
    | succ i ih => exact (pair i (by omega) (ih (by omega))).1
  refine ⟨odd,?_⟩
  classical
  let e (i : Nat) : Bool := if hi : i<n then Classical.choose (pair i hi (odd i (by omega))).2 else false
  refine ⟨e,?_⟩
  intro i hi
  simpa [e,hi] using Classical.choose_spec (pair i hi (odd i (by omega))).2

theorem halt_equation (p : State) : next p=none → 2*Uc p=Vc p+39 := by
  obtain ⟨u,w⟩ := p
  intro h
  have hh := (next_none_iff_halt_line u w).1 h
  simp [Uc,Vc]
  omega

theorem return_from_separated (p : State) (s : Nat) (d P x y : Int)
    (hodd : p.2%2=1) (hd0 : d%27≠0) (hd18 : d%27≠18) (hx : 0≤x) (hy : 0≤y)
    (hU : Uc p=lowA s d*P+x) (hV : Vc p=lowR s*P+y)
    (hsep : 3*cap (budget x y (lowL s)) (lowL s)+39<P) :
    ∃ k t, 0<k ∧ k≤2*lowL s ∧ run k p=some t ∧ isSection t := by
  classical
  by_cases hex : ∃ k t, 0<k ∧ k≤2*lowL s ∧ run k p=some t ∧ isSection t
  · exact hex
  · exfalso
    have avoidGood (N : Nat) (hN : N≤2*lowL s) (hg : good p N) : avoid p N := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,by omega,hg k hkN,hs⟩
    have full (n : Nat) (hn : n≤lowL s) : good p (2*n) := by
      induction n with
      | zero => exact good_zero p
      | succ n ih =>
        have hg := ih (by omega)
        have ⟨ho,e,hb⟩ := tracePrefix p n (2*n) hodd hg (avoidGood _ (by omega) hg) (by omega)
        have hno := low_no_halt s d P x y n (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e hd18 hx hy (by omega)
          (by simpa [trace,run] using hU) (by simpa [trace,run] using hV) hb hsep
        have hnext : next (trace p (2*n))≠none := fun h => hno (halt_equation _ h)
        have hg1 := good_next p (2*n) hg hnext
        have hev := next_odd_to_even _ _ (good_step p (2*n+1) (2*n) hg1 (by omega)) (ho n (by omega)) (avoidGood _ (by omega) hg1 _ (by omega) (by omega))
        have hnext1 : next (trace p (2*n+1))≠none := by
          intro h
          have hh := halt_equation _ h
          simp only [Uc,Vc] at hh
          omega
        have hg2 := good_next p (2*n+1) hg1 hnext1
        simpa only [show 2*n+1+1=2*(n+1) by omega] using hg2
    have hg := full (lowL s) (by omega)
    have ⟨_,e,hb⟩ := tracePrefix p (lowL s) (2*lowL s) hodd hg (avoidGood _ (by omega) hg) (by omega)
    apply low_no_full s d P x y (fun i => Uc (trace p (2*i))) (fun i => Vc (trace p (2*i))) e hd0 hd18 hx hy
      (by simpa [trace,run] using hU) (by simpa [trace,run] using hV) hb _ hsep
    intro i hi
    simp [Uc,Vc]
    omega

#print axioms return_from_separated
end BB429.CoarseExit
