import LagComplementCert
namespace BB6.Agent43LagJump
open BB6.Agent45.DelayedCarry
open BB6.Agent43LagPartition (targetFast)
open BB6.Agent43LagComplement (weight trace_strict fixedWalk)
open BB6.Agent43ReverseSet (Walk BackCover Bits Listed)

def full (bound : Nat) : Nat := 2^bound-1

theorem full_bit (bound c : Nat) (hc : c<bound) : Bits (full bound) c := by
  simp [Bits,full,Nat.testBit_two_pow_sub_one,hc]

/-- One jump from the known initial word, using only reverse covers of
complete carry intervals. No initial forward-lookahead enumeration. -/
theorem jump_empty (n s : Nat) (candidates : List Nat)
    (hs : 1≤s) (hsn : s≤n+1)
    (hcand : BackCover (weight n) (targetFast n 1) s (n+1-s)
      (Listed candidates) (Bits (full (2*n+3))))
    (hfinish : ∀ a∈candidates, (recover n 1 1 (s-1) a).2=(n+2)/2 →
      ∃ bad : List Nat,
        BackCover (weight n) (targetFast n (recover n 1 1 (s-1) a).1) s n
          (Listed bad) (Bits (full (2*n+s+2))) ∧ a∉bad) :
    Covered n s [] := by
  intro B a C c htr he
  obtain ⟨D,d,hD,hpre⟩ := trace_split n s B a 1 htr (by decide) hs
  obtain ⟨F,f,hshort,htail⟩ := extend_split n s B a n C c (n+1-s) he (by omega)
  have hidx : 1+(s-1)=s := by omega
  have hshort' : Extend n (1+(s-1)) B a (n+1-s) F f := by simpa only [hidx] using hshort
  have hE := extend_append n 1 D d (s-1) B a (n+1-s) F f hpre hshort'
  have hE' : Extend n 1 D d n F f := by simpa only [show s-1+(n+1-s)=n by omega] using hE
  have hfirst := covered_first n D d F f hD hE'
  simp only [List.mem_singleton,Prod.mk.injEq] at hfirst
  rcases hfirst with ⟨rfl,rfl⟩
  have hw := fixedWalk n 1 1 ((n+2)/2) (s-1) B a (n+1-s) F f hD hpre hshort' (by omega)
  rw [hidx] at hw
  have hf := trace_strict n _ _ _ (extend_trace n s B a (n+1-s) F f htr hshort)
  have ha : a∈candidates := hcand a f hw (full_bit _ _ (by omega))
  have hr := recover_exact n 1 1 ((n+2)/2) (s-1) B a hD hpre (by omega)
  obtain ⟨bad,hbad,hnot⟩ := hfinish a ha (by simp [hr])
  simp only [hr] at hbad
  have hw2 := fixedWalk n s B a 0 B a n C c htr Extend.nil (by simpa using he) (by omega)
  have hc := trace_strict n _ _ _ (extend_trace n s B a n C c htr he)
  have hm := hbad a c (by simpa using hw2) (full_bit _ _ (by omega))
  exact False.elim (hnot hm)

theorem cert_jump (n K s : Nat) (candidates : List Nat)
    (hs : 1≤s) (hsn : s≤n+1)
    (hcand : BackCover (weight n) (targetFast n 1) s (n+1-s)
      (Listed candidates) (Bits (full (2*n+3))))
    (hfinish : ∀ a∈candidates, (recover n 1 1 (s-1) a).2=(n+2)/2 →
      ∃ bad : List Nat,
        BackCover (weight n) (targetFast n (recover n 1 1 (s-1) a).1) s n
          (Listed bad) (Bits (full (2*n+s+2))) ∧ a∉bad)
    (hgood : MarginOK n K 1 (s-1) [(1,(n+2)/2)]=true) :
    Cert n K s [] := by
  refine ⟨jump_empty n s candidates hs hsn hcand hfinish,?_⟩
  intro j hj hjs
  exact margin_block n K 1 (s-1) j _ (by decide) hj (by omega) (covered_first n) hgood

#print axioms jump_empty
#print axioms cert_jump
end BB6.Agent43LagJump
