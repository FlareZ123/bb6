import BB429InverseWordCore
import BB429NewResidue
import Lean.Elab.Tactic.Omega

namespace BB429InverseWord

/-- Classify every high-output original BB429.next predecessor by one of the
three complete source inverse shapes, with the correct target parity. -/
theorem source_step_legit (x y a b : Nat) (ha : 13 ≤ a)
    (hs : BB429.next (x,y)=some (a,b)) :
    ∃ m, Legit m a b x y := by
  by_cases hodd : a%2=1
  · rcases BB429NewResidue.odd_inverse x y a b ha hodd hs with
      ⟨h1,h2⟩ | ⟨h1,h2,h3⟩
    · exact ⟨.F, ⟨⟨h1,h2⟩,hodd⟩⟩
    · exact ⟨.S, ⟨⟨h1,h2⟩,hodd⟩⟩
  · have heven : a%2=0 := by omega
    obtain ⟨h1,h2,h3⟩ := BB429NewResidue.even_inverse x y a b (by omega) heven hs
    exact ⟨.E, ⟨⟨h1,h2⟩,heven⟩⟩

/-- High-output predecessors decrease a+3 by at most a factor of two. -/
theorem legit_first_shrink (m : Move) (a b x y : Nat)
    (ha:13≤a) (he:Legit m a b x y) : a+3 ≤ 2*(x+3) := by
  cases m <;> simp only [Legit,Edge] at he <;> omega

inductive HighChain : Nat → Nat → List Move → Nat → Nat → Prop
  | nil (a b : Nat) : HighChain a b [] a b
  | cons {a b x y u v ws} (m : Move) :
      Legit m a b x y →
      HighChain x y ws u v →
      HighChain a b (m::ws) u v

/-- Any genuinely blank-reachable high target admits an arbitrarily prescribed
finite-length predecessor prefix as long as the first counter is exponentially
large in the prescribed depth. This is an authentic-root statement. -/
theorem source_high_prefix (k a b : Nat)
    (hr:BB429NewResidue.Reach a b)
    (ha:16*2^k ≤ a+3) :
    ∃ ws x y, ws.length=k ∧ HighChain a b ws x y := by
  induction k generalizing a b with
  | zero =>
      exact ⟨[],a,b,by decide,HighChain.nil a b⟩
  | succ k ih =>
      have hpow : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
      have hkp : 0 < 2^k := Nat.two_pow_pos k
      have ha13 : 13≤a := by omega
      obtain ⟨x,y,hpred,hnext⟩ := BB429NewResidue.pred a b (by omega) hr
      obtain ⟨m,he⟩ := source_step_legit x y a b ha13 hnext
      have hcontract := legit_first_shrink m a b x y ha13 he
      have hx : 16*2^k ≤ x+3 := by omega
      obtain ⟨ws,u,v,hws,hchain⟩ := ih x y hpred hx
      exact ⟨m::ws,u,v,by simp [hws],HighChain.cons m he hchain⟩

#print axioms source_step_legit
#print axioms legit_first_shrink
#print axioms source_high_prefix

end BB429InverseWord
