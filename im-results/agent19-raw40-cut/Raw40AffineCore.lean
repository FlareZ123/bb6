import Raw40NestedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.AffineCore
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent19Raw40.NestedCore

/-- A finite preparation converts the first three right-hand ones into five,
then the common C/D/A core sweeps the whole unary block. -/
def family (n : Nat) : Z0 := ⟨1,[true,true],ones (n+3)⟩
theorem growth (p : PartialMachine) (h : Core p)
    (prep : ∀ R, run0 p 36 ⟨1,[true,true],[true,true,true]++R⟩ =
      some ⟨2,[true,true],[true,true,true,true,true]++R⟩) (n : Nat) :
    run0 p (2*n+53) (family n) = some (family (n+5)) := by
  have h1 := prep (ones n)
  have h1' : run0 p 36 (family n) = some ⟨2,[true,true],ones (n+5)⟩ := by
    simpa only [family,ones,rep,List.singleton_append,List.cons_append,List.nil_append] using h1
  have h2 := rightSweep p h (n+5) [true] []
  simp only [List.append_nil] at h2
  have h3 : run0 p 2 ⟨2,true::(zeros (n+5)++[true]),[]⟩ =
      some ⟨3,zeros (n+8)++[true],[]⟩ := by
    simp [run0,step0,move0,h.c1,h.c0,zeros,rep]
  have h4 := finish p h (n+8)
  have H := join0 (join0 (join0 h1' h2) h3) h4
  simpa only [family,show 36+(n+5)+2+(n+8+2)=2*n+53 by omega,
    show n+8=n+5+3 by omega] using H

theorem never (p : PartialMachine) (h : Core p)
    (prep : ∀ R, run0 p 36 ⟨1,[true,true],[true,true,true]++R⟩ =
      some ⟨2,[true,true],[true,true,true,true,true]++R⟩)
    (entry initial : Nat) (first : run0 p entry ⟨0,[],[]⟩ = some (family initial))
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => family (initial+5*k)) entry
    (fun k => 2*(initial+5*k)+53) _ _ _ m hm
  · simpa using first
  · intro k; omega
  · intro k
    simpa only [show initial+5*(k+1)=initial+5*k+5 by omega] using growth p h prep (initial+5*k)
#print axioms growth
#print axioms never
end BB6.Agent19Raw40.AffineCore
