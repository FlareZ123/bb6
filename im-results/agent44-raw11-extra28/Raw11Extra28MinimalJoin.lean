import Raw11Extra28AllChildren

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Original-source minimal complete-parent join: Boolean exact-table coverage
     is computed independently of opaque child proof arguments. Imports only
     the accepted AllChildren checker, hence no Q0 or Canonical deps.
     Twelve actual child safety proofs are explicit premises. -/
namespace BB6.Agent44Extra28MinimalJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PhaseFrontier

def p7 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,1⟩)
def p8 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,2⟩)
def p9 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,2⟩)
def p10 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,2⟩)
def p12 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,3⟩)
def p13 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,3⟩)
def p14 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,3⟩)
def p15 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,3⟩)
def p16 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,false,4⟩)
def p17 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨false,true,4⟩)
def p18 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,false,4⟩)
def p19 : PartialMachine := refine BB6.Agent44Extra28AllChildren.parent (3,true) (some ⟨true,true,4⟩)

def covered : List PartialMachine := [
  p7,
  p8,
  p9,
  p10,
  p12,
  p13,
  p14,
  p15,
  p16,
  p17,
  p18,
  p19
]

theorem all_remaining_covered :
    (BB6.Agent44Extra28AllChildren.remaining.all fun q => covered.any (sameTable q)) = true := by
  decide +kernel

structure Certificates where
  c7 : ∀ m, compatible p7 m → WeightedBound 72 m
  c8 : ∀ m, compatible p8 m → WeightedBound 42 m
  c9 : ∀ m, compatible p9 m → WeightedBound 84 m
  c10 : ∀ m, compatible p10 m → WeightedBound 101 m
  c12 : ∀ m, compatible p12 m → WeightedBound 64 m
  c13 : ∀ m, compatible p13 m → WeightedBound 79 m
  c14 : ∀ m, compatible p14 m → WeightedBound 96 m
  c15 : ∀ m, compatible p15 m → WeightedBound 119 m
  c16 : ∀ m, compatible p16 m → WeightedBound 81 m
  c17 : ∀ m, compatible p17 m → WeightedBound 150 m
  c18 : ∀ m, compatible p18 m → WeightedBound 141 m
  c19 : ∀ m, compatible p19 m → WeightedBound 158 m

private theorem each_covered (h : Certificates) :
    ∀ p ∈ covered, ∀ m, compatible p m → WeightedBound 158 m := by
  intro p hp m hm
  simp only [covered,List.mem_cons,List.mem_singleton] at hp
  rcases hp with h7 | h8 | h9 | h10 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  · subst p
    exact liftBound (by decide : 72 ≤ 158) (h.c7 m hm)
  · subst p
    exact liftBound (by decide : 42 ≤ 158) (h.c8 m hm)
  · subst p
    exact liftBound (by decide : 84 ≤ 158) (h.c9 m hm)
  · subst p
    exact liftBound (by decide : 101 ≤ 158) (h.c10 m hm)
  · subst p
    exact liftBound (by decide : 64 ≤ 158) (h.c12 m hm)
  · subst p
    exact liftBound (by decide : 79 ≤ 158) (h.c13 m hm)
  · subst p
    exact liftBound (by decide : 96 ≤ 158) (h.c14 m hm)
  · subst p
    exact liftBound (by decide : 119 ≤ 158) (h.c15 m hm)
  · subst p
    exact liftBound (by decide : 81 ≤ 158) (h.c16 m hm)
  · subst p
    exact liftBound (by decide : 150 ≤ 158) (h.c17 m hm)
  · subst p
    exact liftBound (by decide : 141 ≤ 158) (h.c18 m hm)
  · subst p
    exact liftBound (by decide : 158 ≤ 158) (h.c19 m hm)

theorem completeCover (h : Certificates) :
    Cover (WeightedBound 158) BB6.Agent44Extra28AllChildren.parent :=
  BB6.Agent44Extra28AllChildren.consume 158 (by decide) (by
    intro q hq m hm
    have hb : covered.any (sameTable q) = true :=
      List.all_eq_true.mp all_remaining_covered q hq
    obtain ⟨p,hp,he⟩ := List.any_eq_true.mp hb
    have heq : q = p := sameTable_sound he
    rw [heq] at hm
    exact each_covered h p hp m hm)

theorem completeCoverAt (B : Nat) (hB : 158 ≤ B) (h : Certificates) :
    Cover (WeightedBound B) BB6.Agent44Extra28AllChildren.parent :=
  .leaf _ (fun m hm => liftBound hB ((completeCover h).sound m hm))

#print axioms all_remaining_covered
#print axioms completeCover
end BB6.Agent44Extra28MinimalJoin
