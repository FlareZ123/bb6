import Raw10BoxBridge
import WeightedTNFQueueOrbit

namespace BB6.Agent49Raw10Orbit
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent49Box BB6.Agent49BoxBridge BB6.Agent13CrossRouteHeldLeaf109

def inversePerm (e : StatePerm) : StatePerm :=
  ⟨e.backward,e.forward,e.rightInverse,e.leftInverse⟩

/-- A cylinder on the renamed machine is a cylinder on the original machine. -/
def pullback (e : StatePerm) (p : PartialMachine) : PartialMachine :=
  fun s => (p (e.forward s.1,s.2)).map (Option.map (renameMove (inversePerm e)))

theorem compatible_pullback (e : StatePerm) (p : PartialMachine) (m : Machine)
    (h : compatible (pullback e p) m) :
    compatible p (renameTable e m) := by
  rintro ⟨q,b⟩ t ht
  have hs : pullback e p (e.backward q,b) =
      some (t.map (renameMove (inversePerm e))) := by
    simp [pullback,e.rightInverse,ht]
  have hm := h _ _ hs
  change (m (e.backward q,b)).map (renameMove e) = t
  rw [hm]
  cases t with
  | none => rfl
  | some mv =>
    cases mv
    simp [renameMove,inversePerm,e.rightInverse]

def perms : List StatePerm :=
  [swapStates 3 3, swapStates 3 4, swapStates 3 5, swapStates 4 5,
    composeStatePerm (swapStates 3 4) (swapStates 4 5),
    composeStatePerm (swapStates 4 5) (swapStates 3 4)]

theorem perms_fix_zero (e : StatePerm) (he : e ∈ perms) : e.forward 0 = 0 := by
  simp only [perms,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def orbitTables : List PartialMachine :=
  perms.flatMap fun e => sideTables.map (pullback e)

def orbitRemainder : List (Box Slot Transition) :=
  remainder firstOneB0_1LC orbitTables

theorem side_orbit_safe (B : Nat) (hB : 7014 ≤ B)
    (m : Machine) (hp : compatible firstOneB0_1LC m)
    (q : PartialMachine) (hq : q ∈ orbitTables) (hm : compatible q m) :
    WeightedBound B m := by
  obtain ⟨e,he,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hq
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hp'
  apply weighted_rename_back B e m (perms_fix_zero e he)
    (firstOne_terminal firstOneB0_1LC (by decide) m hp)
  have hb := b0_1lcSideWitnesses_safe w hw (renameTable e m)
    (compatible_pullback e _ m hm)
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) hB

/-- Parent-aware cover: all orbit certificates are sound on raw10, without
    requiring a separate proof that every transformed cylinder refines it. -/
theorem orbit_cover (B : Nat) (hB : 7014 ≤ B)
    (hOpen : ∀ r ∈ orbitRemainder, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC := by
  apply Cover.leaf
  intro m hp
  by_cases h : ∃ q ∈ orbitTables, compatible q m
  · obtain ⟨q,hq,hm⟩ := h
    exact side_orbit_safe B hB m hp q hq hm
  · have hn : ∀ q ∈ orbitTables, ¬ compatible q m := by
      intro q hq hm
      exact h ⟨q,hq,hm⟩
    obtain ⟨r,hr,hm⟩ := (remainder_exact firstOneB0_1LC orbitTables m).mpr ⟨hp,hn⟩
    exact hOpen r hr m hm

#print axioms compatible_pullback
#print axioms side_orbit_safe
#print axioms orbit_cover
end BB6.Agent49Raw10Orbit
