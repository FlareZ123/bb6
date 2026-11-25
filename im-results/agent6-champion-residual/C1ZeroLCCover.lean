import F0SiblingCover
import C1Sweep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6C1ZeroLC
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt

theorem branch_cover (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hb : n+6 ≤ B) (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hu : p s = none) (hc : BB6.Agent48Parent.check p n s = true)
    (hchildren : ∀ mv, Cover (WeightedBound B) (refine p s (some mv))) :
    Cover (WeightedBound B) p := by
  apply Cover.branch p s hu
  intro t _
  cases t with
  | some mv => exact hchildren mv
  | none =>
    obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound p n s hc
    have h := first_hole_weighted_halt B p n c hf hr
      (by rw [hs]; exact hu) (BB6.Agent6F0.bound hb)
    rw [hs] at h
    exact .leaf _ h

theorem last_cover (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hb : n+6 ≤ B) (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hu : p s = none) (hc : BB6.Agent48Parent.check p n s = true)
    (ha : ∀ q : Fin 6, ∀ b : Bool, (q,b) ≠ s →
      ((p (q,b)).getD none).isSome = true) :
    Cover (WeightedBound B) p := by
  obtain ⟨c,hr,hs⟩ := BB6.Agent48Parent.check_sound p n s hc
  apply Cover.leaf
  apply last_hole_sound B p n c hf hr (by rw [hs]; exact hu) _ (BB6.Agent6F0.bound hb)
  intro t ht
  have hh := ha t.1 t.2 (by simpa [hs] using ht)
  cases hp : p t with
  | none => simp [hp] at hh
  | some v =>
    cases hv : v with
    | none => simp [hp,hv] at hh
    | some mv => exact ⟨mv,rfl⟩

theorem far_cover (B : Nat) (p : PartialMachine) (C : FAR.Data 1)
    (h : C.fastValid p = true) : Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m (C.sound p (C.fastValid_sound p h) m hm))

theorem far_reflect (B : Nat) (p : PartialMachine) (C : FAR.Data 1)
    (h : C.fastValid (FAR.reflectPartial p) = true) : Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m
    (FAR.reflectNever m (C.sound _ (C.fastValid_sound _ h) _ (FAR.reflectCompatible p m hm))))

theorem hard_cover (B : Nat) (p : PartialMachine)
    (h : ∀ q : Fin 6, ∀ b : Bool, p (q,b) = BB6.Agent6C1Sweep.hard (q,b)) :
    Cover (WeightedBound B) p := by
  have he : p = BB6.Agent6C1Sweep.hard := by
    funext s
    exact h s.1 s.2
  rw [he]
  exact BB6.Agent6C1Sweep.cover B

def p1 : PartialMachine := FAR.fromCodes [7,24,11,24,14,8,3,16,12,11,24,24]
def p2 : PartialMachine := refine p1 (0,true) (some ⟨true,false,0⟩)
def p3 : PartialMachine := refine p2 (1,true) (some ⟨false,false,5⟩)
def p4 : PartialMachine := refine p2 (1,true) (some ⟨false,true,5⟩)
def p5 : PartialMachine := refine p2 (1,true) (some ⟨true,false,5⟩)
def p6 : PartialMachine := refine p2 (1,true) (some ⟨true,true,5⟩)
def p7 : PartialMachine := refine p1 (0,true) (some ⟨false,false,1⟩)
def p8 : PartialMachine := refine p7 (1,true) (some ⟨false,false,5⟩)
def p9 : PartialMachine := refine p7 (1,true) (some ⟨false,true,5⟩)
def p10 : PartialMachine := refine p7 (1,true) (some ⟨true,false,5⟩)
def p11 : PartialMachine := refine p7 (1,true) (some ⟨true,true,5⟩)
def p12 : PartialMachine := refine p1 (0,true) (some ⟨true,false,1⟩)
def p13 : PartialMachine := refine p12 (1,true) (some ⟨false,false,5⟩)
def p14 : PartialMachine := refine p12 (1,true) (some ⟨false,true,5⟩)
def p15 : PartialMachine := refine p12 (1,true) (some ⟨true,false,5⟩)
def p16 : PartialMachine := refine p12 (1,true) (some ⟨true,true,5⟩)
def p17 : PartialMachine := refine p1 (0,true) (some ⟨false,false,5⟩)
def p18 : PartialMachine := refine p17 (5,true) (some ⟨true,false,0⟩)
def p19 : PartialMachine := refine p17 (5,true) (some ⟨true,false,4⟩)
def p20 : PartialMachine := refine p17 (5,true) (some ⟨false,false,5⟩)
def p21 : PartialMachine := refine p17 (5,true) (some ⟨false,true,5⟩)
def p22 : PartialMachine := refine p17 (5,true) (some ⟨true,false,5⟩)
def p23 : PartialMachine := refine p17 (5,true) (some ⟨true,true,5⟩)
def p24 : PartialMachine := refine p1 (0,true) (some ⟨false,true,5⟩)
def p25 : PartialMachine := refine p24 (5,false) (some ⟨true,false,0⟩)
def p26 : PartialMachine := refine p24 (5,false) (some ⟨false,true,2⟩)
def p27 : PartialMachine := refine p24 (5,false) (some ⟨true,false,3⟩)
def p28 : PartialMachine := refine p24 (5,false) (some ⟨false,false,5⟩)
def p29 : PartialMachine := refine p24 (5,false) (some ⟨false,true,5⟩)
def p30 : PartialMachine := refine p24 (5,false) (some ⟨true,false,5⟩)
def p31 : PartialMachine := refine p24 (5,false) (some ⟨true,true,5⟩)
def p32 : PartialMachine := refine p1 (0,true) (some ⟨true,false,5⟩)
def p33 : PartialMachine := refine p32 (5,true) (some ⟨false,true,0⟩)
def p34 : PartialMachine := refine p32 (5,true) (some ⟨true,false,0⟩)
def p35 : PartialMachine := refine p32 (5,true) (some ⟨false,true,1⟩)
def p36 : PartialMachine := refine p32 (5,true) (some ⟨true,true,1⟩)
def p37 : PartialMachine := refine p32 (5,true) (some ⟨false,false,3⟩)
def p38 : PartialMachine := refine p32 (5,true) (some ⟨true,false,4⟩)
def p39 : PartialMachine := refine p32 (5,true) (some ⟨false,false,5⟩)
def p40 : PartialMachine := refine p32 (5,true) (some ⟨false,true,5⟩)
def p41 : PartialMachine := refine p32 (5,true) (some ⟨true,false,5⟩)
def p42 : PartialMachine := refine p32 (5,true) (some ⟨true,true,5⟩)
def p43 : PartialMachine := refine p1 (0,true) (some ⟨true,true,5⟩)
def p44 : PartialMachine := refine p43 (5,false) (some ⟨true,false,0⟩)
def p45 : PartialMachine := refine p43 (5,false) (some ⟨false,false,1⟩)
def p46 : PartialMachine := refine p43 (5,false) (some ⟨true,false,1⟩)
def p47 : PartialMachine := refine p43 (5,false) (some ⟨false,true,2⟩)
def p48 : PartialMachine := refine p43 (5,false) (some ⟨false,false,5⟩)
def p49 : PartialMachine := refine p43 (5,false) (some ⟨false,true,5⟩)
def p50 : PartialMachine := refine p43 (5,false) (some ⟨true,false,5⟩)
def p51 : PartialMachine := refine p43 (5,false) (some ⟨true,true,5⟩)

theorem close3 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p3 := by
  apply branch_cover B p3 21 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 3 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 8 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 6 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 35 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 15 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close4 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p4 := by
  apply branch_cover B p4 21 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 23 false (1) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 39 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 35 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 57 9 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 27 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 43 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 41 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close5 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p5 := by
  apply branch_cover B p5 21 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 12 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 4 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 3 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact last_cover B _ 23 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 2 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 8 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 7 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 15 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close6 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p6 := by
  apply branch_cover B p6 21 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 27 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 23 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 31 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 35 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 33 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close2 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p2 := by
  apply branch_cover B p2 20 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 29 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact close3 B hB
  · exact close4 B hB
  · exact close5 B hB
  · exact close6 B hB

theorem close8 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p8 := by
  apply branch_cover B p8 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 26 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 26 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close9 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p9 := by
  apply branch_cover B p9 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 34 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 5 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 23 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-3) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-3) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close10 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p10 := by
  apply branch_cover B p10 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 13 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close11 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p11 := by
  apply branch_cover B p11 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 48 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close7 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p7 := by
  apply branch_cover B p7 18 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 12 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact close8 B hB
  · exact close9 B hB
  · exact close10 B hB
  · exact close11 B hB

theorem close13 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p13 := by
  apply branch_cover B p13 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 8 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact last_cover B _ 23 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close14 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p14 := by
  apply branch_cover B p14 19 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 5 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close15 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p15 := by
  apply branch_cover B p15 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 13 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 24 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close16 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p16 := by
  apply branch_cover B p16 19 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 48 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close12 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p12 := by
  apply branch_cover B p12 18 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 5 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 6 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 12 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact close13 B hB
  · exact close14 B hB
  · exact close15 B hB
  · exact close16 B hB

theorem close18 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p18 := by
  apply branch_cover B p18 20 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 35 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact last_cover B _ 26 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 39 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close19 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p19 := by
  apply branch_cover B p19 22 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 28 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 21 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 24 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 13 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 16 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 32 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 12 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 12 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 12 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close20 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p20 := by
  apply branch_cover B p20 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 34 1 true (-6) (by decide) (by decide)

theorem close21 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p21 := by
  apply branch_cover B p21 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 5 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)

theorem close22 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p22 := by
  apply branch_cover B p22 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 22 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 13 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)

theorem close23 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p23 := by
  apply branch_cover B p23 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 48 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 3 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)

theorem close17 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p17 := by
  apply branch_cover B p17 18 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 19 false (2) (by decide) (by decide)
  · exact close18 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact close19 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact close20 B hB
  · exact close21 B hB
  · exact close22 B hB
  · exact close23 B hB

theorem close25 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p25 := by
  apply branch_cover B p25 20 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 4 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 26 false (1) (by decide) (by decide)
  · exact last_cover B _ 22 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 22 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 11 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 30 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 50 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 30 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 23 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close26 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p26 := by
  apply branch_cover B p26 26 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 38 42 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 343 4 true (4) (by decide) (by decide)
  · exact last_cover B _ 28 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 96 4 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 42 false (2) (by decide) (by decide)
  · exact last_cover B _ 75 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (2) (by decide) (by decide)
  · exact last_cover B _ 71 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 30 40 false (0) (by decide) (by decide)
  · exact last_cover B _ 79 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 48 52 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 42 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 42 48 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 28 44 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (3) (by decide) (by decide)

theorem close27 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p27 := by
  apply branch_cover B p27 30 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 188 3 true (-14) (by decide) (by decide)
  · exact hard_cover B _ (by decide)
  · exact last_cover B _ 32 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 39 48 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 42 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 48 3 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 40 3 true (-6) (by decide) (by decide)
  · exact last_cover B _ 75 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 32 3 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 34 40 false (0) (by decide) (by decide)
  · exact last_cover B _ 83 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 378 3 true (-18) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 3 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 42 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 104 3 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 34 42 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 3 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 32 48 false (2) (by decide) (by decide)

theorem close28 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p28 := by
  apply branch_cover B p28 20 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 21 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 5 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-4) (by decide) (by decide)

theorem close29 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p29 := by
  apply branch_cover B p29 22 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 23 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 23 true (-4) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 50 1 true (6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 1 true (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 22 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (4) (by decide) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,32,1,34,32,64],[32,64,32,36,4,0,64],64⟩ : FAR.Data 1) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 36 1 true (0) (by decide) (by decide)
  · exact last_cover B _ 52 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 29 true (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 50 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 76 1 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 65 1 true (3) (by decide) (by decide)
  · exact last_cover B _ 26 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 66 true (-8) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 2 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)

theorem close30 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p30 := by
  apply branch_cover B p30 20 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 23 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 29 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 3 true (1) (by decide) (by decide)

theorem close31 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p31 := by
  apply branch_cover B p31 22 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 24 1 true (2) (by decide) (by decide)
  · exact last_cover B _ 315 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 26 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 95 76 false (3) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 67 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 71 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 40 1 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (4) (by decide) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,32,1,34,32,64],[32,64,32,36,4,0,64],64⟩ : FAR.Data 1) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,36,1,38,32,64],[32,64,36,36,4,4,64],64⟩ : FAR.Data 1) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 42 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 46 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 42 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 44 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 42 1 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 24 48 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 1 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)

theorem close24 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p24 := by
  apply branch_cover B p24 18 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 20 false (1) (by decide) (by decide)
  · exact close25 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 8 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 14 false (1) (by decide) (by decide)
  · exact close26 B hB
  · exact BB6.Agent6F0.side_cover B _ 5 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 46 24 false (0) (by decide) (by decide)
  · exact close27 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 62 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact close28 B hB
  · exact close29 B hB
  · exact close30 B hB
  · exact close31 B hB

theorem close33 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p33 := by
  apply branch_cover B p33 20 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-4) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 17 false (1) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 1 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 1 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)

theorem close34 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p34 := by
  apply branch_cover B p34 20 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 7 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)

theorem close35 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p35 := by
  apply branch_cover B p35 19 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 5 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 13 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close36 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p36 := by
  apply branch_cover B p36 19 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 48 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-4) (by decide) (by decide)
  · exact last_cover B _ 20 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close37 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p37 := by
  apply branch_cover B p37 21 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 27 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 31 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 23 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 12 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 23 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 31 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 19 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 35 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 33 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 11 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 29 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close38 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p38 := by
  apply branch_cover B p38 22 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 6 false (-3) (by decide) (by decide)
  · exact last_cover B _ 24 (5,false) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 6 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 14 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 21 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 22 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 13 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 10 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 22 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 20 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 24 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 12 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 12 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 22 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 12 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 14 false (1) (by decide) (by decide)

theorem close39 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p39 := by
  apply branch_cover B p39 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 8 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact last_cover B _ 27 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 27 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 41 1 true (-7) (by decide) (by decide)

theorem close40 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p40 := by
  apply branch_cover B p40 20 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 21 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 21 false (2) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 6 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 6 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 46 7 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 8 51 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 39 5 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 42 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 1 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 20 1 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)

theorem close41 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p41 := by
  apply branch_cover B p41 19 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-5) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 17 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 5 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact last_cover B _ 22 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 13 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 3 false (-4) (by decide) (by decide)

theorem close42 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p42 := by
  apply branch_cover B p42 20 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 4 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 26 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 38 5 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 22 false (1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 6 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 50 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 31 3 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)

theorem close32 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p32 := by
  apply branch_cover B p32 18 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 9 false (0) (by decide) (by decide)
  · exact close33 B hB
  · exact close34 B hB
  · exact BB6.Agent6F0.side_cover B _ 17 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 15 false (1) (by decide) (by decide)
  · exact close35 B hB
  · exact BB6.Agent6F0.side_cover B _ 13 7 false (-1) (by decide) (by decide)
  · exact close36 B hB
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 5 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 15 4 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 6 false (-1) (by decide) (by decide)
  · exact close37 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 25 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 16 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 7 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 15 false (1) (by decide) (by decide)
  · exact close38 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact close39 B hB
  · exact close40 B hB
  · exact close41 B hB
  · exact close42 B hB

theorem close44 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p44 := by
  apply branch_cover B p44 20 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 4 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 26 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 22 false (1) (by decide) (by decide)
  · exact last_cover B _ 21 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 6 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 50 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 10 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact last_cover B _ 25 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 25 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 30 3 true (2) (by decide) (by decide)

theorem close45 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p45 := by
  apply branch_cover B p45 19 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact last_cover B _ 38 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 20 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-3) (by decide) (by decide)

theorem close46 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p46 := by
  apply branch_cover B p46 19 (1,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 13 false (0) (by decide) (by decide)
  · exact last_cover B _ 30 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 21 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 30 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 17 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 11 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 9 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 8 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (5,true) (by omega) (by decide) (by decide) (by decide) (by decide)

theorem close47 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p47 := by
  apply branch_cover B p47 26 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 79 4 true (5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 2 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 81 4 true (5) (by decide) (by decide)
  · exact last_cover B _ 27 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 67 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 27 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 71 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 4 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (2) (by decide) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,36,1,38,4,64],[32,64,36,36,4,36,64],64⟩ : FAR.Data 1) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 151 4 true (-14) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 38 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 42 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 40 40 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 35 4 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 28 80 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 4 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 4 true (3) (by decide) (by decide)

theorem close48 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p48 := by
  apply branch_cover B p48 19 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 23 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 38 5 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 18 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 18 2 true (-3) (by decide) (by decide)

theorem close49 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p49 := by
  apply branch_cover B p49 22 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 0 23 true (-4) (by decide) (by decide)
  · exact last_cover B _ 24 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 50 1 true (6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 37 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 1 22 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (4) (by decide) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,32,1,34,32,64],[32,64,32,36,4,0,64],64⟩ : FAR.Data 1) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 36 1 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 40 false (4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 78 false (7) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 25 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 50 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 66 1 true (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 65 1 true (3) (by decide) (by decide)
  · exact last_cover B _ 26 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 56 true (-6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 2 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)

theorem close50 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p50 := by
  apply branch_cover B p50 19 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 12 13 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 84 3 true (4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 19 2 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 88 3 true (4) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 20 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 5 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 6 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 8 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 8 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 22 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 28 1 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 21 1 false (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 3 true (1) (by decide) (by decide)

theorem close51 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p51 := by
  apply branch_cover B p51 22 (5,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 24 1 true (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 70 1 true (6) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 22 2 true (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 74 1 true (6) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 59 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 23 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact last_cover B _ 63 (1,true) (by omega) (by decide) (by decide) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 32 1 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 26 1 true (4) (by decide) (by decide)
  · exact far_cover B _ (⟨0,[0,0],[2,4,32,1,34,32,64],[32,64,32,36,4,0,64],64⟩ : FAR.Data 1) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 126 1 true (-12) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 34 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 33 38 false (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 34 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 36 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 34 1 true (-4) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 264 1 true (-20) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 29 1 true (-5) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 27 3 false (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 23 1 true (3) (by decide) (by decide)

theorem close43 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p43 := by
  apply branch_cover B p43 18 (5,false) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 17 2 true (-3) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 24 false (1) (by decide) (by decide)
  · exact close44 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact close45 B hB
  · exact BB6.Agent6F0.side_cover B _ 3 20 false (1) (by decide) (by decide)
  · exact close46 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 6 false (-1) (by decide) (by decide)
  · exact close47 B hB
  · exact BB6.Agent6F0.side_cover B _ 13 6 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 16 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 46 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 18 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 30 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 12 8 false (0) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact close48 B hB
  · exact close49 B hB
  · exact close50 B hB
  · exact close51 B hB

theorem close1 (B : Nat) (hB : 321 ≤ B) : Cover (WeightedBound B) p1 := by
  apply branch_cover B p1 17 (0,true) (by omega) (by decide) (by decide) (by decide)
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have := q.isLt
    omega
  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
  · exact BB6.Agent6F0.side_cover B _ 0 19 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 32 false (2) (by decide) (by decide)
  · exact close2 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact close7 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact close12 B hB
  · exact BB6.Agent6F0.side_cover B _ 2 20 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 4 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 38 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 14 4 false (-2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 16 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 24 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 36 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 6 12 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 28 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 4 14 false (1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 2 26 false (2) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 13 6 false (-1) (by decide) (by decide)
  · exact BB6.Agent6F0.side_cover B _ 3 16 false (1) (by decide) (by decide)
  · exact close17 B hB
  · exact close24 B hB
  · exact close32 B hB
  · exact close43 B hB

 theorem cover_zeroLC (B : Nat) (hB : 321 ≤ B) :
    Cover (WeightedBound B) (FAR.fromCodes [7,24,11,24,14,8,3,16,12,11,24,24]) :=
  close1 B hB
#print axioms cover_zeroLC
end BB6.Agent6C1ZeroLC
