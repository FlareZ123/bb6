import R1Parent
import R4Counter

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace BB6.Agent47R4Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent47R1Parent BB6.Agent50TNFPilot
open BB6Coverage.Agent50Zipper BB6Coverage.Agent47R4Counter

theorem r4_never (a : Move)
    (hd : ∀ n, ∃ z, zrun (table a) n start = some z)
    (m : Machine) (hm : compatible (table a) m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := hd n
  have hr := zrun_sound (table a) m hm n start z hz
  have he : embed start = blank := BB6Coverage.Agent47R1Sweep.initial_embed
  rw [he] at hr
  change (run m n blank).isSome = true
  rw [hr]
  rfl

def counterWitness (a : Move)
    (h : ∀ n, ∃ z, zrun (table a) n start = some z) : SiblingWitness :=
  .external (table a) (r4_never a h)

def r4 : SiblingSpec where
  path :=
    [(1,(1,false),⟨true,true,2⟩),
     (2,(2,false),⟨false,false,3⟩),
     (3,(3,true),⟨true,false,4⟩),
     (4,(4,true),⟨false,false,1⟩),
     (8,(4,false),⟨true,false,3⟩),
     (9,(3,false),⟨true,true,0⟩),
     (10,(0,true),⟨false,true,0⟩),
     (13,(1,true),⟨false,false,2⟩),
     (14,(2,true),⟨true,true,5⟩)]
  hole := (5,false)
  splitAt := 15
  lastSlot := (5,true)
  bound := 42
  special := ⟨false,true,4⟩
  witness := fun mv =>
    match mv.write,mv.right,mv.next.val with
    | false,false,0 => .cycle 0 17 true (-3)
    | false,false,1 => .cycle 27 8 false (-2)
    | false,false,2 => .cycle 14 2 true 0
    | false,false,3 => .cycle 83 22 false (-2)
    | false,false,4 => counterWitness zeroLE all_defined_LE0
    | false,false,5 => .last 16
    | false,true,0 => counterWitness zeroRA all_defined_RA0
    | false,true,1 => .cycle 0 27 true (-3)
    | false,true,2 => .cycle 12 16 true 0
    | false,true,3 => .cycle 85 73 true (-1)
    | false,true,4 => .known
    | false,true,5 => .cycle 15 1 true 1
    | true,false,0 => .cycle 0 18 true (-3)
    | true,false,1 => .last 41
    | true,false,2 => .last 17
    | true,false,3 => .cycle 0 22 true (-3)
    | true,false,4 => counterWitness oneLE all_defined_LE1
    | true,false,5 => .last 16
    | true,true,0 => .cycle 12 12 true 0
    | true,true,1 => .cycle 35 10 true 0
    | true,true,2 => counterWitness oneRC all_defined_RC1
    | true,true,3 => .cycle 11 29 true (-1)
    | true,true,4 => counterWitness oneRE all_defined_RE1
    | true,true,5 => .cycle 15 1 true 1
    | _,_,_ => .known

theorem r4_valid : ValidSpec r4 := by
  constructor <;> decide

theorem r4_reachable : FirstHolePath r4.parent 6 := spec_reachable r4 r4_valid

theorem r4_attained : ∃ m, compatible r4.parent m ∧ HaltsAfter m 41 :=
  attain_last r4 r4_valid ⟨true,false,1⟩ 41 rfl

theorem r4_exact_from_attained
    (cert : WeightedTNFCertificate r4.bound r4.parent 6) (B : Nat) :
    (∀ m, compatible r4.parent m → WeightedBound B m) ↔ 42 ≤ B := by
  constructor
  · intro h
    obtain ⟨m,hm,hh⟩ := r4_attained
    have hz := firstOne_terminal r4.parent r4_valid.rootCheck m hm
    have hd : 0 ∈ delays (zeroNext m) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hb := h m hm 41 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (cert.sound m hm k d hk hd) hb

#print axioms r4_never
#print axioms r4_valid
#print axioms r4_reachable
#print axioms r4_attained
#print axioms r4_exact_from_attained
end BB6.Agent47R4Parent
