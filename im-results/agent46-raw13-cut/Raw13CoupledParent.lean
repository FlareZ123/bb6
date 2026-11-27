import Agent46Raw13Base
import Raw13CoupledBoth
import WeightedNonhaltLeafAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13CoupledParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47WeightedHalt

/-- Authentic two-hole node at the end of the raw13 #1093 path
    A1=1LD,D1=0LA,C1=1RE,E1=0RD,D0=1LF,F0=1LC,B1=0RB. -/
def p1 := refine BB6.Agent46Raw13.raw13 (0,true) (some ⟨true,false,3⟩)
def p2 := refine p1 (3,true) (some ⟨false,false,0⟩)
def p3 := refine p2 (2,true) (some ⟨true,true,4⟩)
def p4 := refine p3 (4,true) (some ⟨false,true,3⟩)
def p5 := refine p4 (3,false) (some ⟨true,false,5⟩)
def p6 := refine p5 (5,false) (some ⟨true,false,2⟩)
def parent := refine p6 (1,true) (some ⟨false,true,1⟩)

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent46Raw13.raw13_nohalt))))))

/-- Exact literal E0=1LA machine; the sole external premise is the published
    Cryptids NonHalt theorem for this table (F1 is halt). -/
def published : Machine := fun s => (FAR.fromCodes
  [7,14,11,5,2,19,22,0,2,13,10,24] s).getD none

def certificate (h : NeverHalts published) : Audit :=
  .split 32 (4,false) (byMove [
    .proven (BB6.Agent46Raw13BinarySiblings.p .zeroLA) (BB6.Agent46Raw13BinarySiblings.never .zeroLA),
    .cycle 30 20 true 0,
    .cycle 31 2 true 1,
    .cycle 52 12 true 0,
    .proven (BB6.Agent46Raw13BinarySiblings.p .zeroLE) (BB6.Agent46Raw13BinarySiblings.never .zeroLE),
    .last 33 (5,true),
    .last 35 (5,true),
    .cycle 29 39 true (-2),
    .last 47 (5,true),
    .proven BB6.Agent46Raw13Detour.base BB6.Agent46Raw13CoupledBoth.both_cylinders_never.1,
    .last 133 (5,true),
    .last 33 (5,true),
    .proven (forgetHaltRows published) (forgetHaltRows_all_completions_neverHalt published h),
    .cycle 33 12 true 1,
    .proven BB6.Agent46Raw13Detour.detour BB6.Agent46Raw13CoupledBoth.both_cylinders_never.2,
    .cycle 81 7 false (-3),
    .proven (BB6.Agent46Raw13BinarySiblings.p .oneLE) (BB6.Agent46Raw13BinarySiblings.never .oneLE),
    .last 33 (5,true),
    .proven (BB6.Agent46Raw13BinarySiblings.p .oneRA) (BB6.Agent46Raw13BinarySiblings.never .oneRA),
    .cycle 29 38 true (-1),
    .proven (BB6.Agent46Raw13BinarySiblings.p .oneRC) (BB6.Agent46Raw13BinarySiblings.never .oneRC),
    .last 64 (5,true),
    .cycle 12 21 true (-5),
    .last 33 (5,true)])

theorem checked (h : NeverHalts published) :
    zipCheck 134 parent (certificate h) = true := by rfl

/-- Every completion, including blank-delay lifts, has score at most 134
    if it halts. No assumptions on either of the two unspecified rows. -/
theorem bound (h : NeverHalts published) (m : Machine)
    (hm : compatible parent m) : WeightedBound 134 m :=
  (certifiedZip 134 parent (certificate h) (by decide) parent_nohalt (checked h)).sound m hm

def witness : Machine :=
  weightedTNFDefaultCompletion (refine parent (4,false) (some ⟨false,true,4⟩))

theorem witness_compatible : compatible parent witness := by
  intro s t hs
  by_cases e : s = (4,false)
  · subst s
    change (none : Option Transition) = some t at hs
    contradiction
  · simp [witness,weightedTNFDefaultCompletion,refine,e,hs]

theorem witness_halts : HaltsAfter witness 133 := by
  constructor <;> first | rfl | decide

theorem exact_threshold (h : NeverHalts published) (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 134 ≤ B := by
  constructor
  · intro hb
    have hz := firstOne_terminal parent (by decide) witness witness_compatible
    have hd : 0 ∈ delays (zeroNext witness) 0 :=
      (mem_delays_iff hz).mpr ⟨0, TerminalPath.stop 0 hz⟩
    have hw := hb witness witness_compatible 133 0 witness_halts hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (bound h m hm k d hk hd) hb

#print axioms bound
#print axioms witness_compatible
#print axioms witness_halts
#print axioms exact_threshold
end BB6.Agent46Raw13CoupledParent
