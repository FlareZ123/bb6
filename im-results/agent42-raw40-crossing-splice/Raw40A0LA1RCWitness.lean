import Raw40A0LABase
import SweepPumping
import ZipAuditCore
import SparseBlankDelay

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LA1RCWitness
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

/-- C1=1RC child's exact attained score is 1766: 1764 blank moves,
    a one-unit blank-delay adjustment, and the terminal halt. The literal
    machine is 1RB0LA_1RC0RE_0RD1RC_1LD1LA_HHH0RF_0LA0RD; E0 is the halting slot. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def witness : Machine := fun s => (table s).bind id
theorem witness_compatible : compatible table witness := by
  intro s t ht
  simp only [witness,ht,Option.bind_some,id_eq]

/-- Kernel-checked exact 1764-step original blank tape run: 3×512+228. -/
def z0 : Z0 := ⟨0,[],[]⟩
def z1 : Z0 := ⟨0,[true,true,true,true,false,false,true,true,true,true,true,true],[false,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,false,false,false,true,true,true]⟩
def z2 : Z0 := ⟨3,[false,false,true,true,false,true,true,true,true,true,true,true,false,false,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true],[false,false,false,false,false,true,true,true,false,false,true,true,true,false,false,false,true,true,true]⟩
def z3 : Z0 := ⟨2,[false,true,true,true,true,true],[true,true,true,false,false,false,false,false,true,true,true,true,true,true,false,false,false,true,true,true,false,false,true,true,true,false,false,false,false,false,false,true,true,true,true,true,true,false,true,true,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,false,true,true,true]⟩
def z4 : Z0 := ⟨4,[false,false,true,false,false,true,false,false,true,false,false,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true,true,false,false,true,false,true,true,true,true,true,true,true,false,false,true,false,false,true,true,true,true,true,true],[false,true,true,true,false,false,true,true,true,false,false,false,true,true,true]⟩
theorem part0 : run0 table 512 z0 = some z1 := by decide +kernel
theorem part1 : run0 table 512 z1 = some z2 := by decide +kernel
theorem part2 : run0 table 512 z2 = some z3 := by decide +kernel
theorem part3 : run0 table 228 z3 = some z4 := by decide +kernel
theorem query : run0 table 1764 (project start) = some z4 := by
  have h := part0
  have h := join0 h part1
  have h := join0 h part2
  have h := join0 h part3
  have hn : (((512+512)+512)+228) = 1764 := by omega
  simpa only [hn,z0,project,start] using h

theorem witness_halts : HaltsAfter witness 1764 := by
  have hz : (zrun table 1764 start).map project = some z4 :=
    (run_project table 1764 start).trans query
  cases h : zrun table 1764 start with
  | none => simp [h] at hz
  | some z =>
    have hproj : project z = z4 := by
      simpa only [h,Option.map_some,Option.some.injEq] using hz
    have H := zrun_sound table witness witness_compatible _ start z h
    rw [start_embed] at H
    have hread : readSlot (embed z) = (4,false) := by
      rw [read_embed]
      have e := congrArg (fun x : Z0 => (x.q,x.l.headD false)) hproj
      exact e.trans (by decide)
    constructor
    · rw [H]
      rfl
    · rw [run_append,H,Option.bind_some]
      change rawStep witness (embed z) = none
      rw [rawStep,hread]
      rfl

/-- This child is a genuine delayed-blank-score example: physical
    steps alone underestimate weighted score by two. -/
theorem witness_delay : 1 ∈ delays (zeroNext witness) 0 := by decide

abbrev fiveHoleParent : PartialMachine :=
  BB6.Agent19Raw40.A0LA.child ⟨true,true,2⟩

theorem parent_compatible : compatible fiveHoleParent witness := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first
    | have h : fiveHoleParent (_,_) = none := by decide
      rw [h] at ht
      contradiction
    | cases ht <;> rfl

theorem lower_sharp (B : Nat) (hB : B < 1766) :
    ∃ m : Machine, compatible fiveHoleParent m ∧ ¬ WeightedBound B m := by
  refine ⟨witness,parent_compatible,?_⟩
  intro hb
  have hn := hb 1764 1 witness_halts witness_delay
  omega

#print axioms query
#print axioms witness_halts
#print axioms lower_sharp
end BB6.Agent42Raw40A0LA1RCWitness
