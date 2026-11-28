import SweepPumping
import Raw10EncodedSourceBridge
import Box17AuditCore
import Box27SliceCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
A 4-cylinder, source-preserving reduction for genuine Raw10 Box27.
D0 codes 5,7,9 move left on fresh zero, with deterministic 3/3/2 step
growth; code 10 enters a deterministic two-step recurrence. All other
seven transition slots A1,B1,D1,E0,E1,F0,F1 remain free.
-/
namespace BB6.Agent49.Box27D0FastPumps
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent31Pump
open BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | _ => none

theorem first (d0 : Fin 25) :
    run0 (table d0) 3 ⟨0,[],[]⟩ = some ⟨3,[],[false,true]⟩ := by rfl

theorem macro05 (R : List Bool) :
    run0 (table 5) 3 ⟨3,[],R⟩ =
      some ⟨3,[],[false,true,false]++R⟩ := by rfl
/-- A single three-move rule shifts the boundary left without consulting D1. -/
theorem macro06 (R : List Bool) :
    run0 (table 6) 3 ⟨3,[],false::R⟩ =
      some ⟨3,[],false::true::R⟩ := by rfl

def family06 (n : Nat) : Z0 :=
  ⟨3,[],false::rep [true] n++[true]⟩

theorem growth06 (n : Nat) :
    run0 (table 6) 3 (family06 n) = some (family06 (n+1)) := by
  simpa only [family06,rep,List.append_assoc,List.cons_append,List.nil_append] using
    macro06 (rep [true] n ++ [true])

theorem never06 (m : Machine) (hm : compatible (table 6) m) :
    NeverHalts m :=
  never_of_growth (table 6) family06 3 (fun _ => 3)
    (by rfl) (by intro n; omega) growth06 m hm

theorem macro07 (R : List Bool) :
    run0 (table 7) 3 ⟨3,[],R⟩ =
      some ⟨3,[],[false,true,true]++R⟩ := by rfl
theorem macro09 (R : List Bool) :
    run0 (table 9) 2 ⟨3,[],R⟩ =
      some ⟨3,[],[false,false]++R⟩ := by rfl

theorem macro10 :
    run0 (table 10) 2 ⟨3,[false],[false,true]⟩ =
      some ⟨3,[false],[false,true]⟩ := by rfl

def family05 (n : Nat) : Z0 := ⟨3,[],rep [false,true,false] n ++ [false,true]⟩
def family07 (n : Nat) : Z0 := ⟨3,[],rep [false,true,true] n ++ [false,true]⟩
def family09 (n : Nat) : Z0 := ⟨3,[],rep [false,false] n ++ [false,true]⟩
def family10 (_ : Nat) : Z0 := ⟨3,[false],[false,true]⟩

theorem growth05 (n : Nat) :
    run0 (table 5) 3 (family05 n) = some (family05 (n+1)) := by
  simpa only [family05,rep,List.append_assoc] using
    macro05 (rep [false,true,false] n ++ [false,true])

theorem growth07 (n : Nat) :
    run0 (table 7) 3 (family07 n) = some (family07 (n+1)) := by
  simpa only [family07,rep,List.append_assoc] using
    macro07 (rep [false,true,true] n ++ [false,true])

theorem growth09 (n : Nat) :
    run0 (table 9) 2 (family09 n) = some (family09 (n+1)) := by
  simpa only [family09,rep,List.append_assoc] using
    macro09 (rep [false,false] n ++ [false,true])

theorem first10 :
    run0 (table 10) 5 ⟨0,[],[]⟩ = some (family10 0) := by rfl
theorem growth10 (n : Nat) :
    run0 (table 10) 2 (family10 n) = some (family10 (n+1)) := macro10

theorem never05 (m : Machine) (hm : compatible (table 5) m) :
    NeverHalts m :=
  never_of_growth (table 5) family05 3 (fun _ => 3)
    (by rfl) (by intro n; omega) growth05 m hm
theorem never07 (m : Machine) (hm : compatible (table 7) m) :
    NeverHalts m :=
  never_of_growth (table 7) family07 3 (fun _ => 3)
    (by rfl) (by intro n; omega) growth07 m hm
theorem never09 (m : Machine) (hm : compatible (table 9) m) :
    NeverHalts m :=
  never_of_growth (table 9) family09 3 (fun _ => 2)
    (by rfl) (by intro n; omega) growth09 m hm
theorem never10 (m : Machine) (hm : compatible (table 10) m) :
    NeverHalts m :=
  never_of_growth (table 10) family10 5 (fun _ => 2)
    first10 (by intro n; omega) growth10 m hm

theorem source_compatible (d0 : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0) : compatible (table d0) m := by
  have e0 : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3 : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  have h0 : m (0,false) = decode 8 := by simpa [e0] using hm (0,false)
  have h1 : m (1,false) = decode 11 := by simpa [e1] using hm (1,false)
  have h2 : m (2,false) = decode 13 := by simpa [e2] using hm (2,false)
  have h3 : m (2,true) = decode 13 := by simpa [e3] using hm (2,true)
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases b <;> simp [table] at ht ⊢ <;> simp_all

def sweepCodes : List (Fin 25) := [5,6,7,9,10]

theorem source_never (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 : Fin 25) (hd0 : m (3,false) = decode d0)
    (hc : d0 ∈ sweepCodes) : NeverHalts m := by
  have h : d0=5 ∨ d0=6 ∨ d0=7 ∨ d0=9 ∨ d0=10 := by
    simpa [sweepCodes] using hc
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact never05 m (source_compatible 5 m hm hd0)
  · exact never06 m (source_compatible 6 m hm hd0)
  · exact never07 m (source_compatible 7 m hm hd0)
  · exact never09 m (source_compatible 9 m hm hd0)
  · exact never10 m (source_compatible 10 m hm hd0)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 : Fin 25) (hd0 : m (3,false) = decode d0)
    (hc : d0 ∈ sweepCodes) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 hd0 hc)


/-- The missing fifth D0 value is a three-move halt, irrespective of all
    seven other free transition slots. -/
theorem check0 :
    BB6.Agent13.Box17.leafCheck 255 #[] (table 0) (.halt 3) = true := by
  unfold BB6.Agent13.Box17.leafCheck BB6.Agent13.Box17.haltBound
  unfold BB6.Agent13.Box17.zipHalt BB6Coverage.Agent10ZipAudit.zipRead
  decide

theorem bound0 (m : Machine) (hm : compatible (table 0) m) :
    WeightedBound 255 m :=
  BB6.Agent49.Box27Slice.terminal_sound 255 (table 0) (.halt 3) check0 m hm

def fastCodes : List (Fin 25) := [0,5,6,7,9,10]

/-- Six of twenty original Box27 D0 values
    is now bounded uniformly with all seven other slots unrestricted. -/
theorem source_fast_bound (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 : Fin 25) (hd0 : m (3,false) = decode d0)
    (hc : d0 ∈ fastCodes) : WeightedBound 255 m := by
  have h : d0=0 ∨ d0=5 ∨ d0=6 ∨ d0=7 ∨ d0=9 ∨ d0=10 := by
    simpa [fastCodes] using hc
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl
  · exact bound0 m (source_compatible 0 m hm hd0)
  · exact source_bound 255 m hm 5 hd0 (by decide)
  · exact source_bound 255 m hm 6 hd0 (by decide)
  · exact source_bound 255 m hm 7 hd0 (by decide)
  · exact source_bound 255 m hm 9 hd0 (by decide)
  · exact source_bound 255 m hm 10 hd0 (by decide)

#print axioms check0
#print axioms bound0
#print axioms source_fast_bound

#print axioms first
#print axioms macro06
#print axioms growth06
#print axioms never06
#print axioms macro05
#print axioms macro07
#print axioms macro09
#print axioms macro10
#print axioms growth05
#print axioms growth07
#print axioms growth09
#print axioms growth10
#print axioms never05
#print axioms never07
#print axioms never09
#print axioms never10
#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0FastPumps
