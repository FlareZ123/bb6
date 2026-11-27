import Box28SweepFillSource

namespace BB6.Agent17.Box28SweepFillRectangle
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent13.Box17
open BB6.Agent17.Box28SweepFill
open BB6.Agent17.Box28SweepFillSource
open BB6.Agent17.Box28CarryFamily (Gate Froot localBlank pair)
open BB6.Agent17.Box28CarryPrefix (FinConfig bits view view_q view_a fRight fLeft fAction view_right view_left)
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem view_action (e : Option Move) (c : FinConfig) :
    (fAction e c).map view = action e (view c) := by
  exact BB6.Agent17.Box28CarryPrefix.view_action e c

def fstep (e : Option Move) (c : FinConfig) : Option FinConfig :=
  match c.q,c.a with
  | .A,false => some (fRight .B true c)
  | .A,true => some (fRight .F true c)
  | .B,false | .C,false => some (fLeft .C true c)
  | .B,true => none
  | .C,true => some (fLeft .D false c)
  | .D,false => some (fRight .E false c)
  | .D,true => some (fLeft .D true c)
  | .E,false => fAction e c
  | .E,true => some (fRight .F true c)
  | .F,false => some (fRight .A true c)
  | .F,true => some (fRight .F true c)

theorem fstep_view (e : Option Move) (c : FinConfig) :
    (fstep e c).map view = stepCore (fun _ => none) (action e) (view c) := by
  rcases c with ⟨q,l,a,r⟩
  cases q <;> cases a <;>
    simp only [fstep,stepCore,view_q,view_a,Option.map_some,Option.map_none,view_right,view_left,view_action] <;> rfl

/-- Every successful checked step avoids the missing B1 gate. Thus the
    successful prefix is valid for arbitrary B1, not just halt. -/
theorem fstep_sound (e : Option Move) (b : Gate) (c d : FinConfig)
    (hs : fstep e c = some d) :
    stepCore b (action e) (view c) = some (view d) := by
  have h := fstep_view e c
  rw [hs,Option.map_some] at h
  rcases c with ⟨q,l,a,r⟩
  cases q <;> cases a <;> first | exact h.symm | simp [fstep] at hs

def runFinite (e : Option Move) : Nat → FinConfig → Option FinConfig
  | 0,c => some c
  | n+1,c => (fstep e c).bind (runFinite e n)

theorem runFinite_sound (e : Option Move) (b : Gate) (n : Nat)
    (c d : FinConfig) (h : runFinite e n c = some d) :
    runCore b (action e) n (view c) = some (view d) := by
  induction n generalizing c with
  | zero =>
    have hc : c = d := Option.some.inj h
    subst d
    rfl
  | succ n ih =>
    cases hs : fstep e c with
    | none => simp [runFinite,hs] at h
    | some c' =>
      have h' : runFinite e n c' = some d := by
        simpa only [runFinite,hs,Option.bind_some] using h
      rw [runCore,fstep_sound e b c c' hs,Option.bind_some]
      exact ih c' h'

def fblank : FinConfig := ⟨.A,[],false,[]⟩

theorem sourcePrefix (m : Machine) (e : Option Move)
    (he : m (4,false) = e) (n : Nat) (d : FinConfig)
    (h : runFinite e n fblank = some d) :
    runCore (sourceGate m (1,true)) (sourceGate m (4,false)) n localBlank = some (view d) := by
  have hg : sourceGate m (4,false) = action e := by unfold sourceGate; rw [he]
  rw [hg]
  exact runFinite_sound e (sourceGate m (1,true)) n fblank d h


theorem gate2 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨false,true,0⟩) : NeverHalts m := by
  refine from_root m hm 6 1 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨false,true,0⟩) he 6 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate4 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,true,0⟩) : NeverHalts m := by
  refine from_root m hm 6 2 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨true,true,0⟩) he 6 (⟨.F,[true,true,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate12 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,true,2⟩) : NeverHalts m := by
  refine from_root m hm 9 1 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨true,true,2⟩) he 9 (⟨.F,[true,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate14 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨false,true,3⟩) : NeverHalts m := by
  refine from_root m hm 8 1 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨false,true,3⟩) he 8 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate15 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,false,3⟩) : NeverHalts m := by
  refine from_root m hm 7 1 (C9Pair.push true (zeros)) ?_ (Word.one (Word.endWord))
  have hp := sourcePrefix m (some ⟨true,false,3⟩) he 7 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate16 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,true,3⟩) : NeverHalts m := by
  refine from_root m hm 9 1 (C9Pair.push true (zeros)) ?_ (Word.one (Word.endWord))
  have hp := sourcePrefix m (some ⟨true,true,3⟩) he 9 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate18 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨false,true,4⟩) : NeverHalts m := by
  refine from_root m hm 6 1 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨false,true,4⟩) he 6 (⟨.F,[true,false,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate20 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,true,4⟩) : NeverHalts m := by
  refine from_root m hm 6 2 (zeros) ?_ (Word.endWord)
  have hp := sourcePrefix m (some ⟨true,true,4⟩) he 6 (⟨.F,[true,true,false],false,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate22 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨false,true,5⟩) : NeverHalts m := by
  refine from_root m hm 5 0 (C9Pair.push true (zeros)) ?_ (Word.one (Word.endWord))
  have hp := sourcePrefix m (some ⟨false,true,5⟩) he 5 (⟨.F,[false,false],true,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate23 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,false,5⟩) : NeverHalts m := by
  refine from_root m hm 5 0 (pair false true (C9Pair.push true (zeros))) ?_ (Word.gap (Word.one (Word.endWord)))
  have hp := sourcePrefix m (some ⟨true,false,5⟩) he 5 (⟨.F,[],false,[true,true]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

theorem gate24 (m : Machine) (hm : compatible baseTable m)
    (he : m (4,false) = some ⟨true,true,5⟩) : NeverHalts m := by
  refine from_root m hm 5 1 (C9Pair.push true (zeros)) ?_ (Word.one (Word.endWord))
  have hp := sourcePrefix m (some ⟨true,true,5⟩) he 5 (⟨.F,[true,false],true,[]⟩) (by decide)
  simpa [view,bits,Froot,ones,rep,pair] using hp

def cylinder (e : Fin 25) : PartialMachine :=
  refine baseTable (4,false) (decode e)

def witness (e : Fin 25) : Option Witness :=
  match e.val with
  | 0 => some (.halt 4)
  | 1 => some (.cycle 0 5 false 1)
  | 3 => some (.last 3 6)
  | 5 => some (.cycle 6 1 false (-2))
  | 6 => some (.last 3 5)
  | 7 => some (.cycle 6 1 false (-2))
  | 8 => some (.last 3 5)
  | 9 => some (.cycle 5 1 false (-1))
  | 10 => some (.cycle 8 1 false 2)
  | 11 => some (.cycle 5 1 false (-1))
  | 13 => some (.cycle 3 2 true (-1))
  | 17 => some (.cycle 4 1 false 0)
  | 19 => some (.cycle 4 1 false 0)
  | 21 => some (.last 3 7)
  | _ => none

def witnessOK (e : Fin 25) : Bool :=
  match witness e with
  | none => true
  | some w => leafCheck 8 #[] (cylinder e) w

theorem all_checks : ∀ e : Fin 25, witnessOK e = true := by decide

theorem sweep_cases : ∀ e : Fin 25, (witness e).isSome = false →
    e=2 ∨ e=4 ∨ e=12 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=18 ∨ e=20 ∨ e=22 ∨ e=23 ∨ e=24 := by decide

theorem cut_compatible (m : Machine) (hm : compatible baseTable m)
    (e : Fin 25) (he : m (4,false) = decode e) : compatible (cylinder e) m := by
  unfold cylinder
  rw [← he]
  exact compatible_refine _ _ _ hm

theorem cut_bound (m : Machine) (hm : compatible baseTable m)
    (e : Fin 25) (he : m (4,false) = decode e) : WeightedBound 8 m := by
  cases hw : witness e with
  | some w =>
    have hc : leafCheck 8 #[] (cylinder e) w = true := by
      simpa [witnessOK,hw] using all_checks e
    apply leafCheck_sound 8 #[] ?_ _ w hc m (cut_compatible m hm e he)
    intro i q h
    simp at h
  | none =>
    apply weighted_of_never
    have hc := sweep_cases e (by simp [hw])
    rcases hc with h|h|h|h|h|h|h|h|h|h|h <;> subst e
    · exact gate2 m hm he
    · exact gate4 m hm he
    · exact gate12 m hm he
    · exact gate14 m hm he
    · exact gate15 m hm he
    · exact gate16 m hm he
    · exact gate18 m hm he
    · exact gate20 m hm he
    · exact gate22 m hm he
    · exact gate23 m hm he
    · exact gate24 m hm he

theorem rectangle_bound (m : Machine) (hm : compatible baseTable m) : WeightedBound 8 m := by
  obtain ⟨e,he⟩ := BB6.Agent17.Box28CarryRectangle.decode_complete (m (4,false))
  exact cut_bound m hm e he.symm

theorem rectangle_mono (B : Nat) (hB : 8 ≤ B) (m : Machine)
    (hm : compatible baseTable m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (rectangle_bound m hm k d hk hd) hB

def maxRow : PartialMachine := refine (cylinder 21) (1,true) none
def maxMachine : Machine := fun s => (maxRow s).getD none

theorem max_compatible : compatible maxRow maxMachine := by
  intro s t h
  simp [maxMachine,h]

theorem max_base_check : ∀ (q : Fin 6) (b : Bool),
    (baseTable (q,b)).isSome = true →
    maxRow (q,b) = baseTable (q,b) := by decide

theorem max_base : compatible baseTable maxMachine := by
  intro s t h
  have he := max_base_check s.1 s.2 (by simp [h])
  exact max_compatible s t (he.trans h)

theorem max_halts : HaltsAfter maxMachine 7 :=
  zipHalt_sound maxRow 7 (by decide) maxMachine max_compatible

#print axioms all_checks
#print axioms rectangle_bound
#print axioms max_halts
#print axioms max_base
end BB6.Agent17.Box28SweepFillRectangle
