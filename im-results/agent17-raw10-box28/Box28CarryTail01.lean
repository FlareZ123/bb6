import Box28CarryPrefix

namespace BB6.Agent17.Box28CarryTail01
open BB6Coverage BB6.Agent17.Box28CarryFamily BB6.Agent17.Box28CarryGateSource
open BB6.Agent17.Box28CarryPrefix
open BB6.Agent13.Box33BinaryCounter (zeros zero_head zero_pop zero_push rep rep_add ones ones_succ)
open C9Pair (right left)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The alternate terminal marker is 01, not 1. Both E0=1RA and E0=1RE
    turn that marker into a new 111 digit in exactly the same macro time. -/
def terminal : C9Pair.Stream := pair false true zeros
def entryGate (alt : Bool) : Gate := fun c =>
  some (right (if alt then .E else .A) true c)

inductive Word : C9Pair.Stream → Prop where
  | endWord : Word terminal
  | d111 {s} : Word s → Word (triple true true true s)
  | d110 {s} : Word s → Word (triple true true false s)
  | d101 {s} : Word s → Word (triple true false true s)

theorem prefix_word (k : Nat) (s : C9Pair.Stream) (h : Word s) :
    Word (rep true (3*k) s) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show 3*(k+1)=3+3*k by omega,rep_add]
    exact Word.d111 ih

theorem enterEnd (b : Gate) (alt : Bool) (n : Nat) :
    runCore false b (entryGate alt) 6 (Eroot n terminal) =
      some (Droot (n+2) terminal) := by
  cases alt <;> rfl

theorem endReturn (b : Gate) (alt : Bool) (k : Nat) :
    runCore false b (entryGate alt) (6+(3*k+2+2)) (Eroot (3*k) terminal) =
      some (Eroot 0 (rep true (3*(k+1)) terminal)) := by
  rw [runCore_add,enterEnd,Option.bind_some,rewind]
  rw [show 3*k+2+1=3*(k+1) by omega]

theorem progress (b : Gate) (alt : Bool) (k : Nat) (s : C9Pair.Stream) (h : Word s) :
    ∃ j k' s', 0 < j ∧ runCore false b (entryGate alt) j (Eroot (3*k) s) =
      some (Eroot (3*k') s') ∧ Word s' := by
  cases h with
  | endWord =>
    exact ⟨6+(3*k+2+2),0,rep true (3*(k+1)) terminal,by omega,endReturn b alt k,prefix_word (k+1) _ .endWord⟩
  | d111 ht =>
    refine ⟨3+(3*k+1+2),0,rep true (3*k) (triple true true false _),by omega,?_,prefix_word k _ (.d110 ht)⟩
    rw [runCore_add,enter111,Option.bind_some,rewind,show 3*k+1+1=3*k+2 by omega,rep_add]
    rfl
  | d110 ht =>
    refine ⟨4+(3*k+2),0,rep true (3*k) (triple true false true _),by omega,?_,prefix_word k _ (.d101 ht)⟩
    rw [runCore_add,enter110,Option.bind_some,rewind,rep_add]
    rfl
  | d101 ht => exact ⟨3,k+1,_,by decide,by rw [show 3*(k+1)=3*k+3 by omega,carry3],ht⟩

theorem never (b : Gate) (alt : Bool) (n k : Nat) (s : C9Pair.Stream) (h : Word s) :
    runCore false b (entryGate alt) n (Eroot (3*k) s) ≠ none := by
  induction n using Nat.strongRecOn generalizing k s with
  | ind n ih =>
    intro hn
    obtain ⟨j,k',s',hj,hs,hg⟩ := progress b alt k s h
    by_cases hnj : n≤j
    · rw [show j=n+(j-n) by omega,runCore_add,hn] at hs; contradiction
    · rw [show n=j+(n-j) by omega,runCore_add,hs] at hn
      exact ih _ (by omega) k' s' hg hn

theorem initial (b : Gate) (alt : Bool) :
    runCore false b (entryGate alt) 4 localBlank = some (Eroot 0 terminal) := by
  simp [runCore,stepCore,localBlank,Eroot,terminal,pair,ones,rep,left,right]

theorem never_blank (b : Gate) (alt : Bool) (n : Nat) :
    runCore false b (entryGate alt) n localBlank ≠ none := by
  intro hn
  have hs := initial b alt
  by_cases h : n ≤ 4
  · rw [show (4:Nat)=n+(4-n) by omega,runCore_add,hn] at hs; contradiction
  · rw [show n=4+(n-4) by omega,runCore_add,hs,Option.bind_some] at hn
    exact never b alt (n-4) 0 terminal .endWord hn

theorem source_never (m : Machine) (hm : compatible (baseTable false) m)
    (alt : Bool) (he : sourceGate m (4,false) = entryGate alt) : NeverHalts m := by
  intro n
  have h := project_run false m hm n blank
  change (BB6Coverage.run m n blank).map project =
    runCore false (sourceGate m (1,true)) (sourceGate m (4,false)) n localBlank at h
  rw [he] at h
  have hn := never_blank (sourceGate m (1,true)) alt n
  cases hr : BB6Coverage.run m n blank with
  | none => exact False.elim (hn (by simpa [hr] using h.symm))
  | some c => rfl

theorem gate20_4 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨true,true,0⟩) : NeverHalts m := by
  apply source_never m hm false
  unfold sourceGate
  rw [he]
  rfl

theorem gate20_20 (m : Machine) (hm : compatible (baseTable false) m)
    (he : m (4,false) = some ⟨true,true,4⟩) : NeverHalts m := by
  apply source_never m hm true
  unfold sourceGate
  rw [he]
  rfl

#print axioms endReturn
#print axioms gate20_4
#print axioms gate20_20
end BB6.Agent17.Box28CarryTail01
