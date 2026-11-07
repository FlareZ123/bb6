import WindowR4
import Lean.Elab.Tactic.Omega
namespace BB429WindowLeaf
open BB6Coverage BB429WindowR4
set_option maxRecDepth 30000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

def abstractStep (m : Machine) (q : Fin 6) (w : W) (far : Bool) : Option (Fin 6 × W) :=
  (m (q,w.c)).map (fun t =>
    (t.next, if t.right then shiftR w t.write far else shiftL w t.write far))

theorem abstractStep_sound (m : Machine) (c d : Config)
    (hs : rawStep m c = some d) :
    ∃ far, abstractStep m c.state (view c) far = some (d.state, view d) := by
  cases hm : m (readSlot c) with
  | none => simp [rawStep,hm] at hs
  | some t =>
      have hd : d = applyMove c t := by
        simpa [rawStep,hm] using hs.symm
      obtain ⟨far,hview⟩ := view_move c t
      refine ⟨far,?_⟩
      rw [hd]
      have hr : (c.state, (view c).c) = readSlot c := rfl
      simp only [abstractStep,hr,hm,Option.map_some]
      apply congrArg Option.some
      exact Prod.ext rfl hview.symm

/-- A finite local certificate, sound for any binary six-state machine. -/
theorem closed_abstract_implies_all_blank (m : Machine)
    (P : Fin 6 → W → Bool)
    (hstart : P blank.state (view blank) = true)
    (hclosed : ∀ q w far, P q w = true →
      (match abstractStep m q w far with
       | none => true
       | some next => P next.1 next.2) = true)
    (n : Nat) (c : Config)
    (hr : run m n blank = some c) : P c.state (view c) = true := by
  induction n generalizing c with
  | zero =>
      have hc : c=blank := by simpa [run] using hr.symm
      subst c
      exact hstart
  | succ n ih =>
      cases hp : run m n blank with
      | none => simp [run,hp] at hr
      | some d =>
          have hs : rawStep m d = some c := by
            simpa [run,hp] using hr
          obtain ⟨far,habs⟩ := abstractStep_sound m d c hs
          have hstep := hclosed d.state (view d) far (ih d hp)
          rw [habs] at hstep
          exact hstep

/-- A complete finite reachable-window certificate that excludes all halt
slots proves the entire unbounded physical execution never halts. -/
theorem finite_window_never (m : Machine) (P : Fin 6 → W → Bool)
    (hstart : P blank.state (view blank) = true)
    (hclosed : ∀ q w far, P q w = true →
      (match abstractStep m q w far with
       | none => true
       | some next => P next.1 next.2) = true)
    (hsafe : ∀ q w, P q w = true → (m (q,w.c)).isSome = true) :
    NeverHalts m := by
  intro n
  cases h : run m n blank with
  | some c => simp
  | none =>
      have hall : ∀ k, (run m k blank).isSome = true := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
            cases hk : run m k blank with
            | none => simp [hk] at ih
            | some c =>
                have hp := closed_abstract_implies_all_blank m P hstart hclosed k c hk
                have hrow := hsafe c.state (view c) hp
                have hslot : (c.state, (view c).c) = readSlot c := rfl
                rw [hslot] at hrow
                cases hm : m (readSlot c) with
                | none => simp [hm] at hrow
                | some t => simp [run,hk,rawStep,hm]
      have bad := hall n
      simp [h] at bad

/-- For any sparse partial machine, a finite closed tape-window predicate
mentioning only assigned nonhalting slots certifies every total completion. -/
theorem partial_finite_window_never (p : PartialMachine) (P : Fin 6 → W → Bool)
    (hstart : P blank.state (view blank) = true)
    (hfixed : ∀ q w, P q w = true →
      ∃ mv, p (q,w.c) = some (some mv))
    (hclosed : ∀ q w far mv, P q w = true →
      p (q,w.c) = some (some mv) →
      P mv.next (if mv.right then shiftR w mv.write far
                 else shiftL w mv.write far) = true)
    (m : Machine) (hcompatible : compatible p m) : NeverHalts m := by
  have hrow (q:Fin 6) (w:W) (h:P q w=true) :
      ∃ mv, m (q,w.c) = some mv := by
    obtain ⟨mv,hp⟩ := hfixed q w h
    exact ⟨mv,hcompatible (q,w.c) (some mv) hp⟩
  have hmclosed : ∀ q w far, P q w = true →
    (match abstractStep m q w far with
     | none => true
     | some next => P next.1 next.2) = true := by
    intro q w far h
    obtain ⟨mv,hm⟩ := hrow q w h
    have hp := hfixed q w h
    obtain ⟨mv0,hp0⟩ := hp
    have hm0 := hcompatible (q,w.c) (some mv0) hp0
    have heq : mv0=mv := Option.some.inj (hm0.symm.trans hm)
    subst mv0
    simp only [abstractStep,hm,Option.map_some]
    exact hclosed q w far mv h hp0
  apply finite_window_never m P hstart hmclosed
  intro q w h
  obtain ⟨mv,hm⟩ := hrow q w h
  simp [hm]

/-- A local invariant gives a genuine universal global-coverage leaf for
all 25-way total completions of an assigned sparse machine. -/
theorem finite_window_cover (p : PartialMachine) (P : Fin 6 → W → Bool)
    (hstart : P blank.state (view blank) = true)
    (hfixed : ∀ q w, P q w = true →
      ∃ mv, p (q,w.c) = some (some mv))
    (hclosed : ∀ q w far mv, P q w = true →
      p (q,w.c) = some (some mv) →
      P mv.next (if mv.right then shiftR w mv.write far
                 else shiftL w mv.write far) = true)
    (bound : Nat) : Cover (DecidedBelow bound) p := by
  refine Cover.leaf p ?_
  intro m hm
  exact Or.inl (partial_finite_window_never p P hstart hfixed hclosed m hm)

private def A : Fin 6 := ⟨0,by decide⟩
private def B : Fin 6 := ⟨1,by decide⟩

/-- Four fixed input rows, with all other rows freely assignable. A/0
writes1 and B/0 writes0, so zero-only control graph closure fails. -/
def oscillatory : PartialMachine := fun s =>
  if s = (A,false) then some (some ⟨true,true,B⟩)
  else if s = (A,true) then some (some ⟨true,true,B⟩)
  else if s = (B,false) then some (some ⟨false,false,A⟩)
  else if s = (B,true) then some none
  else none

def oscillatorSafe (q:Fin 6) (w:W) : Bool :=
  if q=A then !w.r1
  else if q=B then !w.c && w.l1
  else false

theorem oscillator_initial : oscillatorSafe blank.state (view blank) = true := by decide

theorem oscillator_fixed : ∀ q w, oscillatorSafe q w = true →
      ∃ mv, oscillatory (q,w.c) = some (some mv) := by
  intro q w h
  rcases w with ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hlt:=q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;>
    cases c <;> simp [oscillatorSafe,oscillatory,A,B] at h ⊢

theorem oscillator_closed : ∀ q w far mv, oscillatorSafe q w = true →
      oscillatory (q,w.c) = some (some mv) →
      oscillatorSafe mv.next (if mv.right then shiftR w mv.write far
                  else shiftL w mv.write far) = true := by
  intro q w far mv h hp
  rcases w with ⟨l4,l3,l2,l1,c,r1,r2,r3,r4⟩
  rcases mv with ⟨write,right,next⟩
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by
    have hlt:=q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;>
    cases c <;>
    simp [oscillatorSafe,oscillatory,A,B] at h hp ⊢ <;>
    cases hp <;> simp_all [shiftR,shiftL,oscillatorSafe,A,B] <;> omega

/-- Every total machine compatible with this four-row partial table
is a genuine infinite blank-tape nonhalting machine. -/
theorem oscillator_never (m:Machine) (hm:compatible oscillatory m) :
    NeverHalts m :=
  partial_finite_window_never oscillatory oscillatorSafe oscillator_initial
    oscillator_fixed oscillator_closed m hm

theorem oscillator_leaf (bound:Nat) : Cover (DecidedBelow bound) oscillatory :=
  finite_window_cover oscillatory oscillatorSafe oscillator_initial
    oscillator_fixed oscillator_closed bound

#print axioms finite_window_cover
#print axioms oscillator_leaf
end BB429WindowLeaf
