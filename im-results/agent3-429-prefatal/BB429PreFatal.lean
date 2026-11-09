import BB429FatalB
import FreshCell
import Lean.Elab.Tactic.Omega

namespace BB429PreFatal
open BB6Coverage BB429PhysicalFrontier

private def A : Fin 6 := ⟨0, by decide⟩
private def B : Fin 6 := ⟨1, by decide⟩
private def C : Fin 6 := ⟨2, by decide⟩

/-- The two physical predecessor shapes of the genuine B/001 fatal gate. -/
def preFatal (a : Config) : Prop :=
  (readSlot a = (A,false) ∨ readSlot a = (C,true)) ∧
  a.tape (a.head+1) = false ∧ a.tape (a.head+2) = false ∧
  a.tape (a.head+3) = true

abbrev fatalB := BB429FatalB.fatalB

private theorem target429_B_input (s : Slot) (mv : Move)
    (h : target429 s = some mv) (hn : mv.next = B) :
    (s = (A,false) ∨ s = (C,true)) ∧ mv.right = true := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    have he := q.isLt
    omega
  rcases hq with hq|hq|hq|hq|hq|hq <;> subst q <;> cases b <;>
    simp [BB429PhysicalFrontier.target429, BB429PhysicalFrontier.prefix11,
      BB429PhysicalFrontier.prefix10, BB429PhysicalFrontier.prefix9,
      BB429PhysicalFrontier.prefix8, BB429PhysicalFrontier.prefix7,
      BB429PhysicalFrontier.prefix6, BB429PhysicalFrontier.prefix5,
      BB429PhysicalFrontier.prefix4, BB429PhysicalFrontier.prefix3,
      BB429PhysicalFrontier.prefix2, BB429PhysicalFrontier.prefix1,
      BB429PhysicalFrontier.prefix0, refine, emptyTable] at h <;>
    cases h <;> simp_all [A,B,C]

private theorem right_tape_0 (a : Config) (mv : Move) (hr : mv.right = true) :
    (applyMove a mv).tape (applyMove a mv).head = a.tape (a.head+1) := by
  simp only [applyMove,hr,ite_true]
  have ne : a.head + 1 ≠ a.head := by omega
  simp [ne]

private theorem right_tape_1 (a : Config) (mv : Move) (hr : mv.right = true) :
    (applyMove a mv).tape ((applyMove a mv).head+1) = a.tape (a.head+2) := by
  simp only [applyMove,hr,ite_true]
  have ne : a.head + 2 ≠ a.head := by omega
  have he : a.head + 1 + 1 = a.head+2 := by omega
  rw [he]
  simp [ne]

private theorem right_tape_2 (a : Config) (mv : Move) (hr : mv.right = true) :
    (applyMove a mv).tape ((applyMove a mv).head+2) = a.tape (a.head+3) := by
  simp only [applyMove,hr,ite_true]
  have ne : a.head + 3 ≠ a.head := by omega
  have he : a.head + 1 + 2 = a.head+3 := by omega
  rw [he]
  simp [ne]

private theorem fatalB_from_preFatal (n : Nat) (a : Config)
    (hreach : run target429 n blank = some a) (hp : preFatal a) :
    ∃ b, run target429 (n+1) blank = some b ∧ fatalB b := by
  rcases hp with ⟨hslot,h1,h2,h3⟩
  rcases hslot with hA|hC
  · let mv : Move := ⟨true,true,B⟩
    have hm : target429 (readSlot a) = some mv := by
      simpa [hA,mv] using
        (show target429 (A,false) = some ⟨true,true,B⟩ by decide)
    let b := applyMove a mv
    have hb : run target429 (n+1) blank = some b := by
      change (run target429 n blank).bind (rawStep target429) = some b
      rw [hreach]; simp [rawStep,hm,b]
    refine ⟨b,hb,?_,?_,?_,?_⟩
    · rfl
    · simpa [b] using (right_tape_0 a mv rfl).trans h1
    · simpa [b] using (right_tape_1 a mv rfl).trans h2
    · simpa [b] using (right_tape_2 a mv rfl).trans h3
  · let mv : Move := ⟨false,true,B⟩
    have hm : target429 (readSlot a) = some mv := by
      simpa [hC,mv] using
        (show target429 (C,true) = some ⟨false,true,B⟩ by decide)
    let b := applyMove a mv
    have hb : run target429 (n+1) blank = some b := by
      change (run target429 n blank).bind (rawStep target429) = some b
      rw [hreach]; simp [rawStep,hm,b]
    refine ⟨b,hb,?_,?_,?_,?_⟩
    · rfl
    · simpa [b] using (right_tape_0 a mv rfl).trans h1
    · simpa [b] using (right_tape_1 a mv rfl).trans h2
    · simpa [b] using (right_tape_2 a mv rfl).trans h3

private theorem preFatal_from_fatalB (n : Nat) (b : Config)
    (hreach : run target429 (n+1) blank = some b) (hb : fatalB b) :
    ∃ a, run target429 n blank = some a ∧ preFatal a := by
  rcases hb with ⟨hB,h0,h1,h2⟩
  cases hprev : run target429 n blank with
  | none => simp [run,hprev] at hreach
  | some a =>
    have hstep : rawStep target429 a = some b := by
      simpa [run,hprev] using hreach
    cases ht : target429 (readSlot a) with
    | none => simp [rawStep,ht] at hstep
    | some mv =>
      have heq : b = applyMove a mv := by
        simpa [rawStep,ht] using hstep.symm
      have hnext : mv.next = B := by
        rw [heq] at hB
        exact hB
      obtain ⟨hslot,hdir⟩ := target429_B_input (readSlot a) mv ht hnext
      have hp1 : a.tape (a.head+1) = false := by
        have h := right_tape_0 a mv hdir
        rw [←heq] at h
        exact h.symm.trans h0
      have hp2 : a.tape (a.head+2) = false := by
        have h := right_tape_1 a mv hdir
        rw [←heq] at h
        exact h.symm.trans h1
      have hp3 : a.tape (a.head+3) = true := by
        have h := right_tape_2 a mv hdir
        rw [←heq] at h
        exact h.symm.trans h2
      exact ⟨a,by simpa using hprev,⟨hslot,hp1,hp2,hp3⟩⟩

/-- Exact source-level equivalence at every original blank-tape step. -/
theorem preFatal_iff_next_fatalB (n : Nat) :
    (∃ a, run target429 n blank = some a ∧ preFatal a) ↔
    (∃ b, run target429 (n+1) blank = some b ∧ fatalB b) := by
  constructor
  · rintro ⟨a, ha, hp⟩
    exact fatalB_from_preFatal n a ha hp
  · rintro ⟨b, hb, hf⟩
    exact preFatal_from_fatalB n b hb hf

/-- The original six-state blank-run halts exactly on either predecessor shape. -/
theorem halts_iff_root_preFatal :
    (∃ n, HaltsAfter target429 n) ↔
    (∃ n a, run target429 n blank = some a ∧ preFatal a) := by
  rw [BB429FatalB.target429_halts_iff_root_B001]
  constructor
  · rintro ⟨n,b,hb,hf⟩
    cases n with
    | zero =>
        have heq : b = blank := by simpa [run] using hb.symm
        have hB : b.state = BB429FatalB.B := hf.1
        rw [heq] at hB
        simp [blank, BB429FatalB.B] at hB
    | succ n =>
        obtain ⟨a,ha,hp⟩ := preFatal_from_fatalB n b hb hf
        exact ⟨n,a,ha,hp⟩
  · rintro ⟨n,a,ha,hp⟩
    obtain ⟨b,hb,hf⟩ := fatalB_from_preFatal n a ha hp
    exact ⟨n+1,b,hb,hf⟩

/-- A genuine halt requires an earlier physical scan three cells right of
    a later A/0001 or C/1001 event. -/
theorem halt_requires_prior_head_three_right
    (hh : ∃ n, HaltsAfter target429 n) :
    ∃ k n d a, k < n ∧ run target429 k blank = some d ∧
      run target429 n blank = some a ∧ preFatal a ∧
      d.head = a.head+3 := by
  obtain ⟨n,a,ha,hp⟩ := halts_iff_root_preFatal.mp hh
  obtain ⟨k,d,hk,hd,hhead⟩ :=
    marked_cell_previously_scanned target429 n a (a.head+3) ha hp.2.2.2
  exact ⟨k,n,d,a,hk,hd,ha,hp,hhead⟩

#print axioms preFatal_iff_next_fatalB
#print axioms halts_iff_root_preFatal
#print axioms halt_requires_prior_head_three_right
end BB429PreFatal
