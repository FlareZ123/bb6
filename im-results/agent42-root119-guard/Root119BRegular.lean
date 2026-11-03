import Root119CGate

set_option linter.unusedSimpArgs false

namespace BB6Root119

def BZero (b : Conf) : Prop := b.q = .B ∧ b.tape b.h = false

/-- C scans r ones; all bits weakly left of its head equal the B seed. -/
def CPhase (b c : Conf) (r : Nat) : Prop :=
  BZero b ∧ c.q = .C ∧
  c.h = b.h - 1 - (r : Int) ∧
  (∀ x : Int, x ≤ c.h → c.tape x = b.tape x) ∧
  (∀ i : Nat, i < r → b.tape (b.h - 1 - (i : Int)) = true)

theorem to_C {u v : Conf} (hs : next u = some v) (hC : v.q = .C) :
    (u.q = .B ∧ u.tape u.h = false) ∨
    (u.q = .C ∧ u.tape u.h = true) := by
  cases u with
  | mk q h t =>
    cases q <;> cases hb : t h <;> simp [next,hb] at hs
    all_goals cases hs
    all_goals simp_all

theorem CPhase_from_B {b c : Conf} (hb : BZero b)
    (hs : next b = some c) : CPhase b c 0 := by
  rcases b with ⟨q,pos,t⟩
  obtain ⟨hB,h0⟩ := hb
  change t pos = false at h0
  cases q <;> try contradiction
  have hstep0 : next ⟨.B,pos,t⟩ = some ⟨.C,pos-1,setBit t pos true⟩ := by
    simp [next,h0]
  rw [hstep0] at hs
  cases hs
  refine ⟨⟨rfl,h0⟩,rfl,?_,?_,?_⟩
  · change pos-1 = pos-1-((0:Nat):Int)
    omega
  · intro x hx
    change setBit t pos true x = t x
    change x ≤ pos-1 at hx
    have hne : x ≠ pos := by omega
    simp [setBit,hne]
  · intro i hi
    omega

theorem CPhase_follow_C {b c d : Conf} {r : Nat}
    (hp : CPhase b c r) (hbit : c.tape c.h = true)
    (hs : next c = some d) : CPhase b d (r+1) := by
  obtain ⟨hb,hC,hh,hpref,hones⟩ := hp
  rcases c with ⟨q,pos,t⟩
  change pos = b.h - 1 - (r:Int) at hh
  change ∀ x : Int, x ≤ pos → t x = b.tape x at hpref
  change t pos = true at hbit
  cases q <;> try contradiction
  have hstep1 : next ⟨.C,pos,t⟩ = some ⟨.C,pos-1,setBit t pos false⟩ := by
    simp [next,hbit]
  rw [hstep1] at hs
  cases hs
  refine ⟨hb,rfl,?_,?_,?_⟩
  · change pos-1 = b.h - 1 - ((r+1 : Nat) : Int)
    omega
  · intro x hx
    change setBit t pos false x = b.tape x
    change x ≤ pos-1 at hx
    have hne : x ≠ pos := by omega
    simp only [setBit, if_neg hne]
    apply hpref x
    omega
  · intro i hi
    by_cases hir : i < r
    · exact hones i hir
    · have ieq : i = r := by omega
      subst i
      have heq : pos = b.h-1-(r:Int) := hh
      have hhead : t pos = b.tape pos := hpref pos (by omega)
      calc
        b.tape (b.h-1-(r:Int)) = b.tape pos := by rw [← heq]
        _ = t pos := hhead.symm
        _ = true := hbit

theorem reached_C_has_phase (c : Conf) (hc : Reach c) :
    c.q = .C → ∃ b r, Reach b ∧ CPhase b c r := by
  induction hc with
  | initial =>
    intro hC
    simp [blank] at hC
  | follow hu hstep ih =>
    intro hC
    obtain hB | hCprev := to_C hstep hC
    · exact ⟨_,0,hu,CPhase_from_B hB hstep⟩
    · obtain ⟨b,r,hb,hphase⟩ := ih hCprev.1
      exact ⟨b,r+1,hb,CPhase_follow_C hphase hCprev.2 hstep⟩

/-- Word read left to right: 1100 (1 repeated r times) 0 at B/0. -/
def BBad (b : Conf) : Prop :=
  BZero b ∧ ∃ r : Nat,
    (∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true) ∧
    b.tape (b.h-1-(r:Int)) = false ∧
    b.tape (b.h-2-(r:Int)) = false ∧
    b.tape (b.h-3-(r:Int)) = true ∧
    b.tape (b.h-4-(r:Int)) = true

theorem CPhase_CGate_implies_BBad {b c : Conf} {r : Nat}
    (hp : CPhase b c r) (hg : CGate c) : BBad b := by
  obtain ⟨hb,hC,hpos,hpre,hones⟩ := hp
  obtain ⟨_,h0,h1,h2,h3⟩ := hg
  have heq0 : b.h-1-(r:Int) = c.h := by omega
  have heq1 : b.h-2-(r:Int) = c.h-1 := by omega
  have heq2 : b.h-3-(r:Int) = c.h-2 := by omega
  have heq3 : b.h-4-(r:Int) = c.h-3 := by omega
  refine ⟨hb,r,hones,?_,?_,?_,?_⟩
  · rw [heq0]
    exact (hpre c.h (by omega)).symm.trans h0
  · rw [heq1]
    exact (hpre (c.h-1) (by omega)).symm.trans h1
  · rw [heq2]
    exact (hpre (c.h-2) (by omega)).symm.trans h2
  · rw [heq3]
    exact (hpre (c.h-3) (by omega)).symm.trans h3

theorem reached_CGate_has_BBad (c : Conf) (hc : Reach c)
    (hg : CGate c) : ∃ b, Reach b ∧ BBad b := by
  obtain ⟨b,r,hb,hphase⟩ := reached_C_has_phase c hc hg.1
  exact ⟨b,hb,CPhase_CGate_implies_BBad hphase hg⟩

theorem B_always_moves (b : Conf) (hB : b.q = .B) :
    ∃ c, next b = some c := by
  rcases b with ⟨q,h,t⟩
  cases q <;> simp_all [next]
  cases hb : t h <;> simp [next,hb]

theorem C_always_moves (c : Conf) (hC : c.q = .C) :
    ∃ d, next c = some d := by
  rcases c with ⟨q,h,t⟩
  cases q <;> simp_all [next]
  cases hb : t h <;> simp [next,hb]

theorem scan_from_B (b : Conf) (hb : Reach b) (hB : BZero b)
    (r : Nat)
    (hones : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true) :
    ∃ c, Reach c ∧ CPhase b c r := by
  induction r with
  | zero =>
    obtain ⟨c,hstep⟩ := B_always_moves b hB.1
    exact ⟨c,Reach.follow hb hstep,CPhase_from_B hB hstep⟩
  | succ r ih =>
    have hpre : ∀ i : Nat, i < r → b.tape (b.h-1-(i:Int)) = true := by
      intro i hi
      exact hones i (by omega)
    obtain ⟨c,hc,phase⟩ := ih hpre
    have hC : c.q = .C := phase.2.1
    have hpos : c.h = b.h-1-(r:Int) := phase.2.2.1
    have hprefix : ∀ x, x ≤ c.h → c.tape x = b.tape x := phase.2.2.2.1
    have hbit : c.tape c.h = true := by
      calc
        c.tape c.h = b.tape c.h := hprefix c.h (by omega)
        _ = b.tape (b.h-1-(r:Int)) := by rw [hpos]
        _ = true := hones r (by omega)
    obtain ⟨d,hstep⟩ := C_always_moves c hC
    exact ⟨d,Reach.follow hc hstep,CPhase_follow_C phase hbit hstep⟩

theorem reached_BBad_has_CGate (b : Conf) (hb : Reach b)
    (hbad : BBad b) : ∃ c, Reach c ∧ CGate c := by
  obtain ⟨hB,r,hones,h0,h1,h2,h3⟩ := hbad
  obtain ⟨c,hc,phase⟩ := scan_from_B b hb hB r hones
  obtain ⟨_,hC,hpos,hprefix,_⟩ := phase
  have hpos0 : c.h = b.h - 1 -(r:Int) := hpos
  have heq0 : c.h = b.h-1-(r:Int) := by omega
  have heq1 : c.h-1 = b.h-2-(r:Int) := by omega
  have heq2 : c.h-2 = b.h-3-(r:Int) := by omega
  have heq3 : c.h-3 = b.h-4-(r:Int) := by omega
  refine ⟨c,hc,⟨hC,?_,?_,?_,?_⟩⟩
  · rw [heq0]
    exact (hprefix (b.h-1-(r:Int)) (by omega)).trans h0
  · rw [heq1]
    exact (hprefix (b.h-2-(r:Int)) (by omega)).trans h1
  · rw [heq2]
    exact (hprefix (b.h-3-(r:Int)) (by omega)).trans h2
  · rw [heq3]
    exact (hprefix (b.h-4-(r:Int)) (by omega)).trans h3

/-- Exact all-time blank-root halting iff a reached B/0 reads the left word
    1100 1^r 0 for some finite natural r. -/
theorem blank_halts_iff_regular_B_gate :
    (∃ a, Reach a ∧ next a = none) ↔ (∃ b, Reach b ∧ BBad b) := by
  rw [blank_halts_iff_C_gate]
  constructor
  · rintro ⟨c,hc,hg⟩
    exact reached_CGate_has_BBad c hc hg
  · rintro ⟨b,hb,hg⟩
    exact reached_BBad_has_CGate b hb hg

#print axioms BB6Root119.blank_halts_iff_regular_B_gate
end BB6Root119
