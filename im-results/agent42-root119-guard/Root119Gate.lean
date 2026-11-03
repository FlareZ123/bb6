import Std

set_option linter.unusedSimpArgs false

namespace BB6Root119

inductive Q where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

structure Conf where
  q : Q
  h : Int
  tape : Int → Bool

def setBit (t : Int → Bool) (loc : Int) (b : Bool) : Int → Bool :=
  fun p => if p = loc then b else t p

-- Literal auxiliary table 1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD.
def next (c : Conf) : Option Conf :=
  match c.q, c.tape c.h with
  | .A, false => some ⟨.B, c.h+1, setBit c.tape c.h true⟩
  | .A, true  => none
  | .B, false => some ⟨.C, c.h-1, setBit c.tape c.h true⟩
  | .B, true  => some ⟨.F, c.h-1, setBit c.tape c.h true⟩
  | .C, false => some ⟨.D, c.h-1, setBit c.tape c.h true⟩
  | .C, true  => some ⟨.C, c.h-1, setBit c.tape c.h false⟩
  | .D, false => some ⟨.E, c.h-1, setBit c.tape c.h false⟩
  | .D, true  => some ⟨.F, c.h+1, setBit c.tape c.h true⟩
  | .E, false => some ⟨.A, c.h+1, setBit c.tape c.h true⟩
  | .E, true  => some ⟨.A, c.h-1, setBit c.tape c.h true⟩
  | .F, false => some ⟨.B, c.h-1, setBit c.tape c.h true⟩
  | .F, true  => some ⟨.D, c.h+1, setBit c.tape c.h false⟩

def blank : Conf := ⟨.A, 0, fun _ => false⟩

inductive Reach : Conf → Prop where
  | initial : Reach blank
  | follow {u v : Conf} (hu : Reach u) (hstep : next u = some v) : Reach v

def Gate (c : Conf) : Prop :=
  c.q = .D ∧ c.tape c.h = false ∧ c.tape (c.h-1) = true ∧ c.tape (c.h-2) = true

theorem next_none_iff (c : Conf) :
    next c = none ↔ c.q = .A ∧ c.tape c.h = true := by
  cases c with
  | mk q h t =>
    cases q <;> cases hb : t h <;> simp [next, hb]

theorem to_E {u v : Conf} (hstep : next u = some v)
    (hE : v.q = .E) : u.q = .D ∧ u.tape u.h = false := by
  cases u with
  | mk q h t =>
    cases q <;> cases hb : t h <;> simp [next, hb] at hstep
    all_goals cases hstep
    all_goals simp_all

theorem to_A {u v : Conf} (hstep : next u = some v)
    (hA : v.q = .A) : u.q = .E := by
  cases u with
  | mk q h t =>
    cases q <;> cases hb : t h <;> simp [next, hb] at hstep
    all_goals cases hstep
    all_goals simp_all

-- Exact D/0 transition chain, including the source cell writes.
theorem D_stop_after_two_moves (c : Conf) (hq : c.q = .D)
    (hb : c.tape c.h = false) :
    ((next c).bind fun e => (next e).bind next) = none ↔
    c.tape (c.h-1) = true ∧ c.tape (c.h-2) = true := by
  rcases c with ⟨q, pos, t⟩
  cases q <;> try simp_all [next]
  have hp1 : pos-1 ≠ pos := by omega
  have hp2 : pos-2 ≠ pos := by omega
  have hp3 : pos-2 ≠ pos-1 := by omega
  have hn : pos-1-1=pos-2 := by omega
  have hp1r : pos ≠ pos-1 := by omega
  by_cases hleft : t (pos-1) = true
  · by_cases hleft2 : t (pos-2) = true
    · simp [next, hb, setBit, hp1, hp1r, hp2, hp3, hn, hleft, hleft2]
    · simp [next, hb, setBit, hp1, hp1r, hp2, hp3, hn, hleft, hleft2]
  · simp [next, hb, setBit, hp1, hp1r, hp2, hp3, hn, hleft]

theorem reached_E_has_D (e : Conf) (hr : Reach e) (he : e.q = .E) :
    ∃ d, Reach d ∧ next d = some e ∧ d.q = .D ∧ d.tape d.h = false := by
  cases hr with
  | initial => simp [blank] at he
  | follow hd hstep =>
    obtain ⟨hq, hb⟩ := to_E hstep he
    exact ⟨_, hd, hstep, hq, hb⟩

theorem reached_stop_has_gate (c : Conf) (hr : Reach c) (hc : next c = none) :
    ∃ d, Reach d ∧ Gate d := by
  obtain ⟨ha, hb⟩ := (next_none_iff c).mp hc
  cases hr with
  | initial => simp [blank] at hb
  | follow hprev hstep =>
    have he : _ := to_A hstep ha
    obtain ⟨d, hdr, hde, hdq, hdb⟩ := reached_E_has_D _ hprev he
    have ht : ((next d).bind fun e => (next e).bind next) = none := by
      simp [hde, hstep, hc]
    obtain ⟨hl1, hl2⟩ := (D_stop_after_two_moves d hdq hdb).mp ht
    exact ⟨d, hdr, hdq, hdb, hl1, hl2⟩

theorem D_always_moves (d : Conf) (hq : d.q = .D) :
    ∃ e, next d = some e := by
  rcases d with ⟨q,h,t⟩
  cases q <;> simp_all [next]
  cases hb : t h <;> simp [next, hb]

theorem D_zero_enters_E {d e : Conf} (hs : next d = some e)
    (hq : d.q = .D) (hb : d.tape d.h = false) : e.q = .E := by
  rcases d with ⟨q,h,t⟩
  cases q <;> simp_all [next]
  cases hs
  rfl

theorem E_always_moves (e : Conf) (hq : e.q = .E) :
    ∃ a, next e = some a := by
  rcases e with ⟨q,h,t⟩
  cases q <;> simp_all [next]
  cases hb : t h <;> simp [next, hb]

theorem reached_gate_has_stop (d : Conf) (hd : Reach d) (hg : Gate d) :
    ∃ a, Reach a ∧ next a = none := by
  obtain ⟨hq,hb,hleft1,hleft2⟩ := hg
  obtain ⟨e, hde⟩ := D_always_moves d hq
  have hE := D_zero_enters_E hde hq hb
  obtain ⟨a, hea⟩ := E_always_moves e hE
  have h3 : ((next d).bind fun e => (next e).bind next) = none :=
    (D_stop_after_two_moves d hq hb).mpr ⟨hleft1,hleft2⟩
  have ha : next a = none := by simpa [hde, hea] using h3
  exact ⟨a, Reach.follow (Reach.follow hd hde) hea, ha⟩

/-- Blank-root halting iff an actual D/0 section has 11 immediately to its left. -/
theorem blank_halts_iff_gate :
    (∃ c, Reach c ∧ next c = none) ↔ (∃ d, Reach d ∧ Gate d) := by
  constructor
  · rintro ⟨c, hc, hn⟩
    exact reached_stop_has_gate c hc hn
  · rintro ⟨d, hd, hg⟩
    exact reached_gate_has_stop d hd hg

#print axioms BB6Root119.blank_halts_iff_gate
end BB6Root119
