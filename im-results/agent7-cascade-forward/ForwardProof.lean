import ForwardGeneric
import ResetChain
import ResetParentStrict
import FastShield

namespace CascadeForwardCert
open CascadeResetInverse
open CascadeManyShield

/-- Exact edge proof checker: every successful row is a genuine
    source-C first-return ResetParent edge, including any odd drain depth. -/
def stepOk (h : Nat) (e : Edge) : Bool :=
  if e.odd then
    let d := (2*e.u+5)/(3^(e.t+1))
    decide (d%2=1 ∧
      (6*2^e.k+1≤2^e.t*d ∧ 2^e.t*d≤8*2^e.k-1) ∧
      2*e.u+5=3^(e.t+1)*d ∧
      2*(2^e.t*d)=8*2^e.k+h+e.k+5)
  else decide ((6*2^e.k-1≤e.u ∧ e.u≤8*2^e.k-3) ∧
    2*e.u=8*2^e.k+h+e.k)

theorem stepOk_sound (h : Nat) (e : Edge) (ho : stepOk h e = true) :
    ResetParent h e.u := by
  by_cases he : e.odd = true
  · simp only [stepOk, he, ↓reduceIte] at ho
    let d := (2*e.u+5)/(3^(e.t+1))
    have hh : d%2=1 ∧
      (6*2^e.k+1≤2^e.t*d ∧ 2^e.t*d≤8*2^e.k-1) ∧
      2*e.u+5=3^(e.t+1)*d ∧
      2*(2^e.t*d)=8*2^e.k+h+e.k+5 := of_decide_eq_true ho
    exact Or.inr ⟨e.k,e.t,d,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2⟩
  · have he' : e.odd = false := by cases hb:e.odd <;> simp_all
    simp only [stepOk, he'] at ho
    have hh : (6*2^e.k-1≤e.u ∧ e.u≤8*2^e.k-3) ∧
      2*e.u=8*2^e.k+h+e.k := of_decide_eq_true ho
    exact Or.inl ⟨e.k,hh.1,hh.2⟩

/-- First-reset outcome determinism, derived from the original source-C
    outcome uniqueness theorem rather than assumed by the checker. -/
theorem parent_functional (h u v : Nat)
    (hu : ResetParent h u) (hv : ResetParent h v) : u = v := by
  have hru : Outcome (h,0) (some u) := (reset_parent_iff h u).mpr hu
  have hrv : Outcome (h,0) (some v) := (reset_parent_iff h v).mpr hv
  exact Option.some.inj (outcome_unique hru hrv)

private theorem embed_chain {s u : Nat} (hr : ResetChain s u) :
    Chain ResetParent s u := by
  induction hr with
  | root => exact Chain.root
  | append hr hp ih => exact Chain.append ih hp

def badHeight (N h : Nat) : Bool := CascadeFastShield.badFast N (h,0)

/-- A finite exact prefix ending above c_N and containing no surviving fatal
    height proves all-time nonreachability of every indexed c_n through N,
    with n%6 in {4,5}. The prefix is checked using first-reset semantics. -/
theorem certified_survivor_exclusion (N : Nat) (es : List Edge)
    (hc : check stepOk (badHeight N) (fatal N) 2 es = true)
    (n : Nat) (hn : 4 ≤ n) (hbound : n ≤ N)
    (hres : n%6=4 ∨ n%6=5) :
    ¬CascadeSweep.ReachC (2,0) (fatal n,0) := by
  intro hr
  have hb : badHeight N (fatal n)=true :=
    CascadeFastShield.badFast_hits N n hn hbound hres
  have hcap : fatal n ≤ fatal N := CascadeFastShield.fatal_mono n N hbound
  have hchain : Chain ResetParent 2 (fatal n) :=
    embed_chain ((root_reset_chain_iff (fatal n)).mp hr)
  exact check_sound reset_parent_strict parent_functional stepOk stepOk_sound
    (badHeight N) (fatal N) es 2 hc (fatal n) hchain hcap hb

#print axioms stepOk_sound
#print axioms parent_functional
#print axioms certified_survivor_exclusion

end CascadeForwardCert
