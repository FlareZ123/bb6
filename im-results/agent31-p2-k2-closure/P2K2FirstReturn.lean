import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import P2K2Shapes
import E110111First
import ACodeFirstReturn
import A1101010111CodeFirst
import BoundaryPadding

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent31P2K2First

open CryptidBoundary
open BB6.Agent31PacketSource
open BB6.Agent2PacketP2Reset
open BB6.Agent31P2K2
open BB6.Agent35
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidACodeFirstReturn

/-- A physical first return is F scanning zero with no marked cell to its left. -/
def PhysicalF0 (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ c.l.any id = false

/-- Strict positive-time exclusion, allowing the starting section itself to be F/0. -/
def NoLaterPhysicalF0 (c : Cfg) (n : Nat) : Prop :=
  ∀ t, 0 < t → t < n → ¬ PhysicalF0 (run t c)

/-- No state-F visit at positive time. This is stronger than no physical F/0 return. -/
def NoLaterF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, 0 < t → t < n → (run t c).st ≠ 5

private theorem anyFalse_allNot (xs : List Bool) :
    xs.any id = false ↔ xs.all (!·) = true := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [ih]

private theorem allNot_memFalse (xs : List Bool) :
    xs.all (!·) = true ↔ ∀ b, b ∈ xs → b = false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [ih]

private theorem physicalA_of_physicalF0 {c : Cfg}
    (h : PhysicalF0 c) : CryptidBoundary.Physical c := by
  rcases h with ⟨hs, _hh, hl⟩
  exact ⟨hs, (allNot_memFalse c.l).mp ((anyFalse_allNot c.l).mp hl)⟩

/-- The exact E,p=2 reset is not merely a designated endpoint: it is the
    first positive physical F/0 return of the original six-state machine. -/
theorem e_two_reset_first (k q : Nat) :
    run (eTwoTime k q)
      (packet (3*k+4) q 2 (false :: List.replicate 6 true)) =
        packet (8*k+5) 0 (2*q+6) marker ∧
    NoLaterPhysicalF0
      (packet (3*k+4) q 2 (false :: List.replicate 6 true))
      (eTwoTime k q) := by
  have hin := BB6.Agent2PacketP2Reset.e_two_input k q
  have hout := BB6.Agent2PacketP2Reset.e_two_output k q
  have h := BB6.Agent32E110111First.full_E_110111_first_return
    k q (List.replicate 3 true)
  constructor
  · rw [hin]
    change run (12*k*k+49*k+68+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false,true,true,true] ++ List.replicate 3 true)))) =
      packet (8*k+5) 0 (2*q+6) marker
    rw [h.1]
    exact hout
  · intro t hpos ht hp
    rw [hin] at hp
    exact h.2 t hpos (by simpa [eTwoTime] using ht) hp

/-- A source-certified mixed A-code return, with no state-F visit before
    the terminal F/0 section. -/
def aTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*(4*k+3+CryptidA.wordInc ws)+6))

def aStart (k : Nat) (ws ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ false :: ys))

def aEnd (k : Nat) (ws ys : List Bool) : Cfg :=
  ⟨[],false,
    List.replicate (2*(4*k+3+CryptidA.wordInc ws)+5) true ++ ys,5⟩

private theorem a_mixed_first (k : Nat) (ws ys : List Bool) :
    run (aTime k ws) (aStart k ws ys) = aEnd k ws ys ∧
    NoLaterF (aStart k ws ys) (aTime k ws) := by
  let pre := 12*k*k+41*k+32
  let close := CryptidA.wordCost (4*k+3) ws +
    (2*(4*k+3+CryptidA.wordInc ws)+6)
  have hprefix : run pre (aStart k ws ys) =
      aBoundary (4*k+3) (CryptidA.wordCode ws ++ false :: ys) := by
    change run pre
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ false :: ys))) = _
    rw [prefix_A]
    rfl
  have hclose := BB6.CryptidACodeFirstReturn.aCodeClose_first
    (4*k+3) ws ys
  constructor
  · change run (pre+close) (aStart k ws ys) = aEnd k ws ys
    rw [run_add,hprefix]
    simpa [aEnd,close] using hclose.1
  · intro t hpos ht
    by_cases hpre : t < pre
    · exact prefixA_positive_noF k
        (CryptidA.wordCode ws ++ false :: ys) t hpos hpre
    · have htime : t = pre+(t-pre) := by omega
      change (run t (aStart k ws ys)).st ≠ 5
      rw [htime,run_add,hprefix]
      exact hclose.2 (t-pre) (by omega)

/-- The 1101010111 A terminal has a genuine physical first-return guard;
    its interior F visits are excluded only after checking the left tape. -/
def aExceptionTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
      (2*(4*k+3+CryptidA.wordInc ws)+36))

def aExceptionStart (k : Nat) (ws : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ BB6.Agent26ACode.packet []))

def aExceptionEnd (k : Nat) (ws : List Bool) : Cfg :=
  ⟨[],false,
    List.replicate (2*(4*k+3+CryptidA.wordInc ws)+5) true ++
      BB6.Agent26ACode.tail [],5⟩

private theorem a_exception_first (k : Nat) (ws : List Bool) :
    run (aExceptionTime k ws) (aExceptionStart k ws) =
      aExceptionEnd k ws ∧
    NoLaterPhysicalF0 (aExceptionStart k ws) (aExceptionTime k ws) := by
  let pre := 12*k*k+41*k+32
  let m := 4*k+3
  let cost := CryptidA.wordCost m ws
  let m' := m+CryptidA.wordInc ws
  let terminal := 2*m'+36
  have hprefix : run pre (aExceptionStart k ws) =
      aBoundary m (CryptidA.wordCode ws ++ BB6.Agent26ACode.packet []) := by
    change run pre
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ BB6.Agent26ACode.packet []))) = _
    rw [prefix_A]
    rfl
  have hcode : run cost
      (aBoundary m (CryptidA.wordCode ws ++ BB6.Agent26ACode.packet [])) =
        aBoundary m' (BB6.Agent26ACode.packet []) := by
    rw [a_code_return]
    rfl
  have hterminal : run terminal
      (aBoundary m' (BB6.Agent26ACode.packet [])) =
        aExceptionEnd k ws := by
    simpa [aExceptionEnd,m',m,terminal] using
      (CryptidBoundary.a1101010111_run m' [])
  have hterminalNo : ∀ t, t < terminal →
      ¬ PhysicalF0 (run t (aBoundary m' (BB6.Agent26ACode.packet []))) := by
    intro t ht hp
    exact (CryptidBoundary.a1101010111_first_physical m' [] t
      (by simpa [terminal] using ht)) (physicalA_of_physicalF0 hp)
  constructor
  · change run (pre+(cost+terminal)) (aExceptionStart k ws) =
      aExceptionEnd k ws
    rw [run_add,hprefix,run_add,hcode]
    exact hterminal
  · intro t hpos ht hp
    by_cases hpre : t < pre
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ BB6.Agent26ACode.packet [])
        t hpos hpre) hp.1
    · have htime : t = pre+(t-pre) := by omega
      rw [htime,run_add,hprefix]
      by_cases hcodeTime : t-pre < cost
      · exact (original_word_noF m ws BB6.Agent26ACode.packet [])
          (t-pre) hcodeTime hp.1
      · have htime2 : t-pre = cost+(t-pre-cost) := by omega
        rw [htime2,run_add,hcode]
        exact hterminalNo (t-pre-cost) (by omega) hp

/-- Implicit far-right blank version of the mixed A first-return guard. -/
def aStartImplicit (k : Nat) (ws : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: CryptidA.wordCode ws)

private theorem a_mixed_implicit_noLaterF (k : Nat) (ws : List Bool) :
    NoLaterF (aStartImplicit k ws) (aTime k ws) := by
  let xs := List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws
  intro t hpos ht
  have hpad := BB6.BoundaryPadding.source_init_pad t 1 xs
  have hstate := hpad.2.2.2
  change (run t (init xs)).st =
    (run t (init (xs ++ List.replicate 1 false))).st at hstate
  have hNoF := (a_mixed_first k ws []).2 t hpos ht
  have hshape : init (xs ++ List.replicate 1 false) =
      aStart k ws [] := by
    simp [xs,aStart,List.append_assoc]
  have hNoF' :
      (run t (init (xs ++ List.replicate 1 false))).st ≠ 5 := by
    simpa only [hshape] using hNoF
  change (run t (aStartImplicit k ws)).st ≠ 5
  rw [hstate]
  exact hNoF'

private theorem sourceCode (ws : List Bool) :
    CryptidA.wordCode ws = BB6.Agent31P2K2.wordCode ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordCode,BB6.Agent31P2K2.wordCode,ih]

private theorem markerEq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker := by
  rfl

private theorem zero_tail (t u : Nat) :
    packet (8*(3*t+2)+5) 0 (2*(3*u)+6)
      BB6.Agent2PacketP2Reset.marker =
    aStart (8*t+6) (List.replicate (2*u+2) true)
      [true,false,true,false,true,true,true] := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := BB6.Agent31P2K2.residue_zero_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
    List.nil_append]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem one_tail (t u : Nat) :
    packet (8*(3*t+2)+5) 0 (2*(3*u+1)+6)
      BB6.Agent2PacketP2Reset.marker =
    aExceptionStart (8*t+6) (List.replicate (2*u+2) true) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := BB6.Agent31P2K2.residue_one_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
    List.nil_append,BB6.Agent26ACode.packet,List.append_nil]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem two_tail (t u : Nat) :
    packet (8*(3*t+2)+5) 0 (2*(3*u+2)+6)
      BB6.Agent2PacketP2Reset.marker =
    aStartImplicit (8*t+6)
      (List.replicate (2*u+3) true ++ [false,false,false,true]) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := BB6.Agent31P2K2.residue_two_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
    List.nil_append]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem start_eq (t : Nat) :
    9*t+10 = 3*(3*t+2)+4 := by omega

/-- For k=3t+2 and q=3u, both consecutive F/0 sections are
    first returns, with exact original primitive times. -/
theorem two_return_zero_first_pair (t u : Nat) :
    let k := 3*t+2
    let q := 3*u
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let eT := eTwoTime k q
    let aT := aTime ka ws
    let start := packet (9*t+10) q 2 (false :: List.replicate 6 true)
    let mid := packet (8*k+5) 0 (2*q+6) BB6.Agent2PacketP2Reset.marker
    let final := aEnd ka ws [true,false,true,false,true,true,true]
    run eT start = mid ∧
    (∀ r, 0 < r → r < eT → ¬ PhysicalF0 (run r start)) ∧
    run aT mid = final ∧
    (∀ r, 0 < r → r < aT → ¬ PhysicalF0 (run r mid)) := by
  dsimp only
  have hE := e_two_reset_first (3*t+2) (3*u)
  have hA := a_mixed_first (8*t+6)
    (List.replicate (2*u+2) true)
    [true,false,true,false,true,true,true]
  have hshape := zero_tail t u
  have hs : 9*t+10 = 3*(3*t+2)+4 := by omega
  constructor
  · rw [hs]
    exact hE.1
  constructor
  · intro r hpos hlt hp
    rw [hs] at hp
    exact hE.2 r hpos (by simpa [eTwoTime] using hlt) hp
  constructor
  · rw [hshape]
    exact hA.1
  · intro r hpos hlt hp
    rw [hshape] at hp
    exact (hA.2 r hpos hlt) hp.1

/-- For k=3t+2 and q=3u+1, the exceptional A terminal also has a
    strict physical first-return guard, so the two-step composition is
    certified as two consecutive first returns. -/
theorem two_return_one_first_pair (t u : Nat) :
    let k := 3*t+2
    let q := 3*u+1
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let eT := eTwoTime k q
    let aT := aExceptionTime ka ws
    let start := packet (9*t+10) q 2 (false :: List.replicate 6 true)
    let mid := packet (8*k+5) 0 (2*q+6) BB6.Agent2PacketP2Reset.marker
    let final := aExceptionEnd ka ws
    run eT start = mid ∧
    (∀ r, 0 < r → r < eT → ¬ PhysicalF0 (run r start)) ∧
    run aT mid = final ∧
    (∀ r, 0 < r → r < aT → ¬ PhysicalF0 (run r mid)) := by
  dsimp only
  have hE := e_two_reset_first (3*t+2) (3*u+1)
  have hA := a_exception_first (8*t+6) (List.replicate (2*u+2) true)
  have hshape := one_tail t u
  have hs : 9*t+10 = 3*(3*t+2)+4 := by omega
  constructor
  · rw [hs]
    exact hE.1
  constructor
  · intro r hpos hlt hp
    rw [hs] at hp
    exact hE.2 r hpos (by simpa [eTwoTime] using hlt) hp
  constructor
  · rw [hshape]
    exact hA.1
  · intro r hpos hlt hp
    rw [hshape] at hp
    exact hA.2 r hpos hlt hp

/-- For k=3t+2 and q=3u+2, the final A code has an implicit far-right
    blank. The padding bisimulation preserves both the endpoint and the
    strict no-earlier-F0 property. -/
theorem two_return_two_first_pair (t u : Nat) :
    let k := 3*t+2
    let q := 3*u+2
    let ka := 8*t+6
    let ws := List.replicate (2*u+3) true ++ [false,false,false,true]
    let eT := eTwoTime k q
    let aT := aTime ka ws
    let start := packet (9*t+10) q 2 (false :: List.replicate 6 true)
    let mid := packet (8*k+5) 0 (2*q+6) BB6.Agent2PacketP2Reset.marker
    let final : Cfg :=
      ⟨[],false,List.replicate
        (2*(4*ka+3+CryptidA.wordInc ws)+5) true,5⟩
    run eT start = mid ∧
    (∀ r, 0 < r → r < eT → ¬ PhysicalF0 (run r start)) ∧
    ObsEq (run aT mid) final ∧
    (∀ r, 0 < r → r < aT → ¬ PhysicalF0 (run r mid)) := by
  dsimp only
  have hE := e_two_reset_first (3*t+2) (3*u+2)
  let ws : List Bool := List.replicate (2*u+3) true ++ [false,false,false,true]
  let xs : List Bool :=
    List.replicate (3*(8*t+6)+1) true ++ false :: CryptidA.wordCode ws
  have hA := a_mixed_first (8*t+6) ws []
  have hANo := a_mixed_implicit_noLaterF (8*t+6) ws
  have hshape := two_tail t u
  have hs : 9*t+10 = 3*(3*t+2)+4 := by omega
  constructor
  · rw [hs]
    exact hE.1
  constructor
  · intro r hpos hlt hp
    rw [hs] at hp
    exact hE.2 r hpos (by simpa [eTwoTime] using hlt) hp
  constructor
  · rw [hshape]
    have hpad := BB6.BoundaryPadding.source_init_pad (aTime (8*t+6) ws) 1 xs
    have hpadShape : init (xs ++ List.replicate 1 false) =
        aStart (8*t+6) ws [] := by
      simp [xs,aStart,List.append_assoc]
    rw [hpadShape,hA.1] at hpad
    exact hpad
  · intro r hpos hlt hp
    rw [hshape] at hp
    exact (hANo r hpos hlt) hp.1

#print axioms e_two_reset_first
#print axioms a_mixed_first
#print axioms a_exception_first
#print axioms two_return_zero_first_pair
#print axioms two_return_one_first_pair
#print axioms two_return_two_first_pair

end BB6.Agent31P2K2First
