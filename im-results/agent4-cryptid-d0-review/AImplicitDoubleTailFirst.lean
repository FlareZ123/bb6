import Lean.Elab.Tactic.Omega
import A1100CodeFirst
import ELowCanonicalBlankFirst

/-!
# Original A-code double-one suffix with physically implicit zero padding

An arbitrary finite combination of 10/111 tokens followed by 11 and
then two implicit blanks is a strict FIRST physical F/0 return.
The existing explicit 1100 source boundary proof excludes the stronger
Physical predicate, and the observational TapeEq-empty predicate transports
that result through the original infinite blank-tape representation.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4AImplicitDouble

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Padding (TapeEq bitAt)
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidELowCanonicalFirst
open BB6.CryptidA1100CodeFirst

def implicitDouble (k : Nat) (ws : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ [true,true]))

/-- Observationally empty half-tape implies each of its finite cells
is physically zero. This is the quotient bridge for Physical. -/
theorem tapeEqEmpty_allZero (xs : List Bool)
    (heq : TapeEq xs []) : ∀ b, b∈xs → b=false := by
  induction xs with
  | nil =>
      intro b hmem
      cases hmem
  | cons x xs ih =>
      have hx : x=false := by
        simpa [bitAt] using (heq 0)
      have ht : TapeEq xs [] := by
        intro i
        simpa [bitAt] using (heq (i+1))
      intro b hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · exact hhead ▸ hx
      · exact ih ht b htail

theorem blankToPhysical (c : Cfg) (hb : BlankLeftF c) : Physical c := by
  exact ⟨hb.1, tapeEqEmpty_allZero c.l hb.2.2⟩

/-- Source padding with two trailing zero cells is observationally exact
for every primitive step, including all intermediate code visits. -/
theorem double_pad (k : Nat) (ws : List Bool) (t : Nat) :
    ObsEq (run t (implicitDouble k ws))
      (run t (codeStart k ws [])) := by
  let xs := List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ [true,true])
  have hp := source_init_pad t 2 xs
  have hrep : List.replicate 2 false = [false,false] := rfl
  rw [hrep] at hp
  have hx : init (xs ++ [false,false]) = codeStart k ws [] := by
    simp [xs,codeStart,packet,List.append_assoc]
  rw [hx] at hp
  simpa only [implicitDouble,xs] using hp

/-- The checked A1100CodeFirst source proof is in terms of Physical
rather than state F alone, since C/1 -> D/1 -> F internal visits occur. -/
theorem double_explicit_noBlank (k : Nat) (ws : List Bool) :
    ∀ t, 0<t → t<codeTime k ws →
      ¬BlankLeftF (run t (codeStart k ws [])) := by
  intro t htpos ht hblank
  by_cases hpref : t<12*k*k+41*k+32
  · exact (prefixA_positive_noF k
      (CryptidA.wordCode ws ++ packet [])
      t htpos hpref) hblank.1
  · have htime : t=(12*k*k+41*k+32)+
      (t-(12*k*k+41*k+32)) := by omega
    have hprefix : run (12*k*k+41*k+32) (codeStart k ws []) =
        BB6.Agent35.aBoundary (4*k+3)
          (CryptidA.wordCode ws ++ packet []) :=
      prefix_A k (CryptidA.wordCode ws ++ packet [])
    rw [htime,run_add,hprefix] at hblank
    have hrest : t-(12*k*k+41*k+32) <
        CryptidA.wordCost (4*k+3) ws+
          (2*(4*k+3+CryptidA.wordInc ws)+16) := by
      dsimp [codeTime] at ht
      omega
    exact (code_close_noPhysical k ws []
      (t-(12*k*k+41*k+32)) hrest)
      (blankToPhysical _ hblank)

/-- Physically implicit two blank cells must not create a spurious
earlier return, even if an interior F control state is visited. -/
theorem double_implicit_noBlank (k : Nat) (ws : List Bool) :
    ∀ t, 0<t → t<codeTime k ws →
      ¬BlankLeftF (run t (implicitDouble k ws)) := by
  intro t htpos ht hblank
  have hcode : BlankLeftF (run t (codeStart k ws [])) :=
    (blankLeftF_congr (double_pad k ws t)).mp hblank
  exact double_explicit_noBlank k ws t htpos ht hcode

/-- Fully unpadded all-code 11-ending source result with exact endpoint,
and no earlier physical F/0 in the infinite tape quotient. -/
theorem double_implicit_strict_first (k : Nat) (ws : List Bool) :
    ObsEq
      (run (codeTime k ws) (implicitDouble k ws))
      (⟨[],false,
        List.replicate (2*(4*k+3+CryptidA.wordInc ws)+1) true ++
          (false::List.replicate 6 true),5⟩ : Cfg) ∧
    ∀ t, 0<t → t<codeTime k ws →
      ¬BlankLeftF (run t (implicitDouble k ws)) := by
  constructor
  · have hp := double_pad k ws (codeTime k ws)
    have he : run (codeTime k ws) (codeStart k ws []) =
      (⟨[],false,
        List.replicate (2*(4*k+3+CryptidA.wordInc ws)+1) true ++
          (false::List.replicate 6 true),5⟩ : Cfg) := by
      simpa using (full_A_code_1100_first_return k ws []).1
    rw [he] at hp
    exact hp
  · exact double_implicit_noBlank k ws

#print axioms tapeEqEmpty_allZero
#print axioms double_implicit_noBlank
#print axioms double_implicit_strict_first

end BB6.Agent4AImplicitDouble
