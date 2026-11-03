import Lean.Elab.Tactic.Omega
import AZeroSource

set_option maxHeartbeats 5000000
namespace BB6.EZeroSource
open CryptidBoundary
open BB6.BoundaryPadding

def eEmpty (m : Nat) : Cfg :=
  ⟨false::false::pairs m ++ [true,true],false,[],4⟩

/-- The first twelve source steps strip two E-stack pair blocks, exposing
    the original B-state sweep with its six-one right packet. -/
theorem e_empty_front (m : Nat) :
    run 12 (eEmpty (m+2)) = preB m (false::List.replicate 6 true) := by
  simp [run,step,goL,goR,eEmpty,preB,pairs]

theorem e_empty_close (m : Nat) :
    run (2*m+15) (eEmpty (m+2)) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate 6 true),5⟩ := by
  have ht : 2*m+15=12+(2*m+3) := by omega
  rw [ht,run_add,e_empty_front,preB_run]

/-- Explicit terminal zero is valid for the original source; its runtime
    equals the modeled pure-unary E return, with the characteristic 0 1^6 tail. -/
theorem full_E_zero_explicit (k : Nat) :
    run (12*k*k+49*k+50)
      (init (List.replicate (3*k+2) true ++ [false])) =
      ⟨[],false,List.replicate (8*k+5) true ++
        (false::List.replicate 6 true),5⟩ := by
  have ht : 12*k*k+49*k+50 =
      (12*k*k+41*k+33)+(2*(4*k+1)+15) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k+1)+15) (eEmpty ((4*k+1)+2)) = _
  rw [e_empty_close]
  have hn : 2*(4*k+1)+3=8*k+5 := by omega
  rw [hn]

private theorem zero_start (k : Nat) :
    DRegularSource.sourceSection ⟨3*k+4,0,0⟩ =
    init (List.replicate (3*k+2) true) := by
  have hn : (3*k+4)-2=3*k+2 := by omega
  simp [DRegularSource.sourceSection,hn,oppairs]

private theorem zero_end (k : Nat) :
    DRegularSource.sourceSection ⟨8*k+5,1,5⟩ =
    (⟨[],false,List.replicate (8*k+5) true ++
      (false::List.replicate 6 true),5⟩ : Cfg) := by
  have hn : (8*k+5)-2=8*k+3 := by omega
  simp only [DRegularSource.sourceSection,init,oppairs,List.replicate_succ,
    List.replicate_zero,List.nil_append,List.append_nil,hn]
  -- Normalize both leading original 'init' bits and the one alternating pair.
  simp [List.append_assoc]

private theorem zero_duration (k : Nat) :
    DRegular.duration ⟨3*k+4,0,0⟩ = 12*k*k+49*k+50 := by
  have h2 : (3*k+4)%3 = 1 := by omega
  have hd : (3*k+4)/3-1=k := by omega
  simp [DRegular.duration,h2,hd]

private theorem zero_next (k : Nat) :
    DRegular.next ⟨3*k+4,0,0⟩ = some ⟨8*k+5,1,5⟩ := by
  have h2 : (3*k+4)%3 = 1 := by omega
  have hd : (3*k+4)/3-1=k := by omega
  simp [DRegular.next,h2,hd]

/-- Exact source transition including all implicit-blank initial tapes. -/
theorem e_zero_model (k : Nat) :
    ObsEq
      (run (DRegular.duration ⟨3*k+4,0,0⟩)
        (DRegularSource.sourceSection ⟨3*k+4,0,0⟩))
      (DRegularSource.sourceSection ⟨8*k+5,1,5⟩) := by
  rw [zero_start,zero_duration,zero_end]
  let n := 12*k*k+49*k+50
  have hp := source_init_pad n 1 (List.replicate (3*k+2) true)
  have hexact := full_E_zero_explicit k
  simp only [List.replicate_one] at hp
  change ObsEq (run n (init (List.replicate (3*k+2) true)))
      (run n (init (List.replicate (3*k+2) true ++ [false]))) at hp
  rw [hexact] at hp
  exact hp

/-- Complete original-source canonical E row with no explicit alternating pair. -/
theorem original_E_zero_row (s t : DRegular.L)
    (hc : DRegular.Canon s) (ha : s.a % 3 = 1)
    (hq : s.q = 0) (hn : DRegular.next s = some t) :
    ObsEq (run (DRegular.duration s)
      (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) := by
  obtain ⟨a,q,b⟩ := s
  change a % 3 = 1 at ha
  change q = 0 at hq
  rcases hc with ⟨ha2,hcanon⟩
  subst q
  have hb : b=0 := by
    cases hcanon with
    | inl h => exact False.elim (h rfl)
    | inr h => exact h
  subst b
  have hnum : a=3*((a/3)-1)+4 := by
    have haa : a ≥ 2 := by simpa using ha2
    have hquot : a/3 ≥ 1 := by omega
    omega
  rw [hnum] at hn ⊢
  rw [zero_next] at hn
  cases hn
  exact e_zero_model (a/3-1)

#print axioms full_E_zero_explicit
#print axioms e_zero_model
#print axioms original_E_zero_row
end BB6.EZeroSource
