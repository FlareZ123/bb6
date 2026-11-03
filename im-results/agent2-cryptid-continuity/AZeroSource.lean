import Lean.Elab.Tactic.Omega
import BRegularSource

set_option maxHeartbeats 5000000
namespace BB6.AZeroSource
open CryptidBoundary
open BB6.BoundaryPadding

def aEmpty (m : Nat) : Cfg :=
  ⟨false :: pairs m ++ [true,true], false, [], 0⟩

/-- An A boundary reading its implicit right-hand blank enters the D sweep. -/
theorem a_empty_three (m : Nat) :
    run 3 (aEmpty m) = sweepD m [true,true] := by
  simp [aEmpty, sweepD, CryptidBoundary.run, CryptidBoundary.step, goL, goR]

/-- Source-level finish for an A boundary with an implicit blank right tape. -/
theorem a_empty_close (m : Nat) :
    run (2*m+6) (aEmpty m) =
      ⟨[],false,List.replicate (2*m+5) true,5⟩ := by
  have ht : 2*m+6 = 3+(2*m+3) := by omega
  rw [ht, run_add, a_empty_three, sweepD_run]
  have hr : List.replicate (2*m+3) true ++ [true,true] =
      List.replicate (2*m+5) true := by
    calc
      _ = List.replicate (2*m+3) true ++ List.replicate 2 true := rfl
      _ = List.replicate ((2*m+3)+2) true := List.replicate_append_replicate
      _ = _ := by congr 1
  rw [hr]

/-- Genuine original six-state F/0 return, beginning with only 3k+3 ones. -/
theorem full_A_zero (k : Nat) :
    run (12*k*k+49*k+44)
      (init (List.replicate (3*k+1) true)) =
      ⟨[],false,List.replicate (8*k+11) true,5⟩ := by
  have ht : 12*k*k+49*k+44 =
      (12*k*k+41*k+32)+(2*(4*k+3)+6) := by omega
  rw [ht, run_add, prefix_A_nil]
  change run (2*(4*k+3)+6) (aEmpty (4*k+3)) = _
  rw [a_empty_close]
  have he : 2*(4*k+3)+5=8*k+11 := by omega
  rw [he]

private theorem zero_start (k : Nat) :
    DRegularSource.sourceSection ⟨3*k+3,0,0⟩ =
    init (List.replicate (3*k+1) true) := by
  have hn : (3*k+3)-2=3*k+1 := by omega
  simp [DRegularSource.sourceSection,hn,oppairs]

private theorem zero_end (k : Nat) :
    DRegularSource.sourceSection ⟨8*k+11,0,0⟩ =
    (⟨[],false,List.replicate (8*k+11) true,5⟩ : Cfg) := by
  have hn : (8*k+11)-2=8*k+9 := by omega
  simp only [DRegularSource.sourceSection, init, oppairs,
    List.replicate_zero, List.nil_append, List.append_nil, hn]
  have hrep : List.replicate (8*k+11) true =
    [true,true] ++ List.replicate (8*k+9) true := by
    calc
      _ = List.replicate (2+(8*k+9)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (8*k+9) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hrep]
  rfl

private theorem zero_duration (k : Nat) :
    DRegular.duration ⟨3*k+3,0,0⟩ = 12*k*k+49*k+44 := by
  have h2 : (3*k+3)%3=0 := by omega
  have hd : (3*k+3)/3-1=k := by omega
  simp [DRegular.duration,h2,hd]

private theorem zero_next (k : Nat) :
    DRegular.next ⟨3*k+3,0,0⟩ = some ⟨8*k+11,0,0⟩ := by
  have h2 : (3*k+3)%3=0 := by omega
  have hd : (3*k+3)/3-1=k := by omega
  simp [DRegular.next,h2,hd]

/-- The entire canonical zero-pair A row of the authenticated source contract. -/
theorem a_zero_model (k : Nat) :
    ObsEq
      (run (DRegular.duration ⟨3*k+3,0,0⟩)
        (DRegularSource.sourceSection ⟨3*k+3,0,0⟩))
      (DRegularSource.sourceSection ⟨8*k+11,0,0⟩) := by
  rw [zero_start,zero_duration,full_A_zero,zero_end]
  exact BB6.Padding.cfgEq_refl _

/-- Generic A residue q=0, with exact model successor and duration. -/
theorem original_A_zero_row (s t : DRegular.L)
    (hc : DRegular.Canon s) (ha : s.a % 3 = 0)
    (hq : s.q = 0) (hn : DRegular.next s = some t) :
    ObsEq
      (run (DRegular.duration s)
        (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) := by
  obtain ⟨a,q,b⟩ := s
  change a % 3 = 0 at ha
  change q = 0 at hq
  rcases hc with ⟨ha2,hcanon⟩
  subst q
  have hb : b=0 := by
    cases hcanon with
    | inl hn => exact False.elim (hn rfl)
    | inr hn => exact hn
  subst b
  have hnum : a=3*((a/3)-1)+3 := by
    have haa : a ≥ 2 := by simpa using ha2
    have hquot : a / 3 ≥ 1 := by omega
    omega
  rw [hnum] at hn ⊢
  rw [zero_next] at hn
  cases hn
  exact a_zero_model (a/3-1)

#print axioms full_A_zero
#print axioms a_zero_model
#print axioms original_A_zero_row
end BB6.AZeroSource
