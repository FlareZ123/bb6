import Lean.Elab.Tactic.Omega
import EZeroSource

set_option maxHeartbeats 7000000
namespace BB6.AOneSource
open CryptidBoundary
open BB6.BoundaryPadding

/-- Physical A boundary after an arbitrary input zero delimiter. -/
def ab (m : Nat) (ys : List Bool) : Cfg :=
  ⟨false::pairs m ++ [true,true],false,ys,0⟩

/-- 10 is a two-step A-boundary increment, preserving the unknown suffix. -/
theorem a_ten (m : Nat) (ys : List Bool) :
    run 2 (ab m (true::false::ys)) = ab (m+1) ys := by
  simp [ab,run,step,goL,goR,pairs,List.append_assoc]

/-- Consecutive 10 tokens commute with the exact source tape semantics. -/
theorem a_ten_run (m q : Nat) (ys : List Bool) :
    run (2*q) (ab m (pairs q ++ ys)) = ab (m+q) ys := by
  induction q generalizing m with
  | zero => simp [run,pairs]
  | succ q ih =>
    have ht : 2*(q+1)=2+2*q := by omega
    rw [ht,run_add]
    change run (2*q) (run 2 (ab m (true::false::(pairs q ++ ys)))) = _
    rw [a_ten,ih]
    have hn : (m+1)+q=m+(q+1) := by omega
    rw [hn]

/-- Source five-step close for the single-one tail and implicit right blank. -/
theorem a_one_front (m : Nat) :
    run 5 (ab m [true]) = sweepD (m+1) [true,true] := by
  simp [ab,sweepD,run,step,goL,goR,pairs,List.append_assoc]

theorem a_one_close (m : Nat) :
    run (2*m+10) (ab m [true]) =
      ⟨[],false,List.replicate (2*m+7) true,5⟩ := by
  have ht : 2*m+10=5+(2*(m+1)+3) := by omega
  rw [ht,run_add,a_one_front,sweepD_run]
  have hrep : List.replicate (2*(m+1)+3) true ++ [true,true] =
    List.replicate (2*m+7) true := by
    calc
      _ = List.replicate (2*(m+1)+3) true ++ List.replicate 2 true := rfl
      _ = List.replicate ((2*(m+1)+3)+2) true := List.replicate_append_replicate
      _ = _ := by congr 1
  rw [hrep]

theorem one_oppairs (q : Nat) :
    true :: oppairs q = pairs q ++ [true] := by
  induction q with
  | zero => rfl
  | succ q ih => simpa [oppairs,pairs] using congrArg (fun l => true::false::l) ih

/-- Unary regular A with arbitrary alternating pairs but no extra 1 tail. -/
theorem full_A_one (k q : Nat) :
    run (12*k*k+41*k+32+2*q+2*(4*k+3+q)+10)
      (init (List.replicate (3*k+1) true ++
        false :: (pairs q ++ [true]))) =
    ⟨[],false,List.replicate (8*k+13+2*q) true,5⟩ := by
  have ht : 12*k*k+41*k+32+2*q+2*(4*k+3+q)+10 =
      (12*k*k+41*k+32)+(2*q+(2*(4*k+3+q)+10)) := by omega
  rw [ht,run_add,prefix_A]
  change run (2*q+(2*(4*k+3+q)+10)) (ab (4*k+3) (pairs q ++ [true])) = _
  rw [run_add,a_ten_run,a_one_close]
  have hn : 2*(4*k+3+q)+7=8*k+13+2*q := by omega
  rw [hn]

/-- The first q>=1 A subfamily, retaining q-1 token increments. -/
theorem a_one_model (k q : Nat) :
    run (DRegular.duration ⟨3*k+3,q+1,0⟩)
      (DRegularSource.sourceSection ⟨3*k+3,q+1,0⟩) =
    DRegularSource.sourceSection ⟨8*k+13+2*q,0,0⟩ := by
  have ha : (3*k+3)%3=0 := by omega
  have hd : (3*k+3)/3-1=k := by omega
  have hb : (0+1)%3=1 := by decide
  have hq : q+1≠0 := by omega
  have hdur : DRegular.duration ⟨3*k+3,q+1,0⟩ =
      12*k*k+41*k+32+2*q+2*(4*k+3+q)+10 := by
    simp [DRegular.duration,ha,hd,hb]
  have hstart : DRegularSource.sourceSection ⟨3*k+3,q+1,0⟩ =
      init (List.replicate (3*k+1) true ++
        false :: (pairs q ++ [true])) := by
    have hn : (3*k+3)-2=3*k+1 := by omega
    simp only [DRegularSource.sourceSection,hn,List.replicate_zero,
      List.append_nil,oppairs]
    rw [one_oppairs q]
  have hout : DRegularSource.sourceSection ⟨8*k+13+2*q,0,0⟩ =
      (⟨[],false,List.replicate (8*k+13+2*q) true,5⟩ : Cfg) := by
    have hn : (8*k+13+2*q)-2 = 8*k+11+2*q := by omega
    simp only [DRegularSource.sourceSection,hn,oppairs,List.replicate_zero,
      List.nil_append,List.append_nil,init]
    have hrep : List.replicate (8*k+13+2*q) true =
      [true,true] ++ List.replicate (8*k+11+2*q) true := by
      calc
        _ = List.replicate (2+(8*k+11+2*q)) true := by congr 1; omega
        _ = List.replicate 2 true ++ List.replicate (8*k+11+2*q) true :=
          (List.replicate_append_replicate).symm
        _ = _ := rfl
    rw [hrep]
    rfl
  rw [hstart,hdur,full_A_one,hout]


private theorem one_next (k q : Nat) :
    DRegular.next ⟨3*k+3,q+1,0⟩ =
      some ⟨8*k+13+2*q,0,0⟩ := by
  have ha : (3*k+3)%3=0 := by omega
  have hd : (3*k+3)/3-1=k := by omega
  simp [DRegular.next,ha,hd]

/-- Entire q>=1, b=0 A subfamily of the original-source return contract. -/
theorem original_A_one_row (s t : DRegular.L)
    (hc : DRegular.Canon s) (ha : s.a % 3=0)
    (hq : s.q>0) (hb : s.b=0)
    (hn : DRegular.next s=some t) :
    ObsEq (run (DRegular.duration s)
      (DRegularSource.sourceSection s))
      (DRegularSource.sourceSection t) := by
  obtain ⟨a,q,b⟩ := s
  change a % 3=0 at ha
  change q>0 at hq
  change b=0 at hb
  subst b
  have haa : a≥2 := by simpa [DRegular.Canon] using hc.1
  have hnum : a=3*((a/3)-1)+3 := by
    have hquot : a/3 ≥ 1 := by omega
    omega
  rw [hnum] at hn ⊢
  cases q with
  | zero => omega
  | succ q =>
    rw [one_next] at hn
    cases hn
    rw [a_one_model]
    exact BB6.Padding.cfgEq_refl _

#print axioms original_A_one_row
#print axioms a_ten_run
#print axioms a_one_close
#print axioms full_A_one
#print axioms a_one_model
end BB6.AOneSource
