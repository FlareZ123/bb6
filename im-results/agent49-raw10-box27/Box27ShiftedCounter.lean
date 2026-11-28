import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27ShiftedCounter
open BB6Coverage BB6Coverage.Agent31Pump

/-- A binary odometer with digits 000 and 001, with F0=1RA and E1=0LE.
    A1 and F1 are never queried, giving 25 arbitrary completions. -/
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,true,5⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some ⟨false,false,4⟩)
  | (5,false) => some (some ⟨true,true,0⟩)
  | _ => none

def encode : List Bool → List Bool
  | [] => []
  | x::ds => false::false::x::encode ds

theorem encode_append (xs ys : List Bool) : encode (xs++ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons b ds ih => simp [encode,ih]

def front (ds : List Bool) (R : List Bool) : Z0 :=
  ⟨4,[false,false],encode ds ++ R⟩
def carry (L : List Bool) (b : Bool) (R : List Bool) : Z0 :=
  ⟨5,false::true::true::true::L,false::b::R⟩

theorem zeroLow (L R : List Bool) :
    run0 table 6 ⟨4,false::L,false::false::false::R⟩ =
    some ⟨4,false::L,false::false::true::R⟩ := by rfl

theorem enter (L R : List Bool) (b : Bool) :
    run0 table 4 ⟨4,false::L,false::false::true::false::false::b::R⟩ =
    some (carry (false::L) b R) := by rfl

theorem carry_zero (L R : List Bool) :
    run0 table 8 (carry L false R) =
    some ⟨4,L,false::false::false::false::false::true::R⟩ := by rfl

theorem carry_more (L R : List Bool) (b : Bool) :
    run0 table 3 (carry L true (false::false::b::R)) =
    some (carry (true::true::true::L) b R) := by rfl

theorem unwind (L R : List Bool) :
    run0 table 3 ⟨4,true::true::true::L,R⟩ =
    some ⟨4,L,false::false::false::R⟩ := by rfl

/-- Each carry into a finite digit stack containing one reserved zero terminates. -/
theorem carry_return (ds : List Bool) (L R : List Bool) (b : Bool) :
    ∃ t ds', 0 < t ∧ run0 table t
      (carry L b (encode ds ++ false::false::false::R)) =
      some ⟨4,L,encode ds' ++ R⟩ := by
  induction ds generalizing L b with
  | nil =>
    cases b with
    | false =>
      exact ⟨8,[false,true,false],by decide,by simpa only [encode,List.nil_append,List.cons_append,List.append_assoc] using carry_zero L (false::false::false::R)⟩
    | true =>
      have h1 := carry_more L R false
      have h2 := carry_zero (true::true::true::L) R
      have h3 := unwind L (false::false::false::false::false::true::R)
      exact ⟨14,[false,false,true],by decide,join0 (join0 h1 h2) h3⟩
  | cons a ds ih =>
    cases b with
    | false =>
      exact ⟨8,[false,true]++(a::ds)++[false],by decide,
        by simpa only [encode,encode_append,List.cons_append,List.append_assoc,List.nil_append] using carry_zero L (encode (a::ds) ++ false::false::false::R)⟩
    | true =>
      have h1 := carry_more L (encode ds ++ false::false::false::R) a
      obtain ⟨t,ds',ht,h2⟩ := ih (true::true::true::L) a
      have h3 := unwind L (encode ds' ++ R)
      exact ⟨3+t+3,false::ds',by omega,join0 (join0 h1 h2) h3⟩

/-- One positive-cost increment consumes at most one reserved zero triplet. -/
theorem next (ds : List Bool) (R : List Bool) :
    ∃ t ds', 0 < t ∧ run0 table t (front ds (false::false::false::R)) =
      some (front ds' R) := by
  cases ds with
  | nil =>
    exact ⟨6,[true],by decide,by simpa only [front,encode,List.nil_append,List.cons_append,List.append_assoc] using zeroLow [false] R⟩
  | cons a ds =>
    cases a with
    | false =>
      refine ⟨6,true::ds++[false],by decide,?_⟩
      simpa only [front,encode,encode_append,List.cons_append,List.nil_append,List.append_assoc] using zeroLow [false] (encode ds++false::false::false::R)
    | true =>
      cases ds with
      | nil =>
        have h1 := enter [false] R false
        have h2 := carry_zero [false,false] R
        exact ⟨12,[false,true],by decide,join0 h1 h2⟩
      | cons x xs =>
        have h1 := enter [false] (encode xs ++ false::false::false::R) x
        obtain ⟨t,ds',ht,h2⟩ := carry_return xs [false,false] R x
        exact ⟨4+t,ds',by omega,join0 h1 h2⟩

def zeros (n : Nat) : List Bool := List.replicate n false

theorem epochs (N : Nat) (ds : List Bool) :
    ∃ t z, N ≤ t ∧ run0 table t (front ds (zeros (3*N))) = some z := by
  induction N generalizing ds with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hp : zeros (3*(N+1)) = false::false::false::zeros (3*N) := by
      rw [show 3*(N+1)=3*N+3 by omega]; rfl
    obtain ⟨a,ds',ha,h1⟩ := next ds (zeros (3*N))
    obtain ⟨c,z,hc,h2⟩ := ih ds'
    exact ⟨a+c,z,by omega,by rw [hp]; exact join0 h1 h2⟩

theorem entry (R : List Bool) :
    run0 table 6 ⟨0,[],false::R⟩ = some (front [] (false::R)) := by rfl

theorem padded_live (N : Nat) :
    ∃ t z, N ≤ t ∧ run0 table t ⟨0,[],false::zeros (3*N+2)⟩ = some z := by
  obtain ⟨t,z,ht,h⟩ := epochs (N+1) []
  have hp : zeros (3*(N+1)) = false::zeros (3*N+2) := by
    rw [show 3*(N+1)=(3*N+2)+1 by omega]; rfl
  have h1 : run0 table 6 ⟨0,[],false::zeros (3*N+2)⟩ =
      some (front [] (zeros (3*(N+1)))) := by
    rw [hp]; exact entry (zeros (3*N+2))
  exact ⟨6+t,z,by omega,join0 h1 h⟩

#print axioms carry_return
#print axioms padded_live

open BB6Coverage.Agent50Zipper

private theorem getD_zeros (k i : Nat) : (zeros k).getD i false = false := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem padded_blank (k : Nat) : embed ⟨0,0,[],zeros k⟩ = blank := by
  unfold embed blank
  congr 1
  funext x
  unfold atCell
  split <;> simp only [List.getD_nil,getD_zeros]

/-- All completions of either one-hole table are nonhalting. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live n
  let start : Z := ⟨0,0,[],false::zeros (3*n+2)⟩
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    have hb : embed start = blank := by
      change embed ⟨0,0,[],zeros (3*n+3)⟩ = blank
      exact padded_blank _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent49.Box27ShiftedCounter
