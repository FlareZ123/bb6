import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent49.Box27MaskedCounter3
open BB6Coverage BB6Coverage.Agent31Pump

/-- Three source transitions at E1: 0LC, 1LC, and 0LE. -/
inductive Variant where
  | e9 | e11 | e17

def extraBit : Variant → Bool
  | .e11 => true
  | _ => false

def table (v : Variant) : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (1,false) => some (some ⟨true,false,2⟩)
  | (1,true) => some (some ⟨true,true,5⟩)
  | (2,false) | (2,true) => some (some ⟨false,false,3⟩)
  | (3,false) => some (some ⟨false,true,3⟩)
  | (3,true) => some (some ⟨false,false,4⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some (match v with
      | .e9 => ⟨false,false,2⟩
      | .e11 => ⟨true,false,2⟩
      | .e17 => ⟨false,false,4⟩))
  | (5,false) => some (some ⟨true,false,4⟩)
  | (5,true) => some (some ⟨true,true,0⟩)
  | _ => none

abbrev Digit := Bool × Bool
abbrev zeroDigit : Digit := (false,false)
def encode : List Digit → List Bool
  | [] => []
  | (x,y)::ds => false::x::y::encode ds

def front (b : Bool) (ds : List Digit) (R : List Bool) : Z0 :=
  ⟨4,[false,false],b::(encode ds++R)⟩
def carry (L : List Bool) (x y : Bool) (R : List Bool) : Z0 :=
  ⟨1,x::true::true::L,y::R⟩

theorem encode_append (xs ys : List Digit) : encode (xs++ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons d ds ih => rcases d with ⟨x,y⟩; simp [encode,ih]

theorem zeroLow (v : Variant) (L R : List Bool) :
    run0 (table v) 2 ⟨4,false::L,false::R⟩ = some ⟨4,false::L,true::R⟩ := by cases v <;> rfl

theorem enter (v : Variant) (L R : List Bool) (x y : Bool) :
    run0 (table v) 3 ⟨4,false::L,true::false::x::y::R⟩ = some (carry (false::L) x y R) := by cases v <;> rfl

theorem unwind (v : Variant) (L R : List Bool) :
    run0 (table v) 3 ⟨4,true::true::true::L,R⟩ = some ⟨4,L,false::false::extraBit v::R⟩ := by cases v <;> rfl

theorem carry_zero (v : Variant) (L R : List Bool) (y : Bool) :
    run0 (table v) 3 (carry L false y R) = some ⟨4,L,false::false::true::y::R⟩ := by cases v <;> rfl

theorem carry_one (v : Variant) (L R : List Bool) :
    run0 (table v) 5 (carry L true false R) = some ⟨4,L,false::false::false::true::R⟩ := by cases v <;> rfl

theorem carry_more (v : Variant) (L R : List Bool) (x y : Bool) :
    run0 (table v) 3 (carry L true true (false::x::y::R)) = some (carry (true::true::true::L) x y R) := by cases v <;> rfl

/-- Carry with a reserved zero digit: each recursive call consumes one maximal
    digit, and the reserved zero guarantees a finite return. -/
theorem carry_return (v : Variant) (ds : List Digit) (L R : List Bool) (x y : Bool) :
    ∃ t ds', 0 < t ∧ run0 (table v) t
      (carry L x y (encode ds++false::false::false::R)) =
      some ⟨4,L,false::(encode ds'++R)⟩ := by
  induction ds generalizing L x y with
  | nil =>
    cases x <;> cases y
    · exact ⟨3,[(true,false),zeroDigit],by decide,carry_zero v L (false::false::false::R) false⟩
    · exact ⟨3,[(true,true),zeroDigit],by decide,carry_zero v L (false::false::false::R) true⟩
    · exact ⟨5,[(false,true),zeroDigit],by decide,carry_one v L (false::false::false::R)⟩
    · have h1 := carry_more v L R false false
      have h2 := carry_zero v (true::true::true::L) R false
      have h3 := unwind v L (false::false::true::false::R)
      exact ⟨9,[(false,extraBit v),(true,false)],by decide,join0 (join0 h1 h2) h3⟩
  | cons d ds ih =>
    rcases d with ⟨a,b⟩
    cases x <;> cases y
    · exact ⟨3,(true,false)::(a,b)::ds++[zeroDigit],by decide,by simpa only [encode,encode_append,List.cons_append,List.append_assoc,List.nil_append] using carry_zero v L (encode ((a,b)::ds)++false::false::false::R) false⟩
    · exact ⟨3,(true,true)::(a,b)::ds++[zeroDigit],by decide,by simpa only [encode,encode_append,List.cons_append,List.append_assoc,List.nil_append] using carry_zero v L (encode ((a,b)::ds)++false::false::false::R) true⟩
    · exact ⟨5,(false,true)::(a,b)::ds++[zeroDigit],by decide,by simpa only [encode,encode_append,List.cons_append,List.append_assoc,List.nil_append] using carry_one v L (encode ((a,b)::ds)++false::false::false::R)⟩
    · have h1 := carry_more v L (encode ds++false::false::false::R) a b
      obtain ⟨t,ds',ht,h2⟩ := ih (true::true::true::L) a b
      have h3 := unwind v L (false::(encode ds'++R))
      exact ⟨3+t+3,(false,extraBit v)::ds',by omega,join0 (join0 h1 h2) h3⟩

theorem next (v : Variant) (b : Bool) (ds : List Digit) (R : List Bool) :
    ∃ t b' ds', 0<t ∧ run0 (table v) t (front b ds (false::false::false::R)) =
      some (front b' ds' R) := by
  cases b with
  | false =>
    refine ⟨2,true,ds++[zeroDigit],by decide,?_⟩
    simpa only [front,encode_append,encode,List.cons_append,List.nil_append,List.append_assoc] using zeroLow v [false] (encode ds++false::false::false::R)
  | true =>
    cases ds with
    | nil =>
      exact ⟨6,false,[(true,false)],by decide,join0 (enter v [false] R false false) (carry_zero v [false,false] R false)⟩
    | cons d ds =>
      rcases d with ⟨x,y⟩
      have h1 := enter v [false] (encode ds++false::false::false::R) x y
      obtain ⟨t,ds',ht,h2⟩ := carry_return v ds [false,false] R x y
      exact ⟨3+t,false,ds',by omega,join0 h1 h2⟩

def zeros (n : Nat) : List Bool := List.replicate n false

theorem epochs (v : Variant) (N : Nat) (b : Bool) (ds : List Digit) :
    ∃ t z, N≤t ∧ run0 (table v) t (front b ds (zeros (3*N))) = some z := by
  induction N generalizing b ds with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hp : zeros (3*(N+1)) = false::false::false::zeros (3*N) := by
      rw [show 3*(N+1)=3*N+3 by omega]; rfl
    obtain ⟨a,b',ds',ha,h1⟩ := next v b ds (zeros (3*N))
    obtain ⟨c,z,hc,h2⟩ := ih b' ds'
    exact ⟨a+c,z,by omega,by rw [hp]; exact join0 h1 h2⟩

theorem entry (v : Variant) (R : List Bool) :
    run0 (table v) 6 ⟨0,[],false::R⟩ = some (front false [] R) := by cases v <;> rfl

theorem padded_live (v : Variant) (N : Nat) :
    ∃ t z, N≤t ∧ run0 (table v) t ⟨0,[],false::zeros (3*N)⟩ = some z := by
  obtain ⟨t,z,ht,h⟩ := epochs v N false []
  exact ⟨6+t,z,by omega,join0 (entry v (zeros (3*N))) h⟩

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
theorem never (v : Variant) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live v n
  let start : Z := ⟨0,0,[],false::zeros (3*n)⟩
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    have hb : embed start = blank := by
      change embed ⟨0,0,[],zeros (3*n+1)⟩ = blank
      exact padded_blank _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent49.Box27MaskedCounter
