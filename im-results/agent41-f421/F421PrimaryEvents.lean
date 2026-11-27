import TertiaryGuard

namespace F421PrimaryEvents
open F421TertiaryGuard

/-- A-input cells are far-to-near, (old Q, previous farther P minus 1).
    The first Q parameter is a dummy, and the last full input row is
    the leading-B ghost. The two drains keep this orientation. -/
def remark (xs : List Cell) : List Cell := xs.map fun c => ⟨c.p-1,c.q⟩
def shift (s : Nat) : List Cell → List Cell
  | [] => []
  | c::cs => ⟨c.p-1+s,c.q-s⟩ :: shift (2*s) cs

def resetFar : List Cell → List Cell
  | [] => []
  | c::cs => ⟨c.p,3⟩::cs

def core (xs : List Cell) : List Cell :=
  resetFar (shift 1 (drain 0 0 (remark (drain 0 0 xs).1)).1)

def step (a : Nat) (xs : List Cell) : Nat × List Cell :=
  let (as,A,rA) := drain 0 0 xs
  let (bs,B,rB) := drain 0 0 (remark as)
  let N := 2^bs.length
  (2*N-1,resetFar (shift 1 bs) ++ [⟨N+3+2*(A+B),a+2+A+B+rA+rB-N⟩])

theorem drainAppend (xs ys : List Cell) (h r : Nat) :
    drain h r (xs++ys) =
    let (as,A,R) := drain h r xs
    let (bs,B,S) := drain A R ys
    (as++bs,B,S) := by
  induction xs generalizing h r with
  | nil => simp [drain]
  | cons c cs ih =>
    by_cases hd : c.p≤2*h+1
    · simp [drain,hd,ih]
    · simp only [List.cons_append,drain,ite_eq_right hd]
      rcases he : drain (2*h+1) 0 cs with ⟨as,A,R⟩
      rcases hf : drain A R ys with ⟨bs,B,S⟩
      rw [ih,he]
      simp [hf]

theorem shiftAppend (xs ys : List Cell) (s : Nat) :
    shift s (xs++ys)=shift s xs++shift (s*2^xs.length) ys := by
  induction xs generalizing s with
  | nil => simp [shift]
  | cons c cs ih =>
    simp only [List.cons_append,shift,ih,List.length_cons,Nat.pow_succ]
    congr 2
    ac_rfl

theorem resetPrefix (xs ys : List Cell) : ∃ zs, resetFar (xs++ys)=resetFar xs++zs := by
  cases xs with
  | nil => exact ⟨_,rfl⟩
  | cons c cs => exact ⟨ys,rfl⟩

theorem corePrefix (xs ys : List Cell) : ∃ zs, core (xs++ys)=core xs++zs := by
  unfold core
  rw [drainAppend]
  rcases he : drain 0 0 xs with ⟨as,A,R⟩
  rcases hf : drain A R ys with ⟨bs,B,S⟩
  simp only [hf,remark,List.map_append]
  rw [drainAppend]
  rcases hg : drain 0 0 (List.map (fun c : Cell => ⟨c.p-1,c.q⟩) as) with ⟨cs,C,T⟩
  rcases hh : drain C T (List.map (fun c : Cell => ⟨c.p-1,c.q⟩) bs) with ⟨ds,D,U⟩
  simp only [hh]
  rw [shiftAppend]
  exact resetPrefix _ _

theorem stepCore (xs : List Cell) (a : Nat) : ∃ c, (step a xs).2=core xs++[c] := by
  unfold step core
  rcases he : drain 0 0 xs with ⟨as,A,R⟩
  rcases hf : drain 0 0 (remark as) with ⟨bs,B,S⟩
  simp only [hf]
  exact ⟨_,rfl⟩

theorem stepPrefix (xs ys : List Cell) (a : Nat) : ∃ zs, (step a (xs++ys)).2=core xs++zs := by
  obtain ⟨c,hc⟩ := stepCore (xs++ys) a
  obtain ⟨zs,hz⟩ := corePrefix xs ys
  exact ⟨zs++[c],by rw [hc,hz,List.append_assoc]⟩

def enough (d s : Nat) : List Cell → Prop
  | [] => True
  | c::cs => d*s≤c.p ∧ enough d (2*s) cs

def drainAffine (s : Nat) : List Cell → List Cell
  | [] => []
  | c::cs => ⟨c.p-(2*s-1),c.q+s⟩::drainAffine (2*s) cs

theorem drainAffineCorrect (xs : List Cell) (s : Nat) (hs : 1≤s) (hx : enough 2 s xs) :
    (drain (s-1) 0 xs).1=drainAffine s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rcases hx with ⟨hp,ht⟩
    have hd : ¬c.p≤2*(s-1)+1 := by omega
    have he : 2*(s-1)+1=2*s-1 := by omega
    simp only [drain,he,ite_eq_right (by omega : ¬c.p≤2*s-1),drainAffine]
    rcases hh : drain (2*s-1) 0 cs with ⟨as,A,R⟩
    have H := ih (2*s) (by omega) ht
    rw [hh] at H
    simp only at H
    rw [H]
    congr 2 <;> omega

theorem remarkEnough (xs : List Cell) (s : Nat) (hs : 1≤s) (hx : enough 4 s xs) :
    enough 2 s (remark (drainAffine s xs)) := by
  induction xs generalizing s with
  | nil => trivial
  | cons c cs ih =>
    rcases hx with ⟨hp,ht⟩
    change 2*s≤c.p-(2*s-1)-1 ∧ enough 2 (2*s) (remark (drainAffine (2*s) cs))
    exact ⟨by omega, ih (2*s) (by omega) ht⟩

theorem enoughMono (xs : List Cell) (d e s : Nat) (h : d≤e) (hx : enough e s xs) : enough d s xs := by
  induction xs generalizing s with
  | nil => trivial
  | cons c cs ih => exact ⟨Nat.le_trans (Nat.mul_le_mul_right s h) hx.1, ih _ hx.2⟩

def affine (k s : Nat) : List Cell → List Cell
  | [] => []
  | c::cs => ⟨c.p-3*k*s,c.q+k*s⟩::affine k (2*s) cs

theorem twoDrains (xs : List Cell) (s : Nat) (hs : 1≤s) (hx : enough 4 s xs) :
    shift s (drainAffine s (remark (drainAffine s xs)))=affine 1 s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rcases hx with ⟨hp,ht⟩
    simp only [drainAffine,remark,List.map_cons,shift,affine,Nat.mul_one,Nat.one_mul]
    change (⟨c.p-(2*s-1)-1-(2*s-1)-1+s,c.q+s+s-s⟩ : Cell)::shift (2*s) (drainAffine (2*s) (remark (drainAffine (2*s) cs))) =
      ⟨c.p-3*s,c.q+s⟩::affine 1 (2*s) cs
    rw [ih (2*s) (by omega) ht]
    congr 2 <;> omega

theorem coreAffine (xs : List Cell) (hx : enough 4 1 xs) : core xs=resetFar (affine 1 1 xs) := by
  unfold core
  rw [show (drain 0 0 xs).1=drainAffine 1 xs from drainAffineCorrect xs 1 (by decide) (enoughMono xs 2 4 1 (by decide) hx)]
  rw [show (drain 0 0 (remark (drainAffine 1 xs))).1=drainAffine 1 (remark (drainAffine 1 xs)) from drainAffineCorrect _ 1 (by decide) (remarkEnough xs 1 (by decide) hx)]
  rw [twoDrains xs 1 (by decide) hx]

theorem enoughReset (xs : List Cell) (d s : Nat) : enough d s (resetFar xs) ↔ enough d s xs := by cases xs <;> rfl

theorem enoughAffine (xs : List Cell) (d k s : Nat) (hx : enough (d+3*k) s xs) : enough d s (affine k s xs) := by
  induction xs generalizing s with
  | nil => trivial
  | cons c cs ih =>
    rcases hx with ⟨hp,ht⟩
    constructor
    · change d*s≤c.p-3*k*s
      rw [Nat.add_mul] at hp
      omega
    · exact ih _ ht

theorem affineAdd (xs : List Cell) (k l s : Nat) : affine k s (affine l s xs)=affine (k+l) s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [affine,ih]
    have e : 3*(k+l)*s = 3*k*s + 3*l*s := by simp [Nat.mul_add,Nat.add_mul]
    congr 2
    · rw [e]; omega
    · rw [Nat.add_mul]; omega

theorem affineReset (xs : List Cell) (k s : Nat) : resetFar (affine k s (resetFar xs))=resetFar (affine k s xs) := by cases xs <;> rfl

def iterate (k : Nat) (xs : List Cell) : List Cell :=
  match k with | 0 => xs | k+1 => iterate k (core xs)

def birthIterate (k a : Nat) (xs : List Cell) : List Cell :=
  match k with | 0 => xs | k+1 => let (a',xs') := step a xs; birthIterate k a' xs'

theorem iterPrefix (k a : Nat) (xs ys : List Cell) : ∃ zs, birthIterate k a (xs++ys)=iterate k xs++zs := by
  induction k generalizing a xs ys with
  | zero => exact ⟨ys,rfl⟩
  | succ k ih =>
    obtain ⟨zs,hz⟩ := stepPrefix xs ys a
    rcases he : step a (xs++ys) with ⟨a',vs⟩
    rw [he] at hz
    simp only at hz
    simp only [birthIterate,he,iterate,hz]
    exact ih a' (core xs) zs

theorem affineZero (xs : List Cell) (s : Nat) : affine 0 s xs=xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [affine,ih]

theorem iterateAffine (k : Nat) (xs : List Cell) (hx : enough (3*k+1) 1 xs) :
    resetFar (iterate k xs)=resetFar (affine k 1 xs) := by
  induction k generalizing xs with
  | zero => simp [iterate,affineZero]
  | succ k ih =>
    have h4 := enoughMono xs 4 (3*(k+1)+1) 1 (by omega) hx
    have hg := enoughAffine xs (3*k+1) 1 1 (by simpa [show 3*k+1+3*1=3*(k+1)+1 by omega] using hx)
    have hg' : enough (3*k+1) 1 (core xs) := by rw [coreAffine xs h4,enoughReset]; exact hg
    simp only [iterate]
    rw [ih _ hg',coreAffine xs h4,affineReset,affineAdd]

#print axioms iterPrefix
#print axioms iterateAffine
end F421PrimaryEvents
