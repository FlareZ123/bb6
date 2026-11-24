import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429AffinePump
set_option maxHeartbeats 5000000

/-- The successful branches; gap = w - 2*u. -/
inductive Tag where
  | F | R2 | R1 | R0 | E1 | Eeven | Eodd | O2 | Oeven1 | Oeven | Oodd
  deriving DecidableEq, Repr

def guard (t : Tag) (u w : Int) : Prop :=
  let g := w-2*u
  match t with
  | .F => 3 ≤ g
  | .R2 => g=2
  | .R1 => g=1
  | .R0 => g=0
  | .E1 => g= -2
  | .Eeven => g ≤ -4 ∧ g%4=0
  | .Eodd => g ≤ -6 ∧ g%4=2
  | .O2 => g= -3
  | .Oeven1 => g ≤ -7 ∧ g%4=1 ∧ w=1
  | .Oeven => g ≤ -7 ∧ g%4=1 ∧ 3 ≤ w
  | .Oodd => g ≤ -5 ∧ g%4=3

instance (t : Tag) (u w : Int) : Decidable (guard t u w) := by
  cases t <;> unfold guard <;> infer_instance

def out (t : Tag) (u w : Int) : Int × Int :=
  let d := u-w/2
  match t with
  | .F => (2*u+3,w-2*u-3)
  | .R2 => (0,4*u+18)
  | .R1 => (11,4*u+2)
  | .R0 => (0,4*u+12)
  | .E1 => (0,2*w+12)
  | .Eeven => (11,2*u+w-2)
  | .Eodd => (0,2*u+w+10)
  | .O2 => (0,2*w+8)
  | .Oeven1 => (11,2*u+10)
  | .Oeven => (d+7,2*w-4)
  | .Oodd => (d+3,2*w)

/-- The integer branch guards imply the exact natural-counter source transition. -/
theorem source_step (t : Tag) (u w : Int) (hu : 0≤u) (hw : 0≤w)
    (h : guard t u w) :
    let (v,z) := out t u w
    0≤v ∧ 0≤z ∧ BB429.next (u.toNat,w.toNat)=some (v.toNat,z.toNat) := by
  have hU : (u.toNat : Int)=u := Int.toNat_of_nonneg hu
  have hW : (w.toNat : Int)=w := Int.toNat_of_nonneg hw
  cases t <;> simp only [guard] at h <;> simp only [out] <;>
    refine ⟨by omega, by omega, ?_⟩
  all_goals
    simp only [BB429.next]
    repeat' first | (exfalso; omega) | split
    simp only [Option.some.injEq, Prod.mk.injEq]
    omega

/-- Every line has even first-coordinate slope and a second-coordinate slope
    divisible by four. Those properties are preserved by every successful tag. -/
structure Line where
  u : Int
  w : Int
  p : Int
  q : Int
  deriving DecidableEq, Repr

def eu (l : Line) (i : Int) : Int := l.u + 2*(l.p*i)
def ew (l : Line) (i : Int) : Int := l.w + 4*(l.q*i)
def eval (l : Line) (i : Nat) : BB429.State :=
  ((eu l i).toNat,(ew l i).toNat)

def move (t : Tag) (l : Line) : Line :=
  let (v,z) := out t l.u l.w
  match t with
  | .F => ⟨v,z,2*l.p,l.q-l.p⟩
  | .R2 | .R1 | .R0 => ⟨v,z,0,2*l.p⟩
  | .E1 | .O2 => ⟨v,z,0,2*l.q⟩
  | .Eeven | .Eodd => ⟨v,z,0,l.p+l.q⟩
  | .Oeven1 => ⟨v,z,0,l.p⟩
  | .Oeven | .Oodd => ⟨v,z,l.p-l.q,2*l.q⟩

theorem move_eval (t : Tag) (l : Line) (i : Int) :
    out t (eu l i) (ew l i) = (eu (move t l) i, ew (move t l) i) := by
  have hhalf : (l.w+4*(l.q*i))/2 = l.w/2+2*(l.q*i) := by
    rw [show l.w+4*(l.q*i)=l.w+2*(2*(l.q*i)) by omega]
    exact Int.add_mul_ediv_left _ _ (by decide)
  cases t <;> simp only [out, eu, ew, move, Prod.mk.injEq, Int.add_mul,
    Int.sub_mul, Int.mul_assoc, hhalf] <;> omega

private theorem between (a b i N : Int) (hi : 0≤i) (hN : i≤N) :
    (a≤a+b*i ∧ a+b*i≤a+b*N) ∨ (a+b*N≤a+b*i ∧ a+b*i≤a) := by
  by_cases hb : 0≤b
  · have h1 := Int.mul_nonneg hb hi
    have h2 := Int.mul_le_mul_of_nonneg_left hN hb
    omega
  · have h1 := Int.mul_nonneg (a := -b) (b := i) (by omega) hi
    have h2 := Int.mul_le_mul_of_nonneg_left hN (c := -b) (by omega)
    simp only [Int.neg_mul] at h1 h2
    omega

private theorem gap (l : Line) (i : Int) :
    ew l i-2*eu l i = (l.w-2*l.u)+4*((l.q-l.p)*i) := by
  simp only [eu,ew,Int.sub_mul]
  omega

/-- Endpoint checks suffice for every integral parameter between the endpoints. -/
theorem guard_between (t : Tag) (l : Line) (i N : Int)
    (hi : 0≤i) (hN : i≤N)
    (h0 : guard t l.u l.w) (h1 : guard t (eu l N) (ew l N)) :
    guard t (eu l i) (ew l i) := by
  have hg := between (l.w-2*l.u) (4*(l.q-l.p)) i N hi hN
  have hw := between l.w (4*l.q) i N hi hN
  simp only [Int.mul_assoc] at hg hw
  rw [← gap l i, ← gap l N] at hg
  change (l.w≤ew l i ∧ ew l i≤ew l N) ∨ (ew l N≤ew l i ∧ ew l i≤l.w) at hw
  have hm : (ew l i-2*eu l i)%4=(l.w-2*l.u)%4 := by
    rw [gap, Int.add_mul_emod_self_left]
  cases t <;> simp only [guard] at h0 h1 ⊢ <;> omega

/-- The checker needs only two guard evaluations per branch, irrespective of
    the number of intermediate parameter values. -/
def checkWord (word : List Tag) (l : Line) (N : Nat) : Option Line :=
  match word with
  | [] => some l
  | t::ts => if guard t l.u l.w ∧ guard t (eu l N) (ew l N) then
      checkWord ts (move t l) N else none

theorem checkWord_sound (word : List Tag) (l l' : Line) (N i : Nat)
    (hi : i≤N) (hu : 0≤eu l i) (hw : 0≤ew l i)
    (hc : checkWord word l N=some l') :
    BB429.run word.length (eval l i)=some (eval l' i) ∧
      0≤eu l' i ∧ 0≤ew l' i := by
  induction word generalizing l with
  | nil =>
    simp only [checkWord, Option.some.injEq] at hc
    subst l'
    exact ⟨rfl,hu,hw⟩
  | cons t ts ih =>
    simp only [checkWord] at hc
    split at hc
    next h =>
      have hg := guard_between t l i N (by omega) (by omega) h.1 h.2
      have hs := source_step t (eu l i) (ew l i) hu hw hg
      rw [move_eval] at hs
      obtain ⟨hr, hu', hw'⟩ := ih (move t l) hs.1 hs.2.1 hc
      refine ⟨?_,hu',hw'⟩
      rw [List.length_cons, Nat.add_comm, BB429.run_add]
      change (BB429.next (eval l i)).bind (BB429.run ts.length)=_
      rw [show BB429.next (eval l i)=some (eval (move t l) i) from hs.2.2]
      exact hr
    next h => simp at hc

def sectionLine (u w q : Nat) : Line := ⟨u,w,0,q⟩

theorem sectionLine_eval (u w q i : Nat) :
    eval (sectionLine u w q) i=(u,w+4*q*i) := by
  simp only [eval,sectionLine,eu,ew,Int.zero_mul,Int.mul_zero,Int.add_zero,
    Int.toNat_natCast]
  have h : (↑w + 4 * (↑q * ↑i) : Int) = ↑(w+4*q*i) := by
    simp [Int.natCast_add, Int.natCast_mul, Int.mul_assoc]
  rw [h, Int.toNat_natCast]

/-- One certificate proves every block in a translation pump, including
    the exact count of successful accelerator transitions. -/
theorem repeated_pump (word : List Tag) (u w q N : Nat)
    (hc : checkWord word (sectionLine u w q) N =
      some (sectionLine u (w+4*q) q)) :
    ∀ k≤N+1, BB429.run (k*word.length) (u,w)=some (u,w+4*q*k) := by
  intro k
  induction k with
  | zero => simp [BB429.run]
  | succ k ih =>
    intro hk
    have hi : k≤N := by omega
    have hprev := ih (by omega)
    have hblock := (checkWord_sound word (sectionLine u w q)
      (sectionLine u (w+4*q) q) N k hi (by simp [eu,sectionLine])
      (by
        simp only [ew,sectionLine]
        have hp : 0 ≤ (q : Int)*(k : Int) := Int.mul_nonneg (by omega) (by omega)
        omega) hc).1
    rw [sectionLine_eval, sectionLine_eval] at hblock
    rw [Nat.succ_mul,BB429.run_add,hprev]
    simp only [Option.bind_some]
    rw [hblock]
    congr 2
    simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

#print axioms source_step
#print axioms move_eval
#print axioms guard_between
#print axioms checkWord_sound
#print axioms repeated_pump
end BB429AffinePump
