import DyadicAncestry
import Lean

namespace BB6.Agent12Dyadic

/-- All small-right images and both special pure-dyadic sum families.
    This intentionally allows more births than the authentic map. -/
def Birth (s : Coord) : Prop :=
  (∃ k : Nat, k<8 ∧ s.h-s.l+1+(s.o:Nat)=k) ∨
  (∃ n : Nat, s.l+s.h-1=(2:Int)^n) ∨
  (∃ n : Nat, s.l+s.h=(2:Int)^n)

def modulus (b : Nat) : Int := 2^b

def reduce (b : Nat) (s : Coord) : Coord :=
  ⟨s.l%modulus b,s.h%modulus b,s.o⟩

def powResidue (b : Nat) (z : Int) : Prop :=
  z%modulus b=0 ∨ ∃ n<b, z%modulus b=(2:Int)^n

def BirthResidue (b : Nat) (s : Coord) : Prop :=
  (∃ k : Nat, k<8 ∧ (s.h-s.l+1+(s.o:Nat))%modulus b=(k:Int)%modulus b) ∨
  powResidue b (s.l+s.h-1) ∨ powResidue b (s.l+s.h)

theorem powResidue_pow (b n : Nat) : powResidue b ((2:Int)^n) := by
  by_cases h : n<b
  · right
    refine ⟨n,h,Int.emod_eq_of_lt (Int.le_of_lt (Int.pow_pos (by decide))) ?_⟩
    unfold modulus
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1<2) h)
  · left
    apply Int.emod_eq_zero_of_dvd
    refine ⟨(2:Int)^(n-b),?_⟩
    rw [modulus,←Int.pow_add,show b+(n-b)=n by omega]

theorem birth_residue (b : Nat) (s : Coord) (h : Birth s) : BirthResidue b s := by
  rcases h with ⟨k,hk,he⟩|⟨n,hn⟩|⟨n,hn⟩
  · exact Or.inl ⟨k,hk,by rw [he]⟩
  · exact Or.inr (Or.inl (by rw [hn]; exact powResidue_pow b n))
  · exact Or.inr (Or.inr (by rw [hn]; exact powResidue_pow b n))

/-- Arbitrarily large shifts require only the two zero-tail graph births. -/
theorem long_shift_birth (b r : Nat) (s : Coord) (hr : b≤r) (ho : s.o≤1) :
    BirthResidue b (affine r s) := by
  have hp : modulus b ∣ (2:Int)^r := by
    refine ⟨(2:Int)^(r-b),?_⟩
    rw [modulus,←Int.pow_add,show b+(r-b)=r by omega]
  have he : (affine r s).l+(affine r s).h-1+(s.o:Nat)=(2:Int)^r*s.l := by simp [affine]; omega
  have hd : modulus b ∣ (affine r s).l+(affine r s).h-1+(s.o:Nat) := by
    rw [he]; exact Int.dvd_trans hp (Int.dvd_mul_right _ _)
  have hz := Int.emod_eq_zero_of_dvd hd
  by_cases h : s.o=0
  · right; left; left; simpa [h] using hz
  · have h1 : s.o=1 := by omega
    right; right; left
    rw [h1] at hz
    simpa only [Int.natCast_one,Int.sub_add_cancel] using hz

/-- Reduction is compatible with every ordinary branch. -/
theorem reduce_affine (b r : Nat) (s : Coord) :
    reduce b (affine r (reduce b s))=reduce b (affine r s) := by
  simp only [reduce,affine]
  congr 1
  · simp only [Int.add_emod,Int.sub_emod,Int.mul_emod,Int.emod_emod]
  · simp only [Int.add_emod,Int.emod_emod]

theorem birth_reduce (b : Nat) (s : Coord) :
    BirthResidue b (reduce b s) ↔ BirthResidue b s := by
  simp only [BirthResidue,powResidue,reduce]
  simp only [Int.add_emod,Int.sub_emod,Int.emod_emod]

/-- The exact ordinary edge / exceptional birth classification is all
    the machine-specific input needed by a finite sieve implementation. -/
abbrev EdgeContract (next : Nat × Nat → Option (Nat × Nat)) : Prop :=
  ∀ a k x y, next (a,k)=some (x,y) →
    Birth (encode x y) ∨ ∃ r, 1≤r ∧ affine r (encode a k)=encode x y

inductive Reach (next : Nat × Nat → Option (Nat × Nat)) : Nat × Nat → Prop
  | root : Reach next (5,1)
  | step {s t} : Reach next s → next s=some t → Reach next t

/-- A certificate needs only root, all finite births, and the b-1 small
    shifts. Long shifts are covered by the births, regardless of input. -/
theorem sieve_sound (next : Nat × Nat → Option (Nat × Nat)) (contract : EdgeContract next)
    (b : Nat) (P : Coord → Prop) (root : P (reduce b (encode 5 1)))
    (birth : ∀ s, BirthResidue b s → P (reduce b s))
    (closed : ∀ r s, 1≤r → r<b → P (reduce b s) → P (reduce b (affine r (reduce b s))))
    (s : Nat × Nat) (hs : Reach next s) : P (reduce b (encode s.1 s.2)) := by
  induction hs with
  | root => exact root
  | @step s t h1 h2 ih =>
    rcases s with ⟨a,k⟩
    rcases t with ⟨x,y⟩
    rcases contract a k x y h2 with h|⟨r,hr,he⟩
    · exact birth _ (birth_residue b _ h)
    · rw [←he]
      by_cases h : r<b
      · rw [←reduce_affine]
        exact closed r _ hr h ih
      · exact birth _ (long_shift_birth b r _ (by omega) (by simp [encode]; omega))

#print axioms reduce_affine
#print axioms birth_reduce
#print axioms sieve_sound
end BB6.Agent12Dyadic
