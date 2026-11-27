import StrictWord
namespace BB6.Agent43StrictWord

/-- Weighted bit sum with arbitrary positional coefficients. -/
def bitSum : Nat → Nat → (Nat → Nat) → Nat
  | 0,_,_ => 0
  | k+1,B,f => (B%2)*f 0+2*bitSum k (B/2) (fun i => f (i+1))

theorem bitSum_congr (k B : Nat) (f g : Nat → Nat) (h : ∀ i<k, f i=g i) :
    bitSum k B f=bitSum k B g := by
  induction k generalizing B f g with
  | zero => rfl
  | succ k ih =>
    rw [bitSum,bitSum,h 0 (by omega)]
    rw [ih (B/2) (fun i => f (i+1)) (fun i => g (i+1)) (fun i hi => h (i+1) (by omega))]

theorem bitSum_add (k B : Nat) (f g : Nat → Nat) :
    bitSum k B (fun i => f i+g i)=bitSum k B f+bitSum k B g := by
  induction k generalizing B f g with
  | zero => rfl
  | succ k ih =>
    rw [bitSum,bitSum,bitSum,ih,Nat.mul_add,Nat.mul_add]
    ac_rfl

theorem bitSum_smul (k B a : Nat) (f : Nat → Nat) :
    bitSum k B (fun i => a*f i)=a*bitSum k B f := by
  induction k generalizing B f with
  | zero => simp [bitSum]
  | succ k ih =>
    rw [bitSum,bitSum,ih,Nat.mul_add]
    ac_rfl

theorem bitSum_ones (k B : Nat) : bitSum k B (fun _ => 1)=B%2^k := by
  induction k generalizing B with
  | zero => simp [bitSum,Nat.mod_one]
  | succ k ih =>
    rw [bitSum,ih,Nat.mul_one,Nat.pow_succ]
    have h₁ := Nat.div_add_mod (B/2) (2^k)
    have h₂ := Nat.mod_lt (B/2) (Nat.two_pow_pos k)
    have h₃ : B%2+2*((B/2)%2^k)+(2^k*2)*((B/2)/2^k)=B := by
      have h : (2^k*2)*((B/2)/2^k)=2*(2^k*((B/2)/2^k)) := by ac_rfl
      rw [h]
      omega
    exact ((Nat.div_mod_unique (by omega : 0<2^k*2)).2 ⟨h₃,by omega⟩).2.symm

def maskValue (m i : Nat) : Nat := if m.testBit i then 1 else 0

theorem and_div2 (B m : Nat) : (B &&& m)/2=(B/2 &&& m/2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two,Nat.testBit_and]

theorem and_mod2 (B m : Nat) : (B &&& m)%2=(B%2)*maskValue m 0 := by
  have h := Nat.testBit_and B m 0
  simp only [Nat.testBit_zero,maskValue] at h ⊢
  rcases (show B%2=0 ∨ B%2=1 by omega) with hb|hb <;>
    rcases (show m%2=0 ∨ m%2=1 by omega) with hm|hm <;>
      rcases (show (B &&& m)%2=0 ∨ (B &&& m)%2=1 by omega) with hr|hr <;>
        simp [hb,hm,hr] at h ⊢

theorem bitSum_mask (k B m : Nat) :
    bitSum k B (maskValue m)=(B &&& m)%2^k := by
  induction k generalizing B m with
  | zero => simp [bitSum,Nat.mod_one]
  | succ k ih =>
    have h : (fun i => maskValue m (i+1))=maskValue (m/2) := by
      funext i
      simp [maskValue,Nat.testBit_div_two]
    rw [bitSum,h,ih,←and_div2,←and_mod2]
    have ht := bitSum_ones (k+1) (B &&& m)
    rw [bitSum,bitSum_ones,Nat.mul_one] at ht
    exact ht

theorem weight_bitSum (q k B : Nat) : weight q k B=bitSum k B (fun i => q+i) := by
  induction k generalizing q B with
  | zero => rfl
  | succ k ih =>
    rw [weight,bitSum,ih,Nat.add_zero,Nat.mul_comm q (B%2)]
    congr 1
    congr 1
    apply bitSum_congr
    intro i hi
    omega

/-- The six masks have a one precisely where the corresponding bit of
    the bit position is one. The only finite decision is on 64 positions. -/
def index64 (i : Nat) : Nat :=
  maskValue 0xAAAAAAAAAAAAAAAA i + 2*maskValue 0xCCCCCCCCCCCCCCCC i +
  4*maskValue 0xF0F0F0F0F0F0F0F0 i + 8*maskValue 0xFF00FF00FF00FF00 i +
  16*maskValue 0xFFFF0000FFFF0000 i + 32*maskValue 0xFFFFFFFF00000000 i

theorem index64_eq (i : Nat) (hi : i<64) : index64 i=i := by
  have h : ∀ i : Fin 64, index64 i.val=i.val := by decide
  exact h ⟨i,hi⟩

/-- Actual bitmask expression used by the C++ packed fitted queries. -/
def dw64 (B : Nat) : Nat :=
  (B &&& 0xAAAAAAAAAAAAAAAA) + 2*(B &&& 0xCCCCCCCCCCCCCCCC) +
  4*(B &&& 0xF0F0F0F0F0F0F0F0) + 8*(B &&& 0xFF00FF00FF00FF00) +
  16*(B &&& 0xFFFF0000FFFF0000) + 32*(B &&& 0xFFFFFFFF00000000)

/-- A word of at most 64 bits can be evaluated with six masks and one
    small-integer multiplication; no individual bit proof is needed. -/
theorem weight_fast (q k B : Nat) (hk : k≤64) (hb : B<2^k) :
    weight q k B=q*B+dw64 B := by
  rw [weight_bitSum]
  rw [bitSum_congr k B (fun i => q+i) (fun i => q+index64 i) (fun i hi => by rw [index64_eq i (by omega)])]
  unfold index64
  rw [show (fun i => q+(maskValue 0xAAAAAAAAAAAAAAAA i + 2*maskValue 0xCCCCCCCCCCCCCCCC i + 4*maskValue 0xF0F0F0F0F0F0F0F0 i + 8*maskValue 0xFF00FF00FF00FF00 i + 16*maskValue 0xFFFF0000FFFF0000 i + 32*maskValue 0xFFFFFFFF00000000 i)) = (fun i => q*1 + (maskValue 0xAAAAAAAAAAAAAAAA i + 2*maskValue 0xCCCCCCCCCCCCCCCC i + 4*maskValue 0xF0F0F0F0F0F0F0F0 i + 8*maskValue 0xFF00FF00FF00FF00 i + 16*maskValue 0xFFFF0000FFFF0000 i + 32*maskValue 0xFFFFFFFF00000000 i)) by simp]
  simp only [bitSum_add,bitSum_smul,bitSum_ones,bitSum_mask]
  have hmod (m : Nat) : (B &&& m)%2^k=B &&& m := Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hb)
  simp only [Nat.mod_eq_of_lt hb,hmod,dw64]

#print axioms bitSum_mask
#print axioms index64_eq
#print axioms weight_fast
end BB6.Agent43StrictWord
