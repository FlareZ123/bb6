import ReverseComplement
import BitCarry
namespace BB6.Agent43ReverseSet
open BB6.Agent28BitCarry (laneMask packedPos packedPos_step packedPos_mask)

def dilateStep (L k x : Nat) : Nat := (x ||| (x <<< 2^k)) &&& laneMask (2^k) (L-k)

theorem dilateStep_sound (L k x i : Nat) (hk : k<L) (hi : i<2^L)
    (h : x.testBit (packedPos (k+1) i)=true) :
    (dilateStep L k x).testBit (packedPos k i)=true := by
  rw [dilateStep,Nat.testBit_and,Nat.testBit_or,packedPos_mask k L i (by omega) hi]
  rcases packedPos_step k i with he|he
  · simp [he,h]
  · rw [he,Nat.testBit_shiftLeft]
    simp [show 2^k≤packedPos (k+1) i+2^k by omega,h]

def dilateFrom (L : Nat) : Nat → Nat → Nat
  | 0,x => x
  | k+1,x => dilateFrom L k (dilateStep L k x)

theorem dilateFrom_sound (L k x i : Nat) (hk : k≤L) (hi : i<2^L)
    (h : x.testBit (packedPos k i)=true) : (dilateFrom L k x).testBit (packedPos 0 i)=true := by
  induction k generalizing x with
  | zero => exact h
  | succ k ih => exact ih _ (by omega) (dilateStep_sound _ _ _ _ (by omega) hi h)

theorem dilate_sound (L x i : Nat) (hi : i<2^L) (h : x.testBit i=true) :
    (dilateFrom L L x).testBit (2*i)=true := by
  have h0 : packedPos 0 i=2*i := by simp [packedPos,Nat.mod_one]
  have hL : packedPos L i=i := by simp [packedPos,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
  rw [← h0]; exact dilateFrom_sound _ _ _ _ (by omega) hi (by simpa [hL] using h)

def backPacked (L C y ends : Nat) : Nat :=
  let z := dilateFrom L L ends <<< y
  (z ||| (z >>> C)) % 2^(C-1)

theorem backPacked_sound (L C y ends b x c : Nat) (hc : c<2^L) (hbit : ends.testBit c=true)
    (hx : x≤1) (hb : b+1<C) (he : 2*c+y=b+x*C) : (backPacked L C y ends).testBit b=true := by
  have hd := dilate_sound L ends c hc hbit
  have hz : (dilateFrom L L ends <<< y).testBit (2*c+y)=true := by
    rw [Nat.testBit_shiftLeft]; simp [show y≤2*c+y by omega,hd]
  unfold backPacked
  rw [Nat.testBit_mod_two_pow,Nat.testBit_or]
  have hb' : b<C-1 := by omega
  by_cases h : x=0
  · subst x; simp at he; rw [he] at hz; simp [hb',hz]
  · have h1 : x=1 := by omega
    subst x; simp at he
    rw [Nat.testBit_shiftRight]
    have hEq : C+b=2*c+y := by omega
    simp [hb',hEq,hz]

def rewindPacked (L : Nat) (C y : Nat → Nat) (s : Nat) : Nat → Nat → Nat
  | 0,ends => ends
  | k+1,ends => rewindPacked L C y s k (backPacked L (C (s+k)) (y (s+k)) ends)

theorem rewindPacked_sound {L : Nat} {C y : Nat → Nat} {s a k c ends : Nat}
    (hw : Walk C y s a k c) (hb : ∀ j, j<k → C (s+j)<2^L)
    (hc : c<2^L) (hbit : ends.testBit c=true) :
    (rewindPacked L C y s k ends).testBit a=true := by
  induction hw generalizing ends with
  | nil => exact hbit
  | step k b x c h hx hbound he ih =>
    exact ih (fun j hj => hb j (by omega)) (by have := hb k (by omega); omega)
      (backPacked_sound _ _ _ _ _ _ _ hc hbit hx hbound he)

theorem walk_split {C y : Nat → Nat} {s a k c : Nat} (hw : Walk C y s a k c)
    (h : Nat) (hh : h≤k) : ∃ b, Walk C y s a h b ∧ Walk C y (s+h) b (k-h) c := by
  induction hw with
  | nil => have he : h=0 := by omega
           subst h; exact ⟨a,Walk.nil,by simpa using (Walk.nil : Walk C y s a 0 a)⟩
  | step k b x c hw hx hb he ih =>
    by_cases hk : h≤k
    · obtain ⟨d,hd,hs⟩ := ih hk
      have hlen : k+1-h=k-h+1 := by omega
      have hidx : s+h+(k-h)=s+k := by omega
      refine ⟨d,hd,?_⟩; rw [hlen]
      exact Walk.step (k-h) b x c hs hx (by rwa [hidx]) (by rwa [hidx])
    · have hEq : h=k+1 := by omega
      subst h; exact ⟨c,Walk.step k b x c hw hx hb he,by simpa using (Walk.nil : Walk C y (s+(k+1)) c 0 c)⟩

/-- One-sided checked reverse cover, with bitset and list checkpoints. -/
def BackCover (C y : Nat → Nat) (s k : Nat) (starts ends : Nat → Prop) : Prop :=
  ∀ a c, Walk C y s a k c → ends c → starts a

theorem BackCover.append {C y : Nat → Nat} {s k j : Nat} {starts mid ends : Nat → Prop}
    (h₁ : BackCover C y s k starts mid) (h₂ : BackCover C y (s+k) j mid ends) :
    BackCover C y s (k+j) starts ends := by
  intro a c hw hc
  obtain ⟨b,hpre,hsuf⟩ := walk_split hw k (by omega)
  have hsuf' : Walk C y (s+k) b j c := by simpa using hsuf
  exact h₁ a b hpre (h₂ b c hsuf' hc)

def Bits (z : Nat) (i : Nat) : Prop := z.testBit i=true
def Listed (cs : List Nat) (i : Nat) : Prop := i∈cs

theorem bits_bound (L z : Nat) (hz : z<2^(2^L)) : ∀ c, Bits z c → c<2^L := by
  intro c hc
  by_cases h : c<2^L
  · exact h
  · exfalso
    have hle : 2^(2^L)≤2^c := Nat.pow_le_pow_right (by decide) (by omega)
    have hh := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hz hle)
    unfold Bits at hc
    rw [hh] at hc
    contradiction

theorem coverPacked (L : Nat) (C y : Nat → Nat) (s k starts ends : Nat)
    (hbound : ∀ j, j<k → C (s+j)<2^L)
    (hEq : rewindPacked L C y s k ends=starts) (hb : ∀ c, Bits ends c → c<2^L) :
    BackCover C y s k (Bits starts) (Bits ends) := by
  intro a c hw hc
  have h := rewindPacked_sound hw hbound (hb c hc) hc
  simpa [Bits,← hEq] using h

theorem coverList (C y : Nat → Nat) (s k : Nat) (starts ends : List Nat)
    (he : rewindBounded C y s k ends=starts) : BackCover C y s k (Listed starts) (Listed ends) := by
  intro a c hw hc; have h := rewindBounded_sound hw ends hc
  simpa [Listed,← he] using h

theorem coverExtract (L : Nat) (C y : Nat → Nat) (s ends : Nat) (cs : List Nat)
    (he : extract 0 ends L=cs) (hb : ∀ c, Bits ends c → c<2^L) :
    BackCover C y s 0 (Listed cs) (Bits ends) := by
  intro a c hw hc
  cases hw
  have h := (extract_iff 0 ends L a).2 ⟨by omega,by have := hb a hc; omega,by simpa [Bits] using hc⟩
  simpa [Listed,← he] using h

theorem cover_no_omitted {C y : Nat → Nat} {s k bound start ends : Nat} {cs : List Nat}
    (hcover : BackCover C y s k (Listed cs) (Bits (omitted bound ends)))
    (hdisjoint : cs.all (fun c => !(start.testBit c))=true)
    {a c : Nat} (hw : Walk C y s a k c) (ha : Bits start a) (hc : c<bound) : Bits ends c := by
  by_cases h : Bits ends c
  · exact h
  · have hfalse : ends.testBit c=false := by cases he : ends.testBit c <;> simp_all [Bits]
    have hbit : Bits (omitted bound ends) c := by simp [Bits,omitted,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,Nat.testBit_mod_two_pow,hc,hfalse]
    have hm := hcover a c hw hbit
    have hcontra := List.all_eq_true.mp hdisjoint a hm
    simp [Bits] at ha
    simp [ha] at hcontra

#print axioms backPacked_sound
#print axioms BackCover.append
#print axioms cover_no_omitted
end BB6.Agent43ReverseSet
