import BitCarry
namespace BB6.Agent28BitExact
open BB6.Agent28BitCarry

/-- Every set lane-mask bit lies in the lower half of its lane. -/
theorem laneMask_support (b r p : Nat) (hb : 0<b) (h : (laneMask b r).testBit p=true) : p%(2*b)<b := by
  induction r generalizing p with
  | zero =>
    simp only [laneMask,Nat.testBit_two_pow_sub_one,decide_eq_true_eq] at h
    rw [Nat.mod_eq_of_lt (show p<2*b by omega)]
    exact h
  | succ r ih =>
    simp only [laneMask,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
    rcases h with h|⟨hp,hh⟩
    · exact ih _ h
    · have he : p=(p-2*b*2^r)+(2*b)*2^r := by omega
      calc
        p%(2*b)=(p-2*b*2^r+(2*b)*2^r)%(2*b) := congrArg (fun z => z%(2*b)) he
        _=(p-2*b*2^r)%(2*b) := Nat.add_mul_mod_self_left _ _ _
        _<b := ih _ hh

def Supported (b x : Nat) : Prop := ∀ p, x.testBit p=true → p%(2*b)<b

theorem mask_supported (b r x : Nat) (hb : 0<b) : Supported b (x &&& laneMask b r) := by
  intro p hp
  rw [Nat.testBit_and,Bool.and_eq_true] at hp
  exact laneMask_support b r p hb hp.2

theorem packedPos_mod (k i : Nat) : packedPos k i % (2*2^k)=i%2^k := by
  unfold packedPos
  rw [Nat.add_comm,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt i (Nat.two_pow_pos k); omega)

theorem opposite_lane (b p : Nat) (hb : 0<b) :
    (p%(2*b)<b ↔ b≤(p+b)%(2*b)) := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (show b<2*b by omega)]
  have hp := Nat.mod_lt p (show 0<2*b by omega)
  by_cases hh : p%(2*b)<b
  · rw [Nat.mod_eq_of_lt (by omega : p%(2*b)+b<2*b)]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : 2*b≤p%(2*b)+b),Nat.mod_eq_of_lt (by omega : p%(2*b)+b-2*b<2*b)]
    omega

theorem packStep_complete (L k x i : Nat) (hx : Supported (2^k) x)
    (h : (packStep L k x).testBit (packedPos (k+1) i)=true) :
    x.testBit (packedPos k i)=true := by
  simp only [packStep,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Bool.and_eq_true,Bool.or_eq_true] at h
  have hm := packedPos_mod k i
  have hlow : packedPos k i%(2*2^k)<2^k := by rw [hm]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hflip := opposite_lane (2^k) (packedPos (k+1) i) (Nat.two_pow_pos _)
  rcases packedPos_step k i with hpos|hpos
  · rw [hpos]
    rcases h.1 with h1|h2
    · exact h1
    · rw [Nat.add_comm] at h2
      have hgood := hx _ h2
      rw [hpos] at hlow
      have hbad := hflip.mp hlow
      omega
  · rw [hpos]
    rcases h.1 with h1|h2
    · have hgood := hx _ h1
      have hbad := hflip.mp hgood
      rw [hpos] at hlow
      omega
    · simpa only [Nat.add_comm] using h2

theorem packStep_supported (L k x : Nat) : Supported (2^(k+1)) (packStep L k x) := by
  unfold packStep
  exact mask_supported _ _ _ (Nat.two_pow_pos _)

theorem packFrom_complete (L k x r i : Nat) (hk : k+r=L) (hx : Supported (2^k) x)
    (h : (packFrom L k x r).testBit (packedPos L i)=true) :
    x.testBit (packedPos k i)=true := by
  induction r generalizing k x with
  | zero => simpa [packFrom,show k=L by omega] using h
  | succ r ih =>
    have h' := ih (k+1) (packStep L k x) (by omega) (packStep_supported L k x) h
    exact packStep_complete L k x i hx h'

/-- Exact, not merely one-directional, even-position compression on the
    declared width. No assumption on the bits outside the width is needed. -/
theorem packEven_complete (L x i : Nat) (hi : i<2^L)
    (h : (packEven L x).testBit i=true) : x.testBit (2*i)=true := by
  have hpos0 : packedPos 0 i=2*i := by simp [packedPos]; omega
  have hposL : packedPos L i=i := by simp [packedPos,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
  have hh : (packFrom L 0 (x &&& laneMask 1 L) L).testBit (packedPos L i)=true := by simpa [packEven,hposL] using h
  have hs := packFrom_complete L 0 (x &&& laneMask 1 L) L i (by omega) (by simpa using mask_supported 1 L x (by decide)) hh
  rw [hpos0,Nat.testBit_and,Bool.and_eq_true] at hs
  exact hs.1

theorem packEven_iff (L x i : Nat) (hi : i<2^L) :
    (packEven L x).testBit i=true ↔ x.testBit (2*i)=true :=
  ⟨packEven_complete L x i hi,packEven_sound L x i hi⟩

def Below (M x : Nat) : Prop := ∀ p, x.testBit p=true → p<M

theorem packFrom_below (L k x r : Nat) (hk : k+r=L)
    (hx : r=0 → Below (2^L) x) : Below (2^L) (packFrom L k x r) := by
  induction r generalizing k x with
  | zero => exact hx rfl
  | succ r ih =>
    apply ih (k+1) (packStep L k x) (by omega)
    intro hr p hp
    have hkl : k+1=L := by omega
    simp only [packStep,Nat.testBit_and,Bool.and_eq_true] at hp
    have hh := hp.2
    rw [hkl,Nat.sub_self,laneMask,Nat.testBit_two_pow_sub_one] at hh
    exact of_decide_eq_true hh

theorem packEven_below (L x : Nat) : Below (2^L) (packEven L x) := by
  unfold packEven
  apply packFrom_below L 0 _ L (by omega)
  intro h p hp
  subst L
  simp only [Nat.testBit_and,Bool.and_eq_true,laneMask,Nat.testBit_two_pow_sub_one] at hp
  exact of_decide_eq_true hp.2

#print axioms packEven_iff
end BB6.Agent28BitExact
