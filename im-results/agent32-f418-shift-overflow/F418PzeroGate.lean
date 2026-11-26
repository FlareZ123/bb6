import F418PzeroBlock

namespace BB6.Agent32F418.PzeroBlock

def NoEven (N : Nat) : Prop := ∀ i, i%2=0 → N.testBit i=false

theorem noEven_div4 {N : Nat} (hn : NoEven N) : NoEven (N/4) := by
  intro i he
  have h := hn (i+2) (by omega)
  rw [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_add] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul]
  simpa [Nat.mul_comm] using h

theorem noEven_remainder {N : Nat} (hn : NoEven N) : N%4=0 ∨ N%4=2 := by
  have h := hn 0 (by decide)
  rw [Nat.testBit_zero] at h
  simp only [decide_eq_false_iff_not] at h
  omega

theorem noEven_lowWord {N m : Nat} (hn : NoEven N) (hw : N<4^m) :
    ∃ v<2^m, N=lowWord v m := by
  induction m generalizing N with
  | zero => simp at hw; exact ⟨0,by decide,by simp [lowWord,prepend]; omega⟩
  | succ m ih =>
    rw [Nat.pow_succ] at hw
    have hd : N/4<4^m := (Nat.div_lt_iff_lt_mul (by decide)).mpr hw
    obtain ⟨v,hv,hq⟩ := ih (noEven_div4 hn) hd
    let b := (N%4)/2
    have hb : b<2 := by dsimp [b]; omega
    have hm := noEven_remainder hn
    refine ⟨2*v+b,by rw [Nat.pow_succ]; omega,?_⟩
    change N=4*lowWord ((2*v+b)/2) m+2*((2*v+b)%2)
    rw [show (2*v+b)/2=v by omega,show (2*v+b)%2=b by omega,←hq]
    dsimp [b]; omega

theorem lowWord_noEven (v m : Nat) : NoEven (lowWord v m) := by
  induction m generalizing v with
  | zero => intro i _; simp [lowWord,prepend]
  | succ m ih =>
    intro i he
    change (4*lowWord (v/2) m+2*(v%2)).testBit i=false
    rw [show 4=2^2 by decide,Nat.testBit_two_pow_mul_add _ (by omega : 2*(v%2)<2^2)]
    split
    · rename_i hi
      have : i=0 := by omega
      subst i
      simp [Nat.testBit_zero,Nat.mul_mod]
    · exact ih (v/2) (i-2) (by omega)

theorem pulses_bit0 {l : Nat} (hl : 0<l) : (pulses l).testBit 0=true := by
  cases l with
  | zero => omega
  | succ l => rw [pulses_low,Nat.testBit_zero]; simp [Nat.add_mod,Nat.mul_mod]

theorem pulse_at_shift {l a q : Nat} (hl : 0<l) (hq : q<2^a) :
    (2^a*pulses l+q).testBit a=true := by
  rw [Nat.testBit_two_pow_mul_add _ hq]
  simpa using pulses_bit0 hl

theorem noEven_low {a H q : Nat} (hq : q<2^a) (hn : NoEven (2^a*H+q)) : NoEven q := by
  intro i hi
  by_cases h : i<a
  · have hh := hn i hi
    rw [Nat.testBit_two_pow_mul_add _ hq,if_pos h] at hh
    exact hh
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega)))

theorem multiplier_bound {u l W : Nat} (hl : l≤W) (hwidth : 2^l*u-7<2^W) :
    u-7<2^(W-l) := by
  have hp := Nat.two_pow_pos l
  have hm := Nat.mul_le_mul_right 7 hp
  simp only [Nat.one_mul] at hm
  have h : 2^l*(u-7) ≤ 2^l*u-7 := by rw [Nat.mul_sub]; omega
  have hpow : 2^W=2^l*2^(W-l) := by rw [←Nat.pow_add,show l+(W-l)=W by omega]
  rw [hpow] at hwidth
  exact (Nat.mul_lt_mul_left hp).mp (Nat.lt_of_le_of_lt h hwidth)

theorem terminal_nonborrow {u l W : Nat} (hl : 0<l) (hlw : l≤W) (hu : 7≤u)
    (hwidth : 2^l*u-7<2^W)
    (hn : NoEven (replay (2^l*u) W l-7)) :
    ∃ m v, W=l+2*m ∧ v<2^m ∧ u=lowWord v m+7 := by
  let a := W-l+3
  let q := u-7
  have hq0 := multiplier_bound hlw hwidth
  have hq : q<2^a := Nat.lt_of_lt_of_le hq0 (Nat.pow_le_pow_right (by decide) (by dsimp [a]; omega))
  have ht : replay (2^l*u) W l-7=2^a*pulses l+q := by
    rw [replay_terminal u l W hlw]; dsimp [a,q]; omega
  rw [ht] at hn
  have hb := pulse_at_shift hl hq
  have ha : a%2=1 := by
    by_cases h : a%2=1
    · exact h
    · have hh:=hn a (by omega)
      rw [hb] at hh
      contradiction
  have hlow := noEven_low hq hn
  let m := (W-l)/2
  have hwm : W=l+2*m := by dsimp [m,a] at *; omega
  have hq' : q<4^m := by rw [←show 2^(2*m)=4^m by rw [Nat.pow_mul],←show W-l=2*m by omega]; exact hq0
  obtain ⟨v,hv,hv'⟩ := noEven_lowWord hlow hq'
  exact ⟨m,v,hwm,hv,by dsimp [q] at hv'; omega⟩

theorem terminal_borrow {u l W : Nat} (hl : 2≤l) (hlw : l≤W) (hw : 3≤W)
    (hu : u%2=1) (hub : u<7) (hn : NoEven (replay (2^l*u) W l-7)) :
    u=1 ∧ W=l := by
  let a := W-l+3
  let d := 7-u
  have hd : 0<d ∧ d≤6 := by dsimp [d]; omega
  have ha : 3≤a := by dsimp [a]; omega
  have hp : 8≤2^a := Nat.pow_le_pow_right (by decide : 0<2) ha
  let q := 2^a-d
  have hq : q<2^a := by dsimp [q]; omega
  have hl' : 0<l-1 := by omega
  have ht : replay (2^l*u) W l-7=2^(a+4)*pulses (l-1)+q := by
    rw [replay_terminal u l W hlw,show l=l-1+1 by omega,pulses_low]
    have hidx : W-(l-1+1)+3=a := by dsimp [a]; omega
    rw [hidx,Nat.pow_add (a:=2) (m:=a) (n:=4),Nat.mul_add]
    dsimp [q,d]
    change u + (2^a*(16*pulses (l-1))+2^a*1)-7 = 2^a*16*pulses (l-1)+(2^a-(7-u))
    rw [Nat.mul_assoc]
    omega
  rw [ht] at hn
  have hq4 : q<2^(a+4) := Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := pulse_at_shift hl' hq4
  have haodd : a%2=1 := by
    by_cases h : a%2=1
    · exact h
    · have hh:=hn (a+4) (by omega)
      rw [hb] at hh
      contradiction
  have hlow := noEven_low hq4 hn
  have ha3 : a=3 := by
    by_cases h : a=3
    · exact h
    · exfalso
      have ha5 : 5≤a := by omega
      have hpow : 16≤2^(a-1) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 4≤a-1)
      have he : 2^a=2^(a-1)*2 := by rw [←Nat.pow_succ]; congr 1
      have hqlo : 2^(a-1)≤q := by dsimp [q]; rw [he]; omega
      have hqhi : q<2^(a-1)*2 := by rw [←he]; exact hq
      have hdiv : q/2^(a-1)=1 := Nat.div_eq_of_lt_le (by simpa using hqlo) (by simpa [Nat.mul_comm] using hqhi)
      have hf := hlow (a-1) (by omega)
      rw [Nat.testBit_eq_decide_div_mod_eq,hdiv] at hf
      contradiction
  have hW : W=l := by dsimp [a] at ha3; omega
  have hbit := hlow 2 (by decide)
  dsimp [q,d] at hbit
  rw [ha3,Nat.testBit_eq_decide_div_mod_eq] at hbit
  simp only [show 2^3=8 by decide,show 2^2=4 by decide,decide_eq_false_iff_not] at hbit
  exact ⟨by omega,hW⟩

theorem exceptional_endpoint {l W : Nat} (hW : W=l) (hl : 3≤W) :
    replay (2^l*1) W l-7=lowWord 1 2+2^(2*2+3)*pulses (l-1) := by
  rw [replay_terminal 1 l W (by omega),hW,show l-l+3=3 by omega]
  have hp : pulses l=16*pulses (l-1)+1 := by
    have h := pulses_low (l-1)
    rwa [show l-1+1=l by omega] at h
  rw [hp]
  change 1+8*(16*pulses (l-1)+1)-7=2+128*pulses (l-1)
  omega

theorem terminal_oddchain (OC : Nat → Nat → Prop)
    (last : ∀ j, j%2=1 → OC (2^j) j)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    {u l W : Nat} (hl : 2≤l) (hlw : l≤W) (hw : 3≤W) (hu : u%2=1)
    (hwidth : 2^l*u-7<2^W) (hn : NoEven (replay (2^l*u) W l-7)) :
    OC (replay (2^l*u) W l-7) 3 := by
  by_cases hub : 7≤u
  · obtain ⟨m,v,hw',_,hu'⟩ := terminal_nonborrow (by omega) hlw hub hwidth hn
    rw [hu',hw']
    rw [←prepared_augmented,prepared_endpoint]
    exact prepared_family OC last more v m l hl
  · obtain ⟨hu',hW⟩ := terminal_borrow hl hlw hw hu (by omega) hn
    rw [hu',exceptional_endpoint hW hw]
    exact prepared_family OC last more 1 2 (l-1) (by omega)

theorem block_length_bound {N W u l : Nat} (hW : 3≤W) (hN : N<2^W)
    (hu : u%2=1) (hM : N+7=2^l*u) : l≤W := by
  by_cases hl : l≤W
  · exact hl
  · have hp : 8≤2^W := Nat.pow_le_pow_right (by decide : 0<2) hW
    have hpow : 2^(W+1)≤2^l := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    have hmul := Nat.mul_le_mul_left (2^l) (show 1≤u by omega)
    simp only [Nat.mul_one] at hmul
    rw [Nat.pow_succ] at hpow
    omega

#print axioms block_length_bound
#print axioms terminal_oddchain
#print axioms terminal_nonborrow
#print axioms terminal_borrow
end BB6.Agent32F418.PzeroBlock
