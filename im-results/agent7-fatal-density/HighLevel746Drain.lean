import HighLevel746Underflow

namespace Agent7HighLevel746

def drainA (i:Nat) : Nat := 2^(i+2)-2
def drainB (x i:Nat) : Nat := 2*x+9+2*i-8*2^i

theorem drainA_plus_two (i:Nat) : drainA i+2=2^(i+2) := by
  unfold drainA
  have h : 2≤2^(i+2) := Nat.le_pow (a:=2) (b:=i+2) (by omega)
  exact Nat.sub_add_cancel h

theorem pow_two_add_two (i:Nat) : 2^(i+2)=4*2^i := by
  rw [Nat.pow_add]
  simp [Nat.mul_comm]

theorem two_pow_ge_succ (r:Nat) : r+1≤2^r := by
  induction r with
  | zero => decide
  | succ r ih =>
      calc
        r+1+1 ≤ 2*(r+1) := by omega
        _ ≤ 2*2^r := Nat.mul_le_mul_left 2 ih
        _ = 2^(r+1) := by rw [Nat.pow_succ]; omega

theorem drain_margin (i r:Nat) (hr:1≤r) :
    2*r ≤ 8*2^i*(2^r-2)+5 := by
  have hp := two_pow_ge_succ r
  have hsub : r-1≤2^r-2 := by omega
  have hi : 1≤2^i := Nat.one_le_pow i 2 (by decide)
  have hmul1 : 8*(r-1) ≤ 8*2^i*(r-1) := by
    calc
      8*(r-1) = 8*(1*(r-1)) := by omega
      _ ≤ 8*(2^i*(r-1)) := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_right (r-1) hi)
      _ = 8*2^i*(r-1) := by simp [Nat.mul_assoc]
  have hmul2 : 8*2^i*(r-1) ≤ 8*2^i*(2^r-2) :=
    Nat.mul_le_mul_left (8*2^i) hsub
  have hbase : 2*r≤8*(r-1)+5 := by omega
  have htotal : 8*(r-1)+5≤8*2^i*(2^r-2)+5 :=
    Nat.add_le_add_right (Nat.le_trans hmul1 hmul2) 5
  exact Nat.le_trans hbase htotal

theorem drain_cond_of_lower (x l i:Nat)
    (hx:4*2^l≤x+l+3) (hi:i<l) :
    2*drainA i+2≤drainB x i := by
  let r := l-i
  have hr : 1≤r := by dsimp [r]; omega
  have hdecomp : l=i+r := by dsimp [r]; omega
  have hpow : 2^l=2^i*2^r := by
    rw [hdecomp, Nat.pow_add]
  have hm := drain_margin i r hr
  have hp := two_pow_ge_succ r
  have hpowi : 1≤2^i := Nat.one_le_pow i 2 (by decide)
  have hpowr : 2≤2^r := Nat.le_trans (by omega) hp
  have hsplit : 2^r=(2^r-2)+2 := by omega
  have hkey : 16*2^i≤8*2^i*2^r-2*r+5 := by
    have hmul : 8*2^i*2^r = 8*2^i*(2^r-2)+16*2^i := by
      calc
        8*2^i*2^r = 8*2^i*((2^r-2)+2) := congrArg (fun q => 8*2^i*q) hsplit
        _ = 8*2^i*(2^r-2)+8*2^i*2 := by rw [Nat.mul_add]
        _ = 8*2^i*(2^r-2)+16*2^i := by omega
    rw [hmul]
    omega
  have hx2 : 8*2^l≤2*x+2*l+6 := by
    have h := Nat.mul_le_mul_left 2 hx
    calc
      8*2^l = 2*(4*2^l) := by omega
      _ ≤ 2*(x+l+3) := h
      _ = 2*x+2*l+6 := by omega
  have hbig : 16*2^i≤2*x+2*i+11 := by
    have hx2' : 8*2^i*2^r≤2*x+2*i+2*r+6 := by
      have htmp := hx2
      rw [hpow] at htmp
      rw [hdecomp] at htmp
      calc
        8*2^i*2^r = 8*(2^i*2^r) := by rw [Nat.mul_assoc]
        _ ≤ 2*x+2*(i+r)+6 := htmp
        _ = 2*x+2*i+2*r+6 := by rw [Nat.mul_add]; omega
    have hbound : 8*2^i*2^r-2*r+5≤2*x+2*i+11 := by
      have h := Nat.sub_le_sub_right hx2' (2*r)
      omega
    exact Nat.le_trans hkey hbound
  have hsub : 8*2^i≤2*x+9+2*i := by
    have hdiff : 8*2^i≤16*2^i-8 := by omega
    omega
  have hB : drainB x i+8*2^i=2*x+9+2*i := by
    unfold drainB
    exact Nat.sub_add_cancel hsub
  have hA : 2*drainA i+2=8*2^i-2 := by
    have hA0 := drainA_plus_two i
    have hp := pow_two_add_two i
    omega
  omega

def drainState (x i:Nat) : State := .C (drainA i) (drainB x i)

theorem drainA_succ (i:Nat) : drainA (i+1)=2*drainA i+2 := by
  have h0 := drainA_plus_two i
  have h1 := drainA_plus_two (i+1)
  have hp : 2^(i+3)=2*2^(i+2) := by rw [Nat.pow_succ]; omega
  have h : drainA (i+1)+2=2*drainA i+4 := by rw [h1, hp, ← h0]; omega
  omega

theorem drainB_succ (x i:Nat) (hcond:2*drainA i+2≤drainB x i) :
    drainB x (i+1)=drainB x i-(2*drainA i+2) := by
  have hA0 := drainA_plus_two i
  have hp := pow_two_add_two i
  have hA : 2*drainA i+2=8*2^i-2 := by omega
  have hsub : 8*2^i≤2*x+9+2*i := by
    unfold drainB at hcond
    omega
  have hBplus : drainB x i+8*2^i=2*x+9+2*i := by
    unfold drainB
    exact Nat.sub_add_cancel hsub
  have hsubNext : 16*2^i≤2*x+11+2*i := by
    have hcond' := Nat.add_le_add_right hcond (8*2^i)
    rw [hA, hBplus] at hcond'
    omega
  have hBnextPlus : drainB x (i+1)+16*2^i=2*x+11+2*i := by
    unfold drainB
    have hpow : 2^(i+1)=2*2^i := by rw [Nat.pow_succ]; omega
    rw [hpow]
    have hnum : 2*x+9+2*(i+1)=2*x+11+2*i := by omega
    have hmul : 8*(2*2^i)=16*2^i := by omega
    rw [hnum, hmul]
    exact Nat.sub_add_cancel hsubNext
  omega

theorem next_drainState (x i:Nat) (hcond:2*drainA i+2≤drainB x i) :
    next (drainState x i)=some (drainState x (i+1)) := by
  have hA := drainA_succ i
  have hB := drainB_succ x i hcond
  have hsplit : drainB x i=(drainB x i-2)+2 := by omega
  have hd : 2*drainA i≤drainB x i-2 := by omega
  change next (.C (drainA i) (drainB x i)) =
    some (.C (drainA (i+1)) (drainB x (i+1)))
  rw [hsplit]
  simp [next, hd]
  rw [hB]
  omega

theorem drain_tail (x l i:Nat) (hx:4*2^l≤x+l+3) (hi:i≤l) :
    Steps (drainState x i) (drainState x l) := by
  by_cases heq:i=l
  · subst l
    exact Steps.refl _
  · have hlt : i<l := by omega
    have hcond := drain_cond_of_lower x l i hx hlt
    have hstep := next_drainState x i hcond
    have htail := drain_tail x l (i+1) hx (by omega)
    exact Steps.step hstep htail
termination_by l-i
decreasing_by omega

theorem drain_path (x l:Nat) (hx:4*2^l≤x+l+3) :
    Steps (.C x 0) (drainState x l) := by
  have hstart : next (.C x 0)=some (drainState x 0) := by
    simp [drainState, drainA, drainB]
  exact Steps.step hstart (drain_tail x l 0 hx (by omega))

theorem low_odd_after_drain (x l c:Nat)
    (hlo:6*2^l+1≤c) (hhi:c≤8*2^l-1)
    (heq:2*c=8*2^l+x+l+5) :
    next (drainState x l)=some (.C (c-3) 2) := by
  have hxlower : 4*2^l≤x+l+3 := by omega
  have hsub : 8*2^l≤2*x+9+2*l := by
    have h := Nat.mul_le_mul_left 2 hxlower
    omega
  have hBplus : drainB x l+8*2^l=2*x+9+2*l := by
    unfold drainB
    exact Nat.sub_add_cancel hsub
  have hBform : drainB x l+24*2^l+1=4*c := by
    omega
  have hAform : drainA l+2=4*2^l := by
    rw [drainA_plus_two, pow_two_add_two]
  have hBlarge : 3≤drainB x l := by omega
  have hBupper : drainB x l≤8*2^l-5 := by omega
  have hBodd : (drainB x l)%2=1 := by
    unfold drainB
    omega
  change next (.C (drainA l) (drainB x l))=some (.C (c-3) 2)
  have hsplit : drainB x l=(drainB x l-2)+2 := by omega
  rw [hsplit]
  have hd : ¬ 2*drainA l≤drainB x l-2 := by omega
  have hdOdd : (drainB x l-2)%2=1 := by omega
  simp [next, hd, hdOdd]
  have hnum : 6*drainA l+(drainB x l-2)+5=4*(c-3)+2 := by
    have hA' : drainA l=4*2^l-2 := by omega
    omega
  rw [hnum]
  omega

theorem low_even_after_drain (x l u:Nat)
    (hlo:6*2^l-1≤u) (hhi:u≤8*2^l-3)
    (heq:2*u=8*2^l+x+l) :
    next (drainState x l)=some (.C u 0) := by
  have hxlower : 4*2^l≤x+l+3 := by omega
  have hsub : 8*2^l≤2*x+9+2*l := by
    have h := Nat.mul_le_mul_left 2 hxlower
    omega
  have hBplus : drainB x l+8*2^l=2*x+9+2*l := by
    unfold drainB
    exact Nat.sub_add_cancel hsub
  have hBform : drainB x l+24*2^l=4*u+9 := by
    omega
  have hAform : drainA l+2=4*2^l := by
    rw [drainA_plus_two, pow_two_add_two]
  have hBlarge : 5≤drainB x l := by omega
  have hBupper : drainB x l≤8*2^l-3 := by omega
  have hBodd : (drainB x l)%2=1 := by
    unfold drainB
    omega
  change next (.C (drainA l) (drainB x l))=some (.C u 0)
  have hsplit : drainB x l=(drainB x l-2)+2 := by omega
  rw [hsplit]
  have hd : ¬ 2*drainA l≤drainB x l-2 := by omega
  have hdOdd : (drainB x l-2)%2=1 := by omega
  simp [next, hd, hdOdd]
  have hnum : 6*drainA l+(drainB x l-2)+5=4*u := by
    have hA' : drainA l=4*2^l-2 := by omega
    omega
  rw [hnum]
  omega

end Agent7HighLevel746
