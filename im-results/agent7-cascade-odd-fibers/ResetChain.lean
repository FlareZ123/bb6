import SourceMacro
import CascadeOdd

namespace CascadeChain
open CascadeSource

def A (k : Nat) : Nat := 4*2^k-2
def B (h k : Nat) : Nat := 2*h+2*k+9-8*2^k

theorem AB0 (h : Nat) : A 0 = 2 ∧ B h 0 = 2*h+1 := by
  simp [A,B]

theorem A_pos (k : Nat) : 2 ≤ A k := by
  have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
  dsimp [A]
  omega

theorem Cstep_large (a b : Nat) (hb : 2 ≤ b)
    (hd : 2*a ≤ b-2) :
    Cstep a b = some (2*a+2,b-2-2*a) := by
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have h : 2*a≤d := by omega
  simp [Cstep,h]

theorem cascade_one (h k : Nat) (hh : 8*2^k ≤ h) :
    Cstep (A k) (B h k) = some (A (k+1),B h (k+1)) := by
  have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
  have hA : A k+2=4*2^k := by dsimp [A]; omega
  have hB : B h k+8*2^k=2*h+2*k+9 := by dsimp [B]; omega
  have hb : 2≤B h k := by omega
  have hd : 2*(A k) ≤ B h k-2 := by omega
  rw [Cstep_large (A k) (B h k) hb hd]
  have hpow : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
  have ha2 : 2*(A k)+2=A (k+1) := by dsimp [A]; omega
  have hb2 : B h k-2-2*(A k)=B h (k+1) := by dsimp [B]; omega
  rw [ha2,hb2]

theorem cascade_run (h m : Nat) (hh : ∀ k<m,8*2^k≤h) :
    Reach (.C h 0) (.C (A m) (B h m)) := by
  have hbase : Reach (.C h 0) (.C (A 0) (B h 0)) := by
    rw [(AB0 h).1,(AB0 h).2]
    exact Reach.one rfl
  induction m with
  | zero => exact hbase
  | succ m ih =>
    have hm : Reach (.C h 0) (.C (A m) (B h m)) := ih (by
      intro k hk; exact hh k (by omega))
    exact hm.trans (C_step_sound (A m) (B h m) (A (m+1)) (B h (m+1))
      (cascade_one h m (hh m (by omega))))

theorem cascade_run_bound (h m : Nat) (hm : 1 ≤ m)
    (hh : 8*2^(m-1)≤h) :
    Reach (.C h 0) (.C (A m) (B h m)) := by
  apply cascade_run
  intro k hk
  have hpow : 2^k ≤ 2^(m-1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem Cstep_two_odd (q : Nat) (hq : 2 ≤ q) :
    Cstep (2*q-3) 2 = some (3*q-3, 2) := by
  have ha : 2*q-3 ≥ 1 := by omega
  have htwo : ¬(2*(2*q-3) ≤ 0) := by omega
  have hx : 6*(2*q-3)+8 = 4*(3*q-3)+2 := by omega
  simp only [Cstep, if_false (by decide : ¬(2=0)),
    if_false (by decide : ¬(2=1))]
  simp [htwo]
  omega

theorem Cstep_two_even (q : Nat) (hq : 2 ≤ q) (hodd : q % 2 = 1) :
    Cstep (3*q-3) 2 = some ((9*q-5)/2, 0) := by
  have ha : 3*q-3 ≥ 1 := by omega
  have htwo : ¬(2*(3*q-3) ≤ 0) := by omega
  have hx : 6*(3*q-3)+8 = 4*((9*q-5)/2) := by omega
  simp only [Cstep, if_false (by decide : ¬(2=0)),
    if_false (by decide : ¬(2=1))]
  simp [htwo]
  omega

theorem odd_tail (q : Nat) (hq : 2 ≤ q) (hodd : q%2=1) :
    Reach (.C (2*q-3) 2) (.C ((9*q-5)/2) 0) := by
  have h1 := C_step_sound (2*q-3) 2 (3*q-3) 2 (Cstep_two_odd q hq)
  have h2 := C_step_sound (3*q-3) 2 ((9*q-5)/2) 0
    (Cstep_two_even q hq hodd)
  exact h1.trans h2

theorem Cstep_underflow_odd (a b y : Nat)
    (hb : 2 ≤ b) (hsmall : b-2 < 2*a)
    (hodd : (b-2)%2=1)
    (hval : 6*a+(b-2)+5=4*y) :
    Cstep a b = some (y,0) := by
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have hn : ¬(2*a≤d) := by omega
  have ht : d%2=1 := by omega
  simp [Cstep,hn,ht]
  omega

theorem even_return (m p x y : Nat) (hm : 1 ≤ m)
    (hp : p=2^m)
    (hx : 6*p-1 ≤ x) (hy : y ≤ 8*p-3)
    (hr : x+8*p+m=2*y) :
    Reach (.C x 0) (.C y 0) := by
  have hpos : 1 ≤ p := by rw [hp]; exact Nat.one_le_pow _ _ (by decide)
  have hp2 : p=2*2^(m-1) := by
    calc
      p = 2^m := hp
      _ = 2^((m-1)+1) := by congr 1 <;> omega
      _ = 2*2^(m-1) := by rw [Nat.pow_succ]; omega
  have hprior : 8*2^(m-1)≤x := by omega
  have hrun := cascade_run_bound x m hm hprior
  have ha : A m=4*p-2 := by dsimp [A]; rw [←hp]
  have hb : B x m=2*x+2*m+9-8*p := by dsimp [B]; rw [←hp]
  have hB2 : 2 ≤ B x m := by omega
  have hsmall : B x m-2 < 2*(A m) := by omega
  have hodd : (B x m-2)%2=1 := by omega
  have hval : 6*(A m)+(B x m-2)+5=4*y := by omega
  have he := Cstep_underflow_odd (A m) (B x m) y hB2 hsmall hodd hval
  exact hrun.trans (C_step_sound (A m) (B x m) y 0 he)

theorem Cstep_underflow_odd_remtwo (u b v : Nat)
    (hb : 2 ≤ b) (hsmall : b-2 < 2*u)
    (hodd : (b-2)%2=1)
    (hval : 6*u+(b-2)+5=4*v+2) :
    Cstep u b = some (v,2) := by
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have hn : ¬(2*u≤d) := by omega
  have ht : d%2=1 := by omega
  simp [Cstep,hn,ht]
  omega

/-- An exact uniform source reset exit of the valuation-one odd branch. -/
theorem odd_return (m p r a h q : Nat)
    (hm : 1 ≤ m) (hr : r=2^m) (hp : p=2*r)
    (hh : 2*p≤h) (ha0 : 3*p-2≤a) (ha1 : a≤4*p-4)
    (hheq : h+4*p+m+2=2*a+3)
    (haeq : a+3=2*q) (hodd : q%2=1) :
    Reach (.C h 0) (.C ((9*q-5)/2) 0) := by
  have hpow : r=2*2^(m-1) := by
    calc
      r=2^m := hr
      _=2^((m-1)+1) := by congr 1 <;> omega
      _=2*2^(m-1) := by rw [Nat.pow_succ]; omega
  have hprior : 8*2^(m-1)≤h := by omega
  have hrun := cascade_run_bound h m hm hprior
  have hA : A m=2*p-2 := by dsimp [A]; rw [←hr]; omega
  have hB : B h m=4*a+11-12*p := by
    dsimp [B]
    rw [←hr]
    omega
  have hpos : 2≤p := by
    have : 1≤r := by rw [hr]; exact Nat.one_le_pow _ _ (by decide)
    omega
  have hA0 : 2≤A m := A_pos m
  have hb : 2≤B h m := by omega
  have hsmall : B h m-2 < 2*(A m) := by omega
  have hoddB : (B h m-2)%2=1 := by omega
  have hval : 6*(A m)+(B h m-2)+5=4*a+2 := by omega
  have he := Cstep_underflow_odd_remtwo (A m) (B h m) a hb hsmall hoddB hval
  have hstep := C_step_sound (A m) (B h m) a 2 he
  have hq : 2≤q := by omega
  have ha : 2*q-3=a := by omega
  have htail := odd_tail q hq hodd
  rw [ha] at htail
  exact (hrun.trans hstep).trans htail

theorem odd_height (n p a h j : Nat) (hn : 10≤n)
    (hp : 31*(2*n+3) ≤ 2*p) (hj : j≤4)
    (hd : CascadeOdd.Q p n j %9=0)
    (he : h+4*p+n=2*a+3)
    (ha : a+3=2*(CascadeOdd.Q p n j/9)) : 2*p≤h := by
  have hbound := CascadeOdd.Q_bounds p n j hn hp hj
  have hq : 9*(CascadeOdd.Q p n j/9)=CascadeOdd.Q p n j := by omega
  omega

theorem descend (n j : Nat) (hn : 10≤n) (hj : j≤4) :
    Reach (.C (CascadeOdd.ancestor (2^(n-1)) n j) 0)
      (.C (CascadeOdd.ancestor (2^(n-1)) n 0) 0) := by
  induction j with
  | zero => exact Reach.refl _
  | succ j ih =>
    have hj0 : j<4 := by omega
    have hj1 : j+1≤4 := by omega
    let p:=2^(n-1)
    have hpb := CascadeOdd.p_bound n hn
    have hb := CascadeOdd.ancestor_bounds p n (j+1) hn hpb hj1
    have hc := CascadeOdd.even_chain p n j hn hpb hj0
    have hrel : CascadeOdd.ancestor p n (j+1)+8*p+(n-1) =
        2*CascadeOdd.ancestor p n j := by
      have := hc.2.2
      omega
    have hstep := even_return (n-1) p
      (CascadeOdd.ancestor p n (j+1)) (CascadeOdd.ancestor p n j)
      (by omega) rfl hb.1 hc.2.1 hrel
    exact hstep.trans (ih (by omega))

/-- True-source C/P reachability of every *synthetic* odd-family fatal height, n>=10. -/
theorem universal_odd_source (n : Nat) (hn : 10≤n)
    (hc : n%6=4 ∨ n%6=5) :
    ∃ h, Reach (.C h 0)
      (.C (CascadeOdd.ancestor (2^(n-1)) n 0) 0) := by
  obtain ⟨j,hj,hmod⟩ := CascadeOdd.mod_open n hc
  have hj4 : j≤4 := by rcases hj with h0|h2|h4 <;> omega
  let p:=2^(n-1)
  have hpb := CascadeOdd.p_bound n hn
  have hd:= CascadeOdd.Q_mod9_zero n j hn hj4 hmod
  obtain ⟨a,h,ha0,ha1,hheq,haeq,hodd,hout⟩ :=
    CascadeOdd.odd_gate p n j hn hpb hj4 hd
  let q:=CascadeOdd.Q p n j/9
  have hheight : 2*p≤h := odd_height n p a h j hn hpb hj4 hd hheq haeq
  let m:=n-2
  let r:=2^m
  have hm : 1≤m := by dsimp [m];omega
  have hpr : p=2*r := by
    dsimp [p,r,m]
    have : n-1=(n-2)+1 := by omega
    rw [this,Nat.pow_succ]
    omega
  have hrel : h+4*p+m+2=2*a+3 := by dsimp [m]; omega
  have hsource : Reach (.C h 0) (.C ((9*q-5)/2) 0) :=
    odd_return m p r a h q hm rfl hpr hheight ha0 ha1 hrel haeq hodd
  have heq : (9*q-5)/2=CascadeOdd.ancestor p n j := by
    have hal : (a+3)/2=q := by dsimp [q]; omega
    rw [←hal]
    exact hout
  rw [heq] at hsource
  exact ⟨h,hsource.trans (descend n j hn hj4)⟩

theorem small4 : Reach (.C 13 0) (.C 56 0) := by
  exact (C_step_sound 13 0 2 27 (by decide)).trans
    ((C_step_sound 2 27 6 21 (by decide)).trans
    ((C_step_sound 6 21 14 7 (by decide)).trans
    ((C_step_sound 14 7 23 2 (by decide)).trans
    ((C_step_sound 23 2 36 2 (by decide)).trans
      (C_step_sound 36 2 56 0 (by decide))))))

theorem small5 : Reach (.C 36 0) (.C 119 0) := by
  exact (C_step_sound 36 0 2 73 (by decide)).trans
    ((C_step_sound 2 73 6 67 (by decide)).trans
    ((C_step_sound 6 67 14 53 (by decide)).trans
    ((C_step_sound 14 53 30 23 (by decide)).trans
    ((C_step_sound 30 23 51 2 (by decide)).trans
    ((C_step_sound 51 2 78 2 (by decide)).trans
      (C_step_sound 78 2 119 0 (by decide)))))))

theorem ancestor_is_fatal (n : Nat) (hn : 1≤n) :
    CascadeOdd.ancestor (2^(n-1)) n 0 = 4*2^n-n-4 := by
  have hp : 2^n=2*2^(n-1) := by
    calc
      2^n = 2^((n-1)+1) := by congr 1 <;> omega
      _ = 2*2^(n-1) := by rw [Nat.pow_succ];omega
  have hp4 : 1 ≤ 2^(n-1) := Nat.one_le_pow _ _ (by decide)
  dsimp [CascadeOdd.ancestor]
  omega

/-- Every complementary target has a source-next-reachable synthetic reset ancestor. -/
theorem all_complementary_source_reachable (n : Nat)
    (hn : 4≤n) (hc : n%6=4 ∨ n%6=5) :
    ∃ h, Reach (.C h 0) (.C (4*2^n-n-4) 0) := by
  by_cases hn10 : 10≤n
  · obtain ⟨h,hs⟩ := universal_odd_source n hn10 hc
    rw [ancestor_is_fatal n (by omega)] at hs
    exact ⟨h,hs⟩
  · have hh : n=4 ∨ n=5 := by omega
    rcases hh with rfl|rfl
    · exact ⟨13,by simpa using small4⟩
    · exact ⟨36,by simpa using small5⟩

#print axioms all_complementary_source_reachable

#print axioms cascade_run
#print axioms odd_tail
end CascadeChain
