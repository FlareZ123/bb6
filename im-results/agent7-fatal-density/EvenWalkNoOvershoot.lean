import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

/-!
# Uniform #746 second-tier inverse gap
The source arithmetic below forces an admissible second-tier even inverse
walk to leave its dyadic image band at step 2, 3 or 4, for all n >= 40.
These algebraic preconditions still require an explicit original-root bridge.
-/

namespace Growth
private def F (n:Nat):Nat := 4*n*n + 8*n
private theorem F_succ (n:Nat):F (n+1)=F n+8*n+12:=by
  simp only [F,Nat.mul_add,Nat.add_mul]
  omega
private theorem F_growth (n:Nat) (hn:40≤n):F (n+1)≤2*F n:=by
  have hm:40*n≤n*n := Nat.mul_le_mul_right n hn
  have hm4:= Nat.mul_le_mul_left 4 hm
  have ha : 8*n+12≤F n:=by
    dsimp [F]
    rw [show 4*n*n=4*(n*n) by ac_rfl]
    omega
  rw [F_succ]
  omega
private theorem F_eq (n:Nat):F n=2*n*(2*n+3)+2*n:=by
  dsimp [F]
  grind
private theorem exp_quad_aux (t : Nat) :
    F (t+40) < 2^(t+27) := by
  induction t with
  | zero => decide
  | succ t ih =>
      have hh :F (t+40+1)≤2*F (t+40) :=
        F_growth (t+40) (by omega)
      have he : t+1+40=t+40+1:=by omega
      have he2 : 2^(t+1+27)=2*2^(t+27):=by
        rw [show t+1+27=t+27+1 by omega, Nat.pow_succ]
        omega
      rw [he,he2]
      omega
theorem exp_quad (n:Nat) (hn:40≤n) :
    2*n*(2*n+3)+2*n < 2^(n-13) := by
  have hnval : n=(n-40)+40 := by omega
  have hh:=exp_quad_aux (n-40)
  have hk : n-13=(n-40)+27 := by omega
  rw [F_eq] at hh
  rw [←hnval,←hk] at hh
  exact hh
#print axioms exp_quad
end Growth

namespace GapNumber
theorem near_power_impossible (n j e c δ : Nat)
    (hquad : 2*n*(2*n+3)+2*n < 2^e)
    (hc : 1≤c) (hδ0 : 0<δ) (hδsmall : δ<2*n)
    (hnear : c*2^e = 2^j*(2*n+3)+δ) : False := by
  have hjlarge : 2*n<2^j := by
    by_cases h : 2*n<2^j
    · exact h
    · have hsmall:2^j≤2*n := by omega
      have hm := Nat.mul_le_mul_right (2*n+3) hsmall
      have hcT := Nat.mul_le_mul_right (2^e) hc
      omega
  have hepos : 0<2^e := Nat.pow_pos (by decide)
  have hjpos : 0<2^j := Nat.pow_pos (by decide)
  by_cases hje : j≤e
  · have hexp : e=j+(e-j) := by omega
    have hp : 2^e=2^j*2^(e-j) := by
      calc
        2^e = 2^(j+(e-j)) := congrArg (fun x:Nat => 2^x) hexp
        _ = 2^j*2^(e-j) := Nat.pow_add 2 j (e-j)
    have hdT : 2^j ∣ c*2^e := by
      rw [hp]
      refine ⟨c*2^(e-j),?_⟩
      ac_rfl
    have hdM : 2^j ∣ 2^j*(2*n+3) := ⟨2*n+3,rfl⟩
    have hd : 2^j∣δ := by
      have hdiff : c*2^e - 2^j*(2*n+3)=δ := by omega
      rw [←hdiff]
      exact Nat.dvd_sub hdT hdM
    have hle := Nat.le_of_dvd hδ0 hd
    omega
  · have hej : e≤j := by omega
    have hexp : j=e+(j-e) := by omega
    have hp : 2^j=2^e*2^(j-e) := by
      calc
        2^j = 2^(e+(j-e)) := congrArg (fun x:Nat => 2^x) hexp
        _ = 2^e*2^(j-e) := Nat.pow_add 2 e (j-e)
    have hdT : 2^e ∣ c*2^e := ⟨c,by ac_rfl⟩
    have hdM : 2^e ∣ 2^j*(2*n+3) := by
      rw [hp]
      refine ⟨2^(j-e)*(2*n+3),?_⟩
      ac_rfl
    have hd : 2^e∣δ := by
      have hdiff : c*2^e - 2^j*(2*n+3)=δ := by omega
      rw [←hdiff]
      exact Nat.dvd_sub hdT hdM
    have hle := Nat.le_of_dvd hδ0 hd
    omega
#print axioms near_power_impossible

private theorem three_proximity (n B p M T:Nat) (hn:40≤n)
 (hmodel:81*B+3=16*p+128*M+169*n)
 (hT:1024*T=196*p)
 (hprev:4*B+3*(n-4)≤2*p+1)
 (hbad:4*p+3≤8*B+7*(n-4)):
  0<T-M ∧ T-M<2*n := by
  grind
private theorem four_proximity (n B p M T:Nat) (hn:40≤n)
 (hmodel:81*B+3=16*p+128*M+169*n)
 (hT:2048*T=68*p)
 (hprev:8*B+7*(n-4)≤2*p+1)
 (hbad:4*p+3≤16*B+15*(n-4)):
  0<T-M ∧ T-M<2*n := by
  grind
private theorem pow_scale_three (n:Nat) (hn:12≤n):
    2^(n-4)=256*2^(n-12) := by
  have h:n-4=(n-12)+8:=by omega
  calc
   2^(n-4)=2^((n-12)+8):=congrArg (fun x:Nat=>2^x) h
   _=2^(n-12)*2^8:=Nat.pow_add 2 (n-12) 8
   _=256*2^(n-12):=by simp;omega
private theorem pow_scale_four (n:Nat) (hn:13≤n):
    2^(n-4)=512*2^(n-13) := by
  have h:n-4=(n-13)+9:=by omega
  calc
   2^(n-4)=2^((n-13)+9):=congrArg (fun x:Nat=>2^x) h
   _=2^(n-13)*2^9:=Nat.pow_add 2 (n-13) 9
   _=512*2^(n-13):=by simp;omega
private theorem exp_quad_three (n:Nat) (hn:40≤n):
    2*n*(2*n+3)+2*n < 2^(n-12) := by
  have h := Growth.exp_quad n hn
  have he:n-12=(n-13)+1:=by omega
  rw [he,Nat.pow_succ]
  omega

theorem no_three_overshoot (n j B:Nat) (hn:40≤n)
  (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hprev:4*B+3*(n-4)≤2*2^(n-4)+1)
  (hbad:4*2^(n-4)+3≤8*B+7*(n-4)) : False := by
  let p:=2^(n-4)
  let M:=2^j*(2*n+3)
  let T:=49*2^(n-12)
  have hp := pow_scale_three n (by omega)
  have hT : 1024*T=196*p := by
    dsimp [T,p]
    rw [hp]
    omega
  have hmodel':81*B+3=16*p+128*M+169*n:=hmodel
  have hprev':4*B+3*(n-4)≤2*p+1:=hprev
  have hbad':4*p+3≤8*B+7*(n-4):=hbad
  have ⟨hpositive,hbound⟩ := three_proximity n B p M T hn hmodel' hT hprev' hbad'
  have hs : T=M+(T-M) := by omega
  exact near_power_impossible n j (n-12) 49 (T-M)
    (exp_quad_three n hn) (by decide) hpositive hbound hs

theorem no_four_overshoot (n j B:Nat) (hn:40≤n)
  (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hprev:8*B+7*(n-4)≤2*2^(n-4)+1)
  (hbad:4*2^(n-4)+3≤16*B+15*(n-4)) : False := by
  let p:=2^(n-4)
  let M:=2^j*(2*n+3)
  let T:=17*2^(n-13)
  have hp := pow_scale_four n (by omega)
  have hT : 2048*T=68*p := by
    dsimp [T,p]
    rw [hp]
    omega
  have hmodel':81*B+3=16*p+128*M+169*n:=hmodel
  have hprev':8*B+7*(n-4)≤2*p+1:=hprev
  have hbad':4*p+3≤16*B+15*(n-4):=hbad
  have ⟨hpositive,hbound⟩ := four_proximity n B p M T hn hmodel' hT hprev' hbad'
  have hs : T=M+(T-M) := by omega
  exact near_power_impossible n j (n-13) 17 (T-M)
    (Growth.exp_quad n hn) (by decide) hpositive hbound hs

/-- A uniform bound, with all dyadic arithmetic and exceptional power
    windows proved in Lean, for any source-typed symbolic second-tier
    inverse ray and every n>=40. -/
theorem uniform_two_four_gap (n j B:Nat) (hn:40≤n)
  (hmodel:81*B+3=16*2^(n-4)+128*(2^j*(2*n+3))+169*n)
  (hweak:2*(2^j*(2*n+3))+2*n+10≤2^(n-4))
  :
  let p:=2^(n-4)
  let k:=n-4
  let B2:=4*B+3*k
  let B3:=8*B+7*k
  let B4:=16*B+15*k
  (2*p+1<B2 ∧ B2<4*p+3) ∨
  (B2≤2*p+1 ∧ 2*p+1<B3 ∧ B3<4*p+3) ∨
  (B3≤2*p+1 ∧ 2*p+1<B4 ∧ B4<4*p+3) := by
  let p:=2^(n-4)
  let k:=n-4
  let M:=2^j*(2*n+3)
  let B2:=4*B+3*k
  let B3:=8*B+7*k
  let B4:=16*B+15*k
  have hquad:=Growth.exp_quad n hn
  have hpval:=pow_scale_four n (by omega)
  have hnq:n<2^(n-13):=by
    have h:n≤2*n*(2*n+3)+2*n:=by omega
    omega
  have hbig:512*n<p:=by
    dsimp[p]
    rw[hpval]
    omega
  have hmodel':81*B+3=16*p+128*M+169*n:=hmodel
  have hweak':2*M+2*n+10≤p:=hweak
  have hB2:B2<4*p+3:=by
    dsimp [B2,k]
    grind
  have hB4:2*p+1<B4:=by
    dsimp [B4,k]
    grind
  by_cases h2:2*p+1<B2
  · exact Or.inl ⟨h2,hB2⟩
  · have h2le:B2≤2*p+1:=by omega
    have hB3:B3<4*p+3:=by
      by_cases h: B3<4*p+3
      · exact h
      · have hbad:4*2^(n-4)+3≤8*B+7*(n-4):=by
          dsimp[B3,k,p] at h
          omega
        exact False.elim (no_three_overshoot n j B hn hmodel
          (by simpa [B2,p,k] using h2le) hbad)
    by_cases h3:2*p+1<B3
    · exact Or.inr (Or.inl ⟨h2le,h3,hB3⟩)
    · have h3le:B3≤2*p+1:=by omega
      have hB4upper:B4<4*p+3:=by
        by_cases h:B4<4*p+3
        · exact h
        · have hbad:4*2^(n-4)+3≤16*B+15*(n-4):=by
            dsimp[B4,k,p] at h
            omega
          exact False.elim (no_four_overshoot n j B hn hmodel
            (by simpa [B3,p,k] using h3le) hbad)
      exact Or.inr (Or.inr ⟨h3le,hB4,hB4upper⟩)

#print axioms uniform_two_four_gap
#print axioms no_three_overshoot
#print axioms no_four_overshoot
end GapNumber
