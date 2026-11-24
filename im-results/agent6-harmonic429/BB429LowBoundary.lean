import BB429LowReturnBand
import Lean.Elab.Tactic.Omega

namespace BB429.LowBoundary
open BB429.LowReturnBand

private theorem period_mod (m j : Nat) :
    16^m % (16^(j+1)-1) = 16^(m%(j+1)) % (16^(j+1)-1) := by
  let p := j+1
  let M := 16^p-1
  let r := m%p
  let q := m/p
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hM : 15 ≤ M := by
    have h := Nat.pow_le_pow_right (n:=16) (by decide) hp
    dsimp [M]
    change 16 ≤ 16^p at h
    omega
  have hbase : 16^p%M=1 := by
    have h : 16^p=M+1 := by dsimp [M]; omega
    rw [h,Nat.add_mod,Nat.mod_self]
    simp [Nat.mod_eq_of_lt (show 1<M by omega)]
  have hpow : 16^m=16^r*(16^p)^q := by
    calc
      16^m = 16^(r+p*q) := congrArg (fun x : Nat => 16^x) (Nat.mod_add_div m p).symm
      _ = 16^r*(16^p)^q := by rw [Nat.pow_add,Nat.pow_mul]
  change 16^m%M=16^r%M
  rw [hpow,Nat.mul_mod,Nat.pow_mod (16^p) q M,hbase]
  simp [Nat.mod_eq_of_lt (show 1<M by omega)]

private theorem linear_le (j : Nat) (hj : 1 ≤ j) : 24*j ≤ 2*16^j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : 1≤j
    · have h' := ih h
      have hp : 0 < 16^j := Nat.pow_pos (by decide)
      rw [Nat.pow_succ]
      omega
    · have h' : j=0 := by omega
      subst j
      decide

/-- No scale or number of complete low-side cycles can reach the direct
    Oe,F halting boundary. The Diophantine equation is impossible. -/
theorem no_low_equation (m j d : Nat) :
    d*(16^(j+1)-1)+18 ≠ 72*16^m+24*j := by
  intro h
  let M := 16^(j+1)-1
  let r := m%(j+1)
  have hr : r < j+1 := Nat.mod_lt _ (by omega)
  have hres : (72*16^r+24*j)%M=18%M := by
    have hpow := period_mod m j
    change 16^m%M=16^r%M at hpow
    have h' : (d*M+18)%M=(72*16^m+24*j)%M := congrArg (fun a : Nat => a%M) h
    rw [Nat.mul_comm d M,Nat.mul_add_mod] at h'
    calc
      (72*16^r+24*j)%M = (72*16^m+24*j)%M := by
        rw [Nat.add_mod (72*16^r),Nat.add_mod (72*16^m),Nat.mul_mod 72 (16^r),Nat.mul_mod 72 (16^m),hpow]
      _ = 18%M := h'.symm
  cases j with
  | zero =>
    have hr0 : r=0 := by omega
    have hM : M=15 := rfl
    rw [hr0,hM] at hres
    contradiction
  | succ j =>
    let X := 16^(j+1)
    have hX : 16 ≤ X := by
      exact Nat.pow_le_pow_right (n:=16) (by decide) (show 1≤j+1 by omega)
    have hM : M=16*X-1 := by
      dsimp [M,X]
      rw [Nat.pow_succ, Nat.mul_comm (16^(j+1)) 16]
    have hlin : 24*(j+1) ≤ 2*X := linear_le (j+1) (by omega)
    have h18 : 18%M=18 := Nat.mod_eq_of_lt (by omega)
    rw [h18] at hres
    by_cases hlt : r<j+1
    · have hp : 16^r ≤ 16^j := Nat.pow_le_pow_right (by decide) (by omega)
      have hx : X=16*16^j := by dsimp [X]; rw [Nat.pow_succ,Nat.mul_comm (16^j) 16]
      have hb : 72*16^r+24*(j+1)<M := by omega
      rw [Nat.mod_eq_of_lt hb] at hres
      have hpos : 0 < 16^r := Nat.pow_pos (by decide)
      omega
    · have he : r=j+1 := by omega
      rw [he] at hres
      change (72*X+24*(j+1))%M=18 at hres
      have hb : 8*X+24*(j+1)+4<M := by omega
      have hsplit : 72*X+24*(j+1)=(8*X+24*(j+1)+4)+M*4 := by omega
      rw [hsplit,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hb] at hres
      omega

/-- The coordinates after Oe,F have a unique immediate halting line. -/
theorem no_direct_boundary (m j d u : Nat)
    (hcoord : 72*16^m+d+24*j = 3*u+d*16^j+9) :
    u ≠ 5*(d*16^j)+3 := by
  intro h
  apply no_low_equation m j d
  have he : d*(16^(j+1)-1)+d=16*(d*16^j) := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_one,Nat.pow_succ,← Nat.mul_assoc]
    rw [Nat.mul_comm (d*16^j) 16]
    have hle : d ≤ 16*(d*16^j) := by
      have h1 := Nat.le_mul_of_pos_right d (Nat.pow_pos (a:=16) (n:=j) (by decide))
      omega
    omega
  omega

private theorem stepF (u w : Nat) (h : 2*u+3 ≤ w) :
    next (u,w) = some (2*u+3,w-2*u-3) := by simp [next,h]

private theorem stepOe (u w : Nat) (h : w+1 < 2*u)
    (hw : w%2=1) (hd : 4 ≤ u-w/2) (he : (u-w/2)%2=0)
    (hw1 : 1 < w) :
    next (u,w) = some (u-w/2+7,2*w-4) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h4 : w%2 ≠ 0 := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : u-w/2 ≠ 2 := by omega
  have h7 : w ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,h4,h5,h6,he,h7]

theorem cycles_to_boundary (j u0 d0 u : Nat) (hd : 6 ≤ d0) (he : d0%2=0)
    (hp : (u0+1)%4=d0%4)
    (hcoord : 3*u0+d0+24*j = 3*u+d0*16^j)
    (hu : 15 ≤ u) :
    run (4*j) (phase u0 d0) = some (phase u (d0*16^j)) ∧
    (u+1)%4=(d0*16^j)%4 ∧ (d0*16^j)%2=0 := by
  induction j generalizing u with
  | zero =>
    simp only [Nat.pow_zero,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at hcoord ⊢
    have h : u=u0 := by omega
    subst u
    exact ⟨rfl,hp,he⟩
  | succ j ih =>
    let D := d0*16^j
    have hD : 6 ≤ D := by
      have h := Nat.le_mul_of_pos_right d0 (Nat.pow_pos (a:=16) (n:=j) (by decide))
      omega
    have hpow : d0*16^(j+1)=16*D := by
      simp only [Nat.pow_succ, D]
      rw [← Nat.mul_assoc, Nat.mul_comm (d0 * 16^j) 16]
    rw [hpow] at hcoord ⊢
    let v := u+5*D-8
    have hv : 5*D+7 ≤ v := by dsimp [v]; omega
    have hcv : 3*u0+d0+24*j=3*v+D := by dsimp [v]; omega
    obtain ⟨hr,hp',he'⟩ := ih v hcv (by omega)
    have hcy := cycle v D hD he' hp' hv
    have hve : v+8-5*D=u := by dsimp [v]; omega
    rw [hve] at hcy
    refine ⟨?_,?_,by omega⟩
    · rw [show 4*(j+1)=4*j+4 by omega,run_add,hr]
      exact hcy
    · have h := cycle_phase v D hp' hv
      simpa [hve] using h

theorem two_step (u d : Nat) (hd : 6 ≤ d) (he : d%2=0)
    (hp : (u+1)%4=d%4) (hu : d+19 ≤ u) :
    run 2 (phase u d) = some (u+6-d,u+14+3*d) := by
  have h1 : next (phase u d) = some ((u+3-d)/2, 2*u+20+2*d) := by
    unfold phase
    rw [stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h2 : next ((u+3-d)/2, 2*u+20+2*d) = some (u+6-d,u+14+3*d) := by
    rw [stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2]

private theorem scale_ge (m : Nat) : 16*m ≤ 16^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have h : 0 < 16^m := Nat.pow_pos (by decide)
    omega

/-- Every reachable direct Oe,F boundary of the low-side scale family
    is nonhalting. This does not exclude halting in a later F burst. -/
theorem zero_boundary (m j d u : Nat) (hm : 1 ≤ m)
    (hd : 6 ≤ d) (hp : d%4=2)
    (hcoord : 72*16^m+d+24*j=3*u+d*16^j+9)
    (hu : d*16^j+19 ≤ u) :
    run (4*m+3+4*j+2) (0,72*16^m+d-(12*m+6)) =
      some (u+6-d*16^j,u+14+3*(d*16^j)) ∧
    next (u+6-d*16^j,u+14+3*(d*16^j)) ≠ none := by
  let X := 16^m
  let a := 24*X-3
  let W := 72*X+d-(12*m+6)
  let D := d*16^j
  have hX : 16*m ≤ X := scale_ge m
  have hD : 6 ≤ D := by
    have h := Nat.le_mul_of_pos_right d (Nat.pow_pos (a:=16) (n:=j) (by decide))
    omega
  have hpow : 2^(4*m+3)=8*X := by
    rw [Nat.pow_add,Nat.pow_mul]
    change 16^m*8=8*X
    exact Nat.mul_comm _ _
  have ha : a+3=3*2^(4*m+3) := by rw [hpow]; dsimp [a]; omega
  have hr : 3*a+12+d=W+3*(4*m+3) := by dsimp [a,W]; omega
  have hburst : run (4*m+3) (0,W)=some (phase a d) := by
    apply zero_burst _ _ _ _ ha
    omega
  have hc : 3*a+d+24*j=3*u+D := by dsimp [a]; omega
  obtain ⟨hcy,hp',he'⟩ := cycles_to_boundary j a d u hd (by omega)
    (by dsimp [a]; omega) hc (by omega)
  have ht := two_step u D hD he' hp' hu
  refine ⟨?_,?_⟩
  · rw [run_add,run_add,hburst]
    simp only [Option.bind_some]
    rw [hcy]
    exact ht
  · intro hn
    have hh := (next_none_iff_halt_line _ _).mp hn
    apply no_direct_boundary m j d u hcoord
    omega

#print axioms zero_boundary
#print axioms no_low_equation
#print axioms no_direct_boundary
end BB429.LowBoundary
