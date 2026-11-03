import UpperTail
import InverseIff
import OneResetWall

namespace BB6.Agent45OneResetSource
open BB6.Agent1UpperTail
open BB6.Agent1Quarter
open BB6.Agent47P1
open BB6.Agent45OneReset

/-- Source-correct conservation law on any genuine depth-zero inverse tail. -/
theorem tail_mass (b0 d0 m0 b d m h : Nat)
    (p : UpperTail b0 d0 m0 b d m h) :
    b+d+2*m=b0+d0+2*m0 := by
  induction p with
  | root => omega
  | step b d m h k c p hb hb4 hd hi hk hc ih =>
    have he := inverseAt_odd_cost b d 0 k c (by omega) hb4 hd hi hc
    omega

/-- All actual inverse histories from the critical root with exactly one
    positive-depth nesting edge, surrounded by any number of depth-zero
    inverse edges, avoid the authentic critical affine wall. -/
theorem source_one_reset_no_wall
    (n r t h bp dp k c b d m : Nat)
    (hn : 30≤n)
    (hp : 512*n*n*n≤2^n)
    (hpre : UpperTail (14*2^n-2*n-16) 3 0 bp dp r r)
    (hb : 8≤bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (ht : 1≤t) (hk : 2≤k) (hc : c%2=1)
    (hpost : UpperTail (2*k-4) (c+4) (r+t+1) b d m h)
    (hwall : b=4*(n+m)) : False := by
  let R := 2^r
  let L := 2^(t+1)
  let H := 2^h
  let S := 7*2^n-n-2
  let Q := (bp+12)/2
  let D := (c+3)/2
  have hp' : 512*(n*n*n)≤2^n := by simpa only [Nat.mul_assoc] using hp
  have hn1 : 1≤n := by omega
  have hn2 : n≤n*n := by
    have hh := Nat.mul_le_mul_left n hn1
    omega
  have hn3 : n*n≤n*n*n := by
    have hh := Nat.mul_le_mul_left (n*n) hn1
    omega
  have hp1 : n+2≤7*2^n := by omega
  have hS : S+n+2=7*2^n := by dsimp [S]; omega
  have hroot : (14*2^n-2*n-16)+12=2*S := by dsimp [S]; omega
  have hrootmass : (14*2^n-2*n-16)+3+9=2*S := by omega
  obtain ⟨hprepow,hprem⟩ := upper_tail_dyadic
    (14*2^n-2*n-16) 3 0 bp dp r r hpre
  have hQ2 : bp+12=2*Q := by dsimp [Q]; omega
  have hQmod : Q%2=0 := by dsimp [Q]; omega
  have hSQ : S=R*Q := by
    have htwpow : R*(2*Q)=2*S := by
      dsimp [R]
      rw [← hQ2]
      exact hprepow.trans hroot
    have htwice : 2*(R*Q)=2*S := by
      calc
        _=R*(2*Q) := by ac_rfl
        _=2*S := htwpow
    omega
  have hMassPre := tail_mass (14*2^n-2*n-16) 3 0 bp dp r r hpre
  obtain ⟨hPower,hMassInv⟩ :=
    (inverseAt_iff_power_mass bp dp t k c (by omega) hb4 hd).mp hi
  have hCD : c+3=2*D := by dsimp [D]; omega
  have hLD : L*D=dp+bp/2+3 := by
    dsimp [L]
    have hfactor : 2^(t+1)*D=2^t*(c+3) := by
      rw [Nat.pow_succ,hCD]
      ac_rfl
    omega
  have hbpQ : bp/2+6=Q := by dsimp [Q]; omega
  have hShift : dp+bp/2+3+Q+2*r=2*S := by omega
  have hInv : R*L*D+2*r*R+S=2*R*S := by
    have hh : L*D+Q+2*r=2*S := by omega
    have hhR := congrArg (fun x : Nat => R*x) hh
    have hleft : R*(L*D+Q+2*r)=R*L*D+R*Q+2*r*R := by
      simp only [Nat.mul_add]
      ac_rfl
    have hright : R*(2*S)=2*R*S := by ac_rfl
    rw [hleft,hright] at hhR
    omega
  have hMassPost := tail_mass (2*k-4) (c+4) (r+t+1) b d m h hpost
  obtain ⟨hpostpow,hpostm⟩ := upper_tail_dyadic
    (2*k-4) (c+4) (r+t+1) b d m h hpost
  have hm : m=r+t+1+h := hpostm
  have hChildMass : (2*k-4)+(c+4)+2*(r+t+1)+9=2*S := by
    omega
  have hMassNorm : k+D+r+(t+1)+3=S := by omega
  have hWallScale : k+4=2*H*(n+r+(t+1)+h+3) := by
    have hpostpow' : H*(b+12)=(2*k-4)+12 := by simpa only [H] using hpostpow
    have hB : b+12=4*(n+r+(t+1)+h+3) := by omega
    rw [hB] at hpostpow'
    have he1 : H*(4*(n+r+(t+1)+h+3)) =
       2*(2*H*(n+r+(t+1)+h+3)) := by
      simp only [show (4:Nat)=2*2 by decide]
      ac_rfl
    rw [he1] at hpostpow'
    omega
  have hWallNorm :
      D+r+(t+1)+2*H*(n+r+(t+1)+h+3)=S+1 := by omega
  exact one_reset_wall_impossible_large n r (t+1) h R L H S Q D
    hn hp rfl rfl rfl (by omega) hS hQmod hSQ hInv hWallNorm

#print axioms tail_mass
#print axioms source_one_reset_no_wall
end BB6.Agent45OneResetSource
