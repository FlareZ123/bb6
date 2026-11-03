import OddUBounce
import Lean.Elab.Tactic.Omega

/-!
The odd-counter cascade beyond the first BB429 U/V ray returns.

A modulo-eleven obstruction removes both second-stage exceptional seams on
the odd-index U ray. Two further exact transition words are proved:
a four-step U overflow and a V_(1 mod 4) odd-one affine return.
All guards are explicit, and authentic blank-entry finite witnesses connect
these words. None asserts all-time nonhalting or an exact BB(6) value.
-/
namespace BB429OddCascade
open BB429 BB429Ladder BB429ElevenExtension BB429ExitTransfer

/-- General two-step overflow of an odd first counter with w=1 modulo 4. -/
theorem odd_one_overflow_step_one (x y:Nat) (hx:x%2=1) (hy:y%4=1)
    (hcap:y+7≤2*x) (hover:2*x+13≤3*y):
    next (x,y)=some (x-y/2+3,2*y) := by
  have hodd:y%2=1:=by omega
  have hlt:y<2*x:=by omega
  have hd:4≤x-y/2:=by omega
  have h1:¬y≥2*x+3:=by omega
  have h2:y≠2*x+2:=by omega
  have h3:y≠2*x+1:=by omega
  have h4:y≠2*x:=by omega
  unfold next
  simp [h1,h2,h3,h4,show y%2≠0 by omega,
    show x-y/2≠1 by omega,show x-y/2≠2 by omega,
    show (x-y/2)%2≠0 by omega]

theorem odd_one_overflow_step_two (x y:Nat) (hy:y%4=1)
    (hcap:y+7≤2*x) (hover:2*x+13≤3*y):
    next (x-y/2+3,2*y)=some (2*x-y+10,3*y-2*x-10) := by
  have hforward:2*(x-y/2+3)+3≤2*y:=by omega
  have hleft:2*(x-y/2+3)+3=2*x-y+10:=by omega
  have hright:2*y-2*(x-y/2+3)-3=3*y-2*x-10:=by omega
  simp only [next,ge_iff_le,if_pos hforward,Option.some.injEq,Prod.mk.injEq]
  exact ⟨hleft,hright⟩

theorem odd_one_overflow_two_step (x y:Nat) (hx:x%2=1) (hy:y%4=1)
    (hcap:y+7≤2*x) (hover:2*x+13≤3*y):
    run 2 (x,y)=some (2*x-y+10,3*y-2*x-10) := by
  change (next (x,y)).bind next = _
  rw [odd_one_overflow_step_one x y hx hy hcap hover]
  simpa only [Option.bind_some] using
    odd_one_overflow_step_two x y hy hcap hover

/-- The odd-index U ray cycles through precisely five allowed residues modulo 11. -/
theorem odd_rayU_mod11 (n:Nat):
    rayU (2*n+1)%11=3 ∨ rayU (2*n+1)%11=10 ∨
    rayU (2*n+1)%11=5 ∨ rayU (2*n+1)%11=7 ∨
    rayU (2*n+1)%11=4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hrec:rayU (2*(n+1)+1)=4*rayU (2*n+1)+9:=by
      have h1:2*(n+1)+1=(2*n+1)+2:=by omega
      rw [h1]
      change 2*(2*rayU (2*n+1)+3)+3=4*rayU (2*n+1)+9
      omega
    rw [hrec]
    rcases ih with h | h | h | h | h <;> omega

/-- Both exceptional second-stage halting-looking arithmetic seams are
arithmetically inaccessible on every odd U ray. -/
theorem odd_rayU_no_secondary_seam (k w:Nat) (hk:k%2=1):
    11*w≠10*rayU k+107 ∧ 11*w≠10*rayU k+111 := by
  obtain ⟨n,hn⟩:∃n,k=2*n+1:=⟨k/2,by omega⟩
  subst k
  have h:=odd_rayU_mod11 n
  constructor <;> intro he <;> omega

/-- For k=3 mod 4 and w=3 mod 4, only the second-stage reset margin or
a strict secondary overflow is possible. -/
theorem odd_rayU_second_dichotomy (k w:Nat) (hk:3≤k) (hkm:k%4=3)
    (hw:w%4=3):
    11*w≤10*rayU k+103 ∨ 10*rayU k+115≤11*w := by
  have hodd:k%2=1:=by omega
  have hh:=odd_rayU_no_secondary_seam k w hodd
  have hu4:rayU k%4=1:=U_mod k (by omega)
  omega

/-- Four exact accelerated steps through two nested overflow tests. -/
theorem odd_U_secondary_overflow (k w:Nat) (hk:3≤k)
    (hkm:k%4=3) (hw:w%4=3)
    (hcap:w+7≤2*rayU k)
    (hscap:5*w≤6*rayU k+51)
    (hsecondary:10*rayU k+115≤11*w):
    run 4 (rayU k,w)=
      some (6*rayU k-5*w+68,11*w-10*rayU k-112) := by
  let u:=rayU k
  let x:=2*u-w+18
  let y:=3*w-2*u-22
  have hu4:u%4=1:=by dsimp [u];exact U_mod k (by omega)
  have hfirstoverflow:2*u+22≤3*w:=by dsimp [u] at *;omega
  have hcases:=BB429OddBoundary.rayU_odd_boundary k w hk hw hcap
  have hFirst:run 2 (u,w)=some (x,y):=by
    rcases hcases with ⟨hr,_⟩ | ⟨_,hs⟩
    · exact False.elim (by omega : False)
    · simpa only [u,x,y] using hs
  have hxodd:x%2=1:=by dsimp [x];omega
  have hymod:y%4=1:=by dsimp [y];omega
  have hcap2:y+7≤2*x:=by dsimp [x,y,u] at *;omega
  have hover2:2*x+13≤3*y:=by dsimp [x,y,u] at *;omega
  have hSecond:=odd_one_overflow_two_step x y hxodd hymod hcap2 hover2
  have hX:2*x-y+10=6*u-5*w+68:=by dsimp [x,y];omega
  have hY:3*y-2*x-10=11*w-10*u-112:=by dsimp [x,y];omega
  rw [show 4=2+2 by decide,BB429.run_add,hFirst]
  simpa only [Option.bind_some,u,hX,hY] using hSecond

/-- A complete two-level split for the phase within both sufficient caps. -/
theorem odd_U_complete_two_level (k w:Nat) (hk:3≤k) (hkm:k%4=3)
    (hw:w%4=3) (hcap:w+7≤2*rayU k)
    (hfirstoverflow:2*rayU k+22≤3*w)
    (hscap:5*w≤6*rayU k+51):
    (11*w≤10*rayU k+103 ∧
      run (k+4) (rayU k,w)=some (rayU k,w+3*k+31)) ∨
    (10*rayU k+115≤11*w ∧
      run 4 (rayU k,w)=
        some (6*rayU k-5*w+68,11*w-10*rayU k-112)) := by
  rcases odd_rayU_second_dichotomy k w hk hkm hw with h | h
  · exact Or.inl ⟨h,BB429OddUBounce.odd_U_bounce k w hk hkm hw
      hcap hfirstoverflow h⟩
  · exact Or.inr ⟨h,odd_U_secondary_overflow k w hk hkm hw
      hcap hscap h⟩

/-- New V-odd-one affine bounce: two odd branches, then the entire 11-ray. -/
theorem odd_V_one_bounce (k w:Nat) (hk:1≤k) (hkm:k%4=1) (hw:w%4=1)
    (hcap:w+7≤2*rayV k)
    (hover:2*rayV k+13≤3*w)
    (hreset:11*w≤10*rayV k+65):
    run (k+4) (rayV k,w)=some (rayV k,w+3*k+41) := by
  let v:=rayV k
  let x:=2*v-w+10
  let y:=3*w-2*v-10
  have hv4:v%4=1:=by dsimp[v];exact V_mod k hk
  have hvodd:v%2=1:=by omega
  have hFirst:=odd_one_overflow_two_step v w hvodd hw hcap hover
  have hxodd:x%2=1:=by dsimp[x];omega
  have hxlarge:11≤x:=by dsimp[x];omega
  have hy3:y%4=3:=by dsimp[y];omega
  have hreset2:3*y≤2*x+15:=by dsimp[x,y,v] at *;omega
  have hSecond:=BB429ElevenOddExtension.odd_even_two_step x y hxodd hxlarge
    hy3 hreset2
  have hW:2*x+y+9=2*v+w+19:=by dsimp[x,y];omega
  have hBal:=v_balance k
  have hdb:demandV k≤2*v+w+19:=by dsimp [v] at *;omega
  have hRay:=v_run k (2*v+w+19) hdb
  have hFinal:(2*v+w+19)-demandV k=w+3*k+41:=by dsimp[v] at *;omega
  have hFirst2:run 2 (v,w)=some (x,y):=by
    simpa only [v,x,y] using hFirst
  have hFour:run 4 (v,w)=some (11,2*v+w+19):=by
    rw [show 4=2+2 by decide,BB429.run_add,hFirst2]
    simpa only [Option.bind_some,hW] using hSecond
  rw [show k+4=4+k by omega,BB429.run_add,hFour]
  simpa only [Option.bind_some,v,hFinal] using hRay

/-- Any finite number of guarded odd-V-one bounces. -/
theorem odd_V_one_ladder (k n w:Nat) (hk:1≤k) (hkm:k%4=1)
    (hw:w%4=1) (hover:2*rayV k+13≤3*w)
    (hbound:w+n*(3*k+41)+7≤2*rayV k)
    (hreturn:11*(w+n*(3*k+41))≤10*rayV k+65):
    run (n*(k+4)) (rayV k,w)=some (rayV k,w+n*(3*k+41)) := by
  have hdmod:(3*k+41)%4=0:=by omega
  induction n with
  | zero => simp [BB429.run]
  | succ n ih =>
    have hboundN:w+n*(3*k+41)+7≤2*rayV k:=by
      rw [Nat.succ_mul n (3*k+41)] at hbound
      omega
    have hreturnN:11*(w+n*(3*k+41))≤10*rayV k+65:=by
      rw [Nat.succ_mul n (3*k+41)] at hreturn
      omega
    have hwmN:(w+n*(3*k+41))%4=1:=by
      simp [Nat.add_mod,Nat.mul_mod,hw,hdmod]
    have hoverN:2*rayV k+13≤3*(w+n*(3*k+41)):=by omega
    have hStep:=odd_V_one_bounce k (w+n*(3*k+41)) hk hkm hwmN
      hboundN hoverN hreturnN
    rw [Nat.succ_mul,BB429.run_add,ih hboundN hreturnN]
    simp only [Option.bind_some,hStep]
    have hEq:w+n*(3*k+41)+3*k+41=w+(n+1)*(3*k+41):=by
      rw [Nat.succ_mul n (3*k+41)]
      omega
    exact congrArg (fun z:Nat=>some (rayV k,z)) hEq

/-- Genuine blank-derived second overflow after the U7 bounce. -/
theorem rooted_to_499_159 : run 237 (0,0)=some (499,159) := by
  have h233:=BB429OddUBounce.rooted_to_U7_371
  have hFour:=odd_U_secondary_overflow 7 371 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have h7:rayU 7=381:=by decide
  have hRes:run 4 (rayU 7,371)=some (499,159):=by
    simpa only [h7,show 6*381-5*371+68=499 by decide,
      show 11*371-10*381-112=159 by decide] using hFour
  rw [show 237=233+4 by decide,BB429.run_add,h233]
  simpa only [Option.bind_some] using hRes

/-- The successor is again on the original V5 odd-one ray. -/
theorem rooted_to_V5_313 : run 244 (0,0)=some (rayV 5,313) := by
  have h0:=rooted_to_499_159
  have h2:run 2 (499,159)=some (11,1166):=by decide
  have hR:=v_run 5 1166 (by decide)
  have h5:run 5 (11,1166)=some (rayV 5,313):=by
    simpa only [show demandV 5=853 by decide,
      show 1166-853=313 by decide] using hR
  have h7:run 7 (499,159)=some (rayV 5,313):=by
    rw [show 7=2+5 by decide,BB429.run_add,h2]
    simpa only [Option.bind_some] using h5
  rw [show 244=237+7 by decide,BB429.run_add,h0]
  simpa only [Option.bind_some] using h7

/-- Two exact consecutive V5 returns appear in the blank trajectory. -/
theorem rooted_to_V5_425 : run 262 (0,0)=some (rayV 5,425) := by
  have h0:=rooted_to_V5_313
  have h1:=odd_V_one_bounce 5 313 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have h2:=odd_V_one_bounce 5 369 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hstep1:run 9 (rayV 5,313)=some (rayV 5,369):=by
    simpa only [show 5+4=9 by decide,
      show 313+3*5+41=369 by decide] using h1
  have hstep2:run 9 (rayV 5,369)=some (rayV 5,425):=by
    simpa only [show 5+4=9 by decide,
      show 369+3*5+41=425 by decide] using h2
  rw [show 262=244+18 by decide,BB429.run_add,h0]
  simp only [Option.bind_some]
  rw [show 18=9+9 by decide,BB429.run_add,hstep1]
  simpa only [Option.bind_some] using hstep2

#print axioms odd_one_overflow_two_step
#print axioms odd_rayU_no_secondary_seam
#print axioms odd_rayU_second_dichotomy
#print axioms odd_U_complete_two_level
#print axioms odd_V_one_bounce
#print axioms odd_V_one_ladder
#print axioms rooted_to_V5_425
end BB429OddCascade
