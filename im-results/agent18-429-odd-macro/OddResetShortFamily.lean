import Q0DoubleBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxHeartbeats 8000000

private theorem cat {w v : List Digit} {p y q f P Y : Nat}
    (h : Trace w p y q f) (g : Trace v q f P Y) : Trace (w++v) p y P Y := by
  induction h with
  | nil => simpa using g
  | cons d hd ht ih => simpa using Trace.cons d hd (ih g)

private theorem zero_run (n p y : Nat) :
    Trace (List.replicate n .zero) p (16^n*y) (p+3*n) y := by
  induction n generalizing p with
  | zero => simpa using Trace.nil p y
  | succ n ih =>
    rw [List.replicate_succ]
    have hnum : num .zero p (16^(n+1)*y)=16*(16^n*y) := by
      simp [num,digit,offset,Nat.pow_succ]; ac_rfl
    apply Trace.cons .zero (by rw [hnum]; omega)
    simp only [nextY,hnum,nextP,cost]
    have he : p+3*(n+1)=p+3+3*n := by omega
    rw [he]
    simpa using ih (p+3)

private theorem five_run (n p y g : Nat) (hp : p=3*y+16^n*g) :
    ∃ Y, Trace (List.replicate n .five) p y (p+6*n) Y ∧ p+6*n=3*Y+g := by
  induction n generalizing p y with
  | zero => exact ⟨y,by simpa using Trace.nil p y,by simpa using hp⟩
  | succ n ih =>
    let Y := y+5*(16^n*g)+2
    have hp' : p=3*y+16*(16^n*g) := by rw [Nat.pow_succ] at hp; grind
    have hnum : num .five p y=16*Y := by simp [num,digit,offset,Y]; omega
    have hY : nextY .five p y=Y := by simp [nextY,hnum]
    have hq : p+6=3*Y+16^n*g := by dsimp [Y]; omega
    obtain ⟨Z,hz,hg⟩ := ih (p+6) Y hq
    refine ⟨Z,?_,by omega⟩
    rw [List.replicate_succ,show p+6*(n+1)=p+6+6*n by omega]
    apply Trace.cons .five (by rw [hnum]; omega)
    simpa [nextP,cost,hY] using hz

private theorem five_step {p y Y : Nat} (h : y+5*p+32=16*Y) :
    Trace [.five] p y (p+6) Y := by
  have hn : num .five p y=16*Y := by simpa [num,digit,offset] using h
  apply Trace.cons .five (by rw [hn]; omega)
  simp [nextP,nextY,cost,hn]
  exact Trace.nil ..

private theorem zero_step (p y : Nat) : Trace [.zero] p (16*y) (p+3) y := by
  simpa using zero_run 1 p y

private theorem pow_linear (s : Nat) : s+1≤16^s := by
  induction s with
  | zero => decide
  | succ s ih => rw [Nat.pow_succ]; omega

private theorem pow_mod3 (s : Nat) : 16^s%3=1 := by
  induction s with
  | zero => decide
  | succ s ih => rw [Nat.pow_succ,Nat.mul_mod]; simp [ih]

/-- Infinite family of exact short-window obstructions, extending a=23,k=117. -/
theorem crossing_family (t : Nat) : Cross2 (23+64*t) 0 (5*(23+64*t)+2) := by
  let a := 23+64*t
  let s := 5*a
  let T := 16^s
  let B := 256*(a*T)
  have hT : s+1≤T := pow_linear s
  have ha : 1≤a := by dsimp [a]; omega
  have hm : 3*s+9+39*T<B := by
    have h := Nat.mul_le_mul_right T ha
    dsimp [s] at hT
    dsimp [B,s]
    simp at h
    omega
  have hB : a*16^(s+2)=B := by
    rw [Nat.pow_add]
    simp only [T,B]
    change a*(16^s*256)=256*(a*16^s)
    ac_rfl
  have hdiv : (a*T+4+11*t)%3=0 := by
    have ht := pow_mod3 s
    have hh : (a*T)%3=a%3 := by
      rw [Nat.mul_mod]; simp [T,ht]
    rw [Nat.add_mod,Nat.add_mod (a*T) 4,hh]
    dsimp [a]
    omega
  let Z := (a*T+4+11*t)/3
  have hZ : 3*Z=a*T+4+11*t := by dsimp [Z]; omega
  have haeq : 44*a+12=256*(4+11*t) := by dsimp [a]; omega
  have htail : B+45*a+12=3*(256*Z)+a := by
    dsimp [B]; omega
  have hw0 := zero_run s (B-(3*s+9)) 13
  have hw1 : Trace [.five] (B-9) 13 (B-3) (80*(a*T)) := by
    have h := five_step (p:=B-9) (y:=13) (Y:=80*(a*T)) (by dsimp [B] at *; omega)
    have he : B-9+6=B-3 := by omega
    simpa only [he] using h
  have hw2 : Trace [.zero] (B-3) (80*(a*T)) B (5*(a*T)) := by
    have h := zero_step (B-3) (5*(a*T))
    have he : B-3+3=B := by omega
    simpa only [he,show 16*(5*(a*T))=80*(a*T) by omega] using h
  have hw0' : Trace (List.replicate s .zero) (B-(3*s+9)) (13*T) (B-9) 13 := by
    have he : B-(3*s+9)+3*s=B-9 := by omega
    simpa only [he,show 16^s*13=13*T by simp [T,Nat.mul_comm]] using hw0
  have hw := cat hw0' (cat hw1 hw2)
  have hv0 := zero_run s B (5*a)
  have hv0' : Trace (List.replicate s .zero) B (5*(a*T)) (B+15*a) (5*a) := by
    have he : 16^s*(5*a)=5*(a*T) := by dsimp [T]; ac_rfl
    simpa only [he,show 3*s=15*a by simp [s]; omega] using hv0
  have hv1 := five_step (p:=B+15*a) (y:=5*a) (Y:=80*(a*T)+5*a+2) (by dsimp [B]; omega)
  have hv2 := five_step (p:=B+15*a+6) (y:=80*(a*T)+5*a+2) (Y:=85*(a*T)+5*a+4) (by dsimp [B]; omega)
  have hv := cat hv0' (cat hv1 hv2)
  obtain ⟨Yz,hz0,hgz⟩ := five_run s (B+15*a+6+6) (85*(a*T)+5*a+4) a (by dsimp [B,T]; grind)
  have hzrank : B+15*a+6+6+6*s=B+45*a+12 := by dsimp [s]; omega
  rw [hzrank] at hz0 hgz
  have hzheight : Yz=256*Z := by omega
  rw [hzheight] at hz0
  have hz1 : Trace (List.replicate 2 .zero) (B+45*a+12) (256*Z) (B+45*a+18) Z := by simpa using zero_run 2 (B+45*a+12) Z
  have hz := cat hz0 hz1
  change Cross2 a 0 (s+2)
  refine ⟨List.replicate s .zero ++ [.five,.zero],List.replicate s .zero ++ [.five,.five],List.replicate s .five ++ List.replicate 2 .zero,B-(3*s+9),13*T,5*(a*T),B+15*a+6+6,85*(a*T)+5*a+4,B+45*a+18,Z,by simp,by simp,by simp,by omega,by omega,?_,?_,hz⟩
  · rw [Nat.add_zero,hB]; simpa using hw
  · rw [Nat.add_zero,hB]; simpa using hv

#print axioms crossing_family
end BB429Q0Macro.RankBarrier
