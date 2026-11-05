import S4ToggleHead
import Lean.Elab.Tactic.Omega

namespace S4TripleHead
open S4Power S4Octet S4Toggle S4ToggleHead
set_option maxHeartbeats 0

def g3 (c b d e : Nat) : List Nat :=
  let a := b+c
  if a%2=0 then [a/2+2,d+a/2,e]
  else
    let a2 := d+a/2+1
    if a2%2=0 then [a/2,a2/2+2,e+a2/2]
    else [a/2,a2/2,h (a2/2+1) e]

theorem G_prefix3 (c b d e : Nat) (S U : List Nat)
    (hG : G c (b::d::e::S)=some U) :
    ∃ T, U=g3 c b d e ++ T := by
  change H (b+c) (d::e::S)=some U at hG
  by_cases h0 : (b+c)%2=0
  · have hu : U=((b+c)/2+2)::(d+(b+c)/2)::e::S := by
      simpa [H,h0] using hG.symm
    subst U
    exact ⟨S, by simp [g3,h0]⟩
  · have hrec : (H (d+(b+c)/2+1) (e::S)).map ((b+c)/2::·)=some U := by
      rw [H] at hG
      simp only [h0,ite_false] at hG
      exact hG
    obtain ⟨V,hV,hVU⟩ := Option.map_eq_some_iff.mp hrec
    subst U
    by_cases h1 : (d+(b+c)/2+1)%2=0
    · have hV : V=((d+(b+c)/2+1)/2+2)::(e+(d+(b+c)/2+1)/2)::S := by
        simpa [H,h1] using hV.symm
      subst V
      exact ⟨S, by simp [g3,h0,h1]⟩
    · have hrec2 : (H (e+(d+(b+c)/2+1)/2+1) S).map ((d+(b+c)/2+1)/2::·)=some V := by
        rw [H] at hV
        simp only [h1,ite_false] at hV
        exact hV
      obtain ⟨X,hX,hXV⟩ := Option.map_eq_some_iff.mp hrec2
      subst V
      have hGX : G ((d+(b+c)/2+1)/2+1) (e::S)=some X := hX
      obtain ⟨T,hXT⟩ := G_head _ e S X hGX
      subst X
      refine ⟨T,?_⟩
      simp [g3,h0,h1]

theorem g3_shape (c b d e : Nat) :
    g3 c b d e = [(g3 c b d e)[0]!, (g3 c b d e)[1]!, (g3 c b d e)[2]!] := by
  by_cases h0 : (b+c)%2=0
  · simp [g3,h0]
  · by_cases h1 : (d+(b+c)/2+1)%2=0
    · simp [g3,h0,h1]
    · simp [g3,h0,h1]

def p3 (a b d : Nat) : List Nat :=
  let v := g3 509 a b d
  let w := g3 290 v[0]! v[1]! v[2]!
  g3 219 w[0]! w[1]! w[2]!

theorem P_prefix3 (a b d : Nat) (S U : List Nat)
    (hp : P (a::b::d::S)=some U) :
    ∃ T, U=p3 a b d ++ T := by
  cases h1 : G 509 (a::b::d::S) with
  | none => simp [P,h1] at hp
  | some X =>
      obtain ⟨T1,hX⟩ := G_prefix3 509 a b d S X h1
      rw [g3_shape] at hX
      subst X
      let v := g3 509 a b d
      have hv : G 509 (a::b::d::S)=some (v[0]!::v[1]!::v[2]!::T1) := by
        simpa [v] using h1
      simp only [P,hv,Option.bind_some] at hp
      change (G 290 (v[0]!::v[1]!::v[2]!::T1)).bind (G 219) = some U at hp
      cases h2 : G 290 (v[0]!::v[1]!::v[2]!::T1) with
      | none => rw [h2] at hp; simp at hp
      | some Y =>
          obtain ⟨T2,hY⟩ := G_prefix3 290 v[0]! v[1]! v[2]! T1 Y h2
          rw [g3_shape] at hY
          subst Y
          let w := g3 290 v[0]! v[1]! v[2]!
          have hw : G 290 (v[0]!::v[1]!::v[2]!::T1) =
              some (w[0]!::w[1]!::w[2]!::T2) := by simpa [w] using h2
          have h3 : G 219 (w[0]!::w[1]!::w[2]!::T2)=some U := by
            rw [hw] at hp
            simpa using hp
          obtain ⟨T3,hU⟩ := G_prefix3 219 w[0]! w[1]! w[2]! T2 U h3
          exact ⟨T3,by simpa [p3,v,w] using hU⟩

private theorem p3_shape (a b d : Nat) :
    p3 a b d = [(p3 a b d)[0]!, (p3 a b d)[1]!, (p3 a b d)[2]!] := by
  exact g3_shape 219 _ _ _

def next3 (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let v := p3 x.1 x.2.1 x.2.2
  (v[0]!,v[1]!,v[2]!)

def tripleRun : Nat → Nat × Nat × Nat
  | 0 => (280,397,1158)
  | n+1 => next3 (tripleRun n)

set_option maxRecDepth 20000

theorem tripleRun_32 : tripleRun 32 = (280,397,1158) := by
  decide

theorem tripleRun_period32 (n : Nat) : tripleRun (n+32) = tripleRun n := by
  induction n with
  | zero => exact tripleRun_32
  | succ n ih =>
      change next3 (tripleRun (n+32)) = next3 (tripleRun n)
      rw [ih]

theorem seed23 :
    prun 23 [301,650,645,322,163,160] =
      some [280,397,1158,1914,8071,6823,3573,1786,895,892] := by
  set_option maxRecDepth 10000 in
    simp [prun,P,G,H]

theorem prun_triple_cycle (n : Nat) (U : List Nat)
    (hr : prun (23+n) [301,650,645,322,163,160]=some U) :
    ∃ T, U=(tripleRun n).1::(tripleRun n).2.1::(tripleRun n).2.2::T := by
  induction n generalizing U with
  | zero =>
      rw [show 23+0=23 by omega, seed23] at hr
      have hU : U=[280,397,1158,1914,8071,6823,3573,1786,895,892] := by
        exact Option.some.inj hr.symm
      subst U
      exact ⟨[1914,8071,6823,3573,1786,895,892],rfl⟩
  | succ n ih =>
      change (prun (23+n) [301,650,645,322,163,160]).bind P=some U at hr
      cases hprev : prun (23+n) [301,650,645,322,163,160] with
      | none => simp [hprev] at hr
      | some V =>
          obtain ⟨T,hV⟩ := ih V hprev
          subst V
          have hp : P ((tripleRun n).1::(tripleRun n).2.1::(tripleRun n).2.2::T)=some U := by
            simpa [hprev] using hr
          obtain ⟨Z,hZ⟩ := P_prefix3 _ _ _ T U hp
          rw [p3_shape] at hZ
          exact ⟨Z,by simpa [tripleRun,next3] using hZ⟩

#print axioms G_prefix3
#print axioms P_prefix3
#print axioms tripleRun_32
#print axioms tripleRun_period32
#print axioms prun_triple_cycle
end S4TripleHead
