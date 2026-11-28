import F421SecondaryPSource
import F421SecondaryExact

namespace F421SecondaryLifetimes
open F421TertiaryGuard
open BB6Coverage.Agent41F421.EpochWords

theorem advanceAuxPositive (d : Nat) (xs : List Nat) (hp : Positive xs) :
    Positive (advanceAux d xs).1 := by
  induction xs generalizing d with
  | nil => intro x hx; simp [advanceAux] at hx
  | cons x xs ih =>
    have px : 0<x := hp x (by simp)
    have pt : Positive xs := fun y hy => hp y (by simp [hy])
    by_cases h1 : x=1
    · simpa [advanceAux,h1] using ih (d+1) pt
    · rcases he : advanceAux d xs with ⟨ys,D⟩
      have h := ih d pt
      rw [he] at h
      simp only [Prod.fst] at h
      simp only [advanceAux,ite_eq_right h1,he,Prod.fst]
      intro y hy
      rcases List.mem_cons.mp hy with hxy|hxy
      · subst y
        apply Nat.mul_pos
        · have : 2≤x := by omega
          omega
        · exact Nat.pow_pos (by decide)
      · exact h y hxy

theorem advancePositive (xs : List Nat) (hp : Positive xs) : Positive (advance xs) := by
  rcases he : advanceAux 0 xs with ⟨ys,D⟩
  have hy := advanceAuxPositive 0 xs hp
  rw [he] at hy
  change Positive ys at hy
  unfold advance
  rw [he]
  intro x hx
  rcases List.mem_append.mp hx with hl|hl
  · exact hy x hl
  · have hh : x=2^(D+1) := by simpa using hl
    rw [hh]
    exact Nat.pow_pos (by decide)

def lifeIter : Nat → List Nat → List Nat
  | 0,xs => xs
  | k+1,xs => lifeIter k (advance xs)

theorem lifeIterPositive (k : Nat) (xs : List Nat) (hp : Positive xs) :
    Positive (lifeIter k xs) := by
  induction k generalizing xs with
  | zero => exact hp
  | succ k ih => exact ih (advance xs) (advancePositive xs hp)

/-- One source successor preserves the protected prefix while exposing the
    exact normalized head regardless of Q values. -/
theorem nextShape (b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 3≤p0) (h1 : 5≤p1) (hp : Positive xs)
    (hh : pProjection hs=physicalP 4 xs) :
    ∃ a' b' q0' q1' hs',
      sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs) =
        (a',b',⟨p0-2,q0'⟩::⟨p1-4,q1'⟩::hs') ∧
      pProjection hs'=physicalP 4 (advance xs) := by
  have hs0 := secondarySourceP b p0 q0 p1 q1 hs xs h0 h1 hp hh
  rcases he : sNext b (⟨p0,q0⟩::⟨p1,q1⟩::hs) with ⟨a',b',cs⟩
  rw [he] at hs0
  cases cs with
  | nil => simp [pProjection] at hs0
  | cons c cs =>
    cases cs with
    | nil => simp [pProjection] at hs0
    | cons d ds =>
      rcases c with ⟨cp,cq⟩
      rcases d with ⟨dp,dq⟩
      simp only [Prod.fst,Prod.snd,pProjection,List.map_cons,List.cons.injEq] at hs0
      rcases hs0 with ⟨hc,hd,ht⟩
      refine ⟨a',b',cq,dq,ds,?_,ht⟩
      simp only [hc,hd]

/-- Arbitrary finite iteration of the exact original source successor,
    with only two protected P-run budgets and all Q masses unrestricted. -/
theorem iterateSourceP (k a b p0 q0 p1 q1 : Nat) (hs : List PC) (xs : List Nat)
    (h0 : 2*k+3≤p0) (h1 : 4*k+5≤p1) (hp : Positive xs)
    (hh : pProjection hs=physicalP 4 xs) :
    ∃ a' b' q0' q1' hs',
      sIter k (a,b,⟨p0,q0⟩::⟨p1,q1⟩::hs) =
        (a',b',⟨p0-2*k,q0'⟩::⟨p1-4*k,q1'⟩::hs') ∧
      pProjection hs'=physicalP 4 (lifeIter k xs) := by
  induction k generalizing a b p0 q0 p1 q1 hs xs with
  | zero =>
    refine ⟨a,b,q0,q1,hs,?_,?_⟩
    · simp [sIter]
    · simpa [lifeIter] using hh
  | succ k ih =>
    obtain ⟨a1,b1,v0,v1,hs1,hstep,hshape⟩ :=
      nextShape b p0 q0 p1 q1 hs xs (by omega) (by omega) hp hh
    have hpos := advancePositive xs hp
    have ht := ih a1 b1 (p0-2) v0 (p1-4) v1 hs1 (advance xs)
      (by omega) (by omega) hpos hshape
    obtain ⟨a2,b2,w0,w1,hs2,hout,hhead⟩ := ht
    refine ⟨a2,b2,w0,w1,hs2,?_,?_⟩
    · simp only [sIter]
      rw [hstep,hout]
      rw [show p0-2-2*k=p0-2*(k+1) by omega]
      rw [show p1-4-4*k=p1-4*(k+1) by omega]
    · simpa [lifeIter] using hhead

/-- Authentic first-secondary-seed normalization: no enormous Q values. -/
def firstLives : List Nat := [327661,14,30,6,22,14,1,2]

def firstHead : List PC :=
  [⟨2621288,3145735⟩,⟨224,3148774⟩,⟨960,3054⟩,⟨384,3038⟩,
   ⟨2816,4031⟩,⟨3584,3967⟩,⟨512,767⟩,⟨2048,1535⟩]

theorem initialHeadEncoding : pProjection firstHead=physicalP 4 firstLives := by
  decide

/-- Exact P projection of the authentic 32,750-cycle endpoint.
    This is not a proof of the next zero crossing or nonhalting. -/
theorem firstSecondaryP :
    ∃ a' b' q0 q1 hs',
      sIter 32750 (2047,3071,firstPrimary) =
        (a',b',⟨2818045,q0⟩::⟨6946811,q1⟩::hs') ∧
      pProjection hs'=physicalP 4 (lifeIter 32750 firstLives) := by
  have h := iterateSourceP 32750 2047 3071 2883545 131073 7077811 2883586
     firstHead firstLives (by decide) (by decide)
      (by simp [Positive,firstLives]) initialHeadEncoding
  have he : firstPrimary=⟨2883545,131073⟩::⟨7077811,2883586⟩::firstHead := by rfl
  rw [←he] at h
  simpa only [show 2883545-2*32750=2818045 by decide,
              show 7077811-4*32750=6946811 by decide] using h

#print axioms advancePositive
#print axioms iterateSourceP
#print axioms firstSecondaryP
end F421SecondaryLifetimes
