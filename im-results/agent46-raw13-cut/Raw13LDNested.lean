import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13LDNested
open BB6Coverage BB6Coverage.Agent31Pump
abbrev p : PartialMachine := FAR.fromCodes [7,14,11,24,2,19,20,0,21,12,0,5]
abbrev P : List Bool := [false,true]
abbrev O : List Bool := [false,false,true,true]
abbrev H : List Bool := [true,false,true,true]
abbrev S : List Bool := [false,false,true,true,true,false,true,false,true,false,true,true]
abbrev R (n : Nat) := rep P n ++ S
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev D (l r : List Bool) : Z0 := ⟨3,l,r⟩
abbrev F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def Reach (a b : Z0) : Prop := ∃ t, run0 p t a = some b
theorem reach {t : Nat} {a b : Z0} (h : run0 p t a = some b) : Reach a b := ⟨t,h⟩
theorem chain {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,join0 ht hu⟩
theorem push0 (n : Nat) (L : List Bool) :
    run0 p 4 (A (false::L) (R (n+2))) = some (F (H++true::L) (R n)) := by rfl
theorem pushQ (n : Nat) (L : List Bool) :
    run0 p 6 (A (H++L) (R (n+1))) = some (F (H++false::true::L) (R n)) := by rfl
theorem fStep (L R : List Bool) :
    run0 p 4 (F (H++L) (P++P++R)) = some (F (H++O++L) R) := by rfl
theorem rep_add' (B : List Bool) (n m : Nat) : rep B (n+m) = rep B n ++ rep B m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.succ_add, rep, ih]; simp [rep,List.append_assoc]
theorem rep_double (n : Nat) : rep (P++P) n = rep P (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add']; rfl
theorem fSweep (n k : Nat) (L : List Bool) :
    run0 p (4*n) (F (H++L) (R (2*n+k))) = some (F (H++rep O n++L) (R k)) := by
  have h := sweepR p 5 H [] (P++P) O 4 (by intro L R; exact fStep L R) n L (R k)
  simpa only [List.nil_append,rep_double,R,rep_add',List.append_assoc] using h
theorem endOdd (L : List Bool) :
    run0 p 26 (F (H++L) (R 1)) = some (A (H++L) (R 1)) := by rfl
theorem endEven (L : List Bool) :
    run0 p 26 (F (H++L) (R 2)) = some (A (H++L) (R 2)) := by rfl
-- a leading A1 and D1 consume two ones and append one alternating pair.
theorem aOne (n : Nat) (L : List Bool) :
    run0 p 1 (A (true::L) (R n)) = some (D L (true::R n)) := by rfl
theorem dOne (n : Nat) (L : List Bool) :
    run0 p 1 (D (true::L) (true::R n)) = some (A L (R (n+1))) := by rfl

def Pop (n : Nat) : Prop := ∀ L, Reach (A (false::L) (R n)) (D L (true::R n))
def Quad (n : Nat) : Prop := ∀ L, Reach (F (true::true::L) (R (n+1))) (A L (R (n+2)))
theorem quad1 : Quad 1 := by intro L; exact ⟨28,rfl⟩
theorem quad2 : Quad 2 := by intro L; exact ⟨122,rfl⟩
theorem quadA (n : Nat) (h : Quad n) (L : List Bool) : Reach (A (H++L) (R n)) (A L (R (n+2))) := by
  have h0 : run0 p 2 (A (H++L) (R n)) = some (F (true::true::L) (R (n+1))) := rfl
  exact chain (reach h0) (h L)
theorem qpush (n : Nat) (L : List Bool) :
    run0 p 4 (F (true::true::L) (R (n+2))) = some (F (H++false::true::L) (R n)) := by rfl
theorem packet (n : Nat) (hp : Pop n) (hq : Quad n) (L : List Bool) : Reach (A (O++L) (R n)) (A L (R (n+2))) := by
  have h0 := hp (false::true::true::L)
  have h1 : run0 p 1 (D (false::true::true::L) (true::R n)) = some (F (true::true::L) (R (n+1))) := rfl
  exact chain (chain h0 (reach h1)) (hq L)
theorem drain (a k : Nat) (L : List Bool) (h : ∀ i, k ≤ i → i+2 ≤ k+2*a → Pop i ∧ Quad i) :
    Reach (A (rep O a++L) (R k)) (A L (R (k+2*a))) := by
  induction a generalizing k with
  | zero => exact ⟨0,rfl⟩
  | succ a ih =>
    have h0 := h k (by omega) (by omega)
    have h1 := packet k h0.1 h0.2 (rep O a++L)
    have h2 := ih (k+2) (fun i hi hj => h i (by omega) (by omega))
    simpa only [rep,List.append_assoc,show k+2+2*a=k+2*(a+1) by omega] using chain h1 h2

theorem popOdd (a : Nat) (h : ∀ i, 3 ≤ i → i+2 ≤ 2*a+3 → Pop i ∧ Quad i) : Pop (2*a+3) := by
  intro L
  have h1 := push0 (2*a+1) L
  have h2 := fSweep a 1 (true::L)
  have h3 := endOdd (rep O a++true::L)
  have h4 := quadA 1 quad1 (rep O a++true::L)
  have h5 := drain a 3 (true::L) (fun i hi hj => h i hi (by omega))
  have h6 := aOne (2*a+3) L
  have h12 : Reach (A (false::L) (R (2*a+3))) (F (H++rep O a++true::L) (R 1)) := by
    simpa only [List.append_assoc,show 2*a+1+2=2*a+3 by omega] using chain (reach h1) (reach h2)
  exact chain (chain (chain (chain h12 (reach h3)) h4) (by simpa only [show 3+2*a=2*a+3 by omega] using h5)) (reach h6)
theorem popEven (a : Nat) (h : ∀ i, 3 ≤ i → i+2 ≤ 2*a+4 → Pop i ∧ Quad i) : Pop (2*a+4) := by
  intro L
  have h1 := push0 (2*a+2) L
  have h2 := fSweep a 2 (true::L)
  have h3 := endEven (rep O a++true::L)
  have h4 := quadA 2 quad2 (rep O a++true::L)
  have h5 := drain a 4 (true::L) (fun i hi hj => h i (by omega) (by omega))
  have h6 := aOne (2*a+4) L
  have h12 : Reach (A (false::L) (R (2*a+4))) (F (H++rep O a++true::L) (R 2)) := by
    simpa only [List.append_assoc,show 2*a+2+2=2*a+4 by omega] using chain (reach h1) (reach h2)
  exact chain (chain (chain (chain h12 (reach h3)) h4) (by simpa only [show 4+2*a=2*a+4 by omega] using h5)) (reach h6)
theorem quadOdd (a : Nat) (hp : Pop (2*a+4)) (h : ∀ i, 3 ≤ i → i+2 ≤ 2*a+4 → Pop i ∧ Quad i) : Quad (2*a+3) := by
  intro L
  have h1 := qpush (2*a+2) L
  have h2 := fSweep a 2 (false::true::L)
  have h3 := endEven (rep O a++false::true::L)
  have h4 := quadA 2 quad2 (rep O a++false::true::L)
  have h5 := drain a 4 (false::true::L) (fun i hi hj => h i (by omega) (by omega))
  have h6 := hp (true::L)
  have h7 := dOne (2*a+4) L
  have h12 : Reach (F (true::true::L) (R (2*a+3+1))) (F (H++rep O a++false::true::L) (R 2)) := by
    simpa only [List.append_assoc,show 2*a+2+2=2*a+3+1 by omega] using chain (reach h1) (reach h2)
  have h12345 : Reach (F (true::true::L) (R (2*a+3+1))) (A (false::true::L) (R (2*a+4))) :=
    chain (chain (chain h12 (reach h3)) h4) (by simpa only [show 4+2*a=2*a+4 by omega] using h5)
  simpa only [show 2*a+4+1=2*a+3+2 by omega] using chain (chain h12345 h6) (reach h7)
theorem quadEven (a : Nat) (hp : Pop (2*a+3)) (h : ∀ i, 3 ≤ i → i < 2*a+2 → Pop i ∧ Quad i) : Quad (2*a+2) := by
  intro L
  have h1 := qpush (2*a+1) L
  have h2 := fSweep a 1 (false::true::L)
  have h3 := endOdd (rep O a++false::true::L)
  have h4 := quadA 1 quad1 (rep O a++false::true::L)
  have h5 := drain a 3 (false::true::L) (fun i hi hj => h i hi (by omega))
  have h6 := hp (true::L)
  have h7 := dOne (2*a+3) L
  have h12 : Reach (F (true::true::L) (R (2*a+2+1))) (F (H++rep O a++false::true::L) (R 1)) := by
    simpa only [List.append_assoc,show 2*a+1+2=2*a+2+1 by omega] using chain (reach h1) (reach h2)
  have h12345 : Reach (F (true::true::L) (R (2*a+2+1))) (A (false::true::L) (R (2*a+3))) :=
    chain (chain (chain h12 (reach h3)) h4) (by simpa only [show 3+2*a=2*a+3 by omega] using h5)
  simpa only [show 2*a+3+1=2*a+2+2 by omega] using chain (chain h12345 h6) (reach h7)
/-- The order is important: establish the zero pop at width n before
    the four-cell pop at width n-1. All packet subcalls have smaller width. -/
theorem allPopQuad (n : Nat) : 3 ≤ n → Pop n ∧ Quad (n-1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    have prev : ∀ i, 3 ≤ i → i+1 < n → Pop i ∧ Quad i := by
      intro i hi h
      exact ⟨(ih i (by omega) hi).1,by simpa only [show i+1-1=i by omega] using (ih (i+1) h (by omega)).2⟩
    have pp : Pop n := by
      by_cases h : n%2=1
      · let a := (n-3)/2
        have he : n=2*a+3 := by dsimp [a]; omega
        rw [he]
        apply popOdd
        intro i hi hj
        exact prev i hi (by omega)
      · let a := (n-4)/2
        have he : n=2*a+4 := by dsimp [a]; omega
        rw [he]
        apply popEven
        intro i hi hj
        exact prev i hi (by omega)
    refine ⟨pp,?_⟩
    by_cases h : n%2=1
    · let a := (n-3)/2
      have he : n=2*a+3 := by dsimp [a]; omega
      have pp' : Pop (2*a+3) := by rw [←he]; exact pp
      have hq := quadEven a pp' (fun i hi hj => prev i hi (by omega))
      simpa only [show 2*a+2=n-1 by omega] using hq
    · let a := (n-4)/2
      have he : n=2*a+4 := by dsimp [a]; omega
      have pp' : Pop (2*a+4) := by rw [←he]; exact pp
      have hq := quadOdd a pp' (fun i hi hj => prev i hi (by omega))
      simpa only [show 2*a+3=n-1 by omega] using hq
def family (n : Nat) : Z0 := A [] (R (3*n+3))
theorem seed : run0 p 126 (A [] []) = some (family 0) := by rfl
theorem blankStart (n : Nat) : run0 p 4 (A [] (R (n+2))) = some (F (H++[true]) (R n)) := by rfl
theorem rootStart (n : Nat) : run0 p 23 (D [] (true::R (n+3))) = some (F (H++[true,true,true,true]) (R (n+2))) := by rfl
theorem afterPush (n : Nat) (hn : 3 ≤ n) (L : List Bool) :
    Reach (F (H++true::L) (R (n-2))) (D L (true::R n)) := by
  have prev (i : Nat) (hi : 3 ≤ i) : Pop i ∧ Quad i :=
    ⟨(allPopQuad i hi).1, by simpa only [show i+1-1=i by omega] using (allPopQuad (i+1) (by omega)).2⟩
  by_cases h : n%2=1
  · let a := (n-3)/2
    have he : n=2*a+3 := by dsimp [a]; omega
    rw [he,show 2*a+3-2=2*a+1 by omega]
    have h2 := fSweep a 1 (true::L)
    have h3 := endOdd (rep O a++true::L)
    have h4 := quadA 1 quad1 (rep O a++true::L)
    have h5 := drain a 3 (true::L) (fun i hi _ => prev i hi)
    have h6 := aOne (2*a+3) L
    exact chain (chain (chain (chain (reach h2) (reach h3)) h4) (by simpa only [show 3+2*a=2*a+3 by omega] using h5)) (reach h6)
  · let a := (n-4)/2
    have he : n=2*a+4 := by dsimp [a]; omega
    rw [he,show 2*a+4-2=2*a+2 by omega]
    have h2 := fSweep a 2 (true::L)
    have h3 := endEven (rep O a++true::L)
    have h4 := quadA 2 quad2 (rep O a++true::L)
    have h5 := drain a 4 (true::L) (fun i hi _ => prev i (by omega))
    have h6 := aOne (2*a+4) L
    exact chain (chain (chain (chain (reach h2) (reach h3)) h4) (by simpa only [show 4+2*a=2*a+4 by omega] using h5)) (reach h6)
theorem rootFinish (n : Nat) : run0 p 3 (D [true,true,true] (true::R n)) = some (A [] (R (n+2))) := by rfl
theorem growth (n : Nat) : ∃ t, 0<t ∧ run0 p t (family n) = some (family (n+1)) := by
  have h1 := blankStart (3*n+1)
  have h1' : run0 p 4 (family n) = some (F (H++[true]) (R (3*n+1))) := by
    simpa only [family,show 3*n+1+2=3*n+3 by omega] using h1
  obtain ⟨t,ht⟩ := afterPush (3*n+3) (by omega) []
  have ht' : run0 p t (F (H++[true]) (R (3*n+1))) = some (D [] (true::R (3*n+3))) := by
    simpa only [show 3*n+3-2=3*n+1 by omega] using ht
  have h2 := rootStart (3*n)
  obtain ⟨u,hu⟩ := afterPush (3*n+4) (by omega) [true,true,true]
  have hu' : run0 p u (F (H++[true,true,true,true]) (R (3*n+2))) = some (D [true,true,true] (true::R (3*n+4))) := by
    simpa only [show 3*n+4-2=3*n+2 by omega] using hu
  have h3 := rootFinish (3*n+4)
  refine ⟨4+t+23+u+3,by omega,?_⟩
  simpa only [family,show 3*n+4+2=3*(n+1)+3 by omega] using join0 (join0 (join0 (join0 h1' ht') h2) hu') h3

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost := fun n => Classical.choose (growth n)
  exact never_of_growth p family 126 cost seed (fun n => (Classical.choose_spec (growth n)).1) (fun n => (Classical.choose_spec (growth n)).2) m hm
#print axioms allPopQuad
#print axioms growth
#print axioms never
end BB6.Agent46Raw13LDNested
