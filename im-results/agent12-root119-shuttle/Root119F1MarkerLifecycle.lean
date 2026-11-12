import Root119EvenExtra
import Root119EvenMarkerGate

namespace BB6Root119

theorem setBit_apply_ne (t : Int → Bool) (loc x : Int) (b : Bool)
    (hne : x ≠ loc) : setBit t loc b x = t x := by
  simp [setBit,hne]

theorem setBit_apply_eq (t : Int → Bool) (loc : Int) (b : Bool) :
    setBit t loc b loc = b := by
  simp [setBit]

/-- Exact inverse transition classification for entry into state F. -/
theorem to_F {u v : Conf} (hstep : next u = some v) (hF : v.q = .F) :
    (u.q = .B ∧ u.tape u.h = true ∧ v.h = u.h-1) ∨
    (u.q = .D ∧ u.tape u.h = true ∧ v.h = u.h+1 ∧
      v.tape (v.h-1) = true) := by
  cases u with
  | mk q h t =>
      cases q <;> cases hb : t h <;> simp [next,hb] at hstep
      all_goals cases hstep
      all_goals simp_all [setBit]

/-- Exact inverse transition classification for entry into state B. -/
theorem to_B {u v : Conf} (hstep : next u = some v) (hB : v.q = .B) :
    (u.q = .A ∧ u.tape u.h = false ∧ v.h = u.h+1 ∧
      v.tape (v.h-1) = true) ∨
    (u.q = .F ∧ u.tape u.h = false ∧ v.h = u.h-1 ∧
      v.tape (v.h+1) = true) := by
  cases u with
  | mk q h t =>
      cases q <;> cases hb : t h <;> simp [next,hb] at hstep
      all_goals cases hstep
      all_goals simp_all [setBit]

/-- A reachable F configuration whose left neighbor is zero can only have
    arrived from B/1 immediately to its right: the alternative D/1
    predecessor necessarily writes one into that left neighbor. -/
theorem reached_F_left_zero_parent (c : Conf) (hc : Reach c)
    (hF : c.q = .F) (hleft : c.tape (c.h-1) = false) :
    ∃ b, Reach b ∧ b.q = .B ∧ b.tape b.h = true ∧
      b.h = c.h+1 ∧ next b = some c := by
  cases hc with
  | initial =>
      simp [blank] at hF
  | @follow u _ hu hstep =>
      rcases to_F hstep hF with hB | hD
      · rcases hB with ⟨hq,hbit,hpos⟩
        have hpos' : u.h = c.h+1 := by omega
        exact ⟨u,hu,hq,hbit,hpos',hstep⟩
      · rcases hD with ⟨hq,hbit,hpos,hwritten⟩
        rw [hleft] at hwritten
        cases hwritten

/-- The even D/F sweep leaves every cell strictly left of its start unchanged. -/
theorem evenSweepTape_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x < h) : evenSweepTape n t h x = t x := by
  induction n generalizing t h x with
  | zero => rfl
  | succ n ih =>
      change evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) x = t x
      have hx' : x < h+2 := by omega
      rw [ih (setBit (setBit t h true) (h+1) false) (h+2) x hx']
      have h0 : x ≠ h := by omega
      have h1 : x ≠ h+1 := by omega
      simp [setBit,h0,h1]

/-- The D positions of an even sweep are all one, including its last D cell. -/
theorem evenSweepTape_D (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)) = true := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero =>
          have hl := evenSweepTape_left n
            (setBit (setBit t h true) (h+1) false) (h+2) h (by omega)
          have hne : h ≠ h+1 := by omega
          simpa [evenSweepTape,setBit,hne] using hl
      | succ j =>
          have hj' : j < n := by omega
          have heq : h+2*((j+1:Nat):Int) = (h+2)+2*(j:Int) := by omega
          rw [show evenSweepTape (n+1) t h =
            evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) by rfl]
          rw [heq]
          exact ih (setBit (setBit t h true) (h+1) false) (h+2) j hj'

/-- The F positions of an even sweep are all zero. -/
theorem evenSweepTape_F (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    evenSweepTape n t h (h+2*(j:Int)+1) = false := by
  induction n generalizing t h j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero =>
          have hl := evenSweepTape_left n
            (setBit (setBit t h true) (h+1) false) (h+2) (h+1) (by omega)
          have hne : h+1 ≠ h := by omega
          simpa [evenSweepTape,setBit,hne] using hl
      | succ j =>
          have hj' : j < n := by omega
          have heq : h+2*((j+1:Nat):Int)+1 = (h+2)+2*(j:Int)+1 := by omega
          rw [show evenSweepTape (n+1) t h =
            evenSweepTape n (setBit (setBit t h true) (h+1) false) (h+2) by rfl]
          rw [heq]
          exact ih (setBit (setBit t h true) (h+1) false) (h+2) j hj'

/-- Exact B endpoint after an even F/1 right corridor. The initial F/1 write
    and the D/F sweep are represented on the complete signed tape. -/
def f1EvenTape (n : Nat) (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit
    (setBit
      (setBit
        (evenSweepTape (n+1) (setBit t h false) (h+1))
        (h+1+((2*(n+1):Nat):Int)) false)
      (h+1+((2*(n+1):Nat):Int)-1) true)
    (h+1+((2*(n+1):Nat):Int)) true

def f1EvenResult (n : Nat) (t : Int → Bool) (h : Int) : Conf :=
  ⟨.B,h+1+((2*(n+1):Nat):Int)+1,f1EvenTape n t h⟩

/-- The two-step backward cone of any reached F state with a zero
    immediately to its left. Its B/1 predecessor must itself have come
    either from A/0 at the F head or from F/0 two cells to its right. -/
theorem reached_F_left_zero_two_step_parent (c : Conf) (hc : Reach c)
    (hF : c.q = .F) (hleft : c.tape (c.h-1) = false) :
    ∃ b, Reach b ∧ b.q = .B ∧ b.tape b.h = true ∧ b.h = c.h+1 ∧
      ((∃ a, Reach a ∧ a.q = .A ∧ a.tape a.h = false ∧
          a.h = c.h ∧ next a = some b) ∨
       (∃ a, Reach a ∧ a.q = .F ∧ a.tape a.h = false ∧
          a.h = c.h+2 ∧ next a = some b)) := by
  obtain ⟨b,hb,hB,hbit,hpos,hstepB⟩ :=
    reached_F_left_zero_parent c hc hF hleft
  cases hb with
  | initial =>
      simp [blank] at hB
  | @follow a _ ha hstepA =>
      rcases to_B hstepA hB with hA | hF0
      · rcases hA with ⟨hq,hzero,hposB,hwritten⟩
        have hposA : a.h = c.h := by omega
        exact ⟨b,Reach.follow ha hstepA,hB,hbit,hpos,
          Or.inl ⟨a,ha,hq,hzero,hposA,hstepA⟩⟩
      · rcases hF0 with ⟨hq,hzero,hposB,hwritten⟩
        have hposA : a.h = c.h+2 := by omega
        exact ⟨b,Reach.follow ha hstepA,hB,hbit,hpos,
          Or.inr ⟨a,ha,hq,hzero,hposA,hstepA⟩⟩

/-- In an A/0 -> B/1 -> F transition, the two writes are at the
    F head and one cell to its right. Consequently the three cells to the
    left are preserved, and an F state with left suffix 110 came from an
    A/0 configuration already carrying 1100 at its head. -/
theorem A0_B1_F1_parent_has_1100 (a b c : Conf)
    (hA : a.q = .A) (hzero : a.tape a.h = false)
    (hAB : next a = some b)
    (hB : b.q = .B) (hbit : b.tape b.h = true)
    (hBC : next b = some c)
    (hpos : a.h = c.h)
    (hleft1 : c.tape (c.h-1) = false)
    (hleft2 : c.tape (c.h-2) = true)
    (hleft3 : c.tape (c.h-3) = true) :
    a.tape (c.h-3) = true ∧ a.tape (c.h-2) = true ∧
    a.tape (c.h-1) = false ∧ a.tape c.h = false := by
  have hBShape : b = ⟨.B,a.h+1,setBit a.tape a.h true⟩ := by
    rcases a with ⟨q,pos,tape⟩
    change q = .A at hA
    subst q
    change tape pos = false at hzero
    have hlocal : next (⟨.A,pos,tape⟩ : Conf) =
        some ⟨.B,pos+1,setBit tape pos true⟩ := by
      simp [next,hzero]
    rw [hlocal] at hAB
    cases hAB
    rfl
  have hCShape : c = ⟨.F,b.h-1,setBit b.tape b.h true⟩ := by
    rcases b with ⟨q,pos,tape⟩
    change q = .B at hB
    subst q
    change tape pos = true at hbit
    have hlocal : next (⟨.B,pos,tape⟩ : Conf) =
        some ⟨.F,pos-1,setBit tape pos true⟩ := by
      simp [next,hbit]
    rw [hlocal] at hBC
    cases hBC
    rfl
  have hctape : c.tape =
      setBit (setBit a.tape a.h true) (a.h+1) true := by
    have ht := congrArg Conf.tape hCShape
    simpa [hBShape] using ht
  have hcell (x : Int) (hx1 : x ≠ a.h) (hx2 : x ≠ a.h+1) :
      c.tape x = a.tape x := by
    rw [hctape]
    rw [setBit_apply_ne _ (a.h+1) x true hx2]
    rw [setBit_apply_ne _ a.h x true hx1]
  constructor
  · exact (hcell (c.h-3) (by rw [hpos]; omega) (by rw [hpos]; omega)).symm.trans hleft3
  constructor
  · exact (hcell (c.h-2) (by rw [hpos]; omega) (by rw [hpos]; omega)).symm.trans hleft2
  constructor
  · exact (hcell (c.h-1) (by rw [hpos]; omega) (by rw [hpos]; omega)).symm.trans hleft1
  · rw [←hpos]
    exact hzero

/-- The exact even F/1 corridor execution, including its final D/0-E/0-A/0
    tail. It uses only the original auxiliary transition table. -/
theorem f1_even_run_exact (n : Nat) (t : Int → Bool) (h : Int)
    (hhead : t h = true)
    (hones : ∀ j : Nat, j < 2*(n+1) →
      t (h+1+(j:Int)) = true)
    (hzero : t (h+1+((2*(n+1):Nat):Int)) = false) :
    shuttleRun (1+(2*(n+1)+3)) (⟨.F,h,t⟩ : Conf) =
      some (f1EvenResult n t h) := by
  let t0 := setBit t h false
  let s : Int := h+1
  let p : Int := s+((2*(n+1):Nat):Int)
  let v := evenSweepTape (n+1) t0 s
  let v1 := setBit v p false
  let v2 := setBit v1 (p-1) true
  let b : Conf := ⟨.B,p+1,setBit v2 p true⟩
  have hstepF : next (⟨.F,h,t⟩ : Conf) = some ⟨.D,s,t0⟩ := by
    simp [next,hhead,t0,s]
  have hones0 : ∀ j : Nat, j < 2*(n+1) → t0 (s+(j:Int)) = true := by
    intro j hj
    have ht0 : t0 (s+(j:Int)) = t (s+(j:Int)) := by
      dsimp [t0]
      exact setBit_apply_ne t h (s+(j:Int)) false (by dsimp [s]; omega)
    rw [ht0]
    simpa [s] using hones j hj
  have hzero0 : t0 (s+((2*(n+1):Nat):Int)) = false := by
    have ht0 : t0 (s+((2*(n+1):Nat):Int)) =
        t (s+((2*(n+1):Nat):Int)) := by
      dsimp [t0]
      exact setBit_apply_ne t h (s+((2*(n+1):Nat):Int)) false
        (by dsimp [s]; omega)
    rw [ht0]
    simpa [s] using hzero
  have hSweep : shuttleRun (2*(n+1)) (⟨.D,s,t0⟩ : Conf) =
      some ⟨.D,p,v⟩ := by
    simpa [s,p,v] using evenSweep (n+1) t0 s hones0
  have hz : v p = false := by
    calc
      v p = t0 p := evenSweepTape_right (n+1) t0 s p (by dsimp [p,s]; omega)
      _ = false := by simpa [p,s] using hzero0
  have hlast : v (p-1) = false := by
    simpa [v,p,s] using evenSweepTape_last n t0 s
  have hreadE : v1 (p-1) = false := by
    simp [v1,setBit,show p-1 ≠ p by omega,hlast]
  have hreadA : v2 p = false := by
    simp [v2,v1,setBit,show p ≠ p-1 by omega,hz]
  have hs1 : next (⟨.D,p,v⟩ : Conf) = some ⟨.E,p-1,v1⟩ := by
    simp [next,hz,v1]
  have hs2 : next (⟨.E,p-1,v1⟩ : Conf) = some ⟨.A,p,v2⟩ := by
    simp [next,hreadE,v2]
  have hs3 : next (⟨.A,p,v2⟩ : Conf) = some b := by
    simp [next,hreadA,b]
  have htail : shuttleRun 3 (⟨.D,p,v⟩ : Conf) = some b := by
    simp [shuttleRun,hs1,hs2,hs3]
  have hDRun : shuttleRun (2*(n+1)+3) (⟨.D,s,t0⟩ : Conf) = some b := by
    rw [shuttleRun_add (2*(n+1)) 3]
    simp [hSweep,htail]
  have hOne : shuttleRun 1 (⟨.F,h,t⟩ : Conf) = some ⟨.D,s,t0⟩ := by
    simp [shuttleRun,hstepF]
  have hRun : shuttleRun (1+(2*(n+1)+3)) (⟨.F,h,t⟩ : Conf) = some b := by
    rw [shuttleRun_add 1 (2*(n+1)+3)]
    rw [hOne]
    simp [hDRun]
  have hbEq : b = f1EvenResult n t h := by
    dsimp [b,f1EvenResult,f1EvenTape,t0,s,p,v,v1,v2]
  rw [hbEq] at hRun
  exact hRun

/-- The even F/1 result preserves the tape weakly left of the original head,
    except for the F/1 transition's write of zero at that head. -/
theorem f1EvenResult_left (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : x ≤ h) :
    (f1EvenResult n t h).tape x = setBit t h false x := by
  change f1EvenTape n t h x = setBit t h false x
  unfold f1EvenTape
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)) x true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)-1) x true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)) x false (by omega)]
  exact evenSweepTape_left (n+1) (setBit t h false) (h+1) x (by omega)

theorem f1EvenResult_A (n : Nat) (t : Int → Bool) (h : Int) :
    (f1EvenResult n t h).tape
      (h+1+((2*(n+1):Nat):Int)) = true := by
  change f1EvenTape n t h (h+1+((2*(n+1):Nat):Int)) = true
  unfold f1EvenTape
  exact setBit_apply_eq _ _ true

theorem f1EvenResult_E (n : Nat) (t : Int → Bool) (h : Int) :
    (f1EvenResult n t h).tape
      (h+1+((2*(n+1):Nat):Int)-1) = true := by
  change f1EvenTape n t h (h+1+((2*(n+1):Nat):Int)-1) = true
  unfold f1EvenTape
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int))
    (h+1+((2*(n+1):Nat):Int)-1) true (by omega)]
  exact setBit_apply_eq _ _ true

/-- The D/F-written cells in the exact even F/1 endpoint. -/
theorem f1EvenResult_D (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j ≤ n) :
    (f1EvenResult n t h).tape (h+1+2*(j:Int)) = true := by
  change f1EvenTape n t h (h+1+2*(j:Int)) = true
  unfold f1EvenTape
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int))
    (h+1+2*(j:Int)) true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)-1)
    (h+1+2*(j:Int)) true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int))
    (h+1+2*(j:Int)) false (by omega)]
  exact evenSweepTape_D (n+1) (setBit t h false) (h+1) j (by omega)

theorem f1EvenResult_F (n : Nat) (t : Int → Bool) (h : Int)
    (j : Nat) (hj : j < n) :
    (f1EvenResult n t h).tape (h+2+2*(j:Int)) = false := by
  change f1EvenTape n t h (h+2+2*(j:Int)) = false
  unfold f1EvenTape
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int))
    (h+2+2*(j:Int)) true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)-1)
    (h+2+2*(j:Int)) true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int))
    (h+2+2*(j:Int)) false (by omega)]
  rw [show h+2+2*(j:Int) = h+1+2*(j:Int)+1 by omega]
  exact evenSweepTape_F (n+1) (setBit t h false) (h+1) j (by omega)

/-- Every cell strictly beyond the even sweep and its tail is untouched. -/
theorem f1EvenResult_right (n : Nat) (t : Int → Bool) (h x : Int)
    (hx : h+1+((2*(n+1):Nat):Int) < x) :
    (f1EvenResult n t h).tape x = t x := by
  change f1EvenTape n t h x = t x
  unfold f1EvenTape
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)) x true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)-1) x true (by omega)]
  rw [setBit_apply_ne _ (h+1+((2*(n+1):Nat):Int)) x false (by omega)]
  have hs := evenSweepTape_right (n+1) (setBit t h false) (h+1) x (by omega)
  rw [setBit_apply_ne t h x false (by omega)] at hs
  exact hs

/-- The last F-written cell is zero, including the n=0 boundary case. -/
theorem f1EvenResult_lastF (n : Nat) (t : Int → Bool) (h : Int) :
    (f1EvenResult n t h).tape (h+2*(n:Int)) = false := by
  cases n with
  | zero =>
      have hs := f1EvenResult_left 0 t h h (by omega)
      simpa [setBit] using hs
  | succ n =>
      have hs := f1EvenResult_F (n+1) t h n (by omega)
      have heq : h+2*((n+1:Nat):Int) = h+2+2*(n:Int) := by omega
      rw [heq]
      exact hs

/-- Convert the even F/1 corridor into the exact finite B/0 ladder which
    reaches the fatal C gate. The left marker 1100 is the terminal 00 11
    of this ladder; the alternating cells are produced by the D/F sweep. -/
theorem f1_even_result_markerB0Pattern (n : Nat) (t : Int → Bool) (h : Int)
    (hleft1 : t (h-1) = false)
    (hleft2 : t (h-2) = true)
    (hleft3 : t (h-3) = true)
    (hnext : t (h+2+((2*(n+1):Nat):Int)) = false) :
    MarkerB0Pattern n (f1EvenResult n t h) := by
  let b := f1EvenResult n t h
  have hpos : b.h = h+2+((2*(n+1):Nat):Int) := by
    simp [b,f1EvenResult] <;> omega
  have hcur : b.tape b.h = false := by
    rw [hpos]
    exact (f1EvenResult_right n t h _ (by omega)).trans hnext
  have hleft1' : b.tape (b.h-1) = true := by
    have heq : b.h-1 = h+1+((2*(n+1):Nat):Int) := by rw [hpos]; omega
    rw [heq]
    simpa [b] using f1EvenResult_A n t h
  have hleft2' : b.tape (b.h-2) = true := by
    have heq : b.h-2 = h+1+((2*(n+1):Nat):Int)-1 := by rw [hpos]; omega
    rw [heq]
    simpa [b] using f1EvenResult_E n t h
  have hleft3' : b.tape (b.h-3) = true := by
    have heq : b.h-3 = h+1+2*(n:Int) := by rw [hpos]; omega
    rw [heq]
    exact f1EvenResult_D n t h n (by omega)
  refine ⟨⟨by simp [b,f1EvenResult],hcur⟩,hleft1',hleft2',hleft3',?_,?_,?_,?_,?_⟩
  · intro i hi
    let j : Nat := n-1-i
    have hj : j < n := by dsimp [j]; omega
    have hFidx : b.h-4-2*(i:Int) = h+2+2*(j:Int) := by
      rw [hpos]
      dsimp [j]
      omega
    have hDidx : b.h-5-2*(i:Int) = h+1+2*(j:Int) := by
      rw [hpos]
      dsimp [j]
      omega
    constructor
    · rw [hFidx]
      exact f1EvenResult_F n t h j hj
    · rw [hDidx]
      exact f1EvenResult_D n t h j (by omega)
  · have heq : b.h-4-2*(n:Int) = h := by rw [hpos]; omega
    rw [heq]
    have hs := f1EvenResult_left n t h h (by omega)
    simpa [setBit] using hs
  · have heq : b.h-5-2*(n:Int) = h-1 := by rw [hpos]; omega
    rw [heq]
    have hs := f1EvenResult_left n t h (h-1) (by omega)
    have hs' : (f1EvenResult n t h).tape (h-1) = t (h-1) := by
      simpa [setBit,show h-1 ≠ h by omega] using hs
    simpa [b] using hs'.trans hleft1
  · have heq : b.h-6-2*(n:Int) = h-2 := by rw [hpos]; omega
    rw [heq]
    have hs := f1EvenResult_left n t h (h-2) (by omega)
    have hs' : (f1EvenResult n t h).tape (h-2) = t (h-2) := by
      simpa [setBit,show h-2 ≠ h by omega] using hs
    simpa [b] using hs'.trans hleft2
  · have heq : b.h-7-2*(n:Int) = h-3 := by rw [hpos]; omega
    rw [heq]
    have hs := f1EvenResult_left n t h (h-3) (by omega)
    have hs' : (f1EvenResult n t h).tape (h-3) = t (h-3) := by
      simpa [setBit,show h-3 ≠ h by omega] using hs
    simpa [b] using hs'.trans hleft3

/-- A finite successful shuttleRun prefix transports genuine blank-root
    reachability to its exact endpoint. -/
theorem reachable_of_shuttleRun {n : Nat} {c d : Conf}
    (hc : Reach c) (hr : shuttleRun n c = some d) : Reach d := by
  induction n generalizing c with
  | zero =>
      simp [shuttleRun] at hr
      cases hr
      exact hc
  | succ n ih =>
      cases hs : next c with
      | none => simp [shuttleRun,hs] at hr
      | some c' =>
          have ht : shuttleRun n c' = some d := by
            simpa [shuttleRun,hs] using hr
          exact ih (Reach.follow hc hs) ht

/-- Every reached F/1 state with left suffix 110 and an even positive
    right one-run followed by two zeros is a genuine blank-root halter.
    The conclusion is a reached stopping configuration, not a simulation
    conjecture. -/
theorem f1_even_double_zero_halts (n : Nat) (c : Conf)
    (hc : Reach c) (hF : c.q = .F)
    (hhead : c.tape c.h = true)
    (hleft1 : c.tape (c.h-1) = false)
    (hleft2 : c.tape (c.h-2) = true)
    (hleft3 : c.tape (c.h-3) = true)
    (hones : ∀ j : Nat, j < 2*(n+1) →
      c.tape (c.h+1+(j:Int)) = true)
    (hzero : c.tape (c.h+1+((2*(n+1):Nat):Int)) = false)
    (hzero2 : c.tape (c.h+2+((2*(n+1):Nat):Int)) = false) :
    ∃ a, Reach a ∧ next a = none := by
  rcases c with ⟨q,h,t⟩
  change q = .F at hF
  subst q
  let b := f1EvenResult n t h
  have hrun := f1_even_run_exact n t h hhead hones hzero
  have hb : Reach b := by
    apply reachable_of_shuttleRun hc
    simpa [b] using hrun
  have hp : MarkerB0Pattern n b :=
    f1_even_result_markerB0Pattern n t h hleft1 hleft2 hleft3 hzero2
  obtain ⟨g,hg,hgate⟩ := markerB0Pattern_to_CGate n b hb hp
  obtain ⟨d,hd,hgate⟩ := reached_C_gate_has_D_gate g hg hgate
  exact reached_gate_has_stop d hd hgate

theorem next_B_one (b : Conf) (hB : b.q = .B)
    (hread : b.tape b.h = true) :
    next b = some ⟨.F,b.h-1,setBit b.tape b.h true⟩ := by
  rcases b with ⟨q,pos,tape⟩
  change q = .B at hB
  subst q
  change tape pos = true at hread
  simp [next,hread]

/-- If the cell after the even corridor's terminating zero is one, the B
    endpoint instead steps left to a new F/1 state. Its left context is
    exactly 011, while the original 1100 marker is now strictly behind it. -/
theorem f1_even_endpoint_one_to_F1 (n : Nat) (t : Int → Bool) (h : Int)
    (hc : Reach (⟨.F,h,t⟩ : Conf))
    (hhead : t h = true)
    (hones : ∀ j : Nat, j < 2*(n+1) →
      t (h+1+(j:Int)) = true)
    (hzero : t (h+1+((2*(n+1):Nat):Int)) = false)
    (hleft1 : t (h-1) = false)
    (hleft2 : t (h-2) = true)
    (hleft3 : t (h-3) = true)
    (hnext : t (h+2+((2*(n+1):Nat):Int)) = true) :
    ∃ f, Reach f ∧ next (f1EvenResult n t h) = some f ∧
      f.q = .F ∧
      f.h = h+1+((2*(n+1):Nat):Int) ∧
      f.tape f.h = true ∧
      f.tape (f.h-1) = true ∧
      f.tape (f.h-2) = true ∧
      f.tape (f.h-3) = false ∧
      f.tape (h-3) = true ∧
      f.tape (h-2) = true ∧
      f.tape (h-1) = false ∧
      f.tape h = false ∧
      h < f.h := by
  let b := f1EvenResult n t h
  let p : Int := h+1+((2*(n+1):Nat):Int)
  let f : Conf := ⟨.F,p,setBit b.tape (p+1) true⟩
  have hrun := f1_even_run_exact n t h hhead hones hzero
  have hb : Reach b := reachable_of_shuttleRun hc (by simpa [b] using hrun)
  have hpos : b.h = p+1 := by simp [b,f1EvenResult,p] <;> omega
  have hnext' : t (p+1) = true := by
    have heq : p+1 = h+2+((2*(n+1):Nat):Int) := by dsimp [p]; omega
    rw [heq]
    exact hnext
  have hread : b.tape b.h = true := by
    rw [hpos]
    exact (f1EvenResult_right n t h (p+1) (by dsimp [p]; omega)).trans hnext'
  have hq : b.q = .B := by simp [b,f1EvenResult]
  have hdest : b.h-1 = p := by rw [hpos]; omega
  have hstep0 := next_B_one b hq hread
  have hstep : next b = some f := by
    simpa [f,hpos,hdest] using hstep0
  have hfhead : f.tape f.h = true := by
    have hBcell : b.tape p = true := by
      simpa [b,p] using f1EvenResult_A n t h
    change setBit b.tape (p+1) true p = true
    rw [setBit_apply_ne b.tape (p+1) p true (by omega)]
    exact hBcell
  have hfleft1 : f.tape (f.h-1) = true := by
    have hBcell : b.tape (p-1) = true := by
      simpa [b,p] using f1EvenResult_E n t h
    change setBit b.tape (p+1) true (p-1) = true
    rw [setBit_apply_ne b.tape (p+1) (p-1) true (by omega)]
    exact hBcell
  have hfleft2 : f.tape (f.h-2) = true := by
    have hBcell : b.tape (p-2) = true := by
      have heq : p-2 = h+1+2*(n:Int) := by dsimp [p]; omega
      rw [heq]
      simpa [b] using f1EvenResult_D n t h n (by omega)
    change setBit b.tape (p+1) true (p-2) = true
    rw [setBit_apply_ne b.tape (p+1) (p-2) true (by omega)]
    exact hBcell
  have hfleft3 : f.tape (f.h-3) = false := by
    have hBcell : b.tape (p-3) = false := by
      have heq : p-3 = h+2*(n:Int) := by dsimp [p]; omega
      rw [heq]
      simpa [b] using f1EvenResult_lastF n t h
    change setBit b.tape (p+1) true (p-3) = false
    rw [setBit_apply_ne b.tape (p+1) (p-3) true (by omega)]
    exact hBcell
  have hfar (x : Int) (hx : x ≤ h) :
      f.tape x = setBit t h false x := by
    have hbfar := f1EvenResult_left n t h x hx
    change setBit b.tape (p+1) true x = setBit t h false x
    rw [setBit_apply_ne b.tape (p+1) x true (by dsimp [p]; omega)]
    exact hbfar
  have hmark3 : f.tape (h-3) = true := by
    rw [hfar (h-3) (by omega)]
    simpa [setBit,show h-3 ≠ h by omega] using hleft3
  have hmark2 : f.tape (h-2) = true := by
    rw [hfar (h-2) (by omega)]
    simpa [setBit,show h-2 ≠ h by omega] using hleft2
  have hmark1 : f.tape (h-1) = false := by
    rw [hfar (h-1) (by omega)]
    simpa [setBit,show h-1 ≠ h by omega] using hleft1
  have hmark0 : f.tape h = false := by
    rw [hfar h (by omega)]
    simp [setBit]
  have hf : Reach f := Reach.follow hb hstep
  refine ⟨f,hf,hstep,rfl,?_,hfhead,hfleft1,hfleft2,hfleft3,
    hmark3,hmark2,hmark1,hmark0,?_⟩
  · rfl
  · change h < p
    dsimp [p]
    omega

#print axioms BB6Root119.to_F
#print axioms BB6Root119.reached_F_left_zero_parent
#print axioms BB6Root119.to_B
#print axioms BB6Root119.reached_F_left_zero_two_step_parent
#print axioms BB6Root119.A0_B1_F1_parent_has_1100
#print axioms BB6Root119.A0_B1_F1_parent_has_1100
#print axioms BB6Root119.f1_even_run_exact
#print axioms BB6Root119.f1_even_result_markerB0Pattern
#print axioms BB6Root119.f1_even_double_zero_halts
#print axioms BB6Root119.f1_even_endpoint_one_to_F1

end BB6Root119
