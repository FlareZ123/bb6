import LowOddSource
import HeadDisplacement
import BubblePrefixHeadBound
import JPhysicalPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429LowOddPhysical
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429PhysicalBridge BB429LowOddSource

private theorem getD_append {α : Type} (xs ys : List α) (j : Nat) (d : α) :
    (xs ++ ys).getD j d =
      if j < xs.length then xs.getD j d else ys.getD (j-xs.length) d := by
  induction xs generalizing j with
  | nil => simp
  | cons a xs ih =>
    cases j with
    | zero => simp
    | succ j => simpa using ih j

private theorem ones_getD (n j : Nat) :
    (ones n).getD j false = decide (j < n) := by
  induction n generalizing j with
  | zero => simp [ones]
  | succ n ih =>
    cases j with
    | zero => simp [ones]
    | succ j => simpa [ones,List.replicate_succ] using ih j

private theorem tens_getD (m j : Nat) :
    (tens m).getD j false = decide (j < 2*m ∧ j%2=0) := by
  induction m generalizing j with
  | zero => simp [tens]
  | succ m ih =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
        change (tens m).getD j false =
          decide (j+2 < 2*(m+1) ∧ (j+2)%2=0)
        rw [ih]
        have h : (j<2*m ∧ j%2=0) ↔
          (j+2<2*(m+1) ∧ (j+2)%2=0) := by omega
        simp [h]

private theorem tens_length (m : Nat) : (tens m).length = 2*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [tens,ih]; omega

private theorem stageOdd_left_char (v n j : Nat) :
    (stageOdd v n).left.getD j false =
      decide (j < 4*v+4*n+14 ∧
        ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by
  change (ones (4*v+4) ++ (tens (2*(n+1)) ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v+4)).length = 4*v+4 := by simp [ones]
  rw [hlen]
  by_cases hj : j<4*v+4
  · rw [if_pos hj,ones_getD]
    have hp : j < 4*v+4*n+14 ∧
      ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1) := by omega
    simp [hj,hp]
  · rw [if_neg hj,getD_append]
    have hlen2 : (tens (2*(n+1))).length=4*n+4 := by
      rw [tens_length]
      omega
    rw [hlen2]
    by_cases ht : j-(4*v+4)<4*n+4
    · rw [if_pos ht,tens_getD]
      have hp :
          ((j-(4*v+4))<2*(2*(n+1)) ∧ ((j-(4*v+4))%2=0)) ↔
          (j < 4*v+4*n+14 ∧
            ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by omega
      simp [hp]
    · rw [if_neg ht,ones_getD]
      have hp : j-(4*v+4)-(4*n+4)<6 ↔
          (j < 4*v+4*n+14 ∧
            ¬(4*v+4 ≤ j ∧ j<4*v+4*n+8 ∧ j%2=1)) := by omega
      simp [hp]

/-- The complete two-counter marked-set formula after v+1 bubble repairs,
    covering every cell of the bi-infinite tape. -/
private theorem stageOdd_tape_character (v n : Nat) (x : Int) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1) x =
    decide (((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
      ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
        x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
       x=2*(v:Int)+4)) := by
  have hp : (negFillTest (v+1) x ∨ jMark (v+2*n+3) (2*v+1) x) ↔
      (((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
          x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
         x=2*(v:Int)+4)) := by
    unfold negFillTest jMark jHole
    omega
  unfold negFill jTape
  by_cases hfill : negFillTest (v+1) x
  · simp only [if_pos hfill]
    exact (decide_eq_true (hp.mp (Or.inl hfill))).symm
  · by_cases hj : jMark (v+2*n+3) (2*v+1) x
    · simp only [if_neg hfill, if_pos hj]
      exact (decide_eq_true (hp.mp (Or.inr hj))).symm
    · have hn : ¬(((-2*(v:Int)-4*(n:Int)-12 ≤ x ∧ x ≤ 2*(v:Int)+2 ∧
        ¬(-2*(v:Int)-4*(n:Int)-6 ≤ x ∧
          x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
         x=2*(v:Int)+4)) := by
        intro hh
        rcases hp.mpr hh with hz | hj'
        · exact hfill hz
        · exact hj hj'
      simp only [if_neg hfill, if_neg hj]
      exact (decide_eq_false hn).symm

private theorem stageOdd_rep_left (v n j : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1)
      ((2*(v:Int)+2)-((j:Int)+1)) =
    (stageOdd v n).left.getD j false := by
  rw [stageOdd_tape_character,stageOdd_left_char]
  apply decide_eq_decide.mpr
  omega

private theorem stageOdd_rep_right (v n j : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1)
      ((2*(v:Int)+2)+((j:Int)+1)) =
    (stageOdd v n).right.getD j false := by
  rw [stageOdd_tape_character]
  have hr : ([false,true] : List Bool).getD j false = decide (j=1) := by
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  change _ = ([false,true] : List Bool).getD j false
  rw [hr]
  apply decide_eq_decide.mpr
  omega

private theorem stageOdd_rep_center (v n : Nat) :
  negFill (jTape (v+2*n+3) (2*v+1)) (v+1) (2*(v:Int)+2) = true := by
  rw [stageOdd_tape_character]
  have hp : (-2*(v:Int)-4*(n:Int)-12 ≤ 2*(v:Int)+2 ∧
      2*(v:Int)+2 ≤ 2*(v:Int)+2 ∧
      ¬(-2*(v:Int)-4*(n:Int)-6 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≤ -2*(v:Int)-4 ∧ (2*(v:Int)+2)%2=0)) := by omega
  exact decide_eq_true (Or.inl hp)

theorem stageOdd_represented (v n : Nat) :
    Represents (stageOdd v n)
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)} := by
  exact ⟨rfl,stageOdd_rep_center v n,stageOdd_rep_left v n,
    stageOdd_rep_right v n⟩

private theorem lowOdd_holes (v n i : Nat) (hi : i < v+1) :
    jTape (v+2*n+3) (2*v+1) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+2*n+3) (2*v+1)
      (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+2*n+3) (2*v+1)
      (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem lowOdd_odds (v n : Nat) (x : Int)
    (hlo : -2*((v+1:Nat):Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+2*n+3) (2*v+1) x = true := by
  have hj : jMark (v+2*n+3) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem lowOdd_right (v n : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*((v+1:Nat):Int)) :
    jTape (v+2*n+3) (2*v+1) x = true := by
  have hj : jMark (v+2*n+3) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem physical_compose (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add',h1]
  exact h2

/-- Original table, exact physical primitive steps, all infinite tape
    cells and head translation. All odd deficits 4k+1 with k>=1. -/
theorem lowOdd_raw_head (v n : Nat) :
    ∃ c', BB6Coverage.run target429 (4*v*v+22*v+22*n+100)
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} = some c' ∧
      Represents (junc (2*n+6) 0 (4*v+2)) c' ∧
      c'.head = 2 - ((2*v : Nat) : Int) := by
  have hfirst : BB6Coverage.run target429
      (4*(v+1)*(v+1)+2*(v+1))
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} =
      some {state:=A,head:=2*(v:Int)+2,
            tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)} := by
    have hhead_cast : 2*((v+1:Nat):Int) = 2*(v:Int)+2 := by omega
    simpa only [hhead_cast] using
      (multi_bubble_prefix target429 (v+1) (v+1)
        (jTape (v+2*n+3) (2*v+1)) (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (lowOdd_holes v n) (lowOdd_odds v n) (lowOdd_right v n))
  obtain ⟨c',hsecond,hrep,hhead⟩ :=
      BB429DeltaPhysicalBridge.source_runWithDelta_rep (12*v+22*n+94)
        (stageOdd v n)
        {state:=A,head:=2*(v:Int)+2,
         tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)}
        (stageOdd_represented v n) (junc (2*n+6) 0 (4*v+2))
        (-((4*v : Nat) : Int)) (stageOdd_to_junc_delta v n)
  have htotal := physical_compose
      (4*(v+1)*(v+1)+2*(v+1)) (12*v+22*n+94)
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)}
      {state:=A,head:=2*(v:Int)+2,
       tape:=negFill (jTape (v+2*n+3) (2*v+1)) (v+1)}
      c' hfirst hsecond
  have htime : (4*(v+1)*(v+1)+2*(v+1))+(12*v+22*n+94) =
      4*v*v+22*v+22*n+100 := by
    simp [Nat.add_mul, Nat.mul_add]
    omega
  have hhead' : c'.head = 2 - ((2*v:Nat):Int) := by
    have hh := hhead
    simp only at hh
    omega
  exact ⟨c',by simpa only [htime] using htotal,hrep,hhead'⟩

#print axioms stageOdd_represented
#print axioms lowOdd_raw_head


/-- Canonical physical configuration at the beginning of the odd stage. -/
def stageOddConfig (v n : Nat) : Config :=
  {state:=A,head:=2*(v:Int)+2,tape:=stageOddTape v n}

/-- The odd stage splits into an extremal left sweep, an extremal right
    sweep, and a final four-step right sweep ending at C/0.  Each source
    segment is lifted to the original physical machine. -/
private theorem stageOdd_decomposition (v n : Nat) :
    ∃ c1 c2 c3 : Config,
      run target429 (4*v+6) (stageOddConfig v n) = some c1 ∧
      run target429 (4*v+6) c1 = some c2 ∧
      run target429 4 c2 = some c3 ∧
      c1.head = (stageOddConfig v n).head - (4*v+6) ∧
      c2.head = (stageOddConfig v n).head ∧
      c3.head = (stageOddConfig v n).head + 4 ∧
      c3.state.val = 2 ∧
      c3.tape c3.head = false ∧
      c3.tape (c3.head+1) = false := by
  let zMid : Zipper :=
    z 0 (tens (2*n+1) ++ ones 6) false (tens (2*v+3) ++ [false,true])
  let zAR : Zipper :=
    z 0 (ones (4*v+6) ++ tens (2*n+1) ++ ones 6) false [false,true]
  let zC0 : Zipper :=
    z 2 (true::false::true::true::(ones (4*v+6) ++ tens (2*n+1) ++ ones 6))
      false []
  have hAF := BB429Low3Delta.af_pairs_delta
    (2*v+2) (tens (2*(n+1)) ++ ones 6) [false,true]
  have h2 := af_tail_delta
    (tens (2*n+1) ++ ones 6) (tens (2*v+2) ++ [false,true])
  have hleft : runWithDelta (4*v+6) (stageOdd v n) =
      some (zMid, -(4*v+6)) := by
    have htime : 4*v+6 = (4*v+4)+2 := by omega
    rw [htime, runWithDelta_add]
    rw [hAF]
    simp only [Option.bind_some]
    rw [h2]
    simp [zMid, tens, List.append_assoc]
  have hAR0 := BB429Low3Delta.ar_pairs_delta
    (2*v+3) (tens (2*n+1) ++ ones 6) [false,true]
  have hAR : runWithDelta (4*v+6) zMid =
      some (zAR, (4*v+6 : Int)) := by
    simpa [zMid,zAR,Nat.mul_add,Nat.add_mul,List.append_assoc] using hAR0
  have h4 : runWithDelta 4 zAR = some (zC0, (4 : Int)) := by
    simpa [zAR,zC0,List.append_assoc] using
      low3_tail_delta (ones (4*v+6) ++ (tens (2*n+1) ++ ones 6))
  have hrepStage : Represents (stageOdd v n) (stageOddConfig v n) := by
    simpa [stageOddConfig] using stageOdd_represented v n
  obtain ⟨c1,hleftP,hrep1,hhead1⟩ :=
    source_runWithDelta_rep (4*v+6) (stageOdd v n) (stageOddConfig v n)
      hrepStage zMid (-(4*v+6)) hleft
  obtain ⟨c2,hARP,hrep2,hhead2⟩ :=
    source_runWithDelta_rep (4*v+6) zMid c1 hrep1 zAR (4*v+6) hAR
  obtain ⟨c3,h4P,hrep3,hhead3⟩ :=
    source_runWithDelta_rep 4 zAR c2 hrep2 zC0 4 h4
  rcases hrep3 with ⟨hstate,hcur,hleftRep,hrightRep⟩
  have hstate' : c3.state.val = 2 := by
    simpa [zC0] using hstate
  have hcur' : c3.tape c3.head = false := by
    simpa [zC0] using hcur
  have hright' : c3.tape (c3.head+1) = false := by
    have h := hrightRep 0
    change c3.tape (c3.head+1) = false at h
    exact h
  have hhead1' : c1.head = (stageOddConfig v n).head - (4*v+6) := by
    simpa using hhead1
  have hhead2' : c2.head = (stageOddConfig v n).head := by
    rw [hhead2,hhead1']
    omega
  have hhead3' : c3.head = (stageOddConfig v n).head + 4 := by
    rw [hhead3,hhead2']
  exact ⟨c1,c2,c3,hleftP,hARP,h4P,hhead1',hhead2',hhead3',
    hstate',hcur',hright'⟩

/-- Before the final four-step C/0 tail, the odd stage never exceeds
    three cells beyond its entry head. -/
private theorem stageOdd_prefix_head_bound (v n s : Nat)
    (hs : s ≤ 8*v+15) :
    ∃ d : Config,
      run target429 s (stageOddConfig v n) = some d ∧
      d.head ≤ (stageOddConfig v n).head + 3 := by
  obtain ⟨c1,c2,c3,hleft,hAR,h4,hhead1,hhead2,hhead3,
      hstate,hcur,hright⟩ := stageOdd_decomposition v n
  let cStage : Config := stageOddConfig v n
  let L : Nat := 4*v+6
  have hhead1L : c1.head = cStage.head - (L:Int) := by
    simpa [cStage,L] using hhead1
  have hdisp1 : c1.head-cStage.head = -(L:Int) := by
    rw [hhead1L]
    omega
  have hdisp2 : c2.head-c1.head = (L:Int) := by
    rw [hhead2,hhead1L]
    omega
  have hdisp3 : c3.head-c2.head = 4 := by
    rw [hhead3,hhead2]
    omega
  by_cases hs1 : s ≤ L
  · obtain ⟨d,hpre⟩ :=
      run_prefix_exists target429 L s cStage c1 hleft hs1
    have hleftExact :=
      run_prefix_left_extremal target429 L s cStage d c1
        hleft hpre hs1 hdisp1
    exact ⟨d,hpre,by rw [hleftExact]; omega⟩
  · by_cases hs2 : s ≤ 2*L
    · let r : Nat := s-L
      have hr : r ≤ L := by
        dsimp [r]
        omega
      obtain ⟨d,hpre2⟩ :=
        run_prefix_exists target429 L r c1 c2 hAR hr
      have hrightExact :=
        run_prefix_right_extremal target429 L r c1 d c2
          hAR hpre2 hr hdisp2
      have htime : s=L+r := by
        dsimp [r]
        omega
      have hpre : run target429 s cStage = some d := by
        rw [htime,run_add',hleft]
        simpa using hpre2
      exact ⟨d,hpre,by rw [hrightExact,hhead1L]; omega⟩
    · let r : Nat := s-2*L
      have hL : 8*v+15 = 2*L+3 := by
        dsimp [L]
        omega
      have hr : r ≤ 3 := by
        dsimp [r]
        omega
      obtain ⟨d,hpre3⟩ :=
        run_prefix_exists target429 4 r c2 c3 h4 (by omega)
      have hrightExact :=
        run_prefix_right_extremal target429 4 r c2 d c3
          h4 hpre3 (by omega) hdisp3
      have hleftAR : run target429 (L+L) cStage = some c2 := by
        rw [run_add',hleft]
        exact hAR
      have htime : s=(L+L)+r := by
        dsimp [r]
        omega
      have hpre : run target429 s cStage = some d := by
        rw [htime,run_add',hleftAR]
        simpa using hpre3
      exact ⟨d,hpre,by rw [hrightExact,hhead2]; omega⟩

/-- The first C/0 event on the low-odd branch is a strict physical
    right-head record: every earlier primitive prefix stays at least one
    cell behind it, and its right neighbour is blank. -/
theorem lowOdd_first_C0_frontier (v n : Nat) :
    ∃ cC : Config,
      run target429 (4*v*v+18*v+22)
        {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} = some cC ∧
      cC.head = 2*(v:Int)+6 ∧
      cC.state.val = 2 ∧
      cC.tape cC.head = false ∧
      cC.tape (cC.head+1) = false ∧
      (∀ t : Nat, t < 4*v*v+18*v+22 →
        ∀ d : Config,
          run target429 t
            {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} = some d →
          d.head < cC.head) := by
  let tape : Int → Bool := jTape (v+2*n+3) (2*v+1)
  let c0 : Config := {state:=A,head:=0,tape:=tape}
  let cStage : Config := stageOddConfig v n
  let B : Nat := 4*(v+1)*(v+1)+2*(v+1)
  have hfirst : run target429 B c0 = some cStage := by
    have hhead : 2*((v+1:Nat):Int) = 2*(v:Int)+2 := by omega
    simpa only [hhead,stageOddConfig,stageOddTape,c0,tape,B] using
      multi_bubble_prefix target429 (v+1) (v+1) tape (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (lowOdd_holes v n) (lowOdd_odds v n) (lowOdd_right v n)
  have hBubblePrefixBound :
      ∀ t : Nat, t ≤ B →
        ∃ d : Config, run target429 t c0 = some d ∧
          d.head ≤ 2*(v:Int)+2 := by
    intro t ht
    obtain ⟨d,hpre,hbound⟩ :=
      multi_bubble_prefix_head_bound target429 (v+1) (v+1) t tape
        (by omega) (by decide) (by decide) (by decide) (by decide)
        (lowOdd_holes v n) (lowOdd_odds v n) (lowOdd_right v n)
        (by simpa [B] using ht)
    exact ⟨d,hpre,by omega⟩
  obtain ⟨c1,c2,cC,hleft,hAR,h4,hhead1,hhead2,hhead3,
      hstate,hcur,hright⟩ := stageOdd_decomposition v n
  let L : Nat := 4*v+6
  have hleftAR : run target429 (L+L) cStage = some c2 := by
    rw [run_add',hleft]
    exact hAR
  have hstageFull : run target429 (L+L+4) cStage = some cC := by
    rw [run_add',hleftAR]
    exact h4
  have hS : 8*v+16 = L+L+4 := by
    dsimp [L]
    omega
  have hstage : run target429 (8*v+16) cStage = some cC := by
    rw [hS]
    exact hstageFull
  have htotal : run target429 (B+8*v+16) c0 = some cC := by
    rw [run_add',hfirst]
    exact hstage
  have htime : B+8*v+16 = 4*v*v+18*v+22 := by
    dsimp [B]
    omega
  have htotal' : run target429 (4*v*v+18*v+22) c0 = some cC := by
    simpa [htime] using htotal
  have hheadC : cC.head = 2*(v:Int)+6 := by
    rw [hhead3]
    simp [stageOddConfig]
    omega
  have hstageHead : cStage.head = 2*(v:Int)+2 := by
    simp [cStage,stageOddConfig]
  have hprev :
      ∀ t : Nat, t < 4*v*v+18*v+22 →
        ∀ d : Config, run target429 t c0 = some d →
          d.head ≤ 2*(v:Int)+5 := by
    intro t ht d hd
    by_cases htb : t ≤ B
    · obtain ⟨d',hpre,hbound⟩ := hBubblePrefixBound t htb
      have heq : d=d' := Option.some.inj (hd.symm.trans hpre)
      subst d
      omega
    · let s : Nat := t-B
      have hs : s ≤ 8*v+15 := by
        have hBS : B+8*v+16 = 4*v*v+18*v+22 := htime
        dsimp [s]
        omega
      obtain ⟨d',hseg,hbound⟩ := stageOdd_prefix_head_bound v n s hs
      have htime2 : t=B+s := by
        dsimp [s]
        omega
      have hpre : run target429 t c0 = some d' := by
        rw [htime2,run_add',hfirst]
        exact hseg
      have heq : d=d' := Option.some.inj (hd.symm.trans hpre)
      subst d
      omega
  have hrecord :
      ∀ t : Nat, t < 4*v*v+18*v+22 →
        ∀ d : Config, run target429 t c0 = some d →
          d.head < cC.head := by
    intro t ht d hd
    have hb := hprev t ht d hd
    rw [hheadC]
    omega
  exact ⟨cC,by simpa [c0,tape] using htotal',hheadC,hstate,hcur,hright,hrecord⟩

#print axioms lowOdd_first_C0_frontier

end BB429LowOddPhysical
