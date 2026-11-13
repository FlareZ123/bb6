import Low43Delta
import HeadDisplacement
import BubblePrefixHeadBound
import JPhysicalPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low43Physical

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429PhysicalBridge BB429DeltaPhysicalBridge BB429HeadDisplacement BB429Low43Delta BB429Low3Delta

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

/-- The physical tape after repairing the nearest v+1 negative-even holes. -/
def stage43Tape (v k : Nat) : Int → Bool :=
  fun x => negFill (jTape (v+2*k+2) (2*v+1)) (v+1) x

private theorem stage43_left_char (v k j : Nat) :
    (stage43 v k).left.getD j false =
      decide (j < 4*v+4*k+12 ∧
        ¬(4*v+4 ≤ j ∧ j<4*v+4*k+6 ∧ j%2=1)) := by
  change (ones (4*v+4) ++ (tens (2*k+1) ++ ones 6)).getD j false = _
  rw [getD_append]
  have hlen : (ones (4*v+4)).length = 4*v+4 := by simp [ones]
  rw [hlen]
  by_cases hj : j<4*v+4
  · rw [if_pos hj,ones_getD]
    have hp : j < 4*v+4*k+12 ∧
        ¬(4*v+4 ≤ j ∧ j<4*v+4*k+6 ∧ j%2=1) := by omega
    simp [hj,hp]
  · rw [if_neg hj,getD_append]
    have hlen2 : (tens (2*k+1)).length=4*k+2 := by
      rw [tens_length]
      omega
    rw [hlen2]
    by_cases ht : j-(4*v+4)<4*k+2
    · rw [if_pos ht,tens_getD]
      have hp :
          (j-(4*v+4)<2*(2*k+1) ∧ (j-(4*v+4))%2=0) ↔
            (j < 4*v+4*k+12 ∧
              ¬(4*v+4 ≤ j ∧ j<4*v+4*k+6 ∧ j%2=1)) := by omega
      simp [hp]
    · rw [if_neg ht,ones_getD]
      have hp : j-(4*v+4)-(4*k+2)<6 ↔
          (j < 4*v+4*k+12 ∧
            ¬(4*v+4 ≤ j ∧ j<4*v+4*k+6 ∧ j%2=1)) := by omega
      simp [hp]

/-- Full two-sided tape characterization, including all cells outside the
    finite zipper words. -/
private theorem stage43_tape_character (v k : Nat) (x : Int) :
    stage43Tape v k x =
      decide (((-2*(v:Int)-4*(k:Int)-10 ≤ x ∧
          x ≤ 2*(v:Int)+2 ∧
          ¬(-2*(v:Int)-4*(k:Int)-4 ≤ x ∧
            x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
        x=2*(v:Int)+4)) := by
  have hp :
      (negFillTest (v+1) x ∨ jMark (v+2*k+2) (2*v+1) x) ↔
        (((-2*(v:Int)-4*(k:Int)-10 ≤ x ∧
            x ≤ 2*(v:Int)+2 ∧
            ¬(-2*(v:Int)-4*(k:Int)-4 ≤ x ∧
              x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
          x=2*(v:Int)+4)) := by
    unfold negFillTest jMark jHole
    omega
  unfold stage43Tape negFill jTape
  by_cases hfill : negFillTest (v+1) x
  · simp only [if_pos hfill]
    exact (decide_eq_true (hp.mp (Or.inl hfill))).symm
  · by_cases hj : jMark (v+2*k+2) (2*v+1) x
    · simp only [if_neg hfill,if_pos hj]
      exact (decide_eq_true (hp.mp (Or.inr hj))).symm
    · have hn :
        ¬(((-2*(v:Int)-4*(k:Int)-10 ≤ x ∧
              x ≤ 2*(v:Int)+2 ∧
              ¬(-2*(v:Int)-4*(k:Int)-4 ≤ x ∧
                x ≤ -2*(v:Int)-4 ∧ x%2=0)) ∨
            x=2*(v:Int)+4)) := by
        intro hh
        rcases hp.mpr hh with hz | hj'
        · exact hfill hz
        · exact hj hj'
      simp only [if_neg hfill,if_neg hj]
      exact (decide_eq_false hn).symm

private theorem stage43_rep_left (v k j : Nat) :
    stage43Tape v k ((2*(v:Int)+2)-((j:Int)+1)) =
      (stage43 v k).left.getD j false := by
  rw [stage43_tape_character,stage43_left_char]
  apply decide_eq_decide.mpr
  omega

private theorem stage43_rep_right (v k j : Nat) :
    stage43Tape v k ((2*(v:Int)+2)+((j:Int)+1)) =
      (stage43 v k).right.getD j false := by
  rw [stage43_tape_character]
  have hr : ([false,true] : List Bool).getD j false = decide (j=1) := by
    cases j with
    | zero => rfl
    | succ j => cases j <;> rfl
  change _ = ([false,true] : List Bool).getD j false
  rw [hr]
  apply decide_eq_decide.mpr
  omega

private theorem stage43_rep_center (v k : Nat) :
    stage43Tape v k (2*(v:Int)+2) = true := by
  rw [stage43_tape_character]
  have hp :
      -2*(v:Int)-4*(k:Int)-10 ≤ 2*(v:Int)+2 ∧
      2*(v:Int)+2 ≤ 2*(v:Int)+2 ∧
      ¬(-2*(v:Int)-4*(k:Int)-4 ≤ 2*(v:Int)+2 ∧
        2*(v:Int)+2 ≤ -2*(v:Int)-4 ∧
        (2*(v:Int)+2)%2=0) := by omega
  exact decide_eq_true (Or.inl hp)

/-- Exact zipper representation of the prepared odd-deficit-3 stage. -/
theorem stage43_represented (v k : Nat) :
    Represents (stage43 v k)
      {state:=A,head:=2*(v:Int)+2,tape:=stage43Tape v k} := by
  exact ⟨rfl,stage43_rep_center v k,stage43_rep_left v k,
    stage43_rep_right v k⟩

private theorem low43_holes (v k i : Nat) (hi : i < v+1) :
    jTape (v+2*k+2) (2*v+1) (-2*((i+1:Nat):Int)) = false := by
  have hj : ¬jMark (v+2*k+2) (2*v+1)
      (-2*((i+1:Nat):Int)) := by
    unfold jMark jHole
    omega
  change (if jMark (v+2*k+2) (2*v+1)
      (-2*((i+1:Nat):Int)) then true else false) = false
  exact if_neg hj

private theorem low43_odds (v k : Nat) (x : Int)
    (hlo : -2*((v+1:Nat):Int)<x) (hhi : x<0) (hodd : x%2≠0) :
    jTape (v+2*k+2) (2*v+1) x = true := by
  have hj : jMark (v+2*k+2) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem low43_right (v k : Nat) (x : Int)
    (hlo : 0≤x) (hhi : x≤2*((v+1:Nat):Int)) :
    jTape (v+2*k+2) (2*v+1) x = true := by
  have hj : jMark (v+2*k+2) (2*v+1) x := by
    unfold jMark jHole
    left
    omega
  simp [jTape,hj]

private theorem physical_compose (m n : Nat) (a b c : Config)
    (h1 : run target429 m a = some b)
    (h2 : run target429 n b = some c) :
    run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add',h1]
  exact h2

private theorem compose_delta (m n : Nat) (a b c : Zipper) (d e : Int)
    (h1 : runWithDelta m a = some (b,d))
    (h2 : runWithDelta n b = some (c,e)) :
    runWithDelta (m+n) a = some (c,d+e) := by
  rw [runWithDelta_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl

private theorem af_tail_delta_local (l r : List Bool) :
    runWithDelta 2 (z 0 (true::false::l) true r) =
      some (z 0 l false (true::false::r), -2) := by
  rfl

private theorem low3_tail_delta_local (l : List Bool) :
    runWithDelta 4 (z 0 l false [false,true]) =
      some (z 2 (true::false::true::true::l) false [], 4) := by
  rfl

def stage43Config (v k : Nat) : Config :=
  {state:=A,head:=2*(v:Int)+2,tape:=stage43Tape v k}

def low43_C0_zipper (v k : Nat) : Zipper :=
  z 2 (true::false::true::true::
    (ones (4*v+6) ++ tens (2*k) ++ ones 6)) false []

private theorem stage43_decomposition (v k : Nat) :
    ∃ c1 c2 c3 : Config,
      run target429 (4*v+6) (stage43Config v k) = some c1 ∧
      run target429 (4*v+6) c1 = some c2 ∧
      run target429 4 c2 = some c3 ∧
      c1.head = (stage43Config v k).head - (4*v+6) ∧
      c2.head = (stage43Config v k).head ∧
      c3.head = (stage43Config v k).head + 4 ∧
      Represents (low43_C0_zipper v k) c3 ∧
      c3.state.val = 2 ∧
      c3.tape c3.head = false ∧
      c3.tape (c3.head+1) = false := by
  let zFirst : Zipper :=
    z 0 (tens (2*k+1) ++ ones 6) true (tens (2*v+2) ++ [false,true])
  let zMid : Zipper :=
    z 0 (tens (2*k) ++ ones 6) false (tens (2*v+3) ++ [false,true])
  let zAR : Zipper :=
    z 0 (ones (4*v+6) ++ (tens (2*k) ++ ones 6)) false [false,true]
  let zC0 : Zipper := low43_C0_zipper v k
  have hAF : runWithDelta (4*v+4) (stage43 v k) =
      some (zFirst, -((4*v+4:Nat):Int)) := by
    simpa [stage43,zFirst,show 2*(2*v+2)=4*v+4 by omega,
      List.append_assoc] using
      (BB429Low3Delta.af_pairs_delta (2*v+2)
        (tens (2*k+1) ++ ones 6) [false,true])
  have h2 : runWithDelta 2 zFirst = some (zMid, -2) := by
    dsimp [zFirst]
    rw [show tens (2*k+1) = true::false::tens (2*k) by rfl]
    change runWithDelta 2
      (z 0 (true::false::(tens (2*k) ++ ones 6)) true
        (tens (2*v+2) ++ [false,true])) =
      some (z 0 (tens (2*k) ++ ones 6) false
        (true::false::(tens (2*v+2) ++ [false,true])),-2)
    simpa [zMid,show tens (2*v+3)=true::false::tens (2*v+2) by rfl] using
      (af_tail_delta_local _ _)
  have hleft0 := compose_delta (4*v+4) 2
    (stage43 v k) zFirst zMid
    (-((4*v+4:Nat):Int)) (-2) hAF h2
  have hleft : runWithDelta (4*v+6) (stage43 v k) =
      some (zMid, -((4*v+6:Nat):Int)) := by
    have htime : (4*v+4)+2=4*v+6 := by omega
    have hdelta : -((4*v+4:Nat):Int)+(-2) =
        -((4*v+6:Nat):Int) := by omega
    rw [← htime, ← hdelta]
    exact hleft0
  have hAR : runWithDelta (4*v+6) zMid =
      some (zAR, ((4*v+6:Nat):Int)) := by
    simpa [zMid,zAR,show 2*(2*v+3)=4*v+6 by omega,
      List.append_assoc] using
      (BB429Low3Delta.ar_pairs_delta (2*v+3)
        (tens (2*k) ++ ones 6) [false,true])
  have h4 : runWithDelta 4 zAR = some (zC0, (4:Int)) := by
    simpa [zAR,zC0,low43_C0_zipper,List.append_assoc] using
      (low3_tail_delta_local (ones (4*v+6) ++ (tens (2*k) ++ ones 6)))
  have hrepStage : Represents (stage43 v k) (stage43Config v k) := by
    simpa [stage43Config] using stage43_represented v k
  obtain ⟨c1,hleftP,hrep1,hhead1⟩ :=
    source_runWithDelta_rep (4*v+6) (stage43 v k) (stage43Config v k)
      hrepStage zMid (-((4*v+6:Nat):Int)) hleft
  obtain ⟨c2,hARP,hrep2,hhead2⟩ :=
    source_runWithDelta_rep (4*v+6) zMid c1 hrep1 zAR (4*v+6) hAR
  obtain ⟨c3,h4P,hrep3,hhead3⟩ :=
    source_runWithDelta_rep 4 zAR c2 hrep2 zC0 4 h4
  rcases hrep3 with ⟨hstate,hcur,hleftRep,hrightRep⟩
  have hrep3' : Represents (low43_C0_zipper v k) c3 := by
    simpa [zC0,low43_C0_zipper] using (show Represents zC0 c3 from ⟨hstate,hcur,hleftRep,hrightRep⟩)
  have hstate' : c3.state.val=2 := by simpa [zC0] using hstate
  have hcur' : c3.tape c3.head=false := by simpa [zC0] using hcur
  have hright' : c3.tape (c3.head+1)=false := by
    have h := hrightRep 0
    change c3.tape (c3.head+1)=false at h
    exact h
  have hhead1' : c1.head=(stage43Config v k).head-(4*v+6) := by
    simpa using hhead1
  have hhead2' : c2.head=(stage43Config v k).head := by
    rw [hhead2,hhead1']
    omega
  have hhead3' : c3.head=(stage43Config v k).head+4 := by
    rw [hhead3,hhead2']
  exact ⟨c1,c2,c3,hleftP,hARP,h4P,hhead1',hhead2',hhead3',
    hrep3',hstate',hcur',hright'⟩

/-- Every primitive prefix of the 8v+16-step prepared stage stays at most
    three cells to the right of its entry head. -/
private theorem stage43_prefix_head_bound (v k s : Nat)
    (hs : s ≤ 8*v+15) :
    ∃ d : Config,
      run target429 s (stage43Config v k) = some d ∧
      d.head ≤ (stage43Config v k).head + 3 := by
  obtain ⟨c1,c2,c3,hleft,hAR,h4,hhead1,hhead2,hhead3,
      hstate,hcur,hright⟩ := stage43_decomposition v k
  let cStage : Config := stage43Config v k
  let L : Nat := 4*v+6
  have hhead1L : c1.head = cStage.head-(L:Int) := by
    simpa [cStage,L] using hhead1
  have hdisp1 : c1.head-cStage.head=-(L:Int) := by
    rw [hhead1L]
    omega
  have hdisp2 : c2.head-c1.head=(L:Int) := by
    rw [hhead2,hhead1L]
    omega
  have hdisp3 : c3.head-c2.head=4 := by
    rw [hhead3,hhead2]
    omega
  by_cases hs1 : s≤L
  · obtain ⟨d,hpre⟩ :=
      run_prefix_exists target429 L s cStage c1 hleft hs1
    have hleftExact :=
      run_prefix_left_extremal target429 L s cStage d c1
        hleft hpre hs1 hdisp1
    have hC : cStage.head = (stage43Config v k).head := rfl
      exact ⟨d,hpre,by omega⟩
  · by_cases hs2 : s≤2*L
    · let r : Nat := s-L
      have hr : r≤L := by dsimp [r]; omega
      obtain ⟨d,hpre2⟩ :=
        run_prefix_exists target429 L r c1 c2 hAR hr
      have hrightExact :=
        run_prefix_right_extremal target429 L r c1 d c2
          hAR hpre2 hr hdisp2
      have htime : s=L+r := by dsimp [r]; omega
      have hpre : run target429 s cStage=some d := by
        rw [htime,run_add',hleft]
        simpa using hpre2
      have hC : cStage.head = (stage43Config v k).head := rfl
      have h := hrightExact
      rw [hhead1L] at h
      exact ⟨d,hpre,by omega⟩
    · let r : Nat := s-2*L
      have hL : 8*v+15=2*L+3 := by dsimp [L]; omega
      have hr : r≤3 := by dsimp [r]; omega
      obtain ⟨d,hpre3⟩ :=
        run_prefix_exists target429 4 r c2 c3 h4 (by omega)
      have hrightExact :=
        run_prefix_right_extremal target429 4 r c2 d c3
          h4 hpre3 (by omega) hdisp3
      have hleftAR : run target429 (L+L) cStage=some c2 := by
        rw [run_add',hleft]
        exact hAR
      have htime : s=(L+L)+r := by dsimp [r]; omega
      have hpre : run target429 s cStage=some d := by
        rw [htime,run_add',hleftAR]
        simpa using hpre3
      have hC : cStage.head = (stage43Config v k).head := rfl
      have h := hrightExact
      rw [hhead2] at h
      exact ⟨d,hpre,by omega⟩

/-- On every odd-deficit-4k+3 input, the first certified C/0 checkpoint is
    a strict physical right-head record. Its right neighbour is blank, and
    every earlier primitive prefix lies at least one cell to its left. -/
theorem low43_C0_record (v k : Nat) :
    ∃ cC : Config,
      run target429 (4*v*v+18*v+22)
        {state:=A,head:=0,tape:=jTape (v+2*k+2) (2*v+1)} = some cC ∧
      cC.head=2*(v:Int)+6 ∧
      Represents (low43_C0_zipper v k) cC ∧
      cC.state.val=2 ∧
      cC.tape cC.head=false ∧
      cC.tape (cC.head+1)=false ∧
      (∀ t : Nat, t<4*v*v+18*v+22 →
        ∀ d : Config,
          run target429 t
            {state:=A,head:=0,tape:=jTape (v+2*k+2) (2*v+1)}=some d →
          d.head<cC.head) := by
  let tape : Int → Bool := jTape (v+2*k+2) (2*v+1)
  let c0 : Config := {state:=A,head:=0,tape:=tape}
  let cStage : Config := stage43Config v k
  let B : Nat := 4*(v+1)*(v+1)+2*(v+1)
  have hfirst : run target429 B c0=some cStage := by
    simpa [c0,cStage,B,stage43Config,stage43Tape,tape,
      Nat.cast_mul,Nat.cast_add] using
      multi_bubble_prefix target429 (v+1) (v+1) tape (by omega)
        (by decide) (by decide) (by decide) (by decide)
        (low43_holes v k) (low43_odds v k) (low43_right v k)
  have hBubblePrefixBound :
      ∀ t : Nat, t≤B →
        ∃ d : Config, run target429 t c0=some d ∧
          d.head≤2*(v:Int)+2 := by
    intro t ht
    obtain ⟨d,hpre,hbound⟩ :=
      multi_bubble_prefix_head_bound target429 (v+1) (v+1) t tape
        (by omega) (by decide) (by decide) (by decide) (by decide)
        (low43_holes v k) (low43_odds v k) (low43_right v k)
        (by simpa [B] using ht)
    exact ⟨d,hpre,by omega⟩
  obtain ⟨c1,c2,cC,hleft,hAR,h4,hhead1,hhead2,hhead3,
      hrepC,hstate,hcur,hright⟩ := stage43_decomposition v k
  let L : Nat := 4*v+6
  have hleftAR : run target429 (L+L) cStage=some c2 := by
    rw [run_add',hleft]
    exact hAR
  have hstageFull : run target429 (L+L+4) cStage=some cC := by
    rw [run_add',hleftAR]
    exact h4
  have hS : 8*v+16=L+L+4 := by dsimp [L]; omega
  have hstage : run target429 (8*v+16) cStage=some cC := by
    rw [hS]
    exact hstageFull
  have htotal : run target429 (B+(8*v+16)) c0=some cC := by
    rw [run_add',hfirst]
    exact hstage
  have hsq : (v+1)*(v+1)=v*v+2*v+1 := by
    rw [Nat.mul_add,Nat.add_mul]
    simp
    omega
  have htime : B+(8*v+16)=4*v*v+18*v+22 := by
    dsimp [B]
    rw [Nat.mul_assoc,hsq]
    simp [Nat.mul_add,Nat.add_mul]
    omega
  have htotal' : run target429 (4*v*v+18*v+22) c0=some cC := by
    simpa [htime] using htotal
  have hheadC : cC.head=2*(v:Int)+6 := by
    rw [hhead3]
    simp [stage43Config]
    omega
  have hprev :
      ∀ t : Nat, t<4*v*v+18*v+22 →
        ∀ d : Config, run target429 t c0=some d →
          d.head≤2*(v:Int)+5 := by
    intro t ht d hd
    by_cases htb : t≤B
    · obtain ⟨d',hpre,hbound⟩ := hBubblePrefixBound t htb
      have heq : d=d' := Option.some.inj (hd.symm.trans hpre)
      subst d
      omega
    · let s : Nat := t-B
      have hs : s≤8*v+15 := by
        have hBS : B+8*v+16=4*v*v+18*v+22 := htime
        dsimp [s]
        omega
      obtain ⟨d',hseg,hbound⟩ := stage43_prefix_head_bound v k s hs
      have htime2 : t=B+s := by dsimp [s]; omega
      have hpre : run target429 t c0=some d' := by
        rw [htime2,run_add',hfirst]
        exact hseg
      have heq : d=d' := Option.some.inj (hd.symm.trans hpre)
      subst d
      omega
  have hrecord :
      ∀ t : Nat, t<4*v*v+18*v+22 →
        ∀ d : Config, run target429 t c0=some d →
          d.head<cC.head := by
    intro t ht d hd
    have hb := hprev t ht d hd
    rw [hheadC]
    omega
  exact ⟨cC,by simpa [c0,tape] using htotal',hheadC,hrepC,hstate,hcur,hright,hrecord⟩

#print axioms stage43_represented
#print axioms low43_C0_record

end BB429Low43Physical
