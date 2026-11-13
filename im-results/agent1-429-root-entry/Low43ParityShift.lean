import Low43Physical
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429ParityShiftedEntry

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429PhysicalBridge
open BB429JPhysical BB429Low43Physical BB429OddExcursion BB429SourceE1Return

/-- The parity-shifted C/0 zipper observed at the end of the 31,154-step
    original-table entry from J(93,0,173). -/
def shiftedC0 : Zipper :=
  z 2 (true::false::(ones 353 ++ pairs01 4 ++ [false] ++ ones 6)) false []

private theorem rawStep_agrees_above (m : Machine) (L : Int)
    (c₁ c₂ d₁ d₂ : Config)
    (hstate : c₁.state=c₂.state)
    (hhead : c₁.head=c₂.head)
    (htape : ∀ x : Int, L≤x → c₁.tape x=c₂.tape x)
    (hfloor : L≤c₁.head)
    (hstep₁ : rawStep m c₁=some d₁)
    (hstep₂ : rawStep m c₂=some d₂) :
    d₁.state=d₂.state ∧ d₁.head=d₂.head ∧
      (∀ x : Int, L≤x → d₁.tape x=d₂.tape x) := by
  have hslot : readSlot c₁=readSlot c₂ := by
    unfold readSlot
    apply Prod.ext
    · exact hstate
    · calc
        c₁.tape c₁.head = c₂.tape c₁.head := htape c₁.head hfloor
        _ = c₂.tape c₂.head := by rw [hhead]
  unfold rawStep at hstep₁ hstep₂
  rw [← hslot] at hstep₂
  cases hm : m (readSlot c₁) with
  | none =>
      simp [hm] at hstep₁
  | some mv =>
      have h₁ : some (applyMove c₁ mv)=some d₁ := by
        simpa [hm] using hstep₁
      have h₂ : some (applyMove c₂ mv)=some d₂ := by
        simpa [hm] using hstep₂
      have heq₁ : d₁=applyMove c₁ mv := (Option.some.inj h₁).symm
      have heq₂ : d₂=applyMove c₂ mv := (Option.some.inj h₂).symm
      subst d₁
      subst d₂
      refine ⟨rfl, ?_, ?_⟩
      · simp [applyMove,hhead]
      · intro x hx
        by_cases hxc : x=c₁.head
        · subst x
          simp [applyMove,hhead]
        · have hxc₂ : x≠c₂.head := by
            rw [hhead]
            exact hxc
          simp [applyMove,hxc,hxc₂,htape x hx]

private theorem rawStep_preserves_below (m : Machine) (L : Int)
    (c d : Config)
    (hstep : rawStep m c=some d)
    (hfloor : L≤c.head) :
    ∀ x : Int, x<L → d.tape x=c.tape x := by
  unfold rawStep at hstep
  cases hm : m (readSlot c) with
  | none =>
      simp [hm] at hstep
  | some mv =>
      have h' : some (applyMove c mv)=some d := by
        simpa [hm] using hstep
      have heq : d=applyMove c mv := (Option.some.inj h').symm
      subst d
      intro x hx
      have hneq : x≠c.head := by omega
      simp [applyMove,hneq]

/-- If the reference run never visits a cell below L, then changing the
    initial tape strictly below L leaves every endpoint state, head, and
    tape cell at or above L unchanged.  The altered run also leaves its
    entire initial left tail untouched. -/
theorem run_agrees_above_of_head_floor (m : Machine) (L : Int) (n : Nat)
    (c₁ c₂ d₁ : Config)
    (hstate : c₁.state=c₂.state)
    (hhead : c₁.head=c₂.head)
    (htape : ∀ x : Int, L≤x → c₁.tape x=c₂.tape x)
    (hbound : ∀ t : Nat, t≤n → ∀ d : Config,
      run m t c₁=some d → L≤d.head)
    (hrun : run m n c₁=some d₁) :
    ∃ d₂ : Config,
      run m n c₂=some d₂ ∧
      d₁.state=d₂.state ∧ d₁.head=d₂.head ∧
      (∀ x : Int, L≤x → d₁.tape x=d₂.tape x) ∧
      (∀ x : Int, x<L → d₂.tape x=c₂.tape x) := by
  induction n generalizing c₁ c₂ d₁ with
  | zero =>
      have h' : some c₁=some d₁ := by
        simpa [BB6Coverage.run] using hrun
      have heq : d₁=c₁ := (Option.some.inj h').symm
      subst d₁
      refine ⟨c₂, ?_, hstate,hhead,htape,?_⟩
      · simp [BB6Coverage.run]
      · intro x hx
        rfl
  | succ n ih =>
      have hrun' := hrun
      simp only [BB6Coverage.run] at hrun'
      cases hmid₁ : run m n c₁ with
      | none =>
          simp [hmid₁] at hrun'
      | some mid₁ =>
          have hstep₁ : rawStep m mid₁=some d₁ := by
            simpa [hmid₁] using hrun'
          have hprefix : ∀ t : Nat, t≤n → ∀ d : Config,
              run m t c₁=some d → L≤d.head := by
            intro t ht d hd
            exact hbound t (by omega) d hd
          obtain ⟨mid₂,hmid₂,hstateMid,hheadMid,haboveMid,hbelowMid⟩ :=
            ih c₁ c₂ mid₁ hstate hhead htape hprefix hmid₁
          have hmidFloor : L≤mid₁.head :=
            hbound n (by omega) mid₁ hmid₁
          have hmidFloor₂ : L≤mid₂.head := by
            rw [hheadMid]
            exact hmidFloor
          have hstep₂_exists : ∃ d₂ : Config, rawStep m mid₂=some d₂ := by
            have hslot : readSlot mid₁=readSlot mid₂ := by
              unfold readSlot
              apply Prod.ext
              · exact hstateMid
              · calc
                  mid₁.tape mid₁.head = mid₂.tape mid₁.head :=
                    haboveMid mid₁.head hmidFloor
                  _ = mid₂.tape mid₂.head := by rw [hheadMid]
            unfold rawStep at hstep₁ ⊢
            rw [← hslot]
            cases hm : m (readSlot mid₁) with
            | none =>
                simp [hm] at hstep₁
            | some mv =>
                exact ⟨applyMove mid₂ mv, by simp [hm]⟩
          obtain ⟨d₂,hstep₂⟩ := hstep₂_exists
          obtain ⟨hstateFinal,hheadFinal,haboveFinal⟩ :=
            rawStep_agrees_above m L mid₁ mid₂ d₁ d₂
              hstateMid hheadMid haboveMid hmidFloor hstep₁ hstep₂
          have hbelowFinal : ∀ x : Int, x<L → d₂.tape x=c₂.tape x := by
            intro x hx
            have hpres := rawStep_preserves_below m L mid₂ d₂
              hstep₂ hmidFloor₂ x hx
            exact hpres.trans (hbelowMid x hx)
          refine ⟨d₂, ?_, hstateFinal,hheadFinal,haboveFinal,hbelowFinal⟩
          simpa [BB6Coverage.run,hmid₂] using hstep₂

private theorem getD_append {α : Type} (xs ys : List α) (j : Nat) (d : α) :
    (xs ++ ys).getD j d =
      if j < xs.length then xs.getD j d else ys.getD (j-xs.length) d := by
  induction xs generalizing j with
  | nil => simp
  | cons a xs ih =>
      cases j with
      | zero => simp
      | succ j => simpa using ih j

private theorem getD_take_of_lt {α : Type} (xs : List α) (n j : Nat) (d : α)
    (hj : j<n) :
    (xs.take n).getD j d = xs.getD j d := by
  induction xs generalizing n j with
  | nil => simp
  | cons a xs ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases j with
          | zero => rfl
          | succ j =>
              simpa only [List.take,List.getD_cons_succ] using
                ih n j (by omega)

private theorem ones_getD (n j : Nat) :
    (ones n).getD j false = decide (j<n) := by
  induction n generalizing j with
  | zero => simp [ones]
  | succ n ih =>
      cases j with
      | zero => simp [ones]
      | succ j => simpa [ones,List.replicate_succ] using ih j

private theorem pairs01_getD (n j : Nat) :
    (pairs01 n).getD j false = decide (j<2*n ∧ j%2=1) := by
  induction n generalizing j with
  | zero => simp [pairs01]
  | succ n ih =>
      cases j with
      | zero => simp [pairs01]
      | succ j =>
          cases j with
          | zero => simp [pairs01]; omega
          | succ j =>
              change (pairs01 n).getD j false =
                decide (j+2<2*(n+1) ∧ (j+2)%2=1)
              rw [ih]
              have hp : (j<2*n ∧ j%2=1) ↔
                  (j+2<2*(n+1) ∧ (j+2)%2=1) := by omega
              simp only [hp]

private theorem low43_shifted_left_take :
    (low43_C0_zipper 86 3).left.take 354 =
      shiftedC0.left.take 354 := by
  decide

private theorem low43_shifted_left_prefix (j : Nat) (hj : j<354) :
    (low43_C0_zipper 86 3).left.getD j false =
      shiftedC0.left.getD j false := by
  have h₁ := getD_take_of_lt (low43_C0_zipper 86 3).left 354 j false hj
  have h₂ := getD_take_of_lt shiftedC0.left 354 j false hj
  rw [← h₁,← h₂,low43_shifted_left_take]

private theorem shifted_left_getD_tail (j : Nat) (hj : 354≤j) :
    shiftedC0.left.getD j false =
      decide (j=354 ∨ (355≤j ∧ j≤362 ∧ j%2=0) ∨
        (364≤j ∧ j≤369)) := by
  change ([true,false] ++ (ones 353 ++ pairs01 4 ++ [false] ++ ones 6)).getD
    j false = _
  rw [getD_append]
  have hprefixLen : ([true,false] : List Bool).length=2 := rfl
  rw [hprefixLen]
  have hj₂ : ¬ j<2 := by omega
  rw [if_neg hj₂]
  rw [getD_append]
  have honesLen : (ones 353).length=353 := by simp [ones]
  rw [honesLen]
  by_cases hones : j-2<353
  · rw [if_pos hones,ones_getD]
    have hjEq : j=354 := by omega
    subst j
    simp
  · rw [if_neg hones]
    rw [getD_append]
    have hpairsLen : (pairs01 4).length=8 := by simp [pairs01]
    rw [hpairsLen]
    by_cases hp : j-355<8
    · rw [if_pos hp,pairs01_getD]
      have hprop : (j-355<8 ∧ (j-355)%2=1) ↔
          (355≤j ∧ j≤362 ∧ j%2=0) := by omega
      exact decide_eq_decide.mpr hprop
    · rw [if_neg hp]
      have hidx₀ : j-355-8=j-363 := by omega
      rw [hidx₀,getD_append]
      have hfalseLen : ([false] : List Bool).length=1 := rfl
      rw [hfalseLen]
      by_cases hz : j-363<1
      · rw [if_pos hz]
        have hjEq : j=363 := by omega
        subst j
        simp
      · rw [if_neg hz]
        have hidx₁ : j-363-1=j-364 := by omega
        rw [hidx₁,ones_getD]
        have hprop : (j-364<6) ↔ (364≤j ∧ j≤369) := by omega
        exact decide_eq_decide.mpr hprop

private theorem jTape93_left_formula (k : Nat) :
    jTape 93 173 (-((k:Int)+1)) =
      decide (k<192 ∧ (186≤k ∨ k%2=0)) := by
  have hmark : jMark 93 173 (-((k:Int)+1)) ↔
      k<192 ∧ (186≤k ∨ k%2=0) := by
    unfold jMark jHole
    omega
  simp [jTape,hmark]

private theorem shifted_left_tail_initial (j : Nat) (hj : 354≤j) :
    jTape 93 173 (177-(j:Int)) = shiftedC0.left.getD j false := by
  let k : Nat := j-178
  have hx : 177-(j:Int) = -((k:Int)+1) := by
    dsimp [k]
    omega
  rw [hx,jTape93_left_formula,shifted_left_getD_tail j hj]
  apply decide_eq_decide.mpr
  dsimp [k]
  omega

/-- The exact 31,154-step original-table entry from J(93,0,173) reaches
    the parity-shifted C/0 zipper.  The proof transfers the already-proved
    J(94,0,173) low43 record across the three-cell far-left tape edit:
    both initial tapes agree above -176, every reference prefix stays
    above -176, and the edited run never touches its distinct left tail. -/
theorem junc93_173_to_shiftedC0 :
    ∃ c : Config,
      run target429 31154
        {state:=A,head:=0,tape:=jTape 93 173}=some c ∧
      c.head=178 ∧ Represents shiftedC0 c := by
  let cStd₀ : Config := {state:=A,head:=0,tape:=jTape 94 173}
  let cShift₀ : Config := {state:=A,head:=0,tape:=jTape 93 173}
  obtain ⟨cStd,hstd,hStdHead,hrepStd,hstateStd,hcurStd,hRightStd,hrecordStd⟩ :=
    low43_C0_record 86 3
  have htime : 4*86*86+18*86+22=31154 := by norm_num
  have hstd' : run target429 31154 cStd₀=some cStd := by
    rw [← htime]
    simpa [cStd₀] using hstd
  have hStdHead' : cStd.head=178 := by simpa using hStdHead
  have hinit : ∀ x : Int, (-176:Int)≤x →
      cStd₀.tape x=cShift₀.tape x := by
    intro x hx
    change jTape 94 173 x = jTape 93 173 x
    have hmark : jMark 94 173 x ↔ jMark 93 173 x := by
      unfold jMark jHole
      omega
    simp [jTape,hmark]
  have hbound : ∀ t : Nat, t≤31154 → ∀ d : Config,
      run target429 t cStd₀=some d → (-176:Int)≤d.head := by
    intro t ht d hd
    have ht' : t≤4*86*86+18*86+22 := by omega
    have h := low43_C0_record_head_floor 86 3 t ht' d
      (by simpa [cStd₀] using hd)
    have h' : (-176:Int)≤d.head := by
      have h₀ : -2*(86:Int)-4≤d.head := h
      norm_num at h₀
      exact h₀
    exact h'
  obtain ⟨cShift,hshift,hstateEnd,hheadEnd,habove,hbelow⟩ :=
    run_agrees_above_of_head_floor target429 (-176) 31154
      cStd₀ cShift₀ cStd (by rfl) (by rfl) hinit hbound hstd'
  have hheadShift : cShift.head=178 := by
    calc
      cShift.head = cStd.head := hheadEnd.symm
      _ = 178 := hStdHead'
  have hstateShift : cShift.state.val=shiftedC0.state := by
    calc
      cShift.state.val = cStd.state.val := congrArg Fin.val hstateEnd.symm
      _ = (low43_C0_zipper 86 3).state := hrepStd.1
      _ = shiftedC0.state := by simp [low43_C0_zipper,shiftedC0,z]
  have hcurStd : cStd.tape cStd.head=false := by
    simpa [low43_C0_zipper,z] using hrepStd.2.1
  have hcurAgree := habove cStd.head (by rw [hStdHead']; norm_num)
  have hcurShift : cShift.tape cShift.head=false := by
    calc
      cShift.tape cShift.head = cShift.tape cStd.head := by rw [hheadEnd.symm]
      _ = cStd.tape cStd.head := hcurAgree.symm
      _ = false := hcurStd
  have hleft : ∀ j : Nat,
      cShift.tape (cShift.head-((j:Int)+1)) =
        shiftedC0.left.getD j false := by
    intro j
    have hcoord : cShift.head-((j:Int)+1)=177-(j:Int) := by
      rw [hheadShift]
      omega
    rw [hcoord]
    by_cases hj : j<354
    · have hfloor : (-176:Int)≤177-(j:Int) := by omega
      have hAgree := habove (177-(j:Int)) hfloor
      have hcoordStd : cStd.head-((j:Int)+1)=177-(j:Int) := by
        rw [hStdHead']
        omega
      have hStdLeft : cStd.tape (177-(j:Int)) =
          (low43_C0_zipper 86 3).left.getD j false := by
        have hh := hrepStd.2.2.1 j
        change cStd.tape (cStd.head-((j:Int)+1)) =
          (low43_C0_zipper 86 3).left.getD j false at hh
        rw [hcoordStd] at hh
        exact hh
      calc
        cShift.tape (177-(j:Int)) = cStd.tape (177-(j:Int)) := hAgree.symm
        _ = (low43_C0_zipper 86 3).left.getD j false := hStdLeft
        _ = shiftedC0.left.getD j false := low43_shifted_left_prefix j hj
    · have hj' : 354≤j := by omega
      have htail := hbelow (177-(j:Int)) (by omega)
      calc
        cShift.tape (177-(j:Int)) = cShift₀.tape (177-(j:Int)) := htail
        _ = jTape 93 173 (177-(j:Int)) := rfl
        _ = shiftedC0.left.getD j false := shifted_left_tail_initial j hj'
  have hright : ∀ j : Nat,
      cShift.tape (cShift.head+((j:Int)+1)) =
        shiftedC0.right.getD j false := by
    intro j
    have hcoord : cShift.head+((j:Int)+1)=178+((j:Int)+1) := by
      rw [hheadShift]
    rw [hcoord]
    have hfloor : (-176:Int)≤178+((j:Int)+1) := by omega
    have hAgree := habove (178+((j:Int)+1)) hfloor
    have hcoordStd : cStd.head+((j:Int)+1)=178+((j:Int)+1) := by
      rw [hStdHead']
    have hStdRight : cStd.tape (178+((j:Int)+1)) =
        (low43_C0_zipper 86 3).right.getD j false := by
      have hh := hrepStd.2.2.2 j
      change cStd.tape (cStd.head+((j:Int)+1)) =
        (low43_C0_zipper 86 3).right.getD j false at hh
      rw [hcoordStd] at hh
      exact hh
    calc
      cShift.tape (178+((j:Int)+1)) =
          cStd.tape (178+((j:Int)+1)) := hAgree.symm
      _ = (low43_C0_zipper 86 3).right.getD j false := hStdRight
      _ = shiftedC0.right.getD j false := by
          simp [low43_C0_zipper,shiftedC0,z]
  have hrepShift : Represents shiftedC0 cShift := by
    change cShift.state.val=shiftedC0.state ∧
      cShift.tape cShift.head=shiftedC0.current ∧
      (∀ j : Nat, cShift.tape (cShift.head-((j:Int)+1)) =
        shiftedC0.left.getD j false) ∧
      (∀ j : Nat, cShift.tape (cShift.head+((j:Int)+1)) =
        shiftedC0.right.getD j false)
    exact ⟨hstateShift,hcurShift,hleft,hright⟩
  exact ⟨cShift,by simpa [cShift₀] using hshift,hheadShift,hrepShift⟩

#print axioms run_agrees_above_of_head_floor
#print axioms junc93_173_to_shiftedC0

end BB429ParityShiftedEntry
