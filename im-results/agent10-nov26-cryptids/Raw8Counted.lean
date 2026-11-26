/- Source-connected exact cost lift for Raw8.
   Upstream pin d1d231afe3a5f6310ac9f956d5687b5a45d7a13d. Original local transition and carry proofs are imported unchanged.
   No expanded astronomical tape or primitive execution is computed. -/
module
import all BusyBeaver.BB6.Halt.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB
import BusyBeaver.Basic
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open Mathlib Relation Nat Turing BusyBeaver
namespace BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.Counted
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def HaltExact (c : Cfg (Fin 2) (Fin 6)) (t : Nat) : Prop :=
  ∃ cfg', (c [target_tm]⊢^{t} cfg') ∧ (step target_tm cfg').isNone

private theorem prependHalt {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {n t : Nat}
    (h : c₁ [target_tm]⊢^{n} c₂) (hh : HaltExact c₂ t) : HaltExact c₁ (n+t) := by
  rcases hh with ⟨cfg', hm, hnone⟩
  exact ⟨cfg', ms_trans h hm, hnone⟩

private def UnitExact (sL : ListBlank (Fin 2)) (t : Nat) : Prop :=
  ∀ sW : ListBlank (Fin 2), HaltExact (evalWin sL sW 1 false [0] []) t

private def CarryExact : Bool → Bool → ListBlank (Fin 2) → Nat → Prop
  | false, false, sL, t => UnitExact (sepBits .S7 +> sL) t
  | false, true, sL, t => UnitExact (sepBits .S2 +> sL) t
  | true, false, sL, t => HaltExact (evalWin (topBits false +> sL) default 1 true [] [0]) t
  | true, true, sL, t => HaltExact (evalWin (topBits true +> sL) default 1 true [] [0]) t

private theorem unitStep_m8_exact {t : Nat} {sX : ListBlank (Fin 2)}
    (hX : UnitExact sX t) (km1 : ℕ) :
    UnitExact ((u8 ^ (km1 + 1)) +> sX) (24*(km1+1)+t) := by
  intro sW
  have h1 := walkWordLeft 24 1 false [0] u8 [] w24 motifB0_body (km1 + 1) sX sW
  exact prependHalt h1 (hX ((w24 ^ (km1 + 1)) +> sW))

private theorem wrap_S7_exact {t : Nat} {sL : ListBlank (Fin 2)} (h1 : UnitExact sL t) :
    CarryExact false false sL (60+t) := by
  intro sW
  have ha : (evalWin (sepBits .S7 +> sL) sW 1 false [0] []) [target_tm]⊢^{60}
      (evalWin sL (w_s7 +> sW) 1 false [0] []) :=
    chkWin_eq false false 60 1 true (sepBits .S7) [0] 1 false [0] w_s7
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  exact prependHalt ha (h1 (w_s7 +> sW))

private theorem wrap_Top0_exact {t : Nat} {sL : ListBlank (Fin 2)} (h1 : UnitExact sL t) :
    CarryExact true false sL (33+t) := by
  have ha : (evalWin (topBits false +> sL) default 1 true [] [0]) [target_tm]⊢^{33}
      (evalWin sL (w_top0 +> default) 1 false [0] []) :=
    chkWin_eq false false 33 1 true (topBits false) [0] 1 false [0] w_top0
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  exact prependHalt ha (h1 (w_top0 +> default))

private theorem wrap_S2_exact1 {t : Nat} {sL : ListBlank (Fin 2)} (h1 : UnitExact sL t) :
    CarryExact false true sL (48+t) := by
  intro sW
  have ha : (evalWin (sepBits .S2 +> sL) sW 1 false [0] []) [target_tm]⊢^{48}
      (evalWin sL (w_s2 +> sW) 1 false [0] []) :=
    chkWin_eq false false 48 1 true (sepBits .S2) [0] 1 false [0] w_s2
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  exact prependHalt ha (h1 (w_s2 +> sW))

private theorem wrap_Top1_exact1 {t : Nat} {sL : ListBlank (Fin 2)} (h1 : UnitExact sL t) :
    CarryExact true true sL (21+t) := by
  have ha : (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{21}
      (evalWin sL (w_top1 +> default) 1 false [0] []) :=
    chkWin_eq false false 21 1 true (topBits true) [0] 1 false [0] w_top1
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  exact prependHalt ha (h1 (w_top1 +> default))

private theorem wrap_S2_exact2 {t : Nat} {c1 : ℕ} {sL sR1 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitExact (u8 +> sR1) t) :
    CarryExact false true sL (48+c1+29+t) := by
  intro sW
  have ha : (evalWin (sepBits .S2 +> sL) sW 1 false [0] []) [target_tm]⊢^{48}
      (evalWin sL (w_s2 +> sW) 1 false [0] []) :=
    chkWin_eq false false 48 1 true (sepBits .S2) [0] 1 false [0] w_s2
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_s2 +> sW)
  have hc : (evalWin (uBits [2] +> sR1) (w_s2 +> sW) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_s2_rem +> sW) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_s2 1 false (0 :: u8) w_s2_rem
      sR1 sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  exact prependHalt (ms_trans (ms_trans ha hb) hc) (h2 (w_s2_rem +> sW))

private theorem wrap_Top1_exact2 {t : Nat} {c1 : ℕ} {sL sR1 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitExact (u8 +> sR1) t) :
    CarryExact true true sL (21+c1+29+t) := by
  have ha : (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{21}
      (evalWin sL (w_top1 +> default) 1 false [0] []) :=
    chkWin_eq false false 21 1 true (topBits true) [0] 1 false [0] w_top1
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_top1 +> default)
  have hc : (evalWin (uBits [2] +> sR1) (w_top1 +> default) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_top1_rem +> default) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_top1 1 false (0 :: u8) w_top1_rem
      sR1 default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  exact prependHalt (ms_trans (ms_trans ha hb) hc) (h2 (w_top1_rem +> default))

private def terminalOverhead (isTop p : Bool) (k : Nat) (j : Sep) : Nat :=
  24*(k+1) + (if p then (if isTop then 21 else 48) else (if isTop then 33 else 60)) +
  (match p, j with
   | true, .S1 | true, .S4 => 56*k+63+29
   | _, _ => 0)

private theorem terminalLift (isTop p : Bool) (k : Nat) (j : Sep)
    {b : Bool} {s : ListBlank (Fin 2)} {t : Nat}
    (he : (step1Carry isTop p k j).2.2.1 = some b)
    (h : CarryExact false b s t) :
    CarryExact isTop p (layerBits k j s) (t + terminalOverhead isTop p k j) := by
  cases isTop <;> cases p <;> cases j <;> simp only [step1Carry] at he <;>
    try contradiction <;> try (injection he with hb; subst b)
  all_goals first
    | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (wrap_S7_exact (unitStep_m8_exact h k))
    | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (wrap_Top0_exact (unitStep_m8_exact h k))
    | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (wrap_S2_exact1 (unitStep_m8_exact h k))
    | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (wrap_Top1_exact1 (unitStep_m8_exact h k))
    | (have hu : UnitExact (u8 +> ((u8 ^ k) +> (sepBits .S2 +> s))) (24*(k+1)+t) := by
         rw [u8_cons_pow]
         exact unitStep_m8_exact h k
       first
       | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
           Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wrap_S2_exact2 (sub_S1 k s) hu
       | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
           Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wrap_Top1_exact2 (sub_S1 k s) hu)
    | (have hu : UnitExact (u8 +> ((u8 ^ k) +> (sepBits .S7 +> s))) (24*(k+1)+t) := by
         rw [u8_cons_pow]
         exact unitStep_m8_exact h k
       first
       | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
           Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wrap_S2_exact2 (sub_S4 k s) hu
       | simpa only [terminalOverhead, ↓reduceIte, Bool.false_eq_true, Nat.add_zero,
           Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using wrap_Top1_exact2 (sub_S4 k s) hu)

/-- The table maxR consumes exactly the requested number of residual child carries,
    and its next parent carry emits to the now-terminal child. -/
private theorem maxR_plan (isTop p : Bool) (j : Sep) (k r : Nat) (hr : r < 6) :
    ∃ k' j' cR, iterCarryAux isTop (maxR p j r) p (qPol j) k j = some (k', j', r, cR) ∧
    (step1Carry isTop (parityXor p (maxR p j r)) k' j').2.2.1 = some (parityXor (qPol j) r) := by
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 := by omega
  rcases h with h|h|h|h|h|h <;> subst r <;>
    cases isTop <;> cases p <;> cases j <;> exact ⟨_,_,_,rfl,rfl⟩

private def ExactTail (isTop p : Bool) (s : ListBlank (Fin 2)) (n t : Nat) : Prop :=
  ∃ s' c1 c2, CarryChain isTop n p c1 s s' ∧
    CarryExact isTop (parityXor p n) s' c2 ∧ t = c1+c2

private theorem exact_prepend {isTop p : Bool} {s s' : ListBlank (Fin 2)} {n c t : Nat}
    (hc : CarrySem isTop p c s s') (h : ExactTail isTop (!p) s' n t) :
    ExactTail isTop p s (n+1) (c+t) := by
  rcases h with ⟨s2,c1,c2,hs,hh,ht⟩
  refine ⟨s2,c+c1,c2,.succ hc hs,?_,by omega⟩
  rw [parityXor_succ]
  exact hh

private theorem exact_terminal {isTop p : Bool} {s : ListBlank (Fin 2)} {t : Nat}
    (h : CarryExact isTop p s t) : ExactTail isTop p s 0 t := by
  exact ⟨s,0,t,.zero p s,by simpa only [parityXor_zero] using h,by omega⟩

/-- Compact summary: number of parent carries, plus local overhead to termination.
    Six alternating child carries give sixteen parent carries; only a remainder
    of at most fifteen needs direct evaluation. -/
private def liftInfo (isTop p : Bool) (k : Nat) (j : Sep) (n : Nat) : Nat × Nat :=
  let Q := n/6
  let r := maxR p j (n%6)
  match iterCarryAux isTop r p (qPol j) (k+4*Q) j with
  | none => (0,0)
  | some (k',j',_,cR) =>
    (16*Q+r, qCyclesCost isTop p j k Q + cR +
      terminalOverhead isTop (parityXor p r) k' j')

private theorem exact_lift (isTop p : Bool) (k : Nat) (j : Sep)
    {s : ListBlank (Fin 2)} {n t : Nat}
    (h : ExactTail false (qPol j) s n t) :
    ExactTail isTop p (layerBits k j s) (liftInfo isTop p k j n).1
      (t+(liftInfo isTop p k j n).2) := by
  rcases h with ⟨s',c1,c2,hchain,hh,ht⟩
  let Q := n/6
  let r := maxR p j (n%6)
  obtain ⟨k',j',cR,hit,he⟩ := maxR_plan isTop p j (k+4*Q) (n%6) (by omega)
  have hn : n = 6*Q+n%6 := by dsimp [Q]; omega
  have hsplit : CarryChain false (6*Q+n%6) (qPol j) c1 s s' := hn ▸ hchain
  obtain ⟨ccQ,ccR,smid,hcc,hQchild,hRchild⟩ := carryChain_split (6*Q) hsplit
  have hp6 : parityXor (qPol j) (6*Q) = qPol j := by
    rw [show 6*Q=2*(3*Q) by omega]
    exact parityXor_even _ _
  rw [hp6] at hRchild
  have hQ := qCycles_sound isTop p j Q k ccQ s smid hQchild
  have hR := iterCarryAux_sound isTop r p (qPol j) (k+4*Q) j
    k' j' (n%6) cR ccR smid s' hit hRchild
  have hp16 : parityXor p (16*Q) = p := by
    rw [show 16*Q=2*(8*Q) by omega]
    exact parityXor_even _ _
  have hcomb := carryChain_append hQ (carryChain_congr_pol hp16.symm hR)
  have hp : parityXor p (16*Q+r) = parityXor p r := by
    unfold parityXor
    rw [show (16*Q+r)%2=r%2 by omega]
  have hq : parityXor (qPol j) n = parityXor (qPol j) (n%6) := by
    unfold parityXor
    rw [show n%2=(n%6)%2 by omega]
  rw [hq] at hh
  have hterm := terminalLift isTop (parityXor p r) k' j' he hh
  have hinfo : liftInfo isTop p k j n =
      (16*Q+r, qCyclesCost isTop p j k Q+cR+
        terminalOverhead isTop (parityXor p r) k' j') := by
    unfold liftInfo
    dsimp only
    rw [hit]
  rw [hinfo]
  refine ⟨layerBits k' j' s',_,_,hcomb,?_,?_⟩
  · rw [hp]
    exact hterm
  · dsimp only
    omega

/-- Two numbers plus a proof. Computation never traverses the giant CarryChain.
    Tape equality transport preserves the summary fields definitionally. -/
private structure Cert (isTop p : Bool) (s : ListBlank (Fin 2)) where
  n : Nat
  ticks : Nat
  sound : ExactTail isTop p s n ticks

private def certCast {isTop p : Bool} {s s' : ListBlank (Fin 2)}
    (h : s=s') (c : Cert isTop p s) : Cert isTop p s' :=
  ⟨c.n,c.ticks,by rw [←h]; exact c.sound⟩

private def certHalt {isTop p : Bool} {s : ListBlank (Fin 2)} {t : Nat}
    (h : CarryExact isTop p s t) : Cert isTop p s :=
  ⟨0,t,exact_terminal h⟩

private def certLift (isTop p : Bool) (k : Nat) (j : Sep) {s : ListBlank (Fin 2)}
    (c : Cert false (qPol j) s) : Cert isTop p (layerBits k j s) :=
  ⟨(liftInfo isTop p k j c.n).1,c.ticks+(liftInfo isTop p k j c.n).2,
    exact_lift isTop p k j c.sound⟩

private def th_ruleC {q : Bool} {c : Nat} {lhs rhs rest : List Nat} {s : ListBlank (Fin 2)}
    (hr : ∀ t : ListBlank (Fin 2), CarrySem false q c (uBits lhs +> t) (uBits rhs +> t))
    (ht : Cert false (!q) (uBits (rhs ++ rest) +> s)) :
    Cert false q (uBits (lhs ++ rest) +> s) :=
  ⟨ht.n+1,c+ht.ticks,by
    rw [uBits_append lhs rest s]
    have h := ht.sound
    rw [uBits_append rhs rest s] at h
    exact exact_prepend (hr (uBits rest +> s)) h⟩

private def th_spawn1C {q : Bool} (j : Sep) {rest : List Nat} {s : ListBlank (Fin 2)}
    (ht : Cert false (qPol j) (uBits rest +> s)) :
    Cert false q (uBits ([8] ++ sepList j ++ rest) +> s) := by
  refine certCast ?_ (certLift false q 0 j ht)
  rw [uBits_append ([8] ++ sepList j) rest s, uBits_append [8] (sepList j) _,
      uBits_eight, uBits_sepList j]
  simp [layerBits, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq]

private def th_spawn2C {q : Bool} (j : Sep) {rest : List Nat} {s : ListBlank (Fin 2)}
    (ht : Cert false (qPol j) (uBits rest +> s)) :
    Cert false q (uBits ([8,8] ++ sepList j ++ rest) +> s) := by
  refine certCast ?_ (certLift false q 1 j ht)
  rw [uBits_append ([8,8] ++ sepList j) rest s, uBits_append [8,8] (sepList j) _,
      uBits_sepList j]
  have h88 : uBits [8,8] = u8^2 := by decide
  rw [h88]
  rfl

private theorem halt_bottom_exact :
    CarryExact false true (uBits [0, 6, 2, 0, 6, 2, 0, 9] +> default) 304 := by
  intro sW
  have hrun : (evalWin (sepBits .S2 +> (uBits [0, 6, 2, 0, 6, 2, 0, 9] +> default)) sW 1 false [0]
    [])
      [target_tm]⊢^{304} (evalWin default sW 2 false [] rsHaltBottom) :=
    chkWin_eq true false 304 1 true (sepBits .S2 ++ uBits [0, 6, 2, 0, 6, 2, 0, 9]) [0]
      2 false [] rsHaltBottom
      default sW (fun _ => rfl) (fun h => nomatch h)
      (by rw [← app_assoc (sepBits .S2) (uBits [0, 6, 2, 0, 6, 2, 0, 9]) default]; exact
        evalWin_b0_pfx _ default sW)
      rfl halt_bottom_win
  refine ⟨evalWin default sW 2 false [] rsHaltBottom, hrun, ?_⟩
  simp [evalWin, step, target_tm, head_def_fin]

private def eat_M06_2C (s : ListBlank (Fin 2))
    (h : Cert false false (uBits [0, 6, 6, 6] +> s)) :
    Cert false false (uBits [0, 6, 6, 6, 0, 6, 0, 6] +> s) := by
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6, 0, 6, 0, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := [0, 6, 0, 6]) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8, 0, 6, 0, 6]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8, 0, 6, 0, 6])
    tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := [0, 6]) tr_04 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14, 0, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [14, 0, 6]) tr_06 ?_
  refine th_ruleC (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := [0, 6]) tr_07 ?_
  refine th_spawn1C .S0 (rest := [0, 20, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_08 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 6]) tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 6]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 6, 6]) ?_
  exact h

private def eat_M06_2_powC (s : ListBlank (Fin 2))
    (h : Cert false false (uBits [0,6,6,6] +> s)) :
    Cert false false (uBits [0,6,6,6] +> ((u06^2) +> s)) := by
  refine certCast ?_ (eat_M06_2C s h)
  have h2 : u06^2 = uBits [0,6,0,6] := by decide
  rw [h2, ← uBits_append [0,6,6,6] [0,6,0,6] s]
  rfl

private def eat_M06_2kC : ∀ (k : Nat) (s : ListBlank (Fin 2)),
    Cert false false (uBits [0,6,6,6] +> s) →
    Cert false false (uBits [0,6,6,6] +> ((u06^(2*k)) +> s))
  | 0,s,h => certCast (by simp [list_pow_succ,list_pow_zero,list_pow_one,ListBlank.append]) h
  | k+1,s,h => certCast (by
      have hpow : (u06^(2*(k+1))) +> s = (u06^2) +> ((u06^(2*k)) +> s) := by
        rw [show 2*(k+1)=2+2*k by omega,pow_add_list,app_assoc]
      rw [hpow])
      (eat_M06_2_powC ((u06^(2*k)) +> s) (eat_M06_2kC k s h))

private def th_peel_uC {q : Bool} {hd xs : List Nat} {cs : List Chunk}
    (h : Cert false q (uBits (hd ++ xs) +> eChunks cs)) :
    Cert false q (uBits hd +> eChunks (.u xs :: cs)) :=
  certCast (by dsimp only [eChunks]; rw [←uBits_append hd xs (eChunks cs)]) h

private def th_peel_m06_1C {q : Bool} {hd : List Nat} {cs : List Chunk}
    (h : Cert false q (uBits (hd ++ [0,6]) +> eChunks cs)) :
    Cert false q (uBits hd +> eChunks (.m06 1 :: cs)) :=
  certCast (by
    dsimp only [eChunks]
    have h1 : u06^1 = uBits [0,6] := by
      simp [list_pow_succ,list_pow_zero,list_pow_one,List.append_eq,u06_eq_uBits]
    rw [h1,←uBits_append hd [0,6] (eChunks cs)]) h

private def th_peel_m06_succC {q : Bool} {hd : List Nat} {n : Nat} {cs : List Chunk}
    (h : Cert false q (uBits (hd ++ [0,6]) +> eChunks (.m06 n :: cs))) :
    Cert false q (uBits hd +> eChunks (.m06 (n+1) :: cs)) :=
  certCast (by
    dsimp only [eChunks]
    have hstep : (u06^(n+1)) +> eChunks cs = uBits [0,6] +> ((u06^n) +> eChunks cs) := by
      rw [pow_succ_left u06 n,app_assoc]
      exact congrArg (· +> ((u06^n) +> eChunks cs)) u06_eq_uBits
    rw [hstep,←uBits_append hd [0,6] ((u06^n) +> eChunks cs)]) h

private def th_loop_evenC (m : Nat) {cs : List Chunk}
    (h : Cert false false (uBits [0,6,6,6] +> eChunks cs)) :
    Cert false false (uBits [0,6,6,6] +> eChunks (.m06 (2*m) :: cs)) :=
  eat_M06_2kC m (eChunks cs) h

private def th_loop_oddC (m : Nat) {cs : List Chunk}
    (h : Cert false false (uBits [0,6,6,6] +> eChunks (.m06 1 :: cs))) :
    Cert false false (uBits [0,6,6,6] +> eChunks (.m06 (2*m+1) :: cs)) :=
  certCast (by dsimp only [eChunks]; rw [pow_add_list u06 (2*m) 1,app_assoc])
    (eat_M06_2kC m ((u06^1) +> eChunks cs) h)

private def tailCert : Cert false false (uBits [] +> eChunks era2Chunks) := by
  dsimp only [era2Chunks]
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := []) tr_00 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [14, 0, 6]) (rhs := [10, 14]) (rest := []) tr_11 ?_
  refine th_ruleC (lhs := [10, 14]) (rhs := [8, 0, 20]) (rest := []) tr_12 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [8, 0, 20, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_13 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_evenC 183 ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 2, 0, 6, 0, 6])
    tr_15 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 2, 0, 6, 0, 6]) tr_06 ?_
  refine th_ruleC (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 2, 0, 6, 0, 6])
    tr_16 ?_
  refine th_spawn1C .S0 (rest := [0, 16, 0, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [2, 0, 6, 0, 6])
    tr_17 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 2, 0, 6, 0, 6]) tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 2, 0, 6, 0,
    6]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 2, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [2, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 2, 2, 0, 6, 0, 6]) (rhs := [10, 6, 0, 2, 2, 14]) (rest := []) tr_18 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [0, 2, 2, 14]) tr_19 ?_
  refine th_spawn1C .S4 (rest := [0, 2, 2, 14]) ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [2, 14]) tr_05 ?_
  refine th_ruleC (lhs := [10, 2]) (rhs := [16]) (rest := [14]) tr_20 ?_
  refine th_ruleC (lhs := [16, 14]) (rhs := [8, 0, 2, 0, 20]) (rest := []) tr_21 ?_
  refine th_ruleC (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [20]) tr_22 ?_
  refine th_ruleC (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [20]) tr_23 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [8, 14, 20, 0, 6]) (rhs := [8, 10, 8, 0, 2, 0, 2, 14]) (rest := []) tr_24
    ?_
  refine th_ruleC (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 2, 0, 2, 14]) tr_25 ?_
  refine th_ruleC (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2,
    14]) tr_26 ?_
  refine th_spawn2C .S0 (rest := [0, 6, 2, 0, 2, 14]) ?_
  refine th_ruleC (lhs := [0, 6, 2, 0, 2, 14]) (rhs := [0, 2, 6, 0, 20]) (rest := []) tr_27 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [6, 0, 20]) tr_05 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [20]) (rest := [0, 20]) tr_28 ?_
  refine th_ruleC (lhs := [20, 0, 20]) (rhs := [8, 0, 2, 0, 2, 28]) (rest := []) tr_29 ?_
  refine th_spawn1C .S0 (rest := [28]) ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [28, 0]) (rhs := [10, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_30 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 0, 2, 0, 6, 6]) tr_31 ?_
  refine th_spawn1C .S1 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_oddC 67 ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_m06_1C ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := []) tr_04 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [14]) tr_06 ?_
  refine th_ruleC (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := []) tr_07 ?_
  refine th_spawn1C .S0 (rest := [0, 20]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2, 0, 6, 0,
    6]) tr_08 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 2, 0, 2, 0, 6,
    0, 6]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 6, 2, 0, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 2, 0, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 2]) (rhs := [10, 8, 0, 4]) (rest := [0, 2, 0, 6, 0, 6]) tr_32 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 4, 0, 2, 0, 6, 0, 6]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [4, 0, 2, 0, 6, 0,
    6]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 4, 0, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6, 4, 0]) (rhs := [0, 2, 12]) (rest := [2, 0, 6, 0, 6]) tr_33 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [12, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 12]) (rhs := [26]) (rest := [2, 0, 6, 0, 6]) tr_34 ?_
  refine th_ruleC (lhs := [26, 2, 0, 6, 0, 6]) (rhs := [8, 0, 2, 0, 2, 0, 2, 6, 0, 2, 14]) (rest :=
    []) tr_35 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 6, 0, 2, 14]) ?_
  refine th_ruleC (lhs := [0, 2, 6]) (rhs := [0, 12]) (rest := [0, 2, 14]) tr_36 ?_
  refine th_ruleC (lhs := [0, 12]) (rhs := [20]) (rest := [0, 2, 14]) tr_37 ?_
  refine th_ruleC (lhs := [20, 0, 2]) (rhs := [10, 0, 2, 10]) (rest := [14]) tr_38 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 10, 14]) tr_31 ?_
  refine th_spawn1C .S1 (rest := [10, 14]) ?_
  refine th_ruleC (lhs := [10, 14]) (rhs := [28]) (rest := []) tr_39 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [28, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_40 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_oddC 24 ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_m06_1C ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := []) tr_04 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [14]) tr_06 ?_
  refine th_ruleC (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := []) tr_07 ?_
  refine th_spawn1C .S0 (rest := [0, 20]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2, 0, 6, 0,
    6]) tr_08 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 2, 0, 2, 0, 6,
    0, 6]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 6, 2, 0, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 2, 0, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 2]) (rhs := [10, 8, 0, 4]) (rest := [0, 2, 0, 6, 0, 6]) tr_32 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 4, 0, 2, 0, 6, 0, 6]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [4, 0, 2, 0, 6, 0,
    6]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 4, 0, 2, 0, 6, 0, 6]) ?_
  refine th_ruleC (lhs := [0, 6, 4, 0]) (rhs := [0, 2, 12]) (rest := [2, 0, 6, 0, 6]) tr_33 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [12, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 12]) (rhs := [26]) (rest := [2, 0, 6, 0, 6]) tr_34 ?_
  refine th_ruleC (lhs := [26, 2, 0, 6, 0, 6]) (rhs := [8, 0, 2, 0, 2, 0, 2, 6, 0, 2, 14]) (rest :=
    []) tr_35 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 6, 0, 2, 14]) ?_
  refine th_ruleC (lhs := [0, 2, 6]) (rhs := [0, 12]) (rest := [0, 2, 14]) tr_36 ?_
  refine th_ruleC (lhs := [0, 12]) (rhs := [20]) (rest := [0, 2, 14]) tr_37 ?_
  refine th_ruleC (lhs := [20, 0, 2]) (rhs := [10, 0, 2, 10]) (rest := [14]) tr_38 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 10, 14]) tr_31 ?_
  refine th_spawn1C .S1 (rest := [10, 14]) ?_
  refine th_ruleC (lhs := [10, 14]) (rhs := [28]) (rest := []) tr_39 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [28, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_40 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_evenC 8 ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 10]) tr_15 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 10]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 10]) tr_06 ?_
  refine th_ruleC (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 10]) tr_16 ?_
  refine th_spawn1C .S0 (rest := [0, 16, 0, 10]) ?_
  refine th_ruleC (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [10]) tr_17 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 10]) tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 10]) tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 10]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 2, 10]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [2, 10]) tr_00 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [14, 2, 10, 0]) (rhs := [10, 6, 14]) (rest := [6]) tr_41 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [14, 6]) tr_19 ?_
  refine th_spawn1C .S4 (rest := [14, 6]) ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [14, 6, 0]) (rhs := [8, 0, 2, 8, 0, 2]) (rest := [6]) tr_42 ?_
  refine th_ruleC (lhs := [8, 0, 2, 8]) (rhs := [8, 0, 14]) (rest := [0, 2, 6]) tr_43 ?_
  refine th_ruleC (lhs := [8, 0, 14]) (rhs := [8, 22]) (rest := [0, 2, 6]) tr_44 ?_
  refine th_ruleC (lhs := [8, 22, 0]) (rhs := [8, 10, 0, 2, 0, 6]) (rest := [2, 6]) tr_45 ?_
  refine th_spawn1C .S5 (rest := [0, 6, 2, 6]) ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [0, 6, 2, 6, 0]) (rhs := [0, 2, 6, 10]) (rest := [6]) tr_46 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [6, 10, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [20]) (rest := [10, 6]) tr_28 ?_
  refine th_ruleC (lhs := [20, 10, 6]) (rhs := [8, 0, 2, 0, 2, 8, 0, 12]) (rest := []) tr_47 ?_
  refine th_spawn1C .S0 (rest := [8, 0, 12]) ?_
  refine th_spawn1C .S4 (rest := []) ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := []) tr_00 ?_
  refine th_peel_m06_succC ?_
  refine th_ruleC (lhs := [14, 0, 6]) (rhs := [10, 14]) (rest := []) tr_11 ?_
  refine th_ruleC (lhs := [10, 14]) (rhs := [8, 0, 20]) (rest := []) tr_12 ?_
  refine th_peel_m06_1C ?_
  refine th_ruleC (lhs := [8, 0, 20, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_13 ?_
  refine th_spawn1C .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_ruleC (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 6, 6]) tr_15 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 6, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 6, 6]) tr_06 ?_
  refine th_ruleC (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 6, 6]) tr_16 ?_
  refine th_spawn1C .S0 (rest := [0, 16, 0, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [6, 6]) tr_17 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 6, 6]) tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 6, 6]) tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 6, 6]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 2, 6, 6]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [2, 6, 6]) tr_00 ?_
  refine th_ruleC (lhs := [14, 2, 6, 6]) (rhs := [10, 6, 16]) (rest := []) tr_48 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [16]) tr_19 ?_
  refine th_spawn1C .S4 (rest := [16]) ?_
  refine th_peel_m06_1C ?_
  refine th_ruleC (lhs := [16, 0]) (rhs := [8, 0, 2, 0, 6]) (rest := [6]) tr_49 ?_
  refine th_ruleC (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [6, 6]) tr_22 ?_
  refine th_ruleC (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [6, 6]) tr_23 ?_
  refine th_ruleC (lhs := [8, 14, 6, 6]) (rhs := [8, 10, 8, 0, 8]) (rest := []) tr_50 ?_
  refine th_ruleC (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 8]) tr_25 ?_
  refine th_ruleC (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_26 ?_
  refine th_spawn2C .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_uC ?_
  refine th_ruleC (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 2, 0, 6, 0, 2, 0, 2,
    0, 9]) tr_15 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9])
    tr_05 ?_
  refine th_ruleC (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9]) tr_06
    ?_
  refine th_ruleC (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 2, 0, 6, 0, 2, 0,
    2, 0, 9]) tr_16 ?_
  refine th_spawn1C .S0 (rest := [0, 16, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9]) ?_
  refine th_ruleC (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [2, 0, 6, 0, 2, 0,
    2, 0, 9]) tr_17 ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 2, 0, 6, 0, 2, 0, 2, 0,
    9]) tr_05 ?_
  refine th_ruleC (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 2, 0, 6, 0, 2, 0, 2, 0,
    9]) tr_09 ?_
  refine th_ruleC (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 2, 0, 6, 0, 2,
    0, 2, 0, 9]) tr_10 ?_
  refine th_spawn1C .S6 (rest := [0, 6, 2, 2, 0, 6, 0, 2, 0, 2, 0, 9]) ?_
  refine th_ruleC (lhs := [0, 6]) (rhs := [14]) (rest := [2, 2, 0, 6, 0, 2, 0, 2, 0, 9]) tr_00 ?_
  refine th_ruleC (lhs := [14, 2, 2, 0, 6, 0, 2]) (rhs := [10, 6, 0, 2, 2, 10]) (rest := [0, 2, 0,
    9]) tr_51 ?_
  refine th_ruleC (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [0, 2, 2, 10, 0, 2, 0, 9]) tr_19 ?_
  refine th_spawn1C .S4 (rest := [0, 2, 2, 10, 0, 2, 0, 9]) ?_
  refine th_ruleC (lhs := [0, 2]) (rhs := [10]) (rest := [2, 10, 0, 2, 0, 9]) tr_05 ?_
  refine th_ruleC (lhs := [10, 2]) (rhs := [16]) (rest := [10, 0, 2, 0, 9]) tr_20 ?_
  refine th_ruleC (lhs := [16, 10]) (rhs := [8, 0, 2, 0, 16]) (rest := [0, 2, 0, 9]) tr_52 ?_
  refine th_ruleC (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [16, 0, 2, 0, 9]) tr_22 ?_
  refine th_ruleC (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [16, 0, 2, 0, 9]) tr_23 ?_
  refine th_ruleC (lhs := [8, 14, 16, 0]) (rhs := [8, 10, 8, 0, 2, 0, 6]) (rest := [2, 0, 9]) tr_53
    ?_
  refine th_ruleC (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 2, 0, 6, 2, 0, 9]) tr_25 ?_
  refine th_ruleC (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 6, 2,
    0, 9]) tr_26 ?_
  refine th_spawn2C .S0 (rest := [0, 6, 2, 0, 6, 2, 0, 9]) ?_
  exact certHalt halt_bottom_exact


private def topCert : Cert true false (layerBits 0 .S0 (layerBits 0 .S4 (eChunks era2Chunks))) :=
  certLift true false 0 .S0 (certLift false true 0 .S4 tailCert)

private def runMasterCount : Nat → BaseState → Option (BaseState × Nat)
  | 0, a => some (a,0)
  | n+1, a =>
    match masterStep a with
    | none => none
    | some (b,c) => (runMasterCount n b).map fun (e,d) => (e,c+d)

private theorem runMasterCount_sound :
    ∀ (n : Nat) (a b : BaseState) (c : Nat), runMasterCount n a = some (b,c) →
      (encodeBase a) [target_tm]⊢^{c} (encodeBase b)
  | 0,a,b,c,h => by
    simp only [runMasterCount,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    rfl
  | n+1,a,b,c,h => by
    rcases hm : masterStep a with _ | ⟨a',c1⟩
    · simp [runMasterCount,hm] at h
    · rcases hr : runMasterCount n a' with _ | ⟨b',c2⟩
      · simp [runMasterCount,hm,hr] at h
      · simp only [runMasterCount,hm,hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ms_trans (masterStep_sound hm) (runMasterCount_sound n a' b' c2 hr)

private def checkedCost (n : Nat) (a b : BaseState) : Option Nat :=
  match runMasterCount n a with
  | none => none
  | some (r,c) => if beqBS r b then some c else none

private theorem checkedCost_sound {n : Nat} {a b : BaseState} {c : Nat}
    (h : checkedCost n a b = some c) : (encodeBase a) [target_tm]⊢^{c} (encodeBase b) := by
  rcases hr : runMasterCount n a with _ | ⟨b',c'⟩
  · simp [checkedCost,hr] at h
  · cases he : beqBS b' b
    · simp [checkedCost,hr,he] at h
    · have hb := beqBS_eq he
      subst b'
      simp [checkedCost,hr,he] at h
      subst c'
      exact runMasterCount_sound n a b c hr

private theorem checkedCost_getD_sound (n : Nat) (a b : BaseState)
    (h : (checkedCost n a b).isSome = true) :
    (encodeBase a) [target_tm]⊢^{(checkedCost n a b).getD 0} (encodeBase b) := by
  cases he : checkedCost n a b with
  | none => simp [he] at h
  | some c => simpa only [he,Option.getD_some] using checkedCost_sound he

private def prefixCost : Nat :=
  (checkedCost 1000 cp0 cp1).getD 0 +
  (checkedCost 1000 cp1 cp2).getD 0 +
  (checkedCost 1000 cp2 cp3).getD 0 +
  (checkedCost 1000 cp3 cp4).getD 0 +
  (checkedCost 444 cp4 cp5).getD 0

private theorem prefixExact : (encodeBase cp0) [target_tm]⊢^{prefixCost} (encodeBase cp5) := by
  have h01 := checkedCost_getD_sound 1000 cp0 cp1 (by decide +kernel)
  have h12 := checkedCost_getD_sound 1000 cp1 cp2 (by decide +kernel)
  have h23 := checkedCost_getD_sound 1000 cp2 cp3 (by decide +kernel)
  have h34 := checkedCost_getD_sound 1000 cp3 cp4 (by decide +kernel)
  have h45 := checkedCost_getD_sound 444 cp4 cp5 (by decide +kernel)
  exact ms_trans (ms_trans (ms_trans (ms_trans h01 h12) h23) h34) h45

private theorem topHalt {p : Bool} {s : ListBlank (Fin 2)} {t : Nat}
    (h : CarryExact true p s t) :
    HaltExact (evalWin (topBits p +> s) default 1 true [] [0]) t := by
  cases p <;> exact h

private theorem countedHalt :
    HaltExact (init [] : Cfg (Fin 2) (Fin 6)) (prefixCost+topCert.ticks) := by
  rcases topCert.sound with ⟨s',c1,c2,hc,hh,ht⟩
  have h := prependHalt (carryChain_top_reaches hc) (topHalt hh)
  rw [←ht,←encode_cp5_eq] at h
  exact prependHalt prefixExact h

#eval prefixCost
#eval topCert.n
#eval topCert.ticks

/-- Primitive ordinary move count plus seven (one halt query and up to six
    blank-delay moves) stays below this explicit champion threshold. -/
private theorem raw8_halt_under_pow2600 :
    ∃ n : Nat, n+7 ≤ 2^2600 ∧
      ∃ cfg', (init [] : Cfg (Fin 2) (Fin 6)) [target]⊢^{n} cfg' ∧ (step target cfg').isNone := by
  refine ⟨prefixCost+topCert.ticks,by decide +kernel,?_⟩
  obtain ⟨cfg',h,hh⟩ := countedHalt
  refine ⟨cfg',?_,?_⟩
  · simpa only [target_tm_eq_target] using h
  · simpa only [target_tm_eq_target] using hh

#print axioms maxR_plan
#print axioms exact_lift
#print axioms countedHalt
#print axioms raw8_halt_under_pow2600
end BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.Counted
