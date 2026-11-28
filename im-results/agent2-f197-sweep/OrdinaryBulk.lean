import OrdinaryData
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (pre_append)

theorem cycles (W : Word) (rs : List Rule) (hok : rs.all ruleOK = true)
    (hc : rs.all coreOnly = true) (ha : applyRules rs 4 (W++flat R 4) = some (22,W))
    (n q : Nat) (l : Tape) (hl : l 0 = true) (hn : n≥4) :
    Reach (state n W (rep R (4*q) l)) (state (n+18*q) W l) := by
  induction q generalizing n with
  | zero => simp [rep]; exact reach_refl _
  | succ q ih =>
    have h := applyRules_shift rs 4 22 (n-4) (W++flat R 4) W hc ha
    rw [show 4+(n-4)=n by omega,show 22+(n-4)=n+18 by omega] at h
    have h1 := applyRules_sound rs n (n+18) (W++flat R 4) W (rep R (4*q) l)
      (rep_first R (by decide) (4*q) l hl) hok h
    simp only [state,pre_append,flat_pre,← rep_add] at h1
    have h2 := ih (n+18) (by omega)
    rw [show 4*(q+1)=4+4*q by omega,show n+18*(q+1)=n+18+18*q by omega]
    exact reach_trans h1 h2

theorem bulkOrd0 (q r : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state 4 E0 (rep R (9+4*q+r) l)) (state (42+18*q) (W0++flat R r) l) := by
  have h1 := applyRules_sound ent0 4 42 (E0++flat R 9) W0 (rep R (4*q+r) l)
    (rep_first R (by decide) _ _ hl) ent0_ok (by exact ent0_apply)
  simp only [state,pre_append,flat_pre,← rep_add] at h1
  have h2 := cycles W0 cyc0 cyc0_ok cyc0_core (by exact cyc0_apply) 42 q (rep R r l) (rep_first R (by decide) r l hl) (by decide)
  simp only [state,← rep_add] at h2
  simp only [state,pre_append,flat_pre]
  rw [show 9+4*q+r = 9+(4*q+r) by omega]
  exact reach_trans h1 h2

theorem bulkOrd1 (q r : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state 1 E1 (rep R (3+4*q+r) l)) (state (15+18*q) (W1++flat R r) l) := by
  have h1 := applyRules_sound ent1 1 15 (E1++flat R 3) W1 (rep R (4*q+r) l)
    (rep_first R (by decide) _ _ hl) ent1_ok (by exact ent1_apply)
  simp only [state,pre_append,flat_pre,← rep_add] at h1
  have h2 := cycles W1 cyc1 cyc1_ok cyc1_core (by exact cyc1_apply) 15 q (rep R r l) (rep_first R (by decide) r l hl) (by decide)
  simp only [state,← rep_add] at h2
  simp only [state,pre_append,flat_pre]
  rw [show 3+4*q+r = 3+(4*q+r) by omega]
  exact reach_trans h1 h2

theorem epoch0_lift (q r : Nat) (t : Terminal) (S : Word) (l : Tape) (hl : l 0 = true)
    (hS : okHead S = true) (hs : okHead t.src = true) (hd : okHead t.dst = true) (hc : terminalOK t = true) :
    ReachPos (state (2*(9+4*q+r+1)) (M++t.src++S) l)
      (state (42+18*q) (W0++flat R r++t.dst++S) l) := by
  have h1 := ordinary0 (9+4*q+r) t (pre S l) (pre_first S l hS hl) hs hd hc
  have h2 := bulkOrd0 q r (pre t.dst (pre S l)) (pre_first t.dst _ hd (pre_first S l hS hl))
  have h := reach_pos_trans h1 h2
  simpa only [state,pre_append] using h

theorem epoch1_lift (q r : Nat) (t : Terminal) (S : Word) (l : Tape) (hl : l 0 = true)
    (hS : okHead S = true) (hs : okHead t.src = true) (hd : okHead t.dst = true) (hc : terminalOK t = true) :
    ReachPos (state (2*(3+4*q+r)+1) (M++t.src++S) l)
      (state (15+18*q) (W1++flat R r++t.dst++S) l) := by
  have h1 := ordinary1 (3+4*q+r) t (pre S l) (pre_first S l hS hl) hs hd hc
  have h2 := bulkOrd1 q r (pre t.dst (pre S l)) (pre_first t.dst _ hd (pre_first S l hS hl))
  have h := reach_pos_trans h1 h2
  simpa only [state,pre_append] using h

def epochOK (t : Terminal) : Bool := okHead t.src && okHead t.dst && terminalOK t

def applyEpoch (t : Terminal) (n : Nat) (w : Word) : Option (Nat × Word) := do
  let src := M++t.src
  let S := w.drop src.length
  if w.take src.length != src || !okHead S then none else
    if n%2 == 0 then
      if n ≥ 20 then
        let m := n/2-10
        some (42+18*(m/4),W0++flat R (m%4)++t.dst++S)
      else none
    else
      if n ≥ 7 then
        let m := n/2-3
        some (15+18*(m/4),W1++flat R (m%4)++t.dst++S)
      else none

theorem applyEpoch_sound (t : Terminal) (n n' : Nat) (w w' : Word) (l : Tape) (hl : l 0 = true)
    (hc : epochOK t = true) (ha : applyEpoch t n w = some (n',w')) : ReachPos (state n w l) (state n' w' l) := by
  simp only [epochOK,Bool.and_eq_true] at hc
  by_cases hpar : n%2 = 0
  · simp [applyEpoch,hpar] at ha
    obtain ⟨⟨hp,hs⟩,hn,h1,h2⟩ := ha
    let S := w.drop (M.length+t.src.length)
    have hw : w = M++t.src++S := by
      dsimp [S]
      conv => lhs; rw [← List.take_append_drop (M.length+t.src.length) w]
      rw [hp]
    have h := epoch0_lift ((n/2-10)/4) ((n/2-10)%4) t S l hl hs hc.1.1 hc.1.2 hc.2
    have h3 : 2*(9+4*((n/2-10)/4)+(n/2-10)%4+1) = n := by omega
    rw [h3,← hw,h1] at h
    simp only [List.append_assoc,S] at h
    rw [h2] at h
    exact h
  · simp [applyEpoch,hpar] at ha
    obtain ⟨⟨hp,hs⟩,hn,h1,h2⟩ := ha
    let S := w.drop (M.length+t.src.length)
    have hw : w = M++t.src++S := by
      dsimp [S]
      conv => lhs; rw [← List.take_append_drop (M.length+t.src.length) w]
      rw [hp]
    have h := epoch1_lift ((n/2-3)/4) ((n/2-3)%4) t S l hl hs hc.1.1 hc.1.2 hc.2
    have h3 : 2*(3+4*((n/2-3)/4)+(n/2-3)%4)+1 = n := by omega
    rw [h3,← hw,h1] at h
    simp only [List.append_assoc,S] at h
    rw [h2] at h
    exact h

#print axioms applyEpoch_sound
end F197.Agent2Self
