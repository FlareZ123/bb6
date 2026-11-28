import SeedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (b pre_append zeros_blank)
open PrefixCheck

def OUT01 := enc "JTAATAATAATATAAATUJTTAATAAATAUJTT"

theorem marker01 (k : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state (2*(2*k+3)) (M++enc "TATJ") l) (state 1 OUT01 (rep LB k (pre (enc "T") l))) := by
  have h1 := descend_many (2*k+3) 0 (pre (enc "TATJ") l) (by rfl)
  have h2 := Agent2EpochMarker.bulk01 k l hl
  rw [kpow_eq,blockpow_eq] at h2
  have hs : Agent2EpochMarker.source l = pre (enc "TATJ") l := by rfl
  have ht : Agent2EpochMarker.t l = pre (enc "T") l := by rfl
  rw [hs,ht] at h2
  have he (z : Tape) : Agent2EpochMarker.ent0 z = pre M (pre K z) := by rw [← pre_append]; rfl
  have ho (z : Tape) : Agent2EpochMarker.out0g2 z = pre P (pre OUT01 z) := by rw [← pre_append]; rfl
  rw [he,ho] at h2
  change run _ (state 0 M (rep K (2*k+3) (pre (enc "TATJ") l))) = some (state 1 OUT01 (rep LB k (pre (enc "T") l))) at h2
  simp only [Nat.add_zero] at h1
  have h3 := reach_trans h1 (show Reach _ _ from ⟨_,h2⟩)
  simpa only [state,pre_append] using h3

def GS := enc "TATUJTTJAA"
def GT := enc "AAATATAAT"
def GW := enc "ATTJAUJ"
def VV := bits "1110"

theorem hpow_eq (k : Nat) (r : Tape) : Agent2EpochMarker.hpow k r = rep HB (2*k) r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Agent2EpochMarker.hpow,ih]
    rw [show 2*(k+1)=2*k+2 by omega]
    rfl

theorem generic11 (k : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state (2*(2*k+2)+1) (M++GS) l) (state 0 OUT (rep LB k (pre GT l))) := by
  have h0 := epoch_enter1 (2*k+2) (pre GS l) (by rfl)
  let r := rep HB (2*k+1) Agent2EpochMarker.r1
  have hr : r 0 = true := rep_first HB (by decide) _ _ (by rfl)
  have h1 := guard_sound GS HB (GW++GT) VV 121 414 l r hl hr (by decide)
  rw [pre_append GW GT] at h1
  have hr1 : rep HB (2*k+2) Agent2EpochMarker.r1 = pre HB r := by rfl
  rw [hr1] at h0
  have h1' : Reach (b (pre GS l) (pre HB r)) (b (pre GW (pre GT l)) (pre VV r)) := ⟨414,h1⟩
  have h2 := Agent2EpochMarker.cycle_many k (pre GT l) (pre HB Agent2EpochMarker.r1) (by rfl) (by rfl)
  rw [hpow_eq,blockpow_eq,rep_comm] at h2
  have hv (z : Tape) : Agent2EpochMarker.v z = pre VV z := by rfl
  have hg (z : Tape) : Agent2EpochMarker.g z = pre GW z := by rfl
  rw [hv,hv,hg,hg] at h2
  let y := rep LB k (pre GT l)
  have hy : y 0 = true := rep_first LB (by decide) _ _ (by rfl)
  have h2' : Reach (b (pre GW (pre GT l)) (pre VV r)) (b (pre GW y) (pre VV (pre HB Agent2EpochMarker.r1))) := ⟨_,h2⟩
  have h3 := guardBlank_sound GW (((VV++HB)++RB1)++List.replicate 5 false) OUT [true] 226 775 y hy (by decide)
  rw [pre_append ((VV++HB)++RB1),zeros_blank,pre_append (VV++HB) RB1,pre_append VV HB] at h3
  have h3' : Reach (b (pre GW y) (pre VV (pre HB Agent2EpochMarker.r1))) (state 0 OUT y) := ⟨775,h3⟩
  have h := reach_trans (reach_of_pos h0) (reach_trans h1' (reach_trans h2' h3'))
  simpa only [state,pre_append,y] using h

-- Deep reservoirs are stored as finite words and exact arbitrary-size counts.
abbrev Rope := List (Word × Nat)
def ropeTape : Rope → Tape
  | [] => e
  | (w,n)::rs => rep w n (ropeTape rs)

def ropeOK (r : Rope) : Bool := r.all (fun (w,_) => w.head? == some true)

theorem rope_head (r : Rope) (h : ropeOK r = true) : ropeTape r 0 = true := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    rcases a with ⟨w,n⟩
    simp only [ropeOK,List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    exact rep_first w h.1 n _ (ih h.2)

theorem rope_pull (w s : Word) (n m : Nat) (r : Rope) (h : m ≤ n) :
    pre w (ropeTape ((s,n)::r)) = pre (w++flat s m) (ropeTape ((s,n-m)::r)) := by
  simp only [ropeTape,pre_append,flat_pre,← rep_add]
  rw [show m+(n-m)=n by omega]

theorem rope_pull_partial (w s a z : Word) (n : Nat) (r : Rope) (h : s = a++z) :
    pre w (ropeTape ((s,n+1)::r)) = pre (w++a) (ropeTape ((z,1)::(s,n)::r)) := by
  simp only [ropeTape,rep,pre_append]
  rw [h]
  simp only [pre_append]

def pushRope (w : Word) (n : Nat) (r : Rope) : Rope :=
  if w.isEmpty || n == 0 then r else (w,n)::r

theorem pushRope_sound (w : Word) (n : Nat) (r : Rope) :
    ropeTape (pushRope w n r) = rep w n (ropeTape r) := by
  cases w with
  | nil =>
    simp [pushRope]
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  | cons b w => cases n <;> rfl

def pullRope : Nat → Nat → Rope → Word × Rope
  | 0,_,r => ([],r)
  | _+1,0,r => ([],r)
  | _+1,_+1,[] => ([],[])
  | f+1,k+1,(s,n)::r =>
    if n*s.length ≤ k+1 then
      let (u,r') := pullRope f (k+1-n*s.length) r
      (flat s n ++ u,r')
    else
      let m := (k+1)/s.length
      let d := (k+1)%s.length
      if d == 0 then (flat s m,pushRope s (n-m) r)
      else (flat s m ++ s.take d,pushRope (s.drop d) 1 (pushRope s (n-m-1) r))

theorem pullRope_sound (f k : Nat) (r : Rope) :
    ropeTape r = pre (pullRope f k r).1 (ropeTape (pullRope f k r).2) := by
  induction f generalizing k r with
  | zero => rfl
  | succ f ih =>
    cases k with
    | zero => rfl
    | succ k =>
      cases r with
      | nil => rfl
      | cons a r =>
        rcases a with ⟨s,n⟩
        simp only [pullRope]
        split
        · rename_i h
          cases hres : pullRope f (k+1-n*s.length) r with
          | mk u r' =>
            have h := ih (k+1-n*s.length) r
            rw [hres] at h
            simp only [ropeTape,pre_append,flat_pre]
            rw [← h]
        · rename_i h
          have hs : 0 < s.length := by
            by_cases hz : s.length = 0
            · simp [hz] at h
            · omega
          have hm : (k+1)/s.length < n := (Nat.div_lt_iff_lt_mul hs).2 (by omega)
          split
          · simp only [ropeTape,flat_pre,pushRope_sound,← rep_add]
            rw [show (k+1)/s.length+(n-(k+1)/s.length)=n by omega]
          · simp only [ropeTape,pre_append,flat_pre,pushRope_sound]
            let m := (k+1)/s.length
            let d := (k+1)%s.length
            change rep s n (ropeTape r) = rep s m (pre (s.take d) (rep (s.drop d) 1 (rep s (n-m-1) (ropeTape r))))
            have he : m + (1+(n-m-1)) = n := by dsimp [m]; omega
            conv => lhs; rw [← he,rep_add,rep_add]
            change rep s m (pre s (rep s (n-m-1) (ropeTape r))) = rep s m (pre (s.take d) (pre (s.drop d) (rep s (n-m-1) (ropeTape r))))
            rw [← pre_append,List.take_append_drop]

def rstate (n : Nat) (w : Word) (r : Rope) := state n w (ropeTape r)

theorem refill (n : Nat) (w a : Word) (r r' : Rope) (f k : Nat)
    (h : pullRope f k r = (a,r')) : Reach (rstate n w r) (rstate n (w++a) r') := by
  have he := pullRope_sound f k r
  rw [h] at he
  have ht : rstate n w r = rstate n (w++a) r' := by
    unfold rstate state
    rw [pre_append]
    conv => lhs; rw [he]
  rw [← ht]
  exact reach_refl _

theorem root_marker01 (k : Nat) (Y : Word) (r : Rope) (hr : ropeOK r = true) (hY : okHead Y = true) :
    Reach (rstate (2*(2*k+3)) (M++enc "TATJ"++Y) r)
      (rstate 1 OUT01 ((LB,k)::(enc "T"++Y,1)::r)) := by
  have h := marker01 k (pre Y (ropeTape r)) (pre_first Y _ hY (rope_head r hr))
  have he : ropeTape ((LB,k)::(enc "T"++Y,1)::r) = rep LB k (pre (enc "T") (pre Y (ropeTape r))) := by
    change rep LB k (pre (enc "T"++Y) (ropeTape r)) = _
    rw [pre_append]
  simp only [rstate,he,state,pre_append]
  exact h

theorem root_generic11 (k : Nat) (Y : Word) (r : Rope) (hr : ropeOK r = true) (hY : okHead Y = true) :
    Reach (rstate (2*(2*k+2)+1) (M++GS++Y) r)
      (rstate 0 OUT ((LB,k)::(GT++Y,1)::r)) := by
  have h := generic11 k (pre Y (ropeTape r)) (pre_first Y _ hY (rope_head r hr))
  have he : ropeTape ((LB,k)::(GT++Y,1)::r) = rep LB k (pre GT (pre Y (ropeTape r))) := by
    change rep LB k (pre (GT++Y) (ropeTape r)) = _
    rw [pre_append]
  simp only [rstate,he,state,pre_append]
  exact h

#print axioms refill
#print axioms root_marker01
#print axioms root_generic11
#print axioms marker01
#print axioms generic11
#print axioms rope_head
#print axioms rope_pull
#print axioms rope_pull_partial
end F197.Agent2Self
