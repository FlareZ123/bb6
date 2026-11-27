import FastBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19MacroDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA

/-- Retain exact pushed bits until the next macro boundary. The remaining
    suffix is represented by its graph summary. -/
structure Stack where
  pre : List Bool
  tailId : Nat

def Holds (g : Graph) (s : Stack) (t : List Bool) : Prop :=
  ∃ u, t = s.pre ++ u ∧ TapeOK g u ∧ summary g u = s.tailId

def pushBit (s : Stack) (b : Bool) : Stack := ⟨b :: s.pre,s.tailId⟩

def popBit (g : Graph) (s : Stack) : List (Bool × Stack) :=
  match s.pre with
  | b::bs => [(b,⟨bs,s.tailId⟩)]
  | [] => (preds g s.tailId).map fun e => (e.1,⟨[],e.2⟩)

theorem push_holds {g s t} (h : Holds g s t) (b : Bool) :
    Holds g (pushBit s b) (b::t) := by
  obtain ⟨u,rfl,hu,he⟩ := h
  exact ⟨u,rfl,hu,he⟩

theorem pop_holds {g s t} (h : Holds g s t) :
    ∃ s', (t.headD false,s') ∈ popBit g s ∧ Holds g s' t.tail := by
  rcases s with ⟨P,i⟩
  obtain ⟨u,rfl,hu,he⟩ := h
  cases P with
  | nil =>
    refine ⟨⟨[],summary g u.tail⟩,?_,u.tail,rfl,tape_tail hu,rfl⟩
    have hp := tape_top hu
    simp only [List.nil_append,popBit,List.mem_map]
    exact ⟨(u.headD false,summary g u.tail),by simpa only [he] using hp,rfl⟩
  | cons b bs =>
    exact ⟨⟨bs,i⟩,by simp [popBit],u,rfl,hu,he⟩

def flush (g : Graph) : List Bool → Nat → Option Nat
  | [],i => some i
  | b::bs,i =>
    match flush g bs i with
    | none => none
    | some j =>
      let k := BB6.Agent32FastBiDFA.push g j b
      if edgeOK g k b j then some k else none

theorem flush_sound {g : Graph} {P : List Bool} {i j : Nat} {u : List Bool}
    (hu : TapeOK g u) (hi : summary g u = i) (hf : flush g P i = some j) :
    TapeOK g (P++u) ∧ summary g (P++u) = j := by
  induction P generalizing j with
  | nil => simpa [flush] using And.intro hu (hi.trans (Option.some.inj hf))
  | cons b bs ih =>
    cases h : flush g bs i with
    | none => simp [flush,h] at hf
    | some k =>
      obtain ⟨ht,he⟩ := ih h
      simp only [flush,h] at hf
      split at hf
      next hp =>
        have hj := Option.some.inj hf
        refine ⟨?_,?_⟩
        · apply tape_push b ht
          simpa only [he] using hp
        · simpa only [List.cons_append,summary,he] using hj
      next => contradiction

def endCheck (c : BB6.Agent32FastBiDFA.Cert) (q : Fin 6) (a : Bool) (l r : Stack) : Bool :=
  match flush c.left l.pre l.tailId, flush c.right r.pre r.tailId with
  | some i,some j => stateOK c q a i j
  | _,_ => false

theorem end_sound {c z l r} (hl : Holds c.left l z.l.tail)
    (hr : Holds c.right r z.r) (h : endCheck c z.q (z.l.headD false) l r = true) :
    BB6.Agent32FastBiDFA.Inv c z := by
  obtain ⟨u,hu,hut,huq⟩ := hl
  obtain ⟨v,hv,hvt,hvq⟩ := hr
  unfold endCheck at h
  cases hL : flush c.left l.pre l.tailId with
  | none => simp [hL] at h
  | some i =>
    cases hR : flush c.right r.pre r.tailId with
    | none => simp [hL,hR] at h
    | some j =>
      obtain ⟨h1,h2⟩ := flush_sound hut huq hL
      obtain ⟨h3,h4⟩ := flush_sound hvt hvq hR
      simp only [hL,hR] at h
      refine ⟨hu ▸ h1,hv ▸ h3,?_⟩
      simpa only [hu,hv,h2,h4] using (show stateOK c z.q (z.l.headD false) i j = true from h)

/-- A positive macro executes at most `fuel` primitive steps, stopping at the
    next visit of `stop`. No intermediate abstraction of newly pushed bits. -/
def go (p : PartialMachine) (c : BB6.Agent32FastBiDFA.Cert) (stop : Fin 6) :
    Nat → Bool → Fin 6 → Bool → Stack → Stack → Bool
  | 0,ret,q,a,l,r => if ret = true ∧ q = stop then endCheck c q a l r else false
  | n+1,ret,q,a,l,r =>
    if ret = true ∧ q = stop then endCheck c q a l r else
    match p (q,a) with
    | some (some mv) =>
      if mv.right then (popBit c.right r).all fun e => go p c stop n true mv.next e.1 (pushBit l mv.write) e.2
      else (popBit c.left l).all fun e => go p c stop n true mv.next e.1 e.2 (pushBit r mv.write)
    | _ => false

def BoundaryInv (c : BB6.Agent32FastBiDFA.Cert) (stop : Fin 6) (z : Z0) : Prop :=
  z.q = stop ∧ BB6.Agent32FastBiDFA.Inv c z

theorem go_sound {p c stop} (fuel : Nat) {ret : Bool} {z : Z0} {l r : Stack}
    (hl : Holds c.left l z.l.tail) (hr : Holds c.right r z.r)
    (h : go p c stop fuel ret z.q (z.l.headD false) l r = true) :
    ∃ n t, n ≤ fuel ∧ run0 p n z = some t ∧ BoundaryInv c stop t ∧ (ret = false → 0 < n) := by
  induction fuel generalizing z ret l r with
  | zero =>
    by_cases hs : ret = true ∧ z.q = stop
    · simp only [go,if_pos hs] at h
      exact ⟨0,z,Nat.le_refl _,rfl,⟨hs.2,end_sound hl hr h⟩,by intro h'; simp [h'] at hs⟩
    · simp [go,hs] at h
  | succ fuel ih =>
    by_cases hs : ret = true ∧ z.q = stop
    · simp only [go,if_pos hs] at h
      exact ⟨0,z,Nat.zero_le _,rfl,⟨hs.2,end_sound hl hr h⟩,by intro h'; simp [h'] at hs⟩
    · simp only [go,if_neg hs] at h
      cases hm : p (z.q,z.l.headD false) with
      | none => simp only [hm,Bool.false_eq_true] at h
      | some op =>
        cases op with
        | none => simp only [hm,Bool.false_eq_true] at h
        | some mv =>
          have step : step0 p z = some (move0 mv z) := by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some]
          cases hd : mv.right with
          | false =>
            simp only [hm,hd,ite_false,Bool.false_eq_true,List.all_eq_true] at h
            obtain ⟨s,hs',ht⟩ := pop_holds hl
            have h' := h _ hs'
            have hp := push_holds hr mv.write
            have hcheck : go p c stop fuel true (move0 mv z).q ((move0 mv z).l.headD false) s (pushBit r mv.write) = true := by
              simpa only [move0,hd,ite_false,Bool.false_eq_true] using h'
            have ht' : Holds c.left s (move0 mv z).l.tail := by
              simpa only [move0,hd,ite_false,Bool.false_eq_true] using ht
            have hp' : Holds c.right (pushBit r mv.write) (move0 mv z).r := by
              simpa only [move0,hd,ite_false,Bool.false_eq_true] using hp
            obtain ⟨n,t,hn,hRun,hInv,_⟩ := ih ht' hp' hcheck
            exact ⟨n+1,t,by omega,by rw [run0,step]; exact hRun,hInv,by omega⟩
          | true =>
            simp only [hm,hd,ite_true,List.all_eq_true] at h
            obtain ⟨s,hs',ht⟩ := pop_holds hr
            have h' := h _ hs'
            have hp := push_holds hl mv.write
            have hcheck : go p c stop fuel true (move0 mv z).q ((move0 mv z).l.headD false) (pushBit l mv.write) s = true := by
              simpa only [move0,hd,ite_true,List.headD_cons] using h'
            have hp' : Holds c.left (pushBit l mv.write) (move0 mv z).l.tail := by
              simpa only [move0,hd,ite_true,List.tail_cons] using hp
            have ht' : Holds c.right s (move0 mv z).r := by
              simpa only [move0,hd,ite_true] using ht
            obtain ⟨n,t,hn,hRun,hInv,_⟩ := ih hp' ht' hcheck
            exact ⟨n+1,t,by omega,by rw [run0,step]; exact hRun,hInv,by omega⟩

def rowCheck (p : PartialMachine) (c : BB6.Agent32FastBiDFA.Cert) (fuel : Nat) (a : Bool) : Bool :=
  (List.range (rows c 0 a).size).all fun l =>
    (row c 0 a l).all fun r => go p c 0 fuel false 0 a ⟨[],l⟩ ⟨[],r⟩

def check (p : PartialMachine) (c : BB6.Agent32FastBiDFA.Cert) (fuel : Nat) : Bool :=
  edgeOK c.left 0 false 0 && edgeOK c.right 0 false 0 && stateOK c 0 false 0 0 &&
    rowCheck p c fuel false && rowCheck p c fuel true

theorem macro_step {p c fuel z} (hc : check p c fuel = true) (hz : BoundaryInv c 0 z) :
    ∃ n t, 0 < n ∧ run0 p n z = some t ∧ BoundaryInv c 0 t := by
  obtain ⟨hq,hl,hr,hs⟩ := hz
  simp only [check,Bool.and_eq_true] at hc
  change stateOK c z.q (z.l.headD false) (summary c.left z.l.tail) (summary c.right z.r) = true at hs
  rw [hq] at hs
  have hh : rowCheck p c fuel (z.l.headD false) = true := by
    cases ha : z.l.headD false
    · exact hc.1.2
    · exact hc.2
  let l := summary c.left z.l.tail
  let r := summary c.right z.r
  have hin : l < (rows c 0 (z.l.headD false)).size := by
    by_cases hn : l < (rows c 0 (z.l.headD false)).size
    · exact hn
    · change stateOK c 0 (z.l.headD false) l r = true at hs
      simp only [BB6.Agent32FastBiDFA.stateOK,BB6.Agent32FastBiDFA.row,Array.getD,hn,dite_false,Trie.has,Bool.false_eq_true] at hs
  have ha := List.all_eq_true.mp hh l (List.mem_range.mpr hin)
  have hgo : go p c 0 fuel false 0 (z.l.headD false) ⟨[],l⟩ ⟨[],r⟩ = true := Trie.all_sound ha hs
  have hgo' : go p c 0 fuel false z.q (z.l.headD false) ⟨[],l⟩ ⟨[],r⟩ = true := by rw [hq]; exact hgo
  obtain ⟨n,t,_,hn,ht,hpos⟩ := go_sound fuel (show Holds c.left ⟨[],l⟩ z.l.tail from ⟨_,rfl,hl,rfl⟩) (show Holds c.right ⟨[],r⟩ z.r from ⟨_,rfl,hr,rfl⟩) hgo'
  exact ⟨n,t,hpos rfl,hn,ht⟩

theorem arbitrary {p c fuel z} (hc : check p c fuel = true) (hz : BoundaryInv c 0 z) (k : Nat) :
    ∃ n t, k ≤ n ∧ run0 p n z = some t ∧ BoundaryInv c 0 t := by
  induction k generalizing z with
  | zero => exact ⟨0,z,Nat.le_refl _,rfl,hz⟩
  | succ k ih =>
    obtain ⟨n,t,hn,ht,hI⟩ := macro_step hc hz
    obtain ⟨j,u,hj,hu,hJ⟩ := ih hI
    exact ⟨n+j,u,by omega,join0 ht hu,hJ⟩

theorem never (p : PartialMachine) (c : BB6.Agent32FastBiDFA.Cert) (fuel : Nat) (hc : check p c fuel = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have hi : BoundaryInv c 0 ⟨0,[],[]⟩ := by
    simp only [check,Bool.and_eq_true] at hc
    exact ⟨rfl, (show (false,0) ∈ preds c.left 0 from of_decide_eq_true hc.1.1.1.1), (show (false,0) ∈ preds c.right 0 from of_decide_eq_true hc.1.1.1.2),hc.1.1.2⟩
  intro n
  obtain ⟨k,t,hk,ht,_⟩ := arbitrary hc hi n
  have hz : (BB6Coverage.Agent50Zipper.zrun p k start).map project = some t := (run_project p k start).trans ht
  cases h : BB6Coverage.Agent50Zipper.zrun p k start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound p m hm k start z h
    rw [start_embed,show k=n+(k-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms go_sound
#print axioms macro_step
#print axioms never
end BB6.Agent19MacroDFA
