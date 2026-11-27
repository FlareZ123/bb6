import SweepPumping
import FastFAR
import WeightedNonhaltLeafAdapter
namespace BB6Coverage.Agent48.H4620
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 4096
set_option maxHeartbeats 0

def ctr : PartialMachine := FAR.fromCodes [7,24,11,21,14,9,12,16,3,11,18,23]
abbrev O (n : Nat) := rep [true] n
abbrev Zs (n : Nat) := rep [false] n

def inc : List Bool → List Bool
  | [] => [true]
  | false::R => true::R
  | true::R => false::inc R

def value : List Bool → Nat
  | [] => 0
  | false::R => 2*value R
  | true::R => 1+2*value R

theorem value_inc (R : List Bool) : value (inc R) = value R + 1 := by
  induction R with
  | nil => rfl
  | cons b R ih => cases b <;> simp [inc,value,ih] <;> omega

theorem appendO (a b : Nat) : O a ++ O b = O (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [Nat.succ_add,rep,List.cons_append,List.nil_append,ih]

theorem appendZ (a b : Nat) : Zs a ++ Zs b = Zs (a+b) := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [Nat.succ_add,rep,List.cons_append,List.nil_append,ih]

def Live (x y : Z0) : Prop := ∃ t : Nat, 0 < t ∧ run0 ctr t x = some y
theorem live_join {x y z : Z0} (h : Live x y) (g : Live y z) : Live x z := by
  obtain ⟨a,ha,hr⟩ := h
  obtain ⟨b,hb,hs⟩ := g
  exact ⟨a+b,by omega,join0 hr hs⟩

theorem d_one (L R : List Bool) :
    run0 ctr 1 ⟨3,false::L,R⟩ = some ⟨3,L,false::R⟩ := rfl

theorem e_one (L R : List Bool) :
    run0 ctr 3 ⟨4,true::L,false::R⟩ = some ⟨4,L,false::true::R⟩ := rfl

theorem f_one (L R : List Bool) :
    run0 ctr 1 ⟨5,true::L,true::R⟩ = some ⟨5,true::true::L,R⟩ := rfl

theorem d_return (j : Nat) (L R : List Bool) :
    run0 ctr (j+1) ⟨3,Zs j ++ true::L,true::R⟩ =
      some ⟨4,L,Zs (j+1) ++ true::R⟩ := by
  have h := sweepL ctr 3 [] [] [false] [false] 1
    (by intro A B; rfl) j (true::L) (true::R)
  have h' : run0 ctr j ⟨3,Zs j ++ true::L,true::R⟩ =
      some ⟨3,true::L,Zs j ++ true::R⟩ := by simpa using h
  have g : run0 ctr 1 ⟨3,true::L,Zs j ++ true::R⟩ =
      some ⟨4,L,Zs (j+1) ++ true::R⟩ := rfl
  exact join0 h' g

theorem carryLoop (bits : List Bool) (j : Nat) (L : List Bool) :
    Live ⟨2,true::(Zs j ++ true::L),bits⟩
         ⟨4,L,Zs (j+2) ++ inc bits⟩ := by
  induction bits generalizing j with
  | nil =>
    have h : run0 ctr 2 ⟨2,true::(Zs j ++ true::L),[]⟩ =
        some ⟨3,Zs (j+1) ++ true::L,[true]⟩ := rfl
    have g := d_return (j+1) L []
    exact ⟨2+(j+1+1),by omega,join0 h g⟩
  | cons b bits ih =>
    cases b with
    | false =>
      have h : run0 ctr 2 ⟨2,true::(Zs j ++ true::L),false::bits⟩ =
          some ⟨3,Zs (j+1) ++ true::L,true::bits⟩ := rfl
      have g := d_return (j+1) L bits
      exact ⟨2+(j+1+1),by omega,join0 h g⟩
    | true =>
      have h : Live ⟨2,true::(Zs j ++ true::L),true::bits⟩
          ⟨2,true::(Zs (j+1) ++ true::L),bits⟩ := ⟨1,by decide,rfl⟩
      have H := live_join h (ih (j+1))
      have eq : Zs (j+1+2) ++ inc bits = Zs (j+2) ++ inc (true::bits) := by
        change Zs (j+1+2) ++ inc bits = Zs (j+2) ++ ([false] ++ inc bits)
        rw [← List.append_assoc,show [false] = Zs 1 by rfl,appendZ]
      rw [eq] at H
      exact H

theorem carry (bits L : List Bool) :
    Live ⟨2,true::true::L,bits⟩ ⟨4,L,false::false::inc bits⟩ :=
  carryLoop bits 0 L

theorem e_sweep (n : Nat) (L R : List Bool) :
    run0 ctr (3*n) ⟨4,O n ++ L,false::R⟩ =
      some ⟨4,L,false::(O n ++ R)⟩ := by
  have h := sweepL ctr 4 [] [false] [true] [true] 3
    (by intro A B; rfl) n L R
  simpa using h

theorem f_sweep (n : Nat) (L R : List Bool) :
    run0 ctr n ⟨5,true::L,O n ++ R⟩ =
      some ⟨5,true::(O n ++ L),R⟩ := by
  have h := sweepR ctr 5 [true] [] [true] [true] 1
    (by intro A B; rfl) n L R
  simpa using h

def cfg (l k : Nat) (bits : List Bool) : Z0 :=
  ⟨0,false::O (2*l+1),O (2*k) ++ false::bits⟩


theorem transfer (l k : Nat) (bits : List Bool) :
    Live (cfg l (k+1) bits) (cfg (l+1) k (inc bits)) := by
  have h : run0 ctr 2 (cfg l (k+1) bits) =
      some ⟨5,true::false::true::O (2*l+1),O (2*k) ++ false::bits⟩ := by
    unfold cfg
    rw [show 2*(k+1)=2*k+1+1 by omega]
    rfl
  have g := f_sweep (2*k) (false::true::O (2*l+1)) (false::bits)
  have t : run0 ctr 3 ⟨5,true::(O (2*k) ++ false::true::O (2*l+1)),false::bits⟩ =
      some ⟨2,true::true::(O (2*k) ++ false::true::O (2*l+1)),bits⟩ := rfl
  have H := join0 (join0 h g) t
  have H' := live_join ⟨2+2*k+3,by omega,H⟩
    (carry bits (O (2*k) ++ false::true::O (2*l+1)))
  have a := e_sweep (2*k) (false::true::O (2*l+1)) (false::inc bits)
  obtain ⟨c,hc,hc'⟩ := H'
  have b : run0 ctr 1 ⟨4,false::true::O (2*l+1),false::(O (2*k) ++ false::inc bits)⟩ =
      some (cfg (l+1) k (inc bits)) := by
    unfold cfg
    rw [show 2*(l+1)+1=2*l+1+1+1 by omega]
    rfl
  exact ⟨c+3*(2*k)+1,by omega,join0 (join0 hc' a) b⟩

theorem turn (l : Nat) (bits : List Bool) :
    Live (cfg l 0 (true::bits)) (cfg 0 (l+1) (inc bits)) := by
  have h : run0 ctr 2 (cfg l 0 (true::bits)) =
      some ⟨2,true::true::(O (2*l+2)),bits⟩ := rfl
  have H := live_join ⟨2,by decide,h⟩ (carry bits (O (2*l+2)))
  obtain ⟨c,hc,hc'⟩ := H
  have a := e_sweep (2*l+2) [] (false::inc bits)
  have a' : run0 ctr (3*(2*l+2)) ⟨4,O (2*l+2),false::false::inc bits⟩ =
      some ⟨4,[],false::(O (2*l+2) ++ false::inc bits)⟩ := by
    simpa only [List.append_nil] using a
  have b : run0 ctr 1 ⟨4,[],false::(O (2*l+2) ++ false::inc bits)⟩ =
      some (cfg 0 (l+1) (inc bits)) := by
    unfold cfg
    rw [show 2*(l+1)=2*l+2 by omega]
    rfl
  exact ⟨c+3*(2*l+2)+1,by omega,join0 (join0 hc' a') b⟩

def incN : Nat → List Bool → List Bool
  | 0,bits => bits
  | k+1,bits => incN k (inc bits)

theorem value_incN (k : Nat) (bits : List Bool) :
    value (incN k bits) = value bits+k := by
  induction k generalizing bits with
  | zero => simp [incN]
  | succ k ih => simp only [incN,ih,value_inc]; omega

theorem drain (l k : Nat) (bits : List Bool) :
    ∃ t, run0 ctr t (cfg l k bits) = some (cfg (l+k) 0 (incN k bits)) := by
  induction k generalizing l bits with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    obtain ⟨a,ha,h⟩ := transfer l k bits
    obtain ⟨b,g⟩ := ih (l+1) (inc bits)
    refine ⟨a+b,?_⟩
    have H := join0 h g
    rw [show l+1+k=l+(k+1) by omega] at H
    exact H

theorem epoch (n : Nat) (bits : List Bool) (hv : value bits+1=n) :
    ∃ t next, 0<t ∧ value next=n ∧
      run0 ctr t (cfg 0 n bits) = some (cfg 0 (n+1) next) := by
  obtain ⟨a,h⟩ := drain 0 n bits
  have v := value_incN n bits
  cases he : incN n bits with
  | nil => rw [he] at v; simp [value] at v; omega
  | cons b tail =>
    rw [he] at v h
    cases b with
    | false => simp only [value] at v; omega
    | true =>
      simp only [value] at v
      obtain ⟨c,hc,g⟩ := turn n tail
      refine ⟨a+c,inc tail,by omega,?_,?_⟩
      · rw [value_inc]; omega
      · exact join0 (by simpa only [Nat.zero_add] using h) g

def Word (n : Nat) := {bits : List Bool // value bits+1=n+2}

noncomputable def nextEpoch (n : Nat) (w : Word n) : Nat × Word (n+1) :=
  let h := epoch (n+2) w.val w.property
  let t := Classical.choose h
  let b := Classical.choose (Classical.choose_spec h)
  let hb := Classical.choose_spec (Classical.choose_spec h)
  (t,⟨b,by
    change value (Classical.choose (Classical.choose_spec h)) + 1 = n+1+2
    have hv := hb.2.1
    omega⟩)

theorem nextEpoch_spec (n : Nat) (w : Word n) :
    0 < (nextEpoch n w).1 ∧
    run0 ctr (nextEpoch n w).1 (cfg 0 (n+2) w.val) =
      some (cfg 0 (n+3) (nextEpoch n w).2.val) := by
  unfold nextEpoch
  dsimp only
  have h := Classical.choose_spec (Classical.choose_spec (epoch (n+2) w.val w.property))
  exact ⟨h.1,h.2.2⟩

noncomputable def words : (n : Nat) → Word n
  | 0 => ⟨[true],rfl⟩
  | n+1 => (nextEpoch n (words n)).2

noncomputable def family (n : Nat) : Z0 := cfg 0 (n+2) (words n).val
noncomputable def cost (n : Nat) : Nat := (nextEpoch n (words n)).1

theorem first : run0 ctr 37 ⟨0,[],[]⟩ = some (family 0) := rfl

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  apply never_of_growth ctr family 37 cost first
  · intro k; exact (nextEpoch_spec k (words k)).1
  · intro k; exact (nextEpoch_spec k (words k)).2
  · exact hm

theorem cover (B : Nat) : Cover (BB6.Agent13BlankDelay.WeightedBound B) ctr := by
  refine .leaf ctr ?_
  intro m hm k d hk hd
  have h := never m hm (k+1)
  rw [hk.2] at h
  simp at h

#print axioms cover
#print axioms transfer
#print axioms turn
#print axioms epoch
#print axioms never

end BB6Coverage.Agent48.H4620
