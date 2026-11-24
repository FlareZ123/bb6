import F418TapeEncoding

namespace BB6.Agent32F418.SourceEvents
open BB6Coverage BB6.Agent32FiniteSource
open Arithmetic EventSystem State TapeEncoding

def DField (k x : Nat) (tail : List Bool) (a n w : Nat) : FiniteCfg :=
  cfg 3 (field k x tail) false (rightWord a n w)

def encode : State → FiniteCfg
  | reg0 N n w => cfg 3 (leftWord 3 N) false (rightWord 0 n w)
  | reg1 n w => cfg 3 (leftWord 3 0) false (rightWord 1 n w)
  | shift2 N a n w => cfg 3 (leftWord 2 N) false (rightWord a n w)
  | shift4 N W => cfg 3 (leftWord 4 N) false (rightWord 0 (2^W) (W+1))
  | shift1 N n w => cfg 3 (leftWord 1 N) false (rightWord 1 n w)

theorem carry_field (k x : Nat) (tail r : List Bool) (hx : x+1<2^k) :
    ∃ j, Run (10*j+10) (cfg 3 (field k x tail) false (true::false::r))
      (cfg 1 ([false,false]++field k (x+1) tail) false r) := by
  obtain ⟨j,l,h1,h2⟩ := field_inc k x tail hx
  refine ⟨j,?_⟩
  rw [h1,h2]
  have hr := carry_to_B j l r
  rw [show 5*j+5=2+(5*j+3) by omega,zeros_add 2 (5*j+3)] at hr
  simpa only [List.append_assoc,show zeros 2=[false,false] by rfl] using hr

/-- Ordinary simultaneous increment, with an arbitrary untouched left suffix. -/
theorem increment (k x : Nat) (tail : List Bool) (a n w : Nat)
    (hx : x+1<2^k) (hn : n+1<2^w) :
    ∃ steps, 0<steps ∧ Run steps (DField k x tail a n w) (DField k (x+1) tail a (n+1) w) := by
  obtain ⟨j,hcarry⟩ := carry_field k x tail ([true,digit a]++pairs w n) hx
  obtain ⟨u,r,h1,h2⟩ := pairs_inc w n hn
  rw [h1] at hcarry
  have hright : Run (4*u+16) (cfg 1 ([false,false]++field k (x+1) tail) false ([true,digit a]++(ones (2*u)++[true,false]++r)))
      (DField k (x+1) tail a (n+1) w) := by
    cases ha : digit a
    · simpa [DField,rightWord,ha,h2,List.append_assoc] using right_inc_zero u (field k (x+1) tail) r
    · simpa [DField,rightWord,ha,h2,List.append_assoc] using right_inc_one u (field k (x+1) tail) r
  refine ⟨10*j+10+(4*u+16),by omega,?_⟩
  have hf := hcarry.trans hright
  simpa [DField,rightWord,h1] using hf

theorem increments (z k x : Nat) (tail : List Bool) (a n w : Nat)
    (hx : x+z<2^k) (hn : n+z<2^w) :
    ∃ steps, z≤steps ∧ Run steps (DField k x tail a n w) (DField k (x+z) tail a (n+z) w) := by
  induction z with
  | zero => exact ⟨0,by omega,by simpa using run_zero (DField k x tail a n w)⟩
  | succ z ih =>
    obtain ⟨s,hs,hr⟩ := ih (by omega) (by omega)
    obtain ⟨t,ht,hr'⟩ := increment k (x+z) tail a (n+z) w (by omega) (by omega)
    exact ⟨s+t,by omega,by simpa [Nat.add_assoc] using hr.trans hr'⟩

theorem standard_zero_source (N n w : Nat) (hs : Safe (reg0 N n w)) :
    ∃ steps, 0<steps ∧ RunEq steps (encode (reg0 N n w))
      (encode (shift2 (N+gap n w) 1 (2^w) (w+1))) := by
  obtain ⟨hw,hN⟩ := hs
  obtain ⟨ht,hlt,_,_⟩ := standard_zero_overflow hw hN
  let t := gap n w
  let z := t-1
  have hpow : n+t=2^w := Nat.add_sub_of_le (Nat.le_of_lt hw.2.2)
  have hwp := hw.1
  have hpos : 0<t := gap_pos hw
  have hx : N+z+1<2^w := by dsimp [z]; omega
  have hn : n+z+1=2^w := by dsimp [z]; omega
  obtain ⟨s,_,h1⟩ := increments z w N (zeros 4) 0 n w (by omega) (by omega)
  obtain ⟨j,h2⟩ := carry_field w (N+z) (zeros 4) ([true,false]++pairs w (n+z)) hx
  rw [pairs_full w (n+z) hn] at h2
  let l := zeros 2 ++ fixedSparse w (N+z+1)
  have hfield : field w (N+z+1) (zeros 4) = false::l := by
    cases w with
    | zero => omega
    | succ w => rw [field_fixed]; rfl
  have h3 := right_overflow_zero w l []
  have h2' : Run (10*j+10) (DField w (N+z) (zeros 4) 0 (n+z) w)
      (cfg 1 ([false,false,false]++l) false ([true,false]++ones (2*w))) := by
    simpa [DField,rightWord,digit,pairs_full w (n+z) hn,hfield,List.append_assoc] using h2
  have h3' : RunEq (4*w+21) (cfg 1 ([false,false,false]++l) false ([true,false]++ones (2*w)))
      (encode (shift2 (N+t) 1 (2^w) (w+1))) := by
    apply runEq_input (c:=cfg 1 ([false,false,false]++l) false ([true,false]++ones (2*w)++[false]))
    · apply cfg_eq
      · exact word_refl _
      · simpa [List.append_assoc,zeros] using word_pad ([true,false]++ones (2*w)) 1
    · apply runEq_output (runEq_of_run (by simpa using h3))
      apply cfg_eq
      · unfold l leftWord
        rw [show N+t=N+z+1 by omega]
        exact word_prefix _ (fixed_sparse_eq _ _ hx)
      · simp [rightWord,digit,pairs_pow,word_refl]
  refine ⟨s+(10*j+10)+(4*w+21),by omega,?_⟩
  apply runEq_input (c:=DField w N (zeros 4) 0 n w)
  · apply cfg_eq
    · cases w with
      | zero => omega
      | succ w => exact field_canonical w N (by omega)
    · exact word_refl _
  · exact runEq_trans (runEq_of_run (h1.trans h2')) h3'

theorem standard_one_source (n w : Nat) (hs : Safe (reg1 n w)) :
    ∃ steps, 0<steps ∧ RunEq steps (encode (reg1 n w))
      (encode (shift4 (gap n w) (w-1))) := by
  obtain ⟨hw,hNP⟩ := hs
  obtain ⟨ht,hlt,_,_,_⟩ := standard_one_overflow hw hNP
  let t := gap n w
  let z := t-1
  have hpow : n+t=2^w := Nat.add_sub_of_le (Nat.le_of_lt hw.2.2)
  have hwp := hw.1
  have hpos : 0<t := gap_pos hw
  have hbound := pow_bound_twice hw.1
  have hx : z+1<2^w := by dsimp [z]; omega
  have hn : n+z+1=2^w := by dsimp [z]; omega
  obtain ⟨s,_,h1⟩ := increments z w 0 (zeros 4) 1 n w (by omega) (by omega)
  obtain ⟨j,h2⟩ := carry_field w z (zeros 4) ([true,true]++pairs w (n+z)) hx
  rw [pairs_full w (n+z) hn] at h2
  let l := field w (z+1) (zeros 4)
  let W := w-1
  have hW : W+1=w := by dsimp [W]; omega
  have h3 := right_overflow_one W l []
  have h2' : Run (10*j+10) (DField w (0+z) (zeros 4) 1 (n+z) w)
      (cfg 1 ([false,false]++l) false ([true,true]++ones (2*w))) := by
    simpa [DField,rightWord,digit,pairs_full w (n+z) hn,l] using h2
  have h3' : RunEq (4*W+11) (cfg 1 ([false,false]++l) false ([true,true]++ones (2*w)))
      (encode (shift4 t W)) := by
    apply runEq_input (c:=cfg 1 ([false,false]++l) false ([true,true]++ones (2*w)++[false]))
    · apply cfg_eq
      · exact word_refl _
      · simpa [List.append_assoc,zeros] using word_pad ([true,true]++ones (2*w)) 1
    · apply runEq_output (runEq_of_run (by simpa [hW] using h3))
      apply cfg_eq
      · unfold l
        rw [show t=z+1 by omega]
        cases w with
        | zero => omega
        | succ w =>
          have h := word_cons false (field_canonical w (z+1) hx)
          exact h
      · simp [rightWord,digit,pairs_pow,word_refl]
  refine ⟨s+(10*j+10)+(4*W+11),by omega,?_⟩
  apply runEq_input (c:=DField w 0 (zeros 4) 1 n w)
  · apply cfg_eq
    · cases w with
      | zero => omega
      | succ w => exact field_canonical w 0 (by omega)
    · exact word_refl _
  · exact runEq_trans (runEq_of_run (h1.trans h2')) h3'


theorem sparse_odd (Q : Nat) : sparseDigits (2*Q+1) = [true,false,false,false,false] ++ sparseDigits Q := by
  simpa [zeros] using sparse_factor 0 Q

theorem left_factor (d j Q : Nat) :
    leftWord d (2^j*(2*Q+1)) = zeros (5*j) ++ leftWord d (2*Q+1) := by
  rw [leftWord,leftWord,sparse_factor,sparse_odd]
  simp only [← List.append_assoc, ← zeros_add]
  rw [Nat.add_comm d (5*j)]

theorem shift12_prefix (d N j Q a n w : Nat) (hf : N=2^j*(2*Q+1))
    (ht : N<gap n w) (_hw : RightWidth n w) :
    ∃ s, Run s (cfg 3 (leftWord d N) false (rightWord a n w))
      (cfg 3 (carryWord j ++ leftWord d (2*Q+1)) false (rightWord a (n+(2^j-1)) w)) := by
  have hb := (shifted12_budget hf ht).1
  have hpos := Nat.two_pow_pos j
  obtain ⟨s,_,hr⟩ := increments (2^j-1) j 0 (shiftedTail j (leftWord d (2*Q+1))) a n w
    (by omega) (by unfold gap at hb; omega)
  refine ⟨s,?_⟩
  simpa [DField,shifted_field_zero,shifted_field_full j (2^j-1) _ (by omega),hf,left_factor] using hr

theorem shift2_source (N a n w : Nat) (hs : Safe (shift2 N a n w)) :
    ∃ steps s', 0<steps ∧ advance (shift2 N a n w) = some s' ∧
      RunEq steps (encode (shift2 N a n w)) (encode s') := by
  obtain ⟨hN,ha,hw,_,ht⟩ := hs
  have hf := splitOdd_spec N hN
  rcases hj : splitOdd N with ⟨j,Q⟩
  rw [hj] at hf
  dsimp at hf
  obtain ⟨s,hr⟩ := shift12_prefix 2 N j Q a n w hf ht hw
  let m := n+(2^j-1)
  let e := (5*j+1)/2
  let n' := resetRight a m e
  let w' := w+e+2
  by_cases hp : j%2=0
  · have he : e=5*(j/2) := by dsimp [e]; omega
    have hj' : 2*(j/2)=j := by omega
    have hreset := reset2_even (j/2) (leftWord 3 Q) (pairs w m) (digit a)
    rw [hj',← he] at hreset
    have hleft : leftWord 2 (2*Q+1) = [false,false,true,false]++leftWord 3 Q := by
      rw [leftWord,sparse_odd,leftWord]; rfl
    have hfinal : Run (30*(j/2)+14) (cfg 3 (carryWord j ++ leftWord 2 (2*Q+1)) false (rightWord a m w))
        (encode (reg0 Q n' w')) := by
      simpa [encode,rightWord,hleft,n',w',pairs_reset a m e w ha,digit,List.append_assoc] using hreset
    refine ⟨s+(30*(j/2)+14),reg0 Q n' w',by omega,?_,runEq_of_run (hr.trans hfinal)⟩
    simp [advance,hj,hp,n',w',m,e]
  · have he : e=5*(j/2)+3 := by dsimp [e]; omega
    have hj' : 2*(j/2)+1=j := by omega
    have hreset := reset2_odd (j/2) (leftWord 2 Q) (pairs w m) (digit a)
    rw [hj',← he] at hreset
    have hleft : leftWord 2 (2*Q+1) = [false,false,true,false,false]++leftWord 2 Q := by
      rw [leftWord,sparse_odd,leftWord]; rfl
    have hfinal : Run (30*(j/2)+36) (cfg 3 (carryWord j ++ leftWord 2 (2*Q+1)) false (rightWord a m w))
        (encode (shift2 Q 1 n' w')) := by
      simpa [encode,rightWord,hleft,n',w',pairs_reset a m e w ha,digit,List.append_assoc] using hreset
    refine ⟨s+(30*(j/2)+36),shift2OrReg1 Q n' w',by omega,?_,?_⟩
    · simp [advance,hj,hp,n',w',m,e]
    · apply runEq_output (runEq_of_run (hr.trans hfinal))
      unfold shift2OrReg1
      split
      · rename_i hQ
        subst Q
        apply cfg_eq
        · simp only [leftWord,sparse_zero,List.append_nil]
          exact word_trans (word_zero 2) (word_symm (word_zero 3))
        · exact word_refl _
      · exact tape_refl _


theorem shift4_prefix (N j Q W : Nat) (hf : N=2^j*(2*Q+1)) (ht : N<2^W) :
    ∃ s, Run s (encode (shift4 N W))
      (cfg 3 (carryWord j ++ [false,false,false,true,true,false,false,false,false] ++ sparseDigits Q)
        false (rightWord 0 (2^W+(2^(j+1)-1)) (W+1))) := by
  let tail := [true,false,false,false,false]++sparseDigits Q
  let z := 2^(j+1)-1
  have hp := Nat.two_pow_pos (j+1)
  have hb := (shifted4_budget hf ht).1
  obtain ⟨s,_,hr⟩ := increments z (j+1) 0 tail 0 (2^W) (W+1)
    (by omega) (by rw [Nat.pow_succ]; omega)
  have hleft : leftWord 4 N = field (j+1) 0 tail := by
    rw [hf,leftWord,sparse_factor,field_zero]
    rw [show 5*j+4=4+5*j by omega,zeros_add 4 (5*j)]
    simp [tail,List.append_assoc]
  refine ⟨s,?_⟩
  unfold DField at hr
  rw [Nat.zero_add,← hleft,field_full j z tail (by omega)] at hr
  simpa [encode,tail,z,List.append_assoc] using hr

theorem shift4_source (N W : Nat) (hs : Safe (shift4 N W)) :
    ∃ steps s', 0<steps ∧ advance (shift4 N W) = some s' ∧
      RunEq steps (encode (shift4 N W)) (encode s') := by
  obtain ⟨hN,ht,_⟩ := hs
  have hf := splitOdd_spec N hN
  rcases hj : splitOdd N with ⟨j,Q⟩
  rw [hj] at hf
  dsimp at hf
  obtain ⟨s,hr⟩ := shift4_prefix N j Q W hf ht
  let m := 2^W+(2^(j+1)-1)
  let e := (5*j+4)/2
  let n' := resetRight 0 m e
  let w' := W+1+e+2
  by_cases hp : j%2=0
  · have he : e=5*(j/2)+2 := by dsimp [e]; omega
    have hj' : 2*(j/2)=j := by omega
    have hreset := reset4_even (j/2) (leftWord 1 Q) (pairs (W+1) m) false
    rw [hj',← he] at hreset
    have hfinal : Run (30*(j/2)+30)
        (cfg 3 (carryWord j ++ [false,false,false,true,true,false,false,false,false] ++ sparseDigits Q)
          false (rightWord 0 m (W+1))) (encode (shift1 Q n' w')) := by
      simpa [encode,rightWord,leftWord,zeros,n',w',pairs_reset 0 m e (W+1) (by decide),digit,List.append_assoc] using hreset
    refine ⟨s+(30*(j/2)+30),shift1 Q n' w',by omega,?_,runEq_of_run (hr.trans hfinal)⟩
    simp [advance,hj,hp,n',w',m,e]
  · have he : e=5*(j/2)+4 := by dsimp [e]; omega
    have hj' : 2*(j/2)+1=j := by omega
    have hreset := reset4_odd (j/2) (leftWord 2 Q) (pairs (W+1) m) false
    rw [hj',← he] at hreset
    have hfinal : Run (30*(j/2)+38)
        (cfg 3 (carryWord j ++ [false,false,false,true,true,false,false,false,false] ++ sparseDigits Q)
          false (rightWord 0 m (W+1))) (encode (shift2 Q 0 n' w')) := by
      simpa [encode,rightWord,leftWord,zeros,n',w',pairs_reset 0 m e (W+1) (by decide),digit,List.append_assoc] using hreset
    refine ⟨s+(30*(j/2)+38),shift2 Q 0 n' w',by omega,?_,runEq_of_run (hr.trans hfinal)⟩
    simp [advance,hj,hp,n',w',m,e]

theorem shift1_source (N n w : Nat) (hs : Safe (shift1 N n w)) :
    ∃ steps c, 0<steps ∧ Run steps (encode (shift1 N n w)) c ∧ query c = (5,true) ∧ step machine c = none := by
  obtain ⟨hN,hw,_,ht⟩ := hs
  have hf := splitOdd_spec N hN
  rcases hj : splitOdd N with ⟨j,Q⟩
  rw [hj] at hf
  dsimp at hf
  obtain ⟨s,hr⟩ := shift12_prefix 1 N j Q 1 n w hf ht hw
  have hleft : leftWord 1 (2*Q+1) = [false,true]++(zeros 4++sparseDigits Q) := by
    rw [leftWord,sparse_odd]; rfl
  let l := zeros 4++sparseDigits Q
  let r := rightWord 1 (n+(2^j-1)) w
  have hhalt := offset1_hazard j l r
  have hr' : Run s (encode (shift1 N n w)) (cfg 3 (carryWord j++[false,true]++l) false r) := by
    simpa [encode,hleft,l,r] using hr
  exact ⟨s+(5*j+2),_,by omega,hr'.trans hhalt,rfl,rfl⟩

theorem advance_source {s s' : State} (hs : Safe s) (ha : advance s = some s') :
    ∃ steps, 0<steps ∧ RunEq steps (encode s) (encode s') := by
  cases s with
  | reg0 N n w =>
    simp only [advance,Option.some.injEq] at ha
    subst s'
    exact standard_zero_source N n w hs
  | reg1 n w =>
    simp only [advance,Option.some.injEq] at ha
    subst s'
    exact standard_one_source n w hs
  | shift2 N a n w =>
    obtain ⟨steps,t,hp,he,hr⟩ := shift2_source N a n w hs
    rw [ha,Option.some.injEq] at he
    subst t
    exact ⟨steps,hp,hr⟩
  | shift4 N W =>
    obtain ⟨steps,t,hp,he,hr⟩ := shift4_source N W hs
    rw [ha,Option.some.injEq] at he
    subst t
    exact ⟨steps,hp,hr⟩
  | shift1 => simp [advance] at ha

theorem terminal_source {s : State} (hs : Safe s) (ha : advance s = none) :
    ∃ steps c, 0<steps ∧ Run steps (encode s) c ∧ query c = (5,true) ∧ step machine c = none := by
  obtain ⟨N,n,w,rfl⟩ := (advance_none_iff s).mp ha
  exact shift1_source N n w hs

#print axioms advance_source
#print axioms terminal_source
end BB6.Agent32F418.SourceEvents
