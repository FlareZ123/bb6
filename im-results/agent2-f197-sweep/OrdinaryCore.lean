import SelfBase
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (b pre_append zeros_blank)
open PrefixCheck

def bits (s : String) : Word := s.toList.map (· == '1')
def encLetter (c : Char) : Word :=
  if c == 'A' then bits "10" else if c == 'T' then bits "1100" else if c == 'J' then bits "100" else
  if c == 'U' then bits "11100" else if c == 'C' then bits "110" else []
def enc (s : String) : Word := s.toList.flatMap encLetter
def M := enc "JTAATAAA"
def K := enc "TATAAT"
def R := enc "AATAAAT"
def HB := bits "111100011111000110"
def XC := bits "10110"
def E0 := enc "AAATATATATAAAT"
def E1 := enc "AAATATAATAATATAAAT"
def W0 := enc "AAATAATATAAATTAAAT"
def W1 := enc "AAATATATAAATTAAAT"
def RB0 := bits "1111000111100011100011100010111100011111000111110001111100011"
def RB1 := bits "11110001111000111100011111000111100010111100011"

theorem descend_one (n : Nat) (l : Tape) (hl : l 0 = true) :
    ReachPos (state (n+2) M l) (state n M (pre K l)) := by
  cases n with
  | zero =>
    have h := direct_lift M (M++K) [] 2 0 2 120 388 l hl (by decide) (by decide) (by decide)
    rw [List.append_nil,List.append_nil] at h
    simpa only [state,pre_append] using h
  | succ n =>
    have h := core_lift M (M++K) [] 2 0 0 n 95 321 l hl (by decide) (by decide) (by decide) (by decide)
    rw [List.append_nil,List.append_nil] at h
    rw [show 2+n+1 = n+1+2 by omega,show 0+n+1+0 = n+1 by omega] at h
    change ReachPos (state (n+1+2) M l) (state (n+1) M (pre K l))
    simpa only [state,pre_append] using h

theorem descend_many (q p : Nat) (l : Tape) (hl : l 0 = true) :
    Reach (state (2*q+p) M l) (state p M (rep K q l)) := by
  induction q generalizing l with
  | zero => simp [rep]; exact reach_refl _
  | succ q ih =>
    rw [show 2*(q+1)+p = (2*q+p)+2 by omega]
    obtain ⟨t,_,h1⟩ := descend_one (2*q+p) l hl
    have h2 := ih (pre K l) (by rfl)
    rw [rep_comm] at h2
    exact reach_trans ⟨t,h1⟩ h2

theorem scanK_many (m : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    Reach (b (rep K m l) r) (b l (rep HB m r)) := by
  induction m generalizing r with
  | zero => exact reach_refl _
  | succ m ih =>
    have h1 := Agent2EpochMarker.scanK (rep K m l) r (rep_first K (by decide) m l hl) hr
    have h2 := ih (pre HB r) (by rfl)
    rw [rep_comm] at h2
    exact reach_trans ⟨82,h1⟩ h2

theorem epoch_enter0 (m : Nat) (l : Tape) (hl : l 0 = true) :
    ReachPos (state (2*(m+1)) M l) (b l (rep HB m Agent2EpochMarker.r0)) := by
  have h1 := descend_many (m+1) 0 l hl
  simp only [Nat.add_zero] at h1
  have h2 := Agent2EpochMarker.enter0 (rep K m l) (rep_first K (by decide) m l hl)
  have h3 := scanK_many m l Agent2EpochMarker.r0 hl (by rfl)
  exact reach_trans_pos h1 (reach_pos_trans ⟨1863,by decide,h2⟩ h3)

theorem epoch_enter1 (m : Nat) (l : Tape) (hl : l 0 = true) :
    ReachPos (state (2*m+1) M l) (b l (rep HB m Agent2EpochMarker.r1)) := by
  have h1 := descend_many m 1 l hl
  have h2 := Agent2EpochMarker.enter1 (rep K m l) (rep_first K (by decide) m l hl)
  have h3 := scanK_many m l Agent2EpochMarker.r1 hl (by rfl)
  exact reach_trans_pos h1 (reach_pos_trans ⟨887,by decide,h2⟩ h3)

structure Terminal where
  src : Word
  dst : Word
  steps : Nat
  cost : Nat
  deriving Repr

def terminalOK (t : Terminal) : Bool :=
  exec t.steps (guard t.src []) == some (t.cost,guard (J++t.dst) XC)

theorem terminal_sound (t : Terminal) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true)
    (h : terminalOK t = true) : Reach (b (pre t.src l) r) (b (pre J (pre t.dst l)) (pre XC r)) := by
  simp only [terminalOK,beq_iff_eq] at h
  have h1 := guard_sound t.src [] (J++t.dst) XC t.steps t.cost l r hl hr h
  rw [pre_append] at h1
  exact ⟨t.cost,h1⟩

theorem decodeH (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 68 (b (pre J l) (pre XC (pre HB r))) = some (b (pre J (pre R l)) (pre XC r)) := by
  exact guard_sound J (XC++HB) (J++R) XC 17 68 l r hl hr (by decide)

theorem decodeH_many (m : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    Reach (b (pre J l) (pre XC (rep HB m r))) (b (pre J (rep R m l)) (pre XC r)) := by
  induction m generalizing l with
  | zero => exact reach_refl _
  | succ m ih =>
    have h1 := decodeH l (rep HB m r) hl (rep_first HB (by decide) m r hr)
    have h2 := ih (pre R l) (by rfl)
    rw [rep_comm] at h2
    exact reach_trans ⟨68,h1⟩ h2

theorem exitOrd0 (l : Tape) (hl : l 0 = true) :
    Reach (b (pre J l) (pre XC Agent2EpochMarker.r0)) (state 4 E0 l) := by
  have h := guardBlank_sound J ((XC++RB0)++[false,false]) (flat P 4++E0) [true] 97 375 l hl (by decide)
  rw [pre_append (XC++RB0),show pre [false,false] blank = blank by exact zeros_blank 2,pre_append XC RB0,pre_append (flat P 4) E0,flat_pre] at h
  exact ⟨375,h⟩

theorem exitOrd1 (l : Tape) (hl : l 0 = true) :
    Reach (b (pre J l) (pre XC Agent2EpochMarker.r1)) (state 1 E1 l) := by
  have h := guardBlank_sound J ((XC++RB1)++[false,false]) (flat P 1++E1) [true] 73 283 l hl (by decide)
  rw [pre_append (XC++RB1),show pre [false,false] blank = blank by exact zeros_blank 2,pre_append XC RB1,pre_append (flat P 1) E1,flat_pre] at h
  exact ⟨283,h⟩

theorem ordinary0 (m : Nat) (t : Terminal) (l : Tape) (hl : l 0 = true)
    (hs : okHead t.src = true) (hd : okHead t.dst = true) (hc : terminalOK t = true) :
    ReachPos (state (2*(m+1)) M (pre t.src l)) (state 4 E0 (rep R m (pre t.dst l))) := by
  have h1 := epoch_enter0 m (pre t.src l) (pre_first t.src l hs hl)
  have h2 := terminal_sound t l (rep HB m Agent2EpochMarker.r0) hl (rep_first HB (by decide) m _ (by rfl)) hc
  have h3 := decodeH_many m (pre t.dst l) Agent2EpochMarker.r0 (pre_first t.dst l hd hl) (by rfl)
  have h4 := exitOrd0 (rep R m (pre t.dst l)) (rep_first R (by decide) m _ (pre_first t.dst l hd hl))
  exact reach_pos_trans h1 (reach_trans h2 (reach_trans h3 h4))

theorem ordinary1 (m : Nat) (t : Terminal) (l : Tape) (hl : l 0 = true)
    (hs : okHead t.src = true) (hd : okHead t.dst = true) (hc : terminalOK t = true) :
    ReachPos (state (2*m+1) M (pre t.src l)) (state 1 E1 (rep R m (pre t.dst l))) := by
  have h1 := epoch_enter1 m (pre t.src l) (pre_first t.src l hs hl)
  have h2 := terminal_sound t l (rep HB m Agent2EpochMarker.r1) hl (rep_first HB (by decide) m _ (by rfl)) hc
  have h3 := decodeH_many m (pre t.dst l) Agent2EpochMarker.r1 (pre_first t.dst l hd hl) (by rfl)
  have h4 := exitOrd1 (rep R m (pre t.dst l)) (rep_first R (by decide) m _ (pre_first t.dst l hd hl))
  exact reach_pos_trans h1 (reach_trans h2 (reach_trans h3 h4))

#print axioms ordinary0
#print axioms ordinary1
end F197.Agent2Self
