import SweepPumping
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4LF296
open BB6Coverage Agent31Pump

-- 1RB0LF_1RC0RE_0RD---_1LD1RE_1RD0RA_1LA0LF

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def P : List Bool := [false,true]
def O : List Bool := [true,true]
def Z : List Bool := [false,false]
def W : List Bool := [true,false]
def H (m : Nat) : List Bool := P ++ rep O m ++ P
def Q (m : Nat) : List Bool := P ++ rep Z m ++ P
def B (S R : List Bool) : Z0 := ⟨1,O ++ S,R⟩
def C (S R : List Bool) : Z0 := ⟨2,false::O ++ S,R⟩
def F (S R : List Bool) : Z0 := ⟨5,S,R⟩
def pad (R : List Bool) : List Bool := false :: R.tail

def Reach (a b : Z0) : Prop := ∃ t, run0 table t a = some b
def Live (a b : Z0) : Prop := ∃ t, 0 < t ∧ run0 table t a = some b

theorem Reach.ofRun {a b : Z0} {t : Nat} (h : run0 table t a = some b) : Reach a b := ⟨t,h⟩
theorem Live.ofRun {a b : Z0} {t : Nat} (ht : 0 < t) (h : run0 table t a = some b) : Live a b := ⟨t,ht,h⟩
theorem Reach.trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨_,join0 ht hu⟩
theorem Live.trans {a b c : Z0} (h : Live a b) (g : Reach b c) : Live a c := by
  obtain ⟨t,ht,hh⟩ := h
  obtain ⟨u,hu⟩ := g
  exact ⟨_,by omega,join0 hh hu⟩
theorem Live.reach {a b : Z0} (h : Live a b) : Reach a b := by
  obtain ⟨t,_,hr⟩ := h
  exact ⟨t,hr⟩

theorem fH (m : Nat) (L R : List Bool) :
    run0 table (2*m+4) (F (H m ++ L) R) = some (F L (Q m ++ R)) := by
  have h1 : run0 table 2 (F (H m ++ L) R) = some (F (rep O m ++ P ++ L) (P ++ R)) := by
    simp only [H,List.append_assoc]
    rfl
  have h2 : run0 table (2*m) (F (rep O m ++ P ++ L) (P ++ R)) =
      some (F (P ++ L) (rep Z m ++ P ++ R)) := by
    simpa only [F,List.nil_append,List.append_assoc] using sweepL table 5 [] [] O Z 2
      (by intro L R; rfl) m (P ++ L) (P ++ R)
  have h3 : run0 table 2 (F (P ++ L) (rep Z m ++ P ++ R)) = some (F L (Q m ++ R)) := by
    simp only [Q,List.append_assoc]
    rfl
  have h := join0 (join0 h1 h2) h3
  rw [show 2+2*m+2=2*m+4 by omega] at h
  exact h

theorem fRep (m n : Nat) (L R : List Bool) : Reach (F (rep (H m) n ++ L) R) (F L (rep (Q m) n ++ R)) := by
  exact Reach.ofRun (by
    simpa only [F,List.nil_append,List.append_assoc] using sweepL table 5 [] [] (H m) (Q m) (2*m+4)
      (by intro L R; exact fH m L R) n L R)

theorem fEnd (R : List Bool) : Reach (F [] R) (B [] R) := Reach.ofRun (show run0 table 2 (F [] R) = some (B [] R) by rfl)

theorem rotateP (m : Nat) (T : List Bool) : rep P m ++ Z ++ T = false::(rep W m ++ false::T) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rep,List.append_assoc]
    simp only [List.append_assoc] at ih
    rw [ih]
    rfl

theorem eSweep (m : Nat) (L R : List Bool) :
    run0 table (2*m) ⟨4,false::L,rep W m ++ R⟩ = some ⟨4,false::(rep O m ++ L),R⟩ := by
  simpa only [List.nil_append,List.cons_append,List.nil_append] using sweepR table 4 [false] [] W O 2
    (by intro L R; rfl) m L R

theorem eBreak (L T : List Bool) :
    run0 table 4 ⟨4,false::L,false::T⟩ = some ⟨0,T.headD false::false::true::L,T.tail⟩ := by rfl

theorem bScan (m : Nat) (S T : List Bool) :
    run0 table (2*m+5) (B S (rep P m ++ Z ++ T)) = some ⟨0,T.headD false::(H m ++ S),T.tail⟩ := by
  rw [rotateP]
  have h1 : run0 table 1 (B S (false::(rep W m ++ false::T))) = some ⟨4,[false,false,true]++S,rep W m ++ false::T⟩ := by rfl
  have h2 := eSweep m (false::true::S) (false::T)
  have h3 := eBreak (rep O m ++ false::true::S) T
  have h := join0 (join0 h1 h2) h3
  rw [show 1+2*m+4=2*m+5 by omega] at h
  simpa only [H,P,List.append_assoc,List.cons_append,List.nil_append] using h

theorem bStore (m : Nat) (S T : List Bool) :
    run0 table (2*m+6) (B S (rep P m ++ Z ++ P ++ T)) = some (B (H m ++ S) T) := by
  have h1 := bScan m S (P ++ T)
  have h2 : run0 table 1 ⟨0,(P ++ T).headD false::(H m ++ S),(P ++ T).tail⟩ = some (B (H m ++ S) T) := by rfl
  simpa only [List.append_assoc] using join0 h1 h2

theorem bToC (m : Nat) (S T : List Bool) : Live (B S (rep P m ++ Z ++ [false,false,false] ++ T)) (C (H m ++ S) T) := by
  have h1 := bScan m S ([false,false,false] ++ T)
  have h2 : run0 table 2 ⟨0,([false,false,false]++T).headD false::(H m ++ S),([false,false,false]++T).tail⟩ = some (C (H m ++ S) T) := by rfl
  exact Live.ofRun (by omega : 0 < (2*m+5)+2) (by simpa only [List.append_assoc] using join0 h1 h2)

theorem bBlank (S : List Bool) : Live (B S Z) (C (H 0 ++ S) []) := by
  exact Live.ofRun (by omega : 0 < 7) (by rfl)

theorem bReset (m : Nat) (S T : List Bool) : Live (B S (rep P m ++ Z ++ true::T)) (F (H m ++ S) (false::T)) := by
  have h1 := bScan m S (true::T)
  have h2 : run0 table 1 ⟨0,true::(H m ++ S),T⟩ = some (F (H m ++ S) (false::T)) := by rfl
  exact Live.ofRun (by omega : 0 < (2*m+5)+1) (by simpa only [List.append_assoc] using join0 h1 h2)

theorem restore (b : Nat) (R : List Bool) : Reach (B [] (rep (Q 1) b ++ R)) (B (rep (H 1) b) R) := by
  exact Reach.ofRun (by
    simpa only [B,List.nil_append,List.append_nil,List.append_assoc] using sweepR table 1 O [] (Q 1) (H 1) 8
      (by intro L R; rfl) b [] R)

theorem cZero (S R : List Bool) (hR : R.headD false = false) : Live (C S R) (F S (Z ++ [true] ++ pad R)) := by
  exact Live.ofRun (by omega : 0 < 9) (by
    cases R with
    | nil => rfl
    | cons x xs => cases x <;> first | rfl | simp at hR)

theorem cRight (m : Nat) (S T : List Bool) : Live (C S (true::(rep P m ++ Z ++ true::T)))
    (F S (Z ++ W ++ rep Z m ++ P ++ false::T)) := by
  rw [rotateP]
  have h1 : run0 table 2 (C S (true::false::(rep W m ++ false::true::T))) = some ⟨4,[false,true,false,true,true]++S,rep W m ++ false::true::T⟩ := by rfl
  have h2 := eSweep m (true::false::true::true::S) (false::true::T)
  have h3 := eBreak (rep O m ++ true::false::true::true::S) (true::T)
  have h4 : run0 table 3 ⟨0,true::false::true::(rep O m ++ true::false::true::true::S),T⟩ =
      some (F (rep O m ++ true::false::true::true::S) (P ++ false::T)) := by rfl
  have h5 : run0 table (2*m) (F (rep O m ++ true::false::true::true::S) (P ++ false::T)) =
      some (F (true::false::true::true::S) (rep Z m ++ P ++ false::T)) := by
    simpa only [F,List.nil_append,List.append_assoc] using sweepL table 5 [] [] O Z 2
      (by intro L R; rfl) m (true::false::true::true::S) (P ++ false::T)
  have h6 : run0 table 4 (F (true::false::true::true::S) (rep Z m ++ P ++ false::T)) =
      some (F S (Z ++ W ++ rep Z m ++ P ++ false::T)) := by rfl
  exact Live.ofRun (by omega : 0 < 2+2*m+4+3+2*m+4) (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6)

def S1 (b : Nat) : List Bool := rep (H 1) b
def S (j b : Nat) : List Bool := rep (H 0) j ++ H 2 ++ S1 b
def ctrl (k : Nat) (T : List Bool) : List Bool := rep P 2 ++ rep Z (2*k+1) ++ P ++ T
def tailCtrl (k : Nat) (T : List Bool) : List Bool := rep Z (2*k+1) ++ P ++ T

theorem q0Rep (j : Nat) : rep (Q 0) j = rep P (2*j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)=2*j+2 by omega]
    change Q 0 ++ rep (Q 0) j = rep P (2*j+2)
    rw [ih]
    rfl

theorem unload1 (b : Nat) (R : List Bool) : Reach (F (S1 b) R) (B (S1 b) R) := by
  have h1 : Reach (F (S1 b) R) (F [] (rep (Q 1) b ++ R)) := by
    simpa only [S1,List.append_nil] using fRep 1 b [] R
  exact h1.trans ((fEnd _).trans (restore b R))

theorem unloadStorage (j b : Nat) (R : List Bool) : Reach (F (S j b) R) (B (S1 b) (Q 2 ++ rep (Q 0) j ++ R)) := by
  have h1 : Reach (F (S j b) R) (F (H 2 ++ S1 b) (rep (Q 0) j ++ R)) := by
    simpa only [S,List.append_assoc] using fRep 0 j (H 2 ++ S1 b) R
  have h2 := Reach.ofRun (fH 2 (S1 b) (rep (Q 0) j ++ R))
  have h3 : Reach (F (S1 b) (Q 2 ++ (rep (Q 0) j ++ R))) (B (S1 b) (Q 2 ++ (rep (Q 0) j ++ R))) := unload1 b _
  simpa only [List.append_assoc] using h1.trans (h2.trans h3)

theorem kick (j b : Nat) (R : List Bool) (hR : R.headD false = false) :
    Live (C (S j b) R) (B (S1 (b+1)) (ctrl j (false::pad R))) := by
  have h1 := cZero (S j b) R hR
  have h2 := unloadStorage j b (Z ++ [true] ++ pad R)
  have h3a := bToC 1 (S1 b) (true::(rep (Q 0) j ++ (Z ++ [true] ++ pad R)))
  have h3 : Live (B (S1 b) (Q 2 ++ rep (Q 0) j ++ (Z ++ [true] ++ pad R)))
      (C (S1 (b+1)) (true::(rep (Q 0) j ++ (Z ++ [true] ++ pad R)))) := by
    simpa only [Q,rep,S1,P,Z,H,List.cons_append,List.nil_append,List.append_assoc] using h3a
  have h4 := cRight (2*j) (S1 (b+1)) (pad R)
  rw [q0Rep] at h3
  have h34 : Reach (B (S1 b) (Q 2 ++ rep (Q 0) j ++ (Z ++ [true] ++ pad R)))
      (F (S1 (b+1)) (Z ++ W ++ rep Z (2*j) ++ P ++ false::pad R)) := by
    rw [q0Rep]
    exact h3.reach.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using h4.reach)
  have h5 := unload1 (b+1) (Z ++ W ++ rep Z (2*j) ++ P ++ false::pad R)
  have h6 : Live (B (S1 (b+1)) (Z ++ W ++ rep Z (2*j) ++ P ++ false::pad R))
      (F (H 0 ++ S1 (b+1)) (false::false::(rep Z (2*j) ++ P ++ false::pad R))) := by
    simpa only [rep,W,List.nil_append,List.cons_append,List.append_assoc] using
      bReset 0 (S1 (b+1)) (false::(rep Z (2*j) ++ P ++ false::pad R))
  have h7 := Reach.ofRun (fH 0 (S1 (b+1)) (false::false::(rep Z (2*j) ++ P ++ false::pad R)))
  have h8 := unload1 (b+1) (Q 0 ++ false::false::(rep Z (2*j) ++ P ++ false::pad R))
  have h := h1.trans (h2.trans (h34.trans (h5.trans (h6.reach.trans (h7.trans h8)))))
  simpa only [ctrl,rep,Q,Z,List.cons_append,List.append_assoc,List.nil_append] using h

theorem tailHead (k : Nat) (T : List Bool) : (false::(rep Z (2*k) ++ P ++ T)).headD false = false := rfl

theorem tailPad (k : Nat) (T : List Bool) : false::pad (false::(rep Z (2*k) ++ P ++ T)) = tailCtrl k T := by
  simp only [pad,tailCtrl,rep,List.tail_cons,List.append_assoc]
  rfl

theorem splitWord (k : Nat) (T : List Bool) :
    tailCtrl (k+1) T = Z ++ [false,false,false] ++ false::(rep Z (2*k) ++ P ++ T) := by
  unfold tailCtrl
  rw [show 2*(k+1)+1=2*k+3 by omega]
  simp only [rep,List.append_assoc,Z,List.cons_append,List.nil_append]

theorem storeBase (b : Nat) (T : List Bool) : Live (B (S1 b) (ctrl 0 T)) (B (S 0 b) T) := by
  exact Live.ofRun (by omega : 0 < 10) (by
    simpa only [ctrl,S,rep,List.nil_append,List.append_assoc] using bStore 2 (S1 b) T)

theorem climb (n : Nat)
    (lower : ∀ k, k < n → ∀ b T, ∃ b', Live (B (S1 b) (ctrl k T)) (B (S k b') T))
    (d j b : Nat) (T : List Bool) (hn : j+d+1 = n) :
    ∃ b', Live (B (S j b) (tailCtrl d T)) (B (S n b') T) := by
  induction d generalizing j b with
  | zero =>
    have h : Live (B (S j b) (tailCtrl 0 T)) (B (S (j+1) b) T) := by
      exact Live.ofRun (by omega : 0 < 6) (by
        simpa only [tailCtrl,S,rep,List.nil_append,List.append_assoc] using bStore 0 (S j b) T)
    have he : j+1 = n := by omega
    rw [he] at h
    exact ⟨b,h⟩
  | succ d ih =>
    let R := false::(rep Z (2*d) ++ P ++ T)
    have h1 : Live (B (S j b) (tailCtrl (d+1) T)) (C (S (j+1) b) R) := by
      rw [splitWord]
      simpa only [R,S,rep,List.nil_append,List.append_assoc] using bToC 0 (S j b) R
    have h2 := kick (j+1) b R rfl
    rw [show false::pad R = tailCtrl d T from tailPad d T] at h2
    obtain ⟨b',h3⟩ := lower (j+1) (by omega) (b+1) (tailCtrl d T)
    obtain ⟨b'',h4⟩ := ih (j+1) b' (by omega)
    exact ⟨b'',h1.trans (h2.reach.trans (h3.reach.trans h4.reach))⟩

theorem resolve (k : Nat) : ∀ b T, ∃ b', Live (B (S1 b) (ctrl k T)) (B (S k b') T) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b T
    cases k with
    | zero => exact ⟨b,storeBase b T⟩
    | succ k =>
      let R := false::(rep Z (2*k) ++ P ++ T)
      have h1 : Live (B (S1 b) (ctrl (k+1) T)) (C (S 0 b) R) := by
        unfold ctrl
        have he : rep Z (2*(k+1)+1) ++ P ++ T = tailCtrl (k+1) T := rfl
        rw [List.append_assoc (rep P 2),List.append_assoc (rep P 2),he,splitWord]
        simpa only [R,S,rep,List.nil_append,List.append_assoc] using bToC 2 (S1 b) R
      have h2 := kick 0 b R rfl
      rw [show false::pad R = tailCtrl k T from tailPad k T] at h2
      have h3 := storeBase (b+1) (tailCtrl k T)
      obtain ⟨b',h4⟩ := climb (k+1) ih k 0 (b+1) T (by omega)
      exact ⟨b',h1.trans (h2.reach.trans (h3.reach.trans h4.reach))⟩

theorem grow (k b : Nat) : ∃ b', Live (C (S k b) []) (C (S (k+1) b') []) := by
  have h1 := kick k b [] rfl
  change Live (C (S k b) []) (B (S1 (b+1)) (ctrl k Z)) at h1
  obtain ⟨b',h2⟩ := resolve k (b+1) Z
  have h3 : Live (B (S k b') Z) (C (S (k+1) b') []) := by
    simpa only [S,rep,List.append_assoc] using bBlank (S k b')
  exact ⟨b',h1.trans (h2.reach.trans h3.reach)⟩

theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z := by
  have aux : ∀ k : Nat, ∃ t b, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (C (S k b) []) := by
    intro k
    induction k with
    | zero => exact ⟨36,0,by omega,by rfl⟩
    | succ k ih =>
      obtain ⟨t,b,ht,h1⟩ := ih
      obtain ⟨b',u,hu,h2⟩ := grow k b
      exact ⟨_,b',by omega,join0 h1 h2⟩
  obtain ⟨t,b,ht,h⟩ := aux n
  exact ⟨t,C (S n b) [],ht,h⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm

#print axioms arbitrary
#print axioms never
end BB6Coverage.Agent4LF296
