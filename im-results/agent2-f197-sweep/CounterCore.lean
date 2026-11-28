import EpochMarkerBulk
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.Agent2Counter
open Agent2EpochMarker (b compose pre_append zeros_blank)
open PrefixCheck
abbrev Word := List Bool
def P : Word := [true,false,true,false,true,true,false,false]
def J : Word := [true,false,false]
def u : Word := [true,true,true,true,false,false,false]
def s : Word := true::u
def x : Word := [true,false]
def e : Tape := pre [true] blank
def d : Tape := pre [true,true] blank

def guard (L R : Word) : C := ⟨.B,L++[true],[false,false]++R++[true]⟩
def guardBlank (L R : Word) : C := ⟨.B,L++[true],[false,false]++R⟩

theorem guard_embed (L R : Word) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    physical (embed (guard L R) (tail l) (tail r)) = b (pre L l) (pre R r) := by
  change other Q.B (pre (L++[true]) (tail l)) (pre (([false,false]++R)++[true]) (tail r)) = _
  rw [pre_append, pre_append, pre_append]
  have h1 : pre [true] (tail l) = l := decompose_bit l true hl
  have h2 : pre [true] (tail r) = r := decompose_bit r true hr
  rw [h1,h2]
  rfl

theorem guard_sound (L R L' R' : Word) (k t : Nat) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true)
    (h : exec k (guard L R) = some (t,guard L' R')) :
    run t (b (pre L l) (pre R r)) = some (b (pre L' l) (pre R' r)) := by
  have h0 := exec_sound k (guard L R) (guard L' R') t (tail l) (tail r) h
  rw [guard_embed L R l r hl hr, guard_embed L' R' l r hl hr] at h0
  exact h0

theorem guardBlank_embed (L R : Word) (l : Tape) (hl : l 0 = true) :
    physical (embed (guardBlank L R) (tail l) blank) = b (pre L l) (pre R blank) := by
  change other Q.B (pre (L++[true]) (tail l)) (pre ([false,false]++R) blank) = _
  rw [pre_append,pre_append]
  have h1 : pre [true] (tail l) = l := decompose_bit l true hl
  rw [h1]
  rfl

theorem guardBlank_sound (L R L' R' : Word) (k t : Nat) (l : Tape)
    (hl : l 0 = true) (h : exec k (guardBlank L R) = some (t,guardBlank L' R')) :
    run t (b (pre L l) (pre R blank)) = some (b (pre L' l) (pre R' blank)) := by
  have h0 := exec_sound k (guardBlank L R) (guardBlank L' R') t (tail l) blank h
  rw [guardBlank_embed L R l hl, guardBlank_embed L' R' l hl] at h0
  exact h0

def rep (w : Word) : Nat → Tape → Tape
  | 0,l => l
  | n+1,l => pre w (rep w n l)

theorem rep_comm (w : Word) (n : Nat) (l : Tape) : rep w n (pre w l) = pre w (rep w n l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep]; rw [ih]

theorem rep_add (w : Word) (n k : Nat) (l : Tape) : rep w (n+k) l = rep w n (rep w k l) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [Nat.succ_add]; simp only [rep]; rw [ih]

theorem rep_first (w : Word) (hw : w.head? = some true) (n : Nat) (l : Tape) (hl : l 0 = true) : rep w n l 0 = true := by
  cases n with
  | zero => exact hl
  | succ n =>
    cases w with
    | nil => simp at hw
    | cons b w => simp at hw; subst b; rfl

theorem scanP (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 36 (b (pre P l) r) = some (b l (pre u (cons true r))) := by
  exact guard_sound P [] [] (u++[true]) 13 36 l r hl hr (by decide)

theorem decodeS (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 32 (b (pre J l) (pre x (pre s r))) = some (b (pre J (pre P l)) (pre x r)) := by
  exact guard_sound J (x++s) (J++P) x 8 32 l r hl hr (by decide)

theorem decodeD (l : Tape) (hl : l 0 = true) :
    run 27 (b (pre J l) (pre x d)) = some (b (pre P l) e) := by
  have h := guardBlank_sound J (x++[true,true,false,false]) P [true] 7 27 l hl (by decide)
  have hz : pre (x++[true,true,false,false]) blank = pre x d := by
    rw [pre_append]
    change pre x (pre ([true,true]++List.replicate 2 false) blank) = _
    rw [pre_append,zeros_blank]
    rfl
  rw [hz] at h
  exact h

def pushCost : Nat → Nat
  | 0 => 0
  | n+1 => 36+pushCost n

def popCost : Nat → Nat
  | 0 => 27
  | n+1 => 32+popCost n

theorem pushP (n : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (pushCost n) (b (rep P n l) (pre u r)) = some (b l (pre u (rep s n r))) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h1 := scanP (rep P n l) (pre u r) (rep_first P (by decide) n l hl) (by rfl)
    have h2 := ih (pre s r) (by rfl)
    rw [rep_comm] at h2
    exact @compose 36 (pushCost n) _ _ _ h1 h2

theorem consumeP (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (36+pushCost n) (b (rep P (n+1) l) e) = some (b l (pre u (rep s n d))) := by
  have h1 := scanP (rep P n l) e (rep_first P (by decide) n l hl) (by rfl)
  have h2 := pushP n l d hl (by rfl)
  exact @compose 36 (pushCost n) _ _ _ h1 h2

theorem popP (n : Nat) (l : Tape) (hl : l 0 = true) :
    run (popCost n) (b (pre J l) (pre x (rep s n d))) = some (b (rep P (n+1) l) e) := by
  induction n generalizing l with
  | zero => exact decodeD l hl
  | succ n ih =>
    have h1 := decodeS l (rep s n d) hl (rep_first s (by decide) n d (by rfl))
    have h2 := ih (pre P l) (by rfl)
    rw [rep_comm] at h2
    exact @compose 32 (popCost n) _ _ _ h1 h2

/-- A local finite prefix core acts for every additional count of P blocks. -/
theorem core (k j extra steps c : Nat) (W Y : Word) (l : Tape) (hl : l 0 = true)
    (hW : W.head? = some true) (hY : Y.head? = some true)
    (cert : exec steps (guard W (u ++ List.flatten (List.replicate k s))) =
      some (c, guard (J++Y) (x ++ List.flatten (List.replicate j s)))) :
    run ((36+pushCost (k+extra)+c)+popCost (j+extra))
      (b (rep P (k+extra+1) (pre W l)) e) =
    some (b (rep P (j+extra+1) (pre Y l)) e) := by
  have hhead (W : Word) (h : W.head? = some true) : pre W l 0 = true := by
    cases W with
    | nil => simp at h
    | cons v W => simp at h; subst v; rfl
  have flat (n : Nat) (r : Tape) : pre (List.flatten (List.replicate n s)) r = rep s n r := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ]; simp only [List.flatten_cons,pre_append,rep]; rw [ih]
  have h1 := consumeP (k+extra) (pre W l) (hhead W hW)
  have h2 := guard_sound W (u++List.flatten (List.replicate k s)) (J++Y)
    (x++List.flatten (List.replicate j s)) steps c l (rep s extra d) hl (rep_first s (by decide) extra d (by rfl)) cert
  rw [pre_append,pre_append,pre_append,flat,flat,← rep_add,← rep_add] at h2
  have h3 := popP (j+extra) (pre Y l) (hhead Y hY)
  exact @compose (36+pushCost (k+extra)+c) (popCost (j+extra)) _ _ _
    (@compose (36+pushCost (k+extra)) c _ _ _ h1 h2) h3

#print axioms core
end F197.Agent2Counter
