import EpochMarkerExit
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.Agent2EpochMarker
open PrefixCheck

def ent0 := pre [true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false]
theorem enter0 (l : Tape) (hl : l 0 = true) :
    run 1863 (b (ent0 l) (pre [true] blank)) = some (b l r0) := by
  let m : C := ⟨.B,[true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false,true],[false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]⟩
  let m' : C := ⟨.B,[true],[false,false,true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,true,true,false,false,false,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true]⟩
  have hz : pre [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] blank = pre [false,false,true] blank := by
    rw [show [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] = [false,false,true] ++ List.replicate 21 false by decide, pre_append, zeros_blank]
  have hs : b (ent0 l) (pre [true] blank) = physical (embed m (tail l) blank) := by
    conv => lhs; rw [← decompose_bit l true hl]
    change other Q.B (pre [true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false,true] (tail l)) (pre [false,false,true] blank) = other Q.B (pre [true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false,true] (tail l)) (pre [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] blank)
    rw [hz]
  have ht : b l r0 = physical (embed m' (tail l) blank) := by
    conv => lhs; rw [← decompose_bit l true hl]
    rfl
  rw [hs,ht]
  exact exec_sound 575 m m' 1863 (tail l) blank (by decide)

#print axioms enter0
def ent1 := pre [true,false,true,false,true,true,false,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false]
theorem enter1 (l : Tape) (hl : l 0 = true) :
    run 887 (b (ent1 l) (pre [true] blank)) = some (b l r1) := by
  let m : C := ⟨.B,[true,false,true,false,true,true,false,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true],[false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]⟩
  let m' : C := ⟨.B,[true],[false,false,true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,true,true,false,false,false,true,false,true,true,true,true,false,false,false,true,true]⟩
  have hz : pre [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] blank = pre [false,false,true] blank := by
    rw [show [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] = [false,false,true] ++ List.replicate 17 false by decide, pre_append, zeros_blank]
  have hs : b (ent1 l) (pre [true] blank) = physical (embed m (tail l) blank) := by
    conv => lhs; rw [← decompose_bit l true hl]
    change other Q.B (pre [true,false,true,false,true,true,false,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true] (tail l)) (pre [false,false,true] blank) = other Q.B (pre [true,false,true,false,true,true,false,false,true,false,false,true,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true] (tail l)) (pre [false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false] blank)
    rw [hz]
  have ht : b l r1 = physical (embed m' (tail l) blank) := by
    conv => lhs; rw [← decompose_bit l true hl]
    rfl
  rw [hs,ht]
  exact exec_sound 281 m m' 887 (tail l) blank (by decide)

#print axioms enter1
def kword := pre [true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false]
theorem scanK (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 82 (b (kword l) r) = some (b l (h r)) := by
  let m : C := ⟨.B,[true,true,false,false,true,false,true,true,false,false,true,false,true,false,true,true,false,false,true],[false,false,true]⟩
  let m' : C := ⟨.B,[true],[false,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,false,true]⟩
  have hs : b (kword l) r = physical (embed m (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  have ht : b l (h r) = physical (embed m' (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  rw [hs,ht]
  exact exec_sound 29 m m' 82 (tail l) (tail r) (by decide)

def kpow : Nat → Tape → Tape
  | 0,l => l
  | n+1,l => kword (kpow n l)
def hsingle : Nat → Tape → Tape
  | 0,r => r
  | n+1,r => h (hsingle n r)
def scancost : Nat → Nat
  | 0 => 0
  | n+1 => 82 + scancost n

theorem kpow_first (n : Nat) (l : Tape) (hl : l 0 = true) : kpow n l 0 = true := by
  cases n with | zero => exact hl | succ n => rfl
theorem hsingle_comm (n : Nat) (r : Tape) : hsingle n (h r) = h (hsingle n r) := by
  induction n with | zero => rfl | succ n ih => simp only [hsingle]; rw [ih]
theorem scan_many (n : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (scancost n) (b (kpow n l) r) = some (b l (hsingle n r)) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have h1 := scanK (kpow n l) r (kpow_first n l hl) hr
    have h2 := ih (h r) (by rfl)
    rw [hsingle_comm] at h2
    exact @compose 82 (scancost n) _ _ _ h1 h2
theorem scancost_eq (n : Nat) : scancost n = 82*n := by
  induction n with | zero => rfl | succ n ih => simp [scancost, ih]; omega

#print axioms scanK
#print axioms scan_many
end F197.Agent2EpochMarker
