import PrefixCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace F197.Agent2EpochMarker

def t : Tape → Tape := pre [true,true,false,false]
def h : Tape → Tape := pre [true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,false]
def v : Tape → Tape := pre [true,true,true,false]
def v2 : Tape → Tape := pre [true,true,true,true,true,true,false,false,false,true,true,false]
def b (l r : Tape) : Config := other Q.B l (pre [false,false] r)
def g := pre [true,false,true,true,false,false,true,true,false,false,true,false,false,true,false,true,true,true,false,false,true,false,false]
def block := pre [true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true,true,false,false]
def g2 := pre [true,false,true,true,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true,true,false,false]
def source := pre [true,true,false,false,true,false,true,true,false,false,true,false,false]

open PrefixCheck
theorem entry (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 112 (b (source l) (h r)) = some (b (g (t l)) (v r)) := by
  let m : C := ⟨.B,[true,true,false,false,true,false,true,true,false,false,true,false,false,true],[false,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,false,true]⟩
  let m' : C := ⟨.B,[true,false,true,true,false,false,true,true,false,false,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true],[false,false,true,true,true,false,true]⟩
  have hs : b (source l) (h r) = physical (embed m (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  have ht : b (g (t l)) (v r) = physical (embed m' (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  rw [hs,ht]
  exact exec_sound 30 m m' 112 (tail l) (tail r) (by decide)

theorem half (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 176 (b (g l) (v (h r))) = some (b (g2 l) (v2 r)) := by
  let m : C := ⟨.B,[true,false,true,true,false,false,true,true,false,false,true,false,false,true,false,true,true,true,false,false,true,false,false,true],[false,false,true,true,true,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,false,true]⟩
  let m' : C := ⟨.B,[true,false,true,true,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true,true,false,false,true],[false,false,true,true,true,true,true,true,false,false,false,true,true,false,true]⟩
  have hs : b (g l) (v (h r)) = physical (embed m (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  have ht : b (g2 l) (v2 r) = physical (embed m' (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  rw [hs,ht]
  exact exec_sound 54 m m' 176 (tail l) (tail r) (by decide)

theorem half2 (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 96 (b (g2 l) (v2 (h r))) = some (b (g (block l)) (v r)) := by
  let m : C := ⟨.B,[true,false,true,true,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true,true,false,false,true],[false,false,true,true,true,true,true,true,false,false,false,true,true,false,true,true,true,true,false,false,false,true,true,true,true,true,false,false,false,true,true,false,true]⟩
  let m' : C := ⟨.B,[true,false,true,true,false,false,true,true,false,false,true,false,false,true,false,true,true,true,false,false,true,false,false,true,false,true,false,true,true,false,false,true,false,true,false,true,false,true,true,false,false,true,false,true,true,true,false,false,true,false,false,true,true,false,false,true,true,false,false,true],[false,false,true,true,true,false,true]⟩
  have hs : b (g2 l) (v2 (h r)) = physical (embed m (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  have ht : b (g (block l)) (v r) = physical (embed m' (tail l) (tail r)) := by
    conv => lhs; rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  rw [hs,ht]
  exact exec_sound 23 m m' 96 (tail l) (tail r) (by decide)

theorem compose {n k : Nat} {x y z : Config}
    (h1 : run n x = some y) (h2 : run k y = some z) : run (n+k) x = some z := by
  rw [run_add, h1]; exact h2

theorem cycle (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (176+96) (b (g l) (v (h (h r)))) = some (b (g (block l)) (v r)) :=
  @compose 176 96 (b (g l) (v (h (h r)))) (b (g2 l) (v2 (h r))) (b (g (block l)) (v r))
    (half l (h r) hl (by rfl)) (half2 l r hl hr)

def hpow : Nat → Tape → Tape
  | 0,r => r
  | n+1,r => h (h (hpow n r))
def blockpow : Nat → Tape → Tape
  | 0,l => l
  | n+1,l => block (blockpow n l)
def cost : Nat → Nat
  | 0 => 0
  | n+1 => (176+96) + cost n
theorem hpow_first (n : Nat) (r : Tape) (hr : r 0 = true) : hpow n r 0 = true := by
  cases n with | zero => exact hr | succ n => rfl
theorem blockpow_comm (n : Nat) (l : Tape) : blockpow n (block l) = block (blockpow n l) := by
  induction n with | zero => rfl | succ n ih => simp only [blockpow]; rw [ih]
theorem cost_eq (n : Nat) : cost n = 272*n := by
  induction n with | zero => rfl | succ n ih => simp [cost, ih]; omega

theorem cycle_many (n : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (cost n) (b (g l) (v (hpow n r))) = some (b (g (blockpow n l)) (v r)) := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    have h1 := cycle l (hpow n r) hl (hpow_first n r hr)
    have h2 := ih (block l) (by rfl)
    rw [blockpow_comm] at h2
    exact @compose (176+96) (cost n) _ _ _ h1 h2

#print axioms entry
#print axioms half
#print axioms half2
#print axioms cycle_many
end F197.Agent2EpochMarker
