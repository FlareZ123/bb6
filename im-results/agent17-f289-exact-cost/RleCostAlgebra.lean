import Std

namespace BB6.Agent17.RleCost

def weight (segs : List (Nat × Nat)) : Nat :=
  segs.foldr (fun (r,c) s => c * (6*r+26) + s) 0

def pushSeg (r c : Nat) (segs : List (Nat × Nat)) : List (Nat × Nat) :=
  if c == 0 then segs else
  match segs with
  | (r2,c2) :: ss => if r == r2 then (r,c+c2) :: ss else (r,c) :: segs
  | [] => [(r,c)]

theorem weight_pushSeg (r c : Nat) (segs : List (Nat × Nat)) :
    weight (pushSeg r c segs) = c*(6*r+26)+weight segs := by
  by_cases hc : c = 0
  · subst c
    simp [pushSeg]
  · cases segs with
    | nil => simp [pushSeg, hc, weight]
    | cons p ss =>
      rcases p with ⟨r2,c2⟩
      by_cases hr : r = r2
      · subst r2
        simp [pushSeg, hc, weight, Nat.add_mul, Nat.add_assoc]
      · simp [pushSeg, hc, hr, weight]

def drBot (k : Nat) := 6*k+14
def drBotZeros (q k : Nat) := 6*k*q+9*q*q+9*q
def sweep (bot S : Nat) := 6*bot+41+S
def drOne (c0 bot S : Nat) := 6*c0+6*bot+46+S
def drZeros (q c0 bot S : Nat) := 6*q*(c0+bot)+15*q*q+35*q+q*S
def rnilOne (c0 bot S : Nat) := 6*c0+6*bot+57+S
def rnilPow (q bot S : Nat) := 6*q*bot+16*q*q+41*q+q*S
def p1One (r bot S : Nat) := 10*r+6*bot+75+S
def p1Pow (q r bot S : Nat) := q*(7*r+50+6*bot+S)+(3*r+25)*q*q
def p2One (r bot S : Nat) := 15*r*r+77*r+73+6*bot*(r+1)+(r+1)*S
def p2Pow (q r bot S : Nat) := q*(37*r+48+6*bot*(r+1)+(r+1)*S)+(r+1)*(15*r+25)*q*q

theorem drBotZeros_succ (q k : Nat) :
    drBotZeros (q+1) k = drBot k + 4 + drBotZeros q (k+3) := by
  unfold drBotZeros drBot
  grind

theorem sweep_nil (bot : Nat) :
    sweep bot 0 = (4*bot+12) + drBot 0 + (2*bot+15) := by
  unfold sweep drBot
  omega

theorem sweep_cons (r c bot S : Nat) :
    sweep bot (c*(6*r+26)+S) = c*(4*r+11) + sweep bot S + c*(2*r+15) := by
  unfold sweep
  grind

theorem drOne_cost (c0 bot S : Nat) :
    drOne c0 bot S = 4*c0 + 3 + sweep bot S + 2*(c0+1) := by
  unfold drOne sweep
  omega

theorem drZeros_succ (q c0 bot S : Nat) :
    drZeros (q+1) c0 bot S = drOne c0 (bot+q) S + 4 + drZeros q (c0+4) bot S := by
  unfold drZeros drOne
  grind

theorem rnilOne_cost (c0 bot S : Nat) :
    rnilOne c0 bot S = 1 + (4*c0+6) + sweep bot S + 2*c0 + 5 + 4 := by
  unfold rnilOne sweep
  omega

theorem rnilPow_succ (q bot S : Nat) :
    rnilPow (q+1) bot S = rnilOne 0 (bot+q) S + rnilPow q bot (26+S) := by
  unfold rnilPow rnilOne
  grind

theorem p1One_cost (r bot S : Nat) :
    p1One r bot S = 4*(r+1)+4+4+drOne (r+2) bot S+5 := by
  unfold p1One drOne
  omega

theorem p1Pow_succ (q r bot S : Nat) :
    p1Pow (q+1) r bot S = p1One r (bot+q) S + p1Pow q r bot (6*(r+3)+26+S) := by
  unfold p1Pow p1One
  grind

theorem p2One_zero (bot S : Nat) :
    p2One 0 bot S = 4+2+4+drOne 2 bot S+5 := by
  unfold p2One drOne
  omega

theorem p2One_succ (t bot S : Nat) :
    p2One (t+1) bot S = 4+2+4+drZeros t 2 (bot+2) S +
      drOne (2+4*t) (bot+1) S+4+drOne (2+4*t+4) bot S+5 := by
  unfold p2One drZeros drOne
  grind

theorem p2Pow_succ (q r bot S : Nat) :
    p2Pow (q+1) r bot S = p2One r (bot+q*(r+1)) S + p2Pow q r bot (6*(4*r+3)+26+S) := by
  unfold p2Pow p2One
  grind

-- These equations characterize every finite recurrence without materializing its trace.
def drZerosRec : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | q+1, c0, bot, S => drOne c0 (bot+q) S + 4 + drZerosRec q (c0+4) bot S

def rnilPowRec : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | q+1, bot, S => rnilOne 0 (bot+q) S + rnilPowRec q bot (26+S)

def p1PowRec : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | q+1, r, bot, S => p1One r (bot+q) S + p1PowRec q r bot (6*(r+3)+26+S)

def p2PowRec : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | q+1, r, bot, S => p2One r (bot+q*(r+1)) S + p2PowRec q r bot (6*(4*r+3)+26+S)

theorem drZeros_closed (q c0 bot S : Nat) : drZerosRec q c0 bot S = drZeros q c0 bot S := by
  induction q generalizing c0 with
  | zero => simp [drZerosRec, drZeros]
  | succ q ih => rw [drZerosRec, ih, ← drZeros_succ]

theorem rnilPow_closed (q bot S : Nat) : rnilPowRec q bot S = rnilPow q bot S := by
  induction q generalizing S with
  | zero => simp [rnilPowRec, rnilPow]
  | succ q ih => rw [rnilPowRec, ih, ← rnilPow_succ]

theorem p1Pow_closed (q r bot S : Nat) : p1PowRec q r bot S = p1Pow q r bot S := by
  induction q generalizing S with
  | zero => simp [p1PowRec, p1Pow]
  | succ q ih => rw [p1PowRec, ih, ← p1Pow_succ]

theorem p2Pow_closed (q r bot S : Nat) : p2PowRec q r bot S = p2Pow q r bot S := by
  induction q generalizing S with
  | zero => simp [p2PowRec, p2Pow]
  | succ q ih => rw [p2PowRec, ih, ← p2Pow_succ]

#print axioms weight_pushSeg
#print axioms drZeros_closed
#print axioms rnilPow_closed
#print axioms p1Pow_closed
#print axioms p2Pow_closed

end BB6.Agent17.RleCost
