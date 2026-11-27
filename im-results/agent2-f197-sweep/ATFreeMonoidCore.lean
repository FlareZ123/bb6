import ATGeneralParser

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace F197
open Q

/- Free-monoid reset transport for F197.
   Input alphabet {P=AAT, Q=TAT}, output alphabet {P, AAAT}.
   Right-marker alphabet s=(5,3), C u=(2,1)(4,3).
   A genuinely arbitrary interspersed P/Q prefix is handled by one
   induction depositing markers and a second reverse-order decoder.
   Source machine: 1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF.
   Each local source lemma is guarded by run alignment. -/

/-- P=AAT, Q=TAT; Q is represented by true. -/
def fmSourceToken (b : Bool) (l : Tape) : Tape :=
  if b then
    pre [true,true,false,false,true,false,true,true,false,false] l
  else
    pre [true,false,true,false,true,true,false,false] l

/-- Tokenwise image: P maps to P; Q maps to AAAT. -/
def fmOutputToken (b : Bool) (l : Tape) : Tape :=
  if b then
    pre [true,false,true,false,true,false,true,true,false,false] l
  else
    pre [true,false,true,false,true,true,false,false] l

def fmWordIn : List Bool → Tape → Tape
  | [], l => l
  | b::bs, l => fmSourceToken b (fmWordIn bs l)

def fmWordOut : List Bool → Tape → Tape
  | [], l => l
  | b::bs, l => fmOutputToken b (fmWordOut bs l)

/-- Deposited right-marker P=s, Q=C u. -/
def fmMarker (b : Bool) (r : Tape) : Tape :=
  if b then
    pre [true,true,false,true,true,true,true,false,false,false] r
  else
    pre [true,true,true,true,true,false,false,false] r

/-- The first token uses a distinct terminating marker: d or C e. -/
def fmBase (b : Bool) : Tape :=
  if b then pre [true,true,false,true] blank
  else pre [true,true] blank

/-- Right stack, most recently consumed token at its near end. -/
def fmMarkers : List Bool → Tape → Tape
  | [], r => r
  | b::bs, r => fmMarkers bs (fmMarker b r)

def fmRightU (r : Tape) : Tape :=
  atpRight (pre [true,true,true,true,false,false,false] r)

def fmRightA (r : Tape) : Tape := atpXRight r

def fmSrcStep (b : Bool) : Nat := if b then 46 else 36
def fmDecStep (b : Bool) : Nat := if b then 36 else 32
def fmBaseDecStep (b : Bool) : Nat := if b then 31 else 27

def fmSrcCost : List Bool → Nat
  | [] => 0
  | b::bs => fmSrcStep b + fmSrcCost bs

/-- Right markers are decoded last-in, first-out. -/
def fmDecCost : List Bool → Nat
  | [] => 0
  | b::bs => fmDecCost bs + fmDecStep b

def fmCountQ : List Bool → Nat
  | [] => 0
  | false::bs => fmCountQ bs
  | true::bs => 1 + fmCountQ bs

theorem fmWordIn_first (ws : List Bool) (l : Tape)
    (hl : l 0 = true) : (fmWordIn ws l) 0 = true := by
  cases ws with
  | nil => exact hl
  | cons b bs => cases b <;> rfl

theorem fmWordOut_first (ws : List Bool) (l : Tape)
    (hl : l 0 = true) : (fmWordOut ws l) 0 = true := by
  cases ws with
  | nil => exact hl
  | cons b bs => cases b <;> rfl

theorem fmMarker_first (b : Bool) (r : Tape) :
    (fmMarker b r) 0 = true := by
  cases b <;> rfl

theorem fmBase_first (b : Bool) : (fmBase b) 0 = true := by
  cases b <;> rfl

theorem fmMarkers_first (ws : List Bool) (r : Tape)
    (hr : r 0 = true) : (fmMarkers ws r) 0 = true := by
  induction ws generalizing r with
  | nil => exact hr
  | cons b bs ih =>
      exact ih (r := fmMarker b r) (fmMarker_first b r)

/-- P/uR -> /u sR in 36 steps; Q/uR -> /u C uR in 46 steps. -/
theorem fmSourceOne (b : Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (fmSrcStep b)
      (other B (fmSourceToken b l) (fmRightU r)) =
    some (other B l (fmRightU (fmMarker b r))) := by
  cases b with
  | false =>
      simpa [fmSrcStep,fmSourceToken,fmRightU,fmMarker,
        atpRight,pre] using atc_consume_u l r hl hr
  | true =>
      have hU : (pre [true,true,true,true,false,false,false] r) 0 =
        true := by rfl
      simpa [fmSrcStep,fmSourceToken,fmRightU,fmMarker,
        atpRight,pre] using
        atc_preconsume l
          (pre [true,true,true,true,false,false,false] r) hl hU

/-- Reverse source steps: J/(A sR) deposits P; J/(A C uR)
    deposits AAAT, each leaving J at the left end. -/
theorem fmDecodeOne (b : Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (fmDecStep b)
      (other B (atpJ l) (fmRightA (fmMarker b r))) =
    some (other B (atpJ (fmOutputToken b l)) (fmRightA r)) := by
  cases b with
  | false =>
      simpa [fmDecStep,fmOutputToken,fmRightA,fmMarker,
        atpJ,atpXRight,pre] using atc_counter_s l r hl hr
  | true =>
      simpa [fmDecStep,fmOutputToken,fmRightA,fmMarker,
        atpJ,atpXRight,pre] using atc_counter_u l r hl hr

/-- Unbounded source transport for arbitrarily interspersed P/Q tokens,
    while the first u marker is already on the right. -/
theorem fmConsumeRest (ws : List Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (fmSrcCost ws)
      (other B (fmWordIn ws l) (fmRightU r)) =
    some (other B l (fmRightU (fmMarkers ws r))) := by
  induction ws generalizing r with
  | nil => rfl
  | cons b bs ih =>
      have hb : (fmWordIn bs l) 0 = true :=
        fmWordIn_first bs l hl
      have hm : (fmMarker b r) 0 = true :=
        fmMarker_first b r
      change run (fmSrcStep b + fmSrcCost bs)
        (other B
          (fmSourceToken b (fmWordIn bs l))
          (fmRightU r)) =
        some (other B l (fmRightU (fmMarkers bs (fmMarker b r))))
      rw [run_add, fmSourceOne b (fmWordIn bs l) r hb hr]
      simp only [Option.bind_some]
      exact ih (r := fmMarker b r) hm

/-- Exact reverse-order marker decoder on a general, aligned right
    continuation: no prescribed sequence shape or finite length bound. -/
theorem fmDecodeRest (ws : List Bool) (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run (fmDecCost ws)
      (other B (atpJ l) (fmRightA (fmMarkers ws r))) =
    some (other B (atpJ (fmWordOut ws l)) (fmRightA r)) := by
  induction ws generalizing l r with
  | nil => rfl
  | cons b bs ih =>
      have hm : (fmMarker b r) 0 = true := fmMarker_first b r
      have hout : (fmWordOut bs l) 0 = true :=
        fmWordOut_first bs l hl
      change run (fmDecCost bs + fmDecStep b)
        (other B (atpJ l)
          (fmRightA (fmMarkers bs (fmMarker b r)))) =
        some (other B
          (atpJ (fmOutputToken b (fmWordOut bs l)))
          (fmRightA r))
      rw [run_add, ih (l := l) (r := fmMarker b r) hl hm]
      simp only [Option.bind_some]
      exact fmDecodeOne b (fmWordOut bs l) r hout hr

#print axioms fmSourceOne
#print axioms fmDecodeOne
#print axioms fmConsumeRest
#print axioms fmDecodeRest

end F197
