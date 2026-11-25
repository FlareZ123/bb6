import Agent46GuardedRun
import FastFAR

namespace BB6.Agent46Raw13ZeroRE.CounterGrammar
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Guarded
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- These two cylinders have identical word dynamics, apart from a trailing
    zero and different fixed primitive costs. The unassigned entry is E1. -/
def table (v : Bool) : PartialMachine :=
  if v then FAR.fromCodes [7,10,11,12,2,5,17,22,5,24,16,10]
  else FAR.fromCodes [7,10,11,12,2,5,17,20,5,24,19,16]

inductive Digit where
  | spacer | d0 | d1 | d2 | d3
  deriving DecidableEq, Repr
inductive Terminal where
  | low | middle | high
  deriving DecidableEq, Repr
inductive CounterWord where
  | terminal (t : Terminal)
  | cons (d : Digit) (w : CounterWord)
  deriving DecidableEq, Repr

/-- All tokens start with 10. Interior run-length codes are respectively
    [2], [8], [1,5], [4,1,2], [1,1,1,2]. -/
def digitTail : Digit → List Bool
  | .spacer => [false]
  | .d0 => [false,false,false,false,false,false,false]
  | .d1 => [true,false,false,false,false,false]
  | .d2 => [false,false,false,true,false,true,false,false]
  | .d3 => [true,false,true,false,true,false,false]

def terminalTail (v : Bool) : Terminal → List Bool
  | .low => [true] ++ (if v then [false] else [])
  | .middle => [false,false,false,true,false,true] ++ (if v then [false] else [])
  | .high => [true,false,true,false,true] ++ (if v then [false] else [])

def body (v : Bool) : CounterWord → List Bool
  | .terminal t => terminalTail v t
  | .cons d w => digitTail d ++ true :: false :: body v w

def encode (v : Bool) (w : CounterWord) : List Bool := true :: false :: body v w

/-- A total carry transducer. No bound on the number of tokens is needed. -/
def advance : CounterWord → CounterWord
  | .terminal .low => .terminal .middle
  | .terminal .middle => .cons .spacer (.terminal .high)
  | .terminal .high => .cons .d0 (.terminal .low)
  | .cons .spacer w => .cons .spacer (advance w)
  | .cons .d0 w => .cons .spacer (.cons .d1 w)
  | .cons .d1 w => .cons .d2 w
  | .cons .d2 w => .cons .spacer (.cons .d3 w)
  | .cons .d3 w => .cons .d0 (advance w)

def scan (s R : List Bool) : Z0 := ⟨0,false::s,true::true::R⟩
def restore (b R : List Bool) : Z0 := ⟨1,false::false::b,true::R⟩
def boundary (v : Bool) (w : CounterWord) : Z0 :=
  ⟨1,false::false::false::encode v w,[]⟩

def stack1 (R : List Bool) := true :: false :: true :: R
def stack4 (R : List Bool) := true :: true :: true :: true :: true :: true :: true :: false :: true :: R

def pushCost (v : Bool) (j : Nat) := (if v then 3 else 7) + 2*j

theorem push1 (v : Bool) (s R : List Bool) :
    run0 (table v) (pushCost v 1) (scan (true::false::false::s) R) =
      some (scan s (stack1 R)) := by
  cases v with
  | false => exact guardRun_sound (table false) false false 9 (z:=⟨0,[false,true,false,false],[true,true]⟩) (z':=⟨0,[false],[true,true,true,false,true]⟩) (by decide) s R (by intro h; cases h) (by intro h; cases h)
  | true => exact guardRun_sound (table true) false false 5 (z:=⟨0,[false,true,false,false],[true,true]⟩) (z':=⟨0,[false],[true,true,true,false,true]⟩) (by decide) s R (by intro h; cases h) (by intro h; cases h)

theorem push4 (v : Bool) (s R : List Bool) :
    run0 (table v) (pushCost v 4) (scan (true::false::true::false::true::false::true::false::false::s) R) =
      some (scan s (stack4 R)) := by
  cases v with
  | false => exact guardRun_sound (table false) false false 15 (z:=⟨0,[false,true,false,true,false,true,false,true,false,false],[true,true]⟩) (z':=⟨0,[false],[true,true,true,true,true,true,true,true,true,false,true]⟩) (by decide) s R (by intro h; cases h) (by intro h; cases h)
  | true => exact guardRun_sound (table true) false false 11 (z:=⟨0,[false,true,false,true,false,true,false,true,false,false],[true,true]⟩) (z':=⟨0,[false],[true,true,true,true,true,true,true,true,true,false,true]⟩) (by decide) s R (by intro h; cases h) (by intro h; cases h)

theorem pop1 (v : Bool) (b R : List Bool) :
    run0 (table v) 5 (restore b (stack1 R)) =
      some (restore (false::true::false::b) R) := by
  cases v with
  | false => exact guardRun_sound (table false) false false 5 (z:=⟨1,[false,false],[true,true,false,true]⟩) (z':=⟨1,[false,false,false,true,false],[true]⟩) (by decide) b R (by intro h; cases h) (by intro h; cases h)
  | true => exact guardRun_sound (table true) false false 5 (z:=⟨1,[false,false],[true,true,false,true]⟩) (z':=⟨1,[false,false,false,true,false],[true]⟩) (by decide) b R (by intro h; cases h) (by intro h; cases h)

theorem pop4 (v : Bool) (b R : List Bool) :
    run0 (table v) 23 (restore b (stack4 R)) =
      some (restore (false::false::false::false::false::false::false::true::false::b) R) := by
  cases v with
  | false => exact guardRun_sound (table false) false false 23 (z:=⟨1,[false,false],[true,true,true,true,true,true,true,true,false,true]⟩) (z':=⟨1,[false,false,false,false,false,false,false,false,false,true,false],[true]⟩) (by decide) b R (by intro h; cases h) (by intro h; cases h)
  | true => exact guardRun_sound (table true) false false 23 (z:=⟨1,[false,false],[true,true,true,true,true,true,true,true,false,true]⟩) (z':=⟨1,[false,false,false,false,false,false,false,false,false,true,false],[true]⟩) (by decide) b R (by intro h; cases h) (by intro h; cases h)

def middleCost (v : Bool) : CounterWord → Nat
  | .terminal .low => if v then 25 else 27
  | .terminal .middle => if v then 17 else 19
  | .terminal .high => if v then 41 else 43
  | .cons .spacer w => pushCost v 1 + middleCost v w + 5
  | .cons .d0 _ => if v then 17 else 19
  | .cons .d1 _ => if v then 25 else 27
  | .cons .d2 _ => if v then 17 else 19
  | .cons .d3 w => pushCost v 4 + middleCost v w + 23

/-- Induction over arbitrary counter words. The right tail R is universally
    quantified; a carry pushes a finite stack frame, recursively processes
    the remaining word, and pops precisely the original frame. -/
theorem middle (v : Bool) (w : CounterWord) (R : List Bool) :
    run0 (table v) (middleCost v w) (scan (encode v w) R) =
      some (restore (body v (advance w)) R) := by
  induction w generalizing R with
  | terminal t =>
    cases t with
    | low =>
      cases v with
      | false => exact guardRun_sound (table false) true false 27 (z:=⟨0,[false,true,false,true],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,true,false,true],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
      | true => exact guardRun_sound (table true) true false 25 (z:=⟨0,[false,true,false,true,false],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,true,false,true,false],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
    | middle =>
      cases v with
      | false => exact guardRun_sound (table false) true false 19 (z:=⟨0,[false,true,false,false,false,false,true,false,true],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,true,false,true],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
      | true => exact guardRun_sound (table true) true false 17 (z:=⟨0,[false,true,false,false,false,false,true,false,true,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,true,false,true,false],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
    | high =>
      cases v with
      | false => exact guardRun_sound (table false) true false 43 (z:=⟨0,[false,true,false,true,false,true,false,true],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,false,false,false,false,true,false,true],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
      | true => exact guardRun_sound (table true) true false 41 (z:=⟨0,[false,true,false,true,false,true,false,true,false],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,false,false,false,false,true,false,true,false],[true]⟩) (by decide) [] R (by intro _; rfl) (by intro h; cases h)
  | cons d w ih =>
    cases d with
    | spacer =>
      have h1 := push1 v (encode v w) R
      have h2 := ih (stack1 R)
      have h3 := pop1 v (body v (advance w)) R
      exact join0 (join0 h1 h2) h3
    | d0 =>
      cases v with
      | false => exact guardRun_sound (table false) false false 19 (z:=⟨0,[false,true,false,false,false,false,false,false,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,false,false,false,false],[true]⟩) (by decide) (encode false w) R (by intro h; cases h) (by intro h; cases h)
      | true => exact guardRun_sound (table true) false false 17 (z:=⟨0,[false,true,false,false,false,false,false,false,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,false,false,false,false],[true]⟩) (by decide) (encode true w) R (by intro h; cases h) (by intro h; cases h)
    | d1 =>
      cases v with
      | false => exact guardRun_sound (table false) false false 27 (z:=⟨0,[false,true,false,true,false,false,false,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,true,false,true,false,false],[true]⟩) (by decide) (encode false w) R (by intro h; cases h) (by intro h; cases h)
      | true => exact guardRun_sound (table true) false false 25 (z:=⟨0,[false,true,false,true,false,false,false,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,false,false,true,false,true,false,false],[true]⟩) (by decide) (encode true w) R (by intro h; cases h) (by intro h; cases h)
    | d2 =>
      cases v with
      | false => exact guardRun_sound (table false) false false 19 (z:=⟨0,[false,true,false,false,false,false,true,false,true,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,true,false,true,false,false],[true]⟩) (by decide) (encode false w) R (by intro h; cases h) (by intro h; cases h)
      | true => exact guardRun_sound (table true) false false 17 (z:=⟨0,[false,true,false,false,false,false,true,false,true,false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false,true,false,true,false,true,false,false],[true]⟩) (by decide) (encode true w) R (by intro h; cases h) (by intro h; cases h)
    | d3 =>
      have h1 := push4 v (encode v w) R
      have h2 := ih (stack4 R)
      have h3 := pop4 v (body v (advance w)) R
      exact join0 (join0 h1 h2) h3

theorem enter (v : Bool) (w : CounterWord) :
    run0 (table v) 4 (boundary v w) = some (scan (encode v w) [true]) := by
  cases v with
  | false => exact guardRun_sound (table false) false true 4 (z:=⟨1,[false,false,false],[]⟩) (z':=⟨0,[false],[true,true,true]⟩) (by decide) (encode false w) [] (by intro h; cases h) (by intro _; rfl)
  | true => exact guardRun_sound (table true) false true 4 (z:=⟨1,[false,false,false],[]⟩) (z':=⟨0,[false],[true,true,true]⟩) (by decide) (encode true w) [] (by intro h; cases h) (by intro _; rfl)

theorem exit (v : Bool) (w : CounterWord) :
    run0 (table v) 5 (restore (body v w) [true]) = some (boundary v w) := by
  cases v with
  | false => exact guardRun_sound (table false) false true 5 (z:=⟨1,[false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false],[]⟩) (by decide) (body false w) [] (by intro h; cases h) (by intro _; rfl)
  | true => exact guardRun_sound (table true) false true 5 (z:=⟨1,[false,false],[true,true]⟩) (z':=⟨1,[false,false,false,true,false],[]⟩) (by decide) (body true w) [] (by intro h; cases h) (by intro _; rfl)

def cost (v : Bool) (w : CounterWord) := 4 + middleCost v w + 5

theorem advance_sound (v : Bool) (w : CounterWord) :
    run0 (table v) (cost v w) (boundary v w) = some (boundary v (advance w)) :=
  join0 (join0 (enter v w) (middle v w [true])) (exit v (advance w))

def seed := CounterWord.terminal .low
def entry (v : Bool) := if v then 27 else 25

theorem first (v : Bool) :
    run0 (table v) (entry v) ⟨0,[],[]⟩ = some (boundary v seed) := by
  cases v <;> decide

def orbit : Nat → CounterWord
  | 0 => seed
  | n+1 => advance (orbit n)

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply never_of_growth (table v) (fun n => boundary v (orbit n))
    (entry v) (fun n => cost v (orbit n)) (first v) _ _ m hm
  · intro n; unfold cost; omega
  · intro n; exact advance_sound v (orbit n)

#print axioms middle
#print axioms advance_sound
#print axioms first
#print axioms never
end BB6.Agent46Raw13ZeroRE.CounterGrammar
