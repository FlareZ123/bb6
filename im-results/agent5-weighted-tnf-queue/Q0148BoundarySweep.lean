import Agent5PackedSweep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent5Q0148BoundarySweep
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
open BB6Coverage.Agent13PackedZipper BB6.Agent5PackedSweep

/-- Original q0-148 F1-open table, not a completed halting program. -/
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => none
  | _,_ => none

/-- The entire local machine calculation on a leftward alternating block.
    The finite checker forbids reading beyond the listed stack prefixes. -/
theorem leftOne :
    Auto.knownRun p 2 ⟨2,[false,true,false],[]⟩ =
      some ⟨2,[false],[true,false]⟩ := by decide +kernel

/-- Parametric left pass across n copies of 10, with arbitrary
    untouched (unbounded) left and right tape tails L and R. -/
theorem transparentLeft (n L R : Nat) :
    runP p (2*n)
      ⟨2,cat [false] (repCat [true,false] n L),cat [] R⟩ =
    some ⟨2,cat [false] L,cat [] (repCat [true,false] n R)⟩ :=
  sweepLP p 2 [false] [] [true,false] [true,false] 2 n L R leftOne

/-- The rightward six-step block, including the fixed zero-cell frame
    immediately to the right of the head. -/
theorem rightOne :
    Auto.knownRun p 6 ⟨0,[false],[false,true,false]⟩ =
      some ⟨0,[false,false,true],[false]⟩ := by decide +kernel

/-- Parametric right pass: copies of 10 to the right become copies of
    01 on the left, with the two fixed zero frame cells retained. -/
theorem transparentRight (n L R : Nat) :
    runP p (6*n)
      ⟨0,cat [false] L,cat [false] (repCat [true,false] n R)⟩ =
    some ⟨0,cat [false] (repCat [false,true] n L),cat [false] R⟩ :=
  sweepRP p 0 [false] [false] [true,false] [false,true] 6 n L R rightOne


/-- A separated 110 marker and its preceding 10 guard are transferred
    during a five-step leftward pass, with exact source semantics. -/
theorem leftMarkerOne :
    Auto.knownRun p 5 ⟨2,[false,true,true,false,true,false],[]⟩ =
      some ⟨2,[false],[true,true,false,true,false]⟩ := by decide +kernel

/-- Blocks in the leftward tape orientation.  The marker constructor
    incorporates the mandatory separating 10 token. -/
inductive LeftChunk where
  | alternating
  | separatedMarker
  deriving DecidableEq, Repr

def chunkBits : LeftChunk → List Bool
  | .alternating => [true,false]
  | .separatedMarker => [true,true,false,true,false]

def chunkCost : LeftChunk → Nat
  | .alternating => 2
  | .separatedMarker => 5

def inputBits : List LeftChunk → List Bool
  | [] => []
  | c::cs => chunkBits c ++ inputBits cs

def outputBits : List LeftChunk → List Bool
  | [] => []
  | c::cs => outputBits cs ++ chunkBits c

def scanCost : List LeftChunk → Nat
  | [] => 0
  | c::cs => chunkCost c + scanCost cs

/-- One block, with arbitrary unobserved left/right tape tails. -/
theorem scanOne (c : LeftChunk) (L R : List Bool) :
    run0 p (chunkCost c)
      ⟨2,[false] ++ chunkBits c ++ L,R⟩ =
      some ⟨2,[false] ++ L,chunkBits c ++ R⟩ := by
  cases c with
  | alternating =>
      simpa [chunkCost,chunkBits,Auto.extend,List.append_assoc] using
        Auto.knownRun_sound p 2 leftOne L R
  | separatedMarker =>
      simpa [chunkCost,chunkBits,Auto.extend,List.append_assoc] using
        Auto.knownRun_sound p 5 leftMarkerOne L R

/-- Exact full *leftward half-sweep* for an arbitrary finite sequence of
    alternating and separated-marker chunks, all with arbitrary tails.
    This is a mathematical all-length statement, not finite simulation. -/
theorem scanChunks (cs : List LeftChunk) (L R : List Bool) :
    run0 p (scanCost cs)
      ⟨2,[false] ++ inputBits cs ++ L,R⟩ =
      some ⟨2,[false] ++ L,outputBits cs ++ R⟩ := by
  induction cs generalizing R with
  | nil =>
      simp [scanCost,inputBits,outputBits,run0]
  | cons c cs ih =>
      have h1 := scanOne c (inputBits cs ++ L) R
      have h2 := ih (chunkBits c ++ R)
      have h := join0 h1 h2
      simpa only [scanCost,inputBits,outputBits,List.cons_append,
        List.nil_append,List.append_assoc] using h

#print axioms leftMarkerOne
#print axioms scanOne
#print axioms scanChunks

#print axioms leftOne
#print axioms transparentLeft
#print axioms rightOne
#print axioms transparentRight
end BB6.Agent5Q0148BoundarySweep
