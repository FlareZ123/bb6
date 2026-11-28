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


/-- A separated 110 marker followed by its 10 separator is consumed in
    fifteen steps by the exact rightward scan. The output is its reversal
    because the generated left stack is nearest-cell first. -/
theorem rightMarkerOne :
    Auto.knownRun p 15 ⟨0,[false],[false,true,true,false,true,false]⟩ =
      some ⟨0,[false,false,true,false,true,true],[false]⟩ := by decide +kernel

inductive RightChunk where
  | alternating
  | separatedMarker
  deriving DecidableEq, Repr

def rightInput : RightChunk → List Bool
  | .alternating => [true,false]
  | .separatedMarker => [true,true,false,true,false]

def rightOutput : RightChunk → List Bool
  | .alternating => [false,true]
  | .separatedMarker => [false,true,false,true,true]

def rightCost : RightChunk → Nat
  | .alternating => 6
  | .separatedMarker => 15

def inputRightChunks : List RightChunk → List Bool
  | [] => []
  | c::cs => rightInput c ++ inputRightChunks cs

def outputRightChunks : List RightChunk → List Bool
  | [] => []
  | c::cs => outputRightChunks cs ++ rightOutput c

def rightScanCost : List RightChunk → Nat
  | [] => 0
  | c::cs => rightCost c + rightScanCost cs

theorem scanRightOne (c : RightChunk) (L R : List Bool) :
    run0 p (rightCost c)
      ⟨0,[false] ++ L,[false] ++ rightInput c ++ R⟩ =
      some ⟨0,[false] ++ rightOutput c ++ L,[false] ++ R⟩ := by
  cases c with
  | alternating =>
      simpa [rightCost,rightInput,rightOutput,Auto.extend,List.append_assoc] using
        Auto.knownRun_sound p 6 rightOne L R
  | separatedMarker =>
      simpa [rightCost,rightInput,rightOutput,Auto.extend,List.append_assoc] using
        Auto.knownRun_sound p 15 rightMarkerOne L R

/-- Exact all-length *rightward* scan for arbitrary words assembled
    from 10 and separated 11010 blocks. -/
theorem scanRightChunks (cs : List RightChunk) (L R : List Bool) :
    run0 p (rightScanCost cs)
      ⟨0,[false] ++ L,[false] ++ inputRightChunks cs ++ R⟩ =
      some ⟨0,[false] ++ outputRightChunks cs ++ L,[false] ++ R⟩ := by
  induction cs generalizing L with
  | nil =>
      simp [rightScanCost,inputRightChunks,outputRightChunks,run0]
  | cons c cs ih =>
      have h1 := scanRightOne c L (inputRightChunks cs ++ R)
      have h2 := ih (rightOutput c ++ L)
      have h := join0 h1 h2
      simpa only [rightScanCost,inputRightChunks,outputRightChunks,
        List.cons_append,List.nil_append,List.append_assoc] using h


/-- The three-step E1 entry from the section boundary. It deposits
    1110 on the right and starts the long leftward C0 scan. -/
theorem entryOne :
    Auto.knownRun p 3 ⟨4,[true,false],[false,true,false]⟩ =
      some ⟨2,[false],[true,true,true,false]⟩ := by decide +kernel

/-- Left reversal after scanning all marked chunks when a leading A
    separator was present. -/
theorem leftEndPositive :
    Auto.knownRun p 1 ⟨2,[false,false],[]⟩ =
      some ⟨0,[false],[false]⟩ := by decide +kernel

/-- Left reversal when the initial 110 marker has *no* leading A
    separator. The moving head reaches two blank cells left of the
    original finite support, and creates one new 1 on the way. -/
theorem leftEndZero :
    Auto.knownRun p 4 ⟨2,[false,true,true,false,false],[]⟩ =
      some ⟨0,[false],[true,false,true,false]⟩ := by decide +kernel

/-- Arbitrarily many separated markers and A blocks: E1 reaches the
    first blank A0 reversal in exactly 3+scanCost(cs)+1 source steps,
    uniformly for ALL untouched tape tails L,R. -/
theorem halfSweepPositive (cs : List LeftChunk) (L R : List Bool) :
    run0 p (3 + (scanCost cs + 1))
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
         [false,true,false] ++ R⟩ =
    some ⟨0,[false] ++ L,
            [false] ++ outputBits cs ++ [true,true,true,false] ++ R⟩ := by
  have h1 : run0 p 3
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
         [false,true,false] ++ R⟩ =
      some ⟨2,[false] ++ inputBits cs ++ [false] ++ L,
               [true,true,true,false] ++ R⟩ := by
    simpa only [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 3 entryOne (inputBits cs ++ [false] ++ L) R
  have h2 : run0 p (scanCost cs)
      ⟨2,[false] ++ inputBits cs ++ [false] ++ L,
         [true,true,true,false] ++ R⟩ =
      some ⟨2,[false] ++ [false] ++ L,
               outputBits cs ++ [true,true,true,false] ++ R⟩ := by
    simpa [List.append_assoc] using
      scanChunks cs ([false] ++ L) ([true,true,true,false] ++ R)
  have h3 : run0 p 1
       ⟨2,[false] ++ [false] ++ L,
          outputBits cs ++ [true,true,true,false] ++ R⟩ =
       some ⟨0,[false] ++ L,
                [false] ++ outputBits cs ++ [true,true,true,false] ++ R⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 1 leftEndPositive L
         (outputBits cs ++ [true,true,true,false] ++ R)
  have h := join0 h1 (join0 h2 h3)
  simpa only [List.append_assoc] using h

/-- Symmetric boundary case with NO leading A before the first 110
    marker. The final left reversal consumes the unguarded initial 110,
    creates a new support cell, and never evaluates the missing F1. -/
theorem halfSweepZero (cs : List LeftChunk) (L R : List Bool) :
    run0 p (3 + (scanCost cs + 4))
      ⟨4,[true,false] ++ inputBits cs ++ [true,true,false,false] ++ L,
         [false,true,false] ++ R⟩ =
    some ⟨0,[false] ++ L,
            [true,false,true,false] ++ outputBits cs ++ [true,true,true,false] ++ R⟩ := by
  have h1 : run0 p 3
      ⟨4,[true,false] ++ inputBits cs ++ [true,true,false,false] ++ L,
         [false,true,false] ++ R⟩ =
      some ⟨2,[false] ++ inputBits cs ++ [true,true,false,false] ++ L,
               [true,true,true,false] ++ R⟩ := by
    simpa only [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 3 entryOne (inputBits cs ++ [true,true,false,false] ++ L) R
  have h2 : run0 p (scanCost cs)
      ⟨2,[false] ++ inputBits cs ++ [true,true,false,false] ++ L,
         [true,true,true,false] ++ R⟩ =
      some ⟨2,[false] ++ [true,true,false,false] ++ L,
               outputBits cs ++ [true,true,true,false] ++ R⟩ := by
    simpa [List.append_assoc] using
      scanChunks cs ([true,true,false,false] ++ L) ([true,true,true,false] ++ R)
  have h3 : run0 p 4
       ⟨2,[false] ++ [true,true,false,false] ++ L,
          outputBits cs ++ [true,true,true,false] ++ R⟩ =
       some ⟨0,[false] ++ L,
               [true,false,true,false] ++ outputBits cs ++ [true,true,true,false] ++ R⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 4 leftEndZero L
         (outputBits cs ++ [true,true,true,false] ++ R)
  have h := join0 h1 (join0 h2 h3)
  simpa only [List.append_assoc] using h


/-- Reinterpret a left-transfer chunk as an equivalent right-transfer
    chunk. Both scans consume the same source-side bit sequence. -/
def toRight : LeftChunk → RightChunk
  | .alternating => .alternating
  | .separatedMarker => .separatedMarker

/-- The leftward scan emits its chunks in reverse order, so the
    subsequent rightward scan must consume them in this order. -/
def rightSequence : List LeftChunk → List RightChunk
  | [] => []
  | c::cs => rightSequence cs ++ [toRight c]

theorem rightInput_append (xs ys : List RightChunk) :
    inputRightChunks (xs ++ ys) =
      inputRightChunks xs ++ inputRightChunks ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append,inputRightChunks,List.append_assoc,ih]

theorem rightCost_append (xs ys : List RightChunk) :
    rightScanCost (xs ++ ys) =
      rightScanCost xs + rightScanCost ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append,rightScanCost,ih,Nat.add_assoc]

theorem rightSequenceInput (cs : List LeftChunk) :
    inputRightChunks (rightSequence cs) = outputBits cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [rightSequence,outputBits,rightInput_append,
        inputRightChunks,ih,List.nil_append]
      cases c <;> rfl

theorem rightSequenceCost (cs : List LeftChunk) :
    rightScanCost (rightSequence cs) = 3 * scanCost cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [rightSequence,scanCost,rightCost_append,
        rightScanCost,ih,List.nil_append]
      cases c <;> simp [toRight,rightCost,chunkCost] <;> omega

/-- The complete *first bidirectional round*: for arbitrary mixed
    10 and separated 110 markers, exact E1 source execution reaches
    A0 at the right-hand triple-one 1110 sentinel, with an exact
    linear step count (4 + 4 * scanCost cs). -/
theorem firstRoundPositive (cs : List LeftChunk) (L R : List Bool) :
    run0 p (4 + 4 * scanCost cs)
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
         [false,true,false] ++ R⟩ =
    some ⟨0,[false] ++ outputRightChunks (rightSequence cs) ++ L,
            [false] ++ [true,true,true,false] ++ R⟩ := by
  have h1 := halfSweepPositive cs L R
  have h2 := scanRightChunks (rightSequence cs) L ([true,true,true,false] ++ R)
  rw [rightSequenceInput] at h2
  have h := join0 h1 h2
  have ht : (3 + (scanCost cs + 1)) +
      rightScanCost (rightSequence cs) = 4 + 4 * scanCost cs := by
    rw [rightSequenceCost]
    omega
  simpa only [ht,List.append_assoc] using h


/-- Exact 147-step bridge from the all-zero blank tape into the first
    10/110 section. This is finite original-table computation only. -/
def blankChunks : List LeftChunk :=
  [.alternating,.alternating,.separatedMarker,.alternating,.alternating]

theorem blank147 :
    runP p 147 startP = some ⟨4,10965,2⟩ := by decide +kernel

theorem blank147Shape :
    runP p 147 startP =
      some ⟨4,
        pack ([true,false] ++ inputBits blankChunks ++ [false]),
        pack [false,true,false]⟩ := by decide +kernel


/-- Thirteen-step local E-hop gadget. From the A0 head at the 1110
    temporary sentinel, with exactly one following 110 marker, the
    machine reaches a fresh E1 with right neighbor zero. The rule
    is checked by the finite original-table known-run kernel. -/
theorem markedEdge13 :
    Auto.knownRun p 13
      ⟨0,[false],[false,true,true,true,false,true,true,false]⟩ =
    some ⟨4,[true,false,true,false,true,false,true,true],[false]⟩ := by
  decide +kernel

/-- Universal E-to-E marked hop: arbitrary marker-bearing left prefix,
    at least one final 10 followed by 110 on the right, arbitrary L,R.
    The returned E reads 1, its immediate right bit is 0, and every
    step on the way is defined (so never uses the F1 hole).
    Arithmetic cost is EXACT: 17 + 4 * scanCost(cs). -/
theorem markedHop (cs : List LeftChunk) (L R : List Bool) :
    run0 p ((4 + 4 * scanCost cs) + 13)
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
         [false,true,false,true,true,false] ++ R⟩ =
    some ⟨4,[true,false,true,false,true,false,true,true] ++
              outputRightChunks (rightSequence cs) ++ L,
            [false] ++ R⟩ := by
  have h1 := firstRoundPositive cs L ([true,true,false] ++ R)
  have h2 := Auto.knownRun_sound p 13 markedEdge13
    (outputRightChunks (rightSequence cs) ++ L) R
  have h := join0 h1 h2
  simpa only [List.append_assoc] using h

#print axioms markedEdge13
#print axioms markedHop

#print axioms blank147
#print axioms blank147Shape

#print axioms rightSequenceInput
#print axioms rightSequenceCost
#print axioms firstRoundPositive

#print axioms entryOne
#print axioms leftEndPositive
#print axioms leftEndZero
#print axioms halfSweepPositive
#print axioms halfSweepZero

#print axioms rightMarkerOne
#print axioms scanRightOne
#print axioms scanRightChunks

#print axioms leftMarkerOne
#print axioms scanOne
#print axioms scanChunks

#print axioms leftOne
#print axioms transparentLeft
#print axioms rightOne
#print axioms transparentRight
end BB6.Agent5Q0148BoundarySweep
