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
  | nil => simp [rightScanCost]
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
  have h2 : run0 p (rightScanCost (rightSequence cs))
       ⟨0,[false] ++ L,[false] ++ outputBits cs ++ [true,true,true,false] ++ R⟩ =
       some ⟨0,[false] ++ outputRightChunks (rightSequence cs) ++ L,
                 [false] ++ [true,true,true,false] ++ R⟩ := by
    simpa [rightSequenceInput,List.append_assoc] using
      scanRightChunks (rightSequence cs) L ([true,true,true,false] ++ R)
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
  simpa [Auto.extend,List.append_assoc] using h


/-- The right boundary's 1110 sentinel is processed in nine original
    steps, reaching control E0 with the final 10 still on the right. -/
theorem rightToEZero :
    Auto.knownRun p 9 ⟨0,[false],[false,true,true,true,false]⟩ =
      some ⟨4,[false,false,true,true],[true,false]⟩ := by
  decide +kernel

/-- Two-step rightward E0 scan across each additional 10 token. -/
theorem rightEAlternating :
    Auto.knownRun p 2 ⟨4,[false],[true,false]⟩ =
      some ⟨4,[false,false,true],[]⟩ := by
  decide +kernel

/-- Two-step rightward E0 scan across the first two 1s of a marker 110:
    the result is E1 with its immediate right neighbor still zero. -/
theorem rightEMarker :
    Auto.knownRun p 2 ⟨4,[false],[true,true]⟩ =
      some ⟨4,[true,false,true],[]⟩ := by
  decide +kernel

/-- All-length source computation: arbitrary number of 10 tokens
    transfers rightwards through the two-state E0/B1 cycle. -/
theorem rightEAltSweep (n : Nat) (L R : List Bool) :
    run0 p (2*n)
      ⟨4,[false] ++ L,rep [true,false] n ++ R⟩ =
    some ⟨4,[false] ++ rep [false,true] n ++ L,R⟩ := by
  have one (l r : List Bool) :
      run0 p 2 ⟨4,[false] ++ l,[true,false] ++ r⟩ =
      some ⟨4,[false] ++ [false,true] ++ l,r⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 2 rightEAlternating l r
  simpa [List.append_assoc] using
    sweepR p 4 [false] [] [true,false] [false,true] 2 one n L R

/-- The complete right-edge transfer over ANY positive-length A-run
    immediately followed by a 110 marker. E0 scans n extra A tokens
    before reaching E1 on the marker; duration exactly 13 + 2*n. -/
theorem rightContinuation (n : Nat) (L R : List Bool) :
    run0 p (13+2*n)
      ⟨0,[false] ++ L,
        [false,true,true,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
    some ⟨4,
      [true,false,true] ++ rep [false,true] (n+1) ++
        [false,true,true] ++ L,
      [false] ++ R⟩ := by
  have h1 : run0 p 9
      ⟨0,[false] ++ L,
         [false,true,true,true,false] ++ rep [true,false] n ++
           [true,true,false] ++ R⟩ =
      some ⟨4,[false,false,true,true] ++ L,
           rep [true,false] (n+1) ++ [true,true,false] ++ R⟩ := by
    simpa [Auto.extend,rep,List.append_assoc] using
      Auto.knownRun_sound p 9 rightToEZero L
        (rep [true,false] n ++ [true,true,false] ++ R)
  have h2 : run0 p (2*(n+1))
      ⟨4,[false,false,true,true] ++ L,
         rep [true,false] (n+1) ++ [true,true,false] ++ R⟩ =
      some ⟨4,[false] ++ rep [false,true] (n+1) ++
                   [false,true,true] ++ L,
                [true,true,false] ++ R⟩ := by
    simpa [List.append_assoc] using
      rightEAltSweep (n+1) ([false,true,true] ++ L) ([true,true,false] ++ R)
  have h3 : run0 p 2
      ⟨4,[false] ++ rep [false,true] (n+1) ++
          [false,true,true] ++ L,[true,true,false] ++ R⟩ =
      some ⟨4,[true,false,true] ++ rep [false,true] (n+1) ++
          [false,true,true] ++ L,[false] ++ R⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p 2 rightEMarker
        (rep [false,true] (n+1) ++ [false,true,true] ++ L) ([false] ++ R)
  have h := join0 h1 (join0 h2 h3)
  have ht : 9 + (2*(n+1) + 2) = 13 + 2*n := by omega
  simpa only [ht,List.append_assoc] using h

/-- Generalized marked E1 -> E1 macro: there can be *any* number
    n of extra 10 tokens between the E-head's next 10 token and
    the following 110 marker. Source-defined for all n,cs,L,R. -/
theorem markedHopN (cs : List LeftChunk) (n : Nat) (L R : List Bool) :
    run0 p ((4 + 4 * scanCost cs) + (13 + 2*n))
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
        [false,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
    some ⟨4,[true,false,true] ++ rep [false,true] (n+1) ++
        [false,true,true] ++ outputRightChunks (rightSequence cs) ++ L,
         [false] ++ R⟩ := by
  have h1 := firstRoundPositive cs L
    (rep [true,false] n ++ [true,true,false] ++ R)
  have h2 := rightContinuation n
    (outputRightChunks (rightSequence cs) ++ L) R
  have h := join0 h1 h2
  simpa [List.append_assoc] using h

#print axioms rightToEZero
#print axioms rightEAlternating
#print axioms rightEMarker
#print axioms rightEAltSweep
#print axioms rightContinuation
#print axioms markedHopN


/-- The alternative 13-step right-end gadget, valid when the 1110
    sentinel is followed by two additional blank zeros instead of a
    110 marker. It changes direction to a leftward C0 scan. -/
theorem rightBlank13 :
    Auto.knownRun p 13
      ⟨0,[false],[false,true,true,true,false,false,false]⟩ =
    some ⟨2,[false,true,true,false,true,false,true,true],[]⟩ := by
  decide +kernel

/-- Source-defined first expansion turn at the blank right boundary,
    for ARBITRARILY LONG prefixed A/B-marker words and arbitrary
    untouched outer tails. This is the other major branch of the
    q0-148 boundary grammar: unlike marker-followed hops, it lands in
    C0 rather than E1 and thus needs a subsequent leftward sweep. -/
theorem rightBlankTurn (cs : List LeftChunk) (L R : List Bool) :
    run0 p ((4 + 4 * scanCost cs) + 13)
      ⟨4,[true,false] ++ inputBits cs ++ [false] ++ L,
         [false,true,false,false,false] ++ R⟩ =
    some ⟨2,[false,true,true,false,true,false,true,true] ++
          outputRightChunks (rightSequence cs) ++ L,R⟩ := by
  have h1 := firstRoundPositive cs L ([false,false] ++ R)
  have h2 := Auto.knownRun_sound p 13 rightBlank13
    (outputRightChunks (rightSequence cs) ++ L) R
  have h := join0 h1 h2
  simpa [Auto.extend,List.append_assoc] using h


/-- Regular right-sweep output as a substitution in the original chunk
    order. A:10 -> 01, M:11010 -> 01011. -/
def rightSubst : List LeftChunk → List Bool
  | [] => []
  | c::cs => rightOutput (toRight c) ++ rightSubst cs

theorem outputRightChunks_append (xs ys : List RightChunk) :
    outputRightChunks (xs ++ ys) =
      outputRightChunks ys ++ outputRightChunks xs := by
  induction xs with
  | nil => simp [outputRightChunks]
  | cons c cs ih =>
      simp only [List.cons_append,outputRightChunks,ih,List.append_assoc]

theorem outputRightChunks_rightSeq (cs : List LeftChunk) :
    outputRightChunks (rightSequence cs) = rightSubst cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [rightSequence,rightSubst,outputRightChunks_append,
        outputRightChunks,ih,List.nil_append]
      cases c <;> rfl

theorem inputBits_append (xs ys : List LeftChunk) :
    inputBits (xs ++ ys) = inputBits xs ++ inputBits ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append,inputBits,ih,List.append_assoc]

/-- Only three one-sided carry residues are possible when processing
    the right-sweep output, regardless of how many arbitrary markers
    the source tape contains. -/
inductive Carry where
  | eleven
  | elevenZeroOne
  | one
  deriving DecidableEq,Repr

def carryBits : Carry → List Bool
  | .eleven => [true,true]
  | .elevenZeroOne => [true,true,false,true]
  | .one => [true]

/-- Finite-state word transducer. Its six clauses are all exact
    bit-string identities, not empirical classifications. -/
def carryStep : Carry → LeftChunk → List LeftChunk × Carry
  | .eleven,.alternating => ([],.elevenZeroOne)
  | .eleven,.separatedMarker => ([.separatedMarker],.eleven)
  | .elevenZeroOne,.alternating => ([.separatedMarker],.one)
  | .elevenZeroOne,.separatedMarker => ([.separatedMarker,.alternating],.eleven)
  | .one,.alternating => ([.alternating],.one)
  | .one,.separatedMarker => ([.alternating,.alternating],.eleven)

theorem carryStepBits (carry : Carry) (chunk : LeftChunk) :
    carryBits carry ++ rightOutput (toRight chunk) =
      inputBits (carryStep carry chunk).1 ++
        carryBits (carryStep carry chunk).2 := by
  cases carry <;> cases chunk <;> rfl

def carryFold (carry : Carry) : List LeftChunk → (List LeftChunk × Carry)
  | [] => ([],carry)
  | c::cs =>
      let step := carryStep carry c
      let rest := carryFold step.2 cs
      (step.1 ++ rest.1, rest.2)

/-- Whole-list three-residue transducer identity, with no limit on the
    length of the source alternating/separated-marker word. -/
theorem carryFoldBits (carry : Carry) (cs : List LeftChunk) :
    carryBits carry ++ rightSubst cs =
      inputBits (carryFold carry cs).1 ++ carryBits (carryFold carry cs).2 := by
  induction cs generalizing carry with
  | nil => simp [carryFold,rightSubst,inputBits]
  | cons c cs ih =>
      have hStep := carryStepBits carry c
      have hTail := ih (carryStep carry c).2
      change carryBits carry ++
          (rightOutput (toRight c) ++ rightSubst cs) =
        inputBits ((carryStep carry c).1 ++
          (carryFold (carryStep carry c).2 cs).1) ++
        carryBits (carryFold (carryStep carry c).2 cs).2
      calc
        carryBits carry ++ (rightOutput (toRight c) ++ rightSubst cs)
            = (inputBits (carryStep carry c).1 ++
                carryBits (carryStep carry c).2) ++ rightSubst cs := by
                    rw [← List.append_assoc,hStep]
        _ = inputBits (carryStep carry c).1 ++
              (inputBits (carryFold (carryStep carry c).2 cs).1 ++
               carryBits (carryFold (carryStep carry c).2 cs).2) := by
                    rw [List.append_assoc,hTail]
        _ = inputBits ((carryStep carry c).1 ++
              (carryFold (carryStep carry c).2 cs).1) ++
              carryBits (carryFold (carryStep carry c).2 cs).2 := by
                    rw [inputBits_append,List.append_assoc]

/-- The full C0 left input after the blank-right 13-step turn consists
    of an arbitrary, transduced sequence of 10/11010 blocks followed
    by exactly one of THREE bounded residual bit strings. -/
theorem rightBlankCarryShape (cs : List LeftChunk) :
    [false,true,true,false,true,false,true,true] ++
      outputRightChunks (rightSequence cs) =
    [false] ++ inputBits
       (.separatedMarker :: (carryFold .eleven cs).1) ++
      carryBits (carryFold .eleven cs).2 := by
  have h := congrArg
    (fun v : List Bool => [false,true,true,false,true,false] ++ v)
    (carryFoldBits Carry.eleven cs)
  simpa [outputRightChunks_rightSeq,inputBits,carryBits,List.append_assoc] using h

/-- All three exceptional left-edge residues are handled by fixed
    original-table runs. No infinite search is required. -/
def carryCost : Carry → Nat
  | .eleven => 4
  | .elevenZeroOne => 6
  | .one => 3

def carryRight : Carry → List Bool
  | .eleven => [true,false,true,false]
  | .elevenZeroOne => [false,true,true,false,true,false]
  | .one => [false,true,false]

theorem carryTerminal (carry : Carry) :
    Auto.knownRun p (carryCost carry)
      ⟨2,[false] ++ carryBits carry ++ [false,false],[]⟩ =
      some ⟨0,[false],carryRight carry⟩ := by
  cases carry <;> decide +kernel

/-- TWO COMPLETE bidirectional sweeps from an E1 checkpoint at the
    far-right blank boundary; source-defined and finite for any list
    of the arbitrary A/M grammar chunks. The total duration is given
    by closed computations of scanCost and a 3-state transducer. -/
theorem twoBlankTurns (cs : List LeftChunk) (L R : List Bool) :
    let f := carryFold .eleven cs
    let chunks := LeftChunk.separatedMarker :: f.1
    run0 p (((4 + 4*scanCost cs) + 13) +
        (scanCost chunks + carryCost f.2))
      ⟨4,[true,false] ++ inputBits cs ++ [false,false,false] ++ L,
         [false,true,false,false,false] ++ R⟩ =
      some ⟨0,[false] ++ L,
              carryRight f.2 ++ outputBits chunks ++ R⟩ := by
  dsimp only
  let f := carryFold Carry.eleven cs
  let chunks := LeftChunk.separatedMarker :: f.1
  have h1 : run0 p ((4+4*scanCost cs)+13)
      ⟨4,[true,false] ++ inputBits cs ++ [false,false,false] ++ L,
         [false,true,false,false,false] ++ R⟩ =
      some ⟨2,[false] ++ inputBits chunks ++ carryBits f.2 ++
                    [false,false] ++ L,R⟩ := by
    simpa [f,chunks,rightBlankCarryShape,List.append_assoc] using
      rightBlankTurn cs ([false,false] ++ L) R
  have h2 : run0 p (scanCost chunks)
      ⟨2,[false] ++ inputBits chunks ++ carryBits f.2 ++
              [false,false] ++ L,R⟩ =
      some ⟨2,[false] ++ carryBits f.2 ++ [false,false] ++ L,
              outputBits chunks ++ R⟩ := by
    simpa [List.append_assoc] using
      scanChunks chunks (carryBits f.2 ++ [false,false] ++ L) R
  have h3 : run0 p (carryCost f.2)
      ⟨2,[false] ++ carryBits f.2 ++ [false,false] ++ L,
         outputBits chunks ++ R⟩ =
      some ⟨0,[false] ++ L,
           carryRight f.2 ++ outputBits chunks ++ R⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p (carryCost f.2)
         (carryTerminal f.2) L (outputBits chunks ++ R)
  have h := join0 h1 (join0 h2 h3)
  simpa [f,chunks,List.append_assoc] using h

#print axioms carryStepBits
#print axioms carryFoldBits
#print axioms rightBlankCarryShape
#print axioms carryTerminal

/-- Generic right-end blank-only reversal after an ordinary token
    sweep (contrasting with the 13-step triple-1110 right gadget). -/
theorem rightEdgeTwo :
    Auto.knownRun p 2 ⟨0,[false],[false,false]⟩ =
      some ⟨2,[false,true,true],[]⟩ := by
  decide +kernel

theorem rightSubst_append (xs ys : List LeftChunk) :
    rightSubst (xs ++ ys) = rightSubst xs ++ rightSubst ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append,rightSubst,ih,List.append_assoc]

/-- After a right scan of a new token followed by all old chunks,
    the left-facing C0 sees precisely the right-substitution image
    of the old list with the new token appended. -/
theorem secondRightOutput (tok : LeftChunk) (chunks : List LeftChunk) :
    outputRightChunks (toRight tok :: rightSequence chunks) =
      rightSubst (chunks ++ [tok]) := by
  simp [outputRightChunks,outputRightChunks_rightSeq,
        rightSubst_append,rightSubst]

theorem secondCarryShape (tok : LeftChunk) (chunks : List LeftChunk) :
    [false,true,true] ++
      outputRightChunks (toRight tok :: rightSequence chunks) =
    [false] ++ inputBits
      (carryFold .eleven (chunks ++ [tok])).1 ++
      carryBits (carryFold .eleven (chunks ++ [tok])).2 := by
  have h := congrArg (fun v : List Bool => [false] ++ v)
      (carryFoldBits Carry.eleven (chunks ++ [tok]))
  simpa [secondRightOutput,carryBits,List.append_assoc] using h

/-- A **repeatable entire bidirectional boundary cycle**.
    If qA begins with 0 then ONE 10 or 11010 token, then a reversed
    arbitrary chunk list and blank right tail, exact original-source
    execution returns qA at the next blank left boundary.
    No F1 is used, regardless of the word's length. -/
theorem anotherBlankCycle (tok : LeftChunk) (chunks : List LeftChunk)
    (L R : List Bool) :
    let rs := toRight tok :: rightSequence chunks
    let f := carryFold .eleven (chunks ++ [tok])
    run0 p ((rightScanCost rs + 2) +
        (scanCost f.1 + carryCost f.2))
      ⟨0,[false,false,false] ++ L,
        [false] ++ chunkBits tok ++ outputBits chunks ++
          [false,false] ++ R⟩ =
    some ⟨0,[false] ++ L,
      carryRight f.2 ++ outputBits f.1 ++ [false] ++ R⟩ := by
  dsimp only
  let rs := toRight tok :: rightSequence chunks
  let f := carryFold Carry.eleven (chunks ++ [tok])
  have h1 : run0 p (rightScanCost rs)
      ⟨0,[false,false,false] ++ L,
        [false] ++ chunkBits tok ++ outputBits chunks ++
          [false,false] ++ R⟩ =
      some ⟨0,[false] ++ outputRightChunks rs ++
              [false,false] ++ L,[false,false,false] ++ R⟩ := by
    simpa [rs,rightSequenceInput,toRight,rightInput,
           List.append_assoc] using
      scanRightChunks rs ([false,false] ++ L) ([false,false] ++ R)
  have h2 : run0 p 2
      ⟨0,[false] ++ outputRightChunks rs ++
           [false,false] ++ L,[false,false,false] ++ R⟩ =
      some ⟨2,[false] ++ inputBits f.1 ++ carryBits f.2 ++
          [false,false] ++ L,[false] ++ R⟩ := by
    have h := Auto.knownRun_sound p 2 rightEdgeTwo
      (outputRightChunks rs ++ [false,false] ++ L) ([false] ++ R)
    simpa [Auto.extend,rs,f,secondCarryShape,List.append_assoc] using h
  have h3 : run0 p (scanCost f.1)
      ⟨2,[false] ++ inputBits f.1 ++ carryBits f.2 ++
              [false,false] ++ L,[false] ++ R⟩ =
      some ⟨2,[false] ++ carryBits f.2 ++
          [false,false] ++ L,
          outputBits f.1 ++ [false] ++ R⟩ := by
    simpa [List.append_assoc] using
      scanChunks f.1 (carryBits f.2 ++ [false,false] ++ L) ([false] ++ R)
  have h4 : run0 p (carryCost f.2)
      ⟨2,[false] ++ carryBits f.2 ++
           [false,false] ++ L,outputBits f.1 ++ [false] ++ R⟩ =
      some ⟨0,[false] ++ L,
          carryRight f.2 ++ outputBits f.1 ++ [false] ++ R⟩ := by
    simpa [Auto.extend,List.append_assoc] using
      Auto.knownRun_sound p (carryCost f.2) (carryTerminal f.2)
        L (outputBits f.1 ++ [false] ++ R)
  have h := join0 h1 (join0 h2 (join0 h3 h4))
  simpa [rs,f,Nat.add_assoc,List.append_assoc] using h


/-- Uniformly close an E0 right-sweep with the first 110 marker after
    any number of 10 tokens, without evaluating the missing transition. -/
theorem ERightFirstMarker (n : Nat) (L R : List Bool) :
    run0 p (2*n+2)
      ⟨4,[false] ++ L,rep [true,false] n ++ [true,true] ++ R⟩ =
    some ⟨4,[true,false,true] ++ rep [false,true] n ++ L,R⟩ := by
  have h1 := rightEAltSweep n L ([true,true] ++ R)
  have h2 := Auto.knownRun_sound p 2 rightEMarker
    (rep [false,true] n ++ L) R
  have h := join0 h1 h2
  simpa [Auto.extend,List.append_assoc,Nat.add_assoc] using h

/-- The left-edge A0 starts with 10 then reaches E0; any extra 10
    tokens before a 110 marker terminate in a safe E1. -/
theorem ARightFirstMarker :
    Auto.knownRun p 2 ⟨0,[false],[true,false]⟩ =
      some ⟨4,[false,false,true],[]⟩ := by
  decide +kernel

theorem ARightToEOne (n : Nat) (L R : List Bool) :
    run0 p (2*n+6)
      ⟨0,[false] ++ L,
        [true,false,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
    some ⟨4,[true,false,true] ++
          rep [false,true] (n+1) ++ [false,true] ++ L,
          [false] ++ R⟩ := by
  have h1 : run0 p 2
     ⟨0,[false] ++ L,
        [true,false,true,false] ++ rep [true,false] n ++
          [true,true,false] ++ R⟩ =
     some ⟨4,[false,false,true] ++ L,
              rep [true,false] (n+1) ++ [true,true,false] ++ R⟩ := by
    simpa [Auto.extend,rep,List.append_assoc] using
      Auto.knownRun_sound p 2 ARightFirstMarker L
       ([true,false] ++ rep [true,false] n ++ [true,true,false] ++ R)
  have h2 : run0 p (2*(n+1)+2)
      ⟨4,[false,false,true] ++ L,
         rep [true,false] (n+1) ++ [true,true,false] ++ R⟩ =
      some ⟨4,[true,false,true] ++ rep [false,true] (n+1) ++
                 [false,true] ++ L,[false] ++ R⟩ := by
    simpa [List.append_assoc] using
      ERightFirstMarker (n+1) ([false,true] ++ L) ([false] ++ R)
  have h := join0 h1 h2
  have ht : 2 + (2*(n+1)+2) = 2*n+6 := by omega
  simpa only [ht,List.append_assoc] using h

#print axioms ERightFirstMarker
#print axioms ARightFirstMarker
#print axioms ARightToEOne

#print axioms rightEdgeTwo
#print axioms secondCarryShape
#print axioms anotherBlankCycle

#print axioms twoBlankTurns

#print axioms rightBlank13
#print axioms rightBlankTurn

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
