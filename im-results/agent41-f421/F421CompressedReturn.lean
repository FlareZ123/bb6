import F421CompressedWord

namespace BB6Coverage.Agent41F421.Compressed
open Agent31Pump EpochWords
open Regular (fwords effect)

inductive LeftChunk where
  | manyA (n : Nat)
  | one (tok : Block)
  deriving Repr

def LeftChunk.blocks : LeftChunk → List Block
  | .manyA n => List.replicate n .a
  | .one tok => [tok]

def brackets (cs : List LeftChunk) : List Block := cs.flatMap LeftChunk.blocks

def LeftChunk.input : LeftChunk → List Piece
  | .manyA n => [.run ⟨true,false⟩ n]
  | .one tok => tok.inp.map .bit

def LeftChunk.output : LeftChunk → List Piece
  | .manyA n => [.run ⟨false,true⟩ n]
  | .one tok => tok.out.map .bit

theorem spellAppend (xs ys : List Piece) : spell (xs++ys) = spell xs++spell ys := by
  simp [spell]

theorem spellBits (bs : List Bool) : spell (bs.map .bit) = bs := by
  induction bs with
  | nil => rfl
  | cons v bs ih => simpa [spell,Piece.word] using congrArg (v :: ·) ih

theorem inputsWord (cs : List LeftChunk) : spell (cs.flatMap LeftChunk.input) = ins (brackets cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,spellAppend,brackets,Regular.insAppend] at *
    rw [ih]
    cases c with
    | manyA n => simp [LeftChunk.input,LeftChunk.blocks,spell,Piece.word,Regular.insA,Regular.P,Bits.word]
    | one tok => simp [LeftChunk.input,LeftChunk.blocks,spellBits,ins]

theorem outputsWord (cs : List LeftChunk) : spell (cs.flatMap LeftChunk.output) = outs (brackets cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,spellAppend,brackets,Regular.outsAppend] at *
    rw [ih]
    cases c with
    | manyA n => simp [LeftChunk.output,LeftChunk.blocks,spell,Piece.word,Regular.outsA,Regular.Q,Bits.word]
    | one tok => simp [LeftChunk.output,LeftChunk.blocks,spellBits,outs]

abbrev RightChunks := List (Pair × Nat)
def pairing (cs : RightChunks) : List Pair := cs.flatMap (fun (p,n) => List.replicate n p)

def Pair.inputBits : Pair → Bits
  | .z1 => ⟨true,false⟩
  | .o1 => ⟨true,true⟩
  | .o0 => ⟨false,true⟩

def Pair.outputBits : Pair → Bits
  | .z1 => ⟨true,false⟩
  | .o1 => ⟨false,false⟩
  | .o0 => ⟨false,true⟩

theorem fwordsRepeat (p : Pair) (n : Nat) :
    fwords (List.replicate n p)=rep (Pair.inputBits p).word n := by
  induction n with
  | zero => rfl
  | succ n ih => cases p <;> simp [List.replicate_succ,fwords,Pair.word,Pair.inputBits,Bits.word,rep,ih]

theorem effectRepeat (p : Pair) (n : Nat) :
    effect (List.replicate n p)=rep (Pair.outputBits p).word n := by
  induction n with
  | zero => rfl
  | succ n ih => cases p <;> simp [List.replicate_succ,effect,Pair.next,Pair.outputBits,Bits.word,rep,ih]

theorem pairInputsWord (cs : RightChunks) :
    spell (cs.map (fun (p,n) => .run (Pair.inputBits p) n)) = fwords (pairing cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨p,n⟩ := c
    simp only [List.map_cons, pairing,List.flatMap_cons,Regular.fwordsAppend,fwordsRepeat]
    change rep (Pair.inputBits p).word n ++ spell _ = rep (Pair.inputBits p).word n ++ fwords (pairing cs)
    rw [ih]

theorem pairOutputsWord (cs : RightChunks) :
    spell (cs.map (fun (p,n) => .run (Pair.outputBits p) n)) = effect (pairing cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨p,n⟩ := c
    simp only [List.map_cons, pairing,List.flatMap_cons,Regular.effectAppend,effectRepeat]
    change rep (Pair.outputBits p).word n ++ spell _ = rep (Pair.outputBits p).word n ++ effect (pairing cs)
    rw [ih]

structure Return where
  left : List LeftChunk
  turn : Turn
  right : RightChunks
  odd : Bool
  suffix : List Piece

def Return.before (w : Return) : List Piece :=
  w.left.flatMap LeftChunk.input ++ w.turn.inp.map .bit ++ w.suffix

def Return.after (w : Return) : List Piece :=
  [.run ⟨!w.odd,false⟩ 1] ++
  w.right.map (fun (p,n) => .run (Pair.outputBits p) n) ++
  [.run ⟨!w.turn.leftBit,w.turn.leftBit⟩ 1] ++ w.suffix

def Return.leftStream (w : Return) : List Piece :=
  .bit true :: (w.left.flatMap LeftChunk.output ++ w.turn.start.reverse.map .bit)

def Return.rightStream (w : Return) : List Piece :=
  (endStream w.odd).map .bit ++ w.right.map (fun (p,n) => .run (Pair.inputBits p) n) ++
  w.turn.pair.reverse.map .bit

def Return.cost (w : Return) : Nat :=
  (w.left.map (fun c => match c with | .manyA n => 2*n | .one tok => tok.inp.length)).sum +
  w.turn.inp.length + 2 + (w.right.map (fun (p,n) => p.cost*n)).sum + 2

theorem leftLength (cs : List LeftChunk) :
    (ins (brackets cs)).length =
      (cs.map (fun c => match c with | .manyA n => 2*n | .one tok => tok.inp.length)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [brackets,List.flatMap_cons,Regular.insAppend,List.length_append,List.map_cons,List.sum_cons] at *
    rw [ih]
    cases c with
    | manyA n => simp [LeftChunk.blocks,Regular.insA,Regular.repLength,Regular.P]
    | one tok => simp [LeftChunk.blocks,ins]

theorem rightCost (cs : RightChunks) :
    pairCost (pairing cs)= (cs.map (fun (p,n) => p.cost*n)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨p,n⟩ := c
    change pairCost (List.replicate n p ++ pairing cs) = p.cost*n + _
    rw [Regular.costAppend,Regular.costRep,ih]
    rfl

theorem Return.sound (w : Return) (h : pack w.leftStream = pack w.rightStream) :
    run0 table w.cost (frontier (spell w.before)) = some (frontier (spell w.after)) := by
  have hs := eqOfPack h
  change true :: spell (w.left.flatMap LeftChunk.output ++ w.turn.start.reverse.map .bit) = spell w.rightStream at hs
  simp only [Return.rightStream,spellAppend,spellBits,outputsWord,pairInputsWord] at hs
  change true :: (outs (brackets w.left) ++ w.turn.start.reverse) =
    endStream w.odd ++ fwords (pairing w.right) ++ w.turn.pair.reverse at hs
  have hc := congrArg List.reverse hs
  simp only [List.reverse_cons,List.reverse_append,List.reverse_reverse,Regular.fwordsReverse] at hc
  have hturn : (endStream w.odd).reverse = endStream w.odd := by cases w.odd <;> rfl
  rw [hturn] at hc
  have hret := frontierReturn (brackets w.left) w.turn (spell w.suffix) (pairing w.right).reverse w.odd
    (by simpa only [List.append_assoc] using hc)
  rw [Regular.costReverse,leftLength,rightCost,Regular.accEffect] at hret
  simp only [Return.cost,Return.before,Return.after,spellAppend,inputsWord,spellBits,pairOutputsWord,List.append_assoc]
  have singleton (p : Bits) : spell [.run p 1] = p.word := rfl
  simpa only [List.append_assoc,singleton,Bits.word,List.cons_append,List.nil_append] using hret

#print axioms Return.sound
end BB6Coverage.Agent41F421.Compressed
