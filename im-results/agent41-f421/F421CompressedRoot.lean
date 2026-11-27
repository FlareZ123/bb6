import F421CompressedTrace
import F421SecondaryExact

namespace BB6Coverage.Agent41F421.Compressed
open BB6Coverage Agent31Pump Agent50Zipper EpochWords

private theorem getDZero (n i : Nat) :
    (rep [false,false] n).getD i false = false := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => exact ih i

private theorem appendZero (w : List Bool) (n i : Nat) :
    (w++rep [false,false] n).getD i false = w.getD i false := by
  induction w generalizing i with
  | nil => rw [List.nil_append,getDZero]; cases i <;> rfl
  | cons a as ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem embedPad (q : Fin 6) (pos : Int) (left right : List Bool) (n : Nat) :
    embed ⟨q,pos,left++rep [false,false] n,right⟩ = embed ⟨q,pos,left,right⟩ := by
  unfold embed
  congr 1
  funext i
  simp only [atCell,appendZero]

def initial (pad : Nat) : Packed :=
  ⟨none, [(⟨true,false⟩,1),(⟨false,true⟩,3),(⟨false,false⟩,pad)]⟩

/-- The 24-step primitive entry, with arbitrarily many explicit left blank pairs. -/
theorem blankInitial (m : Machine) (hm : compatible table m) (pad : Nat) :
    run m 24 blank = some (embed ⟨3,4,(initial pad).word,[true]⟩) := by
  rw [← start_embed]
  have hi : (initial pad).word = [true,false,false,true,false,true,false,true]++rep [false,false] pad := by
    simp [initial,Packed.word,decode,Bits.word]
    rfl
  rw [hi]
  rw [embedPad]
  exact zrun_sound table m hm 24 start _ rfl

theorem followFrontier (m : Machine) (hm : compatible table m) (n bound : Nat) (pos : Int)
    (u v : List Bool) (h0 : run m n blank = some (embed ⟨3,pos,u,[true]⟩))
    (h : reaches bound u v) :
    ∃ k nextPos, n+bound ≤ k ∧ run m k blank = some (embed ⟨3,nextPos,v,[true]⟩) := by
  obtain ⟨k,hk,hr⟩ := h
  let z : Z := ⟨3,pos,u,[true]⟩
  obtain ⟨z',hz',hs⟩ := originalRun m hm k z (frontier v) hr
  have hq : z'.q=3 := congrArg Z0.q hz'
  have hl : z'.l=v := congrArg Z0.l hz'
  have hright : z'.r=[true] := congrArg Z0.r hz'
  refine ⟨n+k,z'.h,by omega,?_⟩
  rw [run_append,h0]
  change run m k (embed z) = _
  rw [hs]
  congr 2
  cases z'
  simp_all

theorem blankFollow (m : Machine) (hm : compatible table m) (pad bound : Nat) (v : List Bool)
    (h : reaches bound (initial pad).word v) :
    ∃ n pos, (24+bound) ≤ n ∧ run m n blank = some (embed ⟨3,pos,v,[true]⟩) :=
  followFrontier m hm 24 bound 4 _ v (blankInitial m hm pad) h

def srowPieces (c : TC) : List Piece :=
  (if c.f then [zeroPair] else []) ++ [qRun c.z,pRun c.r]

theorem srowPiecesWord (c : TC) : spell (srowPieces c) = scell c := by
  cases c with
  | mk z r f =>
    cases f <;> simp [srowPieces,scell,spell,Piece.word,pRun,qRun,zeroPair,
      Regular.P,Regular.Q,Regular.Z,Bits.word,rep]

theorem srowsPiecesWord (cs : List TC) :
    spell (cs.flatMap srowPieces) = cs.flatMap scell := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons,spellAppend,srowPiecesWord,ih]

def seedPieces (a b x y : Nat) (cs : List PC) (xs : List TC) (suffix : List Piece) : List Piece :=
  [pRun a,qRun b] ++ (MergedDrain.rows false cs).reverse.flatMap rowPieces ++
    [pRun x,zeroPair,pRun y] ++ xs.flatMap srowPieces ++ suffix

theorem seedPiecesWord (a b x y : Nat) (cs : List PC) (xs : List TC) (suffix : List Piece) :
    spell (seedPieces a b x y cs xs suffix) = sbody a b x y cs xs (spell suffix) := by
  have leading : spell [pRun a,qRun b] = rep Regular.P a ++ rep Regular.Q b := by
    simp [spell,Piece.word,pRun,qRun,Regular.P,Regular.Q,Bits.word]
  have body : spell [pRun x,zeroPair,pRun y] = rep Regular.P x ++ Regular.Z ++ rep Regular.P y := by
    simp [spell,Piece.word,pRun,zeroPair,Regular.P,Regular.Z,Bits.word,Agent31Pump.rep]
  simp only [seedPieces,sbody,spellAppend,leading,body,rowsPiecesWord,srowsPiecesWord,
    MergedDrain.word,GeneralDrain.farWord,stail,List.append_assoc]

#print axioms blankFollow
#print axioms seedPiecesWord
end BB6Coverage.Agent41F421.Compressed
