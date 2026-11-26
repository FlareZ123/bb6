import SweepPumping

namespace BB6Coverage.Agent41F421
open BB6Coverage Agent31Pump Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | _,_ => none

inductive Block where | a | b | c deriving DecidableEq, Repr

def Block.inp : Block → List Bool
  | .a => [true,false]
  | .b => [true,true,false]
  | .c => [false,true,false]

def Block.out : Block → List Bool
  | .a => [false,true]
  | .b => [false,true,true]
  | .c => [true,false,true]

def ins : List Block → List Bool
  | [] => []
  | b::bs => b.inp ++ ins bs

def outs : List Block → List Bool
  | [] => []
  | b::bs => b.out ++ outs bs

theorem blockStep (b : Block) (L R : List Bool) :
    run0 table b.inp.length ⟨3,b.inp++L,R⟩ = some ⟨3,L,b.out.reverse++R⟩ := by
  cases b <;> rfl

theorem leftScan (bs : List Block) (L R : List Bool) :
    run0 table (ins bs).length ⟨3,ins bs++L,R⟩ = some ⟨3,L,(outs bs).reverse++R⟩ := by
  induction bs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    have H := join0 (blockStep b (ins bs++L) R) (ih (b.out.reverse++R))
    simpa only [ins,outs,List.length_append,List.reverse_append,List.append_assoc] using H

def Bconf (T s : List Bool) : Z0 := ⟨1,s.headD false::T,s.tail⟩
def frontier (u : List Bool) : Z0 := ⟨3,u,[true]⟩

inductive Turn where | d | e deriving DecidableEq, Repr

def Turn.inp : Turn → List Bool
  | .d => [false,false]
  | .e => [false,true,true]

def Turn.start : Turn → List Bool
  | .d => [true]
  | .e => [false,true]

def Turn.pair : Turn → List Bool
  | .d => [true,true]
  | .e => [false,true]

def Turn.leftBit : Turn → Bool
  | .d => true
  | .e => false

theorem turnStep (t : Turn) (U R : List Bool) :
    run0 table t.inp.length ⟨3,t.inp++U,R⟩ = some (Bconf (t.leftBit::U) (t.start++R)) := by
  cases t <;> rfl

theorem badStep (U R : List Bool) :
    run0 table 2 ⟨3,true::true::true::U,R⟩ = some ⟨5,true::U,[true,false]++R⟩ := by rfl

theorem badUndefined (U R : List Bool) :
    step0 table ⟨5,true::U,R⟩ = none := by rfl

theorem normalPair (a : Bool) (T s : List Bool) :
    run0 table 2 (Bconf T (a::true::s)) = some (Bconf (false::(!a)::T) s) := by
  cases a <;> rfl

theorem bouncePair (T s : List Bool) :
    run0 table 6 (Bconf (false::T) (true::false::s)) = some (Bconf (false::false::true::T) s) := by rfl

def endStream (odd : Bool) : List Bool := if odd then [true] else []
theorem finish (odd : Bool) (T : List Bool) :
    run0 table 2 (Bconf T (endStream odd)) = some (frontier ((!odd)::T)) := by
  cases odd <;> rfl

inductive Pair where | z1 | o1 | o0 deriving DecidableEq, Repr

def Pair.word : Pair → List Bool
  | .z1 => [false,true]
  | .o1 => [true,true]
  | .o0 => [true,false]

def Pair.cost : Pair → Nat
  | .o0 => 6
  | _ => 2

/-- T excludes the fixed nearest zero. -/
def Pair.next : Pair → List Bool → List Bool
  | .z1,T => true::false::T
  | .o1,T => false::false::T
  | .o0,T => false::true::T

def pairWords : List Pair → List Bool
  | [] => []
  | p::ps => p.word ++ pairWords ps

def pairCost : List Pair → Nat
  | [] => 0
  | p::ps => p.cost + pairCost ps

def acc : List Pair → List Bool → List Bool
  | [],T => T
  | p::ps,T => acc ps (p.next T)

theorem pairStep (p : Pair) (T s : List Bool) :
    run0 table p.cost (Bconf (false::T) (p.word++s)) = some (Bconf (false::p.next T) s) := by
  cases p <;> rfl

theorem rightScan (ps : List Pair) (T s : List Bool) :
    run0 table (pairCost ps) (Bconf (false::T) (pairWords ps++s)) = some (Bconf (false::acc ps T) s) := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih =>
    have H := join0 (pairStep p T (pairWords ps++s)) (ih (p.next T))
    simpa only [pairCost,pairWords,List.append_assoc,acc] using H

theorem turnFirst (t : Turn) (U R : List Bool) :
    run0 table 2 (Bconf (t.leftBit::U) (t.pair++R)) = some (Bconf (false::(!t.leftBit)::t.leftBit::U) R) := by
  cases t <;> rfl

/-- Exact frontier return for any finite valid parse and right-stream decomposition. -/
theorem frontierReturn (bs : List Block) (t : Turn) (U : List Bool) (ps : List Pair) (odd : Bool)
    (h : t.start++((outs bs).reverse++[true]) = t.pair++(pairWords ps++endStream odd)) :
    run0 table ((ins bs).length+t.inp.length+2+pairCost ps+2)
      (frontier (ins bs++t.inp++U)) =
    some (frontier ((!odd)::false::acc ps ((!t.leftBit)::t.leftBit::U))) := by
  have H1 := leftScan bs (t.inp++U) [true]
  have H2 := turnStep t U ((outs bs).reverse++[true])
  rw [h] at H2
  have H3 := turnFirst t U (pairWords ps++endStream odd)
  have H4 := rightScan ps ((!t.leftBit)::t.leftBit::U) (endStream odd)
  have H5 := finish odd (false::acc ps ((!t.leftBit)::t.leftBit::U))
  have H := join0 (join0 (join0 (join0 H1 H2) H3) H4) H5
  simpa only [frontier,List.append_assoc] using H

/-- No two adjacent zeros, with terminal 1 whenever nonempty. -/
def good : Bool → List Bool → Prop
  | prev,[] => prev = true
  | prev,a::s => (prev = true ∨ a = true) ∧ good a s

theorem goodWeaken (a : Bool) (s : List Bool) (h : good a s) : good true s := by
  cases s with
  | nil => rfl
  | cons b s => exact ⟨Or.inl rfl,h.2⟩

theorem pairDecompose (s : List Bool) (h : good true s) :
    ∃ ps odd, s = pairWords ps++endStream odd := by
  match s with
  | [] => exact ⟨[],false,rfl⟩
  | [a] =>
    have ha : a = true := h.2
    subst a
    exact ⟨[],true,rfl⟩
  | a::b::s =>
    obtain ⟨ps,odd,he⟩ := pairDecompose s (goodWeaken b s h.2.2)
    cases a <;> cases b
    · exact False.elim (by simpa [good] using h.2.1)
    · exact ⟨.z1::ps,odd,by simp [pairWords,Pair.word,he]⟩
    · exact ⟨.o0::ps,odd,by simp [pairWords,Pair.word,he]⟩
    · exact ⟨.o1::ps,odd,by simp [pairWords,Pair.word,he]⟩
termination_by s.length

theorem goodOut (bs : List Block) (R : List Bool) (h : good true (true::R)) :
    ∃ S, (outs bs).reverse++true::R = true::S ∧ good true (true::S) := by
  induction bs generalizing R with
  | nil => exact ⟨R,rfl,h⟩
  | cons b bs ih =>
    have h' : ∃ S, b.out.reverse++true::R = true::S ∧ good true (true::S) := by
      cases b with
      | a => exact ⟨false::true::R,rfl,by simp [good] at *; exact h⟩
      | b => exact ⟨true::false::true::R,rfl,by simp [good] at *; exact h⟩
      | c => exact ⟨false::true::true::R,rfl,by simp [good] at *; exact h⟩
    obtain ⟨S,he,hg⟩ := h'
    obtain ⟨T,ht,hgood⟩ := ih S hg
    exact ⟨T,by simpa only [outs,List.reverse_append,List.append_assoc,he] using ht,hgood⟩

theorem pairDecomposeTurn (bs : List Block) (t : Turn) :
    ∃ ps odd, t.start++((outs bs).reverse++[true]) = t.pair++(pairWords ps++endStream odd) := by
  obtain ⟨S,hS,hgood⟩ := goodOut bs [] (by simp [good])
  cases t with
  | d =>
    obtain ⟨ps,odd,he⟩ := pairDecompose S hgood.2
    exact ⟨ps,odd,by simp [Turn.start,Turn.pair,hS,he]⟩
  | e =>
    obtain ⟨ps,odd,he⟩ := pairDecompose (true::S) hgood
    exact ⟨ps,odd,by simp [Turn.start,Turn.pair,hS,he]⟩

theorem completeReturn (bs : List Block) (t : Turn) (U : List Bool) :
    ∃ n v, 0 < n ∧ run0 table n (frontier (ins bs++t.inp++U)) = some (frontier v) := by
  obtain ⟨ps,odd,h⟩ := pairDecomposeTurn bs t
  exact ⟨_,_,by omega,frontierReturn bs t U ps odd h⟩

theorem badFrontier (bs : List Block) (U : List Bool) :
    run0 table ((ins bs).length+2) (frontier (ins bs++[true,true,true]++U)) =
      some ⟨5,true::U,[true,false]++(outs bs).reverse++[true]⟩ := by
  have H := join0 (leftScan bs (true::true::true::U) [true]) (badStep U ((outs bs).reverse++[true]))
  simpa only [frontier,List.append_assoc,List.cons_append,List.nil_append] using H

def parsed (w : List Bool) : Prop :=
    (∃ (bs : List Block) (t : Turn) (U : List Bool), w = ins bs++t.inp++U) ∨
    (∃ bs U, w = ins bs++[true,true,true]++U)

theorem prependBlock (b : Block) (w : List Bool) (h : parsed w) : parsed (b.inp++w) := by
  rcases h with ⟨bs,t,U,he⟩ | ⟨bs,U,he⟩
  · exact Or.inl ⟨b::bs,t,U,by simp only [ins,List.append_assoc,he]⟩
  · exact Or.inr ⟨b::bs,U,by simp only [ins,List.append_assoc,he]⟩

theorem parseComplete (w : List Bool) : parsed (w++[false,false,false]) := by
  match w with
  | [] => exact Or.inl ⟨[],.d,[false],rfl⟩
  | [a] =>
    cases a
    · exact Or.inl ⟨[],.d,[false,false],rfl⟩
    · exact Or.inl ⟨[.a],.d,[],rfl⟩
  | [a,b] =>
    cases a <;> cases b
    · exact Or.inl ⟨[],.d,[false,false,false],rfl⟩
    · exact Or.inl ⟨[.c],.d,[],rfl⟩
    · exact Or.inl ⟨[.a],.d,[false],rfl⟩
    · exact Or.inl ⟨[.b],.d,[],rfl⟩
  | a::b::c::w =>
    cases a <;> cases b <;> cases c
    · exact Or.inl ⟨[],.d,false::w++[false,false,false],rfl⟩
    · exact Or.inl ⟨[],.d,true::w++[false,false,false],rfl⟩
    · exact prependBlock .c _ (parseComplete w)
    · exact Or.inl ⟨[],.e,w++[false,false,false],rfl⟩
    · exact prependBlock .a _ (parseComplete (false::w))
    · exact prependBlock .a _ (parseComplete (true::w))
    · exact prependBlock .b _ (parseComplete w)
    · exact Or.inr ⟨[],w++[false,false,false],rfl⟩
termination_by w.length

theorem accFormula (ps : List Pair) (T : List Bool) :
    acc ps T = (ps.reverse.map (fun p => p.next [])).flatten ++ T := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih =>
    simp only [acc,ih,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_assoc,List.append_nil]
    cases p <;> rfl

theorem costFormula (ps : List Pair) : pairCost ps = 2*ps.length+4*ps.count .o0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p <;> simp [pairCost,Pair.cost,ih] <;> omega

theorem blankEntry : run0 table 3 ⟨0,[],[]⟩ = some (frontier [true,true]) := by rfl

/-- Lift any exact relative zipper execution through the original raw semantics. -/
theorem originalRun (m : Machine) (hm : compatible table m) (n : Nat) (z : Z) (v : Z0)
    (h : run0 table n (project z) = some v) :
    ∃ z', project z' = v ∧ run m n (embed z) = some (embed z') := by
  have H := run_project table n z
  rw [h] at H
  cases e : zrun table n z with
  | none => simp [e] at H
  | some z' =>
    exact ⟨z',by simpa [e] using H,zrun_sound table m hm n z z' e⟩

theorem originalBlankEntry (m : Machine) (hm : compatible table m) :
    run m 3 blank = some (embed ⟨3,1,[true,true],[true]⟩) := by
  rw [← start_embed]
  exact zrun_sound table m hm 3 start _ rfl

#print axioms frontierReturn
#print axioms completeReturn
#print axioms parseComplete
#print axioms badFrontier
#print axioms accFormula
#print axioms costFormula
#print axioms originalRun
#print axioms originalBlankEntry
end BB6Coverage.Agent41F421
