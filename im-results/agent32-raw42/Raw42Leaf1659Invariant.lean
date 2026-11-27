import Raw42Leaf1659
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RA.Leaf1659
open BB6Coverage BB6Coverage.Agent31Pump

def Bword : List Bool := [true,false,false,true,false]
def G (u v : List Bool) : Prop := ∀ a : Nat,
  Parse false a ([true,false] ++ u) (emitRun a ++ false::v)

inductive Phase where | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7
open Phase

def P : Phase → List Bool
  | p0 => [true,false,true,false,true,false,true,false,true,false,true,false]
  | p1 => [true,false,false,false,true,false,true,false,false,false,true,false]
  | p2 => [true,false,true,true,false,true,false,false,false,true,false]
  | p3 => [true,false,false,false,false,true,false,false,false,true,false]
  | p4 => [true,false,true,false,true,false,false,false,true,false]
  | p5 => [true,false,false,false,true,false,false,false,true,false]
  | p6 => [true,false,true,true,false,false,false,true,false]
  | p7 => [true,false,false,false,false,true,false,true,false,true,false,true,false]
def next : Phase → Phase
  | p0 => p1
  | p1 => p2
  | p2 => p3
  | p3 => p4
  | p4 => p5
  | p5 => p6
  | p6 => p7
  | p7 => p0
def active : Phase → Bool
  | p0 | p2 | p4 => true
  | _ => false
def plusBlock : Phase → Bool
  | p1 | p3 | p5 | p7 => true
  | _ => false
def phaseOut (i : Phase) := (if plusBlock i then Bword else []) ++ P (next i)
theorem G_block {u v : List Bool} (h : G u v) : G (Bword ++ u) (Bword ++ v) := by
  intro a
  simpa [Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (h 1)))
theorem G_phase {u v : List Bool} (h : G u v) (i : Phase) :
    G (P i ++ u) (phaseOut i ++ (if active i then v else u)) := by
  intro a
  cases i
  case p0 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.one (Parse.zero (Parse.more1010 (Parse.one (Parse.zero (h 2)))))))
  case p1 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero Parse.stop))
  case p2 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.one (Parse.one (Parse.zero (Parse.more100 (Parse.zero (h 2)))))))
  case p3 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero Parse.stop))
  case p4 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.one (Parse.zero (Parse.more100 (Parse.zero (h 2))))))
  case p5 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero Parse.stop))
  case p6 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.one (Parse.one (Parse.zero Parse.stop))))
  case p7 => simpa [P,phaseOut,plusBlock,active,next,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero Parse.stop))
def U : Phase → List Bool
  | p0 => [true,false,false,false,true,false,true,false,true]
  | p1 => [true,false,false,true,false,true,false,true,true,false,true,false,true]
  | p2 => [true,false,false,true,false,true,false,false,false,false,true,false,true,false,false,true,false,true,false,true]
  | p3 => [true,false,false,true,false,true,false,false,true,false,true,false,true,false,true,false,true,false,false,true,false,true,false,true]
  | p4 => [true,false,false,true,false,true,false,false,true,false,true,false,false,false,true,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true]
  | p5 => [true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,true,true,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true]
  | p6 => [true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,false,false,true,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true]
  | p7 => [true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,true,false,true,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true]
def seedOut : Phase → List Bool
  | p7 => Bword ++ Bword ++ Bword ++ Bword ++ P p5 ++ P p6 ++ U p0
  | i => U (next i)
theorem G_seed (i : Phase) : G (U i) (seedOut i) := by
  intro a
  cases i
  case p0 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero Parse.stop))
  case p1 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.one (Parse.one (Parse.zero (Parse.more101 (Parse.zeroEmpty Parse.stopEmpty))))))))
  case p2 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero Parse.stop))))
  case p3 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.one (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.one (Parse.zeroEmpty Parse.stopEmpty))))))))))))
  case p4 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero Parse.stop))))))
  case p5 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.one (Parse.one (Parse.zero (Parse.more100 (Parse.one (Parse.zero (Parse.more100 (Parse.zero (Parse.more1010 (Parse.one (Parse.zeroEmpty Parse.stopEmpty))))))))))))))))))
  case p6 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero Parse.stop))))))))
  case p7 => simpa [U,seedOut,next,P,Bword,emitRun,bits,rep,List.append_assoc] using (Parse.more1010 (a := a) (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.one (Parse.zero (Parse.more100 (Parse.zero Parse.stop)))))))))))))

inductive Lang : List Bool → Prop where
  | seed (i : Phase) : Lang (U i)
  | block {u : List Bool} : Lang u → Lang (Bword ++ u)
  | phase (i : Phase) {u : List Bool} : Lang u → Lang (P i ++ u)

theorem Lang.seedOut_mem (i : Phase) : Lang (seedOut i) := by
  cases i
  case p0 => exact Lang.seed p1
  case p1 => exact Lang.seed p2
  case p2 => exact Lang.seed p3
  case p3 => exact Lang.seed p4
  case p4 => exact Lang.seed p5
  case p5 => exact Lang.seed p6
  case p6 => exact Lang.seed p7
  case p7 => exact Lang.block (Lang.block (Lang.block (Lang.block (Lang.phase p5 (Lang.phase p6 (Lang.seed p0))))))

theorem Lang.phaseOut_mem (i : Phase) {u : List Bool} (h : Lang u) : Lang (phaseOut i ++ u) := by
  cases i
  case p0 => exact Lang.phase p1 h
  case p1 => exact Lang.block (Lang.phase p2 h)
  case p2 => exact Lang.phase p3 h
  case p3 => exact Lang.block (Lang.phase p4 h)
  case p4 => exact Lang.phase p5 h
  case p5 => exact Lang.block (Lang.phase p6 h)
  case p6 => exact Lang.phase p7 h
  case p7 => exact Lang.block (Lang.phase p0 h)

theorem Lang.closed {u : List Bool} (h : Lang u) : ∃ v, Lang v ∧ G u v := by
  induction h with
  | seed i => exact ⟨seedOut i, Lang.seedOut_mem i, G_seed i⟩
  | block hu ih =>
    obtain ⟨v,hv,hg⟩ := ih
    exact ⟨Bword ++ v,Lang.block hv,G_block hg⟩
  | phase i hu ih =>
    obtain ⟨v,hv,hg⟩ := ih
    refine ⟨phaseOut i ++ (if active i then v else _),Lang.phaseOut_mem i ?_,G_phase hg i⟩
    cases active i <;> assumption

-- TOP LEVEL
def H (u v : List Bool) : Prop := Parse true 0 (false::u) (false::true::false::v)

inductive TopPhase where | q0 | q1 | q2 | q3 | q4 | q5
open TopPhase

def Q : TopPhase → List Bool
  | q0 => [true,false,false,false,true,false,false,false,true,false] -- 1000100010
  | q1 => [false,false,true,false,false,false,true,false] -- 00100010
  | q2 => [true,false,true,false,true,false,false,false,true,false] -- 1010100010
  | q3 => [true,false,false,false,true,false,true,false,true,false,true,false] -- 100010101010
  | q4 => [false,false,true,false,true,false,false,false,true,false] -- 0010100010
  | q5 => [true,false,true,false,true,false,true,false,false,false,true,false] -- 101010100010
def topNext : TopPhase → TopPhase
  | q0 => q1
  | q1 => q2
  | q2 => q3
  | q3 => q4
  | q4 => q5
  | q5 => q0
def topActive : TopPhase → Bool
  | q0 | q3 | q5 => true
  | _ => false
theorem H_phase {u v : List Bool} (h : G u v) (i : TopPhase) :
    H (Q i ++ u) (Q (topNext i) ++ (if topActive i then v else u)) := by
  cases i
  case q0 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more100 (Parse.zero (Parse.more100 (Parse.zero (h 2))))))
  case q1 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case q2 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero Parse.stop))))
  case q3 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more100 (Parse.zero (Parse.more1010 (Parse.one (Parse.zero (h 2)))))))
  case q4 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case q5 => simpa [H,Q,topNext,topActive,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero (Parse.more100 (Parse.zero (h 2)))))))
inductive StartPhase where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11
open StartPhase
def T : StartPhase → List Bool
  | s0 => [true] -- 1
  | s1 => [false,false,true,false,true,false,true] -- 0010101
  | s2 => [true,false,true,false,true,false,true,false,true] -- 101010101
  | s3 => [true,false,false,false,true,false,true,false,false,true,false,true,false,true] -- 10001010010101
  | s4 => [false,false,true,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 001010010100010101
  | s5 => [true,false,true,false,true,false,true,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 10101010010100010101
  | s6 => [true,false,false,false,true,false,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 100010000100010100010101
  | s7 => [false,false,true,false,false,false,true,false,true,false,true,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 00100010101100010100010101
  | s8 => [true,false,true,false,true,false,false,false,true,false,true,false,true,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 1010100010101100010100010101
  | s9 => [true,false,false,false,true,false,true,false,true,false,true,false,true,false,true,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true] -- 100010101010101100010100010101
  | s10 => [false,false,true,false,true,false,false,false,true,false,true,false,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,true] -- 00101000101000010101010100010101
  | s11 => [true,false,true,false,true,false,true,false,false,false,true,false,true,false,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,true,false,true] -- 1010101000101000010101010100010101
def startOut : StartPhase → List Bool
  | s0 => T s1
  | s1 => T s2
  | s2 => T s3
  | s3 => T s4
  | s4 => T s5
  | s5 => T s6
  | s6 => T s7
  | s7 => T s8
  | s8 => T s9
  | s9 => T s10
  | s10 => T s11
  | s11 => Q q0 ++ Bword ++ P p0 ++ U p0
theorem H_seed (i : StartPhase) : H (T i) (startOut i) := by
  cases i
  case s0 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1 (Parse.zeroEmpty Parse.stopEmpty)))
  case s1 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case s2 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero (Parse.more101 (Parse.zeroEmpty Parse.stopEmpty))))))
  case s3 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more100 (Parse.zero (Parse.more1010 (Parse.zero (Parse.more1010 (Parse.one (Parse.zeroEmpty Parse.stopEmpty))))))))
  case s4 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case s5 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero (Parse.more100 (Parse.one (Parse.zero (Parse.more100 (Parse.zero (Parse.more1010 (Parse.one (Parse.zeroEmpty Parse.stopEmpty))))))))))))
  case s6 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more100 (Parse.zero (Parse.more100 (Parse.zero Parse.stop)))))
  case s7 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case s8 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero Parse.stop))))
  case s9 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more100 (Parse.zero (Parse.more1010 (Parse.one (Parse.zero (Parse.more1010 (Parse.one (Parse.one (Parse.zero Parse.stop))))))))))
  case s10 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) Parse.stop)
  case s11 => simpa [H,T,startOut,Q,Bword,P,U,emitRun,bits,rep,List.append_assoc] using (Parse.zero (a := 0) (Parse.more1010 (Parse.one (Parse.zero (Parse.more100 (Parse.zero (Parse.more1010 (Parse.zero Parse.stop))))))))

inductive TopLang : List Bool → Prop where
  | seed (i : StartPhase) : TopLang (T i)
  | phase (i : TopPhase) {u : List Bool} : Lang u → TopLang (Q i ++ u)

theorem TopLang.seedOut_mem (i : StartPhase) : TopLang (startOut i) := by
  cases i
  case s0 => exact TopLang.seed s1
  case s1 => exact TopLang.seed s2
  case s2 => exact TopLang.seed s3
  case s3 => exact TopLang.seed s4
  case s4 => exact TopLang.seed s5
  case s5 => exact TopLang.seed s6
  case s6 => exact TopLang.seed s7
  case s7 => exact TopLang.seed s8
  case s8 => exact TopLang.seed s9
  case s9 => exact TopLang.seed s10
  case s10 => exact TopLang.seed s11
  case s11 => exact TopLang.phase q0 (Lang.block (Lang.phase p0 (Lang.seed p0)))

theorem TopLang.closed {u : List Bool} (hu : TopLang u) : ∃ v, TopLang v ∧ H u v := by
  cases hu with
  | seed i => exact ⟨startOut i, TopLang.seedOut_mem i, H_seed i⟩
  | phase i hu =>
    obtain ⟨v,hv,hg⟩ := Lang.closed hu
    refine ⟨Q (topNext i) ++ (if topActive i then v else _),TopLang.phase (topNext i) ?_,H_phase hg i⟩
    cases topActive i <;> assumption

def ReturnLang (r : List Bool) : Prop := ∃ u, r = false::u ∧ TopLang u

theorem ReturnLang.seed : ReturnLang [false,true] := ⟨T s0,rfl,TopLang.seed s0⟩

theorem ReturnLang.closed : ∀ r, ReturnLang r → ∃ s, ReturnLang s ∧ Parse true 0 r (false::true::s) := by
  intro r hr
  obtain ⟨u,rfl,hu⟩ := hr
  obtain ⟨v,hv,hp⟩ := TopLang.closed hu
  exact ⟨false::v,⟨v,rfl,hv⟩,hp⟩

theorem never : ∀ m, compatible table m → NeverHalts m :=
  never_of_language ReturnLang ReturnLang.seed ReturnLang.closed

#print axioms Lang.closed
#print axioms TopLang.closed
#print axioms never
end BB6.Agent32Raw42RA.Leaf1659
