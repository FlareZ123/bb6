import Raw58RFTripleCore
import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent4RFTripleCases
open BB6Coverage Agent31Pump Agent4RFTriple
namespace M116
-- 1RB0RF_1RC0RE_0RD1LB_1LD1RE_---0RA_0RC0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 5 ⟨0,[],[]⟩ = some (D [true,true]) := by rfl
theorem anchor (b : Bool) (r : List Bool) : run0 table 3 (D (true::true::b::r)) = some (F 0 b r) := by rfl
theorem anchorShort : run0 table 3 (D [true,true]) = some (F 0 false []) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) :
    run0 table 7 (F k false (true::true::b::r)) = some (F (k+1) b r) := by rfl
theorem shortCarry (k : Nat) : run0 table 7 (F k false [true,true]) = some (F (k+1) false []) := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (3+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)) := by
  have h : run0 table 3 (F k true r) =
      some ⟨3,rep [false,false,false] k ++ [true,true],true::true::false::r⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem overflow (k : Nat) : run0 table (7+3*k) (F k false []) = some (D (rep [true,true,true] k ++ [true,true,true,true,true])) := by
  have h : run0 table 7 (F k false []) = some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true]⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z :=
  Agent4RFTriple.arbitrary table 7 3 7 [true,true,true,true,true] (Code.block true _ Code.short) (by decide) (by decide) (by decide)
    entry anchor anchorShort carry shortCarry stop overflow n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end M116

namespace M317
-- 1RB0RF_1RC---_0RD0LC_1LD1RE_0RC0RA_0RE1LB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem entry : run0 table 5 ⟨0,[],[]⟩ = some (D [true,true]) := by rfl
theorem anchor (b : Bool) (r : List Bool) : run0 table 3 (D (true::true::b::r)) = some (F 0 b r) := by rfl
theorem anchorShort : run0 table 3 (D [true,true]) = some (F 0 false []) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) :
    run0 table 3 (F k false (true::true::b::r)) = some (F (k+1) b r) := by rfl
theorem shortCarry (k : Nat) : run0 table 3 (F k false [true,true]) = some (F (k+1) false []) := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)) := by
  have h : run0 table 7 (F k true r) =
      some ⟨3,rep [false,false,false] k ++ [true,true],true::true::false::r⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem overflow (k : Nat) : run0 table (9+3*k) (F k false []) = some (D (rep [true,true,true] k ++ [true,true,true,true,true,true])) := by
  have h : run0 table 9 (F k false []) = some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true,true]⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z :=
  Agent4RFTriple.arbitrary table 3 7 9 [true,true,true,true,true,true] (Code.block true _ (Code.block true _ Code.nil)) (by decide) (by decide) (by decide)
    entry anchor anchorShort carry shortCarry stop overflow n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end M317

namespace M345
-- 1RB0RF_1RC---_0RD0LC_1LD1RE_0RD0RA_0RE1LB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem entry : run0 table 5 ⟨0,[],[]⟩ = some (D [true,true]) := by rfl
theorem anchor (b : Bool) (r : List Bool) : run0 table 3 (D (true::true::b::r)) = some (F 0 b r) := by rfl
theorem anchorShort : run0 table 3 (D [true,true]) = some (F 0 false []) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) :
    run0 table 3 (F k false (true::true::b::r)) = some (F (k+1) b r) := by rfl
theorem shortCarry (k : Nat) : run0 table 3 (F k false [true,true]) = some (F (k+1) false []) := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)) := by
  have h : run0 table 7 (F k true r) =
      some ⟨3,rep [false,false,false] k ++ [true,true],true::true::false::r⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem overflow (k : Nat) : run0 table (7+3*k) (F k false []) = some (D (rep [true,true,true] k ++ [true,true,true,true,true])) := by
  have h : run0 table 7 (F k false []) = some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true]⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z :=
  Agent4RFTriple.arbitrary table 3 7 7 [true,true,true,true,true] (Code.block true _ Code.short) (by decide) (by decide) (by decide)
    entry anchor anchorShort carry shortCarry stop overflow n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end M345

namespace M350
-- 1RB0RF_1RC---_0RD0LC_1LD1RE_1LC0RA_0RE0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem entry : run0 table 5 ⟨0,[],[]⟩ = some (D [true,true]) := by rfl
theorem anchor (b : Bool) (r : List Bool) : run0 table 3 (D (true::true::b::r)) = some (F 0 b r) := by rfl
theorem anchorShort : run0 table 3 (D [true,true]) = some (F 0 false []) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) :
    run0 table 3 (F k false (true::true::b::r)) = some (F (k+1) b r) := by rfl
theorem shortCarry (k : Nat) : run0 table 3 (F k false [true,true]) = some (F (k+1) false []) := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (3+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)) := by
  have h : run0 table 3 (F k true r) =
      some ⟨3,rep [false,false,false] k ++ [true,true],true::true::false::r⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem overflow (k : Nat) : run0 table (11+3*k) (F k false []) = some (D (rep [true,true,true] k ++ [true,true,true,true,true])) := by
  have h : run0 table 11 (F k false []) = some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true]⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z :=
  Agent4RFTriple.arbitrary table 3 3 11 [true,true,true,true,true] (Code.block true _ Code.short) (by decide) (by decide) (by decide)
    entry anchor anchorShort carry shortCarry stop overflow n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end M350

namespace M353
-- 1RB0RF_1RC---_0RD0LC_1LD1RE_1LC0RA_0RE1LB
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem entry : run0 table 5 ⟨0,[],[]⟩ = some (D [true,true]) := by rfl
theorem anchor (b : Bool) (r : List Bool) : run0 table 3 (D (true::true::b::r)) = some (F 0 b r) := by rfl
theorem anchorShort : run0 table 3 (D [true,true]) = some (F 0 false []) := by rfl
theorem carry (k : Nat) (b : Bool) (r : List Bool) :
    run0 table 3 (F k false (true::true::b::r)) = some (F (k+1) b r) := by rfl
theorem shortCarry (k : Nat) : run0 table 3 (F k false [true,true]) = some (F (k+1) false []) := by rfl
theorem stop (k : Nat) (r : List Bool) :
    run0 table (7+3*k) (F k true r) = some (D (rep [true,true,true] k ++ true::true::false::r)) := by
  have h : run0 table 7 (F k true r) =
      some ⟨3,rep [false,false,false] k ++ [true,true],true::true::false::r⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem overflow (k : Nat) : run0 table (11+3*k) (F k false []) = some (D (rep [true,true,true] k ++ [true,true,true,true,true])) := by
  have h : run0 table 11 (F k false []) = some ⟨3,rep [false,false,false] k ++ [true,true],[true,true,true,true,true]⟩ := by rfl
  exact join0 h (sweep table (by intro L R; rfl) k _)
theorem arbitrary (n : Nat) : ∃ t z, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z :=
  Agent4RFTriple.arbitrary table 3 7 11 [true,true,true,true,true] (Code.block true _ Code.short) (by decide) (by decide) (by decide)
    entry anchor anchorShort carry shortCarry stop overflow n
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent4Live.never_of_live table arbitrary m hm
#print axioms never
end M353

end BB6Coverage.Agent4RFTripleCases
