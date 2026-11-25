import Raw118M2869Data
namespace BB6Coverage.Agent1Raw118M2869
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none

def frameBits : Frame → List Bool
  | .a => [false,true]
  | .b => [true,false,true,true]
  | .c => [false,true,false,true]
  | .d => [false,false,true,true]
  | .e => [true,false,true,true,true,false,true,true]
  | .s => [true,false,true,true,true,false,true]
def tokBits : Tok → List Bool
  | .x => [false,false,true]
  | .y => [false,true,false,true]
  | .z => [false,false,false,true,false,false,false,true]
  | .u => [false,true]
  | .v => [false,false,false,true]
def leftBits : List Frame → List Bool
  | [] => [true,false,true]
  | f::l => frameBits f ++ leftBits l
def rightBits : List Tok → List Bool
  | [] => []
  | t::r => tokBits t ++ rightBits r
def cfg (back p : Bool) (l : List Frame) (r : List Tok) : Z0 :=
  if back then ⟨0,(if p then [true,false,true] else [true,false]) ++ leftBits l,false::rightBits r⟩
  else ⟨0,false::leftBits l,(if p then [false,true] else [true]) ++ rightBits r⟩

theorem fxP_run (l : List Frame) (r : List Tok) :
    run0 table 2 (cfg false false l (.x::r)) = some (cfg false true (.a::l) r) := by rfl

theorem fxQ_run (l : List Frame) (r : List Tok) :
    run0 table 4 (cfg false true l (.x::r)) = some (cfg false false (.b::l) r) := by rfl

theorem fyP_run (l : List Frame) (r : List Tok) :
    run0 table 4 (cfg false false l (.y::r)) = some (cfg false false (.c::l) r) := by rfl

theorem fyQ_run (l : List Frame) (r : List Tok) :
    run0 table 6 (cfg false true l (.y::r)) = some (cfg false true (.d::l) r) := by rfl

theorem fzP_run (l : List Frame) (r : List Tok) :
    run0 table 29 (cfg false false l (.z::r)) = some (cfg true false l (.x::.y::r)) := by rfl

theorem fzQ_run (l : List Frame) (r : List Tok) :
    run0 table 8 (cfg false true l (.z::r)) = some (cfg false true (.e::l) r) := by rfl

theorem feP_run (l : List Frame) :
    run0 table 13 (cfg false false l []) = some (cfg true false l [.x]) := by rfl

theorem feQ_run (l : List Frame) :
    run0 table 16 (cfg false true l []) = some (cfg true true l [.v]) := by rfl

theorem fvP_run (l : List Frame) :
    run0 table 29 (cfg false false l [.v]) = some (cfg true false l [.x,.u]) := by rfl

theorem fvQ_run (l : List Frame) :
    run0 table 32 (cfg false true l [.v]) = some (cfg true true l [.z]) := by rfl

theorem fu_run (l : List Frame) :
    run0 table 19 (cfg false true (.a::l) [.u]) = some (cfg false true (.s::l) []) := by rfl

theorem ba_run (l : List Frame) (r : List Tok) :
    run0 table 11 (cfg true true (.a::l) r) = some (cfg true false l (.x::r)) := by rfl

theorem bb_run (l : List Frame) (r : List Tok) :
    run0 table 11 (cfg true false (.b::l) r) = some (cfg true true l (.x::r)) := by rfl

theorem bc_run (l : List Frame) (r : List Tok) :
    run0 table 20 (cfg true false (.c::l) r) = some (cfg true false l (.y::r)) := by rfl

theorem be_run (l : List Frame) (r : List Tok) :
    run0 table 24 (cfg true true (.e::l) r) = some (cfg true true l (.z::r)) := by rfl

theorem bs_run (l : List Frame) (r : List Tok) :
    run0 table 24 (cfg true true (.s::l) r) = some (cfg true false l (.z::r)) := by rfl

theorem bd_run (l : List Frame) (r : List Tok) :
    run0 table 13 (cfg true true (.d::.a::l) r) = some (cfg false true (.s::l) r) := by rfl

theorem base_run (r : List Tok) :
    run0 table 23 (cfg true false [] r) = some (cfg false false [] (.x::r)) := by rfl

theorem entry_run : run0 table 53 ⟨0,[],[]⟩ = some (cfg false false [] [.z]) := by rfl
end BB6Coverage.Agent1Raw118M2869
