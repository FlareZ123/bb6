import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Word66
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none

def enc : List Bool → List Bool
  | [] => []
  | b::bs => b::b::enc bs

def block (b : Bool) : List Bool := [true,true,b,true]
def stack : List Bool → List Bool
  | [] => block false
  | b::bs => block b ++ stack bs

def cfg (ws : List Bool) : Z0 := ⟨0,[false,true,false,true],false::enc ws⟩
def bcfg (bs ws : List Bool) : Z0 := ⟨1,false::stack bs,enc ws⟩
def ecfg (bs ws : List Bool) : Z0 := ⟨4,stack bs,false::enc ws⟩

def finishWord : List Bool → List Bool → List Bool
  | [],ws => true::ws
  | b::bs,ws => finishWord bs (false::(!b)::ws)

theorem popBlock (b : Bool) (L R : List Bool) :
    run0 table (if b then 4 else 12) ⟨4,block b ++ L,false::R⟩ = some ⟨4,L,false::false::false::(!b)::(!b)::R⟩ := by
  cases b <;> rfl

theorem finish (bs ws : List Bool) : ∃ t, 0<t ∧ run0 table t (ecfg bs ws) = some (cfg (finishWord bs ws)) := by
  induction bs generalizing ws with
  | nil =>
    refine ⟨16,by decide,?_⟩
    rfl
  | cons b bs ih =>
    have h : run0 table (if b then 4 else 12) (ecfg (b::bs) ws) = some (ecfg bs (false::(!b)::ws)) := popBlock b (stack bs) (enc ws)
    obtain ⟨t,ht,hh⟩ := ih (false::(!b)::ws)
    exact ⟨_,by omega,join0 h hh⟩

def scanWord : List Bool → List Bool → List Bool
  | [],bs => finishWord bs [true]
  | false::ws,bs => finishWord bs (true::ws)
  | [true],bs => finishWord (false::bs) [true]
  | true::b::ws,bs => scanWord ws (b::bs)

theorem scanStep (b : Bool) (bs ws : List Bool) : run0 table (if b then 14 else 6) (bcfg bs (true::b::ws)) = some (bcfg (b::bs) ws) := by
  cases b <;> rfl

theorem scanLast (bs : List Bool) : run0 table 6 (bcfg bs [true]) = some (bcfg (false::bs) []) := by rfl

theorem scan (ws bs : List Bool) : ∃ t, 0<t ∧ run0 table t (bcfg bs ws) = some (cfg (scanWord ws bs)) := by
  cases ws with
  | nil =>
    have h : run0 table 5 (bcfg bs []) = some (ecfg bs [true]) := by rfl
    obtain ⟨t,ht,hh⟩ := finish bs [true]
    exact ⟨_,by omega,join0 h hh⟩
  | cons a ws =>
    cases a
    · have h : run0 table 5 (bcfg bs (false::ws)) = some (ecfg bs (true::ws)) := by rfl
      obtain ⟨t,ht,hh⟩ := finish bs (true::ws)
      exact ⟨_,by omega,join0 h hh⟩
    · cases ws with
      | nil =>
        have h : run0 table 5 (bcfg (false::bs) []) = some (ecfg (false::bs) [true]) := by rfl
        obtain ⟨t,ht,hh⟩ := finish (false::bs) [true]
        exact ⟨_,by omega,join0 (join0 (scanLast bs) h) hh⟩
      | cons b ws =>
        obtain ⟨t,ht,hh⟩ := scan ws (b::bs)
        exact ⟨_,by omega,join0 (scanStep b bs ws) hh⟩
termination_by ws.length

def next (ws : List Bool) : List Bool := scanWord ws []
def orbit : Nat → List Bool
  | 0 => [true,false,true]
  | n+1 => next (orbit n)
def family (n : Nat) : Z0 := cfg (orbit n)

theorem first : run0 table 37 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem stepFamily (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h : run0 table 1 (cfg (orbit n)) = some (bcfg [] (orbit n)) := by rfl
  obtain ⟨t,ht,hh⟩ := scan (orbit n) []
  exact ⟨_,by omega,join0 h hh⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 37 first stepFamily m hm
#print axioms never
end BB6.Agent8Raw54.Word66
