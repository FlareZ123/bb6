import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent38M62
open BB6Coverage BB6Coverage.Agent31Pump

/-- Literal Raw43 B1=0LE E0=1LA i62 partial table. F1 alone is unassigned. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
def zeros (n : Nat) : List Bool := List.replicate n false
def ones (n : Nat) : List Bool := List.replicate n true

/-- Each right-prefixed fixed path leaves its next scanned bit arbitrary.
The regular zipper invariant later proves that this bit is zero. -/
theorem forward18 (L R : List Bool) :
    run0 table 18 ⟨5,false::L,bits "10000"++R⟩ =
      some ⟨5,R.headD false::bits "110011"++L,R.tail⟩ := by
  cases R <;> rfl

theorem forward18_blank (L : List Bool) :
    run0 table 18 ⟨5,false::L,[true]⟩ =
      some ⟨5,false::bits "110011"++L,[]⟩ := by rfl

theorem forward8 (L R : List Bool) :
    run0 table 8 ⟨5,false::L,bits "10101"++R⟩ =
      some ⟨5,R.headD false::bits "111110"++L,R.tail⟩ := by
  cases R <;> rfl

theorem forward11a (L R : List Bool) :
    run0 table 11 ⟨5,false::L,bits "0101"++R⟩ =
      some ⟨5,R.headD false::bits "11111"++L,R.tail⟩ := by
  cases R <;> rfl

theorem forward11b (L R : List Bool) :
    run0 table 11 ⟨5,false::L,bits "000101"++R⟩ =
      some ⟨5,R.headD false::bits "1100111"++L,R.tail⟩ := by
  cases R <;> rfl

/-- The exact blank prefix reaches phase A: near-left 111, right 1. -/
theorem blank_entry :
    run0 table 12 ⟨0,[],[]⟩ =
      some ⟨5,false::bits "111",bits "1"⟩ := by rfl

#print axioms forward18
#print axioms forward18_blank
#print axioms forward8
#print axioms forward11a
#print axioms forward11b
#print axioms blank_entry

end BB6.Agent38M62
