import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump

/-- Raw43 B1=0LE/E0=1LA local i44; sole unspecified instruction F0. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def bits (s : String) : List Bool := s.toList.map (· == '1')
def phase (k : Nat) (R : List Bool) : Z0 :=
  ⟨5,bits "111",bits "10000101" ++ rep (bits "0101") k ++ R⟩

theorem root_entry : run0 table 15 ⟨0,[],[]⟩ = some ⟨5,bits "111",bits "10"⟩ := by rfl
#print axioms root_entry

theorem prelude (R : List Bool) :
    run0 table 222 ⟨5,bits "111",bits "10000101"++R⟩ =
      some ⟨5,bits "1111111",bits "10010101"++R⟩ := by rfl

theorem transfer (L R : List Bool) :
    run0 table 10 ⟨5,bits "11"++L,bits "10"++bits "0101"++R⟩ =
      some ⟨5,bits "11"++bits "1110"++L,bits "10"++R⟩ := by rfl

theorem back_start (L R : List Bool) :
    run0 table 29 ⟨5,bits "111110"++L,bits "10010000"++R⟩ =
      some ⟨0,bits "11110"++L,bits "101000101"++R⟩ := by rfl

theorem back_token (L R : List Bool) :
    run0 table 12 ⟨0,bits "1"++bits "1110"++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++bits "0101"++R⟩ := by rfl

theorem back_finish (R : List Bool) :
    run0 table 21 ⟨0,bits "111111",bits "101"++R⟩ =
      some ⟨5,bits "111",bits "10000101"++R⟩ := by rfl

theorem pair_commute (k : Nat) (R : List Bool) :
    bits "01" ++ rep (bits "0101") k ++ R =
      rep (bits "0101") k ++ bits "01" ++ R := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [rep,List.append_assoc] at *
      change bits "0101" ++ (bits "01" ++ (rep (bits "0101") k ++ R)) = _
      rw [ih]

theorem forward (k : Nat) (R : List Bool) :
    run0 table (222 + 10*(k+1)) (phase k R) =
      some ⟨5,bits "11"++rep (bits "1110") (k+1)++bits "11111",bits "1001"++R⟩ := by
  have h1 := prelude (rep (bits "0101") k ++ R)
  have h2 := sweepR table 5 (bits "11") (bits "10") (bits "0101") (bits "1110") 10 transfer
    (k+1) (bits "11111") (bits "01"++R)
  have hh : bits "10010101" ++ (rep (bits "0101") k ++ R) =
      bits "10" ++ rep (bits "0101") (k+1) ++ (bits "01"++R) := by
    simp only [rep,List.append_assoc]
    change bits "100101" ++ (bits "01" ++ (rep (bits "0101") k ++ R)) =
      bits "100101" ++ (rep (bits "0101") k ++ (bits "01" ++ R))
    have hc := pair_commute k R
    simp only [List.append_assoc] at hc
    rw [hc]
  rw [← hh] at h2
  exact join0 h1 h2

theorem backward (k : Nat) (R : List Bool) :
    run0 table (50+12*(k+1))
      ⟨5,bits "11"++rep (bits "1110") (k+1)++bits "11111",bits "10010000"++R⟩ =
      some (phase (k+1) (bits "000101"++R)) := by
  have h1 := back_start (rep (bits "1110") k ++ bits "11111") R
  have h2 := sweepL table 0 (bits "1") (bits "101") (bits "1110") (bits "0101") 12 back_token
    (k+1) (bits "11111") (bits "000101"++R)
  have h3 := back_finish (rep (bits "0101") (k+1) ++ (bits "000101"++R))
  have h12 : run0 table (29+12*(k+1))
      ⟨5,bits "11"++rep (bits "1110") (k+1)++bits "11111",bits "10010000"++R⟩ =
      some ⟨0,bits "111111",bits "101"++(rep (bits "0101") (k+1)++(bits "000101"++R))⟩ := by
    apply join0 (b := ⟨0,bits "11110"++(rep (bits "1110") k++bits "11111"),bits "101000101"++R⟩)
    · exact h1
    · exact h2
  have H := join0 h12 h3
  rw [show 50+12*(k+1) = 29+12*(k+1)+21 by omega]
  simpa only [phase,List.append_assoc] using H

/-- A genuine arbitrary-tail return, but only on one of the return branches. -/
theorem four_zero (k : Nat) (R : List Bool) :
    run0 table (294+22*k) (phase k (bits "0000"++R)) =
      some (phase (k+1) (bits "000101"++R)) := by
  have h1 := forward k (bits "0000"++R)
  have h2 := backward k R
  have H := join0 h1 h2
  rw [show 294+22*k=(222+10*(k+1))+(50+12*(k+1)) by omega]
  exact H

#print axioms four_zero
end BB6.Agent38M44
