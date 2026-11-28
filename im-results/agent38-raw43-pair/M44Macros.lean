import M44Sweeps
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38M44
open BB6Coverage BB6Coverage.Agent31Pump

def tokL (p : Nat) := List.replicate p true ++ [false]
def tokR (p : Nat) := List.replicate p false ++ [true]
def stackL : List Nat → List Bool
  | [] => []
  | p::s => tokL p ++ stackL s
def stackR : List Nat → List Bool
  | [] => []
  | p::s => tokR p ++ stackR s

def base (j : Nat) := rep (bits "1110") j ++ bits "11111"
def rawF (s d : List Nat) (j z : Nat) : Z0 :=
  ⟨5,bits "11" ++ stackL s ++ base j,bits "10" ++ stackR d ++ List.replicate z false⟩
def rawA (s d : List Nat) (j z : Nat) : Z0 :=
  ⟨0,bits "1" ++ stackL s ++ base j,bits "101" ++ stackR d ++ List.replicate z false⟩

theorem stackL_append (s t : List Nat) : stackL (s++t) = stackL s ++ stackL t := by
  induction s with
  | nil => rfl
  | cons p s ih => simp [stackL,ih,List.append_assoc]
theorem stackR_append (s t : List Nat) : stackR (s++t) = stackR s ++ stackR t := by
  induction s with
  | nil => rfl
  | cons p s ih => simp [stackR,ih,List.append_assoc]

theorem f0 (L R : List Bool) :
    run0 table 7 ⟨5,bits "11"++L,bits "10"++stackR [0]++R⟩ =
      some ⟨5,bits "11"++stackL [0]++L,bits "10"++R⟩ := by rfl

theorem f11 (L R : List Bool) :
    run0 table 10 ⟨5,bits "11"++L,bits "10"++stackR [1,1]++R⟩ =
      some ⟨5,bits "11"++stackL [3]++L,bits "10"++R⟩ := by rfl

theorem f210 (L R : List Bool) :
    run0 table 28 ⟨5,bits "11"++L,bits "10"++stackR [2,1,0]++R⟩ =
      some ⟨5,bits "11"++stackL [5]++L,bits "10"++R⟩ := by rfl

theorem f2121 (L R : List Bool) :
    run0 table 16 ⟨5,bits "11"++L,bits "10"++stackR [2,1,2,1]++R⟩ =
      some ⟨5,bits "11"++stackL [3,0,4]++L,bits "10"++R⟩ := by rfl

theorem f211 (L R : List Bool) :
    run0 table 13 ⟨5,bits "11"++L,bits "10"++stackR [2,1,1]++R⟩ =
      some ⟨5,bits "11"++stackL [0,0,4]++L,bits "10"++R⟩ := by rfl

theorem f121 (L R : List Bool) :
    run0 table 13 ⟨5,bits "11"++L,bits "10"++stackR [1,2,1]++R⟩ =
      some ⟨5,bits "11"++stackL [6]++L,bits "10"++R⟩ := by rfl

theorem f13121 (L R : List Bool) :
    run0 table 19 ⟨5,bits "11"++L,bits "10"++stackR [1,3,1,2,1]++R⟩ =
      some ⟨5,bits "11"++stackL [3,0,7]++L,bits "10"++R⟩ := by rfl

theorem f3 (L R : List Bool) :
    run0 table 12 ⟨5,bits "11"++L,bits "10000"++R⟩ =
      some ⟨0,bits "1110"++L,bits "101"++R⟩ := by rfl

theorem f14 (L R : List Bool) :
    run0 table 15 ⟨5,bits "11"++L,bits "10010000"++R⟩ =
      some ⟨0,bits "1111110"++L,bits "101"++R⟩ := by rfl

theorem f10 (L R : List Bool) :
    run0 table 21 ⟨5,bits "11"++L,bits "10011"++R⟩ =
      some ⟨0,bits "1"++L,bits "101000"++R⟩ := by rfl

theorem azero (L R : List Bool) :
    run0 table 7 ⟨0,bits "10"++L,bits "101"++R⟩ =
      some ⟨5,bits "111"++L,bits "10"++R⟩ := by rfl

theorem f3_end0 (L : List Bool) :
    run0 table 12 ⟨5,bits "11"++L,bits "10"++List.replicate 0 false⟩ =
      some ⟨0,bits "1110"++L,bits "101"⟩ := by rfl

theorem f3_end1 (L : List Bool) :
    run0 table 12 ⟨5,bits "11"++L,bits "10"++List.replicate 1 false⟩ =
      some ⟨0,bits "1110"++L,bits "101"⟩ := by rfl

theorem f3_end2 (L : List Bool) :
    run0 table 12 ⟨5,bits "11"++L,bits "10"++List.replicate 2 false⟩ =
      some ⟨0,bits "1110"++L,bits "101"⟩ := by rfl

theorem f14_end0 (L : List Bool) :
    run0 table 15 ⟨5,bits "11"++L,bits "1001"++List.replicate 0 false⟩ =
      some ⟨0,bits "1111110"++L,bits "101"⟩ := by rfl

theorem f14_end1 (L : List Bool) :
    run0 table 15 ⟨5,bits "11"++L,bits "1001"++List.replicate 1 false⟩ =
      some ⟨0,bits "1111110"++L,bits "101"⟩ := by rfl

theorem f14_end2 (L : List Bool) :
    run0 table 15 ⟨5,bits "11"++L,bits "1001"++List.replicate 2 false⟩ =
      some ⟨0,bits "1111110"++L,bits "101"⟩ := by rfl

theorem f14_end3 (L : List Bool) :
    run0 table 15 ⟨5,bits "11"++L,bits "1001"++List.replicate 3 false⟩ =
      some ⟨0,bits "1111110"++L,bits "101"⟩ := by rfl

theorem apos2 (L R : List Bool) :
    run0 table 11 ⟨0,bits "1"++tokL 2++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [0,1]++R⟩ := by rfl

theorem apos3 (L R : List Bool) :
    run0 table 12 ⟨0,bits "1"++tokL 3++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [1,1]++R⟩ := by rfl

theorem apos4 (L R : List Bool) :
    run0 table 13 ⟨0,bits "1"++tokL 4++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [2,1]++R⟩ := by rfl

theorem apos5 (L R : List Bool) :
    run0 table 14 ⟨0,bits "1"++tokL 5++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [3,1]++R⟩ := by rfl

theorem apos6 (L R : List Bool) :
    run0 table 15 ⟨0,bits "1"++tokL 6++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [4,1]++R⟩ := by rfl

theorem apos7 (L R : List Bool) :
    run0 table 16 ⟨0,bits "1"++tokL 7++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [5,1]++R⟩ := by rfl

theorem apos8 (L R : List Bool) :
    run0 table 17 ⟨0,bits "1"++tokL 8++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [6,1]++R⟩ := by rfl

theorem apos9 (L R : List Bool) :
    run0 table 18 ⟨0,bits "1"++tokL 9++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [7,1]++R⟩ := by rfl

theorem apos10 (L R : List Bool) :
    run0 table 19 ⟨0,bits "1"++tokL 10++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [8,1]++R⟩ := by rfl

theorem apos11 (L R : List Bool) :
    run0 table 20 ⟨0,bits "1"++tokL 11++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [9,1]++R⟩ := by rfl

theorem apos12 (L R : List Bool) :
    run0 table 21 ⟨0,bits "1"++tokL 12++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [10,1]++R⟩ := by rfl

theorem apos13 (L R : List Bool) :
    run0 table 22 ⟨0,bits "1"++tokL 13++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [11,1]++R⟩ := by rfl

theorem apos14 (L R : List Bool) :
    run0 table 23 ⟨0,bits "1"++tokL 14++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [12,1]++R⟩ := by rfl

theorem apos15 (L R : List Bool) :
    run0 table 24 ⟨0,bits "1"++tokL 15++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [13,1]++R⟩ := by rfl

theorem apos16 (L R : List Bool) :
    run0 table 25 ⟨0,bits "1"++tokL 16++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [14,1]++R⟩ := by rfl

theorem apos (p : Nat) (hp : 2 ≤ p) (hb : p ≤ 16) (L R : List Bool) :
    run0 table (p+9) ⟨0,bits "1"++tokL p++L,bits "101"++R⟩ =
      some ⟨0,bits "1"++L,bits "101"++stackR [p-2,1]++R⟩ := by
  have h : p=2 ∨ p=3 ∨ p=4 ∨ p=5 ∨ p=6 ∨ p=7 ∨ p=8 ∨ p=9 ∨ p=10 ∨ p=11 ∨ p=12 ∨ p=13 ∨ p=14 ∨ p=15 ∨ p=16 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact apos2 L R
  · exact apos3 L R
  · exact apos4 L R
  · exact apos5 L R
  · exact apos6 L R
  · exact apos7 L R
  · exact apos8 L R
  · exact apos9 L R
  · exact apos10 L R
  · exact apos11 L R
  · exact apos12 L R
  · exact apos13 L R
  · exact apos14 L R
  · exact apos15 L R
  · exact apos16 L R

-- The reset carries the immutable alternating-block base into a larger base.
theorem reset (j : Nat) (R : List Bool) :
    run0 table (12*j+21+(294+22*j)+(222+10*((j+1)+1))+19)
      ⟨0,bits "1"++base j,bits "101"++bits "000000101"++R⟩ =
      some ⟨5,bits "11"++stackL [3,0,7]++base (j+2),bits "10"++R⟩ := by
  have h1 := sweepL table 0 (bits "1") (bits "101") (bits "1110") (bits "0101") 12 back_token j (bits "11111") (bits "000000101"++R)
  have h2 := back_finish (rep (bits "0101") j ++ (bits "000000101"++R))
  have h12 : run0 table (12*j+21) ⟨0,bits "1"++base j,bits "101"++bits "000000101"++R⟩ = some (phase j (bits "000000101"++R)) := by
    simpa only [base,phase,List.append_assoc] using join0 h1 h2
  have h3 := four_zero j (bits "00101"++R)
  have h4 := forward (j+1) (bits "00010100101"++R)
  have h34 : run0 table ((294+22*j)+(222+10*((j+1)+1))) (phase j (bits "000000101"++R)) = some ⟨5,bits "11"++base (j+2),bits "10"++stackR [1,3,1,2,1]++R⟩ := by
    exact join0 h3 h4
  have h5 := f13121 (base (j+2)) R
  have H := join0 (join0 h12 h34) h5
  rw [show 12*j+21+(294+22*j)+(222+10*((j+1)+1))+19 = (12*j+21)+((294+22*j)+(222+10*((j+1)+1)))+19 by omega]
  exact H

def W0 : List Nat := [0,1,0,1,1,1,1,1,0,1,0,1]

theorem marker_entry : run0 table 3289 ⟨0,[],[]⟩ = some (phase 7 (bits "000000101"++stackR W0)) := by rfl

theorem initial_macro : ∃ t, run0 table t ⟨0,[],[]⟩ = some (rawF [3,0,7] W0 9 0) := by
  have h1 := four_zero 7 (bits "00101"++stackR W0)
  have h2 := forward 8 (bits "00010100101"++stackR W0)
  have h3 := f13121 (base 9) (stackR W0)
  have H := join0 (join0 (join0 marker_entry h1) h2) h3
  exact ⟨_, H⟩
#print axioms initial_macro
#print axioms reset
#print axioms apos
end BB6.Agent38M44
