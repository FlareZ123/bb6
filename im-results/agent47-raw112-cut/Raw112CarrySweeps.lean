import Raw115CounterBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw112CarrySweeps
open BB6Coverage BB6Coverage.Agent31Pump
open BB6Coverage.Agent31Pump.Raw115CounterBase

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

/-- Nearest-first left word excludes the scanned cell; the right word includes it. -/
def cfg (q : Fin 6) (L R : List Bool) : Z0 := ⟨q,R.headD false :: L,R.tail⟩
abbrev w (s : String) : List Bool := s.toList.map (· == '1')
abbrev P := w "110000"
abbrev Q := w "101111"
abbrev K := w "000011"
abbrev W := w "111101"
abbrev J := w "111011"
abbrev V := w "001100"
abbrev U := w "011111"

def boundary (n : Nat) (S : List Bool) : Z0 := cfg 2 [true] (w "000" ++ rep P n ++ w "001111" ++ S)

theorem enter (X : List Bool) : run0 table 15 (cfg 2 [true] (w "000" ++ X)) = some (cfg 0 (w "01011") X) := by rfl

theorem aPump (L R : List Bool) : run0 table 38 (cfg 0 (w "0" ++ L) (P ++ R)) = some (cfg 0 (w "0" ++ Q ++ L) R) := by rfl

theorem aTurn (L R : List Bool) : run0 table 23 (cfg 0 (w "0" ++ Q ++ L) (w "001111" ++ R)) = some (cfg 1 L (w "1" ++ K ++ w "110111" ++ R)) := by rfl

theorem bPump1 (L R : List Bool) : run0 table 12 (cfg 1 (Q ++ L) (w "1" ++ R)) = some (cfg 1 L (w "1" ++ K ++ R)) := by rfl

theorem bTurn1 (R : List Bool) : run0 table 19 (cfg 1 (w "1011") (w "1" ++ R)) = some (cfg 2 [true] (w "011011" ++ R)) := by rfl

theorem cPump (L R : List Bool) : run0 table 38 (cfg 2 L (w "011011" ++ K ++ R)) = some (cfg 2 (W ++ L) (w "011011" ++ R)) := by rfl

theorem cTurn (L R : List Bool) : run0 table 32 (cfg 2 L (w "011011110111" ++ R)) = some (cfg 2 (W ++ L) (w "010111" ++ R)) := by rfl

theorem bPump2 (L R : List Bool) : run0 table 12 (cfg 1 (J ++ L) (w "1" ++ R)) = some (cfg 1 L (w "1" ++ V ++ R)) := by rfl

theorem bTurn2 (R : List Bool) : run0 table 3 (cfg 1 [] (w "1" ++ R)) = some (cfg 3 (w "01") R) := by rfl

theorem dEnter (R : List Bool) : run0 table 20 (cfg 3 (w "01") (V ++ R)) = some (cfg 3 (w "011001011") R) := by rfl

theorem dPump (L R : List Bool) : run0 table 38 (cfg 3 (w "011001" ++ L) (V ++ R)) = some (cfg 3 (w "011001" ++ U ++ L) R) := by rfl

theorem bPump3 (L R : List Bool) : run0 table 12 (cfg 1 (w "111" ++ U ++ L) (w "100" ++ R)) = some (cfg 1 (w "111" ++ L) (w "100" ++ P ++ R)) := by rfl

theorem bTurn3 (R : List Bool) : run0 table 14 (cfg 1 (w "111011") (w "100" ++ R)) = some (cfg 2 [true] (w "000" ++ P ++ R)) := by rfl

/-- Frame-preserving pumping in the head-explicit presentation. -/
theorem pumpR (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R, run0 table k (cfg q (lp++L) (rp++I++R)) =
      some (cfg q (lp++O++L) (rp++R))) (n : Nat) (L R : List Bool) :
    run0 table (k*n) (cfg q (lp++L) (rp++rep I n++R)) =
      some (cfg q (lp++rep O n++L) (rp++R)) := by
  induction n generalizing L with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h1 := one L (rep I n++R)
    have h2 := ih (O++L)
    have h1' : run0 table k (cfg q (lp++L) (rp++rep I (n+1)++R)) =
        some (cfg q (lp++(O++L)) (rp++rep I n++R)) := by
      simpa only [rep,List.append_assoc] using h1
    have H := join0 h1' h2
    rw [Nat.mul_succ, Nat.add_comm (k*n) k]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O L,rep_snoc O n] using H

theorem pumpL (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R, run0 table k (cfg q (lp++I++L) (rp++R)) =
      some (cfg q (lp++L) (rp++O++R))) (n : Nat) (L R : List Bool) :
    run0 table (k*n) (cfg q (lp++rep I n++L) (rp++R)) =
      some (cfg q (lp++L) (rp++rep O n++R)) := by
  induction n generalizing R with
  | zero => simp [rep,run0]
  | succ n ih =>
    have h1 := one (rep I n++L) R
    have h2 := ih (O++R)
    have h1' : run0 table k (cfg q (lp++rep I (n+1)++L) (rp++R)) =
        some (cfg q (lp++rep I n++L) (rp++(O++R))) := by
      simpa only [rep,List.append_assoc] using h1
    have H := join0 h1' h2
    rw [Nat.mul_succ, Nat.add_comm (k*n) k]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep O n) O R,rep_snoc O n] using H

/-- All long sweeps before the first suffix operation; n+1 is the pump length. -/
theorem preSuffix (n : Nat) (S : List Bool) :
    run0 table (88*n+165) (boundary (n+1) S) =
      some (cfg 2 (rep W (n+2) ++ [true]) (w "010111" ++ S)) := by
  have h1 := enter (rep P (n+1) ++ w "001111" ++ S)
  have h2 := pumpR 0 (w "0") [] P Q 38 (by simpa using aPump) (n+1) (w "1011") (w "001111" ++ S)
  have h3 := aTurn (rep Q n ++ w "1011") S
  have h4 := pumpL 1 [] (w "1") Q K 12 (by simpa using bPump1) n (w "1011") (K ++ w "110111" ++ S)
  have h5 := bTurn1 (rep K n ++ K ++ w "110111" ++ S)
  have h6 := pumpR 2 [] (w "011011") K W 38 (by simpa using cPump) (n+1) [true] (w "110111" ++ S)
  have h7 := cTurn (rep W (n+1) ++ [true]) S
  have e1 : run0 table 15 (boundary (n+1) S) = some (cfg 0 (w "0" ++ w "1011") (rep P (n+1) ++ w "001111" ++ S)) := by
    rw [show w "01011" = w "0" ++ w "1011" by rfl] at h1
    simpa only [boundary,List.append_assoc] using h1
  have e2 : run0 table (38*(n+1)) (cfg 0 (w "0" ++ w "1011") (rep P (n+1) ++ w "001111" ++ S)) = some (cfg 0 (w "0" ++ Q ++ rep Q n ++ w "1011") (w "001111" ++ S)) := by
    simpa only [List.nil_append,rep,List.append_assoc] using h2
  have e3 := join0 (join0 e1 e2) (by simpa only [List.append_assoc] using h3)
  have e4 := join0 e3 (by simpa only [List.nil_append,List.append_assoc] using h4)
  have e5 := join0 e4 (by simpa only [List.append_assoc] using h5)
  have e6 := join0 e5 (by
    simpa only [List.nil_append,rep,List.append_assoc,← rep_snoc K n] using h6)
  have e7 := join0 e6 (by
    rw [show w "011011110111" = w "011011" ++ w "110111" by rfl] at h7
    simpa only [List.append_assoc,rep] using h7)
  rw [show 88*n+165 = 15+38*(n+1)+23+12*n+19+38*(n+1)+32 by omega]
  simpa only [rep,List.append_assoc] using e7

/-- All long sweeps between the two suffix operations. -/
theorem middle (n : Nat) (T : List Bool) :
    run0 table (50*n+85) (cfg 1 (rep J (n+2)) (w "101100" ++ T)) =
      some (cfg 3 (w "011001" ++ rep U (n+1) ++ w "011") (w "01100" ++ T)) := by
  have h1 := pumpL 1 [] (w "1") J V 12 (by simpa using bPump2) (n+2) [] (w "01100" ++ T)
  have e1 : run0 table (12*(n+2)) (cfg 1 (rep J (n+2)) (w "101100" ++ T)) =
      some (cfg 1 [] (w "1" ++ rep V (n+2) ++ w "01100" ++ T)) := by
    rw [show w "101100" = w "1" ++ w "01100" by rfl]
    simpa only [List.nil_append,List.append_nil,List.append_assoc] using h1
  have h2 := bTurn2 (rep V (n+2) ++ w "01100" ++ T)
  have h3 := dEnter (rep V (n+1) ++ w "01100" ++ T)
  have h4 := pumpR 3 (w "011001") [] V U 38 (by simpa using dPump) (n+1) (w "011") (w "01100" ++ T)
  have e3 := join0 (join0 e1 h2) (by simpa only [rep,List.append_assoc] using h3)
  have e4 := join0 e3 (by
    rw [show w "011001" ++ w "011" = w "011001011" by rfl] at h4
    simpa only [List.nil_append,rep,List.append_assoc] using h4)
  rw [show 50*n+85 = 12*(n+2)+3+20+38*(n+1) by omega]
  exact e4

/-- Final return to a canonical boundary, after the second suffix operation. -/
theorem finish (n : Nat) (S : List Bool) :
    run0 table (12*n+26) (cfg 1 (w "111" ++ rep U (n+1) ++ w "011") (w "100001111" ++ S)) =
      some (boundary (n+2) S) := by
  have h1 := pumpL 1 (w "111") (w "100") U P 12 (by simpa using bPump3) (n+1) (w "011") (w "001111" ++ S)
  have e1 : run0 table (12*(n+1)) (cfg 1 (w "111" ++ rep U (n+1) ++ w "011") (w "100001111" ++ S)) =
      some (cfg 1 (w "111011") (w "100" ++ rep P (n+1) ++ w "001111" ++ S)) := by
    rw [show w "100001111" = w "100" ++ w "001111" by rfl, show w "111011" = w "111" ++ w "011" by rfl]
    simpa only [List.append_assoc] using h1
  have h2 := bTurn3 (rep P (n+1) ++ w "001111" ++ S)
  rw [show 12*n+26 = 12*(n+1)+14 by omega]
  simpa only [boundary,rep,List.append_assoc] using join0 e1 h2

/-- A local suffix return implies the full outer return for every positive pump length. -/
theorem return_of_suffix (n a b : Nat) (S T S' : List Bool)
    (hc : ∀ L, run0 table a (cfg 2 (true::L) (w "010111" ++ S)) =
      some (cfg 1 L (w "101100" ++ T)))
    (hd : ∀ L, run0 table b (cfg 3 (w "011001" ++ L) (w "01100" ++ T)) =
      some (cfg 1 (w "111" ++ L) (w "100001111" ++ S'))) :
    run0 table (150*n+276+a+b) (boundary (n+1) S) = some (boundary (n+2) S') := by
  have h1 := preSuffix n S
  have hrot : rep W (n+2) ++ [true] = true :: rep J (n+2) := by
    exact (rotate true (w "11101") (n+2)).symm
  rw [hrot] at h1
  have h2 := hc (rep J (n+2))
  have h3 := middle n T
  have h4 := hd (rep U (n+1) ++ w "011")
  have h5 := finish n S'
  have h := join0 (join0 (join0 (join0 h1 h2) h3) (by simpa only [List.append_assoc] using h4)) (by simpa only [List.append_assoc] using h5)
  rw [show 150*n+276+a+b = 88*n+165+a+(50*n+85)+b+(12*n+26) by omega]
  exact h

#print axioms preSuffix
#print axioms middle
#print axioms finish
#print axioms return_of_suffix
end BB6Coverage.Agent31Pump.Raw112CarrySweeps
