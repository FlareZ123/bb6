import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF141
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none
def b3 : List Bool := [false,true,true,true]
def b6 : List Bool := [false,true,true,true,true,true,true]
def b8 : List Bool := [false,true,true,true,true,true,true,true,true]
def p2 : List Bool := [false,false,true,true]
def p4 : List Bool := [false,false,false,false,true,true]
def p5 : List Bool := [false,false,false,false,false,true,true]
def p7 : List Bool := [false,false,false,false,false,false,false,true,true]
def p10 : List Bool := [false,false,false,false,false,false,false,false,false,false,true,true]
def p12 : List Bool := [false,false,false,false,false,false,false,false,false,false,false,false,true,true]
def f01 : List Bool := [false,true]
def f011 : List Bool := [false,true,true]
def f00011 : List Bool := [false,false,false,true,true]
def extra : List Bool := [true,true]
def r00 : List Bool := [false,false]
def E (L R : List Bool) : Z0 := ⟨4,L,R⟩
theorem enter (R : List Bool) :
    run0 table 18 (E ([]) (p4++p7++R)) = some (E (f01++b8) (f00011++R)) := by rfl
theorem carry7 (L R : List Bool) :
    run0 table 15 (E (f01++L) (f00011++p7++R)) = some (E (f01++b8++L) (f00011++R)) := by rfl
theorem carry5 (L R : List Bool) :
    run0 table 15 (E (f01++L) (f00011++p5++R)) = some (E (f01++b8++L) (f011++R)) := by rfl
theorem short2 (L R : List Bool) :
    run0 table 9 (E (f01++L) (f00011++p2++R)) = some (E (f01++b6++L) (f01++R)) := by rfl
theorem shortend (L : List Bool) :
    run0 table 9 (E (f01++L) (f00011++extra)) = some (E (b6++L) (r00)) := by rfl
theorem carry3A (L R : List Bool) :
    run0 table 6 (E (f01++L) (f01++p2++R)) = some (E (f01++b3++L) (f01++R)) := by rfl
theorem carryAend (L : List Bool) :
    run0 table 6 (E (f01++L) (f01++extra)) = some (E (b3++L) (r00)) := by rfl
theorem carry3B (L R : List Bool) :
    run0 table 4 (E (f01++L) (f011++p2++R)) = some (E (f01++b3++L) (f011++R)) := by rfl
theorem carryBend (L : List Bool) :
    run0 table 4 (E (f01++L) (f011)) = some (E (f01++b3++L) ([])) := by rfl
theorem blankReturn (L : List Bool) :
    run0 table 12 (E (f01++L) ([])) = some (E (L) (p5)) := by rfl
theorem drain3first (L : List Bool) :
    run0 table 14 (E (b3++L) (r00)) = some (E (L) (p7)) := by rfl
theorem drain6first (L : List Bool) :
    run0 table 17 (E (b6++L) (r00)) = some (E (L) (p10)) := by rfl
theorem drain3next (L R : List Bool) :
    run0 table 14 (E (b3++L) (p7++R)) = some (E (L) (p7++p2++R)) := by rfl
theorem drain6next (L R : List Bool) :
    run0 table 17 (E (b6++L) (p7++R)) = some (E (L) (p10++p2++R)) := by rfl
theorem drain3Bfirst (L : List Bool) :
    run0 table 14 (E (b3++L) (p5)) = some (E (L) (p7++extra)) := by rfl
theorem drain8Bfirst (L R : List Bool) :
    run0 table 19 (E (b8++L) (p7++R)) = some (E (L) (p12++p2++R)) := by rfl
theorem drain8Afirst (L R : List Bool) :
    run0 table 19 (E (b8++L) (p10++R)) = some (E (L) (p12++p5++R)) := by rfl
theorem drain8next (L R : List Bool) :
    run0 table 19 (E (b8++L) (p12++R)) = some (E (L) (p12++p7++R)) := by rfl
theorem finish (R : List Bool) :
    run0 table 11 (E ([]) (p12++R)) = some (E ([]) (p4++p7++R)) := by rfl

theorem scan (k : Nat) (R : List Bool) :
    run0 table (18+15*k) (E [] (p4++rep p7 (k+1)++R)) =
      some (E (f01++rep b8 (k+1)) (f00011++R)) := by
  have a := enter (rep p7 k++R)
  have b := sweepR table 4 f01 f00011 p7 b8 15 carry7 k b8 R
  simp only [List.append_assoc] at a b
  have h := join0 a b
  simpa only [E,rep,List.append_assoc,rep_snoc] using h

theorem shortA (k : Nat) (L : List Bool) :
    run0 table (9+6*k) (E (f01++L) (f00011++rep p2 k++extra)) =
      some (E (rep b3 k++b6++L) r00) := by
  cases k with
  | zero => simpa only [rep,List.nil_append,List.append_nil,Nat.mul_zero,Nat.add_zero] using shortend L
  | succ j =>
    have a := short2 L (rep p2 j++extra)
    have b := sweepR table 4 f01 f01 p2 b3 6 carry3A j (b6++L) extra
    have c := carryAend (rep b3 j++b6++L)
    simp only [List.append_assoc] at a b c
    have h := join0 (join0 a b) c
    simpa only [E,rep,List.append_assoc,Nat.mul_succ,Nat.add_assoc] using h

theorem drainA (k : Nat) (L : List Bool) :
    run0 table (14*k+17) (E (rep b3 k++b6++L) r00) =
      some (E L (p10++rep p2 k)) := by
  cases k with
  | zero => simpa only [rep,List.nil_append,List.append_nil,Nat.mul_zero,Nat.zero_add] using drain6first L
  | succ j =>
    have a := drain3first (rep b3 j++b6++L)
    have b := sweepL table 4 [] p7 b3 p2 14 (by
      intro X Y
      simpa only [E,List.nil_append] using drain3next X Y) j (b6++L) []
    have c := drain6next L (rep p2 j)
    simp only [List.nil_append,List.append_nil,List.append_assoc] at a b c
    have h := join0 (join0 a b) c
    rw [show 14*(j+1)+17=14+14*j+17 by omega]
    simpa only [E,rep,List.append_assoc] using h

theorem drain8A (k : Nat) :
    run0 table (19+19*k) (E (rep b8 (k+1)) (p10++rep p2 k)) =
      some (E [] (p12++rep p7 k++p5++rep p2 k)) := by
  have a := drain8Afirst (rep b8 k) (rep p2 k)
  have b := sweepL table 4 [] p12 b8 p7 19 (by
    intro X Y
    simpa only [E,List.nil_append] using drain8next X Y) k [] (p5++rep p2 k)
  simp only [List.nil_append,List.append_nil,List.append_assoc] at a b
  have h := join0 a b
  simpa only [E,rep,List.append_assoc] using h

theorem shortB (k : Nat) (L : List Bool) :
    run0 table (4*k+4+12) (E (f01++L) (f011++rep p2 k)) =
      some (E (rep b3 (k+1)++L) p5) := by
  have a := sweepR table 4 f01 f011 p2 b3 4 carry3B k L []
  have b := carryBend (rep b3 k++L)
  have c := blankReturn (b3++rep b3 k++L)
  simp only [List.append_nil,List.append_assoc] at a b c
  have h := join0 (join0 a b) c
  simpa only [E,rep,List.append_assoc] using h

theorem drainB (k : Nat) (L : List Bool) :
    run0 table (14+14*k) (E (rep b3 (k+1)++L) p5) =
      some (E L (p7++rep p2 k++extra)) := by
  have a := drain3Bfirst (rep b3 k++L)
  have b := sweepL table 4 [] p7 b3 p2 14 (by
    intro X Y
    simpa only [E,List.nil_append] using drain3next X Y) k L extra
  simp only [List.nil_append,List.append_assoc] at a b
  have h := join0 a b
  simpa only [E,rep,List.append_assoc] using h

theorem drain8B (k : Nat) :
    run0 table (19+19*(k+1)) (E (rep b8 (k+2)) (p7++rep p2 k++extra)) =
      some (E [] (p12++rep p7 (k+1)++rep p2 (k+1)++extra)) := by
  have a := drain8Bfirst (rep b8 (k+1)) (rep p2 k++extra)
  have b := sweepL table 4 [] p12 b8 p7 19 (by
    intro X Y
    simpa only [E,List.nil_append] using drain8next X Y) (k+1) [] (p2++rep p2 k++extra)
  simp only [List.nil_append,List.append_nil,List.append_assoc] at a b
  have h := join0 a b
  simpa only [E,rep,List.append_assoc] using h

def A (k : Nat) : Z0 := E [] (p4++rep p7 (k+1)++rep p2 k++extra)
def B (k : Nat) : Z0 := E [] (p4++rep p7 (k+1)++p5++rep p2 k)

theorem AB (k : Nat) : ∃ t, 0<t ∧ run0 table t (A k) = some (B k) := by
  have a := scan k (rep p2 k++extra)
  have b := shortA k (rep b8 (k+1))
  have c := drainA k (rep b8 (k+1))
  have d := drain8A k
  have e := finish (rep p7 k++p5++rep p2 k)
  simp only [List.append_assoc] at a b c d e
  have h := join0 (join0 (join0 (join0 a b) c) d) e
  refine ⟨(18+15*k)+(9+6*k)+(14*k+17)+(19+19*k)+11,by omega,?_⟩
  simpa only [A,B,E,rep,List.append_assoc] using h

theorem BA (k : Nat) : ∃ t, 0<t ∧ run0 table t (B k) = some (A (k+1)) := by
  have a := scan k (p5++rep p2 k)
  have b := carry5 (rep b8 (k+1)) (rep p2 k)
  have c := shortB k (rep b8 (k+2))
  have d := drainB k (rep b8 (k+2))
  have e := drain8B k
  have f := finish (rep p7 (k+1)++rep p2 (k+1)++extra)
  simp only [List.append_assoc] at a b c d e f
  have b' : run0 table 15 (E (f01++rep b8 (k+1)) (f00011++(p5++rep p2 k))) =
      some (E (f01++rep b8 (k+2)) (f011++rep p2 k)) := by
    simpa only [rep,List.append_assoc] using b
  have h := join0 (join0 (join0 (join0 (join0 a b') c) d) e) f
  refine ⟨(18+15*k)+15+(4*k+4+12)+(14+14*k)+(19+19*(k+1))+11,by omega,?_⟩
  simpa only [A,B,E,rep,List.append_assoc] using h

theorem first : run0 table 87 ⟨0,[],[]⟩ = some (A 0) := by rfl
theorem next (k : Nat) : ∃ t, 0<t ∧ run0 table t (A k) = some (A (k+1)) := by
  obtain ⟨t,ht,h⟩ := AB k
  obtain ⟨s,hs,g⟩ := BA k
  exact ⟨t+s,by omega,join0 h g⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table A 87 first next m hm
#print axioms never
end BB6.Agent8Raw54.RF141
