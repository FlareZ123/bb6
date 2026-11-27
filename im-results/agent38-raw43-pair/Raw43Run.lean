import Raw43Octal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43Run
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent38Raw43Octal (rename bits zeros ones blocks blocks_snoc blocks_add scan)

def table0 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none

def table (s : Bool) : PartialMachine := fun (q,b) =>
  (table0 (rename s q,b)).map (Option.map (fun mv => {mv with next := rename s mv.next}))

def Reach (s : Bool) (a b : Z0) : Prop := ∃ t, run0 (table s) t a = some b

theorem reach_refl (s : Bool) (a : Z0) : Reach s a a := ⟨0,rfl⟩
theorem reach_trans {s : Bool} {a b c : Z0} (h : Reach s a b) (g : Reach s b c) : Reach s a c := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := g
  exact ⟨n+m,join0 hn hm⟩

def Q := bits "1100110000"
def P := bits "0111110111"
def Pout := bits "1100001100"
def Bbase := bits "01111011111"
def H := bits "00111"
def front (k : Nat) (W : List Bool) : Z0 := ⟨0,[],bits "000000011000" ++ blocks Q k ++ W⟩

theorem odd1 (s : Bool) (W : List Bool) :
    run0 (table s) 11 ⟨0,[],bits "000000011000"++W⟩ = some ⟨0,[],bits "0011000011000"++W⟩ := by cases s <;> rfl

theorem even1 (s : Bool) (W : List Bool) :
    run0 (table s) 45 ⟨0,[],bits "0011000011000"++W⟩ = some ⟨0,[],bits "00000001101110"++W⟩ := by cases s <;> rfl

theorem odd2 (s : Bool) (W : List Bool) :
    run0 (table s) 11 ⟨0,[],bits "00000001101110"++W⟩ = some ⟨0,[],bits "001100001101110"++W⟩ := by cases s <;> rfl

theorem prepare0 (s : Bool) (W : List Bool) :
    run0 (table s) 28 ⟨0,[],bits "001100001101110"++W⟩ = some (scan 3 (H++Bbase) W) := by cases s <;> cases W <;> rfl

theorem prepare1 (s : Bool) (L W : List Bool) :
    run0 (table s) 30 (scan 3 (H++L) (Q++W)) = some (scan 3 (H++P++L) W) := by cases s <;> cases W <;> rfl

theorem prepareMany (s : Bool) (k : Nat) (L W : List Bool) :
    run0 (table s) (30*k) (scan 3 (H++L) (blocks Q k++W)) = some (scan 3 (H++blocks P k++L) W) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 := prepare1 s L (blocks Q k++W)
    have h2 := ih (P++L)
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    rw [Nat.mul_succ,Nat.add_comm (30*k) 30]
    simpa only [blocks,List.append_assoc,← List.append_assoc (blocks P k) P L,blocks_snoc P k] using h

theorem prepare (s : Bool) (k : Nat) (W : List Bool) :
    run0 (table s) (95+30*k) (front k W) = some (scan 3 (H++blocks P k++Bbase) W) := by
  have h1 := odd1 s (blocks Q k++W)
  have h2 := even1 s (blocks Q k++W)
  have h3 := odd2 s (blocks Q k++W)
  have h4 := prepare0 s (blocks Q k++W)
  have h5 := prepareMany s k Bbase W
  simpa only [front,List.append_assoc] using join0 (join0 (join0 (join0 h1 h2) h3) h4) (by simpa only [List.append_assoc] using h5)

theorem unwind1 (s : Bool) (L R : List Bool) :
    run0 (table s) 30 ⟨0,P++L,zeros 5++R⟩ = some ⟨0,L,zeros 5++Pout++R⟩ := by cases s <;> rfl

theorem unwindMany (s : Bool) (k : Nat) (L R : List Bool) :
    run0 (table s) (30*k) ⟨0,blocks P k++L,zeros 5++R⟩ = some ⟨0,L,zeros 5++blocks Pout k++R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := unwind1 s (blocks P k++L) R
    have h2 := ih (Pout++R)
    have h := join0 (by simpa only [List.append_assoc] using h1) h2
    rw [Nat.mul_succ,Nat.add_comm (30*k) 30]
    simpa only [blocks,List.append_assoc,← List.append_assoc (blocks Pout k) Pout R,blocks_snoc Pout k] using h

theorem unwind0 (s : Bool) (R : List Bool) :
    run0 (table s) 31 ⟨0,Bbase,zeros 5++R⟩ = some ⟨0,[],bits "0000000110001100"++R⟩ := by cases s <;> rfl

theorem rotation (k : Nat) : bits "1100" ++ blocks Pout k = blocks Q k ++ bits "1100" := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he : bits "1100" ++ Pout = Q ++ bits "1100" := rfl
    rw [blocks,blocks,← List.append_assoc,he,List.append_assoc,ih,List.append_assoc]

theorem finish (s : Bool) (k : Nat) (R : List Bool) :
    run0 (table s) (30*k+31) ⟨0,blocks P k++Bbase,zeros 5++R⟩ = some (front k (bits "1100"++R)) := by
  have h1 := unwindMany s k Bbase R
  have h2 := unwind0 s (blocks Pout k++R)
  have h := join0 h1 (by simpa only [List.append_assoc] using h2)
  have he : bits "0000000110001100" = bits "000000011000"++bits "1100" := rfl
  simpa only [front,he,List.append_assoc,← List.append_assoc (bits "1100") (blocks Pout k) R,rotation k] using h

def low0 := bits "0000000000"
def low1 := bits "11111000000000"
def low2 := bits "01111110"
def low3 := bits "111111111110"
def low4 := bits "11001100111111111100"
def R0 := bits "000111000000000"
def R2 := bits "0001111111110"

theorem lowLocal0 (s : Bool) (L W : List Bool) :
    run0 (table s) 10 (scan 3 (H++L) (low0++W)) = some ⟨0,L,R0++W⟩ := by cases s <;> rfl
theorem lowLocal1 (s : Bool) (L W : List Bool) :
    run0 (table s) 82 (scan 3 (H++L) (low1++W)) = some ⟨0,L,zeros 5++bits "11000001111110"++W⟩ := by cases s <;> rfl
theorem lowLocal2 (s : Bool) (L W : List Bool) :
    run0 (table s) 10 (scan 3 (H++L) (low2++W)) = some ⟨0,L,R2++W⟩ := by cases s <;> rfl

theorem lowFinish0 (s : Bool) (k : Nat) (W : List Bool) :
    Reach s ⟨0,blocks P k++Bbase,R0++W⟩ (front k (low1++W)) := by
  cases k with
  | zero => exact ⟨31,by cases s <;> rfl⟩
  | succ k =>
    have h1 : run0 (table s) 30 ⟨0,P++(blocks P k++Bbase),R0++W⟩ = some ⟨0,blocks P k++Bbase,zeros 5++bits "110000"++low1++W⟩ := by cases s <;> rfl
    have h2 := finish s k (bits "110000"++low1++W)
    refine ⟨30+(30*k+31),?_⟩
    have he : bits "1100"++bits "110000"=Q := rfl
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    simpa only [blocks,front,List.append_assoc,← List.append_assoc (bits "1100") (bits "110000") _,he,← List.append_assoc (blocks Q k) Q _,blocks_snoc Q k] using h

theorem lowFinish2 (s : Bool) (k : Nat) (W : List Bool) :
    Reach s ⟨0,blocks P k++Bbase,R2++W⟩ (front k (low3++W)) := by
  cases k with
  | zero => exact ⟨31,by cases s <;> rfl⟩
  | succ k =>
    have h1 : run0 (table s) 30 ⟨0,P++(blocks P k++Bbase),R2++W⟩ = some ⟨0,blocks P k++Bbase,zeros 5++bits "110000"++low3++W⟩ := by cases s <;> rfl
    have h2 := finish s k (bits "110000"++low3++W)
    refine ⟨30+(30*k+31),?_⟩
    have he : bits "1100"++bits "110000"=Q := rfl
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    simpa only [blocks,front,List.append_assoc,← List.append_assoc (bits "1100") (bits "110000") _,he,← List.append_assoc (blocks Q k) Q _,blocks_snoc Q k] using h

theorem phase0 (s : Bool) (k : Nat) (W : List Bool) : ∃ t, 0<t ∧ run0 (table s) t (front k (low0++W)) = some (front k (low1++W)) := by
  have h1 := prepare s k (low0++W)
  have h2 := lowLocal0 s (blocks P k++Bbase) W
  obtain ⟨t,h3⟩ := lowFinish0 s k W
  exact ⟨95+30*k+10+t,by omega,join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) h3⟩

theorem phase1 (s : Bool) (k : Nat) (W : List Bool) : Reach s (front k (low1++W)) (front (k+1) (low2++W)) := by
  have h1 := prepare s k (low1++W)
  have h2 := lowLocal1 s (blocks P k++Bbase) W
  have h3 := finish s k (bits "11000001111110"++W)
  refine ⟨95+30*k+82+(30*k+31),?_⟩
  have he : bits "1100"++bits "11000001111110"=Q++low2 := rfl
  have h := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  simpa only [front,blocks,List.append_assoc,← List.append_assoc (bits "1100") (bits "11000001111110") _,he,← List.append_assoc (blocks Q k) Q _,blocks_snoc Q k] using h

theorem phase2 (s : Bool) (k : Nat) (W : List Bool) : Reach s (front k (low2++W)) (front k (low3++W)) := by
  have h1 := prepare s k (low2++W)
  have h2 := lowLocal2 s (blocks P k++Bbase) W
  obtain ⟨t,h3⟩ := lowFinish2 s k W
  exact ⟨95+30*k+10+t,join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) h3⟩
def Alt := bits "01"
def AltR := bits "10"
def Tblock (m : Nat) := bits "1110" ++ blocks AltR m ++ bits "111"
def Tbase := bits "0101010101110111"
def Ubase := bits "1010101010111100111110111"

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  unfold ones
  rw [List.replicate_append_replicate]
theorem zeros_add (a b : Nat) : zeros (a+b) = zeros a ++ zeros b := by
  unfold zeros
  rw [List.replicate_append_replicate]
theorem altRotate (m : Nat) : bits "1" ++ blocks Alt m = blocks AltR m ++ bits "1" := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : bits "1"++Alt=AltR++bits "1" := rfl
    rw [blocks,blocks,← List.append_assoc,he,List.append_assoc,ih,List.append_assoc]

theorem cPair (s : Bool) (L W : List Bool) :
    run0 (table s) 2 (scan 2 L (bits "11"++W)) = some (scan 2 (Alt++L) W) := by cases s <;> cases W <;> rfl

theorem cPairs (s : Bool) (m : Nat) (L W : List Bool) :
    run0 (table s) (2*m) (scan 2 L (ones (2*m)++W)) = some (scan 2 (blocks Alt m++L) W) := by
  induction m generalizing L with
  | zero => rfl
  | succ m ih =>
    have h1 := cPair s L (ones (2*m)++W)
    have h2 := ih (Alt++L)
    have h := join0 h1 h2
    rw [Nat.mul_succ,Nat.add_comm (2*m) 2,ones_add]
    have he : ones 2=bits "11" := rfl
    simpa only [he,blocks,List.append_assoc,← List.append_assoc (blocks Alt m) Alt L,blocks_snoc Alt m] using h

theorem dEntry (s : Bool) (L W : List Bool) :
    run0 (table s) 7 (scan 3 (false::L) (bits "11"++W)) = some (scan 2 (bits "11"++L) (true::W)) := by cases s <;> rfl

theorem dToC (s : Bool) (m : Nat) (L W : List Bool) :
    run0 (table s) (7+2*m) (scan 3 (false::L) (ones (2*m+2)++W)) = some (scan 2 (blocks Alt m++bits "11"++L) (true::W)) := by
  have h1 := dEntry s L (ones (2*m)++W)
  have h2 := cPairs s m (bits "11"++L) (true::W)
  have he : true::(ones (2*m)++W) = ones (2*m)++true::W := by
    have htrue : ∀ V : List Bool, true::V = ones 1++V := fun _ => rfl
    rw [htrue (ones (2*m)++W),htrue W,← List.append_assoc,← ones_add, Nat.add_comm 1 (2*m),ones_add,List.append_assoc]
  have h := join0 h1 (by simpa only [he] using h2)
  rw [Nat.add_comm (2*m) 2,ones_add,show ones 2=bits "11" by rfl]
  simpa only [List.append_assoc] using h

theorem tPush (s : Bool) (m : Nat) (L W : List Bool) :
    run0 (table s) (13+2*m) (scan 3 (false::L) (ones (2*m+2)++zeros 5++W)) = some (scan 3 (false::(Tblock m++L)) W) := by
  have h1 := dToC s m L (zeros 5++W)
  have h2 : run0 (table s) 6 (scan 2 (blocks Alt m++bits "11"++L) (true::(zeros 5++W))) = some (scan 3 (bits "011101"++(blocks Alt m++bits "11"++L)) W) := by cases s <;> cases W <;> rfl
  have he : bits "011101" = bits "01110"++bits "1" := rfl
  have he2 : bits "1"++bits "11"=bits "111" := rfl
  have h := join0 h1 h2
  rw [show 7+2*m+6=13+2*m by omega] at h
  simpa only [Tblock,he,List.append_assoc,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m,← List.append_assoc (bits "1") (bits "11") _,he2,show bits "01110"=false::bits "1110" by rfl,List.cons_append] using h

theorem aAlt (s : Bool) (L R : List Bool) :
    run0 (table s) 12 ⟨0,bits "010"++L,zeros 3++R⟩ = some ⟨0,false::L,zeros 3++bits "11"++R⟩ := by cases s <;> rfl

theorem aAlts (s : Bool) (m : Nat) (L R : List Bool) :
    run0 (table s) (12*m) ⟨0,false::(blocks AltR m++L),zeros 3++R⟩ = some ⟨0,false::L,zeros 3++ones (2*m)++R⟩ := by
  induction m generalizing R with
  | zero => rfl
  | succ m ih =>
    have h1 := aAlt s (blocks AltR m++L) R
    have h2 := ih (bits "11"++R)
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    rw [Nat.mul_succ,Nat.add_comm (12*m) 12,Nat.mul_succ,ones_add]
    simpa only [blocks,List.append_assoc,show bits "010"=false::AltR by rfl,List.cons_append,show ones 2=bits "11" by rfl] using h

theorem aTail (s : Bool) (L R : List Bool) :
    run0 (table s) 14 ⟨0,false::(bits "111"++L),zeros 3++R⟩ = some ⟨0,L,zeros 5++bits "11"++R⟩ := by cases s <;> rfl

theorem tPop (s : Bool) (m : Nat) (L R : List Bool) :
    run0 (table s) (17+12*m) ⟨0,Tblock m++L,zeros 5++R⟩ = some ⟨0,L,zeros 5++ones (2*m+2)++zeros 5++R⟩ := by
  have h1 : run0 (table s) 3 ⟨0,Tblock m++L,zeros 5++R⟩ = some ⟨0,false::(blocks AltR m++bits "111"++L),zeros 3++zeros 5++R⟩ := by
    simp only [Tblock,List.append_assoc]; cases s <;> rfl
  have h2 := aAlts s m (bits "111"++L) (zeros 5++R)
  have h3 := aTail s L (ones (2*m)++zeros 5++R)
  have h := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  rw [show 3+12*m+14=17+12*m by omega] at h
  rw [Nat.add_comm (2*m) 2,ones_add,show ones 2=bits "11" by rfl]
  simpa only [List.append_assoc] using h

theorem tTurn (s : Bool) (m : Nat) (L U : List Bool) :
    run0 (table s) (36+14*m) (scan 3 (false::L) (ones (2*m+2)++zeros 10++U)) = some ⟨0,L,zeros 5++ones (2*m+4)++zeros 4++U⟩ := by
  have h1 := dToC s m L (zeros 10++U)
  have h2 : run0 (table s) 15 (scan 2 (blocks Alt m++bits "11"++L) (true::(zeros 10++U))) = some ⟨0,bits "01"++(blocks Alt m++bits "11"++L),zeros 3++bits "11"++zeros 4++U⟩ := by cases s <;> rfl
  have he : bits "01" = false::bits "1" := rfl
  have hh : bits "1"++bits "11"=bits "111" := rfl
  have H12 := join0 h1 h2
  have H12' : run0 (table s) (7+2*m+15) (scan 3 (false::L) (ones (2*m+2)++(zeros 10++U))) = some ⟨0,false::(blocks AltR m++bits "111"++L),zeros 3++bits "11"++zeros 4++U⟩ := by
    simpa only [he,List.cons_append,List.append_assoc,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m,← List.append_assoc (bits "1") (bits "11") _,hh] using H12
  have h3 := aAlts s m (bits "111"++L) (bits "11"++zeros 4++U)
  have h4 := aTail s L (ones (2*m)++bits "11"++zeros 4++U)
  have h := join0 (join0 H12' (by simpa only [List.append_assoc] using h3)) (by simpa only [List.append_assoc] using h4)
  rw [show 7+2*m+15+12*m+14=36+14*m by omega] at h
  have he3 : ones (2*m+4) = bits "11"++ones (2*m)++bits "11" := by
    rw [show 2*m+4=2+2*m+2 by omega,ones_add,ones_add,show ones 2=bits "11" by rfl]
  simpa only [he3,List.append_assoc] using h

def tRuns : List Nat → List Bool
  | [] => []
  | m::ms => ones (2*m+2)++zeros 5++tRuns ms

theorem tSweep (s : Bool) (ms : List Nat) (n : Nat) (L U : List Bool) :
    Reach s (scan 3 (false::L) (tRuns ms++ones (2*n+2)++zeros 10++U)) ⟨0,L,zeros 5++tRuns ms++ones (2*n+4)++zeros 4++U⟩ := by
  induction ms generalizing L with
  | nil => exact ⟨36+14*n,by simpa only [tRuns,List.nil_append,List.append_nil] using tTurn s n L U⟩
  | cons m ms ih =>
    have h1 := tPush s m L (tRuns ms++ones (2*n+2)++zeros 10++U)
    obtain ⟨t,h2⟩ := ih (Tblock m++L)
    have h3 := tPop s m L (tRuns ms++ones (2*n+4)++zeros 4++U)
    refine ⟨13+2*m+t+(17+12*m),?_⟩
    simpa only [tRuns,List.append_assoc] using join0 (join0 h1 h2) (by simpa only [List.append_assoc] using h3)

theorem tStart (s : Bool) (L W : List Bool) :
    run0 (table s) 18 (scan 3 (H++L) (low3++W)) = some (scan 3 (false::(Tbase++L)) W) := by cases s <;> cases W <;> rfl

theorem tFinish (s : Bool) (L R : List Bool) :
    run0 (table s) 76 ⟨0,Tbase++L,zeros 5++R⟩ = some ⟨0,L,zeros 5++bits "1100111111111100"++R⟩ := by cases s <;> rfl

theorem phase3 (s : Bool) (k : Nat) (ms : List Nat) (n : Nat) (U : List Bool) :
    Reach s (front k (low3++tRuns ms++ones (2*n+2)++zeros 10++U)) (front k (low4++tRuns ms++ones (2*n+4)++zeros 4++U)) := by
  let L := blocks P k++Bbase
  let R := tRuns ms++ones (2*n+4)++zeros 4++U
  have h1 := prepare s k (low3++tRuns ms++ones (2*n+2)++zeros 10++U)
  have h2 := tStart s L (tRuns ms++ones (2*n+2)++zeros 10++U)
  obtain ⟨t,h3⟩ := tSweep s ms n (Tbase++L) U
  have h4 := tFinish s L R
  have h5 := finish s k (bits "1100111111111100"++R)
  refine ⟨95+30*k+18+t+76+(30*k+31),?_⟩
  have he : bits "1100"++bits "1100111111111100"=low4 := rfl
  have h := join0 (join0 (join0 (join0 h1 (by simpa only [L,List.append_assoc] using h2)) h3) (by simpa only [R,List.append_assoc] using h4)) (by simpa only [R,L,List.append_assoc] using h5)
  simpa only [front, L,R,List.append_assoc,← List.append_assoc (bits "1100") (bits "1100111111111100") _,he] using h

#print axioms phase0
#print axioms phase1
#print axioms phase2
#print axioms phase3

def a := bits "0000011"
def b := bits "000000000011"
def c := bits "0000000000111111"
def d := bits "000000000011111111"
def e := bits "000011"
def f := bits "000001111"
def g := bits "0000111111"
def h := bits "000011111111"
def Chead := bits "1110"
def K0 := bits "101111110111101111110101010111100111110111"
def K := bits "1011111101111011110"
def AEnd := bits "1010111101011110"
def Kout := bits "1100011000110000011"
def Aout := bits "110001111000110011111"
def M := bits "1111110111111111110"
def J := bits "1010101111111111111110111"
def I0 := bits "101111111111101111110"
def I := bits "10101111111111101111110"
def Mout := bits "1100000000001100000"
def code (r : Nat) : List Bool := match r with
  | 0 => b++a
  | 1 => a++d++e++a
  | n+2 => a++c++blocks (f++g) n++f++h++e++a

theorem uStart (s : Bool) (L W : List Bool) :
    run0 (table s) 36 (scan 3 (H++L) (low4++W)) = some (scan 0 (Ubase++L) W) := by cases s <;> cases W <;> rfl

theorem uPrep0 (s : Bool) (L W : List Bool) :
    run0 (table s) 269 (scan 0 (Ubase++L) (ones 10++zeros 4++ones 2++zeros 5++W)) = some (scan (rename s 4) (I0++J++L) W) := by cases s <;> cases W <;> rfl

theorem uPrep1 (s : Bool) (L W : List Bool) :
    run0 (table s) 55 (scan 0 (Ubase++L) (ones 8++zeros 5++ones 4++zeros 4++W)) = some (scan 2 (Chead++K0++L) W) := by cases s <;> cases W <;> rfl

theorem uCpush (s : Bool) (L W : List Bool) :
    run0 (table s) 43 (scan 2 (Chead++L) (ones 6++zeros 5++ones 4++zeros 4++W)) = some (scan 2 (Chead++K++L) W) := by cases s <;> cases W <;> rfl

theorem uCturn (s : Bool) (L W : List Bool) :
    run0 (table s) 24 (scan 2 (Chead++L) (ones 8++zeros 4++W)) = some (scan 0 (AEnd++L) W) := by cases s <;> cases W <;> rfl

theorem uApop (s : Bool) (L W : List Bool) :
    run0 (table s) 97 (scan 0 (AEnd++L) (ones 2++zeros 5++W)) = some ⟨0,L,zeros 2++Aout++W⟩ := by cases s <;> rfl

theorem uKpop (s : Bool) (L R : List Bool) :
    run0 (table s) 59 ⟨0,K++L,zeros 2++R⟩ = some ⟨0,L,zeros 2++Kout++R⟩ := by cases s <;> rfl

theorem uKbase (s : Bool) (L R : List Bool) :
    run0 (table s) 189 ⟨0,K0++L,zeros 2++R⟩ = some (scan (rename s 4) (M++J++L) R) := by cases s <;> cases R <;> rfl

theorem uEreadK (s : Bool) (L R : List Bool) :
    run0 (table s) 49 (scan (rename s 4) L (Kout++R)) = some (scan (rename s 4) (M++L) R) := by cases s <;> cases R <;> rfl

theorem uEreadA (s : Bool) (L R : List Bool) :
    run0 (table s) 55 (scan (rename s 4) L (Aout++R)) = some (scan (rename s 4) (I0++L) R) := by cases s <;> cases R <;> rfl

theorem uEread2 (s : Bool) (L R : List Bool) :
    run0 (table s) 2 (scan (rename s 4) (I0++L) (ones 2++R)) = some (scan (rename s 4) (I++L) R) := by cases s <;> cases R <;> rfl

theorem uEcarry0 (s : Bool) (L R : List Bool) :
    run0 (table s) 88 (scan (rename s 4) (I++L) (b++R)) = some ⟨0,L,zeros 2++ones 2++a++d++e++R⟩ := by cases s <;> rfl

theorem uEcarryS (s : Bool) (L R : List Bool) :
    run0 (table s) 118 (scan (rename s 4) (I++L) (a++zeros 10++R)) = some ⟨0,L,zeros 2++ones 2++a++c++f++zeros 4++R⟩ := by cases s <;> rfl

theorem uMpop (s : Bool) (L R : List Bool) :
    run0 (table s) 39 ⟨0,M++L,zeros 2++R⟩ = some ⟨0,L,zeros 2++Mout++R⟩ := by cases s <;> rfl

theorem uJpop (s : Bool) (L R : List Bool) :
    run0 (table s) 65 ⟨0,J++L,zeros 2++R⟩ = some ⟨0,L,zeros 5++ones 2++zeros 14++ones 6++R⟩ := by cases s <;> rfl

def cycleIn := ones 6++zeros 5++ones 4++zeros 4

theorem uCpushMany (s : Bool) (n : Nat) (L W : List Bool) :
    Reach s (scan 2 (Chead++L) (blocks cycleIn n++W)) (scan 2 (Chead++blocks K n++L) W) := by
  induction n generalizing L with
  | zero => exact reach_refl s _
  | succ n ih =>
    have h1 := uCpush s L (blocks cycleIn n++W)
    have h2 := ih (K++L)
    have H1 : Reach s (scan 2 (Chead++L) (blocks cycleIn (n+1)++W)) (scan 2 (Chead++(K++L)) (blocks cycleIn n++W)) := ⟨43,by simpa only [blocks,cycleIn,List.append_assoc] using h1⟩
    simpa only [blocks,List.append_assoc,← List.append_assoc (blocks K n) K L,blocks_snoc K n] using reach_trans H1 h2

theorem uKpopMany (s : Bool) (n : Nat) (L R : List Bool) :
    Reach s ⟨0,blocks K n++L,zeros 2++R⟩ ⟨0,L,zeros 2++blocks Kout n++R⟩ := by
  induction n generalizing R with
  | zero => exact reach_refl s _
  | succ n ih =>
    have h1 := uKpop s (blocks K n++L) R
    have h2 := ih (Kout++R)
    obtain ⟨t,h2⟩ := h2
    have h := join0 h1 (by simpa only [List.append_assoc] using h2)
    exact ⟨59+t,by simpa only [blocks,List.append_assoc,← List.append_assoc (blocks Kout n) Kout R,blocks_snoc Kout n] using h⟩

theorem uEreadMany (s : Bool) (n : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (blocks Kout n++W)) (scan (rename s 4) (blocks M n++L) W) := by
  induction n generalizing L with
  | zero => exact reach_refl s _
  | succ n ih =>
    have h1 := uEreadK s L (blocks Kout n++W)
    obtain ⟨t,h2⟩ := ih (M++L)
    exact ⟨49+t,by simpa only [blocks,List.append_assoc,← List.append_assoc (blocks M n) M L,blocks_snoc M n] using join0 h1 h2⟩

def transformed (r : Nat) : List Bool := match r with
  | 0 => ones 10++zeros 4++ones 2++zeros 5
  | n+1 => ones 8++zeros 5++ones 4++zeros 4++blocks cycleIn n++ones 8++zeros 4++ones 2++zeros 5

theorem uDprep (s : Bool) (r : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++W)) (scan (rename s 4) (I0++blocks M r++J++L) W) := by
  cases r with
  | zero => exact ⟨269,by simpa only [transformed,blocks,List.append_assoc,List.nil_append,List.append_nil] using uPrep0 s L W⟩
  | succ n =>
    have h1 := uPrep1 s L (blocks cycleIn n++ones 8++zeros 4++ones 2++zeros 5++W)
    have h2 := uCpushMany s n (K0++L) (ones 8++zeros 4++ones 2++zeros 5++W)
    have h3 := uCturn s (blocks K n++K0++L) (ones 2++zeros 5++W)
    have h4 := uApop s (blocks K n++K0++L) W
    have h5 := uKpopMany s n (K0++L) (Aout++W)
    have h6 := uKbase s L (blocks Kout n++Aout++W)
    have h7 := uEreadMany s n (M++J++L) (Aout++W)
    have h8 := uEreadA s (blocks M n++M++J++L) W
    obtain ⟨t2,h2⟩ := h2
    obtain ⟨t5,h5⟩ := h5
    obtain ⟨t7,h7⟩ := h7
    have h := join0 (join0 (join0 (join0 (join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)) h4) (by simpa only [List.append_assoc] using h5)) (by simpa only [List.append_assoc] using h6)) (by simpa only [List.append_assoc] using h7)) (by simpa only [List.append_assoc] using h8)
    exact ⟨55+t2+24+97+t5+189+t7+55,by simpa only [transformed,blocks,List.append_assoc,← List.append_assoc (blocks M n) M _,blocks_snoc M n] using h⟩

theorem uMpopMany (s : Bool) (n : Nat) (L R : List Bool) :
    Reach s ⟨0,blocks M n++L,zeros 2++R⟩ ⟨0,L,zeros 2++blocks Mout n++R⟩ := by
  induction n generalizing R with
  | zero => exact reach_refl s _
  | succ n ih =>
    have h1 := uMpop s (blocks M n++L) R
    obtain ⟨t,h2⟩ := ih (Mout++R)
    have H := join0 h1 (by simpa only [List.append_assoc] using h2)
    exact ⟨39+t,by simpa only [blocks,List.append_assoc,← List.append_assoc (blocks Mout n) Mout R,blocks_snoc Mout n] using H⟩

theorem mRotate (n : Nat) : blocks Mout n++ones 2 = ones 2++blocks (code 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : Mout++ones 2 = ones 2++code 0 := rfl
    rw [blocks,blocks,List.append_assoc,ih,← List.append_assoc,he,List.append_assoc]

theorem uUnwind (s : Bool) (n : Nat) (L R : List Bool) :
    Reach s ⟨0,blocks M n++J++L,zeros 2++ones 2++R⟩ ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) n++R⟩ := by
  obtain ⟨t,h1⟩ := uMpopMany s n (J++L) (ones 2++R)
  have h2 := uJpop s L (blocks Mout n++ones 2++R)
  have h := join0 (by simpa only [List.append_assoc] using h1) (by simpa only [List.append_assoc] using h2)
  refine ⟨t+65,?_⟩
  simpa only [List.append_assoc,← List.append_assoc (blocks Mout n) (ones 2) R,mRotate n,← List.append_assoc (ones 6) (ones 2) _,← ones_add] using h

theorem uOrdinary0 (s : Bool) (r : Nat) (L R : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones 2++b++R)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) r++a++d++e++R⟩ := by
  obtain ⟨t,h1⟩ := uDprep s r L (ones 2++b++R)
  have h2 := uEread2 s (blocks M r++J++L) (b++R)
  have h3 := uEcarry0 s (blocks M r++J++L) R
  obtain ⟨t2,h4⟩ := uUnwind s r L (a++d++e++R)
  exact ⟨t+2+88+t2,by simpa only [List.append_assoc] using join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) h3) (by simpa only [List.append_assoc] using h4)⟩

theorem uOrdinaryS (s : Bool) (r : Nat) (L R : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones 2++a++zeros 10++R)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) r++a++c++f++zeros 4++R⟩ := by
  obtain ⟨t,h1⟩ := uDprep s r L (ones 2++a++zeros 10++R)
  have h2 := uEread2 s (blocks M r++J++L) (a++zeros 10++R)
  have h3 := uEcarryS s (blocks M r++J++L) R
  obtain ⟨t2,h4⟩ := uUnwind s r L (a++c++f++zeros 4++R)
  exact ⟨t+2+118+t2,by simpa only [List.append_assoc] using join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) h3) (by simpa only [List.append_assoc] using h4)⟩

theorem eEntry (s : Bool) (L W : List Bool) :
    run0 (table s) 1 (scan (rename s 4) L (bits "11"++W)) = some (scan 2 (false::L) (true::W)) := by cases s <;> rfl

theorem eToC (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (ones (2*m+2)++W)) (scan 2 (blocks Alt m++false::L) (true::W)) := by
  have h1 := eEntry s L (ones (2*m)++W)
  have h2 := cPairs s m (false::L) (true::W)
  have he : true::(ones (2*m)++W) = ones (2*m)++true::W := by
    have htrue : ∀ V : List Bool, true::V = ones 1++V := fun _ => rfl
    rw [htrue (ones (2*m)++W),htrue W,← List.append_assoc,← ones_add,Nat.add_comm 1 (2*m),ones_add,List.append_assoc]
  have H := join0 h1 (by simpa only [he] using h2)
  refine ⟨1+2*m,?_⟩
  rw [Nat.add_comm (2*m) 2,ones_add,show ones 2=bits "11" by rfl]
  simpa only [List.append_assoc] using H

theorem ePush (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (ones (2*m+2)++zeros 5++W)) (scan 3 (false::(bits "11101"++blocks Alt m++false::L)) W) := by
  obtain ⟨t,h1⟩ := eToC s m L (zeros 5++W)
  have h2 : run0 (table s) 6 (scan 2 (blocks Alt m++false::L) (true::(zeros 5++W))) = some (scan 3 (false::(bits "11101"++blocks Alt m++false::L)) W) := by cases s <;> cases W <;> rfl
  exact ⟨t+6,by simpa only [List.append_assoc] using join0 h1 h2⟩

theorem eTurn (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (ones (2*m+2)++zeros 10++W)) ⟨0,false::(blocks AltR m++bits "10"++L),zeros 3++ones 2++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := eToC s m L (zeros 10++W)
  have h2 : run0 (table s) 15 (scan 2 (blocks Alt m++false::L) (true::(zeros 10++W))) = some ⟨0,bits "01"++(blocks Alt m++false::L),zeros 3++ones 2++zeros 4++W⟩ := by cases s <;> rfl
  have H := join0 h1 h2
  exact ⟨t+15,by simpa only [List.append_assoc,show bits "01"=false::bits "1" by rfl,List.cons_append,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m,← List.append_assoc (bits "1") [false] L,show bits "1"++false::L=bits "10"++L by rfl] using H⟩

theorem ePop (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,bits "11101"++blocks Alt m++false::L,zeros 5++R⟩ ⟨0,bits "010"++L,zeros 3++ones (2*m)++zeros 5++R⟩ := by
  have h1 : run0 (table s) 3 ⟨0,bits "11101"++blocks Alt m++false::L,zeros 5++R⟩ = some ⟨0,false::(blocks AltR m++bits "10"++L),zeros 3++zeros 5++R⟩ := by
    have h0 : run0 (table s) 3 ⟨0,bits "11101"++blocks Alt m++false::L,zeros 5++R⟩ = some ⟨0,bits "01"++(blocks Alt m++false::L),zeros 3++zeros 5++R⟩ := by cases s <;> rfl
    simpa only [List.append_assoc,show bits "01"=false::bits "1" by rfl,List.cons_append,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m,← List.append_assoc (bits "1") [false] L,show bits "1"++false::L=bits "10"++L by rfl] using h0
  have h2 := aAlts s m (bits "10"++L) (zeros 5++R)
  have H := join0 h1 (by simpa only [List.append_assoc] using h2)
  exact ⟨3+12*m,by simpa only [List.append_assoc,show false::(bits "10"++L)=bits "010"++L by rfl] using H⟩

theorem ePop0 (s : Bool) (L R : List Bool) :
    run0 (table s) 74 ⟨0,bits "010"++I0++L,zeros 3++R⟩ = some ⟨0,L,zeros 2++ones 2++a++c++R⟩ := by cases s <;> rfl

theorem eGap5 (s : Bool) (L W : List Bool) :
    run0 (table s) 5 (scan (rename s 4) (I++L) (zeros 5++W)) = some (scan 3 (false::(bits "1110"++I++L)) W) := by cases s <;> cases W <;> rfl

theorem eGapPop (s : Bool) (L R : List Bool) :
    run0 (table s) 77 ⟨0,bits "1110"++I++L,zeros 5++R⟩ = some ⟨0,L,zeros 2++ones 2++a++c++zeros 5++R⟩ := by cases s <;> rfl

theorem uEterminal (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) (I0++L) (ones (2*m+2)++zeros 10++W)) ⟨0,L,zeros 2++ones 2++a++zeros 10++ones (2*m+8)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := eTurn s m (I0++L) W
  have h2 := aAlts s m (bits "10"++I0++L) (ones 2++zeros 4++W)
  have h3 := ePop0 s L (ones (2*m)++ones 2++zeros 4++W)
  have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc,show bits "010"++(I0++L)=false::(bits "10"++I0++L) by rfl] using h3)
  have he : c++ones (2*m)++ones 2 = zeros 10++ones (2*m+8) := by
    change (zeros 10++ones 6)++ones (2*m)++ones 2 = _
    rw [List.append_assoc,List.append_assoc,← ones_add,← ones_add,show 6+(2*m+2)=2*m+8 by omega]
  exact ⟨t+12*m+74,by simpa only [List.append_assoc,← List.append_assoc c (ones (2*m)) _,← List.append_assoc (c++ones (2*m)) (ones 2) _,he] using H⟩

theorem uEpartial (s : Bool) (m : Nat) (ms : List Nat) (n : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) (I0++L) (ones (2*m+2)++zeros 5++tRuns ms++ones (2*n+2)++zeros 10++W)) ⟨0,L,zeros 2++ones 2++a++zeros 10++ones (2*m+6)++zeros 5++tRuns ms++ones (2*n+4)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := ePush s m (I0++L) (tRuns ms++ones (2*n+2)++zeros 10++W)
  obtain ⟨u,h2⟩ := tSweep s ms n (bits "11101"++blocks Alt m++false::(I0++L)) W
  obtain ⟨v,h3⟩ := ePop s m (I0++L) (tRuns ms++ones (2*n+4)++zeros 4++W)
  have h4 := ePop0 s L (ones (2*m)++zeros 5++tRuns ms++ones (2*n+4)++zeros 4++W)
  have H := join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)) (by simpa only [List.append_assoc] using h4)
  have he : c++ones (2*m) = zeros 10++ones (2*m+6) := by
    change (zeros 10++ones 6)++ones (2*m) = _
    rw [List.append_assoc,← ones_add, Nat.add_comm 6]
  exact ⟨t+u+v+74,by simpa only [List.append_assoc,← List.append_assoc c (ones (2*m)) _,he] using H⟩

theorem uEGrowth (s : Bool) (ms : List Nat) (n : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) (I++L) (zeros 5++tRuns ms++ones (2*n+2)++zeros 10++W)) ⟨0,L,zeros 2++ones 2++a++c++zeros 5++tRuns ms++ones (2*n+4)++zeros 4++W⟩ := by
  have h1 := eGap5 s L (tRuns ms++ones (2*n+2)++zeros 10++W)
  obtain ⟨t,h2⟩ := tSweep s ms n (bits "1110"++I++L) W
  have h3 := eGapPop s L (tRuns ms++ones (2*n+4)++zeros 4++W)
  exact ⟨5+t+77,by simpa only [List.append_assoc] using join0 (join0 h1 h2) (by simpa only [List.append_assoc] using h3)⟩

def Bhead := bits "1101011110"
def Btail := bits "1111110101010111100111110111"
def Bcarry := bits "11111011110"
def Bmark := bits "1100011"
def Ebase := bits "111111111110"

theorem bEntry (s : Bool) (L W : List Bool) :
    run0 (table s) 13 (scan 1 (Bhead++L) (bits "11"++W)) = some (scan 2 (Bcarry++L) (true::W)) := by cases s <;> rfl

theorem bToC (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan 1 (Bhead++L) (ones (2*m+2)++W)) (scan 2 (blocks Alt m++Bcarry++L) (true::W)) := by
  have h1 := bEntry s L (ones (2*m)++W)
  have h2 := cPairs s m (Bcarry++L) (true::W)
  have he : true::(ones (2*m)++W) = ones (2*m)++true::W := by
    have htrue : ∀ V : List Bool, true::V = ones 1++V := fun _ => rfl
    rw [htrue (ones (2*m)++W),htrue W,← List.append_assoc,← ones_add,Nat.add_comm 1 (2*m),ones_add,List.append_assoc]
  have H := join0 h1 (by simpa only [he] using h2)
  refine ⟨13+2*m,?_⟩
  rw [Nat.add_comm (2*m) 2,ones_add,show ones 2=bits "11" by rfl]
  simpa only [List.append_assoc] using H

theorem bPop0 (s : Bool) (L R : List Bool) :
    run0 (table s) 43 ⟨0,bits "01"++Bcarry++L,zeros 3++R⟩ = some ⟨0,L,zeros 2++Bmark++zeros 5++ones 2++R⟩ := by cases s <;> rfl

theorem bPop (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,bits "01"++blocks Alt m++Bcarry++L,zeros 3++R⟩ ⟨0,L,zeros 2++Bmark++zeros 5++ones (2*m+2)++R⟩ := by
  have h1 := aAlts s m (bits "1"++Bcarry++L) R
  have h2 := bPop0 s L (ones (2*m)++R)
  have h1' : run0 (table s) (12*m) ⟨0,bits "01"++blocks Alt m++Bcarry++L,zeros 3++R⟩ = some ⟨0,bits "01"++Bcarry++L,zeros 3++ones (2*m)++R⟩ := by
    simpa only [List.append_assoc,show bits "01"=false::bits "1" by rfl,List.cons_append,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m] using h1
  have H := join0 h1' (by simpa only [List.append_assoc] using h2)
  exact ⟨12*m+43,by simpa only [List.append_assoc,← List.append_assoc (ones 2) (ones (2*m)) _,← ones_add,Nat.add_comm 2 (2*m)] using H⟩

theorem bSweep1 (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan 1 (Bhead++L) (ones (2*m+2)++zeros 10++W)) ⟨0,L,zeros 2++Bmark++zeros 5++ones (2*m+4)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := bToC s m L (zeros 10++W)
  have h2 : run0 (table s) 15 (scan 2 (blocks Alt m++Bcarry++L) (true::(zeros 10++W))) = some ⟨0,bits "01"++blocks Alt m++Bcarry++L,zeros 3++ones 2++zeros 4++W⟩ := by cases s <;> rfl
  obtain ⟨u,h3⟩ := bPop s m L (ones 2++zeros 4++W)
  have H := join0 (join0 h1 h2) (by simpa only [List.append_assoc] using h3)
  exact ⟨t+15+u,by simpa only [List.append_assoc,← List.append_assoc (ones (2*m+2)) (ones 2) _,← ones_add,show 2*m+2+2=2*m+4 by omega] using H⟩

theorem bSweepMore (s : Bool) (m : Nat) (ms : List Nat) (n : Nat) (L W : List Bool) :
    Reach s (scan 1 (Bhead++L) (ones (2*m+2)++zeros 5++tRuns ms++ones (2*n+2)++zeros 10++W)) ⟨0,L,zeros 2++Bmark++zeros 5++ones (2*m+2)++zeros 5++tRuns ms++ones (2*n+4)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := bToC s m L (zeros 5++tRuns ms++ones (2*n+2)++zeros 10++W)
  let R := tRuns ms++ones (2*n+2)++zeros 10++W
  let R' := tRuns ms++ones (2*n+4)++zeros 4++W
  have h2 : run0 (table s) 6 (scan 2 (blocks Alt m++Bcarry++L) (true::(zeros 5++R))) = some (scan 3 (false::(bits "11101"++blocks Alt m++Bcarry++L)) R) := by cases s <;> cases R <;> rfl
  obtain ⟨u,h3⟩ := tSweep s ms n (bits "11101"++blocks Alt m++Bcarry++L) W
  have h4 : run0 (table s) 3 ⟨0,bits "11101"++blocks Alt m++Bcarry++L,zeros 5++R'⟩ = some ⟨0,bits "01"++blocks Alt m++Bcarry++L,zeros 3++zeros 5++R'⟩ := by cases s <;> rfl
  obtain ⟨v,h5⟩ := bPop s m L (zeros 5++R')
  have H := join0 (join0 (join0 (join0 h1 (by simpa only [R,List.append_assoc] using h2)) (by simpa only [R,List.append_assoc] using h3)) (by simpa only [R',List.append_assoc] using h4)) (by simpa only [R',List.append_assoc] using h5)
  exact ⟨t+6+u+3+v,by simpa only [R,R',List.append_assoc] using H⟩

theorem uBinit (s : Bool) (L W : List Bool) :
    run0 (table s) 35 (scan 0 (Ubase++L) (ones 8++zeros 5++W)) = some (scan 1 (Bhead++Btail++L) W) := by cases s <;> cases W <;> rfl

theorem bTailToE (s : Bool) (L W : List Bool) :
    run0 (table s) 132 ⟨0,Btail++L,zeros 2++Bmark++W⟩ = some (scan (rename s 4) (Ebase++J++L) W) := by cases s <;> cases W <;> rfl

theorem eBaseGap (s : Bool) (L W : List Bool) :
    run0 (table s) 5 (scan (rename s 4) L (zeros 5++W)) = some (scan 3 (false::(bits "1110"++L)) W) := by cases s <;> cases W <;> rfl

theorem eBasePop (s : Bool) (L R : List Bool) :
    run0 (table s) 36 ⟨0,bits "1110"++Ebase++L,zeros 5++R⟩ = some ⟨0,L,zeros 2++ones 2++b++zeros 5++R⟩ := by cases s <;> rfl

def Ctail := bits "11110"
def Mark := bits "11000"
def Eunit := bits "1111110"
def Eframe (m : Nat) := match m with
  | 0 => Ebase
  | n+1 => Eunit++blocks AltR n++Eunit

def highOut (m : Nat) := match m with
  | 0 => zeros 10
  | n+1 => zeros 5++ones (2*n+2)++zeros 5

theorem cLong (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan 2 (Chead++L) (ones (2*m+6)++zeros 5++W)) (scan 1 (Bhead++blocks AltR m++Ctail++L) W) := by
  have h1 := cPairs s m (Chead++L) (ones 6++zeros 5++W)
  have h2 : run0 (table s) 23 (scan 2 (blocks Alt m++Chead++L) (ones 6++zeros 5++W)) = some (scan 1 (Bhead++bits "1"++blocks Alt m++Chead++L) W) := by cases s <;> cases W <;> rfl
  have H := join0 (by simpa only [List.append_assoc] using h1) h2
  refine ⟨2*m+23,?_⟩
  simpa only [ones_add,List.append_assoc,← List.append_assoc (bits "1") (blocks Alt m) _,altRotate m,← List.append_assoc (bits "1") Chead _,show bits "1"++Chead=Ctail by rfl] using H

theorem bZero (s : Bool) (L W : List Bool) :
    run0 (table s) 49 (scan 1 (Bhead++L) (zeros 5++W)) = some ⟨0,L,zeros 2++Mark++ones 6++zeros 2++W⟩ := by cases s <;> rfl

theorem aLongAlt (s : Bool) (L R : List Bool) :
    run0 (table s) 12 ⟨0,AltR++L,zeros 2++R⟩ = some ⟨0,L,zeros 2++ones 2++R⟩ := by cases s <;> rfl

theorem aLongAlts (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,blocks AltR m++L,zeros 2++R⟩ ⟨0,L,zeros 2++ones (2*m)++R⟩ := by
  induction m generalizing R with
  | zero => exact reach_refl s _
  | succ m ih =>
    have h1 := aLongAlt s (blocks AltR m++L) R
    obtain ⟨t,h2⟩ := ih (ones 2++R)
    have H := join0 h1 (by simpa only [List.append_assoc] using h2)
    exact ⟨12+t,by simpa only [blocks,List.append_assoc,Nat.mul_succ,ones_add] using H⟩

theorem cLongPop0 (s : Bool) (L R : List Bool) :
    run0 (table s) 15 ⟨0,Ctail++L,zeros 2++R⟩ = some ⟨0,L,zeros 2++Mark++R⟩ := by cases s <;> rfl

theorem cLongPop (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,blocks AltR m++Ctail++L,zeros 2++Mark++R⟩ ⟨0,L,zeros 2++Mark++ones (2*m+2)++zeros 3++R⟩ := by
  obtain ⟨t,h1⟩ := aLongAlts s m (Ctail++L) (Mark++R)
  have h2 := cLongPop0 s L (ones (2*m)++Mark++R)
  have H := join0 (by simpa only [List.append_assoc] using h1) (by simpa only [List.append_assoc] using h2)
  exact ⟨t+15,by simpa only [List.append_assoc,show Mark=ones 2++zeros 3 by rfl,← List.append_assoc (ones (2*m)) (ones 2) _,← ones_add] using H⟩

theorem eLongEntry (s : Bool) (L W : List Bool) :
    run0 (table s) 19 (scan (rename s 4) L (Mark++ones 2++W)) = some (scan (rename s 4) (Eunit++L) W) := by cases s <;> cases W <;> rfl

theorem ePair (s : Bool) (L W : List Bool) :
    run0 (table s) 2 (scan (rename s 4) L (ones 2++W)) = some (scan (rename s 4) (AltR++L) W) := by cases s <;> cases W <;> rfl

theorem ePairs (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (ones (2*m)++W)) (scan (rename s 4) (blocks AltR m++L) W) := by
  induction m generalizing L with
  | zero => exact reach_refl s _
  | succ m ih =>
    have h1 := ePair s L (ones (2*m)++W)
    obtain ⟨t,h2⟩ := ih (AltR++L)
    have H := join0 h1 h2
    exact ⟨2+t,by simpa only [Nat.mul_succ,Nat.add_comm (2*m) 2,ones_add,blocks,List.append_assoc,← List.append_assoc (blocks AltR m) AltR L,blocks_snoc AltR m] using H⟩

theorem eLongMark (s : Bool) (m : Nat) (L W : List Bool) :
    run0 (table s) 17 (scan (rename s 4) (blocks AltR m++Eunit++L) (bits "00011"++W)) = some (scan (rename s 4) (Eframe m++L) W) := by
  cases m with
  | zero => cases s <;> cases W <;> rfl
  | succ n => cases s <;> cases W <;> rfl

theorem eLong (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) L (Mark++ones (2*m+2)++bits "00011"++W)) (scan (rename s 4) (Eframe m++L) W) := by
  have h1 := eLongEntry s L (ones (2*m)++bits "00011"++W)
  obtain ⟨t,h2⟩ := ePairs s m (Eunit++L) (bits "00011"++W)
  have h3 := eLongMark s m L W
  have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  exact ⟨19+t+17,by simpa only [Nat.add_comm (2*m) 2,ones_add,List.append_assoc] using H⟩

theorem frameLast (s : Bool) (L R : List Bool) :
    run0 (table s) 28 ⟨0,false::(Eunit++L),zeros 3++R⟩ = some ⟨0,L,zeros 2++ones 2++zeros 5++ones 2++R⟩ := by cases s <;> rfl

theorem frameGapPop (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,bits "1110"++Eframe m++L,zeros 5++R⟩ ⟨0,L,zeros 2++ones 2++highOut m++ones 2++zeros 5++R⟩ := by
  cases m with
  | zero => exact ⟨36,by simpa only [Eframe,highOut,show b=zeros 10++ones 2 by rfl,List.append_assoc] using eBasePop s L R⟩
  | succ m =>
    have h1 : run0 (table s) 20 ⟨0,bits "1110"++Eframe (m+1)++L,zeros 5++R⟩ = some ⟨0,false::(blocks AltR m++Eunit++L),zeros 3++zeros 5++ones 2++zeros 5++R⟩ := by cases s <;> rfl
    have h2 := aAlts s m (Eunit++L) (zeros 5++ones 2++zeros 5++R)
    have h3 := frameLast s L (ones (2*m)++zeros 5++ones 2++zeros 5++R)
    have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
    exact ⟨20+12*m+28,by simpa only [highOut,List.append_assoc,← List.append_assoc (ones 2) (ones (2*m)) _,← ones_add,Nat.add_comm 2 (2*m)] using H⟩

theorem frameTurnPop (s : Bool) (m : Nat) (L R : List Bool) :
    Reach s ⟨0,bits "010"++Eframe m++L,zeros 3++R⟩ ⟨0,L,zeros 2++ones 2++highOut m++ones 4++R⟩ := by
  cases m with
  | zero => exact ⟨45,by cases s <;> rfl⟩
  | succ m =>
    have h1 : run0 (table s) 29 ⟨0,bits "010"++Eframe (m+1)++L,zeros 3++R⟩ = some ⟨0,false::(blocks AltR m++Eunit++L),zeros 3++zeros 5++ones 4++R⟩ := by cases s <;> rfl
    have h2 := aAlts s m (Eunit++L) (zeros 5++ones 4++R)
    have h3 := frameLast s L (ones (2*m)++zeros 5++ones 4++R)
    have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
    exact ⟨29+12*m+28,by simpa only [highOut,List.append_assoc,← List.append_assoc (ones 2) (ones (2*m)) _,← ones_add,Nat.add_comm 2 (2*m)] using H⟩

theorem frameSweep (s : Bool) (m : Nat) (ms : List Nat) (n : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) (Eframe m++L) (zeros 5++tRuns ms++ones (2*n+2)++zeros 10++W)) ⟨0,L,zeros 2++ones 2++highOut m++ones 2++zeros 5++tRuns ms++ones (2*n+4)++zeros 4++W⟩ := by
  have h1 := eBaseGap s (Eframe m++L) (tRuns ms++ones (2*n+2)++zeros 10++W)
  obtain ⟨t,h2⟩ := tSweep s ms n (bits "1110"++Eframe m++L) W
  obtain ⟨u,h3⟩ := frameGapPop s m L (tRuns ms++ones (2*n+4)++zeros 4++W)
  exact ⟨5+t+u,by simpa only [List.append_assoc] using join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)⟩

theorem frameTerminal (s : Bool) (m : Nat) (L W : List Bool) :
    Reach s (scan (rename s 4) (Eframe m++L) (ones 4++zeros 10++W)) ⟨0,L,zeros 2++ones 2++highOut m++ones 8++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := eTurn s 1 (Eframe m++L) W
  have h2 := aAlts s 1 (bits "10"++Eframe m++L) (ones 2++zeros 4++W)
  obtain ⟨u,h3⟩ := frameTurnPop s m L (ones 4++zeros 4++W)
  have h := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc,show bits "010"++(Eframe m++L)=false::(bits "10"++Eframe m++L) by rfl,show ones 2++ones 2=ones 4 by rfl,← List.append_assoc (ones 2) (ones 2) _] using h3)
  exact ⟨t+12+u,by simpa only [List.append_assoc,← List.append_assoc (ones 4) (ones 4) _,← ones_add] using h⟩

def V := ones 8++zeros 5++ones 4++zeros 4

theorem uKtoE (s : Bool) (k : Nat) (L W : List Bool) :
    Reach s ⟨0,blocks K k++K0++L,zeros 2++W⟩ (scan (rename s 4) (blocks M (k+1)++J++L) W) := by
  obtain ⟨t,h1⟩ := uKpopMany s k (K0++L) W
  have h2 := uKbase s L (blocks Kout k++W)
  obtain ⟨u,h3⟩ := uEreadMany s k (M++J++L) W
  have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [List.append_assoc] using h3)
  exact ⟨t+189+u,by simpa only [blocks,List.append_assoc,← List.append_assoc (blocks M k) M _,blocks_snoc M k] using H⟩

theorem uLongPrep (s : Bool) (k : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (V++blocks cycleIn k++W)) (scan 2 (Chead++blocks K k++K0++L) W) := by
  have h1 := uPrep1 s L (blocks cycleIn k++W)
  obtain ⟨t,h2⟩ := uCpushMany s k (K0++L) W
  exact ⟨55+t,by simpa only [V,List.append_assoc] using join0 h1 h2⟩

def tail5 (ms : List Nat) (n : Nat) := zeros 5++tRuns ms++ones (2*n+2)

theorem uLongHead (s : Bool) (k m : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (V++blocks cycleIn k++ones (2*m+6)++zeros 5++W)) (scan 1 (Bhead++blocks AltR m++Ctail++blocks K k++K0++L) W) := by
  obtain ⟨t,h1⟩ := uLongPrep s k L (ones (2*m+6)++zeros 5++W)
  obtain ⟨u,h2⟩ := cLong s m (blocks K k++K0++L) W
  exact ⟨t+u,by simpa only [List.append_assoc] using join0 h1 (by simpa only [List.append_assoc] using h2)⟩

theorem uLongMid (s : Bool) (k m : Nat) (L W : List Bool) :
    Reach s ⟨0,blocks AltR m++Ctail++blocks K k++K0++L,zeros 2++Mark++ones 2++W⟩ (scan (rename s 4) (Eframe m++blocks M (k+1)++J++L) W) := by
  obtain ⟨t,h1⟩ := cLongPop s m (blocks K k++K0++L) (ones 2++W)
  obtain ⟨u,h2⟩ := uKtoE s k L (Mark++ones (2*m+2)++bits "00011"++W)
  have he : zeros 3++ones 2=bits "00011" := rfl
  obtain ⟨v,h3⟩ := eLong s m (blocks M (k+1)++J++L) W
  have H := join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 3) (ones 2) W,he] using h2)) (by simpa only [List.append_assoc] using h3)
  exact ⟨t+u+v,by simpa only [List.append_assoc] using H⟩

theorem uLongTerminal (s : Bool) (k m : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (V++blocks cycleIn k++ones (2*m+6)++zeros 18++W)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) (k+1)++highOut m++ones 8++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uLongHead s k m L (zeros 13++W)
  have h2 := bZero s (blocks AltR m++Ctail++blocks K k++K0++L) (zeros 8++W)
  obtain ⟨u,h3⟩ := uLongMid s k m L (ones 4++zeros 10++W)
  obtain ⟨v,h4⟩ := frameTerminal s m (blocks M (k+1)++J++L) W
  obtain ⟨x,h5⟩ := uUnwind s (k+1) L (highOut m++ones 8++zeros 4++W)
  have H := join0 (join0 (join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 5) (zeros 8) W,show zeros 5++zeros 8=zeros 13 by rfl] using h2)) (by simpa only [List.append_assoc,show ones 2++ones 4=ones 6 by rfl,show zeros 2++zeros 8=zeros 10 by rfl,← List.append_assoc (ones 2) (ones 4) _,← List.append_assoc (zeros 2) (zeros 8) _] using h3)) (by simpa only [List.append_assoc] using h4)) (by simpa only [List.append_assoc] using h5)
  exact ⟨t+49+u+v+x,by simpa only [List.append_assoc,← List.append_assoc (zeros 5) (zeros 13) _,show zeros 5++zeros 13=zeros 18 by rfl] using H⟩

theorem uLongMore1 (s : Bool) (k m n : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (V++blocks cycleIn k++ones (2*m+6)++tail5 [] n++zeros 16++W)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) (k+1)++highOut m++ones 2++tail5 [] (n+2)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uLongHead s k m L (ones (2*n+2)++zeros 16++W)
  obtain ⟨u,h2⟩ := bSweep1 s n (blocks AltR m++Ctail++blocks K k++K0++L) (zeros 6++W)
  obtain ⟨v,h3⟩ := uLongMid s k m L (zeros 5++ones (2*n+4)++zeros 10++W)
  obtain ⟨x,h4⟩ := frameSweep s m [] (n+1) (blocks M (k+1)++J++L) W
  obtain ⟨y,h5⟩ := uUnwind s (k+1) L (highOut m++ones 2++tail5 [] (n+2)++zeros 4++W)
  have H := join0 (join0 (join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 10) (zeros 6) _,show zeros 10++zeros 6=zeros 16 by rfl] using h2)) (by simpa only [List.append_assoc,show Bmark=Mark++ones 2 by rfl,← List.append_assoc (zeros 4) (zeros 6) _,show zeros 4++zeros 6=zeros 10 by rfl] using h3)) (by simpa only [tRuns,List.nil_append,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega] using h4)) (by simpa only [tail5,tRuns,List.nil_append,List.append_assoc,show 2*(n+2)+2=2*(n+1)+4 by omega] using h5)
  exact ⟨t+u+v+x+y,by simpa only [tail5,tRuns,List.nil_append,List.append_assoc,show 2*(n+2)+2=2*(n+1)+4 by omega] using H⟩

theorem uLongMore (s : Bool) (k m n p : Nat) (ms : List Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (V++blocks cycleIn k++ones (2*m+6)++tail5 (p::ms) n++zeros 16++W)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++blocks (code 0) (k+1)++highOut m++ones 2++tail5 (p::ms) (n+2)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uLongHead s k m L (ones (2*p+2)++zeros 5++tRuns ms++ones (2*n+2)++zeros 16++W)
  obtain ⟨u,h2⟩ := bSweepMore s p ms n (blocks AltR m++Ctail++blocks K k++K0++L) (zeros 6++W)
  obtain ⟨v,h3⟩ := uLongMid s k m L (tail5 (p::ms) (n+1)++zeros 10++W)
  obtain ⟨x,h4⟩ := frameSweep s m (p::ms) (n+1) (blocks M (k+1)++J++L) W
  obtain ⟨y,h5⟩ := uUnwind s (k+1) L (highOut m++ones 2++tail5 (p::ms) (n+2)++zeros 4++W)
  have H := join0 (join0 (join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 10) (zeros 6) _,show zeros 10++zeros 6=zeros 16 by rfl] using h2)) (by simpa only [tail5,tRuns,List.append_assoc,show Bmark=Mark++ones 2 by rfl,← List.append_assoc (zeros 4) (zeros 6) _,show zeros 4++zeros 6=zeros 10 by rfl,show 2*(n+1)+2=2*n+4 by omega] using h3)) (by simpa only [tail5,tRuns,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega] using h4)) (by simpa only [tail5,tRuns,List.append_assoc,show 2*(n+2)+2=2*(n+1)+4 by omega] using h5)
  exact ⟨t+u+v+x+y,by simpa only [tail5,tRuns,List.append_assoc,show 2*(n+2)+2=2*(n+1)+4 by omega] using H⟩

theorem uH0End (s : Bool) (ms : List Nat) (n : Nat) (L W : List Bool) :
    Reach s ⟨0,Btail++L,zeros 2++Bmark++tail5 ms n++zeros 10++W⟩ ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++b++tail5 ms (n+1)++zeros 4++W⟩ := by
  have h1 := bTailToE s L (tail5 ms n++zeros 10++W)
  obtain ⟨t,h2⟩ := frameSweep s 0 ms n (J++L) W
  obtain ⟨u,h3⟩ := uUnwind s 0 L (b++tail5 ms (n+1)++zeros 4++W)
  have H := join0 (join0 h1 (by simpa only [tail5,Eframe,List.append_assoc] using h2)) (by simpa only [blocks,List.nil_append,tail5,highOut,show b=zeros 10++ones 2 by rfl,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega] using h3)
  exact ⟨132+t+u,by simpa only [blocks,List.nil_append,tail5,show b=zeros 10++ones 2 by rfl,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using H⟩

theorem uH0One (s : Bool) (n : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (ones 8++tail5 [] n++zeros 16++W)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++b++tail5 [] (n+2)++zeros 4++W⟩ := by
  have h1 := uBinit s L (ones (2*n+2)++zeros 16++W)
  obtain ⟨t,h2⟩ := bSweep1 s n (Btail++L) (zeros 6++W)
  obtain ⟨u,h3⟩ := uH0End s [] (n+1) L W
  have H := join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 10) (zeros 6) W,show zeros 10++zeros 6=zeros 16 by rfl] using h2)) (by simpa only [tail5,tRuns,List.nil_append,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega,← List.append_assoc (zeros 4) (zeros 6) W,show zeros 4++zeros 6=zeros 10 by rfl] using h3)
  exact ⟨35+t+u,by simpa only [tail5,tRuns,List.nil_append,List.append_assoc] using H⟩

theorem uH0More (s : Bool) (p n : Nat) (ms : List Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (ones 8++tail5 (p::ms) n++zeros 16++W)) ⟨0,L,zeros 5++ones 2++zeros 14++ones 8++b++tail5 (p::ms) (n+2)++zeros 4++W⟩ := by
  have h1 := uBinit s L (ones (2*p+2)++zeros 5++tRuns ms++ones (2*n+2)++zeros 16++W)
  obtain ⟨t,h2⟩ := bSweepMore s p ms n (Btail++L) (zeros 6++W)
  obtain ⟨u,h3⟩ := uH0End s (p::ms) (n+1) L W
  have H := join0 (join0 h1 (by simpa only [List.append_assoc,← List.append_assoc (zeros 10) (zeros 6) W,show zeros 10++zeros 6=zeros 16 by rfl] using h2)) (by simpa only [tail5,tRuns,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega,← List.append_assoc (zeros 4) (zeros 6) W,show zeros 4++zeros 6=zeros 10 by rfl] using h3)
  exact ⟨35+t+u,by simpa only [tail5,tRuns,List.append_assoc] using H⟩

-- Wrap a local U return in the two outer sweeps.
theorem phase4of (s : Bool) (k : Nat) (W W' : List Bool)
    (h : ∀ L, Reach s (scan 0 (Ubase++L) W) ⟨0,L,zeros 5++ones 2++zeros 14++W'⟩) :
    Reach s (front k (low4++W)) (front (k+1) (low0++W')) := by
  let L := blocks P k++Bbase
  have h1 := prepare s k (low4++W)
  have h2 := uStart s L W
  obtain ⟨t,h3⟩ := h L
  have h4 := finish s k (ones 2++zeros 14++W')
  have H := join0 (join0 (join0 h1 (by simpa only [L,List.append_assoc] using h2)) h3) (by simpa only [L,List.append_assoc] using h4)
  have he : bits "1100"++ones 2++zeros 14=Q++low0 := rfl
  exact ⟨95+30*k+36+t+(30*k+31),by simpa only [front,blocks,List.append_assoc,← List.append_assoc (bits "1100") (ones 2) _,← List.append_assoc (bits "1100"++ones 2) (zeros 14) _,he,← List.append_assoc (blocks Q k) Q _,blocks_snoc Q k] using H⟩

def Dcode (r : Nat) := match r with
  | 0 => b
  | 1 => a++d++e
  | n+2 => a++c++blocks (f++g) n++f++h++e

def longCode (k m : Nat) := match k with
  | 0 => a++zeros 10++ones (2*m+6)
  | j+1 => a++c++blocks (f++g) j++f++zeros 4++ones (2*m+6)

theorem codeD (r : Nat) : code r = Dcode r++a := by
  cases r with
  | zero => rfl
  | succ r => cases r <;> simp only [code,Dcode,List.append_assoc]

theorem cycleRotate (r : Nat) : ones 6++blocks (f++g) r = blocks cycleIn r++ones 6 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have he : ones 6++(f++g)=cycleIn++ones 6 := rfl
    rw [blocks,blocks,← List.append_assoc,he,List.append_assoc,ih,List.append_assoc]

theorem tD (s : Bool) (k r : Nat) (W : List Bool) :
    Reach s (front k (low3++ones 8++Dcode r++zeros 5++W)) (front k (low4++transformed r++W)) := by
  cases r with
  | zero =>
    have H := phase3 s k [] 3 (ones 2++zeros 5++W)
    simpa only [Dcode,transformed,tRuns,List.nil_append,show b=zeros 10++ones 2 by rfl,List.append_assoc] using H
  | succ r =>
    cases r with
    | zero =>
      have H := phase3 s k [3] 0 (ones 8++zeros 4++ones 2++zeros 5++W)
      simpa only [Dcode,transformed,tRuns,List.nil_append,blocks,show a=zeros 5++ones 2 by rfl,show d=zeros 10++ones 8 by rfl,show e=zeros 4++ones 2 by rfl,List.append_assoc] using H
    | succ r =>
      have H := phase3 s k [3] 0 (ones 6++zeros 5++ones 4++zeros 4++blocks cycleIn r++ones 8++zeros 4++ones 2++zeros 5++W)
      have hrot : ones 6++blocks (f++g) r++f++zeros 4 = blocks cycleIn (r+1) := by
        rw [cycleRotate,List.append_assoc,List.append_assoc,show ones 6++(f++zeros 4)=cycleIn by rfl,blocks,blocks_snoc]
      have he : ones 6++blocks (f++g) r++f++h = blocks cycleIn (r+1)++ones 8 := by
        rw [show h=zeros 4++ones 8 by rfl,← List.append_assoc,hrot]
      have H := phase3 s k [3] 0 (blocks cycleIn (r+1)++ones 8++zeros 4++ones 2++zeros 5++W)
      have hin : Dcode (r+2) = zeros 5++ones 2++zeros 10++blocks cycleIn (r+1)++ones 8++zeros 4++ones 2 := by
        simp only [Dcode,show a=zeros 5++ones 2 by rfl,show c=zeros 10++ones 6 by rfl,show e=zeros 4++ones 2 by rfl,List.append_assoc]
        rw [← List.append_assoc (ones 6) (blocks (f++g) r) _,← List.append_assoc (ones 6++blocks (f++g) r) f _,← List.append_assoc (ones 6++blocks (f++g) r++f) h _,he,List.append_assoc]
      simpa only [hin,transformed,tRuns,List.nil_append,List.append_assoc] using H

theorem longRot (j : Nat) : ones 6++blocks (f++g) j++f++zeros 4 = blocks cycleIn (j+1) := by
  rw [cycleRotate,List.append_assoc,List.append_assoc,show ones 6++(f++zeros 4)=cycleIn by rfl,blocks,blocks_snoc]

theorem tLong (s : Bool) (k j m : Nat) (W : List Bool) :
    Reach s (front k (low3++ones 8++longCode j m++W)) (front k (low4++V++blocks cycleIn j++ones (2*m+6)++W)) := by
  cases j with
  | zero =>
    have H := phase3 s k [3] 0 (ones (2*m+6)++W)
    simpa only [longCode,V,tRuns,List.nil_append,blocks,show a=zeros 5++ones 2 by rfl,List.append_assoc] using H
  | succ j =>
    have H := phase3 s k [3] 0 (blocks cycleIn (j+1)++ones (2*m+6)++W)
    have he : longCode (j+1) m = zeros 5++ones 2++zeros 10++blocks cycleIn (j+1)++ones (2*m+6) := by
      simp only [longCode,show a=zeros 5++ones 2 by rfl,show c=zeros 10++ones 6 by rfl,List.append_assoc]
      rw [← List.append_assoc (ones 6) (blocks (f++g) j) _,← List.append_assoc (ones 6++blocks (f++g) j) f _,← List.append_assoc (ones 6++blocks (f++g) j++f) (zeros 4) _,longRot]
    simpa only [he,V,tRuns,List.nil_append,List.append_assoc] using H

def pre := zeros 5++ones 2++zeros 14++ones 8

theorem uIncD (s : Bool) (r j : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones 2++Dcode j++W)) ⟨0,L,pre++blocks (code 0) r++Dcode (j+1)++W⟩ := by
  cases j with
  | zero => simpa only [Dcode,pre,List.append_assoc] using uOrdinary0 s r L W
  | succ j =>
    cases j with
    | zero =>
      simpa only [Dcode,pre,blocks,List.nil_append,show d=zeros 10++ones 8 by rfl,show h=zeros 4++ones 8 by rfl,List.append_assoc] using uOrdinaryS s r L (ones 8++e++W)
    | succ j =>
      have H := uOrdinaryS s r L (ones 6++blocks (f++g) j++f++h++e++W)
      simpa only [Dcode,pre,show c=zeros 10++ones 6 by rfl,show g=zeros 4++ones 6 by rfl,blocks,List.append_assoc] using H

theorem uIncLong (s : Bool) (r j m : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones 2++longCode j m++W)) ⟨0,L,pre++blocks (code 0) r++longCode (j+1) m++W⟩ := by
  cases j with
  | zero => simpa only [longCode,blocks,List.nil_append,pre,List.append_assoc] using uOrdinaryS s r L (ones (2*m+6)++W)
  | succ j =>
    have H := uOrdinaryS s r L (ones 6++blocks (f++g) j++f++zeros 4++ones (2*m+6)++W)
    simpa only [longCode,pre,show c=zeros 10++ones 6 by rfl,show g=zeros 4++ones 6 by rfl,blocks,List.append_assoc] using H

theorem uPart1 (s : Bool) (r n : Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones (2*n+2)++zeros 10++W)) ⟨0,L,pre++blocks (code 0) r++longCode 0 (n+1)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uDprep s r L (ones (2*n+2)++zeros 10++W)
  obtain ⟨u,h2⟩ := uEterminal s n (blocks M r++J++L) W
  obtain ⟨v,h3⟩ := uUnwind s r L (longCode 0 (n+1)++zeros 4++W)
  have H := join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [longCode,show 2*(n+1)+6=2*n+8 by omega,List.append_assoc] using h3)
  exact ⟨t+u+v,by simpa only [pre,longCode,tail5,show 2*(n+1)+6=2*n+8 by omega,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using H⟩

theorem uPartMore (s : Bool) (r p n : Nat) (ms : List Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones (2*p+2)++tail5 ms n++zeros 10++W)) ⟨0,L,pre++blocks (code 0) r++longCode 0 p++tail5 ms (n+1)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uDprep s r L (ones (2*p+2)++tail5 ms n++zeros 10++W)
  obtain ⟨u,h2⟩ := uEpartial s p ms n (blocks M r++J++L) W
  obtain ⟨v,h3⟩ := uUnwind s r L (longCode 0 p++tail5 ms (n+1)++zeros 4++W)
  have H := join0 (join0 h1 (by simpa only [tail5,List.append_assoc] using h2)) (by simpa only [longCode,tail5,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using h3)
  exact ⟨t+u+v,by simpa only [pre,longCode,tail5,show 2*(n+1)+6=2*n+8 by omega,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using H⟩

theorem uCarryTail (s : Bool) (r n : Nat) (ms : List Nat) (L W : List Bool) :
    Reach s (scan 0 (Ubase++L) (transformed r++ones 2++tail5 ms n++zeros 10++W)) ⟨0,L,pre++blocks (code 0) r++longCode 0 0++tail5 ms (n+1)++zeros 4++W⟩ := by
  obtain ⟨t,h1⟩ := uDprep s r L (ones 2++tail5 ms n++zeros 10++W)
  have h2 := uEread2 s (blocks M r++J++L) (tail5 ms n++zeros 10++W)
  obtain ⟨u,h3⟩ := uEGrowth s ms n (blocks M r++J++L) W
  obtain ⟨v,h4⟩ := uUnwind s r L (longCode 0 0++tail5 ms (n+1)++zeros 4++W)
  have H := join0 (join0 (join0 h1 (by simpa only [List.append_assoc] using h2)) (by simpa only [tail5,List.append_assoc] using h3)) (by simpa only [longCode,tail5,show c=zeros 10++ones 6 by rfl,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using h4)
  exact ⟨t+2+u+v,by simpa only [pre,longCode,tail5,show 2*(n+1)+2=2*n+4 by omega,List.append_assoc] using H⟩

inductive Good : List Bool → Prop where
  | tail (ms : List Nat) (n : Nat) : Good (tail5 ms n)
  | part (r : Nat) (ms : List Nat) (n : Nat) : Good (Dcode r++tail5 ms n)
  | long (k m : Nat) (ms : List Nat) (n : Nat) : Good (longCode k m++tail5 ms n)
  | last (k m : Nat) : Good (longCode k (m+1))
  | cons (r : Nat) {W : List Bool} : Good W → Good (code r++W)

theorem goodPrefix (r : Nat) {W : List Bool} (h : Good W) : Good (blocks (code 0) r++W) := by
  induction r with
  | zero => exact h
  | succ r ih => simpa only [blocks,List.append_assoc] using Good.cons 0 ih

def lowFront (k : Nat) (W R : List Bool) := front k (low0++ones 8++W++R)
def highFront (k : Nat) (W R : List Bool) := front k (low3++ones 8++W++R)

theorem goodReturn (s : Bool) (k : Nat) {W : List Bool} (h : Good W) (R : List Bool) :
    ∃ W' p, Good W' ∧ Reach s (highFront k W (zeros 22++R)) (lowFront (k+1) W' (zeros p++R)) := by
  cases h with
  | tail ms n =>
    have h1 := phase3 s k (3::ms) n (zeros 12++R)
    have h2 : Reach s (front k (low4++ones 8++tail5 ms (n+1)++zeros 16++R)) (lowFront (k+1) (Dcode 0++tail5 ms (n+3)) (zeros 4++R)) := by
      unfold lowFront
      simp only [List.append_assoc]
      apply phase4of s k (ones 8++(tail5 ms (n+1)++(zeros 16++R))) (ones 8++(Dcode 0++(tail5 ms (n+3)++(zeros 4++R))))
      intro L
      cases ms with
      | nil => simpa only [Dcode,pre,lowFront,List.append_assoc] using uH0One s (n+1) L R
      | cons p ms => simpa only [Dcode,pre,lowFront,List.append_assoc] using uH0More s p (n+1) ms L R
    refine ⟨Dcode 0++tail5 ms (n+3),4,Good.part 0 ms (n+3),?_⟩
    have h1' : Reach s (highFront k (tail5 ms n) (zeros 22++R)) (front k (low4++ones 8++tail5 ms (n+1)++zeros 16++R)) := by
      simpa only [highFront,tail5,tRuns,List.append_assoc,show 2*(n+1)+2=2*n+4 by omega,← List.append_assoc (zeros 10) (zeros 12) R,← List.append_assoc (zeros 4) (zeros 12) R,show zeros 10++zeros 12=zeros 22 by rfl,show zeros 4++zeros 12=zeros 16 by rfl] using h1
    exact reach_trans h1' h2
  | part r ms n =>
    cases ms with
    | nil =>
      have h1 := tD s k r (ones (2*n+2)++zeros 22++R)
      have h2 := phase4of s k (transformed r++ones (2*n+2)++zeros 22++R) (ones 8++blocks (code 0) r++longCode 0 (n+1)++zeros 16++R) (fun L => by
        simpa only [pre,List.append_assoc,← List.append_assoc (zeros 10) (zeros 12) R,← List.append_assoc (zeros 4) (zeros 12) R,show zeros 10++zeros 12=zeros 22 by rfl,show zeros 4++zeros 12=zeros 16 by rfl] using uPart1 s r n L (zeros 12++R))
      exact ⟨blocks (code 0) r++longCode 0 (n+1),16,goodPrefix r (Good.last 0 n),by simpa only [highFront,lowFront,tail5,tRuns,List.nil_append,List.append_assoc] using reach_trans h1 (by simpa only [List.append_assoc] using h2)⟩
    | cons p ms =>
      have h1 := tD s k r (ones (2*p+2)++tail5 ms n++zeros 22++R)
      have h2 := phase4of s k (transformed r++ones (2*p+2)++tail5 ms n++zeros 22++R) (ones 8++blocks (code 0) r++longCode 0 p++tail5 ms (n+1)++zeros 16++R) (fun L => by
        simpa only [pre,List.append_assoc,← List.append_assoc (zeros 10) (zeros 12) R,← List.append_assoc (zeros 4) (zeros 12) R,show zeros 10++zeros 12=zeros 22 by rfl,show zeros 4++zeros 12=zeros 16 by rfl] using uPartMore s r p n ms L (zeros 12++R))
      exact ⟨blocks (code 0) r++(longCode 0 p++tail5 ms (n+1)),16,goodPrefix r (Good.long 0 p ms (n+1)),by simpa only [highFront,lowFront,tail5,tRuns,List.append_assoc] using reach_trans h1 (by simpa only [tail5,List.append_assoc] using h2)⟩
  | long j m ms n =>
    have h1 := tLong s k j m (tail5 ms n++zeros 22++R)
    have h2 := phase4of s k (V++blocks cycleIn j++ones (2*m+6)++tail5 ms n++zeros 22++R) (ones 8++blocks (code 0) (j+1)++highOut m++ones 2++tail5 ms (n+2)++zeros 10++R) (fun L => by
      cases ms with
      | nil => simpa only [List.append_assoc,← List.append_assoc (zeros 16) (zeros 6) R,← List.append_assoc (zeros 4) (zeros 6) R,show zeros 16++zeros 6=zeros 22 by rfl,show zeros 4++zeros 6=zeros 10 by rfl] using uLongMore1 s j m n L (zeros 6++R)
      | cons p ms => simpa only [List.append_assoc,← List.append_assoc (zeros 16) (zeros 6) R,← List.append_assoc (zeros 4) (zeros 6) R,show zeros 16++zeros 6=zeros 22 by rfl,show zeros 4++zeros 6=zeros 10 by rfl] using uLongMore s j m n p ms L (zeros 6++R))
    have H := reach_trans h1 (by simpa only [List.append_assoc] using h2)
    cases m with
    | zero =>
      refine ⟨blocks (code 0) (j+1)++(Dcode 0++tail5 ms (n+2)),10,goodPrefix (j+1) (Good.part 0 ms (n+2)),?_⟩
      simpa only [highFront,lowFront,Dcode,highOut,show b=zeros 10++ones 2 by rfl,List.append_assoc] using H
    | succ m =>
      refine ⟨blocks (code 0) (j+1)++tail5 (m::0::ms) (n+2),10,goodPrefix (j+1) (Good.tail (m::0::ms) (n+2)),?_⟩
      simpa only [highFront,lowFront,highOut,tail5,tRuns,List.append_assoc] using H
  | last j m =>
    have h1 := tLong s k j (m+1) (zeros 22++R)
    have h2 := phase4of s k (V++blocks cycleIn j++ones (2*(m+1)+6)++zeros 22++R) (ones 8++blocks (code 0) (j+1)++highOut (m+1)++ones 8++zeros 8++R) (fun L => by
      simpa only [List.append_assoc,← List.append_assoc (zeros 18) (zeros 4) R,← List.append_assoc (zeros 4) (zeros 4) R,show zeros 18++zeros 4=zeros 22 by rfl,show zeros 4++zeros 4=zeros 8 by rfl] using uLongTerminal s j (m+1) L (zeros 4++R))
    refine ⟨blocks (code 0) (j+1)++tail5 [m] 3,8,goodPrefix (j+1) (Good.tail [m] 3),?_⟩
    simpa only [highFront,lowFront,highOut,tail5,tRuns,List.nil_append,List.append_assoc] using reach_trans h1 (by simpa only [highOut,tail5,tRuns,List.nil_append,List.append_assoc] using h2)
  | @cons r W hW =>
    have h1 := tD s k r (ones 2++W++zeros 22++R)
    have h1' : Reach s (highFront k (code r++W) (zeros 22++R)) (front k (low4++transformed r++ones 2++W++zeros 22++R)) := by
      simpa only [highFront,codeD,show a=zeros 5++ones 2 by rfl,List.append_assoc] using h1
    cases hW with
    | tail ms n =>
      have h2 := phase4of s k (transformed r++ones 2++tail5 ms n++zeros 22++R) (ones 8++blocks (code 0) r++longCode 0 0++tail5 ms (n+1)++zeros 16++R) (fun L => by
        simpa only [pre,List.append_assoc,← List.append_assoc (zeros 10) (zeros 12) R,← List.append_assoc (zeros 4) (zeros 12) R,show zeros 10++zeros 12=zeros 22 by rfl,show zeros 4++zeros 12=zeros 16 by rfl] using uCarryTail s r n ms L (zeros 12++R))
      exact ⟨blocks (code 0) r++(longCode 0 0++tail5 ms (n+1)),16,goodPrefix r (Good.long 0 0 ms (n+1)),by simpa only [lowFront,List.append_assoc] using reach_trans h1' (by simpa only [List.append_assoc] using h2)⟩
    | part j ms n =>
      have h2 := phase4of s k (transformed r++ones 2++Dcode j++tail5 ms n++zeros 22++R) (ones 8++blocks (code 0) r++Dcode (j+1)++tail5 ms n++zeros 22++R) (fun L => by simpa only [pre,List.append_assoc] using uIncD s r j L (tail5 ms n++zeros 22++R))
      exact ⟨blocks (code 0) r++(Dcode (j+1)++tail5 ms n),22,goodPrefix r (Good.part (j+1) ms n),by simpa only [lowFront,List.append_assoc] using reach_trans h1' (by simpa only [List.append_assoc] using h2)⟩
    | long j m ms n =>
      have h2 := phase4of s k (transformed r++ones 2++longCode j m++tail5 ms n++zeros 22++R) (ones 8++blocks (code 0) r++longCode (j+1) m++tail5 ms n++zeros 22++R) (fun L => by simpa only [pre,List.append_assoc] using uIncLong s r j m L (tail5 ms n++zeros 22++R))
      exact ⟨blocks (code 0) r++(longCode (j+1) m++tail5 ms n),22,goodPrefix r (Good.long (j+1) m ms n),by simpa only [lowFront,List.append_assoc] using reach_trans h1' (by simpa only [List.append_assoc] using h2)⟩
    | last j m =>
      have h2 := phase4of s k (transformed r++ones 2++longCode j (m+1)++zeros 22++R) (ones 8++blocks (code 0) r++longCode (j+1) (m+1)++zeros 22++R) (fun L => by simpa only [pre,List.append_assoc] using uIncLong s r j (m+1) L (zeros 22++R))
      exact ⟨blocks (code 0) r++longCode (j+1) (m+1),22,goodPrefix r (Good.last (j+1) m),by simpa only [lowFront,List.append_assoc] using reach_trans h1' (by simpa only [List.append_assoc] using h2)⟩
    | @cons j U hU =>
      have h2 := phase4of s k (transformed r++ones 2++code j++U++zeros 22++R) (ones 8++blocks (code 0) r++code (j+1)++U++zeros 22++R) (fun L => by simpa only [pre,codeD,List.append_assoc] using uIncD s r j L (a++U++zeros 22++R))
      exact ⟨blocks (code 0) r++(code (j+1)++U),22,goodPrefix r (Good.cons (j+1) hU),by simpa only [lowFront,List.append_assoc] using reach_trans h1' (by simpa only [List.append_assoc] using h2)⟩

theorem epochs (s : Bool) (N k : Nat) {W : List Bool} (h : Good W) (p : Nat) :
    ∃ t z, N≤t ∧ run0 (table s) t (lowFront k W (zeros (22*N+p))) = some z := by
  induction N generalizing k W p with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    let R := zeros (22*N+p)
    let V := ones 8++W++zeros 22++R
    obtain ⟨a,ha,h1⟩ := phase0 s k V
    obtain ⟨b,h2⟩ := phase1 s k V
    obtain ⟨c,h3⟩ := phase2 s (k+1) V
    obtain ⟨W',p',hg,d,h4⟩ := goodReturn s (k+1) h R
    obtain ⟨e,z,he,h5⟩ := ih (k+2) hg (p+p')
    have H := join0 (join0 (join0 h1 h2) h3) (by simpa only [highFront,V,List.append_assoc] using h4)
    have h5' : run0 (table s) e (lowFront (k+1+1) W' (zeros p'++R)) = some z := by
      simpa only [R,← zeros_add,show p'+(22*N+p)=22*N+(p+p') by omega] using h5
    refine ⟨a+b+c+d+e,z,by omega,?_⟩
    simpa only [lowFront,V,R,List.append_assoc,← zeros_add,show 22+ (22*N+p)=22*(N+1)+p by omega] using join0 H h5'


theorem entry (s : Bool) (R : List Bool) :
    run0 (table s) 4054 ⟨0,[],zeros 150++R⟩ =
      some (lowFront 4 (tail5 [0,0] 7) (zeros 89++R)) := by
  have h0 : run0 (table s) 200 ⟨rename s 0,bits "",bits "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "01111111",bits "1011100001111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h1 : run0 (table s) 200 ⟨rename s 3,bits "01111111",bits "1011100001111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "0010111011101111011111",bits "11111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h2 : run0 (table s) 200 ⟨rename s 3,bits "0010111011101111011111",bits "11111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 2,bits "011",bits "000001101110110011000001111111111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h3 : run0 (table s) 200 ⟨rename s 2,bits "011",bits "000001101110110011000001111111111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 1,bits "101",bits "1000011011101100110000111111111111111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h4 : run0 (table s) 200 ⟨rename s 1,bits "101",bits "1000011011101100110000111111111111111110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "101110111011111011101111011111",bits "00111111111100011111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h5 : run0 (table s) 200 ⟨rename s 0,bits "101110111011111011101111011111",bits "00111111111100011111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "1011111011101111011111",bits "00001100110011111111111100011111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h6 : run0 (table s) 200 ⟨rename s 3,bits "1011111011101111011111",bits "00001100110011111111111100011111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "10111110111011111011101111011111",bits "0110001111111111000001111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h7 : run0 (table s) 200 ⟨rename s 0,bits "10111110111011111011101111011111",bits "0110001111111111000001111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "0011111011111011101111011111",bits "00000000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h8 : run0 (table s) 200 ⟨rename s 3,bits "0011111011111011101111011111",bits "00000000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 1,bits "1100111011111011101111011111",bits "001100000000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h9 : run0 (table s) 200 ⟨rename s 1,bits "1100111011111011101111011111",bits "001100000000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "0011",bits "1000011011101100110000110011000011111000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h10 : run0 (table s) 200 ⟨rename s 0,bits "0011",bits "1000011011101100110000110011000011111000000000111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "1111111011101111011111",bits "1100110000110011000001111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h11 : run0 (table s) 200 ⟨rename s 3,bits "1111111011101111011111",bits "1100110000110011000001111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 3,bits "0100111110111011111011101111011111",bits "10110011000001111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h12 : run0 (table s) 200 ⟨rename s 3,bits "0100111110111011111011101111011111",bits "10110011000001111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 2,bits "001111011111",bits "00110011000011001100001100110000111111111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h13 : run0 (table s) 200 ⟨rename s 2,bits "001111011111",bits "00110011000011001100001100110000111111111110111111111100000111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "10111010101010111010101010111011101111101110111110111011111011101111011111",bits "11111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h14 : run0 (table s) 200 ⟨rename s 0,bits "10111010101010111010101010111011101111101110111110111011111011101111011111",bits "11111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "10111011101111101110111110111011111011101111011111",bits "00111111110011111111110000011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h15 : run0 (table s) 200 ⟨rename s 0,bits "10111011101111101110111110111011111011101111011111",bits "00111111110011111111110000011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "111111",bits "011011101100110000110011000011001100001100110011111111110011111111110000011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h16 : run0 (table s) 200 ⟨rename s 0,bits "111111",bits "011011101100110000110011000011001100001100110011111111110011111111110000011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "01010111111010101011110011111011101111101110111110111011111011101111011111",bits "011100011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h17 : run0 (table s) 200 ⟨rename s 0,bits "01010111111010101011110011111011101111101110111110111011111011101111011111",bits "011100011111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "111011110011111011101111101110111110111011111011101111011111",bits "11111100000111100011000001111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h18 : run0 (table s) 200 ⟨rename s 0,bits "111011110011111011101111101110111110111011111011101111011111",bits "11111100000111100011000001111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 1,bits "10110111111011111101111110101010111111111111111011101111101110111110111011111011101111011111",bits "111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h19 : run0 (table s) 200 ⟨rename s 1,bits "10110111111011111101111110101010111111111111111011101111101110111110111011111011101111011111",bits "111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "0111111011101111011111",bits "1100110000110011000011001100000000000000111111110000011000001100000111111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  have h20 : run0 (table s) 54 ⟨rename s 0,bits "0111111011101111011111",bits "1100110000110011000011001100000000000000111111110000011000001100000111111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ = some ⟨rename s 0,bits "",bits "00000001100011001100001100110000110011000011001100000000000000111111110000011000001100000111111111111111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"++R⟩ := by cases s <;> rfl
  exact join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20

theorem padded_live (s : Bool) (N : Nat) :
    ∃ t z, N≤t ∧ run0 (table s) t ⟨0,[],zeros (150+22*N)⟩ = some z := by
  have h0 := entry s (zeros (22*N))
  obtain ⟨t,z,ht,h⟩ := epochs s N 4 (Good.tail [0,0] 7) 89
  have h' : run0 (table s) t (lowFront 4 (tail5 [0,0] 7) (zeros 89++zeros (22*N))) = some z := by
    simpa only [← zeros_add, Nat.add_comm 89 (22*N)] using h
  exact ⟨4054+t,z,by omega,by simpa only [zeros_add] using join0 h0 h'⟩
open BB6Coverage.Agent50Zipper

private theorem getD_zeros (k i : Nat) : (zeros k).getD i false = false := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem padded_blank (k : Nat) : embed ⟨0,0,[],zeros k⟩ = blank := by
  unfold embed blank
  congr 1
  funext x
  unfold atCell
  split <;> simp only [List.getD_nil,getD_zeros]

/-- All completions of all two literal one-hole tables are nonhalting. -/
theorem never (s : Bool) (m : Machine) (hm : compatible (table s) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live s n
  let start : Z := ⟨0,0,[],zeros (150+22*n)⟩
  have hz : (zrun (table s) t start).map project = some z :=
    (run_project (table s) t start).trans hr
  cases hZ : zrun (table s) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table s) m hm t start z' hZ
    have hb : embed start = blank := padded_blank _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43Run
