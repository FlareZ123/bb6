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
