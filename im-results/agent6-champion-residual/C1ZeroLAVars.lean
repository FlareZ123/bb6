import C1ZeroLACore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1ZeroLAVars
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6C1ZeroLACore
open BB6.Agent6C1ZeroLAFour (P Q T L0 h f z u as bs cs rep_add z_add shift)
inductive V | v84 | v85 | v87 | v89 | v90 | v91 | v92 | v93 | v156
open V
def ctr : V → PartialMachine
  | v84 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,0]
  | v85 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,4]
  | v87 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,8]
  | v89 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,10]
  | v90 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,11]
  | v91 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,16]
  | v92 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,18]
  | v93 => FAR.fromCodes [7,21,11,24,14,0,3,16,12,11,3,19]
  | v156 => FAR.fromCodes [7,23,11,24,14,0,3,16,12,11,20,13]
def sc : V → Nat | v156 => 7 | _ => 5
def st : V → Nat | v156 => 11 | _ => 9
def sq : V → Fin 6 | v156 => 3 | _ => 5
def core (v : V) : Core (ctr v) where
  q := sq v
  sc := sc v
  st := st v
  start := by cases v <;> intro R <;> rfl
  scan := by cases v <;> intro L R <;> rfl
  pop := by cases v <;> intro L R <;> rfl
  finish := by cases v <;> intro R <;> rfl

theorem core_q (v : V) : (core v).q = sq v := rfl
theorem bs_one : bs 1 = Q := rfl

theorem zero (v : V) (L R : List Bool) : run0 (ctr v) 11 ⟨sq v,L0++L,z 2++f++R⟩ = some ⟨4,P++L,f++u 3++R⟩ := by cases v <;> rfl

theorem t84 (L : List Bool) : run0 (ctr v84) 23 ⟨5,L0++L,z 2++u 3⟩ = some ⟨4,P++L,f++Q++u 3⟩ := rfl
theorem t156 (L : List Bool) : run0 (ctr v156) 31 ⟨3,L0++L,z 2++u 3⟩ = some ⟨4,P++L,f++bs 2++u 3⟩ := rfl
theorem t87a (L : List Bool) : run0 (ctr v87) 15 ⟨5,L0++L,z 2++u 3⟩ = some ⟨4,P++L,f++Q++[true,false]⟩ := rfl
theorem t87b (L : List Bool) : run0 (ctr v87) 21 ⟨5,L0++L,z 2++[true,false]⟩ = some ⟨4,P++L,f++Q++u 3⟩ := rfl

def pair (b : Bool) : V := if b then v85 else v89
def pCost (b : Bool) := if b then 19 else 15
def qCost (b : Bool) := if b then 23 else 19
theorem pair_q (b : Bool) : sq (pair b)=5 := by cases b <;> rfl
theorem pairA (b : Bool) (L R : List Bool) : run0 (ctr (pair b)) (pCost b) ⟨5,L0++L,z 2++u 3++R⟩ = some ⟨4,P++L,f++Q++u 2++R⟩ := by cases b <;> rfl
theorem pairB (b : Bool) (L : List Bool) : run0 (ctr (pair b)) (qCost b) ⟨5,L0++L,z 2++u 2++f++u 3⟩ = some ⟨4,P++L,f++Q++z 2++u 3⟩ := by cases b <;> rfl

theorem t90 (L R : List Bool) : run0 (ctr v90) 17 ⟨5,L0++L,z 2++u 3++f++R⟩ = some ⟨4,P++L,f++Q++z 2++h++R⟩ := rfl

def pair2 (b : Bool) : V := if b then v93 else v91
def p2Cost (b : Bool) := if b then 17 else 15
theorem pair2_q (b : Bool) : sq (pair2 b)=5 := by cases b <;> rfl
theorem t9193 (b : Bool) (L R : List Bool) : run0 (ctr (pair2 b)) (p2Cost b) ⟨5,L0++L,z 2++u 3++f++R⟩ = some ⟨4,P++L,f++Q++z 3++R⟩ := by cases b <;> rfl

theorem t92 (L R : List Bool) : run0 (ctr v92) 15 ⟨5,L0++L,z 2++u 3++R⟩ = some ⟨4,P++L,f++Q++f++h++R⟩ := rfl

theorem step_add (v : V) (n k j : Nat) (S U : List Bool)
    (term : ∀ L : List Bool, run0 (ctr v) k ⟨(core v).q,L0++L,z 2++S⟩ = some ⟨4,P++L,f++bs j++U⟩) :
    run0 (ctr v) (cost (core v) n k) (cfg n S) = some (cfg (n+j) U) := by
  rw [←cfg_add n j U]
  exact step (core v) n k S (bs j++U) (fun L => by simpa only [core_q,bs_one,pair_q,pair2_q,sq,List.append_assoc] using term L)

theorem grow84 (n : Nat) : run0 (ctr v84) (cost (core v84) n 23) (cfg n (u 3)) = some (cfg (n+1) (u 3)) := step_add v84 n 23 1 _ _ t84
theorem grow156 (n : Nat) : run0 (ctr v156) (cost (core v156) n 31) (cfg n (u 3)) = some (cfg (n+2) (u 3)) := step_add v156 n 31 2 _ _ t156

theorem grow87 (n : Nat) : run0 (ctr v87) (cost (core v87) n 15+cost (core v87) (n+1) 21) (cfg n (u 3)) = some (cfg (n+2) (u 3)) := by
  have H1 := step_add v87 n 15 1 (u 3) [true,false] t87a
  have H2 := step_add v87 (n+1) 21 1 [true,false] (u 3) t87b
  exact join0 H1 H2

def S85 := u 3++f++u 3
def S85b := u 2++f++u 3
def S85c := z 2++u 3

theorem grow8589 (b : Bool) (n : Nat) :
    run0 (ctr (pair b)) (cost (core (pair b)) n (pCost b)+cost (core (pair b)) (n+1) (qCost b)+cost (core (pair b)) (n+2) 11) (cfg n S85) = some (cfg (n+2) S85) := by
  have H1 := step_add (pair b) n (pCost b) 1 S85 S85b (fun L => by
    simpa only [core_q,bs_one,pair_q,pair2_q,S85,S85b,List.append_assoc] using pairA b L (f++u 3))
  have H2 := step_add (pair b) (n+1) (qCost b) 1 S85b S85c (fun L => by
    simpa only [core_q,bs_one,pair_q,pair2_q,S85b,S85c,List.append_assoc] using pairB b L)
  have H3 := step (core (pair b)) (n+2) 11 S85c S85 (fun L => by
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,S85,S85c,List.append_assoc,show z 2=f++f by rfl] using zero (pair b) L (f++u 3))
  exact join0 (join0 H1 H2) H3

def S90 (n : Nat) := u 3++f++u (n+3)
theorem grow90 (n : Nat) :
    run0 (ctr v90) (cost (core v90) n 17+cost (core v90) (n+1) 11) (cfg n (S90 n)) = some (cfg (n+1) (S90 (n+1))) := by
  have H1 := step_add v90 n 17 1 (S90 n) (z 2++u (n+4)) (fun L => by
    have e : u (n+4)=h++u (n+3) := rfl
    rw [e]
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,S90,List.append_assoc] using t90 L (u (n+3)))
  have H2 := step (core v90) (n+1) 11 (z 2++u (n+4)) (S90 (n+1)) (fun L => by
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,S90,show n+1+3=n+4 by omega,List.append_assoc,show z 2=f++f by rfl] using zero v90 L (f++u (n+4)))
  exact join0 H1 H2

def S9193 (n : Nat) := u 3++z (n+1)++u 3
theorem grow9193 (b : Bool) (n : Nat) :
    run0 (ctr (pair2 b)) (cost (core (pair2 b)) n (p2Cost b)+cost (core (pair2 b)) (n+1) 11) (cfg n (S9193 n)) = some (cfg (n+1) (S9193 (n+1))) := by
  have H1 := step_add (pair2 b) n (p2Cost b) 1 (S9193 n) (z (n+3)++u 3) (fun L => by
    have H := t9193 b L (z n++u 3)
    have e : z 3++z n=z (n+3) := by rw [←z_add]; congr 1; omega
    simp only [List.append_assoc] at H
    rw [←List.append_assoc (z 3),e] at H
    simpa only [core_q,bs_one,pair_q,pair2_q,S9193,List.append_assoc,show z (n+1)=f++z n by rfl] using H)
  have H2 := step (core (pair2 b)) (n+1) 11 (z (n+3)++u 3) (S9193 (n+1)) (fun L => by
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,S9193,show n+1+1=n+2 by omega,List.append_assoc,show z (n+3)=f++z (n+2) by rfl] using zero (pair2 b) L (z (n+2)++u 3))
  exact join0 H1 H2

theorem u_add (a b : Nat) : u (a+b)=u a++u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change true :: u (a+b)=true :: (u a++u b); rw [ih]

def S92 (n : Nat) := u (n+3)++f++u 3
theorem grow92 (n : Nat) :
    run0 (ctr v92) (cost (core v92) n 15+cost (core v92) (n+1) 11) (cfg n (S92 n)) = some (cfg (n+1) (S92 (n+1))) := by
  have H1 := step_add v92 n 15 1 (S92 n) (f++u (n+1)++f++u 3) (fun L => by
    have e : u (n+3)=u 3++u n := by rw [←u_add]; congr 1 <;> omega
    rw [S92,e]
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,List.append_assoc,show u (n+1)=h++u n by rfl] using t92 L (u n++f++u 3))
  have H2 := step (core v92) (n+1) 11 (f++u (n+1)++f++u 3) (S92 (n+1)) (fun L => by
    have e : u 3++u (n+1)=u (n+1+3) := by rw [←u_add]; congr 1 <;> omega
    have H := zero v92 L (u (n+1)++f++u 3)
    simp only [List.append_assoc] at H
    rw [←List.append_assoc (u 3),e] at H
    simpa only [core_q,bs_one,pair_q,pair2_q,sq,S92,List.append_assoc] using H)
  exact join0 H1 H2

def family : V → Nat → Z0
  | v84,n => cfg (n+3) (u 3)
  | v156,n => cfg (2*n+3) (u 3)
  | v87,n => cfg (2*n+2) (u 3)
  | v85,n => cfg (2*n) S85
  | v89,n => cfg (2*n) S85
  | v90,n => cfg n (S90 n)
  | v91,n => cfg n (S9193 n)
  | v93,n => cfg n (S9193 n)
  | v92,n => cfg n (S92 n)
def entryCost : V → Nat
  | v84 => 142
  | v156 => 160
  | v87 => 78
  | _ => 52

def cycleCost : V → Nat → Nat
  | v84,n => cost (core v84) (n+3) 23
  | v156,n => cost (core v156) (2*n+3) 31
  | v87,n => cost (core v87) (2*n+2) 15 + cost (core v87) (2*n+2+1) 21
  | v85,n => cost (core v85) (2*n) 19 + cost (core v85) (2*n+1) 23 + cost (core v85) (2*n+2) 11
  | v89,n => cost (core v89) (2*n) 15 + cost (core v89) (2*n+1) 19 + cost (core v89) (2*n+2) 11
  | v90,n => cost (core v90) n 17 + cost (core v90) (n+1) 11
  | v91,n => cost (core v91) n 15 + cost (core v91) (n+1) 11
  | v93,n => cost (core v93) n 17 + cost (core v93) (n+1) 11
  | v92,n => cost (core v92) n 15 + cost (core v92) (n+1) 11

theorem entry (v : V) : run0 (ctr v) (entryCost v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) : run0 (ctr v) (cycleCost v n) (family v n) = some (family v (n+1)) := by
  cases v
  case v84 => simpa only [cycleCost,family,show n+1+3=n+3+1 by omega] using grow84 (n+3)
  case v156 => simpa only [cycleCost,family,show 2*(n+1)+3=2*n+3+2 by omega] using grow156 (2*n+3)
  case v87 => simpa only [cycleCost,family,show 2*(n+1)+2=2*n+2+2 by omega] using grow87 (2*n+2)
  case v85 =>
    have H := grow8589 true (2*n)
    change run0 (ctr v85) (cycleCost v85 n) (family v85 n) = some (cfg (2*n+2) S85) at H
    simpa only [family,show 2*(n+1)=2*n+2 by omega] using H
  case v89 =>
    have H := grow8589 false (2*n)
    change run0 (ctr v89) (cycleCost v89 n) (family v89 n) = some (cfg (2*n+2) S85) at H
    simpa only [family,show 2*(n+1)=2*n+2 by omega] using H
  case v90 => exact grow90 n
  case v91 => exact grow9193 false n
  case v93 => exact grow9193 true n
  case v92 => exact grow92 n

theorem positive (v : V) (n : Nat) : 0 < cycleCost v n := by cases v <;> simp [cycleCost,cost] <;> omega

open BB6.Agent13BlankDelay
theorem never (v : V) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m :=
  never_of_growth (ctr v) (family v) (entryCost v) (cycleCost v) (entry v) (positive v) (growth v) m hm
theorem cover (v : V) (B : Nat) : Cover (WeightedBound B) (ctr v) :=
  .leaf _ (fun m hm => weighted_never B m (never v m hm))
#print axioms growth
#print axioms entry
#print axioms never
#print axioms cover
end BB6.Agent6C1ZeroLAVars
