import ZipThreeHoleAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1TwoLatePair
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot

def p (w : Bool) : PartialMachine := FAR.fromCodes
  (if w then [7,3,11,6,14,18,2,13,24,22,3,8]
        else [7,3,11,6,14,18,2,13,24,20,15,10])
abbrev oo := rep [true]
abbrev blocks := rep [false,true,true]
def pad (w : Bool) : List Bool := if w then [] else [false]
def tail (w : Bool) : List Bool := if w then [true] else []
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def family (w : Bool) (n j : Nat) : Z0 :=
  F [] (pad w ++ oo n ++ blocks j ++ tail w)

theorem oo_add (i j : Nat) : oo (i+j) = oo i ++ oo j := by
  induction i with
  | zero => simp [rep]
  | succ i ih => simp [rep,Nat.succ_add,ih]
theorem oo_snoc (n : Nat) : oo n ++ [true] = oo (n+1) := rep_snoc [true] n

theorem oo_true (n : Nat) (R : List Bool) : oo n ++ true::R = oo (n+1) ++ R := by
  rw [← oo_snoc]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem blocks_add (i j : Nat) : blocks (i+j) = blocks i ++ blocks j := by
  induction i with
  | zero => simp [rep]
  | succ i ih => simp [rep,Nat.succ_add,ih,List.append_assoc]

theorem trip_ones (k r : Nat) : oo (3*k+r) = rep [true,true,true] k ++ oo r := by
  induction k with
  | zero => simp [rep]
  | succ k ih =>
    rw [show 3*(k+1)+r=3+(3*k+r) by omega,oo_add,ih]
    rfl

theorem rot (n : Nat) : rep [true,true,false] n ++ [true,true] = [true,true] ++ blocks n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.append_assoc,ih]; rfl

variable (w : Bool)

theorem a_sweep (n : Nat) (L R : List Bool) :
    run0 (p w) n (A (true::L) (oo n ++ R)) = some (A (true::(oo n ++ L)) R) := by
  have h := sweepR (p w) 0 [true] [] [true] [true] 1
    (by intro X Y; cases w <;> rfl) n L R
  simpa only [Nat.one_mul,List.nil_append,List.cons_append] using h

theorem b_sweep (n : Nat) (L R : List Bool) :
    run0 (p w) n (B (oo n ++ L) R) = some (B L (oo n ++ R)) := by
  have h := sweepL (p w) 1 [] [] [true] [true] 1
    (by intro X Y; cases w <;> rfl) n L R
  simpa only [Nat.one_mul,List.nil_append] using h

theorem f_sweep (n : Nat) (L R : List Bool) :
    run0 (p w) (3*n) (F (rep [true,true,true] n ++ L) R) =
      some (F L (rep (if w then [true,true,false] else [false,true,true]) n ++ R)) := by
  have h := sweepL (p w) 5 [] [] [true,true,true]
    (if w then [true,true,false] else [false,true,true]) 3
    (by intro X Y; cases w <;> rfl) n L R
  simpa only [List.nil_append] using h

/-- Consume one 011 block, incrementing the unary prefix by five. -/
theorem block (n : Nat) (R : List Bool) :
    run0 (p w) (2*(n+1)+(if w then 8 else 12))
      (F [] (pad w ++ oo (n+1) ++ false::true::true::R)) =
      some (F [] (pad w ++ oo (n+6) ++ R)) := by
  cases w with
  | false =>
    have h1 : run0 (p false) 2 (F [] (pad false ++ oo (n+1) ++ false::true::true::R)) =
      some (A [true] (oo (n+2) ++ false::true::true::R)) := rfl
    have h2 := a_sweep false (n+2) [] (false::true::true::R)
    simp only [List.append_nil] at h2
    have h3 : run0 (p false) 2 (A (oo (n+3)) (false::true::true::R)) =
      some (B (oo (n+5)) (true::R)) := rfl
    have h4 := b_sweep false (n+5) [] (true::R)
    simp only [List.append_nil] at h4
    have h5 : run0 (p false) 3 (B [] (oo (n+5) ++ true::R)) =
      some (F [] (pad false ++ oo (n+6) ++ R)) := by
      rw [oo_true]
      rfl
    have H := join0 h1 (join0 h2 (join0 h3 (join0 h4 h5)))
    rw [show 2*(n+1)+(if false then 8 else 12)=2+((n+2)+(2+((n+5)+3))) by simp; omega]
    exact H
  | true =>
    have h1 : run0 (p true) 1 (F [] (pad true ++ oo (n+1) ++ false::true::true::R)) =
      some (A [true,true] (oo n ++ false::true::true::R)) := rfl
    have h2 := a_sweep true n [true] (false::true::true::R)
    have h2' : run0 (p true) n (A [true,true] (oo n ++ false::true::true::R)) =
      some (A (oo (n+2)) (false::true::true::R)) := by
      rw [← oo_snoc]; exact h2
    have h3 : run0 (p true) 2 (A (oo (n+2)) (false::true::true::R)) =
      some (B (oo (n+4)) (true::R)) := rfl
    have h4 := b_sweep true (n+4) [] (true::R)
    simp only [List.append_nil] at h4
    have h5 : run0 (p true) 3 (B [] (oo (n+4) ++ true::R)) =
      some (F [] (pad true ++ oo (n+6) ++ R)) := by
      rw [oo_true]
      rfl
    have H := join0 h1 (join0 h2' (join0 h3 (join0 h4 h5)))
    rw [show 2*(n+1)+(if true then 8 else 12)=1+(n+(2+((n+4)+3))) by simp; omega]
    exact H

def blockCost (w : Bool) (n : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => 2*n+(if w then 8 else 12)+blockCost w (n+5) j

theorem all_blocks (n j : Nat) : run0 (p w) (blockCost w (n+1) j)
    (family w (n+1) j) = some (family w (n+1+5*j) 0) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    have h1 : run0 (p w) (2*(n+1)+(if w then 8 else 12))
        (family w (n+1) (j+1)) = some (family w (n+6) j) := by
      simpa only [family,rep,List.append_assoc,List.cons_append,List.nil_append] using block w n (blocks j ++ tail w)
    have h2 := ih (n+5)
    have H := join0 h1 h2
    rw [show n+1+5*(j+1)=(n+5)+1+5*j by omega]
    exact H

def base (w : Bool) : List Bool := if w then [true,true,true] else [false,true,true]

theorem blank_sweep (n : Nat) :
    run0 (p w) ((n+1)+(if w then 14 else 16)) (family w (n+1) 0) =
      some (F (oo (n+4)) (base w)) := by
  cases w with
  | false =>
    have h1 : run0 (p false) 2 (family false (n+1) 0) =
      some (A [true] (oo (n+2))) := by
      simp only [family,pad,tail,Bool.false_eq_true,ite_false,show blocks 0=[] by rfl,List.append_nil,List.cons_append,List.nil_append]
      rfl
    have h2 : run0 (p false) (n+2) (A [true] (oo (n+2))) =
      some (A (oo (n+3)) []) := by
      change _ = some (A (true::oo (n+2)) [])
      simpa only [List.append_nil] using a_sweep false (n+2) [] []
    have h3 : run0 (p false) 13 (A (oo (n+3)) []) = some (F (oo (n+4)) (base false)) := rfl
    have H := join0 h1 (join0 h2 h3)
    rw [show n+1+(if false then 14 else 16)=2+(n+2+13) by simp; omega]
    exact H
  | true =>
    have h1 : run0 (p true) 1 (family true (n+1) 0) =
      some (A [true,true] (oo (n+1))) := by
      simp only [family,pad,tail,ite_true,List.nil_append,show blocks 0=[] by rfl,List.append_nil,oo_snoc]
      rfl
    have h2 : run0 (p true) (n+1) (A [true,true] (oo (n+1))) =
      some (A (oo (n+3)) []) := by
      have h := a_sweep true (n+1) [true] []
      change _ = some (A (true::oo (n+2)) [])
      simpa only [List.append_nil,oo_snoc] using h
    have h3 : run0 (p true) 13 (A (oo (n+3)) []) = some (F (oo (n+4)) (base true)) := rfl
    have H := join0 h1 (join0 h2 h3)
    rw [show n+1+(if true then 14 else 16)=1+(n+1+13) by simp; omega]
    exact H

def phaseCost (w : Bool) (k a : Nat) : Nat := 3*k+a+(if w then 14 else 16)+3*(k+1)

theorem packed (k : Nat) :
    rep (if w then [true,true,false] else [false,true,true]) (k+1) ++ base w =
      pad w ++ oo 2 ++ blocks (k+1) ++ tail w := by
  cases w with
  | false => simp only [Bool.false_eq_true,ite_false,base,pad,tail,List.append_nil,rep_snoc]; rfl
  | true =>
    simp only [ite_true,base,pad,tail,List.nil_append]
    change rep [true,true,false] (k+1) ++ ([true,true] ++ [true]) = _
    rw [← List.append_assoc,rot]
    rfl

theorem phase (k a : Nat) (h : 0 < 3*k+a) :
    run0 (p w) (phaseCost w k a) (family w (3*k+a) 0) =
      some (F (oo a) (pad w ++ oo 2 ++ blocks (k+1) ++ tail w)) := by
  have h1 := blank_sweep w (3*k+a-1)
  rw [show 3*k+a-1+1=3*k+a by omega,show 3*k+a-1+4=3*(k+1)+a by omega,trip_ones] at h1
  have h2 := f_sweep w (k+1) (oo a) (base w)
  rw [packed] at h2
  exact join0 h1 h2

theorem phase0 (k : Nat) (h : 0 < k) :
    run0 (p w) (phaseCost w k 0) (family w (3*k) 0) = some (family w 2 (k+1)) := by
  exact phase w k 0 (by omega)

theorem phase1 (k : Nat) :
    run0 (p w) (phaseCost w k 1+9) (family w (3*k+1) 0) = some (family w 4 (k+2)) := by
  have h1 := phase w k 1 (by omega)
  have h2 : run0 (p w) 9 (F (oo 1) (pad w ++ oo 2 ++ blocks (k+1) ++ tail w)) =
      some (family w 4 (k+2)) := by cases w <;> rfl
  exact join0 h1 h2

def last (w : Bool) (k : Nat) : Z0 :=
  ⟨4,[],(if w then [true,false] else [true,true]) ++ (pad w ++ oo 2 ++ blocks (k+1) ++ tail w)⟩

theorem phase2 (k : Nat) :
    run0 (p w) (phaseCost w k 2+2) (family w (3*k+2) 0) = some (last w k) := by
  have h1 := phase w k 2 (by omega)
  have h2 : run0 (p w) 2 (F (oo 2) (pad w ++ oo 2 ++ blocks (k+1) ++ tail w)) =
      some (last w k) := by cases w <;> rfl
  exact join0 h1 h2

-- Exact chain from the blank tape, calculated through the symbolic macros.
theorem entry : run0 (p w) (if w then 37 else 41) ⟨0,[],[]⟩ = some (family w 9 0) := by cases w <;> decide

theorem c9 : run0 (p w) (phaseCost w 3 0 + blockCost w 2 4) (family w 9 0) = some (family w 22 0) :=
  join0 (phase0 w 3 (by decide)) (all_blocks w 1 4)
theorem c22 : run0 (p w) (phaseCost w 7 1+9+blockCost w 4 9) (family w 22 0) = some (family w 49 0) :=
  join0 (phase1 w 7) (all_blocks w 3 9)
theorem c49 : run0 (p w) (phaseCost w 16 1+9+blockCost w 4 18) (family w 49 0) = some (family w 94 0) :=
  join0 (phase1 w 16) (all_blocks w 3 18)
theorem c94 : run0 (p w) (phaseCost w 31 1+9+blockCost w 4 33) (family w 94 0) = some (family w 169 0) :=
  join0 (phase1 w 31) (all_blocks w 3 33)
theorem c169 : run0 (p w) (phaseCost w 56 1+9+blockCost w 4 58) (family w 169 0) = some (family w 294 0) :=
  join0 (phase1 w 56) (all_blocks w 3 58)
theorem c294 : run0 (p w) (phaseCost w 98 0+blockCost w 2 99) (family w 294 0) = some (family w 497 0) :=
  join0 (phase0 w 98 (by decide)) (all_blocks w 1 99)
def stopTime (w : Bool) : Nat := if w then 77850 else 78752

theorem arrival : run0 (p w) (stopTime w) ⟨0,[],[]⟩ = some (last w 165) := by
  have H := join0 (entry w) (join0 (c9 w) (join0 (c22 w) (join0 (c49 w) (join0 (c94 w) (join0 (c169 w) (join0 (c294 w) (phase2 w 165)))))))
  cases w <;> exact H

theorem readArrival : (knownRun (p w) (stopTime w)).map readSlot = some (4,false) := by
  have H : (zrun (p w) (stopTime w) start).map project = some (last w 165) :=
    (run_project (p w) (stopTime w) start).trans (arrival w)
  rw [knownRun_zip]
  cases hz : zrun (p w) (stopTime w) start with
  | none => simp [hz] at H
  | some z =>
    have h := Option.some.inj (by simpa only [hz,Option.map_some] using H)
    simp only [Option.map_some,read_embed]
    have hq := congrArg Z0.q h
    have hl := congrArg Z0.l h
    change z.q = 4 at hq
    change z.l = [] at hl
    rw [hq,hl]
    rfl

theorem cover (B : Nat) (hw : weightOK (p w) (4,false) (stopTime w) B = true) : Cover (WeightedBound B) (p w) := by
  cases hr : knownRun (p w) (stopTime w) with
  | none => have H := readArrival w; simp [hr] at H
  | some c =>
    have hs : readSlot c = (4,false) := by simpa [hr] using readArrival w
    have hroot : p w initialSlot = some (some ⟨true,true,1⟩) := by cases w <;> decide
    have hh : p w (4,false) = none := by cases w <;> decide
    have hrest : restOK (p w) (4,false) = true := by cases w <;> decide
    exact .leaf _ (WeightedTNFCertificate.lastHole (cut := 6) hroot (support6 (p w)) (by decide) hr
      (by rw [hs]; exact hh)
      (by rw [hs]; exact restOK_sound _ _ hrest)
      (by rw [hs]; exact weightOK_sound _ _ _ _ hw)).sound

theorem cover6 : Cover (WeightedBound 78753) (FAR.fromCodes [7,3,11,6,14,18,2,13,24,20,15,10]) :=
  cover false 78753 (by decide)
theorem cover7 : Cover (WeightedBound 77851) (FAR.fromCodes [7,3,11,6,14,18,2,13,24,22,3,8]) :=
  cover true 77851 (by decide)
#print axioms cover6
#print axioms cover7
end BB6.Agent6D1TwoLatePair
