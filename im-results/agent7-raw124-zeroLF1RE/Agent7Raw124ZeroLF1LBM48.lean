import BlockPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw124ZeroLF1LBM48
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,false,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,true,1⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,false,1⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def B (l r : List Bool) : HZ := ⟨1,l,r⟩
def F (l r : List Bool) : HZ := ⟨5,l,r⟩
def P : Nat → List Bool | 0 => [] | n+1 => true::true::true::false::P n
def Q : Nat → List Bool | 0 => [] | n+1 => false::true::true::true::Q n
def ones : Nat → List Bool | 0 => [] | n+1 => true::ones n
def zeros : Nat → List Bool | 0 => [] | n+1 => false::zeros n
def enc : List Bool → List Bool | [] => [] | a::ds => a::a::enc ds

def Reach (a b : HZ) : Prop := ∃ t, hrun table t a = some b

theorem reflR (a : HZ) : Reach a a := ⟨0,rfl⟩
theorem joinR {a b c : HZ} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,hjoin ht hu⟩
theorem exactR {a b : HZ} {t : Nat} (h : hrun table t a = some b) : Reach a b := ⟨t,h⟩

theorem scan (j k : Nat) (R : List Bool) :
    Reach (B (false::Q j) (P k++R)) (B (false::Q (j+k)) R) := by
  induction k generalizing j with
  | zero => exact reflR _
  | succ k ih =>
    have h : hrun table 6 (B (false::Q j) (P (k+1)++R)) = some (B (false::Q (j+1)) (P k++R)) := by rfl
    rw [show j+(k+1)=j+1+k by omega]
    exact joinR (exactR h) (ih (j+1))

theorem scanBlank (k : Nat) (R : List Bool) :
    Reach (B [] (P (k+1)++R)) (B (false::Q (k+1)) R) := by
  have h : hrun table 6 (B [] (P (k+1)++R)) = some (B (false::Q 1) (P k++R)) := by rfl
  have g := scan 1 k R
  rw [show 1+k=k+1 by omega] at g
  exact joinR (exactR h) g

theorem unscan (k : Nat) (R : List Bool) :
    Reach (B (true::true::true::Q k) R) (B [] (P (k+1)++R)) := by
  induction k generalizing R with
  | zero => exact ⟨4,rfl⟩
  | succ k ih =>
    have h : hrun table 4 (B (true::true::true::Q (k+1)) R) = some (B (true::true::true::Q k) (P 1++R)) := by rfl
    have g := ih (P 1++R)
    have he : ∀ n, P n ++ P 1 = P (n+1) := by
      intro n; induction n with
      | zero => rfl
      | succ n ih =>
        change true::true::true::false::(P n ++ P 1) = true::true::true::false::P (n+1)
        rw [ih]
    rw [← List.append_assoc,he] at g
    exact joinR (exactR h) g

def aTail (ds : List Bool) : List Bool := [true,false,false,false,false,false]++enc ds
def bTail (ds : List Bool) : List Bool := [true,false,false,true,true,false,true,false,false,false,true,true]++enc ds
def secA (k : Nat) (ds : List Bool) : HZ := B [] (P (k+2)++aTail ds)
def secB (k : Nat) (ds : List Bool) : HZ := B [] (P (k+1)++bTail ds)

theorem aPrep (k : Nat) (ds : List Bool) :
    hrun table 28 (B (false::Q (k+2)) (aTail ds)) =
    some (B (true::true::true::true::true::Q (k+1)) ([true,false,false,false,true,true]++enc ds)) := by rfl

theorem aTurn (k : Nat) (ds : List Bool) :
    hrun table 6 (B (true::true::true::true::true::Q (k+1)) ([true,false,false,false,true,true]++enc ds)) =
    some (B (true::true::true::Q k) (bTail ds)) := by rfl

theorem aToB (k : Nat) (ds : List Bool) :
    ∃ t, 0<t ∧ hrun table t (secA k ds) = some (secB k ds) := by
  obtain ⟨t,ht⟩ := scanBlank (k+1) (aTail ds)
  obtain ⟨u,hu⟩ := unscan k (bTail ds)
  exact ⟨t+28+6+u,by omega,hjoin (hjoin (hjoin ht (aPrep k ds)) (aTurn k ds)) hu⟩

theorem bPrep (k : Nat) (ds : List Bool) :
    hrun table 28 (B (false::Q (k+1)) (bTail ds)) =
    some (B (false::Q (k+3)) (true::true::true::true::enc ds)) := by rfl

theorem pairUnit (L R : List Bool) :
    hrun table 4 (B (false::L) (true::true::R)) = some (B (false::true::true::L) R) := by rfl

theorem fScan (n : Nat) (L R : List Bool) :
    hrun table n (F (ones n++L) R) = some (F L (zeros n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : hrun table 1 (F (ones (n+1)++L) R) = some (F (ones n++L) (false::R)) := by rfl
    have g := hjoin h (ih (false::R))
    rw [show 1+n=n+1 by omega] at g
    have hz : ∀ j, zeros j ++ false::R = zeros (j+1)++R := by
      intro j; induction j with
      | zero => rfl
      | succ j ih => simp only [zeros,List.cons_append,ih]
    rw [hz] at g
    exact g

theorem carryStep (n : Nat) (L R : List Bool) :
    Reach (B (false::ones (n+1)++false::L) (false::false::R))
          (B L (true::zeros (n+2)++true::true::R)) := by
  have h : hrun table 6 (B (false::ones (n+1)++false::L) (false::false::R)) =
    some (F (ones (n+2)++false::L) (true::true::R)) := by rfl
  have g := fScan (n+2) (false::L) (true::true::R)
  have h' : hrun table 1 (F (false::L) (zeros (n+2)++true::true::R)) =
    some (B L (true::zeros (n+2)++true::true::R)) := by rfl
  exact joinR (exactR h) (joinR (exactR g) (exactR h'))

theorem carryBlank (n : Nat) (L : List Bool) :
    Reach (B (false::ones (n+1)++false::L) [])
          (B L (true::zeros (n+2)++[true,true])) := by
  have h : hrun table 6 (B (false::ones (n+1)++false::L) []) =
    some (F (ones (n+2)++false::L) [true,true]) := by rfl
  have g := fScan (n+2) (false::L) [true,true]
  have h' : hrun table 1 (F (false::L) (zeros (n+2)++[true,true])) =
    some (B L (true::zeros (n+2)++[true,true])) := by rfl
  exact joinR (exactR h) (joinR (exactR g) (exactR h'))

def zbits : Nat → List Bool | 0 => [] | n+1 => false::zbits n

theorem tail_eq (j : Nat) (ds : List Bool) :
    true::zeros (2*j+5)++true::true::enc ds = aTail (zbits j++true::ds) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2*(j+1)+5=2*j+5+2 by omega]
    unfold aTail at *
    simp only [zbits,List.cons_append,enc,zeros] at *
    -- both are equal because adding two zeros to the leading zero run adds one encoded zero.
    exact congrArg (fun xs : List Bool => true::false::false::xs) (List.cons.inj ih).2

def inc : List Bool → List Bool
  | [] => [true]
  | false::ds => true::ds
  | true::ds => false::inc ds

theorem carry (j k : Nat) (ds : List Bool) :
    Reach (B (false::ones (2*j+4)++Q (k+1)) (enc ds))
      (B [] (P (k+1)++aTail (zbits j++inc ds))) := by
  induction ds generalizing j with
  | nil =>
    have h := carryBlank (2*j+3) (true::true::true::Q k)
    rw [show 2*j+3+2=2*j+5 by omega] at h
    have g := unscan k (true::zeros (2*j+5)++[true,true])
    have e : true::zeros (2*j+5)++[true,true] = aTail (zbits j++inc []) := tail_eq j []
    rw [e] at h g
    exact joinR h g
  | cons b ds ih =>
    cases b with
    | false =>
      have h := carryStep (2*j+3) (true::true::true::Q k) (enc ds)
      rw [show 2*j+3+2=2*j+5 by omega] at h
      have g := unscan k (true::zeros (2*j+5)++true::true::enc ds)
      rw [tail_eq] at h g
      exact joinR h g
    | true =>
      have h := pairUnit (ones (2*j+4)++Q (k+1)) (enc ds)
      have e : (true::true::(ones (2*j+4)++Q (k+1))) = ones (2*(j+1)+4)++Q (k+1) := by
        rw [show 2*(j+1)+4=2*j+4+2 by omega]; rfl
      rw [e] at h
      have g := ih (j+1)
      have ez : ∀ n (L : List Bool), zbits (n+1)++L = zbits n++false::L := by
        intro n L; induction n with
        | zero => rfl
        | succ n ih =>
          change false::(zbits (n+1)++L) = false::(zbits n++false::L)
          rw [ih]
      rw [ez] at g
      exact joinR (exactR h) g

theorem bToA (k : Nat) (ds : List Bool) : Reach (secB k ds) (secA (k+1) (inc ds)) := by
  have h := scanBlank k (bTail ds)
  have h1 := exactR (bPrep k ds)
  have h2 := exactR (pairUnit (Q (k+3)) (true::true::enc ds))
  have h3 := exactR (pairUnit (true::true::Q (k+3)) (enc ds))
  have h4 := carry 0 (k+2) ds
  exact joinR h (joinR h1 (joinR h2 (joinR h3 h4)))

theorem growth (k : Nat) (ds : List Bool) :
    ∃ t, 0<t ∧ hrun table t (secA k ds) = some (secA (k+1) (inc ds)) := by
  obtain ⟨t,ht,h⟩ := aToB k ds
  obtain ⟨u,g⟩ := bToA k ds
  exact ⟨t+u,by omega,hjoin h g⟩

theorem root : hrun table 112 ⟨0,[],[]⟩ = some (secA 0 [true]) := by rfl

theorem arbitraryLive (n : Nat) : ∃ t k ds, n≤t ∧ hrun table t ⟨0,[],[]⟩ = some (secA k ds) := by
  induction n with
  | zero => exact ⟨112,0,[true],by omega,root⟩
  | succ n ih =>
    obtain ⟨t,k,ds,ht,h⟩ := ih
    obtain ⟨u,hu,g⟩ := growth k ds
    exact ⟨t+u,k+1,inc ds,by omega,hjoin h g⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,a,ds,hk,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [show embed (HZ.at ⟨0,[],[]⟩ 0) = blank from blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
#print axioms growth
#print axioms arbitraryLive
end BB6.Agent7Raw124ZeroLF1LBM48
