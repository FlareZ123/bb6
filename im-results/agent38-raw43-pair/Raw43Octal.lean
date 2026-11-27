import Raw43Pair
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43Octal
open BB6Coverage BB6Coverage.Agent31Pump

def rename (s : Bool) (q : Fin 6) : Fin 6 :=
  if s then if q = 4 then 5 else if q = 5 then 4 else q else q

def table (v s : Bool) : PartialMachine := fun (q,b) =>
  (BB6.Agent38Raw43Pair.table v (rename s q,b)).map
    (Option.map (fun mv => {mv with next := rename s mv.next}))

def bits (s : String) : List Bool := s.toList.map (fun c => c == '1')
def zeros (n : Nat) : List Bool := List.replicate n false
def ones (n : Nat) : List Bool := List.replicate n true

def blocks (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ blocks w n

theorem blocks_snoc (w : List Bool) (n : Nat) : blocks w n ++ w = w ++ blocks w n := by
  induction n with
  | zero => simp [blocks]
  | succ n ih => simp only [blocks,List.append_assoc,ih]

theorem blocks_add (w : List Bool) (n k : Nat) : blocks w (n+k) = blocks w n ++ blocks w k := by
  induction n with
  | zero => simp [blocks]
  | succ n ih => rw [show n+1+k=n+k+1 by omega]; simp only [blocks,ih,List.append_assoc]

def P := bits "1110"
def Q := bits "1100"
def front (k : Nat) (W : List Bool) : Z0 := ⟨0,[],zeros 8 ++ blocks Q k ++ W⟩
def scan (q : Fin 6) (L W : List Bool) : Z0 := ⟨q,W.headD false::L,W.tail⟩
def carry (n : Nat) (L W : List Bool) : Z0 :=
  scan 1 (bits "00" ++ ones 21 ++ ones n ++ [false] ++ L) W

def low : Nat → List Bool
  | 0 => bits "000000000000000000"
  | 1 => bits "11110000000000000000"
  | 2 => bits "001101111000000000"
  | 3 => bits "11111101111000000000"
  | 4 => bits "000000001100000000"
  | 5 => bits "11110000001100000000"
  | 6 => bits "001101100000011110"
  | 7 => bits "11111101100000011110"
  | 8 => bits "000000000011000011"
  | 9 => bits "11110000000011000011"
  | 10 => bits "001101111011000011"
  | 11 => bits "11111101111011000011"
  | 12 => bits "000000001111000011"
  | 13 => bits "11110000001111000011"
  | 14 => bits "001101100001100011"
  | _ => bits "11111101100001100011"

def digit : Nat → List Bool
  | 0 => bits "0000000000000000"
  | 1 => bits "1101111000000000"
  | 2 => bits "0000001100000000"
  | 3 => bits "1101100000011110"
  | 4 => bits "0000000011000011"
  | 5 => bits "1101111011000011"
  | 6 => bits "0000001111000011"
  | _ => bits "1101100001100011"

def encode : List (Fin 8) → List Bool
  | [] => []
  | d::ds => digit d.val ++ encode ds

theorem encode_append (xs ys : List (Fin 8)) : encode (xs++ys) = encode xs ++ encode ys := by
  induction xs with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append,encode,ih,List.append_assoc]

def lowCost (v : Bool) : Nat → Nat
  | 1 | 9 => 73
  | 3 | 11 => 67
  | 5 => if v then 115 else 117
  | 7 => if v then 109 else 111
  | 13 => 91
  | _ => 21

def digitCost (v : Bool) : Nat → Nat
  | 0 | 4 => 70
  | 1 | 5 => 64
  | 2 => if v then 112 else 114
  | 3 => if v then 106 else 108
  | _ => 88

theorem odd_entry (v s : Bool) (W : List Bool) :
    run0 (table v s) 11 ⟨0,[],zeros 8++W⟩ = some ⟨0,[],bits "001100000"++W⟩ := by cases v <;> cases s <;> rfl

theorem scan_entry (v s : Bool) (W : List Bool) :
    run0 (table v s) (if v then 26 else 28) ⟨0,[],bits "001100000"++W⟩ =
      some (scan 2 (P++ones 6) W) := by cases v <;> cases s <;> cases W <;> rfl

theorem scan_one (v s : Bool) (L W : List Bool) :
    run0 (table v s) 4 (scan 2 L (Q++W)) = some (scan 2 (P++L) W) := by cases v <;> cases s <;> cases W <;> rfl

theorem scan_many (v s : Bool) (k : Nat) (L W : List Bool) :
    run0 (table v s) (4*k) (scan 2 L (blocks Q k++W)) =
      some (scan 2 (blocks P k++L) W) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h1 := scan_one v s L (blocks Q k++W)
    have h2 := ih (P++L)
    have h := join0 h1 h2
    rw [Nat.mul_succ,Nat.add_comm (4*k) 4]
    simpa only [blocks,List.append_assoc,← List.append_assoc (blocks P k) P L,blocks_snoc P k] using h

theorem prepare (v s : Bool) (k : Nat) (W : List Bool) :
    run0 (table v s) (11+(if v then 26 else 28)+4*k) (front k W) =
      some (scan 2 (P++(blocks P k++ones 6)) W) := by
  have h1 := odd_entry v s (blocks Q k++W)
  have h2 := scan_entry v s (blocks Q k++W)
  have h3 := scan_many v s k (P++ones 6) W
  have h := join0 (join0 h1 h2) h3
  simpa only [front,List.append_assoc,← List.append_assoc (blocks P k) P (ones 6),blocks_snoc P k] using h

theorem unwind_one (v s : Bool) (L R : List Bool) :
    run0 (table v s) 14 ⟨0,P++L,bits "00"++R⟩ = some ⟨0,L,bits "00"++Q++R⟩ := by cases v <;> cases s <;> rfl

theorem unwind_many (v s : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v s) (14*k) ⟨0,blocks P k++L,bits "00"++R⟩ =
      some ⟨0,L,bits "00"++blocks Q k++R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h1 := unwind_one v s (blocks P k++L) R
    have h2 := ih (Q++R)
    have h := join0 (by simpa only [List.append_assoc] using h1) h2
    rw [Nat.mul_succ,Nat.add_comm (14*k) 14]
    simpa only [blocks,List.append_assoc,← List.append_assoc (blocks Q k) Q R,blocks_snoc Q k] using h

theorem unwind_end (v s : Bool) (R : List Bool) :
    run0 (table v s) 6 ⟨0,ones 6,bits "00"++R⟩ = some ⟨0,[],zeros 8++R⟩ := by cases v <;> cases s <;> rfl

theorem low_local (v s : Bool) (r : Nat) (hr : r<15) (L U : List Bool) :
    run0 (table v s) (lowCost v r) (scan 2 (P++L) (low r++U)) =
      some ⟨0,L,bits "00"++blocks Q (r%2)++low (r+1)++U⟩ := by
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 ∨ r=8 ∨ r=9 ∨ r=10 ∨ r=11 ∨ r=12 ∨ r=13 ∨ r=14 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;> cases v <;> cases s <;> rfl

theorem carry_entry (v s : Bool) (L U : List Bool) :
    run0 (table v s) (if v then 78 else 82) (scan 2 (P++L) (low 15++U)) =
      some (carry 0 L U) := by cases v <;> cases s <;> cases U <;> rfl

theorem carry_seven (v s : Bool) (n : Nat) (L U : List Bool) :
    run0 (table v s) (if v then 70 else 74) (carry n L (digit 7++U)) =
      some (carry (n+16) L U) := by
  have h : run0 (table v s) (if v then 70 else 74) (carry n L (digit 7++U)) =
      some (scan 1 (bits "00"++ones 37++ones n++[false]++L) U) := by
    cases v <;> cases s <;> cases U <;> rfl
  simpa only [carry,ones,List.append_assoc,← List.append_assoc (bits "00") (List.replicate 37 true) _,
    ← List.append_assoc (bits "00") (List.replicate 21 true) _,
    ← List.append_assoc (List.replicate 37 true) (List.replicate n true) _,
    ← List.append_assoc (List.replicate 21 true) (List.replicate (n+16) true) _,
    List.replicate_append_replicate,show 37+n=21+(n+16) by omega] using h

theorem digit_local (v s : Bool) (r : Nat) (hr : r<7) (n : Nat) (L U : List Bool) :
    run0 (table v s) (digitCost v r) (carry n L (digit r++U)) =
      some ⟨0,ones n++false::L,zeros 23++digit (r+1)++U⟩ := by
  have h : r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 := by omega
  rcases h with h|h|h|h|h|h|h <;> subst r <;> cases v <;> cases s <;> simp only [carry,scan,List.append_assoc] <;> rfl

theorem erase_ones (v s : Bool) (n : Nat) (L R : List Bool) :
    run0 (table v s) n ⟨0,ones n++L,R⟩ = some ⟨0,L,zeros n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 : run0 (table v s) 1 ⟨0,true::(ones n++L),R⟩ = some ⟨0,ones n++L,false::R⟩ := by cases v <;> cases s <;> rfl
    have h := join0 h1 (ih (false::R))
    rw [Nat.add_comm 1 n] at h
    have hr : zeros n ++ false::R = zeros (n+1) ++ R := by
      rw [zeros,zeros,List.replicate_succ',List.append_assoc]; rfl
    rw [hr] at h
    simpa only [ones,List.replicate_succ,List.cons_append] using h

theorem finish_carry (v s : Bool) (L R : List Bool) :
    run0 (table v s) 11 ⟨0,false::L,zeros 5++R⟩ = some ⟨0,L,bits "001100"++R⟩ := by cases v <;> cases s <;> rfl

theorem digit_finish (v s : Bool) (r : Nat) (hr : r<7) (n : Nat) (L U : List Bool) :
    run0 (table v s) (digitCost v r+n+11) (carry n L (digit r++U)) =
      some ⟨0,L,bits "001100"++zeros (18+n)++digit (r+1)++U⟩ := by
  have h1 := digit_local v s r hr n L U
  have h2 := erase_ones v s n (false::L) (zeros 23++digit (r+1)++U)
  have h := join0 h1 h2
  have he : zeros n++(zeros 23++digit (r+1)++U) = zeros 5++(zeros (18+n)++digit (r+1)++U) := by
    simp only [zeros,← List.append_assoc,List.replicate_append_replicate,show n+23=5+(18+n) by omega]
  rw [he] at h
  have h3 := finish_carry v s L (zeros (18+n)++digit (r+1)++U)
  simpa only [List.append_assoc] using join0 h h3

/-- A high zero digit guarantees that carry terminates. Each leading seven
    becomes a zero digit by adding sixteen cells to the unary carry run. -/
theorem carry_with_zero (v s : Bool) (ds : List (Fin 8)) (n : Nat) (L R : List Bool) :
    ∃ t ds', 0<t ∧ run0 (table v s) t (carry n L (encode ds++digit 0++R)) =
      some ⟨0,L,bits "001100"++zeros (18+n)++encode ds'++R⟩ := by
  induction ds generalizing n with
  | nil =>
    refine ⟨digitCost v 0+n+11,[1],by omega,?_⟩
    simpa only [encode,List.nil_append,List.append_nil,List.append_assoc,show (1 : Fin 8).val=1 by decide] using digit_finish v s 0 (by decide) n L R
  | cons d ds ih =>
    by_cases h : d.val=7
    · have h1 := carry_seven v s n L (encode ds++digit 0++R)
      obtain ⟨t,ds',ht,h2⟩ := ih (n+16)
      have H := join0 h1 h2
      refine ⟨(if v then 70 else 74)+t,0::ds',by omega,?_⟩
      have he : zeros (18+(n+16)) = zeros (18+n)++digit 0 := by
        change List.replicate (18+(n+16)) false = List.replicate (18+n) false ++ List.replicate 16 false
        rw [List.replicate_append_replicate]; congr 1 <;> omega
      rw [he] at H
      simpa only [encode,h,List.append_assoc,show (0 : Fin 8).val=0 by decide] using H
    · have hr : d.val<7 := by have := d.isLt; omega
      have h1 := digit_finish v s d.val hr n L (encode ds++digit 0++R)
      refine ⟨digitCost v d.val+n+11,⟨d.val+1,by omega⟩::(ds++[0]),by omega,?_⟩
      simpa only [encode,encode_append,List.append_nil,List.append_assoc,show (0 : Fin 8).val=0 by decide] using h1

theorem low_epoch (v s : Bool) (k r : Nat) (hr : r<15) (U : List Bool) :
    ∃ t, 0<t ∧ run0 (table v s) t (front k (low r++U)) =
      some (front (k+r%2) (low (r+1)++U)) := by
  have h1 := prepare v s k (low r++U)
  have h2 := low_local v s r hr (blocks P k++ones 6) U
  have h3 := unwind_many v s k (ones 6) (blocks Q (r%2)++low (r+1)++U)
  have h4 := unwind_end v s (blocks Q k++blocks Q (r%2)++low (r+1)++U)
  have H12 := join0 h1 h2
  have H123 := join0 H12 (by simpa only [List.append_assoc] using h3)
  have H := join0 H123 (by simpa only [List.append_assoc] using h4)
  refine ⟨11+(if v then 26 else 28)+4*k+lowCost v r+14*k+6,by omega,?_⟩
  simpa only [front,blocks_add,List.append_assoc] using H

theorem carry_epoch (v s : Bool) (k : Nat) (ds : List (Fin 8)) (R : List Bool) :
    ∃ t ds', 0<t ∧ run0 (table v s) t (front k (low 15++encode ds++digit 0++R)) =
      some (front (k+1) (low 0++encode ds'++R)) := by
  have h1 := prepare v s k (low 15++encode ds++digit 0++R)
  have h2 := carry_entry v s (blocks P k++ones 6) (encode ds++digit 0++R)
  have H12 := join0 h1 (by simpa only [List.append_assoc] using h2)
  obtain ⟨t,ds',ht,h3⟩ := carry_with_zero v s ds 0 (blocks P k++ones 6) R
  have H123 := join0 H12 (by simpa only [List.append_assoc] using h3)
  have h4 := unwind_many v s k (ones 6) (Q++low 0++encode ds'++R)
  have H1234 := join0 H123 (by simpa only [List.append_assoc,show bits "001100"=bits "00"++Q by rfl,show zeros (18+0)=low 0 by rfl] using h4)
  have h5 := unwind_end v s (blocks Q k++Q++low 0++encode ds'++R)
  have H := join0 H1234 (by simpa only [List.append_assoc] using h5)
  refine ⟨11+(if v then 26 else 28)+4*k+(if v then 78 else 82)+t+14*k+6,ds',by omega,?_⟩
  simpa only [front,blocks,List.append_assoc,← List.append_assoc (blocks Q k) Q _,blocks_snoc Q k] using H

/-- N positive-cost frontier epochs from a finite word padded with N zero
    digits. The proof never relies on a simulated cutoff. At each epoch at
    most one reserved zero digit is incorporated into the active word. -/
theorem epochs (v s : Bool) (N k r : Nat) (hr : r<16) (ds : List (Fin 8)) :
    ∃ t z, N≤t ∧ run0 (table v s) t (front k (low r++encode ds++zeros (16*N))) = some z := by
  induction N generalizing k r ds with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hpad : zeros (16*(N+1)) = digit 0++zeros (16*N) := by
      change List.replicate (16*(N+1)) false = List.replicate 16 false ++ List.replicate (16*N) false
      rw [List.replicate_append_replicate]; congr 1 <;> omega
    by_cases h : r<15
    · obtain ⟨a,ha,h1⟩ := low_epoch v s k r h (encode (ds++[0])++zeros (16*N))
      obtain ⟨b,z,hb,h2⟩ := ih (k+r%2) (r+1) (by omega) (ds++[0])
      have H := join0 h1 (by simpa only [List.append_assoc] using h2)
      refine ⟨a+b,z,by omega,?_⟩
      simpa only [hpad,encode_append,encode,List.append_nil,List.append_assoc,show (0 : Fin 8).val=0 by decide] using H
    · have he : r=15 := by omega
      subst r
      obtain ⟨a,ds',ha,h1⟩ := carry_epoch v s k ds (zeros (16*N))
      obtain ⟨b,z,hb,h2⟩ := ih (k+1) 0 (by decide) ds'
      have H := join0 h1 h2
      exact ⟨a+b,z,by omega,by simpa only [hpad,List.append_assoc] using H⟩

theorem padded_live (v s : Bool) (N : Nat) :
    ∃ t z, N≤t ∧ run0 (table v s) t ⟨0,[],zeros (26+16*N)⟩ = some z := by
  obtain ⟨t,z,ht,h⟩ := epochs v s N 0 0 (by decide) []
  refine ⟨t,z,ht,?_⟩
  change run0 (table v s) t ⟨0,[],List.replicate (26+16*N) false⟩ = some z
  have h' : run0 (table v s) t ⟨0,[],List.replicate 8 false++List.replicate 18 false++List.replicate (16*N) false⟩ = some z := h
  simpa only [List.replicate_append_replicate] using h'

#print axioms padded_live

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

/-- All completions of all four literal one-hole tables are nonhalting. -/
theorem never (v s : Bool) (m : Machine) (hm : compatible (table v s) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live v s n
  let start : Z := ⟨0,0,[],zeros (26+16*n)⟩
  have hz : (zrun (table v s) t start).map project = some z :=
    (run_project (table v s) t start).trans hr
  cases hZ : zrun (table v s) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v s) m hm t start z' hZ
    have hb : embed start = blank := padded_blank _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43Octal
