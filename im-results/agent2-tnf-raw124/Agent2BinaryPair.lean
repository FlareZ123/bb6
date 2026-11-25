import BlockPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent2BinaryPair
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

/-- The two raw124/F1=1LA leaves, 1254 (false) and 2919 (true). -/
def p (b : Bool) : PartialMachine := fun s =>
  ([some (some ⟨true,true,1⟩),some (some ⟨true,b,if b then 4 else 0⟩),
    some (some ⟨true,true,2⟩),some (some ⟨false,true,4⟩),
    some (some ⟨false,true,3⟩),none,
    some (some ⟨true,false,3⟩),some (some ⟨true,true,4⟩),
    some (some ⟨false,true,1⟩),some (some ⟨true,false,5⟩),
    some (some ⟨false,false,5⟩),some (some ⟨true,false,0⟩)] : List (Option (Option Move)))[2*s.1.val+s.2.toNat]?.getD none

def E (l r : List Bool) : HZ := ⟨4,l,r⟩
def F (l r : List Bool) : HZ := ⟨5,l,r⟩
def P := bits "1101101001"
def z4 := bits "0000"
def sect (t : Nat) (w r : List Bool) : HZ :=
  E (bits "1" ++ rep z4 t ++ bits "00000000000" ++ P ++ w) r

def Reach (b : Bool) (a c : HZ) : Prop := ∃ n, hrun (p b) n a = some c
def Pos (b : Bool) (a c : HZ) : Prop := ∃ n, 0 < n ∧ hrun (p b) n a = some c
theorem Reach.trans {b : Bool} {a c d : HZ} : Reach b a c → Reach b c d → Reach b a d := by
  rintro ⟨n,h⟩ ⟨m,g⟩; exact ⟨n+m,hjoin h g⟩
theorem Pos.trans {b : Bool} {a c d : HZ} : Pos b a c → Reach b c d → Pos b a d := by
  rintro ⟨n,hn,h⟩ ⟨m,g⟩; exact ⟨n+m,by omega,hjoin h g⟩
theorem Pos.reach {b : Bool} {a c : HZ} : Pos b a c → Reach b a c := by
  rintro ⟨n,_,h⟩; exact ⟨n,h⟩
theorem framed {b : Bool} {n : Nat} {a c : HZ}
    (hn : 0<n) (h : openRun (p b) false false n a = some c) (L R : List Bool) :
    Pos b (tail a L R) (tail c L R) :=
  ⟨n,hn,openRun_sound _ _ _ _ _ _ L R (by simp) (by simp) h⟩

theorem rep_add (w : List Bool) (a b : Nat) : rep w (a+b) = rep w a ++ rep w b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega,rep,rep,ih,List.append_assoc]
theorem rep_double (w : List Bool) (n : Nat) : rep (w++w) n = rep w (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add]
    simp [rep]

theorem enterF (b : Bool) (L R : List Bool) : Pos b (E (bits "1"++L) R) (F L (bits "1"++R)) := by
  have h : openRun (p b) false false 1 (E (bits "1") []) = some (F [] (bits "1")) := by cases b <;> decide
  exact framed (by decide) h L R

theorem scanF (b : Bool) (t : Nat) (L R : List Bool) :
    Reach b (F (rep z4 t ++ L) R) (F L (rep z4 t ++ R)) := by
  have h : openRun (p b) false false 4 (F z4 []) = some (F [] z4) := by cases b <;> decide
  exact ⟨4*t,sweepL (p b) 5 [] z4 [] z4 4 h t L R⟩

theorem front (b : Bool) (L R : List Bool) :
    Pos b (F (bits "00000000000" ++ P ++ L) R)
      (E (bits "10000011" ++ L) (bits "0100000000000" ++ R)) := by
  have h : openRun (p b) false false (if b then 45 else 37) (F (bits "00000000000"++P) []) =
      some (E (bits "10000011") (bits "0100000000000")) := by cases b <;> decide
  simpa only [tail,F,E,List.append_assoc,List.nil_append] using framed (by cases b <;> decide) h L R

theorem start (b : Bool) (t : Nat) (W R : List Bool) :
    Pos b (sect t W R)
      (E (bits "10000011" ++ W) (bits "0100000000000" ++ rep z4 t ++ bits "1" ++ R)) := by
  have h := enterF b (rep z4 t ++ bits "00000000000" ++ P ++ W) R
  have g := scanF b t (bits "00000000000" ++ P ++ W) (bits "1"++R)
  have k := front b W (rep z4 t ++ bits "1" ++ R)
  simp only [sect,List.append_assoc] at h g k ⊢
  exact h.trans (g.trans k.reach)

theorem carryInit (b : Bool) (L R : List Bool) :
    Pos b (E (bits "100000110"++L) R) (E (bits "101"++L) (bits "000001"++R)) := by
  have h : openRun (p b) false false (if b then 12 else 10) (E (bits "100000110") []) = some (E (bits "101") (bits "000001")) := by cases b <;> decide
  exact framed (by cases b <;> decide) h L R

theorem carrySweep (b : Bool) (i : Nat) (L R : List Bool) :
    Reach b (E (bits "101"++rep (bits "10") i++L) R)
      (E (bits "101"++L) (rep (bits "01") i++R)) := by
  have h : openRun (p b) false false (if b then 8 else 6) (E (bits "10110") []) = some (E (bits "101") (bits "01")) := by cases b <;> decide
  exact ⟨_,sweepL (p b) 4 (bits "101") (bits "10") [] (bits "01") _ h i L R⟩

theorem carryExit (b : Bool) (L R : List Bool) :
    Pos b (E (bits "1010"++L) R) (E (bits "001"++L) (bits "1"++R)) := by
  have h : openRun (p b) false false 5 (E (bits "1010") []) = some (E (bits "001") (bits "1")) := by cases b <;> decide
  exact framed (by decide) h L R

theorem sweep10 (b : Bool) (i : Nat) (L R : List Bool) :
    Reach b (E (bits "0"++L) (rep (bits "10") i++R))
      (E (bits "0"++rep (bits "00") i++L) R) := by
  have h : openRun (p b) false false 2 (E (bits "0") (bits "10")) = some (E (bits "000") []) := by cases b <;> decide
  exact ⟨_,sweepR (p b) 4 [] (bits "10") (bits "0") (bits "00") 2 h i L R⟩

theorem carry (b : Bool) (i : Nat) (U R : List Bool) :
    Pos b (E (bits "10000011"++rep (bits "01") i++bits "00"++U) R)
      (E (bits "000"++rep (bits "00") i++bits "01"++U) (bits "00001"++R)) := by
  have hl : rep (bits "01") i ++ bits "0" = bits "0" ++ rep (bits "10") i := rep_intertwine (bits "0") (bits "01") (bits "10") rfl i
  have hr : rep (bits "10") i ++ bits "1" = bits "1" ++ rep (bits "01") i := rep_intertwine (bits "1") (bits "10") (bits "01") rfl i
  have h := carryInit b (rep (bits "10") i++bits "0"++U) R
  have g := carrySweep b i (bits "0"++U) (bits "000001"++R)
  have k := carryExit b U (rep (bits "01") i++bits "000001"++R)
  have j := sweep10 b (i+1) (bits "01"++U) (bits "00001"++R)
  have h0 : E (bits "10000011"++rep (bits "01") i++bits "00"++U) R =
      E (bits "100000110"++rep (bits "10") i++bits "0"++U) R := by
    congr 1
    rw [show bits "00" = bits "0"++bits "0" by rfl]
    simp only [List.append_assoc]
    rw [← List.append_assoc (rep (bits "01") i) (bits "0") (bits "0"++U),hl]
    simp only [List.append_assoc]
    rfl
  have hg : E (bits "001"++U) (bits "1"++(rep (bits "01") i++bits "000001"++R)) =
      E (bits "0"++(bits "01"++U)) (rep (bits "10") (i+1)++(bits "00001"++R)) := by
    congr 1
    rw [show bits "000001" = bits "0"++bits "00001" by rfl]
    simp only [List.append_assoc,← List.append_assoc (bits "1") (rep (bits "01") i),← hr]
    rw [← List.append_assoc (bits "1") (bits "0") (bits "00001"++R),show bits "1"++bits "0" = bits "10" by rfl, ← List.append_assoc,rep_snoc]
    rfl
  rw [h0]
  have h' : Pos b (E (bits "100000110"++rep (bits "10") i++bits "0"++U) R)
      (E (bits "001"++U) (bits "1"++(rep (bits "01") i++bits "000001"++R))) := by
    simp only [List.append_assoc] at h g k ⊢
    exact h.trans (g.trans k.reach)
  rw [hg] at h'
  have j' := h'.trans j
  have hb : bits "0"++bits "00" = bits "000" := rfl
  simpa only [rep,← List.append_assoc,hb] using j'

theorem middle (b : Bool) (W R : List Bool) :
    Pos b (E (bits "000"++W) (bits "000010100000000000"++R))
      (E (bits "00101101001"++W) (bits "0010001000"++R)) := by
  have h : openRun (p b) false false (if b then 142 else 136)
      (E (bits "000") (bits "000010100000000000")) = some (E (bits "00101101001") (bits "0010001000")) := by cases b <;> decide
  exact framed (by cases b <;> decide) h W R

theorem frontCarry (b : Bool) (t i : Nat) (U R : List Bool) :
    Pos b (sect t (rep (bits "01") i++bits "00"++U) R)
      (E (bits "00101101001"++rep (bits "00") i++bits "01"++U)
        (bits "0010001000"++rep z4 t++bits "1"++R)) := by
  have h := start b t (rep (bits "01") i++bits "00"++U) R
  have g := carry b i U (bits "0100000000000"++rep z4 t++bits "1"++R)
  have k := middle b (rep (bits "00") i++bits "01"++U) (rep z4 t++bits "1"++R)
  simp only [List.append_assoc] at h g k ⊢
  exact h.trans (g.reach.trans k.reach)

theorem sweep0010 (b : Bool) (k : Nat) (L R : List Bool) :
    Reach b (E (bits "0"++L) (rep (bits "0010") k++R))
      (E (bits "0"++rep (bits "1010") k++L) R) := by
  have h : openRun (p b) false false 4 (E (bits "0") (bits "0010")) = some (E (bits "01010") []) := by cases b <;> decide
  exact ⟨_,sweepR (p b) 4 [] (bits "0010") (bits "0") (bits "1010") 4 h k L R⟩

theorem right000 (b : Bool) (L R : List Bool) :
    Pos b (E (bits "0"++L) (bits "000"++R)) (E (bits "101"++L) (bits "1"++R)) := by
  have h : openRun (p b) false false 10 (E (bits "0") (bits "000")) = some (E (bits "101") (bits "1")) := by cases b <;> decide
  exact framed (by decide) h L R

theorem right11 (b : Bool) (L R : List Bool) :
    Pos b (E (bits "0"++L) (bits "11"++R)) (E (bits "100"++L) R) := by
  have h : openRun (p b) false false 2 (E (bits "0") (bits "11")) = some (E (bits "100") []) := by cases b <;> decide
  exact framed (by decide) h L R

theorem exitPhase (b : Bool) (k : Nat) (W V : List Bool) :
    Reach b (E (bits "00101101001"++W) (rep (bits "0010") k++bits "000"++V))
      (E (bits "1"++rep z4 k++bits "000"++P++W) V) := by
  have h := sweep0010 b k (bits "0101101001"++W) (bits "000"++V)
  have g := right000 b (rep (bits "1010") k++bits "0101101001"++W) V
  have j := carrySweep b (2*k) (bits "0101101001"++W) (bits "1"++V)
  have l := carryExit b (bits "101101001"++W) (rep (bits "01") (2*k)++bits "1"++V)
  have m := sweep10 b (2*k) (bits "0"++P++W) (bits "11"++V)
  have f := right11 b (rep (bits "00") (2*k)++bits "0"++P++W) V
  have hd : rep (bits "1010") k = rep (bits "10") (2*k) := rep_double (bits "10") k
  have hz : rep z4 k = rep (bits "00") (2*k) := rep_double (bits "00") k
  have hr : bits "1" ++ rep (bits "01") (2*k) = rep (bits "10") (2*k) ++ bits "1" := (rep_intertwine (bits "1") (bits "10") (bits "01") rfl (2*k)).symm
  simp only [List.append_assoc] at h g j l m f
  have hgl := h.trans g.reach
  rw [hd] at hgl
  have hj := hgl.trans j
  have hl := hj.trans l.reach
  have he : bits "1" ++ (rep (bits "01") (2*k)++(bits "1"++V)) = rep (bits "10") (2*k)++(bits "11"++V) := by
    rw [← List.append_assoc (bits "1") (rep (bits "01") (2*k)) (bits "1"++V),hr]
    simp only [List.append_assoc]
    rfl
  rw [he] at hl
  have hm := hl.trans m
  have hf := hm.trans f.reach
  rw [hz]
  have he' : bits "100" ++ (rep (bits "00") (2*k)++bits "0"++P++W) = bits "1"++rep (bits "00") (2*k)++bits "000"++P++W := by
    rw [show bits "100" = bits "1"++bits "00" by rfl, show bits "000" = bits "00"++bits "0" by rfl]
    simp only [List.append_assoc,← List.append_assoc (bits "00") (rep (bits "00") (2*k)),← rep_snoc]
  simp only [List.append_assoc] at he' ⊢
  rw [← he']
  exact hf

theorem epochSucc (b : Bool) (s i : Nat) (U R : List Bool) :
    Pos b (sect (s+1) (rep (bits "01") i++bits "00"++U) R)
      (sect 0 (rep (bits "00") i++bits "01"++U) (rep z4 s++bits "0001"++R)) := by
  have h := frontCarry b (s+1) i U R
  have g := exitPhase b 2 (rep (bits "00") i++bits "01"++U) (rep z4 s++bits "0001"++R)
  have hr : bits "0010001000"++rep z4 (s+1)++bits "1"++R =
      rep (bits "0010") 2++bits "000"++(rep z4 s++bits "0001"++R) := by
    rw [rep,← rep_snoc]
    simp only [List.append_assoc]
    change bits "0010001000" ++ (rep z4 s ++ (bits "0" ++ (bits "0001"++R))) = _
    rw [← List.append_assoc (rep z4 s) (bits "0"),rep_intertwine (bits "0") z4 z4 rfl s]
    simp only [List.append_assoc]
    rfl
  -- Move the last zero block after the repeated frame.
  rw [hr] at h
  exact h.trans g

theorem epochZero (b : Bool) (i j : Nat) (U V : List Bool) :
    Pos b (sect 0 (rep (bits "01") i++bits "00"++U) (rep (bits "0001") j++z4++V))
      (sect (j+1) (rep (bits "00") i++bits "01"++U) V) := by
  have h := frontCarry b 0 i U (rep (bits "0001") j++z4++V)
  have g := exitPhase b (j+3) (rep (bits "00") i++bits "01"++U) V
  have hcomm := rep_intertwine (bits "001") (bits "0010") (bits "0001") rfl j
  have hr : bits "0010001000"++rep z4 0++bits "1"++(rep (bits "0001") j++z4++V) =
      rep (bits "0010") (j+3)++bits "000"++V := by
    rw [show j+3=3+j by omega,rep_add]
    simp only [rep,List.nil_append,List.append_assoc]
    -- Normalize only the constant prefix and the suffix of the commutation.
    change bits "00100010" ++ (bits "001" ++ (rep (bits "0001") j ++ (z4++V))) = _
    rw [← List.append_assoc (bits "001") (rep (bits "0001") j),← hcomm]
    simp only [List.append_assoc]
    change bits "00100010" ++ (rep (bits "0010") j ++ (bits "0010" ++ (bits "000" ++ V))) = _
    rw [← List.append_assoc (rep (bits "0010") j),rep_snoc]
    simp only [List.append_assoc]
    rfl
  rw [hr] at h
  have hg := h.trans g
  have he : rep z4 (j+3)++bits "000" = rep z4 (j+1)++bits "00000000000" := by
    rw [show j+3=(j+1)+2 by omega,rep_add,List.append_assoc]
    rfl
  simp only [sect,List.append_assoc] at hg ⊢
  have he2 := congrArg (fun l => l ++ (P ++ (rep (bits "00") i ++ (bits "01" ++ U)))) he
  simp only [List.append_assoc] at he2
  rw [← he2]
  exact hg

#print axioms epochSucc
#print axioms epochZero

def enc (z o : List Bool) : List Bool → List Bool
  | [] => []
  | b::bs => (if b then o else z) ++ enc z o bs

theorem enc_append (z o a b : List Bool) : enc z o (a++b) = enc z o a ++ enc z o b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [enc,ih,List.append_assoc]
theorem enc_ones (z o : List Bool) (n : Nat) : enc z o (List.replicate n true) = rep o n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,enc,rep,ih]
theorem enc_zeros (z o : List Bool) (n : Nat) : enc z o (List.replicate n false) = rep z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,enc,rep,ih]
theorem split_digit (w : List Bool) : ∃ i u, w++[false] = List.replicate i true ++ false::u := by
  induction w with
  | nil => exact ⟨0,[],rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0,bs++[false],rfl⟩
    | true => obtain ⟨i,u,h⟩ := ih; exact ⟨i+1,u,by simp [List.replicate_succ,h]⟩

def e2 := enc (bits "00") (bits "01")
def e4 := enc z4 (bits "0001")

theorem getD_zeros (l : List Bool) (n k : Nat) :
    (l ++ List.replicate k false).getD n false = l.getD n false := by
  induction l generalizing n with
  | nil => simp [List.getD_eq_getElem?_getD,List.getElem?_replicate]; split <;> rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [List.cons_append,List.getD_cons_succ] using ih n

theorem pad_embed (a : HZ) (h : Int) (k j : Nat) :
    embed ((tail a (List.replicate k false) (List.replicate j false)).at h) = embed (a.at h) := by
  unfold embed HZ.at tail
  congr 1
  funext x
  simp only [atCell,getD_zeros]

def inv (c : Config) : Prop := ∃ t w r h, c = embed ((sect t (e2 w) (e4 r)).at h)

theorem inv_next (b : Bool) (m : Machine) (hm : compatible (p b) m) (c : Config) (hc : inv c) :
    ∃ n d, 0 < n ∧ run m n c = some d ∧ inv d := by
  obtain ⟨t,w,r,h,rfl⟩ := hc
  obtain ⟨i,u,hw⟩ := split_digit w
  have hL : e2 (w++[false]) = rep (bits "01") i ++ bits "00" ++ e2 u := by
    rw [hw]; simp [e2,enc_append,enc_ones,enc,List.append_assoc]
  have hL' : e2 (List.replicate i false ++ true::u) = rep (bits "00") i ++ bits "01" ++ e2 u := by
    simp [e2,enc_append,enc_zeros,enc,List.append_assoc]
  let w' := List.replicate i false ++ true::u
  have hp : embed ((sect t (e2 (w++[false])) (e4 (r++[false]))).at h) =
      embed ((sect t (e2 w) (e4 r)).at h) := by
    have h1 : e2 (w++[false]) = e2 w ++ List.replicate 2 false := by simp [e2,enc_append,enc]; rfl
    have h2 : e4 (r++[false]) = e4 r ++ List.replicate 4 false := by simp [e4,enc_append,enc]; rfl
    rw [h1,h2]
    simpa only [sect,E,tail,List.append_assoc] using pad_embed (sect t (e2 w) (e4 r)) h 2 4
  have H : ∃ t' r', Pos b (sect t (e2 (w++[false])) (e4 (r++[false]))) (sect t' (e2 w') (e4 r')) := by
    cases t with
    | zero =>
      obtain ⟨j,v,hv⟩ := split_digit r
      have hr : e4 (r++[false]) = rep (bits "0001") j ++ z4 ++ e4 v := by
        rw [hv]; simp [e4,enc_append,enc_ones,enc,List.append_assoc]
      exact ⟨j+1,v,by simpa only [hL,hr,w',hL'] using epochZero b i j (e2 u) (e4 v)⟩
    | succ s =>
      have hr : e4 (List.replicate s false ++ true::(r++[false])) = rep z4 s ++ bits "0001" ++ e4 (r++[false]) := by
        simp [e4,enc_append,enc_zeros,enc,List.append_assoc]
      exact ⟨0,List.replicate s false ++ true::(r++[false]),by simpa only [hL,w',hL',hr] using epochSucc b s i (e2 u) (e4 (r++[false]))⟩
  obtain ⟨t',r',n,hn,hrun'⟩ := H
  obtain ⟨h',hz⟩ := hrun_sound (p b) n _ _ h hrun'
  have Hraw := zrun_sound (p b) m hm n _ _ hz
  rw [hp] at Hraw
  exact ⟨n,_,hn,Hraw,⟨t',w',r',h',rfl⟩⟩

theorem entry (b : Bool) : hrun (p b) (if b then 485 else 441) ⟨0,[],[]⟩ = some (sect 1 (e2 []) (e4 [])) := by cases b <;> decide

theorem never (b : Bool) (m : Machine) (hm : compatible (p b) m) : NeverHalts m := by
  have H : ∀ k : Nat, ∃ n c, k ≤ n ∧ run m n blank = some c ∧ inv c := by
    intro k
    induction k with
    | zero =>
      obtain ⟨h',hz⟩ := hrun_sound (p b) _ _ _ 0 (entry b)
      have Hraw := zrun_sound (p b) m hm _ _ _ hz
      rw [blank_embed] at Hraw
      exact ⟨_,_,Nat.zero_le _,Hraw,⟨1,[],[],h',rfl⟩⟩
    | succ k ih =>
      obtain ⟨n,c,hn,hc,hi⟩ := ih
      obtain ⟨t,d,ht,hd,hid⟩ := inv_next b m hm c hi
      exact ⟨n+t,d,by omega,by rw [run_append,hc]; exact hd,hid⟩
  intro n
  obtain ⟨k,c,hk,hc,_⟩ := H n
  rw [show k=n+(k-n) by omega,run_append] at hc
  cases hr : run m n blank with
  | none => simp [hr] at hc
  | some z => rfl

#print axioms inv_next
#print axioms never
end BB6.Agent2BinaryPair
