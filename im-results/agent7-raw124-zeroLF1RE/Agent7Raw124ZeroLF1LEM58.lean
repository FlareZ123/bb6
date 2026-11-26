import BlockPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw124ZeroLF1LEM58
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,true,0⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,3⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨true,true,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,false,4⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def A (l r : List Bool) : HZ := ⟨0,l,r⟩
def D (l r : List Bool) : HZ := ⟨3,l,r⟩
def F (l r : List Bool) : HZ := ⟨5,l,r⟩
def O : Nat → List Bool | 0 => [] | n+1 => true :: O n
def Z : Nat → List Bool | 0 => [] | n+1 => false :: Z n
def P : Nat → List Bool | 0 => [] | n+1 => false :: true :: P n
def L (n : Nat) : List Bool := Z (2*n+1) ++ [true]
def G (n : Nat) : List Bool := Z (5*n+3) ++ [true,true]
def left : List Nat → List Bool | [] => [] | n::xs => L n ++ left xs
def right : List Nat → List Bool | [] => [] | n::xs => G n ++ right xs
def dec : List Nat → List Nat | [] => [] | n::xs => (n-1)::xs
def sec (n : Nat) (xs : List Nat) : HZ := F (left xs) (O (2*n) ++ Z (5*n+2) ++ [true,true] ++ right (dec xs))
def Good : List Nat → Prop | [] => True | n::_ => 0<n

def Reach (a b : HZ) : Prop := ∃ t, hrun table t a = some b
theorem exactR {a b : HZ} {t : Nat} (h : hrun table t a = some b) : Reach a b := ⟨t,h⟩
theorem joinR {a b c : HZ} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨t,ht⟩ := h; obtain ⟨u,hu⟩ := g; exact ⟨t+u,hjoin ht hu⟩
theorem Oadd (a b : Nat) : O (a+b) = O a ++ O b := by
  induction a with
  | zero => simp [O]
  | succ a ih => rw [show a+1+b = (a+b)+1 by omega]; simp [O,ih]
theorem Zadd (a b : Nat) : Z (a+b) = Z a ++ Z b := by
  induction a with
  | zero => simp [Z]
  | succ a ih => rw [show a+1+b = (a+b)+1 by omega]; simp [Z,ih]
theorem Padd (a b : Nat) : P (a+b) = P a ++ P b := by
  induction a with
  | zero => simp [P]
  | succ a ih => rw [show a+1+b = (a+b)+1 by omega]; simp [P,ih]
theorem scanA (n j : Nat) (l r : List Bool) :
  hrun table n (A (true::Z j++l) (O n++r)) = some (A (true::Z (j+n)++l) r) := by
  induction n generalizing j with
  | zero => simp [hrun,O]
  | succ n ih =>
    have h : hrun table 1 (A (true::Z j++l) (O (n+1)++r)) = some (A (true::Z (j+1)++l) (O n++r)) := by rfl
    have q := hjoin h (ih (j+1))
    rw [show 1+n=n+1 by omega,show j+1+n=j+(n+1) by omega] at q
    exact q

theorem enter (l r : List Bool) : hrun table 2 (F (false::false::l) r) = some (A (true::true::l) r) := by rfl
theorem enterBlank (r : List Bool) : hrun table 2 (F [] r) = some (A [true,true] r) := by rfl
theorem turnA (j : Nat) (l r : List Bool) : hrun table 1 (A (true::Z j++true::l) (false::r)) = some (A (false::false::Z j++true::l) r) := by rfl
theorem endA (j : Nat) (l r : List Bool) : hrun table 9 (A (false::false::Z j++true::l) (false::false::false::r)) = some (F (false::Z j++true::l) (false::false::true::true::r)) := by rfl

theorem prepA (n : Nat) (l : List Bool) (ys : List Nat) :
  hrun table (2*(n+1)+10) (A (true::true::l) (O (2*(n+1)) ++ Z (5*(n+1)+2) ++ [true,true] ++ right ys)) =
  some (F (L (n+1)++l) ([false,false,true,true] ++ right (n::ys))) := by
  have h := scanA (2*(n+1)) 0 (true::l) (Z (5*(n+1)+2) ++ [true,true] ++ right ys)
  simp only [Z,List.nil_append,Nat.zero_add] at h
  have h := hjoin h (turnA (2*(n+1)) l (Z (5*(n+1)+1) ++ [true,true] ++ right ys))
  have h := hjoin h (endA (2*(n+1)) l (Z (5*n+3) ++ [true,true] ++ right ys))
  rw [show 2*(n+1)+1+9=2*(n+1)+10 by omega] at h
  simpa only [L,G,right,Z,List.append_assoc,List.cons_append,List.nil_append] using h

theorem prep (n : Nat) (l : List Bool) (ys : List Nat) :
  hrun table (2+ (2*(n+1)+10)) (F (false::false::l) (O (2*(n+1)) ++ Z (5*(n+1)+2) ++ [true,true] ++ right ys)) =
  some (F (L (n+1)++l) ([false,false,true,true] ++ right (n::ys))) := by
  exact hjoin (enter l _) (prepA n l ys)
theorem prepBlank (n : Nat) :
  hrun table (2+ (2*(n+1)+10)) (sec (n+1) []) = some (F (L (n+1)) ([false,false,true,true] ++ right [n])) := by
  have h := hjoin (enterBlank (O (2*(n+1)) ++ Z (5*(n+1)+2) ++ [true,true] ++ right [])) (prepA n [] [])
  simpa only [sec,left,right,dec,List.append_nil] using h

theorem toD (l r : List Bool) : hrun table 6 (F (false::false::l) (false::false::true::true::r)) = some (D (O 4 ++ P 1 ++ l) r) := by rfl
theorem sweepD (a : Nat) (l r : List Bool) : hrun table 5 (D (O (a+1)++l) (G 0++r)) = some (D (O (a+6)++l) r) := by rfl
theorem endD (a : Nat) (l r : List Bool) : hrun table 9 (D (O (a+1)++l) (Z 5++r)) = some (F (O (a+4)++l) (true::true::r)) := by rfl
theorem endDBlank (a : Nat) (l : List Bool) : hrun table 9 (D (O (a+1)++l) []) = some (F (O (a+4)++l) [true,true]) := by rfl

theorem sweepF (a b : Nat) (l r : List Bool) : hrun table a (F (O a++l) (Z b++r)) = some (F l (Z (a+b)++r)) := by
  induction a generalizing b with
  | zero => simp [hrun,O,Z,P]
  | succ a ih =>
    have h : hrun table 1 (F (O (a+1)++l) (Z b++r)) = some (F (O a++l) (Z (b+1)++r)) := by rfl
    have h := hjoin h (ih (b+1))
    rw [show 1+a=a+1 by omega,show a+(b+1)=a+1+b by omega] at h
    exact h

theorem popF (a b : Nat) (l r : List Bool) : hrun table (2*a) (F (P a++l) (O b++r)) = some (F l (O (2*a+b)++r)) := by
  induction a generalizing b with
  | zero => simp [hrun,O,Z,P]
  | succ a ih =>
    have h : hrun table 2 (F (P (a+1)++l) (O b++r)) = some (F (P a++l) (O (b+2)++r)) := by rfl
    have h := hjoin h (ih (b+2))
    rw [show 2+2*a=2*(a+1) by omega,show 2*a+(b+2)=2*(a+1)+b by omega] at h
    exact h
theorem scan (ys : List Nat) (j : Nat) :
    ∃ k zs, Good zs ∧ Reach (D (O (5*j+4) ++ P (j+1) ++ left ys) (right ys)) (sec (k+1) zs) := by
  induction ys generalizing j with
  | nil =>
    refine ⟨j,[],trivial,?_⟩
    have h1 := endDBlank (5*j+3) (P (j+1) ++ left [])
    have h1' : Reach (D (O (5*j+4) ++ P (j+1) ++ left []) (right [])) (F (O (5*j+7) ++ P (j+1)) [true,true]) := by
      apply exactR
      simpa only [left,right,List.append_nil,List.append_assoc,show 5*j+3+1=5*j+4 by omega,show 5*j+3+4=5*j+7 by omega] using h1
    have h2 := exactR (sweepF (5*j+7) 0 (P (j+1)) [true,true])
    have h3 := exactR (popF (j+1) 0 [] (Z (5*j+7)++[true,true]))
    have h2' : Reach (F (O (5*j+7) ++ P (j+1)) [true,true]) (F (P (j+1)) (Z (5*j+7)++[true,true])) := by
      simpa [Z] using h2
    have h3' : Reach (F (P (j+1)) (Z (5*j+7)++[true,true])) (sec (j+1) []) := by
      simpa [O,sec,left,right,dec,List.append_assoc,show 5*(j+1)+2=5*j+7 by omega] using h3
    exact joinR h1' (joinR h2' h3')
  | cons a ys ih =>
    cases a with
    | zero =>
      obtain ⟨k,zs,hg,h⟩ := ih (j+1)
      refine ⟨k,zs,hg,?_⟩
      have h1 := sweepD (5*j+3) (P (j+1) ++ left (0::ys)) (right ys)
      have h1' : Reach (D (O (5*j+4) ++ P (j+1) ++ left (0::ys)) (right (0::ys))) (D (O (5*(j+1)+4) ++ P (j+1+1) ++ left ys) (right ys)) := by
        apply exactR
        have hp : P (j+1) ++ L 0 = P (j+1+1) := by
          change P (j+1) ++ P 1 = _
          rw [← Padd]
        rw [show 5*j+3+1=5*j+4 by omega,show 5*j+3+6=5*(j+1)+4 by omega] at h1
        rw [← hp]
        simpa only [right,left,List.append_assoc] using h1
      exact joinR h1' h
    | succ a =>
      refine ⟨j,(a+1)::ys,by simp [Good],?_⟩
      have hr : right ((a+1)::ys) = Z 5 ++ right (a::ys) := by
        simp only [right,G,List.append_assoc]
        rw [show 5*(a+1)+3=5+(5*a+3) by omega,Zadd,List.append_assoc]
      have h1 := endD (5*j+3) (P (j+1) ++ left ((a+1)::ys)) (right (a::ys))
      have h1' : Reach (D (O (5*j+4) ++ P (j+1) ++ left ((a+1)::ys)) (right ((a+1)::ys))) (F (O (5*j+7) ++ P (j+1) ++ left ((a+1)::ys)) ([true,true] ++ right (a::ys))) := by
        rw [hr]
        apply exactR
        simpa only [List.append_assoc,List.cons_append,List.nil_append,show 5*j+3+1=5*j+4 by omega,show 5*j+3+4=5*j+7 by omega] using h1
      have h2 := exactR (sweepF (5*j+7) 0 (P (j+1) ++ left ((a+1)::ys)) ([true,true] ++ right (a::ys)))
      have h3 := exactR (popF (j+1) 0 (left ((a+1)::ys)) (Z (5*j+7) ++ [true,true] ++ right (a::ys)))
      have h2' : Reach (F (O (5*j+7) ++ P (j+1) ++ left ((a+1)::ys)) ([true,true] ++ right (a::ys))) (F (P (j+1) ++ left ((a+1)::ys)) (Z (5*j+7) ++ [true,true] ++ right (a::ys))) := by
        simpa [Z,List.append_assoc] using h2
      have h3' : Reach (F (P (j+1) ++ left ((a+1)::ys)) (Z (5*j+7) ++ [true,true] ++ right (a::ys))) (sec (j+1) ((a+1)::ys)) := by
        simpa [O,sec,dec,List.append_assoc,show 5*(j+1)+2=5*j+7 by omega] using h3
      exact joinR h1' (joinR h2' h3')
def prepared (n : Nat) (ys : List Nat) : HZ := F (left ((n+1)::ys)) ([false,false,true,true] ++ right (n::ys))
theorem prepAll (n : Nat) (xs : List Nat) (hg : Good xs) :
  hrun table (2+(2*(n+1)+10)) (sec (n+1) xs) = some (prepared n (dec xs)) := by
  cases xs with
  | nil => simpa [prepared,left,dec] using prepBlank n
  | cons a ys =>
    cases a with
    | zero => simp [Good] at hg
    | succ a =>
      have h := prep n (left (a::ys)) (a::ys)
      simpa only [sec,prepared,left,L,dec,Nat.add_sub_cancel,show 2*(a+1)=2*a+2 by omega,Z,List.append_assoc,List.cons_append,List.nil_append] using h

theorem preparedD (n : Nat) (ys : List Nat) :
  hrun table 6 (prepared n ys) = some (D (O 4 ++ P 1 ++ left (n::ys)) (right (n::ys))) := by
  have h := toD (left (n::ys)) (right (n::ys))
  simpa only [prepared,left,L,show 2*(n+1)=2*n+2 by omega,Z,List.append_assoc,List.cons_append,List.nil_append] using h

theorem growth (n : Nat) (xs : List Nat) (hg : Good xs) :
  ∃ t k zs, 0<t ∧ Good zs ∧ hrun table t (sec (n+1) xs) = some (sec (k+1) zs) := by
  obtain ⟨k,zs,hg',u,hu⟩ := scan (n::dec xs) 0
  have h := hjoin (prepAll n xs hg) (preparedD n (dec xs))
  exact ⟨_,k,zs,by omega,hg',hjoin h hu⟩

theorem root : hrun table 33 ⟨0,[],[]⟩ = some (sec 1 []) := by rfl

theorem arbitraryLive (n : Nat) : ∃ t k xs, n≤t ∧ Good xs ∧ hrun table t ⟨0,[],[]⟩ = some (sec (k+1) xs) := by
  induction n with
  | zero => exact ⟨33,0,[],by omega,trivial,root⟩
  | succ n ih =>
    obtain ⟨t,k,xs,ht,hg,h⟩ := ih
    obtain ⟨u,j,zs,hu,hg',h'⟩ := growth k xs hg
    exact ⟨t+u,j,zs,by omega,hg',hjoin h h'⟩
#print axioms growth
#print axioms arbitraryLive
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,a,xs,hk,hg,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [show embed (HZ.at ⟨0,[],[]⟩ 0) = blank from blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
end BB6.Agent7Raw124ZeroLF1LEM58
