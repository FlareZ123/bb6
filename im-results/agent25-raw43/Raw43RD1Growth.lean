import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43RD1Growth
open BB6Coverage BB6Coverage.Agent31Pump

inductive Kind where
  | rb | rc | rd | re | le
  deriving DecidableEq

def cOne : Kind → Move
  | .rb => ⟨false,true,1⟩
  | .rc => ⟨false,true,2⟩
  | .rd => ⟨false,true,3⟩
  | .re => ⟨false,true,4⟩
  | .le => ⟨true,false,4⟩

def table (k : Kind) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (cOne k))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Z : List Bool := [false,false]
def Q : List Bool := [true,false]
def X : List Bool := [true,false,true,false]
def block (d : Nat) : List Bool := rep Z d ++ P
def ending (d : Nat) : List Bool := rep Z d ++ [true]
def A (m : Nat) : Z0 := ⟨0,[],rep P m⟩
def E (l : List Bool) (r : Nat) : Z0 := ⟨4,[true]++l,rep P r⟩
def Reaches (k : Kind) (a b : Z0) : Prop :=
  ∃ n, run0 (table k) n a = some b

theorem trans {k : Kind} {a b c : Z0} (h : Reaches k a b) (g : Reaches k b c) :
    Reaches k a c := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨m,hm⟩ := g
  exact ⟨n+m,join0 hn hm⟩

theorem rep_add (W : List Bool) (a b : Nat) :
    rep W (a+b) = rep W a ++ rep W b := by
  induction a with
  | zero => simp [rep]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [rep,ih,List.append_assoc]

theorem rep_double (W : List Bool) (n : Nat) :
    rep W (2*n) = rep (W++W) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2+2*n by omega,rep_add,ih]
    simp only [rep,List.append_nil,List.append_assoc]

theorem rep_length (W : List Bool) (n : Nat) :
    (rep W n).length = W.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih,Nat.mul_succ,Nat.add_comm]

private theorem rightOne (k : Kind) (L R : List Bool) :
    run0 (table k) 4 ⟨4,[true]++L,[]++P++R⟩ =
    some ⟨4,[true]++Z++L,[]++R⟩ := by cases k <;> rfl

private theorem leftOne (k : Kind) (L R : List Bool) :
    run0 (table k) 2 ⟨4,[]++Z++L,[]++R⟩ =
    some ⟨4,[]++L,[]++P++R⟩ := by cases k <;> rfl

private theorem turn (k : Kind) (L : List Bool) :
    run0 (table k) 6 ⟨4,[true]++L,[]⟩ =
    some ⟨4,[false]++L,P⟩ := by cases k <;> rfl

private theorem exit (k : Kind) (R : List Bool) :
    run0 (table k) 2 ⟨4,P,R⟩ =
    some ⟨0,[],P++R⟩ := by cases k <;> rfl

private theorem zeroRotate (r : Nat) :
    [false] ++ rep Z r = rep Z r ++ [false] :=
  rotate false [false] r

/-- Sweep all pairs rightward, turn on blank, sweep all pairs back. -/
theorem bounce (k : Kind) (r : Nat) (L : List Bool) :
    Reaches k (E L r) ⟨4,[false]++L,rep P (r+1)⟩ := by
  have h1 := sweepR (table k) 4 [true] [] P Z 4 (rightOne k) r L []
  have h1' : run0 (table k) (4*r) (E L r) =
      some ⟨4,[true]++rep Z r++L,[]⟩ := by
    simpa only [E,List.nil_append,List.append_nil] using h1
  have h2 := turn k (rep Z r++L)
  have h2' : run0 (table k) 6 ⟨4,[true]++rep Z r++L,[]⟩ =
      some ⟨4,rep Z r++([false]++L),P⟩ := by
    have he : [false]++(rep Z r++L) = rep Z r++([false]++L) := by
      rw [← List.append_assoc,zeroRotate,List.append_assoc]
    simpa only [List.append_assoc,he] using h2
  have h3 := sweepL (table k) 4 [] [] Z P 2 (leftOne k) r ([false]++L) P
  have h3' : run0 (table k) (2*r) ⟨4,rep Z r++([false]++L),P⟩ =
      some ⟨4,[false]++L,rep P (r+1)⟩ := by
    simpa only [List.nil_append,rep_snoc,rep] using h3
  exact ⟨_,join0 (join0 h1' h2') h3'⟩

/-- A left block with 2d+1 zeros then 1 is consumed, adding d+2 pairs. -/
theorem eStep (k : Kind) (d r : Nat) (L : List Bool) :
    Reaches k (E (block d++L) r) (E L (r+d+2)) := by
  have h := bounce k r (block d++L)
  have he : [false]++(block d++L) = rep Z (d+1)++([true]++L) := by
    unfold block
    rw [← List.append_assoc,← List.append_assoc,zeroRotate]
    simp only [List.append_assoc]
    change rep Z d ++ (Z ++ ([true]++L)) = _
    rw [← List.append_assoc,rep_snoc]
    rfl
  rw [he] at h
  have hs := sweepL (table k) 4 [] [] Z P 2 (leftOne k) (d+1) ([true]++L) (rep P (r+1))
  have hs' : run0 (table k) (2*(d+1)) ⟨4,rep Z (d+1)++([true]++L),rep P (r+1)⟩ =
      some (E L (r+d+2)) := by
    simp only [E,List.nil_append] at hs ⊢
    rw [← rep_add,show d+1+(r+1)=r+d+2 by omega] at hs
    exact hs
  exact trans h ⟨_,hs'⟩

/-- The final block has 2d zeros then 1; the left turn enters A. -/
theorem eLast (k : Kind) (d r : Nat) :
    Reaches k (E (ending d) r) (A (r+d+2)) := by
  have h := bounce k r (ending d)
  have he : [false]++ending d = rep Z d++P := by
    unfold ending
    rw [← List.append_assoc,zeroRotate,List.append_assoc]
    rfl
  rw [he] at h
  have hs := sweepL (table k) 4 [] [] Z P 2 (leftOne k) d P (rep P (r+1))
  have hs' : run0 (table k) (2*d) ⟨4,rep Z d++P,rep P (r+1)⟩ =
      some ⟨4,P,rep P (r+d+1)⟩ := by
    simp only [List.nil_append] at hs
    rw [← rep_add,show d+(r+1)=r+d+1 by omega] at hs
    exact hs
  have hf := exit k (rep P (r+d+1))
  exact trans (trans h ⟨_,hs'⟩) ⟨2,by simpa only [A,rep,show r+d+2=(r+d+1)+1 by omega] using hf⟩

/-- Any finite stack of equal odd-zero blocks and one even-zero end block
    returns to A, adding the corresponding number of pairs. -/
theorem chain (k : Kind) (d e n r : Nat) :
    Reaches k (E (rep (block d) n++ending e) r)
      (A (r+(d+2)*n+e+2)) := by
  induction n generalizing r with
  | zero => simpa [rep] using eLast k e r
  | succ n ih =>
    have h := eStep k d r (rep (block d) n++ending e)
    have h' := trans h (ih (r+d+2))
    rw [show r+d+2+(d+2)*n+e+2=r+(d+2)*(n+1)+e+2 by
      rw [Nat.mul_succ]; omega] at h'
    simpa only [rep,List.append_assoc] using h'

#print axioms bounce
#print axioms eStep
#print axioms eLast
#print axioms chain
end BB6.Agent25Raw43RD1Growth
