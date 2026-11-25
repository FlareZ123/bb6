import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60LBCounter
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

def z (n : Nat) := List.replicate n false
def o (n : Nat) := List.replicate n true
def L (a : Nat) : List Bool := z (3*a+2) ++ [true,true]
def F (l r : List Bool) : Z0 := ⟨5,l,r⟩
def D (l r : List Bool) : Z0 := ⟨3,l,r⟩
def Reach (c d : Z0) : Prop := ∃ t, run0 table t c = some d

theorem trans {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨i,hi⟩ := h
  obtain ⟨j,hj⟩ := g
  exact ⟨i+j,join0 hi hj⟩

theorem repl_add (x : Bool) (n m : Nat) : List.replicate (n+m) x = List.replicate n x ++ List.replicate m x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.succ_add,List.replicate_succ,ih,List.cons_append]

theorem L_prefix (a : Nat) : L a = [false,false] ++ (z (3*a) ++ [true,true]) := by
  unfold L z
  rw [show 3*a+2=2+3*a by omega,repl_add false 2 (3*a)]
  rfl

theorem L_succ (a : Nat) : L (a+1) = [false,false,false] ++ L a := by
  unfold L z
  rw [show 3*(a+1)+2=3+(3*a+2) by omega,repl_add false 3 (3*a+2)]
  rfl

theorem zr (n : Nat) : rep [false] n = z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,z,List.replicate_succ,ih]
theorem or (n : Nat) : rep [true] n = o n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,o,List.replicate_succ,ih]

theorem clear1 (l r : List Bool) : run0 table 1 (D (false::l) r) = some (D l (true::r)) := rfl

theorem clear (k : Nat) (R : List Bool) :
    Reach (D (z (k+2) ++ [true,true]) R) (F (L 0) (o k ++ R)) := by
  have h := sweepL table 3 [] [] [false] [true] 1 (by intro l r; exact clear1 l r) k ([false,false,true,true]) R
  have h' : run0 table (1*k) (D (z (k+2) ++ [true,true]) R) = some (D [false,false,true,true] (o k ++ R)) := by
    simpa only [List.nil_append,zr,or, D,z,repl_add,List.append_assoc,show List.replicate 2 false ++ [true,true] = [false,false,true,true] by rfl] using h
  have h2 (S : List Bool) : run0 table 6 (D [false,false,true,true] S) = some (F (L 0) S) := rfl
  exact ⟨1*k+6,join0 h' (h2 _)⟩

theorem consume (a : Nat) (R : List Bool) (hR : R.headD false = false) :
    run0 table 3 (F (L a) ([true,true]++R)) = some (F (L (a+1)) R.tail) := by
  rw [L_succ,L_prefix]
  cases R with
  | nil => rfl
  | cons b R =>
    have hb : b = false := hR
    subst b
    rfl

theorem expand (a : Nat) (R : List Bool) :
    run0 table 4 (F (L a) ([true,true,true]++R)) = some (D (z (3*a+2+2) ++ [true,true]) (false::R)) := by
  rw [L_prefix]
  unfold z
  rw [show 3*a+2+2=4+3*a by omega,repl_add false 4 (3*a)]
  rfl

theorem transfer (a b : Nat) (R : List Bool) (hR : R.headD false = false) :
    Reach (F (L a) (o (3*b+2) ++ R)) (F (L (a+b+1)) R.tail) := by
  -- strong induction on total, then induction on the number of right triples
  have aux : ∀ n b a, a+b=n → ∀ R : List Bool, R.headD false = false →
      Reach (F (L a) (o (3*b+2) ++ R)) (F (L (a+b+1)) R.tail) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro b
      induction b with
      | zero =>
        intro a hn R hR
        simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,show o 2 = [true,true] by rfl] using (show Reach (F (L a) ([true,true]++R)) (F (L (a+1)) R.tail) from ⟨3,consume a R hR⟩)
      | succ b ib =>
        intro a hn R hR
        let S := o (3*b+2) ++ R
        have h1 : Reach (F (L a) (o (3*(b+1)+2) ++ R)) (D (z (3*a+2+2) ++ [true,true]) (false::S)) := by
          refine ⟨4,?_⟩
          simpa only [show 3*(b+1)+2=3+(3*b+2) by omega,o,repl_add,List.append_assoc,S,show List.replicate 3 true = [true,true,true] by rfl] using expand a S
        have h2 := clear (3*a+2) (false::S)
        have h3 := ih a (by omega) a 0 (by omega) (false::S) rfl
        have h4 := ib (a+1) (by omega) R hR
        have h3' : Reach (F (L 0) (o (3*a+2) ++ (false::S))) (F (L (a+1)) S) := by simpa using h3
        have h4' : Reach (F (L (a+1)) S) (F (L (a+(b+1)+1)) R.tail) := by
          simpa only [S,show a+1+b+1=a+(b+1)+1 by omega] using h4
        exact trans h1 (trans h2 (trans h3' h4'))
  exact aux (a+b) b a rfl R hR

theorem begin (a : Nat) : run0 table 2 (F (L a) []) = some (D (z (3*a+2+2) ++ [true,true]) []) := by
  rw [L_prefix]
  unfold z
  rw [show 3*a+2+2=4+3*a by omega,repl_add false 4 (3*a)]
  rfl

theorem grow (a : Nat) : Reach (F (L a) []) (F (L (a+1)) []) := by
  have h1 : Reach (F (L a) []) (D (z (3*a+2+2) ++ [true,true]) []) := ⟨2,begin a⟩
  have h2 := clear (3*a+2) []
  have h3 := transfer 0 a [] rfl
  simpa only [List.append_nil,Nat.zero_add,List.tail_nil] using trans h1 (trans h2 (by simpa only [List.append_nil,Nat.zero_add,List.tail_nil] using h3))

def family (n : Nat) : Z0 := F (L (n+1)) []
noncomputable def cost (n : Nat) : Nat := Classical.choose (grow (n+1))
theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := Classical.choose_spec (grow (n+1))
theorem positive (n : Nat) : 0 < cost n := by
  by_cases hz : cost n = 0
  · have h := growth n
    rw [hz,run0] at h
    have he := congrArg (fun c : Z0 => c.l.length) (Option.some.inj h)
    simp [family,F,L,z] at he
    omega
  · omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 cost entry positive growth m hm

#print axioms transfer
#print axioms grow
#print axioms never
end BB6.Agent1Raw60LBCounter
