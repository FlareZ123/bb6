import LaneGenerator
namespace BB6.Agent12PlaneSum
open BB6.Agent12BitPlanes BB6.Agent12PlaneOps

/-- Multiplication in every lane, with no truncation of result width. -/
def mulP : List Nat → List Nat → List Nat
  | [],_ => []
  | p::ps,qs => addP (maskP p qs) (mul2 (mulP ps qs))

theorem mulP_sound (ps qs : List Nat) (j : Nat) : value (mulP ps qs) j=value ps j*value qs j := by
  induction ps with
  | nil => simp [mulP,value]
  | cons p ps ih => simp only [mulP,addP_sound,value_maskP,value_mul2,ih,value]; grind

def nsum (f : Nat→Nat) : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,j => nsum f n j+f (j+n)

theorem nsum_split (f : Nat→Nat) (a b j : Nat) : nsum f (a+b) j=nsum f a j+nsum f b (j+a) := by
  induction b with
  | zero => simp [nsum]
  | succ b ih =>
    rw [show a+(b+1)=(a+b)+1 by omega,nsum,ih,nsum]
    rw [show j+(a+b)=j+a+b by omega]; omega

theorem nsum_congr (f g : Nat→Nat) (n j : Nat) (h:∀ i<n,f (j+i)=g (j+i)) : nsum f n j=nsum g n j := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsum]; rw [ih (fun i hi=>h i (by omega)),h n (by omega)]

def horizontal (ps : List Nat) : Nat → List Nat
  | 0 => ps
  | k+1 => let v:=horizontal ps k; addP v (v.map (fun p=>p>>>2^k))

theorem horizontal_sound (ps : List Nat) (k j : Nat) : value (horizontal ps k) j=nsum (value ps) (2^k) j := by
  induction k generalizing j with
  | zero => simp [horizontal,nsum]
  | succ k ih =>
    simp only [horizontal,addP_sound,value_rshift,ih,Nat.pow_succ]
    rw [show 2^k*2=2^k+2^k by omega,nsum_split]

def aggregate (N q : Nat) (ps : List Nat) : Nat := value (horizontal (maskP q ps) (N.log2+1)) 0

theorem nsum_zero (f : Nat→Nat) (n j : Nat) (h:∀ i<n,f (j+i)=0) : nsum f n j=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nsum,ih (fun i hi=>h i (by omega)),h n (by omega)]

theorem aggregate_sound (N q : Nat) (ps : List Nat) (hq:q<2^N) :
    aggregate N q ps=nsum (fun j=>bit q j*value ps j) N 0 := by
  unfold aggregate
  rw [horizontal_sound]
  have hn : N≤2^(N.log2+1) := by
    have h:=@Nat.lt_log2_self N; omega
  rw [show 2^(N.log2+1)=N+(2^(N.log2+1)-N) by omega,nsum_split]
  have htail : nsum (value (maskP q ps)) (2^(N.log2+1)-N) (0+N)=0 := by
    apply nsum_zero
    intro i hi
    have hq' : q<2^(N+i) := Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide) (by omega))
    simp [value_maskP,bit,Nat.testBit_lt_two_pow hq']
  rw [htail,Nat.add_zero]
  apply nsum_congr
  intro i hi; exact value_maskP _ _ _

/-- Signed sums are used only in the theorem; the executable reduction uses
    nonnegative lane sums and a small integer linear combination. -/
def isum (f : Nat→Int) : Nat → Nat → Int
  | 0,_ => 0
  | n+1,j => isum f n j+f (j+n)

theorem isum_congr (f g : Nat→Int) (n j : Nat) (h:∀ i<n,f (j+i)=g (j+i)) : isum f n j=isum g n j := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [isum]; rw [ih (fun i hi=>h i (by omega)),h n (by omega)]

theorem isum_add (f g : Nat→Int) (n j : Nat) : isum (fun i=>f i+g i) n j=isum f n j+isum g n j := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum,ih]; omega

theorem isum_sub (f g : Nat→Int) (n j : Nat) : isum (fun i=>f i-g i) n j=isum f n j-isum g n j := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum,ih]; omega

theorem isum_mul (f : Nat→Int) (k : Int) (n j : Nat) : isum (fun i=>k*f i) n j=k*isum f n j := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp only [isum,ih,Int.mul_add]

theorem isum_cast (f : Nat→Nat) (n j : Nat) : isum (fun i=>(f i:Int)) n j=(nsum f n j:Int) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [isum,nsum,ih,Int.natCast_add]

theorem aggregate_int (N q : Nat) (ps : List Nat) (hq:q<2^N) :
    (aggregate N q ps:Int)=isum (fun j=>(bit q j:Int)*(value ps j:Int)) N 0 := by
  rw [aggregate_sound N q ps hq,←isum_cast]
  apply isum_congr
  intro i hi; push_cast; rfl

/-- A signed linear combination of nonnegative packed lane expressions. -/
def evalTerms : List (Int×List Nat) → Nat → Int
  | [],_ => 0
  | (c,ps)::ts,j => c*(value ps j:Int)+evalTerms ts j

def sumTerms (N q : Nat) : List (Int×List Nat) → Int
  | [] => 0
  | (c,ps)::ts => c*(aggregate N q ps:Int)+sumTerms N q ts

theorem sumTerms_sound (N q : Nat) (ts : List (Int×List Nat)) (hq:q<2^N) :
    sumTerms N q ts=isum (fun j=>(bit q j:Int)*evalTerms ts j) N 0 := by
  induction ts with
  | nil =>
    simp only [sumTerms,evalTerms,Int.mul_zero]
    have h : ∀ n, isum (fun _=>0) n 0=0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp [isum,ih]
    exact (h N).symm
  | cons t ts ih =>
    rcases t with ⟨c,ps⟩
    simp only [sumTerms,ih,evalTerms,aggregate_int N q ps hq]
    rw [←isum_mul,←isum_add]
    apply isum_congr
    intro i hi; grind

#print axioms mulP_sound
#print axioms horizontal_sound
#print axioms aggregate_int
#print axioms sumTerms_sound
end BB6.Agent12PlaneSum
