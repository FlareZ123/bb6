import Lean
namespace BB6.Agent12BitPlanes

def bit (x i : Nat) : Nat := (x.testBit i).toNat

def wsum : Nat → (Nat → Nat) → Nat
  | 0,_ => 0
  | n+1,f => wsum n f + 2^n*f n

theorem wsum_congr (n : Nat) (f g : Nat→Nat) (h : ∀ i<n, f i=g i) : wsum n f=wsum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wsum]; rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem wsum_add (n : Nat) (f g : Nat→Nat) : wsum n (fun i=>f i+g i)=wsum n f+wsum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wsum,ih,Nat.mul_add]; omega

theorem wsum_mul (n c : Nat) (f : Nat→Nat) : wsum n (fun i=>c*f i)=c*wsum n f := by
  induction n with
  | zero => simp [wsum]
  | succ n ih => simp only [wsum,ih,Nat.mul_add]; rw [←Nat.mul_assoc, Nat.mul_comm (2^n) c, Nat.mul_assoc]

theorem wsum_bit (n q : Nat) : wsum n (bit q)=q%2^n := by
  induction n with
  | zero => simp [wsum,Nat.mod_one]
  | succ n ih => rw [wsum,ih,bit,Nat.toNat_testBit,Nat.mod_pow_succ]

theorem bit_and (x y i : Nat) : bit (x&&&y) i=bit x i*bit y i := by
  unfold bit
  simp only [Nat.testBit_and]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem bit_add (x y i : Nat) : bit x i+bit y i=bit (x^^^y) i+2*bit (x&&&y) i := by
  unfold bit
  simp only [Nat.testBit_and,Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> decide

/-- A list of binary planes, low value bit first. Each mask contains one bit
    for every independently packed natural-number lane. -/
def value : List Nat → Nat → Nat
  | [],_ => 0
  | p::ps,i => bit p i + 2*value ps i

def addMask : List Nat → Nat → List Nat
  | [],c => [c]
  | p::ps,c => (p^^^c)::addMask ps (p&&&c)

theorem value_addMask (ps : List Nat) (c i : Nat) : value (addMask ps c) i=value ps i+bit c i := by
  induction ps generalizing c with
  | nil => simp [addMask,value]
  | cons p ps ih => simp only [addMask,value,ih]; have h:=bit_add p c i; omega

theorem value_append_zero (ps : List Nat) (i : Nat) : value (ps++[0]) i=value ps i := by
  induction ps with
  | nil => simp [value,bit]
  | cons p ps ih => simp [value,ih]

theorem value_rshift (ps : List Nat) (k i : Nat) : value (ps.map (fun p=>p>>>k)) i=value ps (i+k) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [value,bit,Nat.add_comm k i,ih]

theorem value_lshift (ps : List Nat) (k i : Nat) : value (ps.map (fun p=>p<<<k)) i=if k≤i then value ps (i-k) else 0 := by
  induction ps with
  | nil => simp [value]
  | cons p ps ih =>
    by_cases h : k≤i <;> simp [value,bit,h,ih]

theorem value_clip (ps : List Nat) (n i : Nat) : value (ps.map (fun p=>p&&&(2^n-1))) i=if i<n then value ps i else 0 := by
  induction ps with
  | nil => simp [value]
  | cons p ps ih =>
    simp only [List.map_cons,value,bit_and,ih]
    by_cases h : i<n <;> simp [bit,h]

theorem value_bound (ps : List Nat) (n i : Nat) (h : ∀ p∈ps, p<2^n) (hi : n≤i) : value ps i=0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    have hp' : p<2^i := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) hi)
    simp [value,bit,Nat.testBit_lt_two_pow hp',ih (fun v hv=>h v (by simp [hv]))]

def weightedPlanes (n q : Nat) : List Nat → Nat
  | [] => 0
  | p::ps => ((p&&&q)%2^n)+2*weightedPlanes n q ps

theorem weightedPlanes_sound (n q : Nat) (ps : List Nat) : weightedPlanes n q ps=wsum n (fun i=>bit q i*value ps i) := by
  induction ps with
  | nil =>
    simp only [weightedPlanes,value,Nat.mul_zero]
    induction n with
    | zero => rfl
    | succ n ih => simp only [wsum,Nat.mul_zero,Nat.add_zero]; exact ih
  | cons p ps ih =>
    simp only [weightedPlanes,ih,value,Nat.mul_add]
    rw [wsum_add,←wsum_mul]
    congr 1
    · rw [←wsum_bit]
      apply wsum_congr
      intro i hi
      rw [bit_and,Nat.mul_comm]
    · apply wsum_congr
      intro i hi
      ac_rfl

/-- Certify a suffix count in parallel. The extra zero plane checks that no
    lane overflows. The bound prevents an arbitrary constant above the word. -/
def countCheck (n q : Nat) (ps : List Nat) : Prop :=
  (∀ p∈ps,p<2^n) ∧ ps++[0]=addMask (ps.map (fun p=>p>>>1)) q

def countCheckB (n q : Nat) (ps : List Nat) : Bool :=
  ps.all (fun p=>decide (p<2^n)) && decide (ps++[0]=addMask (ps.map (fun p=>p>>>1)) q)

theorem countCheckB_sound (n q : Nat) (ps : List Nat) (h : countCheckB n q ps=true) : countCheck n q ps := by
  simpa [countCheckB,countCheck,List.all_eq_true] using h

theorem count_rec (n q : Nat) (ps : List Nat) (h : countCheck n q ps) (i : Nat) :
    value ps i=value ps (i+1)+bit q i := by
  have he := congrArg (fun v=>value v i) h.2
  rw [value_append_zero,value_addMask,value_rshift] at he
  exact he

theorem count_top (n q : Nat) (ps : List Nat) (h : countCheck n q ps) : value ps n=0 := value_bound ps n n h.1 (by omega)

/-- A second parallel certificate gives the bit-position j in every lane. -/
def indexCheck (n : Nat) (ps : List Nat) : Prop :=
  ps++[0]=(addMask (ps.map (fun p=>p<<<1)) ((2^n-1)&&&(2^n-2))).map (fun p=>p&&&(2^n-1))

theorem index_sound (n : Nat) (ps : List Nat) (h : indexCheck n ps) (i : Nat) (hi : i<n) : value ps i=i := by
  induction i with
  | zero =>
    have he := congrArg (fun v=>value v 0) h
    rw [value_append_zero,value_clip,value_addMask,value_lshift] at he
    have hn : 0<n := hi
    have hm : (2^n-2)%2=0 := by
      obtain ⟨m,rfl⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
      rw [Nat.pow_succ]; omega
    simp only [hi,ite_true,bit_and] at he
    have hb : bit (2^n-2) 0=0 := by simp [bit,hm]
    simpa [hb] using he
  | succ i ih =>
    have he := congrArg (fun v=>value v (i+1)) h
    rw [value_append_zero,value_clip,value_addMask,value_lshift] at he
    simp only [hi,ite_true,show 1≤i+1 by omega,Nat.add_sub_cancel,bit_and] at he
    have hn : 0<n := by omega
    have hb : bit (2^n-1) (i+1)=1 := by simp [bit,hi]
    have hb' : bit (2^n-2) (i+1)=1 := by
      have eq : 2^n-2=2*(2^(n-1)-1) := by
        obtain ⟨m,hm⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
        rw [hm,Nat.pow_succ]; simp; have hp:=Nat.two_pow_pos m; omega
      rw [eq,bit,show 2*(2^(n-1)-1)=2^1*(2^(n-1)-1) by simp,Nat.testBit_two_pow_mul]
      simp [show i<n-1 by omega]
    rw [hb,hb',Nat.one_mul,ih (by omega)] at he
    exact he

#print axioms weightedPlanes_sound
#print axioms countCheckB_sound
#print axioms count_rec
#print axioms index_sound
end BB6.Agent12BitPlanes
