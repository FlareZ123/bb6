import BB429LowZeroCycle
import Lean.Elab.Tactic.Omega

namespace BB429.LowWord
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000

/-- The three non-reset transitions in the exact rank coordinates. -/
inductive Move where
  | f | oe | oo
  deriving DecidableEq, Repr

abbrev RankState := Int × Int

def encode (s : State) : RankState := (2*(s.1:Int)+6, 2*(s.1:Int)+(s.2:Int))

def guard (v : Move) (s : RankState) : Prop :=
  match v with
  | .f => 2*s.1 ≤ s.2+9
  | .oe => s.2%4=1 ∧ s.2-2*s.1+12 ≤ -7 ∧ 3 ≤ s.2-s.1+6
  | .oo => s.2%4=3 ∧ s.2-2*s.1+12 ≤ -5

def step (v : Move) (s : RankState) : RankState :=
  match v with
  | .f => (2*s.1,s.2+3)
  | .oe => (2*s.1-s.2+9,s.2+11)
  | .oo => (2*s.1-s.2+1,s.2+7)

/-- Guarded rank transitions give actual successful source transitions. -/
theorem source_step (v : Move) (u w : Nat) (h : guard v (encode (u,w))) :
    ∃ a b, next (u,w)=some (a,b) ∧ encode (a,b)=step v (encode (u,w)) := by
  cases v with
  | f =>
    simp only [guard,encode,Prod.fst,Prod.snd] at h
    have hg : 2*u+3≤w := by omega
    refine ⟨2*u+3,w-2*u-3,?_,?_⟩
    · simp [next,hg]
    · simp only [encode,step,Prod.mk.injEq]
      omega
  | oe =>
    simp only [guard,encode,Prod.fst,Prod.snd] at h
    rcases h with ⟨h4,hg,hpos⟩
    have hF : ¬w≥2*u+3 := by omega
    have h2 : w≠2*u+2 := by omega
    have h1 : w≠2*u+1 := by omega
    have h0 : w≠2*u := by omega
    have hw : w%2≠0 := by omega
    have hd1 : u-w/2≠1 := by omega
    have hd2 : u-w/2≠2 := by omega
    have he : (u-w/2)%2=0 := by omega
    have hw1 : w≠1 := by omega
    refine ⟨u-w/2+7,2*w-4,?_,?_⟩
    · simp [next,hF,h2,h1,h0,hw,hd1,hd2,he,hw1]
    · simp only [encode,step,Prod.mk.injEq]
      omega
  | oo =>
    simp only [guard,encode,Prod.fst,Prod.snd] at h
    rcases h with ⟨h4,hg⟩
    have hF : ¬w≥2*u+3 := by omega
    have h2 : w≠2*u+2 := by omega
    have h1 : w≠2*u+1 := by omega
    have h0 : w≠2*u := by omega
    have hw : w%2≠0 := by omega
    have hd1 : u-w/2≠1 := by omega
    have hd2 : u-w/2≠2 := by omega
    have he : (u-w/2)%2≠0 := by omega
    refine ⟨u-w/2+3,2*w,?_,?_⟩
    · simp [next,hF,h2,h1,h0,hw,hd1,hd2,he]
    · simp only [encode,step,Prod.mk.injEq]
      omega

/-- Every successful source transition avoiding the two section counters
    is one of the three guarded non-reset transitions. -/
theorem nonsection_step (u w a b : Nat) (h : next (u,w)=some (a,b))
    (h0 : a≠0) (h11 : a≠11) :
    ∃ v, guard v (encode (u,w)) ∧ encode (a,b)=step v (encode (u,w)) := by
  simp only [next] at h
  split at h
  · simp only [Option.some.injEq,Prod.mk.injEq] at h
    refine ⟨.f,?_,?_⟩ <;> simp only [guard,encode,step,Prod.fst,Prod.snd,Prod.mk.injEq] <;> omega
  · split at h
    · simp_all
    · split at h
      · simp_all
      · split at h
        · simp_all
        · split at h
          · split at h
            · simp_all
            · split at h <;> simp_all
          · split at h
            · simp at h
            · split at h
              · simp_all
              · split at h
                · split at h
                  · simp_all
                  · simp only [Option.some.injEq,Prod.mk.injEq] at h
                    refine ⟨.oe,?_,?_⟩ <;> simp only [guard,encode,step,Prod.fst,Prod.snd,Prod.mk.injEq] <;> omega
                · simp only [Option.some.injEq,Prod.mk.injEq] at h
                  refine ⟨.oo,?_,?_⟩ <;> simp only [guard,encode,step,Prod.fst,Prod.snd,Prod.mk.injEq] <;> omega

def legal : List Move → RankState → Prop
  | [], _ => True
  | v::vs, s => guard v s ∧ legal vs (step v s)

def advance : List Move → RankState → RankState
  | [], s => s
  | v::vs,s => advance vs (step v s)

theorem legal_source (vs : List Move) (u w : Nat) (h : legal vs (encode (u,w))) :
    ∃ a b, run vs.length (u,w)=some (a,b) ∧ encode (a,b)=advance vs (encode (u,w)) := by
  induction vs generalizing u w with
  | nil => exact ⟨u,w,rfl,rfl⟩
  | cons v vs ih =>
    obtain ⟨hg,ht⟩ := h
    obtain ⟨x,y,hs,he⟩ := source_step v u w hg
    rw [←he] at ht
    obtain ⟨a,b,hr,ha⟩ := ih x y ht
    refine ⟨a,b,?_,?_⟩
    · rw [List.length_cons, Nat.add_comm vs.length 1,run_add]
      change (next (u,w)).bind (run vs.length)=some (a,b)
      rw [hs]
      exact hr
    · simpa only [advance,←he] using ha

/-- A trace with no intervening section return. -/
inductive NoSection : Nat → State → State → Prop where
  | nil (s : State) : NoSection 0 s s
  | cons {n : Nat} {s x t : State} : next s=some x → x.1≠0 → x.1≠11 →
      NoSection n x t → NoSection (n+1) s t

theorem complete_word {n : Nat} {s t : State} (h : NoSection n s t) :
    ∃ vs : List Move, vs.length=n ∧ legal vs (encode s) ∧ advance vs (encode s)=encode t := by
  induction h with
  | nil s => exact ⟨[],rfl,trivial,rfl⟩
  | @cons n s x t hs h0 h11 ht ih =>
    obtain ⟨v,hg,he⟩ := nonsection_step s.1 s.2 x.1 x.2 hs h0 h11
    obtain ⟨vs,hlen,hl,ha⟩ := ih
    exact ⟨v::vs,by simp [hlen],⟨hg,he ▸ hl⟩,by simp only [advance,←he,ha]⟩

/-- Symbolic A=aX+b*d+c, R=72X+d+r. -/
structure Form where
  a : Int
  b : Int
  c : Int
  r : Int
  deriving Repr, DecidableEq

def initial : Form := ⟨48,0,0,3⟩
def eval (f : Form) (X d : Int) : RankState := (f.a*X+f.b*d+f.c,72*X+d+f.r)

def symStep (v : Move) (f : Form) : Form :=
  match v with
  | .f => ⟨2*f.a,2*f.b,2*f.c,f.r+3⟩
  | .oe => ⟨2*f.a-72,2*f.b-1,2*f.c-f.r+9,f.r+11⟩
  | .oo => ⟨2*f.a-72,2*f.b-1,2*f.c-f.r+1,f.r+7⟩

theorem eval_step (v : Move) (f : Form) (X d : Int) :
    eval (symStep v f) X d=step v (eval f X d) := by
  cases v <;> simp only [eval,symStep,step,Prod.mk.injEq,Int.sub_mul,Int.mul_assoc,Int.mul_add,Int.mul_sub,Int.one_mul] <;> try omega
  all_goals exact ⟨trivial, by omega⟩

def symbolic : List Move → Form → Form
  | [], f => f
  | v::vs,f => symbolic vs (symStep v f)

theorem eval_symbolic (vs : List Move) (f : Form) (X d : Int) :
    eval (symbolic vs f) X d=advance vs (eval f X d) := by
  induction vs generalizing f with
  | nil => rfl
  | cons v vs ih =>
    simp only [symbolic,advance]
    rw [ih,eval_step]

def Modulus (f : Form) : Int := 1-2*f.b
def Coefficient (f : Form) : Int := 2*f.a-72
def Offset (f : Form) : Int := f.r+13-2*f.c

theorem affine_gate (f : Form) (X d : Int) :
    2*(eval f X d).1=(eval f X d).2+13 ↔
      Modulus f*d=Coefficient f*X-Offset f := by
  simp only [eval,Modulus,Coefficient,Offset,Prod.fst,Prod.snd,Int.sub_mul,Int.mul_add,Int.mul_assoc,Int.one_mul]
  omega

theorem symbolic_coefficients (vs : List Move) (f : Form) (hb : f.b≤0) :
    let g := symbolic vs f
    g.b≤0 ∧ g.a-72*g.b=(2:Int)^vs.length*(f.a-72*f.b) := by
  induction vs generalizing f with
  | nil => simp [symbolic,hb]
  | cons v vs ih =>
    have hb' : (symStep v f).b≤0 := by cases v <;> simp [symStep] <;> omega
    obtain ⟨h1,h2⟩ := ih (symStep v f) hb'
    simp only [symbolic,List.length_cons]
    refine ⟨h1,?_⟩
    rw [h2,Int.pow_succ,Int.mul_assoc]
    congr 1
    cases v <;> simp only [symStep,Int.mul_add,Int.mul_sub] <;> omega

theorem modulus_positive_odd (vs : List Move) :
    0<Modulus (symbolic vs initial) ∧ Modulus (symbolic vs initial)%2=1 := by
  have h := (symbolic_coefficients vs initial (by decide)).1
  unfold Modulus
  omega

theorem coefficient_identity (vs : List Move) :
    Coefficient (symbolic vs initial)=96*(2:Int)^vs.length-72*Modulus (symbolic vs initial) := by
  have h : (symbolic vs initial).a-72*(symbolic vs initial).b=(2:Int)^vs.length*48 := (symbolic_coefficients vs initial (by decide)).2
  simp only [Coefficient,Modulus,Int.mul_sub,Int.mul_one]
  rw [Int.mul_comm ((2:Int)^vs.length) 48] at h
  omega

theorem halt_encoded (u w : Nat) :
    next (u,w)=none ↔ 2*(encode (u,w)).1=(encode (u,w)).2+13 := by
  rw [next_none_iff_halt_line]
  simp only [encode,Prod.fst,Prod.snd]
  omega

/-- The initial low-side burst is a real source run at every positive scale. -/
theorem initial_burst (m d : Nat) (hm : 1≤m) (hd : 6≤d) :
    ∃ u w, run (4*m+3) (0,72*16^m+d-(12*m+6))=some (u,w) ∧
      encode (u,w)=eval initial (16^m) d := by
  let X := 16^m
  let u := 24*X-3
  let w := u+12+d
  have hX : 16*m≤X := by
    dsimp [X]
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.pow_succ]
      have hp : 0<16^m := Nat.pow_pos (by decide)
      omega
  have hpow : 2^(4*m+3)=8*X := by
    rw [Nat.pow_add,Nat.pow_mul]
    change 16^m*8=8*X
    exact Nat.mul_comm _ _
  have hu : u+3=3*2^(4*m+3) := by rw [hpow]; dsimp [u]; omega
  have hr : 2*u+w=72*X+d-(12*m+6)+3*(4*m+3) := by dsimp [u,w]; omega
  have hrun := LowZeroCycle.first_of_coordinates (4*m+3) 0 (72*X+d-(12*m+6)) u w (by omega) (by simpa only [Nat.mul_zero,Nat.zero_add] using hr)
  refine ⟨u,w,?_,?_⟩
  · exact LowZeroCycle.first_is_run _ _ _ _ _ hrun
  · simp only [eval,initial,encode,Prod.mk.injEq,Int.zero_mul,Int.add_zero]
    have hcast : (X:Int)=(16:Int)^m := by exact_mod_cast (show X=16^m from rfl)
    dsimp [u,w]
    omega

/-- Full mixed-word terminal criterion. The affine equation covers all finite
    words over the three non-reset transitions, not just repeating pairs. -/
def Terminal (m : Nat) (vs : List Move) : Prop :=
  1≤m ∧ ∃ d : Nat, 6≤d ∧ d%4=2 ∧ legal vs (eval initial (16^m) d) ∧
    Modulus (symbolic vs initial)*(d:Int)=Coefficient (symbolic vs initial)*(16:Int)^m-Offset (symbolic vs initial)

theorem terminal_source (m : Nat) (vs : List Move) (h : Terminal m vs) :
    ∃ d a b : Nat, 6≤d ∧ d%4=2 ∧
      run (4*m+3+vs.length) (0,72*16^m+d-(12*m+6))=some (a,b) ∧ next (a,b)=none := by
  obtain ⟨hm,d,hd,hmod,hl,hg⟩ := h
  obtain ⟨u,w,hr,he⟩ := initial_burst m d hm hd
  rw [←he] at hl
  obtain ⟨a,b,hs,ha⟩ := legal_source vs u w hl
  refine ⟨d,a,b,hd,hmod,?_,?_⟩
  · rw [run_add,hr]
    exact hs
  · apply (halt_encoded a b).mpr
    rw [ha,he,←eval_symbolic]
    exact (affine_gate _ _ _).mpr hg

/-- Completeness for any first halt following the initial burst and having no
    intervening section return. -/
theorem terminal_complete (m d n u w a b : Nat) (hm : 1≤m) (hd : 6≤d) (hmod : d%4=2)
    (he : encode (u,w)=eval initial (16^m) d) (hs : NoSection n (u,w) (a,b))
    (hh : next (a,b)=none) : ∃ vs, vs.length=n ∧ Terminal m vs := by
  obtain ⟨vs,hlen,hl,ha⟩ := complete_word hs
  refine ⟨vs,hlen,hm,d,hd,hmod,?_,?_⟩
  · rwa [←he]
  · apply (affine_gate _ _ _).mp
    rw [eval_symbolic,←he,ha]
    exact (halt_encoded a b).mp hh

#print axioms source_step
#print axioms nonsection_step
#print axioms legal_source
#print axioms complete_word
#print axioms terminal_source
#print axioms terminal_complete
#print axioms coefficient_identity
end BB429.LowWord
