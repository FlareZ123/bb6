import Q0MacroCore
import BB429Rank

namespace BB429Q0Macro
set_option maxHeartbeats 4000000

def stateAR (a R : Nat) : BB429.State := (a,R-2*a)
def original (x r : Nat) : BB429.State := stateAR (4*x-3) (4*r-1)

/-- The exact F predecessor equations suffice for a genuine accelerator step. -/
theorem invF_rank (a R x S : Nat) (ha : a=2*x+3) (hr : R=S+3)
    (hb : 2*a≤R) : BB429.next (stateAR x S)=some (stateAR a R) := by
  have hw : 2*x+3≤S-2*x := by omega
  simp [stateAR,BB429.next,hw]
  omega

/-- The exact S equations suffice, including all non-special guards. -/
theorem invS_rank (a R x S : Nat) (ha : 13≤a) (hao : a%2=1)
    (hr : R=S+11) (hA : 2*a+S=4*x+15) (_hS : S%2=1)
    (hb : 2*a≤R) : BB429.next (stateAR x S)=some (stateAR a R) := by
  let w := S-2*x
  have hd : x-w/2=a-7 := by dsimp [w]; omega
  have hd1 : x-w/2≠1 := by omega
  have hd2 : x-w/2≠2 := by omega
  have hde : (x-w/2)%2=0 := by omega
  have hw1 : w≠1 := by dsimp [w]; omega
  have hwo : w%2≠0 := by dsimp [w]; omega
  have hg : ¬ 2*x+3≤w := by dsimp [w]; omega
  have hg2 : w≠2*x+2 := by dsimp [w]; omega
  have hg1 : w≠2*x+1 := by dsimp [w]; omega
  have hg0 : w≠2*x := by dsimp [w]; omega
  change BB429.next (x,w)=some (a,R-2*a)
  simp only [BB429.next,ite_eq_right hg,ite_eq_right hg2,ite_eq_right hg1,ite_eq_right hg0,ite_eq_right hwo,
    ite_eq_right hd1,ite_eq_right hd2,ite_eq_left hde,ite_eq_right hw1,Option.some.injEq,Prod.mk.injEq]
  dsimp [w]
  omega

/-- The exact E equations suffice, including all non-special guards. -/
theorem invE_rank (a R x S : Nat) (ha : 6≤a) (hae : a%2=0)
    (hr : R=S+7) (hA : 2*a+S=4*x+7) (_hS : S%2=1)
    (hb : 2*a≤R) : BB429.next (stateAR x S)=some (stateAR a R) := by
  let w := S-2*x
  have hd : x-w/2=a-3 := by dsimp [w]; omega
  have hd1 : x-w/2≠1 := by omega
  have hd2 : x-w/2≠2 := by omega
  have hde : (x-w/2)%2≠0 := by omega
  have hwo : w%2≠0 := by dsimp [w]; omega
  have hg : ¬ 2*x+3≤w := by dsimp [w]; omega
  have hg2 : w≠2*x+2 := by dsimp [w]; omega
  have hg1 : w≠2*x+1 := by dsimp [w]; omega
  have hg0 : w≠2*x := by dsimp [w]; omega
  change BB429.next (x,w)=some (a,R-2*a)
  simp only [BB429.next,ite_eq_right hg,ite_eq_right hg2,ite_eq_right hg1,ite_eq_right hg0,ite_eq_right hwo,
    ite_eq_right hd1,ite_eq_right hd2,ite_eq_right hde,Option.some.injEq,Prod.mk.injEq]
  dsimp [w]
  omega

private theorem run4_steps {s0 s1 s2 s3 s4 : BB429.State}
    (h1 : BB429.next s0=some s1) (h2 : BB429.next s1=some s2)
    (h3 : BB429.next s2=some s3) (h4 : BB429.next s3=some s4) :
    BB429.run 4 s0=some s4 := by
  simp [BB429.run,h1,h2,h3,h4]

/-- All four macro inverse equations are sufficient, in the large cone.
This establishes the actual deterministic BB429.run equality. -/
theorem macro_converse (d : Digit) (x r X R : Nat)
    (hx : 400≤x) (hc : 3*x≤r) (hr : r=R+cost d)
    (he : 16*X+offset d=x+digit d*r) :
    BB429.run 4 (original X R)=some (original x r) := by
  cases d <;> simp [digit,cost,offset] at hr he
  · unfold original
    apply run4_steps (s1:=stateAR (8*X-3) (4*R+2))
      (s2:=stateAR (16*X-3) (4*R+5)) (s3:=stateAR (32*X-3) (4*R+8))
    all_goals apply invF_rank <;> omega
  · unfold original
    apply run4_steps (s1:=stateAR (8*X-3) (4*R+2))
      (s2:=stateAR (16*X-3) (4*R+5)) (s3:=stateAR (32*X-2*R-1) (4*R+16))
    · apply invF_rank <;> omega
    · apply invF_rank <;> omega
    · apply invS_rank <;> omega
    · apply invF_rank <;> omega
  · unfold original
    apply run4_steps (s1:=stateAR (8*X-2*R-2) (4*R+6))
      (s2:=stateAR (16*X-4*R-1) (4*R+9)) (s3:=stateAR (32*X-8*R+1) (4*R+12))
    · apply invE_rank <;> omega
    · apply invF_rank <;> omega
    · apply invF_rank <;> omega
    · apply invF_rank <;> omega
  · unfold original
    apply run4_steps (s1:=stateAR (8*X-2*R-2) (4*R+6))
      (s2:=stateAR (16*X-4*R-1) (4*R+9)) (s3:=stateAR (32*X-10*R+1) (4*R+20))
    · apply invE_rank <;> omega
    · apply invF_rank <;> omega
    · apply invS_rank <;> omega
    · apply invF_rank <;> omega

/-- Path with its terminal coordinates and little-endian digit polynomial. -/
inductive PathEnd : Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (p y : Nat) : PathEnd 0 p y p y 0
  | cons (d : Digit) {m p y P Y D : Nat} (h : num d p y%16=0)
      (tail : PathEnd m (nextP d p) (nextY d p y) P Y D) :
      PathEnd (m+1) p y P Y (digit d+16*D)

theorem path_end_exists {m p y : Nat} (h : Path m p y) :
    ∃ P Y D, PathEnd m p y P Y D := by
  induction h with
  | nil p y => exact ⟨p,y,0,.nil _ _⟩
  | cons d h tail ih =>
    obtain ⟨P,Y,D,hp⟩ := ih
    exact ⟨P,Y,digit d+16*D,.cons d h hp⟩

theorem PathEnd.toPath {m p y P Y D : Nat} (h : PathEnd m p y P Y D) :
    Path m p y := by
  induction h with
  | nil p y => exact .nil _ _
  | cons d h tail ih => exact .cons d h ih

private theorem cone_back (d : Digit) (x r X R : Nat)
    (hx : 400≤x) (hc : 3*x≤r) (hr : r=R+cost d)
    (he : 16*X+offset d=x+digit d*r) :
    x≤16*X ∧ 3*X≤R := by
  cases d <;> simp [cost,offset,digit] at * <;> omega

/-- Converse lift: every signed path in the large cone has a genuine
prepared-state chain of the original accelerator, with explicit endpoint. -/
theorem path_end_lift {m p y P Y D : Nat} (h : PathEnd m p y P Y D)
    (x r A B : Nat) (hx : 25*16^m≤x) (hc : 3*x≤r)
    (hrsum : r+p=16^m*A) (hxsum : x+y=16^m*B) :
    ∃ X R, BB429.run (4*m) (original X R)=some (original x r) ∧
      25≤X ∧ 3*X≤R ∧ R+P=16^m*A ∧ X+Y=B+A*D := by
  induction h generalizing x r A B with
  | nil p y =>
    refine ⟨x,r,?_,?_,hc,?_,?_⟩ <;> simp [BB429.run] at * <;> omega
  | @cons d m p y P Y D hdiv tail ih =>
    have hxbig : 400≤x := by
      rw [Nat.pow_succ] at hx
      have hp : 0<16^m := Nat.pow_pos (by decide)
      omega
    let K := 16^m*(B+digit d*A)
    have htotal : x+digit d*r+num d p y=16*K+offset d := by
      unfold num
      calc
        x+digit d*r+(y+digit d*p+offset d) =
            (x+y)+digit d*(r+p)+offset d := by rw [Nat.mul_add]; omega
        _ = 16*K+offset d := by
          rw [hxsum,hrsum,Nat.pow_succ]
          dsimp [K]
          simp only [Nat.mul_add]
          ac_rfl
    have hn : 16*nextY d p y=num d p y := by
      have hh := Nat.mod_add_div (num d p y) 16
      unfold nextY
      omega
    rw [←hn] at htotal
    have hOff : offset d≤digit d*r := by
      cases d <;> simp [digit,offset] <;> omega
    have hyK : nextY d p y≤K := by omega
    let X := K-nextY d p y
    let R := r-cost d
    have hr : r=R+cost d := by
      have hcost : cost d≤6 := by cases d <;> decide
      dsimp [R]; omega
    have he : 16*X+offset d=x+digit d*r := by dsimp [X]; omega
    have hcone := cone_back d x r X R hxbig hc hr he
    have hX : 25*16^m≤X := by rw [Nat.pow_succ] at hx; omega
    have hr' : R+nextP d p=16^m*(16*A) := by
      have hh : 16^(m+1)*A=16^m*(16*A) := by rw [Nat.pow_succ,Nat.mul_assoc]
      unfold nextP
      omega
    have hx' : X+nextY d p y=16^m*(B+digit d*A) := by dsimp [X,K]; omega
    obtain ⟨X',R',hRun,hX',hC',hR',hSum'⟩ :=
      ih X R (16*A) (B+digit d*A) hX hcone.2 hr' hx'
    refine ⟨X',R',?_,hX',hC',?_,?_⟩
    · have hstep := macro_converse d x r X R hxbig hc hr he
      rw [show 4*(m+1)=4*m+4 by omega,BB429.run_add,hRun]
      exact hstep
    · rw [hR',Nat.pow_succ,Nat.mul_assoc]
    · rw [hSum',Nat.mul_add]
      ac_rfl

/-- The forward signed lift retains the actual rooted endpoint rather
than merely forgetting it into a path-existence predicate. -/
theorem rooted_path_end {Reach : Nat → Nat → Prop} (src : Source Reach) :
    ∀ m a b r x p y A B : Nat, Reach a b → a+3=4*x → 2*a+b+1=4*r →
      25*16^m≤x → 3*x≤r → r+p=16^m*A → x+y=16^m*B →
      ∃ P Y D X R, PathEnd m p y P Y D ∧
        Reach (original X R).1 (original X R).2 ∧
        25≤X ∧ 3*X≤R ∧ R+P=16^m*A ∧ X+Y=B+A*D := by
  intro m
  induction m with
  | zero =>
    intro a b r x p y A B hr ha hb hx hc hP hQ
    have he : original x r=(a,b) := by unfold original stateAR; congr 1 <;> omega
    refine ⟨p,y,0,x,r,.nil _ _,?_,?_,hc,?_,?_⟩
    · simpa [he] using hr
    all_goals simp at * <;> omega
  | succ m ih =>
    intro a b r x p y A B hr ha hb hx hc hP hQ
    have hm : 0<16^m := Nat.pow_pos (by decide)
    have hx' : 400≤x := by rw [Nat.pow_succ] at hx; omega
    obtain ⟨d,a',b',r',x',hr',ha',hb',hrcost,hxstep,hxle⟩ :=
      macro_back src a b r x hx' ha hb hr
    have hcone := cone_back d x r x' r' hx' hc hrcost hxstep
    have hnum : 16*x'+num d p y=16^(m+1)*(B+digit d*A) := by
      unfold num
      calc
        16*x'+(y+digit d*p+offset d) = (x+y)+digit d*(r+p) := by
          rw [Nat.mul_add]; omega
        _ = 16^(m+1)*(B+digit d*A) := by rw [hP,hQ,Nat.mul_add]; ac_rfl
    have hnum' : 16*x'+num d p y=16*(16^m*(B+digit d*A)) := by
      rw [hnum,Nat.pow_succ]; ac_rfl
    have hdiv : num d p y%16=0 := by omega
    have hsum : x'+nextY d p y=16^m*(B+digit d*A) := by
      have ht := Nat.mod_add_div (num d p y) 16
      unfold nextY
      omega
    have hrank : r'+nextP d p=16^m*(16*A) := by
      unfold nextP
      have hp : 16^(m+1)*A=16^m*(16*A) := by rw [Nat.pow_succ,Nat.mul_assoc]
      omega
    have hxlo : 25*16^m≤x' := by rw [Nat.pow_succ] at hx; omega
    obtain ⟨P,Y,D,X,R,hend,hreach,hX,hC,hR,hS⟩ :=
      ih a' b' r' x' (nextP d p) (nextY d p y) (16*A) (B+digit d*A)
        hr' ha' hb' hxlo hcone.2 hrank hsum
    refine ⟨P,Y,digit d+16*D,X,R,.cons d hdiv hend,hreach,hX,hC,?_,?_⟩
    · rw [hR,Nat.pow_succ,Nat.mul_assoc]
    · rw [hS,Nat.mul_add]; ac_rfl

def Rooted (a b : Nat) : Prop := ∃ n, BB429.run n (0,0)=some (a,b)

private theorem q0_coordinates (u n a b : Nat)
    (hn : n=23+32*u) (ha : a+24*u+19=13*2^n) (hb : b+13=2*a) :
    ∃ x r, a+3=4*x ∧ 2*a+b+1=4*r ∧ 25*16^(8*u+5)≤x ∧ 3*x≤r ∧
      r+(24*u+22)=16^(8*u+5)*104 ∧ x+(6*u+4)=16^(8*u+5)*26 := by
  let m := 8*u+5
  let p := 24*u+22
  let y := 6*u+4
  have hn' : n=4*m+3 := by dsimp [m]; omega
  have hpw : 2^n=8*16^m := by
    rw [hn',Nat.pow_add,Nat.pow_mul]
    change 16^m*8=8*16^m
    omega
  have hp0 (m : Nat) : m+1≤16^m := by
    induction m with
    | zero => decide
    | succ m ih => rw [Nat.pow_succ]; omega
  have hy : y≤16^m := by have hh := hp0 m; dsimp [m,y] at *; omega
  have hp : p≤104*16^m := by dsimp [m,p] at *; have hh := hp0 m; omega
  let x := 26*16^m-y
  let r := 104*16^m-p
  rw [hpw] at ha
  refine ⟨x,r,?_,?_,?_,?_,?_,?_⟩ <;> dsimp [x,r,m,p,y] at * <;> omega

/-- A complete signed q0 path is sufficient for a real accelerator
ancestry of length 4m from a prepared, explicitly constrained endpoint. -/
theorem q0_prepared_ancestry (u n a b : Nat)
    (hn : n=23+32*u) (ha : a+24*u+19=13*2^n) (hb : b+13=2*a)
    (h : Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ P Y D X R,
      PathEnd (8*u+5) (24*u+22) (6*u+4) P Y D ∧
      BB429.run (4*(8*u+5)) (original X R)=some (a,b) ∧
      25≤X ∧ 3*X≤R ∧ R+P=104*16^(8*u+5) ∧ X+Y=26+104*D := by
  obtain ⟨x,r,hax,hbr,hx,hc,hp,hy⟩ := q0_coordinates u n a b hn ha hb
  have he : original x r=(a,b) := by unfold original stateAR; congr 1 <;> omega
  obtain ⟨P,Y,D,hend⟩ := path_end_exists h
  obtain ⟨X,R,hRun,hX,hC,hR,hSum⟩ := path_end_lift hend x r 104 26 hx hc hp hy
  rw [he] at hRun
  exact ⟨P,Y,D,X,R,hend,hRun,hX,hC,by simpa [Nat.mul_comm] using hR,hSum⟩

/-- Exact root-preserving reduction. In contrast to path existence alone,
the final condition retains the real blank-origin reachability question.
The Source hypothesis is definitionally the interface already instantiated
for BB429NewResidue.Reach by Q0MacroSource. -/
theorem q0_rooted_iff_endpoint (src : Source Rooted) (u n a b : Nat)
    (hn : n=23+32*u) (ha : a+24*u+19=13*2^n) (hb : b+13=2*a) :
    Rooted a b ↔ ∃ P Y D X R,
      PathEnd (8*u+5) (24*u+22) (6*u+4) P Y D ∧
      Rooted (original X R).1 (original X R).2 ∧
      25≤X ∧ 3*X≤R ∧ R+P=104*16^(8*u+5) ∧ X+Y=26+104*D := by
  obtain ⟨x,r,hax,hbr,hx,hc,hp,hy⟩ := q0_coordinates u n a b hn ha hb
  constructor
  · intro hr
    obtain ⟨P,Y,D,X,R,hend,hReach,hX,hC,hR,hS⟩ :=
      rooted_path_end src (8*u+5) a b r x (24*u+22) (6*u+4) 104 26
        hr hax hbr hx hc hp hy
    exact ⟨P,Y,D,X,R,hend,hReach,hX,hC,by simpa [Nat.mul_comm] using hR,hS⟩
  · rintro ⟨P,Y,D,X,R,hend,hReach,hX,hC,hR,hS⟩
    obtain ⟨X',R',hRun,_,_,hR',hS'⟩ := path_end_lift hend x r 104 26 hx hc hp hy
    have heX : X'=X := by omega
    have heR : R'=R := by rw [Nat.mul_comm] at hR'; omega
    rw [heX,heR] at hRun
    have he : original x r=(a,b) := by unfold original stateAR; congr 1 <;> omega
    rw [he] at hRun
    obtain ⟨k,hk⟩ := hReach
    refine ⟨k+4*(8*u+5),?_⟩
    rw [BB429.run_add,hk]
    exact hRun

#print axioms macro_converse
#print axioms path_end_lift
#print axioms q0_prepared_ancestry
#print axioms rooted_path_end
#print axioms q0_rooted_iff_endpoint
end BB429Q0Macro
