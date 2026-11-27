import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw47Complement3423
open BB6Coverage BB6Coverage.Agent31Pump

def ctr : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def zz : List Bool := [false,false]
def oo : List Bool := [true,true]
def zo : List Bool := [false,true]
def oz : List Bool := [true,false]

def packL : List Bool → List Bool
  | [] => []
  | b::d => [false,b] ++ packL d

def packR : List Bool → List Bool
  | [] => []
  | b::w => [true,b] ++ packR w

-- The blank left ray is represented by [], not an extra explicit zero.
def left0 : List Bool → List Bool
  | [] => []
  | b::d => false :: packL (b::d)

def cfg (k : Nat) (d w T : List Bool) : Z0 :=
  ⟨0,left0 d,rep oo (k+1) ++ zz ++ packR w ++ zo ++ T⟩

theorem packL_zeros (n : Nat) (d : List Bool) :
    packL (List.replicate n false ++ d) = rep zz n ++ packL d := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,packL,rep,ih,List.append_assoc,zz]

theorem packR_zeros (n : Nat) (d : List Bool) :
    packR (List.replicate n false ++ d) = rep oz n ++ packR d := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,packR,rep,ih,List.append_assoc,oz]

theorem packR_ones (n : Nat) (d : List Bool) :
    packR (List.replicate n true ++ d) = rep oo n ++ packR d := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,packR,rep,ih,List.append_assoc,oo]

theorem zeroComm (n : Nat) : [false] ++ rep zz n = rep zz n ++ [false] := by
  exact rotate false [false] n

theorem oneComm (n : Nat) : [true] ++ rep oo n = rep oo n ++ [true] := by
  exact rotate true [true] n

-- A0 and B erase the leading even run of ones, then write a delimiter.
theorem enterC (k : Nat) (d R : List Bool) :
    run0 ctr (2*k+4) ⟨0,left0 d,rep oo (k+1) ++ zz ++ R⟩ =
      some ⟨2,[false,true] ++ rep zz (k+1) ++ [true] ++ packL d,R⟩ := by
  have h1 : run0 ctr 1 ⟨0,left0 d,rep oo (k+1) ++ zz ++ R⟩ =
      some ⟨1,[true,true] ++ packL d,[true] ++ rep oo k ++ zz ++ R⟩ := by
    cases d <;> rfl
  have h2 : run0 ctr (2*k) ⟨1,[true,true] ++ packL d,[true] ++ rep oo k ++ zz ++ R⟩ =
      some ⟨1,[true] ++ rep zz k ++ [true] ++ packL d,[true] ++ zz ++ R⟩ := by
    simpa only [List.append_assoc] using
      sweepR ctr 1 [true] [true] oo zz 2 (by intro L R; rfl) k ([true] ++ packL d) (zz ++ R)
  have h3 : run0 ctr 3 ⟨1,[true] ++ rep zz k ++ [true] ++ packL d,[true] ++ zz ++ R⟩ =
      some ⟨2,[false,true] ++ rep zz (k+1) ++ [true] ++ packL d,R⟩ := rfl
  have H := join0 (join0 h1 h2) h3
  rw [show 1+2*k+3=2*k+4 by omega] at H
  exact H

-- The first one of the right-hand counter is cleared; all preceding
-- zero digits become ones.  The left counter receives k zeros and a one.
theorem decrementPrefix (k j : Nat) (d R : List Bool) :
    run0 ctr (2*k+4*j+14) ⟨0,left0 d,rep oo (k+1) ++ zz ++ rep oz j ++ oo ++ R⟩ =
      some ⟨0,[true] ++ packL (List.replicate k false ++ true::d),
        zz ++ rep oo j ++ oz ++ R⟩ := by
  have h1 := enterC k d (rep oz j ++ oo ++ R)
  have h2 : run0 ctr (2*j)
      ⟨2,[false,true] ++ rep zz (k+1) ++ [true] ++ packL d,rep oz j ++ oo ++ R⟩ =
      some ⟨2,[false] ++ rep zz j ++ [true] ++ rep zz (k+1) ++ [true] ++ packL d,oo ++ R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepR ctr 2 [false] [] oz zz 2 (by intro L R; rfl) j
        ([true] ++ rep zz (k+1) ++ [true] ++ packL d) (oo ++ R)
  have h3 : run0 ctr 3
      ⟨2,[false] ++ rep zz j ++ [true] ++ rep zz (k+1) ++ [true] ++ packL d,oo ++ R⟩ =
      some ⟨4,rep zz (j+1) ++ [true] ++ rep zz (k+1) ++ [true] ++ packL d,[false] ++ R⟩ := rfl
  have h4 : run0 ctr (2*(j+1))
      ⟨4,rep zz (j+1) ++ [true] ++ rep zz (k+1) ++ [true] ++ packL d,[false] ++ R⟩ =
      some ⟨4,[true] ++ rep zz (k+1) ++ [true] ++ packL d,rep oo (j+1) ++ [false] ++ R⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepL ctr 4 [] [] zz oo 2 (by intro L R; rfl) (j+1)
        ([true] ++ rep zz (k+1) ++ [true] ++ packL d) ([false] ++ R)
  have h5 : run0 ctr 1
      ⟨4,[true] ++ rep zz (k+1) ++ [true] ++ packL d,rep oo (j+1) ++ [false] ++ R⟩ =
      some ⟨0,rep zz (k+1) ++ [true] ++ packL d,[false] ++ rep oo (j+1) ++ [false] ++ R⟩ := rfl
  have h6 : run0 ctr 4
      ⟨0,rep zz (k+1) ++ [true] ++ packL d,[false] ++ rep oo (j+1) ++ [false] ++ R⟩ =
      some ⟨0,[true,false] ++ rep zz k ++ [true] ++ packL d,
        zz ++ [true] ++ rep oo j ++ [false] ++ R⟩ := rfl
  have hL : [true,false] ++ rep zz k ++ [true] ++ packL d =
      [true] ++ packL (List.replicate k false ++ true::d) := by
    calc
      _ = [true] ++ ([false] ++ rep zz k) ++ [true] ++ packL d := by simp only [List.append_assoc] <;> rfl
      _ = [true] ++ (rep zz k ++ [false]) ++ [true] ++ packL d := by rw [zeroComm]
      _ = _ := by simp only [packL_zeros,packL,List.append_assoc] <;> rfl
  have hR : zz ++ [true] ++ rep oo j ++ [false] ++ R =
      zz ++ rep oo j ++ oz ++ R := by
    calc
      _ = zz ++ ([true] ++ rep oo j) ++ [false] ++ R := by simp only [List.append_assoc]
      _ = zz ++ (rep oo j ++ [true]) ++ [false] ++ R := by rw [oneComm]
      _ = _ := by simp only [List.append_assoc] <;> rfl
  rw [hL,hR] at h6
  have H := join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6
  rw [show 2*k+4+2*j+3+2*(j+1)+1+4 = 2*k+4*j+14 by omega] at H
  exact H

-- On exhaustion, the right counter is refilled with k+1 ones and a
-- longer tail, and the left ray is reset to blank.
theorem resetPrefix (k n : Nat) (T : List Bool) :
    run0 ctr (4*k+4*n+19) (cfg k [] (List.replicate n false) T) =
      some (cfg 0 [] (List.replicate (k+1) true) (rep oo n ++ [true] ++ T)) := by
  have h1 : run0 ctr (2*k+4) (cfg k [] (List.replicate n false) T) =
      some ⟨2,[false,true] ++ rep zz (k+1) ++ [true],rep oz n ++ zo ++ T⟩ := by
    simpa only [cfg,packR_zeros,packR,packL,List.append_nil,List.append_assoc] using
      enterC k [] (rep oz n ++ zo ++ T)
  have h2 : run0 ctr (2*n)
      ⟨2,[false,true] ++ rep zz (k+1) ++ [true],rep oz n ++ zo ++ T⟩ =
      some ⟨2,[false] ++ rep zz n ++ [true] ++ rep zz (k+1) ++ [true],zo ++ T⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepR ctr 2 [false] [] oz zz 2 (by intro L R; rfl) n
        ([true] ++ rep zz (k+1) ++ [true]) (zo ++ T)
  have h3 : run0 ctr 1
      ⟨2,[false] ++ rep zz n ++ [true] ++ rep zz (k+1) ++ [true],zo ++ T⟩ =
      some ⟨3,rep zz (n+1) ++ [true] ++ rep zz (k+1) ++ [true],[true] ++ T⟩ := rfl
  have h4 : run0 ctr (2*(n+1))
      ⟨3,rep zz (n+1) ++ [true] ++ rep zz (k+1) ++ [true],[true] ++ T⟩ =
      some ⟨3,[true] ++ rep zz (k+1) ++ [true],rep oo (n+1) ++ [true] ++ T⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepL ctr 3 [] [] zz oo 2 (by intro L R; rfl) (n+1)
        ([true] ++ rep zz (k+1) ++ [true]) ([true] ++ T)
  have h5 : run0 ctr 2
      ⟨3,[true] ++ rep zz (k+1) ++ [true],rep oo (n+1) ++ [true] ++ T⟩ =
      some ⟨4,[false] ++ rep zz (k+1) ++ [true],zo ++ rep oo n ++ [true] ++ T⟩ := rfl
  have hL : [false] ++ rep zz (k+1) ++ [true] = rep zz (k+1) ++ [false,true] := by
    calc
      _ = ([false] ++ rep zz (k+1)) ++ [true] := by simp only [List.append_assoc]
      _ = (rep zz (k+1) ++ [false]) ++ [true] := by rw [zeroComm]
      _ = _ := by simp only [List.append_assoc] <;> rfl
  rw [hL] at h5
  have h6 : run0 ctr (2*(k+1))
      ⟨4,rep zz (k+1) ++ [false,true],zo ++ rep oo n ++ [true] ++ T⟩ =
      some ⟨4,[false,true],rep oo (k+1) ++ zo ++ rep oo n ++ [true] ++ T⟩ := by
    simpa only [List.nil_append,List.append_assoc] using
      sweepL ctr 4 [] [] zz oo 2 (by intro L R; rfl) (k+1)
        [false,true] (zo ++ rep oo n ++ [true] ++ T)
  have h7 : run0 ctr 8
      ⟨4,[false,true],rep oo (k+1) ++ zo ++ rep oo n ++ [true] ++ T⟩ =
      some ⟨0,[],oo ++ zz ++ rep oo (k+1) ++ zo ++ rep oo n ++ [true] ++ T⟩ := rfl
  have H := join0 (join0 (join0 (join0 (join0 (join0 h1 h2) h3) h4) h5) h6) h7
  rw [show 2*k+4+2*n+1+2*(n+1)+2+2*(k+1)+8 = 4*k+4*n+19 by omega] at H
  simpa only [cfg,left0,packR_ones,packR,List.append_nil,List.append_assoc,rep] using H

-- Canonical finite low-endian left digits: no redundant final zero.
def Valid : List Bool → Prop
  | [] => True
  | b::d => Valid d ∧ (b = true ∨ d ≠ [])

def val : List Bool → Nat
  | [] => 0
  | b::d => (if b then 1 else 0) + 2*val d

def carry : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::d => (0,d)
  | true::d => ((carry d).1+1,(carry d).2)

theorem validPush (k : Nat) (d : List Bool) (hd : Valid d) :
    Valid (List.replicate k false ++ true::d) := by
  induction k with
  | zero => exact ⟨hd,Or.inl rfl⟩
  | succ k ih =>
    change Valid (false :: (List.replicate k false ++ true::d))
    refine ⟨ih,Or.inr ?_⟩
    intro h
    have he := congrArg List.length h
    simp at he <;> omega

theorem carryValid (d : List Bool) (hd : Valid d) : Valid (carry d).2 := by
  induction d with
  | nil => trivial
  | cons b d ih =>
    cases b
    · exact hd.1
    · exact ih hd.1

-- Each A1,F0 pair pops one digit.  The first implicit or explicit
-- zero terminates the carry.  No F1 transition can be consulted.
theorem carryRun (d : List Bool) (hd : Valid d) (R : List Bool) :
    run0 ctr (2*((carry d).1+1)) ⟨0,[true] ++ packL d,R⟩ =
      some ⟨0,left0 (carry d).2,rep oo ((carry d).1+1) ++ R⟩ := by
  induction d generalizing R with
  | nil => rfl
  | cons b d ih =>
    cases b
    · have hn : d ≠ [] := by
        rcases hd.2 with h|h
        · cases h
        · exact h
      cases d with
      | nil => exact False.elim (hn rfl)
      | cons a d => rfl
    · have h1 : run0 ctr 2 ⟨0,[true] ++ packL (true::d),R⟩ =
          some ⟨0,[true] ++ packL d,oo ++ R⟩ := rfl
      have h2 := ih hd.1 (oo ++ R)
      have H := join0 h1 h2
      rw [show 2+2*((carry d).1+1)=2*((carry d).1+1+1) by omega] at H
      have hr : rep oo ((carry d).1+1) ++ (oo ++ R) =
          rep oo ((carry d).1+1+1) ++ R := by
        rw [← List.append_assoc,rep_snoc]
        rfl
      rw [hr] at H
      exact H

theorem valZeros (k : Nat) (d : List Bool) :
    val (List.replicate k false ++ d) = 2^k * val d := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,val,Bool.false_eq_true,if_false,Nat.zero_add,ih,Nat.pow_succ]
    simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

theorem valOnes (k : Nat) (d : List Bool) :
    val (List.replicate k true ++ d)+1 = 2^k * (val d+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,val,if_true]
    calc
      _ = 2 * (val (List.replicate k true ++ d)+1) := by omega
      _ = _ := by rw [ih,Nat.pow_succ]; simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

theorem carryValue (d : List Bool) :
    val d+1 = 2^(carry d).1 * (1+2*val (carry d).2) := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    cases b
    · simp [val,carry,Nat.add_comm]
    · simp only [val,carry,if_true,Nat.pow_succ]
      calc
        _ = 2*(val d+1) := by omega
        _ = _ := by rw [ih]; simp only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

theorem validZero (d : List Bool) (hd : Valid d) (hv : val d=0) : d=[] := by
  induction d with
  | nil => rfl
  | cons b d ih =>
    cases b
    · have hv' : val d=0 := by simp [val] at hv; omega
      have he := ih hd.1 hv'
      rcases hd.2 with h|h
      · cases h
      · exact False.elim (h he)
    · simp [val] at hv <;> omega

theorem powerOdd (k n x : Nat) (h : 2^k*(1+2*x)=2^n) : k=n ∧ x=0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero =>
      simp at h
      exact ⟨rfl,by omega⟩
    | succ k =>
      have he : 2*(2^k*(1+2*x))=1 := by
        simpa only [Nat.pow_succ,Nat.pow_zero,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
      omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [Nat.pow_zero,Nat.one_mul,Nat.pow_succ] at h
      omega
    | succ k =>
      have he : 2*(2^k*(1+2*x))=2*2^n := by
        simpa only [Nat.pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
      obtain ⟨hk,hx⟩ := ih k (by omega)
      exact ⟨by omega,hx⟩

theorem zerosOrOne (w : List Bool) :
    (∃ n, w=List.replicate n false) ∨
      ∃ j s, w=List.replicate j false ++ true::s := by
  induction w with
  | nil => exact Or.inl ⟨0,rfl⟩
  | cons b w ih =>
    cases b
    · rcases ih with ⟨n,rfl⟩|⟨j,s,rfl⟩
      · exact Or.inl ⟨n+1,rfl⟩
      · exact Or.inr ⟨j+1,s,rfl⟩
    · exact Or.inr ⟨0,w,rfl⟩

def Balance (k : Nat) (d w : List Bool) : Prop :=
  2^k*(1+2*val d)+val w=2^w.length

theorem goodStep (k : Nat) (d w T : List Bool) (hd : Valid d) (hb : Balance k d w) :
    ∃ k' d' w' T' t, 0<t ∧ Valid d' ∧ Balance k' d' w' ∧
      run0 ctr t (cfg k d w T) = some (cfg k' d' w' T') := by
  rcases zerosOrOne w with ⟨n,rfl⟩|⟨j,s,rfl⟩
  · have hz : val (List.replicate n false)=0 := by
      simpa [val] using valZeros n []
    have he : 2^k*(1+2*val d)=2^n := by
      simpa only [Balance,hz,Nat.add_zero,List.length_replicate] using hb
    obtain ⟨hk,hv⟩ := powerOdd k n (val d) he
    subst k
    have hnil := validZero d hd hv
    subst d
    refine ⟨0,[],List.replicate (n+1) true,rep oo n ++ [true] ++ T,
      4*n+4*n+19,by omega,trivial,?_,resetPrefix n n T⟩
    have H := valOnes (n+1) []
    simpa [Balance,val,Nat.add_comm] using H
  · let pushed := List.replicate k false ++ true::d
    let w' := List.replicate j true ++ false::s
    have hp : Valid pushed := validPush k d hd
    have h1 : run0 ctr (2*k+4*j+14) (cfg k d (List.replicate j false ++ true::s) T) =
        some ⟨0,[true] ++ packL pushed,zz ++ packR w' ++ zo ++ T⟩ := by
      simpa only [cfg,pushed,w',packR_zeros,packR_ones,packR,List.append_assoc,oo,oz] using
        decrementPrefix k j d (packR s ++ zo ++ T)
    have h2 : run0 ctr (2*((carry pushed).1+1))
        ⟨0,[true] ++ packL pushed,zz ++ packR w' ++ zo ++ T⟩ =
        some (cfg (carry pushed).1 (carry pushed).2 w' T) :=
      carryRun pushed hp (zz ++ packR w' ++ zo ++ T)
    refine ⟨(carry pushed).1,(carry pushed).2,w',T,
      2*k+4*j+14+2*((carry pushed).1+1),by omega,carryValid pushed hp,?_,join0 h1 h2⟩
    have hm : val pushed = 2^k*(1+2*val d) := by simp only [pushed,valZeros,val,if_true]
    have hc := carryValue pushed
    have hv1 : val (List.replicate j false ++ true::s)=2^j*(1+2*val s) := by simp only [valZeros,val,if_true]
    have hv2 : val w'+1=2^j*(1+2*val s) := by
      simpa [w',val,Nat.add_comm] using valOnes j (false::s)
    have hl : w'.length=(List.replicate j false ++ true::s).length := by simp [w']
    unfold Balance at hb ⊢
    rw [← hc,hm,hl]
    omega

theorem entry : run0 ctr 15 ⟨0,[],[]⟩ = some (cfg 0 [] [] []) := rfl

theorem arbitrarilyLive (n : Nat) :
    ∃ k d w T t, n≤t ∧ Valid d ∧ Balance k d w ∧
      run0 ctr t ⟨0,[],[]⟩ = some (cfg k d w T) := by
  induction n with
  | zero => exact ⟨0,[],[],[],15,by omega,trivial,by rfl,entry⟩
  | succ n ih =>
    obtain ⟨k,d,w,T,t,ht,hd,hb,hr⟩ := ih
    obtain ⟨k',d',w',T',u,hu,hd',hb',hs⟩ := goodStep k d w T hd hb
    exact ⟨k',d',w',T',t+u,by omega,hd',hb',join0 hr hs⟩

theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m := by
  intro n
  obtain ⟨k,d,w,T,t,ht,_,_,hr⟩ := arbitrarilyLive n
  have hz : (Agent50Zipper.zrun ctr t start).map project = some (cfg k d w T) :=
    (run_project ctr t start).trans hr
  cases h : Agent50Zipper.zrun ctr t start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound ctr m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms decrementPrefix
#print axioms resetPrefix
#print axioms goodStep
#print axioms never
end BB6.Agent12Raw47Complement3423
