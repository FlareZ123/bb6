import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LEE1LFM3493501834
open BB6Coverage BB6Coverage.Agent31Pump

inductive V where | a | b | c
  deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,if v = .b then 5 else 4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some (if v = .c then ⟨true,true,1⟩ else ⟨false,false,4⟩))
  | _,_ => none

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false
def A (L R : List Bool) : Z0 := ⟨0,false::L,false::R⟩
def C (n : Nat) (L T : List Bool) : Z0 := ⟨2,(ones n++T).headD false::L,(ones n++T).tail⟩
def D (n : Nat) (L R : List Bool) : Z0 := ⟨3,zeros n++true::L,R⟩
def fcost : V → Nat | .c => 3 | _ => 1

private theorem C_sweep (v : V) (n : Nat) (L T : List Bool) :
    run0 (table v) n (C n L T) = some ⟨2,T.headD false::(zeros n++L),T.tail⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (C (n+1) L T) = some (C n (false::L) T) := by
      simp only [C,ones,List.replicate_succ,List.cons_append,List.headD_cons,List.tail_cons]
      rfl
    have H := join0 h (ih (false::L))
    rw [Nat.add_comm 1 n] at H
    simpa only [zeros,List.replicate_succ',List.append_assoc,List.singleton_append] using H

private theorem D_sweep (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) n (D n L R) = some (D 0 L (ones n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (D (n+1) L R) = some (D n L (true::R)) := by
      simp only [D,zeros,List.replicate_succ,List.cons_append]
      rfl
    have H := join0 h (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    simpa only [ones,List.replicate_succ',List.append_assoc,List.singleton_append] using H

private theorem prep (v : V) (r : Nat) (L T : List Bool) :
    run0 (table v) (2+r) (A L (ones r++T)) =
      some ⟨2,T.headD false::(zeros r++true::true::L),T.tail⟩ := by
  have h : run0 (table v) 2 (A L (ones r++T)) = some (C r (true::true::L) T) := by rfl
  exact join0 h (C_sweep v r (true::true::L) T)

private theorem long_mid (v : V) (r : Nat) (L T : List Bool)
    (h0 : T.headD false = false) (h1 : T.tail.headD false = false) :
    run0 (table v) (2*r+8+fcost v) (A L (ones r++T)) =
      some ⟨4,L,false::(ones (r+3)++T.tail.tail)⟩ := by
  have a := prep v r L T
  rw [h0] at a
  have b : run0 (table v) 1 ⟨2,false::(zeros r++true::true::L),T.tail⟩ =
      some (D (r+2) (true::L) T.tail.tail) := by
    simp only [run0,step0,table,Option.bind_some,id,Option.map_some,move0,ite_true,List.headD_cons,List.tail_cons,h1,D,zeros,List.replicate_succ,List.cons_append]
    rfl
  have c := D_sweep v (r+2) (true::L) T.tail.tail
  have d : run0 (table v) 3 (D 0 (true::L) (ones (r+2)++T.tail.tail)) =
      some ⟨5,true::L,ones (r+3)++T.tail.tail⟩ := by
    simp only [D,zeros,ones,List.replicate_zero,List.replicate_succ,List.nil_append,List.cons_append]
    rfl
  have e : run0 (table v) (fcost v) ⟨5,true::L,ones (r+3)++T.tail.tail⟩ =
      some ⟨4,L,false::(ones (r+3)++T.tail.tail)⟩ := by
    cases v <;> simp only [fcost,ones,List.replicate_succ,List.cons_append] <;> rfl
  have H := join0 (join0 (join0 (join0 a b) c) d) e
  rw [show 2*r+8+fcost v = 2+r+1+(r+2)+3+fcost v by omega]
  exact H

private theorem pair_step (v : V) (L R : List Bool) :
    run0 (table v) 2 ⟨4,[]++[true,true]++L,[]++R⟩ =
      some ⟨4,[]++L,[]++[false,false]++R⟩ := by cases v <;> rfl

private theorem rep_pair (b : Bool) (j : Nat) :
    rep [b,b] j = List.replicate (2*j) b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rep,ih,show 2*(j+1)=2*j+2 by omega]
    simp only [List.replicate_succ,List.cons_append,List.nil_append]

private theorem long (v : V) (r j : Nat) (U T : List Bool)
    (h0 : T.headD false = false) (h1 : T.tail.headD false = false) :
    run0 (table v) (2*r+8+fcost v+2*j+2)
      (A (ones (2*j)++[false,false,false]++U) (ones r++T)) =
      some (A U (true::(zeros (2*j+1)++ones (r+3)++T.tail.tail))) := by
  have a := long_mid v r (ones (2*j)++[false,false,false]++U) T h0 h1
  have b := sweepL (table v) 4 [] [] [true,true] [false,false] 2 (pair_step v) j
    ([false,false,false]++U) (false::(ones (r+3)++T.tail.tail))
  have b' : run0 (table v) (2*j) ⟨4,ones (2*j)++[false,false,false]++U,false::(ones (r+3)++T.tail.tail)⟩ =
      some ⟨4,[false,false,false]++U,zeros (2*j+1)++ones (r+3)++T.tail.tail⟩ := by
    have h : zeros (2*j)++[false] = zeros (2*j+1) := by simp only [zeros,List.replicate_succ']
    rw [← h]
    simpa only [List.nil_append,rep_pair,ones,zeros,List.append_assoc,List.singleton_append,List.cons_append] using b
  have c : run0 (table v) 2 ⟨4,[false,false,false]++U,zeros (2*j+1)++ones (r+3)++T.tail.tail⟩ =
      some (A U (true::(zeros (2*j+1)++ones (r+3)++T.tail.tail))) := by rfl
  exact join0 (join0 a b') c

private theorem short (v : V) (r : Nat) (L R : List Bool) :
    run0 (table v) (r+8) (A L (ones (r+1)++[false,true,true]++R)) =
      some ⟨0,zeros (r+1)++true::true::L,false::true::true::R⟩ := by
  have a := prep v (r+1) L ([false,true,true]++R)
  have b : run0 (table v) 5 ⟨2,false::(zeros (r+1)++true::true::L),true::true::R⟩ =
      some ⟨0,zeros (r+1)++true::true::L,false::true::true::R⟩ := by
    simp only [zeros,List.replicate_succ,List.cons_append]
    rfl
  have H := join0 a b
  rw [show r+8=2+(r+1)+5 by omega]
  simpa only [List.append_assoc] using H

#print axioms long
#print axioms short

-- A left token is either a pair of ones or a triple of zeros.
def token (b : Bool) : List Bool := if b then [true,true] else [false,false,false]
def encode : List Bool → List Bool
  | [] => []
  | b::bs => token b ++ encode bs

private theorem encode_append (xs ys : List Bool) : encode (xs++ys) = encode xs++encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]

private theorem encode_zeros (k : Nat) : encode (List.replicate k false) = zeros (3*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,encode,ih,show 3*(k+1)=3*k+3 by omega]
    simp only [token,Bool.false_eq_true,ite_false,zeros,List.replicate_succ,List.cons_append,List.nil_append]

private theorem left_cut (ds : List Bool) (U : List Bool) :
    ∃ j ds', encode ds++token false++U = ones (2*j)++token false++encode ds'++U := by
  induction ds with
  | nil => exact ⟨0,[],rfl⟩
  | cons b ds ih =>
    cases b with
    | false =>
      exact ⟨0,ds++[false],by simp only [encode,encode_append,List.append_nil,List.append_assoc,ones,Nat.mul_zero,List.replicate_zero,List.nil_append]⟩
    | true =>
      obtain ⟨j,ds',h⟩ := ih
      refine ⟨j+1,ds',?_⟩
      have H := congrArg (fun x => token true++x) h
      rw [show 2*(j+1)=2*j+2 by omega]
      simpa only [encode,token,ite_true,ones,List.replicate_succ,List.append_assoc,List.cons_append,List.nil_append] using H

-- All noninitial right runs have at least two ones.  Interior run lengths
-- are 1 modulo 3, while the terminal run is 0 modulo 3.
inductive Right where
  | terminal (m : Nat)
  | node (k s : Nat) (tail : Right)

def firstLen : Right → Nat
  | .terminal m => 3*m
  | .node k _ _ => 3*k+1

def valid : Right → Prop
  | .terminal _ => True
  | .node _ _ tail => 2≤firstLen tail ∧ valid tail

def word : Right → List Bool
  | .terminal m => ones (3*m)
  | .node k s tail => ones (3*k+1)++zeros (2*s+1)++word tail

private theorem large_word (r : Right) (h : 2≤firstLen r) : ∃ R, word r = true::true::R := by
  cases r with
  | terminal m =>
    simp only [firstLen] at h
    have he : 3*m=(3*m-2)+2 := by omega
    refine ⟨ones (3*m-2),?_⟩
    rw [word,he]
    rfl
  | node k s tail =>
    simp only [firstLen] at h
    have he : 3*k+1=(3*k-1)+2 := by omega
    refine ⟨ones (3*k-1)++zeros (2*s+1)++word tail,?_⟩
    rw [word,he]
    rfl

/-- One positive-cost section step preserves both stack grammars, with at
    most one additional reserved zero token required on the left. -/
theorem advance (v : V) (ds : List Bool) (r : Right) (hr : valid r) (U : List Bool) :
    ∃ t ds' r', 0<t ∧ valid r' ∧
      run0 (table v) t (A (encode ds++token false++U) (word r)) =
      some (A (encode ds'++U) (word r')) := by
  cases r with
  | terminal m =>
    obtain ⟨j,ds',h⟩ := left_cut ds U
    have H := long v (3*m) j (encode ds'++U) [] rfl rfl
    refine ⟨2*(3*m)+8+fcost v+2*j+2,ds',.node 0 j (.terminal (m+1)),by omega,?_ ,?_⟩
    · simp only [valid,firstLen]; exact ⟨by omega,trivial⟩
    · rw [h]
      have he : 3*(m+1)=3*m+3 := by omega
      simpa only [token,Bool.false_eq_true,ite_false,word,he,ones,Nat.mul_zero,Nat.zero_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,List.tail_nil] using H
  | node k s tail =>
    obtain ⟨hlarge,hvalid⟩ := hr
    cases s with
    | zero =>
      obtain ⟨R,hR⟩ := large_word tail hlarge
      have H := short v (3*k) (encode ds++token false++U) R
      refine ⟨3*k+8,List.replicate k false++true::(ds++[false]),tail,by omega,hvalid,?_⟩
      rw [word,hR]
      simpa only [encode_append,encode,encode_zeros,A,token,ite_true,Bool.false_eq_true,ite_false,zeros,Nat.mul_zero,Nat.zero_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H
    | succ s =>
      obtain ⟨j,ds',h⟩ := left_cut ds U
      let T := false::false::(zeros (2*s+1)++word tail)
      have H := long v (3*k+1) j (encode ds'++U) T rfl rfl
      refine ⟨2*(3*k+1)+8+fcost v+2*j+2,ds',.node 0 j (.node (k+1) s tail),by omega,?_ ,?_⟩
      · simp only [valid,firstLen]; exact ⟨by omega,hlarge,hvalid⟩
      · rw [h]
        have he : 3*(k+1)+1=3*k+1+3 := by omega
        have hf : 2*(s+1)+1=(2*s+1)+2 := by omega
        simpa only [token,Bool.false_eq_true,ite_false,word,he,hf,T,List.tail_cons,ones,zeros,Nat.mul_zero,Nat.zero_add,List.replicate_succ,List.replicate_zero,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using H

theorem epochs (v : V) (N : Nat) (ds : List Bool) (r : Right) (hr : valid r) :
    ∃ t u, N≤t ∧ run0 (table v) t (A (encode ds++zeros (3*N)) (word r)) = some u := by
  induction N generalizing ds r with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hp : zeros (3*(N+1)) = token false++zeros (3*N) := by
      change List.replicate (3*(N+1)) false = List.replicate 3 false++List.replicate (3*N) false
      rw [List.replicate_append_replicate]; congr 1 <;> omega
    obtain ⟨a,ds',r',ha,hr',h1⟩ := advance v ds r hr (zeros (3*N))
    obtain ⟨b,u,hb,h2⟩ := ih ds' r' hr'
    exact ⟨a+b,u,by omega,by simpa only [hp,List.append_assoc] using join0 h1 h2⟩

theorem padded_live (v : V) (N : Nat) :
    ∃ t u, N≤t ∧ run0 (table v) t ⟨0,zeros (3*N+1),[false]⟩ = some u := by
  simpa only [A,encode,List.nil_append,word,ones,zeros,Nat.mul_zero,List.replicate_zero,List.replicate_succ] using epochs v N [] (.terminal 0) trivial

open BB6Coverage.Agent50Zipper

private theorem getD_zeros (k i : Nat) : (zeros k).getD i false = false := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem padded_blank (a b : Nat) : embed ⟨0,0,zeros a,zeros b⟩ = blank := by
  unfold embed blank
  congr 1
  funext x
  unfold atCell
  split <;> simp only [getD_zeros]

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live v n
  let start : Z := ⟨0,0,zeros (3*n+1),zeros 1⟩
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    have hb : embed start = blank := padded_blank _ _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms advance
#print axioms never
end BB6.Agent25Raw43B1LEE1LFM3493501834
