import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LEE1LFTriple
open BB6Coverage BB6Coverage.Agent31Pump

-- 0=i330, 1=i331, 2=i396. The other entries are identical.
def table (v : Fin 3) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some (if v.val=0 then ⟨true,false,5⟩ else ⟨true,true,3⟩))
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some (if v.val=2 then ⟨true,false,0⟩ else ⟨false,true,1⟩))
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def P : List Bool := [false,true]
def Q : List Bool := [false,false,true]
def J : List Bool := [true,false]
def digit (b : Bool) : List Bool := if b then Q else P
def bits (w : List Bool) : List Bool := w.flatMap digit
def pre (b : Bool) : List Bool := if b then [false,true] else [true]
def F (L w : List Bool) : Z0 := ⟨5,L,true::bits w⟩
def B (L R : List Bool) : Z0 := ⟨1,false::L,R⟩

def Reach (v : Fin 3) (a b : Z0) : Prop := ∃ t, run0 (table v) t a = some b
def Pos (v : Fin 3) (a b : Z0) : Prop := ∃ t, 0<t ∧ run0 (table v) t a = some b

theorem reach_refl (v : Fin 3) (a : Z0) : Reach v a a := ⟨0,rfl⟩
theorem reach_trans {v : Fin 3} {a b c : Z0} (h : Reach v a b) (g : Reach v b c) : Reach v a c := by
  obtain ⟨n,hn⟩ := h; obtain ⟨m,hm⟩ := g
  exact ⟨n+m,join0 hn hm⟩
theorem pos_reach {v : Fin 3} {a b : Z0} (h : Pos v a b) : Reach v a b := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem reach_pos {v : Fin 3} {a b c : Z0} (h : Reach v a b) (g : Pos v b c) : Pos v a c := by
  obtain ⟨n,hn⟩ := h; obtain ⟨m,hm,hg⟩ := g
  exact ⟨n+m,by omega,join0 hn hg⟩
theorem pos_then {v : Fin 3} {a b c : Z0} (h : Pos v a b) (g : Reach v b c) : Pos v a c := by
  obtain ⟨n,hn,hh⟩ := h; obtain ⟨m,hm⟩ := g
  exact ⟨n+m,by omega,join0 hh hm⟩

-- Finite macros: tails are arbitrary and the proofs are by reduction.
theorem fp (v : Fin 3) (L w : List Bool) : Pos v (F (P++L) w) (F L (false::w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl
  · exact ⟨2,by decide,rfl⟩
  · exact ⟨6,by decide,rfl⟩
  · exact ⟨6,by decide,rfl⟩
theorem fx (v : Fin 3) (L w : List Bool) : Pos v (F ([true,true,false]++L) w) (F L (true::w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨3,by decide,rfl⟩
theorem fx_end (v : Fin 3) (w : List Bool) : Pos v (F [true,true] w) (F [] (true::w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨3,by decide,rfl⟩
theorem fq_start (v : Fin 3) (L w : List Bool) : Pos v (F (Q++L) w) (B ([true,true]++L) (pre false++bits w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨2,by decide,rfl⟩
theorem fn_start (v : Fin 3) (w : List Bool) : Pos v (F [] w) (B [true] (pre false++bits w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨2,by decide,rfl⟩
theorem fj_start (v : Fin 3) (L w : List Bool) : Pos v (F (J++L) w) (B L (pre true++bits w)) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨1,by decide,rfl⟩

theorem b_step (v : Fin 3) (b : Bool) (L R : List Bool) : Pos v (B L (pre b++false::R)) (B (digit b++L) R) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> cases b
  · exact ⟨2,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
  · exact ⟨2,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
  · exact ⟨4,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
theorem b_last (v : Fin 3) (b : Bool) (L : List Bool) : Pos v (B L (pre b)) (B (digit b++L) []) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> cases b
  · exact ⟨2,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
  · exact ⟨2,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
  · exact ⟨4,by decide,rfl⟩
  · exact ⟨3,by decide,rfl⟩
theorem b_end (v : Fin 3) (L : List Bool) : Pos v (B L []) (F L [false]) := by
  have hv : v=0 ∨ v=1 ∨ v=2 := by omega
  rcases hv with rfl|rfl|rfl <;> exact ⟨7,by decide,rfl⟩

theorem bits_append (w u : List Bool) : bits (w++u)=bits w++bits u := by simp [bits,List.flatMap_append]
theorem pre_shift (a b : Bool) (w : List Bool) : pre a++bits (b::w)=pre a++false::(pre b++bits w) := by cases a <;> cases b <;> rfl

theorem b_all (v : Fin 3) (b : Bool) (w L : List Bool) : Pos v (B L (pre b++bits w)) (F (bits w.reverse++digit b++L) [false]) := by
  induction w generalizing b L with
  | nil => simpa [bits] using pos_then (b_last v b L) (pos_reach (b_end v (digit b++L)))
  | cons c w ih =>
    rw [pre_shift]
    have h := b_step v b L (pre c++bits w)
    have g := ih c (digit b++L)
    have H := pos_then h (pos_reach g)
    rw [List.reverse_cons,bits_append]
    simpa only [show bits [c]=digit c by simp [bits],List.append_assoc] using H

theorem fq (v : Fin 3) (L w : List Bool) : Pos v (F (Q++L) w) (F (bits w.reverse++P++[true,true]++L) [false]) := by
  simpa only [digit, Bool.false_eq_true, ite_false,List.append_assoc] using pos_then (fq_start v L w) (pos_reach (b_all v false w ([true,true]++L)))
theorem fn (v : Fin 3) (w : List Bool) : Pos v (F [] w) (F (bits w.reverse++P++[true]) [false]) := by
  exact pos_then (fn_start v w) (pos_reach (b_all v false w [true]))
theorem fj (v : Fin 3) (L w : List Bool) : Pos v (F (J++L) w) (F (bits w.reverse++Q++L) [false]) := by
  exact pos_then (fj_start v L w) (pos_reach (b_all v true w L))
-- With left [1], B's empty left list and the explicit blank in B []
-- are identical after the next right move.
theorem f1 (v : Fin 3) (w : List Bool) : Pos v (F [true] w) (F (bits w.reverse++Q) [false]) := by
  have h : run0 (table v) 2 (F [true] w) = run0 (table v) 2 (F (J++[]) w) := by
    have hv : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases hv with rfl|rfl|rfl <;> rfl
  obtain ⟨t,ht,hr⟩ := fj v [] w
  have ht2 : 2≤t := by
    by_cases hh : 2≤t
    · exact hh
    have he : t=1 := by omega
    subst t
    have hv : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases hv with rfl|rfl|rfl <;>
      change some (B [] (pre true++bits w)) = some (F (bits w.reverse++Q++[]) [false]) at hr <;>
      have bad := congrArg Z0.q (Option.some.inj hr) <;> change (1 : Fin 6)=5 at bad <;> contradiction
  refine ⟨t,ht,?_⟩
  rw [show t=2+(t-2) by omega,run0_add,h,←run0_add,show 2+(t-2)=t by omega]
  simpa using hr

abbrev zs (n : Nat) : List Bool := List.replicate n false
def ps (n : Nat) : List Bool := bits (zs n)
theorem ps_succ (n : Nat) : ps (n+1)=P++ps n := by rfl
theorem ps_add (n m : Nat) : ps (n+m)=ps n++ps m := by
  unfold ps
  change bits (List.replicate (n+m) false)=bits (List.replicate n false)++bits (List.replicate m false)
  rw [←List.replicate_append_replicate,bits_append]
theorem pscan (v : Fin 3) (n : Nat) (L w : List Bool) : Reach v (F (ps n++L) w) (F L (zs n++w)) := by
  induction n generalizing w with
  | zero => exact reach_refl v _
  | succ n ih =>
    rw [ps_succ,List.append_assoc]
    have h := pos_reach (fp v (ps n++L) w)
    have H := reach_trans h (ih (false::w))
    have he : zs n++false::w=zs (n+1)++w := by
      change zs n++(zs 1++w)=zs (n+1)++w
      rw [←List.append_assoc]
      change (List.replicate n false++List.replicate 1 false)++w=List.replicate (n+1) false++w
      rw [List.replicate_append_replicate]
    rw [he] at H
    exact H

inductive Word : List Bool → Prop
  | nil : Word []
  | one : Word [true]
  | two : Word [true,true]
  | p (L : List Bool) : Word L → Word (P++L)
  | j (L : List Bool) : Word L → Word (J++L)
inductive Suffix : List Bool → Prop
  | nil : Suffix []
  | word (L : List Bool) : Word L → Suffix (false::L)

theorem prefix_suffix (m : Nat) (L : List Bool) (h : Word L) : Suffix (ps m++false::L) := by
  induction m generalizing L with
  | zero => exact Suffix.word L h
  | succ m ih =>
    rw [show m+1=1+m by omega,ps_add,List.append_assoc]
    -- Move the leading zero across the all-P prefix, turning each P into J.
    have rot : ∀ n (R : List Bool), ps n++false::R = false::((List.replicate n J).flatten++R) := by
      intro n R
      induction n with
      | zero => rfl
      | succ n ih => rw [ps_succ,List.append_assoc,ih]; rfl
    rw [rot]
    apply Suffix.word
    have wj : ∀ n, Word ((List.replicate n J).flatten++L) := by
      intro n
      induction n with
      | zero => exact h
      | succ n ih => exact Word.j _ ih
    -- The single P is also a J after rotation.
    exact Word.j _ (wj m)

def epoch (n : Nat) (S : List Bool) : Z0 := F (ps n++Q++S) [false]

theorem rev_acc (n m : Nat) : bits (zs m++true::zs n).reverse = ps n++Q++ps m := by
  rw [List.reverse_append,List.reverse_cons]
  change bits ((List.replicate n false).reverse++[true]++(List.replicate m false).reverse) = _
  rw [List.reverse_replicate,List.reverse_replicate,bits_append,bits_append]
  rfl

theorem scan_word (v : Fin 3) (n m : Nat) (L : List Bool) (h : Word L) :
    ∃ S, Suffix S ∧ Pos v (F L (zs m++true::zs n)) (epoch n S) := by
  induction h generalizing m with
  | nil =>
    refine ⟨ps m++P++[true],?_,?_⟩
    · simpa only [List.append_assoc,P,List.cons_append,List.nil_append] using prefix_suffix m [true,true] Word.two
    · have H := fn v (zs m++true::zs n)
      rw [rev_acc] at H
      simpa only [epoch,List.append_assoc] using H
  | one =>
    refine ⟨ps m++Q,?_,?_⟩
    · exact prefix_suffix m P (Word.p [] Word.nil)
    · have H := f1 v (zs m++true::zs n)
      rw [rev_acc] at H
      simpa only [epoch,List.append_assoc] using H
  | two =>
    refine ⟨ps m++Q++P++[true],?_,?_⟩
    · have hW : Word (P++P++[true]) := by simpa only [List.append_assoc] using Word.p (P++[true]) (Word.p [true] Word.one)
      have H := prefix_suffix m (P++P++[true]) hW
      simpa only [List.append_assoc,P,Q,List.cons_append,List.nil_append] using H
    · have H := fn v (true::(zs m++true::zs n))
      have he : bits (true::(zs m++true::zs n)).reverse = (ps n++Q++ps m)++Q := by
        rw [List.reverse_cons,bits_append,rev_acc]; rfl
      rw [he] at H
      have H := pos_then (fx_end v (zs m++true::zs n)) (pos_reach H)
      simpa only [epoch,List.append_assoc] using H
  | p L h ih =>
    have H := fp v L (zs m++true::zs n)
    obtain ⟨S,hS,hR⟩ := ih (m+1)
    exact ⟨S,hS,pos_then H (pos_reach hR)⟩
  | j L h ih =>
    refine ⟨ps m++Q++L,?_,?_⟩
    · have H := prefix_suffix m (P++L) (Word.p L h)
      simpa only [List.append_assoc,P,Q,List.cons_append,List.nil_append] using H
    · have H := fj v L (zs m++true::zs n)
      rw [rev_acc] at H
      simpa only [epoch,List.append_assoc] using H

theorem epoch_step (v : Fin 3) (n : Nat) (S : List Bool) (h : Suffix S) :
    ∃ S', Suffix S' ∧ Pos v (epoch n S) (epoch (n+3) S') := by
  have h0 := pscan v n (Q++S) [false]
  have h1 := fq v S (zs n++[false])
  have hw : zs n++[false]=zs (n+1) := by
    change List.replicate n false++List.replicate 1 false=List.replicate (n+1) false
    exact List.replicate_append_replicate
  have hr : bits (zs n++[false]).reverse++P=ps (n+2) := by
    rw [hw]
    change bits (List.replicate (n+1) false).reverse++P=ps (n+2)
    rw [List.reverse_replicate,ps_add (n+1) 1]; rfl
  have h1' : Pos v (F (Q++S) (zs n++[false])) (F (ps (n+2)++[true,true]++S) [false]) := by
    -- The output has the enlarged prefix and a two-one marker.
    simpa only [←List.append_assoc,hr] using h1
  have h2 := pscan v (n+2) ([true,true]++S) [false]
  have h0' : Reach v (epoch n S) (F (Q++S) (zs n++[false])) := by simpa only [epoch,List.append_assoc] using h0
  have h2' : Reach v (F (ps (n+2)++[true,true]++S) [false]) (F ([true,true]++S) (zs (n+3))) := by
    have he : zs (n+2)++[false]=zs (n+3) := by
      change List.replicate (n+2) false++List.replicate 1 false=List.replicate (n+3) false
      exact List.replicate_append_replicate
    simpa only [List.append_assoc,he] using h2
  have H := pos_then (reach_pos h0' h1') h2'
  cases h with
  | nil =>
    have h3 := fx_end v (zs (n+3))
    obtain ⟨S',hS,hR⟩ := scan_word v (n+3) 0 [] Word.nil
    exact ⟨S',hS,pos_then H (pos_reach (pos_then h3 (pos_reach hR)))⟩
  | word L hL =>
    have h3 := fx v L (zs (n+3))
    obtain ⟨S',hS,hR⟩ := scan_word v (n+3) 0 L hL
    exact ⟨S',hS,pos_then H (pos_reach (pos_then h3 (pos_reach hR)))⟩

theorem initial (v : Fin 3) : Pos v ⟨0,[],[]⟩ (epoch 1 []) := by
  have h : Pos v ⟨0,[],[]⟩ (F [true] [false]) := by
    have hv : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases hv with rfl|rfl|rfl <;> exact ⟨8,by decide,rfl⟩
  exact pos_then h (pos_reach (f1 v [false]))

theorem live (v : Fin 3) (N : Nat) : ∃ t z, N≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some z := by
  have h : ∀ k, ∃ t n S, k≤t ∧ Suffix S ∧ run0 (table v) t ⟨0,[],[]⟩=some (epoch n S) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨t,ht,hr⟩ := initial v
      exact ⟨t,1,[],by omega,Suffix.nil,hr⟩
    | succ k ih =>
      obtain ⟨t,n,S,ht,hS,hr⟩ := ih
      obtain ⟨S',hS',a,ha,hs⟩ := epoch_step v n S hS
      exact ⟨t+a,n+3,S',by omega,hS',join0 hr hs⟩
  obtain ⟨t,n,S,ht,_,hr⟩ := h N
  exact ⟨t,epoch n S,ht,hr⟩
open BB6Coverage.Agent50Zipper
theorem never (v : Fin 3) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := live v n
  let s : Z := ⟨0,0,[],[]⟩
  have hz : (zrun (table v) t s).map project = some z :=
    (run_project (table v) t s).trans hr
  cases hZ : zrun (table v) t s with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t s z' hZ
    have hb : embed s = blank := BB6Coverage.Agent31Pump.start_embed
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
#print axioms epoch_step
#print axioms live
end BB6.Agent25Raw43B0LEE1LFTriple
