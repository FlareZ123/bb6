import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Raw61Blocks
open BB6Coverage Agent31Pump Agent50Zipper
abbrev W := List Bool
abbrev o (n : Nat) : W := List.replicate n true
abbrev cfg (q : Fin 6) (l r : W) : Z0 := ⟨q,l,r⟩
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
abbrev P : W := [false,false,false,true]
abbrev Q : W := [false,false,true]
abbrev E (L R : W) : Z0 := cfg 4 (false::true::false::L) R
abbrev F (L R : W) : Z0 := cfg 5 L R
abbrev A (R : W) : Z0 := cfg 0 [] R
inductive Good : W → Prop
  | end5 : Good (o 5)
  | endT (k : Nat) : Good (o (4*k+6))
  | t (k : Nat) {L : W} : Good L → Good (o (4*k+6) ++ false::L)
  | u (k : Nat) {L : W} : Good L → Good (o (4*k+4) ++ false::true::false::L)
inductive Groups : W → Prop
  | nil : Groups []
  | cons (a : Nat) {R : W} : Groups R → Groups (Q ++ rep P (a+1) ++ R)

def Reach (c d : Z0) : Prop := ∃ n, run0 table n c = some d
def ReachPos (c d : Z0) : Prop := ∃ n, 0 < n ∧ run0 table n c = some d

theorem rflR (c : Z0) : Reach c c := ⟨0,rfl⟩
theorem transR {a b c : Z0} (h : Reach a b) (g : Reach b c) : Reach a c := by
  obtain ⟨n,h⟩ := h; obtain ⟨k,g⟩ := g; exact ⟨n+k,join0 h g⟩
theorem transPos {a b c : Z0} (h : ReachPos a b) (g : Reach b c) : ReachPos a c := by
  obtain ⟨n,hn,h⟩ := h; obtain ⟨k,g⟩ := g; exact ⟨n+k,by omega,join0 h g⟩
theorem nextR {a b : Z0} {n : Nat} (h : run0 table n a = some b) : Reach a b := ⟨n,h⟩
theorem nextP {a b : Z0} {n : Nat} (hn : 0<n) (h : run0 table n a = some b) : ReachPos a b := ⟨n,hn,h⟩

theorem repTail (b : Bool) (n m : Nat) (L : W) :
    List.replicate n b ++ (List.replicate m b ++ L) = List.replicate (n+m) b ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]
theorem repSnoc (X : W) (n : Nat) : rep X n ++ X = rep X (n+1) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]
theorem repCat (X : W) (n : Nat) (R : W) : rep X n ++ X ++ R = rep X (n+1) ++ R := by rw [repSnoc]

-- The forward encoder adds four ones for each 0010 token and a separator for 010.
theorem bStep (L R : W) : run0 table 18 (E L (false::false::true::false::R)) = some (E (true::true::true::true::L) R) := by rfl
theorem bLast (L : W) : run0 table 18 (E L Q) = some (E (true::true::true::true::L) []) := by rfl
theorem dStep (L R : W) : run0 table 3 (E L (false::true::false::R)) = some (E (false::true::false::L) R) := by rfl

theorem forwardPrefix (a : Nat) (L R : W) : Reach (E L (Q ++ rep P a ++ R)) (E (o (4*a) ++ L) (Q++R)) := by
  induction a generalizing L with
  | zero => exact rflR _
  | succ a ih =>
    have h : Reach (E L (Q ++ rep P (a+1) ++ R)) (E (true::true::true::true::L) (Q ++ rep P a ++ R)) := by
      exact nextR (bStep L (Q ++ rep P a ++ R))
    have H := transR h (ih (true::true::true::true::L))
    have hh : o (4*a) ++ true::true::true::true::L = o (4*(a+1)) ++ L := by
      rw [show 4*(a+1)=4*a+4 by omega]; exact repTail true (4*a) 4 L
    rw [hh] at H
    exact H

theorem finishGroups {R : W} (hR : Groups R) : ∀ L, Good (o 4 ++ L) → ∃ L', Good L' ∧ Reach (E L (Q++R)) (E L' []) := by
  induction hR with
  | nil => intro L hL; exact ⟨_,hL,nextR (bLast L)⟩
  | @cons a R hR ih =>
    intro L hL
    have h1 : Reach (E L (Q ++ (Q ++ rep P (a+1) ++ R))) (E (o 4 ++ L) (false::true::rep P (a+1) ++ R)) := by
      exact nextR (bStep L (false::true::rep P (a+1) ++ R))
    have h2 : Reach (E (o 4 ++ L) (false::true::rep P (a+1) ++ R)) (E (false::true::false::(o 4 ++ L)) (Q ++ rep P a ++ R)) := by
      exact nextR (dStep (o 4 ++ L) (Q ++ rep P a ++ R))
    have h3 := forwardPrefix a (false::true::false::(o 4 ++ L)) R
    have hG : Good (o 4 ++ (o (4*a) ++ false::true::false::(o 4 ++ L))) := by
      rw [repTail true 4 (4*a) _,show 4+4*a=4*a+4 by omega]
      exact Good.u a hL
    obtain ⟨L',hG',h4⟩ := ih _ hG
    exact ⟨L',hG',transR (transR (transR h1 h2) h3) h4⟩

theorem forward (a : Nat) (L : W) {R : W} (hR : Groups R) (hG : Good (o (4*a+4) ++ L)) : ∃ L', Good L' ∧ Reach (E L (Q ++ rep P a ++ R)) (E L' []) := by
  have hh : Good (o 4 ++ (o (4*a) ++ L)) := by
    rw [repTail true 4 (4*a) _,show 4+4*a=4*a+4 by omega]; exact hG
  obtain ⟨L',hg,h⟩ := finishGroups hR _ hh
  exact ⟨L',hg,transR (forwardPrefix a L R) h⟩

theorem aForward (a : Nat) {R : W} (hR : Groups R) : ∃ L', Good L' ∧ Reach (A (Q++rep P (a+1)++R)) (E L' []) := by
  have h : Reach (A (Q++rep P (a+1)++R)) (E [true,true] (Q++rep P a++R)) := nextR (show run0 table 4 _ = some _ by rfl)
  have hG : Good (o (4*a+4) ++ [true,true]) := by
    rw [show o (4*a+4) ++ [true,true] = o (4*a+4+2) from @List.replicate_append_replicate (4*a+4) Bool true 2]
    exact Good.endT a
  obtain ⟨L',hg,h'⟩ := forward a [true,true] hR hG
  exact ⟨L',hg,transR h h'⟩

-- Backward phase: each four ones produces one P block.
theorem fStep (L R : W) : run0 table 4 (F (true::true::true::true::L) R) = some (F L (P++R)) := by rfl

theorem fSweep (k : Nat) (L R : W) : Reach (F (o (4*k) ++ L) R) (F L (rep P k ++ R)) := by
  induction k generalizing R with
  | zero => exact rflR _
  | succ k ih =>
    have h := transR (nextR (fStep (o (4*k) ++ L) R)) (ih (P++R))
    have hh : rep P k ++ (P++R) = rep P (k+1) ++ R := by rw [← List.append_assoc,repSnoc]
    rw [hh] at h
    rw [show 4*(k+1)=4*k+4 by omega]
    exact h

theorem turn (L R : W) : run0 table 23 (F (false::true::L) (P++P++R)) = some (F (true::true::true::L) (P++Q++R)) := by rfl
theorem turnBlank (R : W) : run0 table 23 (F [] (P++P++R)) = some (F [true,true] (P++Q++R)) := by rfl
theorem turnRun (n : Nat) (L R : W) : Reach (F (false::(o (n+1) ++ L)) (P++P++R)) (F (o (n+3) ++ L) (P++Q++R)) := nextR (turn (o n ++ L) R)
theorem stopU (L R : W) : run0 table 5 (F (true::true::false::true::L) (P++R)) = some (E (true::true::L) (Q++R)) := by rfl
theorem stopBlank (R : W) : run0 table 5 (F [true,true] (P++R)) = some (E [true] (Q++R)) := by rfl
theorem stop5 (R : W) : run0 table 3 (F [true,true,true] R) = some (A (Q++R)) := by rfl

theorem uForward (a : Nat) (L : W) (hL : Good L) {R : W} (hR : Groups R) : ∃ L', Good L' ∧ Reach (F (true::true::false::true::false::L) (rep P (a+1)++R)) (E L' []) := by
  have h := nextR (stopU (false::L) (rep P a ++ R))
  have hG : Good (o (4*a+4) ++ true::true::false::L) := by
    have hh : o (4*a+4) ++ true::true::false::L = o (4*a+6) ++ false::L := repTail true (4*a+4) 2 (false::L)
    rw [hh]; exact Good.t a hL
  obtain ⟨L',hg,h'⟩ := forward a (true::true::false::L) hR hG
  exact ⟨L',hg,transR h h'⟩

theorem blankForward (a : Nat) {R : W} (hR : Groups R) : ∃ L', Good L' ∧ Reach (F [] (rep P (a+3)++R)) (E L' []) := by
  have h1 := nextR (turnBlank (rep P (a+1)++R))
  have h2 := nextR (stopBlank (Q++rep P (a+1)++R))
  have hG : Good (o (4*0+4) ++ [true]) := Good.end5
  obtain ⟨L',hg,h3⟩ := forward 0 [true] (Groups.cons a hR) hG
  exact ⟨L',hg,transR (transR h1 h2) h3⟩

-- Consume a left suffix through arbitrary many T blocks; stop at a U or the terminal.
theorem drain {L : W} (hL : Good L) : ∀ a R, Groups R → ∃ L', Good L' ∧ Reach (F (false::L) (rep P (a+3)++R)) (E L' []) := by
  induction hL with
  | end5 =>
    intro a R hR
    have h1 := turnRun 4 [] (rep P (a+1)++R)
    have h2 := fSweep 1 [true,true,true] (P++Q++rep P (a+1)++R)
    have h3 := nextR (stop5 (rep P 2 ++ Q++rep P (a+1)++R))
    have h1' : Reach (F (false::o 5) (rep P (a+3)++R)) (F (o 7) (P++Q++rep P (a+1)++R)) := by
      simpa only [List.append_nil,rep,List.append_assoc] using h1
    have h2' : Reach (F (o 7) (P++Q++rep P (a+1)++R)) (F [true,true,true] (rep P 2 ++ Q++rep P (a+1)++R)) := by simpa only [rep,List.append_assoc,List.nil_append,List.replicate_succ,List.replicate_zero,List.cons_append] using h2
    obtain ⟨L',hg,h4⟩ := aForward 1 (Groups.cons a hR)
    exact ⟨L',hg,transR (transR (transR h1' h2') h3) h4⟩
  | endT k =>
    intro a R hR
    have h1 := turnRun (4*k+5) [] (rep P (a+1)++R)
    have h2 := fSweep (k+2) [] (P++Q++rep P (a+1)++R)
    have h1' : Reach (F (false::o (4*k+6)) (rep P (a+3)++R)) (F (o (4*(k+2))) (P++Q++rep P (a+1)++R)) := by
      simpa only [List.append_nil,rep,List.append_assoc,show 4*k+5+1=4*k+6 by omega,show 4*k+5+3=4*(k+2) by omega] using h1
    have hh : rep P (k+2) ++ (P++Q++rep P (a+1)++R) = rep P (k+3) ++ (Q++rep P (a+1)++R) := by
      simp only [← List.append_assoc,repSnoc]
    rw [hh] at h2
    simp only [List.append_nil] at h2
    obtain ⟨L',hg,h3⟩ := blankForward k (Groups.cons a hR)
    exact ⟨L',hg,transR (transR h1' h2) h3⟩
  | @t k L hL ih =>
    intro a R hR
    have h1 := turnRun (4*k+5) (false::L) (rep P (a+1)++R)
    have h2 := fSweep (k+2) (false::L) (P++Q++rep P (a+1)++R)
    have h1' : Reach (F (false::(o (4*k+6)++false::L)) (rep P (a+3)++R)) (F (o (4*(k+2))++false::L) (P++Q++rep P (a+1)++R)) := by
      simpa only [rep,List.append_assoc,show 4*k+5+1=4*k+6 by omega,show 4*k+5+3=4*(k+2) by omega] using h1
    have hh : rep P (k+2) ++ (P++Q++rep P (a+1)++R) = rep P (k+3) ++ (Q++rep P (a+1)++R) := by
      simp only [← List.append_assoc,repSnoc]
    rw [hh] at h2
    obtain ⟨L',hg,h3⟩ := ih k _ (Groups.cons a hR)
    exact ⟨L',hg,transR (transR h1' h2) h3⟩
  | @u k L hL _ =>
    intro a R hR
    have h1 := turnRun (4*k+3) (false::true::false::L) (rep P (a+1)++R)
    have h2 := fSweep (k+1) (true::true::false::true::false::L) (P++Q++rep P (a+1)++R)
    have h1' : Reach (F (false::(o (4*k+4)++false::true::false::L)) (rep P (a+3)++R)) (F (o (4*(k+1))++true::true::false::true::false::L) (P++Q++rep P (a+1)++R)) := by
      rw [show 4*k+3+1=4*k+4 by omega,show 4*k+3+3=4*(k+1)+2 by omega] at h1
      rw [← repTail true (4*(k+1)) 2 (false::true::false::L)] at h1
      simpa only [rep,List.append_assoc,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append] using h1
    have hh : rep P (k+1) ++ (P++Q++rep P (a+1)++R) = rep P (k+2) ++ (Q++rep P (a+1)++R) := by
      simp only [← List.append_assoc,repSnoc]
    rw [hh] at h2
    obtain ⟨L',hg,h3⟩ := uForward (k+1) L hL (Groups.cons a hR)
    exact ⟨L',hg,transR (transR h1' h2) h3⟩

theorem startBack (L : W) : run0 table 23 (E L []) = some (F (true::true::L) P) := by rfl

theorem progress {L : W} (hL : Good L) : ∃ L', Good L' ∧ ReachPos (E L []) (E L' []) := by
  have h0 := nextP (by decide : 0<23) (startBack L)
  cases hL with
  | end5 =>
    have h1 : Reach (F (true::true::o 5) P) (F [true,true,true] (rep P 2)) := fSweep 1 [true,true,true] P
    have h2 := nextR (stop5 (rep P 2))
    obtain ⟨L',hg,h3⟩ := aForward 1 Groups.nil
    exact ⟨L',hg,transPos h0 (transR (transR h1 h2) h3)⟩
  | endT k =>
    have h1 := fSweep (k+2) [] P
    have h1' : Reach (F (true::true::o (4*k+6)) P) (F [] (rep P (k+3)++[])) := by
      rw [repSnoc] at h1
      simpa only [List.append_nil,show 4*(k+2)=4*k+6+2 by omega,List.replicate_succ] using h1
    obtain ⟨L',hg,h2⟩ := blankForward k Groups.nil
    exact ⟨L',hg,transPos h0 (transR h1' h2)⟩
  | @t k L hL =>
    have h1 := fSweep (k+2) (false::L) P
    have h1' : Reach (F (true::true::(o (4*k+6)++false::L)) P) (F (false::L) (rep P (k+3)++[])) := by
      rw [repSnoc] at h1
      simpa only [List.append_nil,show 4*(k+2)=4*k+6+2 by omega,List.replicate_succ,List.cons_append] using h1
    obtain ⟨L',hg,h2⟩ := drain hL k [] Groups.nil
    exact ⟨L',hg,transPos h0 (transR h1' h2)⟩
  | @u k L hL =>
    have h1 := fSweep (k+1) (true::true::false::true::false::L) P
    have h1' : Reach (F (true::true::(o (4*k+4)++false::true::false::L)) P) (F (true::true::false::true::false::L) (rep P (k+2)++[])) := by
      rw [repSnoc] at h1
      have hh : o (4*(k+1)) ++ true::true::false::true::false::L = true::true::(o (4*k+4)++false::true::false::L) := by
        rw [show 4*(k+1)=4*k+4 by omega]
        calc
          _ = o (4*k+4+2) ++ false::true::false::L := repTail true (4*k+4) 2 (false::true::false::L)
          _ = _ := by rfl
      rw [hh] at h1
      simpa only [List.append_nil] using h1
    obtain ⟨L',hg,h2⟩ := uForward (k+1) L hL Groups.nil
    exact ⟨L',hg,transPos h0 (transR h1' h2)⟩

theorem entry : run0 table 55 (cfg 0 [] []) = some (E (o 5) []) := by rfl

theorem unbounded (n : Nat) : ∃ t, n ≤ t ∧ ∃ L, Good L ∧ run0 table t (cfg 0 [] []) = some (E L []) := by
  induction n with
  | zero => exact ⟨55,by omega,_,Good.end5,entry⟩
  | succ n ih =>
    obtain ⟨t,ht,L,hL,hr⟩ := ih
    obtain ⟨L',hg,k,hk,hstep⟩ := progress hL
    exact ⟨t+k,by omega,L',hg,join0 hr hstep⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,L,_,hr⟩ := unbounded n
  have hz : (zrun table t start).map project = some (E L []) :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
#print axioms unbounded
#print axioms progress
#print axioms entry
end BB6Coverage.Raw61Blocks

namespace BB6.Agent10Recursive.R61M353
open BB6Coverage
abbrev table := Raw61Blocks.table
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Raw61Blocks.never m hm
end BB6.Agent10Recursive.R61M353
