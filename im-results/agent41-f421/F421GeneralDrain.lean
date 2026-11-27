import F421Drain
import F421DrainPlan

namespace BB6Coverage.Agent41F421.GeneralDrain
open BB6Coverage Agent31Pump Regular F421DrainPlan

def rowWord (c : Row) : List Bool := rep P c.p ++ (if c.mark then Z else []) ++ rep Q c.q
def nearWord (cs : List Row) : List Bool := cs.flatMap rowWord
def farWord (cs : List Row) : List Bool := nearWord cs.reverse

theorem nearAppend (xs ys : List Row) : nearWord (xs++ys)=nearWord xs++nearWord ys := by
  simp [nearWord]
theorem farAppend (xs ys : List Row) : farWord (xs++ys)=farWord ys++farWord xs := by
  simp [farWord,List.reverse_append,nearAppend]
theorem farCons (c : Row) (cs : List Row) : farWord (c::cs)=farWord cs++rowWord c := by
  simp [farWord,List.reverse_cons,nearWord]

def carrySegs (b : Nat) (cs : List Row) (p : Nat) : List Seg :=
  match cs with
  | [] => [(b-2,p-1)]
  | c::cs => if c.p=0 then carrySegs (b+c.q) cs p
      else (b-2,c.p-1)::carrySegs c.q cs p

def lowGood (cs : List Row) : Prop := ∀ c∈cs, c.mark=false ∧ (c.p=0 ∨ 2≤c.p) ∧ 2≤c.q

theorem carryInput (b : Nat) (cs : List Row) (p : Nat) (hb : 2≤b) (hp : 1≤p) (hg : lowGood cs) :
    inputs (carrySegs b cs p)=rep Q b++nearWord cs++rep P p := by
  induction cs generalizing b with
  | nil => simp [carrySegs,inputs,segInput,nearWord,show b-2+2=b by omega,show p-1+1=p by omega]
  | cons c cs ih =>
    obtain ⟨hm,hp',hq⟩ := hg c (by simp)
    have ht : lowGood cs := by intro x hx; exact hg x (by simp [hx])
    by_cases h0 : c.p=0
    · rw [carrySegs,ite_eq_left h0,ih (b+c.q) (by omega) ht,repAdd]
      simp [nearWord,rowWord,hm,h0,rep,List.append_assoc]
    · have h := ih c.q hq ht
      rw [carrySegs,ite_eq_right h0]
      change segInput (b-2,c.p-1)++inputs (carrySegs c.q cs p)=_
      rw [h]
      simp [segInput,nearWord,rowWord,hm,show b-2+2=b by omega,show c.p-1+1=c.p by omega,List.append_assoc]

theorem carryOutput (b : Nat) (cs : List Row) (p : Nat) (hb : 2≤b) (hg : lowGood cs) :
    outputs (carrySegs b cs p)=Z++rep Q b++nearWord (cs.map lowStep)++rep P (p-1) := by
  induction cs generalizing b with
  | nil => simp [carrySegs,outputs,segOutput,nearWord,show b-2+2=b by omega,List.append_assoc]
  | cons c cs ih =>
    obtain ⟨hm,hp',hq⟩ := hg c (by simp)
    have ht : lowGood cs := by intro x hx; exact hg x (by simp [hx])
    by_cases h0 : c.p=0
    · rw [carrySegs,ite_eq_left h0,ih (b+c.q) (by omega) ht,repAdd]
      simp [nearWord,rowWord,lowStep,hm,h0,rep,List.append_assoc]
    · rw [carrySegs,ite_eq_right h0]
      change segOutput (b-2,c.p-1)++outputs (carrySegs c.q cs p)=_
      rw [ih c.q hq ht]
      simp [segOutput,nearWord,rowWord,lowStep,h0,show b-2+2=b by omega,List.append_assoc]

/-- Carry across positive unmarked cells and zero-P unmarked Q ghosts.
    The latter merge as words, but never acquire a marker. -/
theorem carryGhosts (a b : Nat) (cs : List Row) (c : Row) (U : List Bool)
    (hb : 2≤b) (hp : 1≤c.p) (hm : c.mark=true) (hg : lowGood cs) :
    ∃ n, 1≤n ∧ run0 table n
      (frontier (rep P a++rep Q b++nearWord cs++rowWord c++U)) =
      some (frontier (rep P (a+2)++rep Q (b+1)++nearWord (cs.map lowStep)++rowWord (termStep c)++U)) := by
  let ss := carrySegs b cs c.p
  let V := rep Q c.q++U
  let W := rep Q b++nearWord (cs.map lowStep)++rep P (c.p-1)++Q++V
  have h1 := evenReturn a ss V
  rw [show inputs ss=rep Q b++nearWord cs++rep P c.p from carryInput b cs c.p hb hp hg,
      show outputs ss=Z++rep Q b++nearWord (cs.map lowStep)++rep P (c.p-1) from carryOutput b cs c.p hb hg] at h1
  have h1' : run0 table (4*a+costs ss+6)
      (frontier (rep P a++rep Q b++nearWord cs++rowWord c++U)) =
      some (frontier (rep P (a+1)++Z++W)) := by
    simpa [W,V,rowWord,hm,List.append_assoc] using h1
  have h2 := evenReturn (a+1) [] W
  have h2' : run0 table (4*(a+1)+6) (frontier (rep P (a+1)++Z++W)) =
      some (frontier (rep P (a+2)++rep Q (b+1)++nearWord (cs.map lowStep)++rowWord (termStep c)++U)) := by
    simpa [W,V,inputs,outputs,costs,rep,termStep,rowWord,List.append_assoc] using h2
  exact ⟨_,by omega,join0 h1' h2'⟩

/-- General drain with arbitrary terminal deletions, no bound on list size
    or run lengths. The arithmetic plan retains unmarked zero-P ghosts,
    whose tape words are exactly the merged Q runs. -/
theorem generalDrainAt (N : Nat) (cs : List Row) (a b : Nat) (U : List Bool)
    (hb : 2≤b) (hg : good 0 cs) (he : count 0 cs=N) :
    ∃ n, count 0 cs≤n ∧ run0 table n
      (frontier (rep P a++rep Q b++farWord cs++U)) =
      some (frontier (rep P (a+2*count 0 cs)++rep Q (b+count 0 cs)++farWord (finish 0 cs)++U)) := by
  induction N using Nat.strongRecOn generalizing cs a b with
  | ind N ih =>
    rcases splitMarked cs with hm|⟨fs,c,ns,rfl,hm,hn⟩
    · obtain ⟨hc,hf⟩ := unmarkedPlan cs hm
      exact ⟨0,by omega,by simp [hc,hf,run0]⟩
    · let xs := fs++c::ns
      let ys := fs++termStep c::ns.map lowStep
      obtain ⟨hg',hC,hF,⟨hp,hq⟩,hlow⟩ := splitPlan fs ns c 0 hm hn hg
      change good 0 ys at hg'
      change count 0 xs=count 0 ys+1 at hC
      change finish 0 xs=finish 0 ys at hF
      change count 0 xs=N at he
      have hlow' : lowGood ns.reverse := by
        intro x hx
        have he := List.mem_reverse.mp hx
        exact ⟨hn x he,hlow x he⟩
      obtain ⟨k,hk,hr⟩ := carryGhosts a b ns.reverse c (farWord fs++U) hb hp hm hlow'
      have hr' : run0 table k (frontier (rep P a++rep Q b++farWord xs++U)) =
          some (frontier (rep P (a+2)++rep Q (b+1)++farWord ys++U)) := by
        simp only [xs,ys,farAppend,farCons]
        rw [show farWord (ns.map lowStep)=nearWord (ns.reverse.map lowStep) by simp [farWord,List.map_reverse]]
        simpa only [farWord,List.append_assoc] using hr
      obtain ⟨n,hn',hr2⟩ := ih (count 0 ys) (by omega) ys (a+2) (b+1) (by omega) hg' rfl
      have ha : a+2+2*count 0 ys=a+2*count 0 xs := by omega
      have hb' : b+1+count 0 ys=b+count 0 xs := by omega
      rw [ha,hb',←hF] at hr2
      change ∃ n, count 0 xs≤n ∧ run0 table n _ = some _
      exact ⟨k+n,by omega,join0 hr' hr2⟩

theorem generalDrain (cs : List Row) (a b : Nat) (U : List Bool)
    (hb : 2≤b) (hg : good 0 cs) :
    ∃ n, count 0 cs≤n ∧ run0 table n
      (frontier (rep P a++rep Q b++farWord cs++U)) =
      some (frontier (rep P (a+2*count 0 cs)++rep Q (b+count 0 cs)++farWord (finish 0 cs)++U)) :=
  generalDrainAt (count 0 cs) cs a b U hb hg rfl

#print axioms carryGhosts
#print axioms generalDrain
end BB6Coverage.Agent41F421.GeneralDrain
