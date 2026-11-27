import F421EpochCycle

namespace BB6Coverage.Agent41F421.EpochWords
open Agent31Pump
open F421TertiaryGuard (drain QBudget Marked8 Survives8)

def crossDirect (b x : Nat) : List PC → List PC
  | [] => [⟨b,x-1⟩]
  | c::cs => ⟨c.q,x-1⟩::crossDirect b c.p cs

theorem crossNearSnoc (b x : Nat) (cs : List PC) (c : PC) :
    crossNear b x (cs++[c])=crossNear b c.p cs++[⟨c.q,x-1⟩] := by
  induction cs generalizing b with
  | nil => rfl
  | cons d ds ih => simp [crossNear,ih]

theorem crossFarEq (b x : Nat) (cs : List PC) : crossFar b x cs=crossDirect b x cs := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    simp only [crossFar,List.reverse_cons,crossNearSnoc,List.reverse_append,List.reverse_singleton,List.singleton_append,crossDirect]
    rw [← crossFar,ih]
    rfl

theorem crossLength (b x : Nat) (cs : List PC) : (crossFar b x cs).length=cs.length+1 := by
  rw [crossFarEq]
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih => simp [crossDirect,ih,Nat.add_comm]

def pLower (m : Nat) (cs : List PC) : Prop := ∀ c∈cs, m≤c.p

def qMod (cs : List PC) : Prop := ∀ c∈cs, c.q%8=7

theorem crossQ (b x B : Nat) (cs : List PC) (hx : 3≤x) (hp : pLower 3 cs) :
    QBudget 0 B (crossDirect b x cs) := by
  induction cs generalizing x B with
  | nil => simp [crossDirect,QBudget]; omega
  | cons c cs ih =>
    have hc := hp c (by simp)
    have h := ih c.p (2*B) hc (fun z hz => hp z (by simp [hz]))
    exact ⟨by change 2+0*B≤x-1; omega,h⟩

theorem crossMarked (b x : Nat) (cs : List PC) (hb : b%8=7) (hq : qMod cs) : Marked8 (crossDirect b x cs) := by
  induction cs generalizing x with
  | nil => simpa [crossDirect,Marked8] using hb
  | cons c cs ih =>
    intro z hz
    simp only [crossDirect,List.mem_cons] at hz
    rcases hz with rfl|hz
    · exact hq c (by simp)
    · exact ih c.p (fun z hz => hq z (by simp [hz])) z hz

theorem qBudgetLower (k B : Nat) (cs : List PC) (hq : QBudget k B cs) : ∀ c∈cs, 2≤c.q := by
  induction cs generalizing B with
  | nil => simp
  | cons c cs ih =>
    intro z hz
    rcases hq with ⟨hc,ht⟩
    rcases List.mem_cons.mp hz with rfl|hz
    · omega
    · exact ih (2*B) ht z hz

theorem markedGuard (cs : List PC) (h B k : Nat) (hm : Marked8 cs) (hq : QBudget k B cs) : guarded h cs :=
  MergedDrain.allOddGuard cs h (fun c hc => ⟨qBudgetLower k B cs hq c hc,F421TertiaryGuard.terminalParity c.p (hm c hc)⟩)

/-- Three fixed far rows, after which the mod-eight invariant permits arbitrary terminal deletions. -/
theorem drain3 (c0 c1 c2 : PC) (hs : List PC)
    (hp0 : 1<c0.p) (hp1 : 3<c1.p) (hp2 : 7<c2.p) :
    drain 0 0 (c0::c1::c2::hs) =
      let (ds,H,r) := drain 7 0 hs
      (⟨c0.p-1,c0.q+1⟩::⟨c1.p-3,c1.q+2⟩::⟨c2.p-7,c2.q+4⟩::ds,H,r) := by
  simp only [drain,show ¬c0.p≤2*0+1 by omega,ite_false]
  -- keep the arbitrary head evaluation opaque
  simp only [show 2*0+1=1 by decide,show ¬c1.p≤2*1+1 by omega,show 2*1+1=3 by decide,show ¬c2.p≤2*3+1 by omega,show 2*3+1=7 by decide,ite_false]

theorem guard3 (c0 c1 c2 : PC) (hs : List PC)
    (hp0 : 1<c0.p) (hp1 : 3<c1.p) (hp2 : 7<c2.p)
    (hq0 : 2≤c0.q) (hq1 : 2≤c1.q) (hq2 : 2≤c2.q) (hh : guarded 7 hs) :
    guarded 0 (c0::c1::c2::hs) := by
  have h0 : min c0.p (2*0+1)=1 := by omega
  have h1 : min c1.p (2*1+1)=3 := by omega
  have h2 : min c2.p (2*3+1)=7 := by omega
  simp only [MergedDrain.guarded, h0, show 0+(1+1)/2=1 by decide,h1,show 1+(3+1)/2=3 by decide,h2,show 3+(7+1)/2=7 by decide]
  exact ⟨hq0,by omega,by omega,hq1,by omega,by omega,hq2,by omega,by omega,hh⟩

/-- No-drop drain for the third crossing, with its final horizon returned exactly. -/
def strictBudget (B : Nat) : List PC → Prop
  | [] => True
  | c::cs => 2*B+2≤c.p ∧ 2≤c.q ∧ strictBudget (2*B) cs

def strictFinish (B : Nat) : List PC → List PC
  | [] => []
  | c::cs => ⟨c.p-(2*B-1),c.q+B⟩::strictFinish (2*B) cs

theorem strictDrain (B : Nat) (cs : List PC) (hB : 1≤B) (hg : strictBudget B cs) :
    guarded (B-1) cs ∧ drain (B-1) 0 cs=(strictFinish B cs,B*2^cs.length-1,0) := by
  induction cs generalizing B with
  | nil => simp [MergedDrain.guarded,drain,strictFinish]
  | cons c cs ih =>
    rcases hg with ⟨hp,hq,ht⟩
    have hmin : min c.p (2*(B-1)+1)=2*B-1 := by omega
    have hnext : B-1+(2*B-1+1)/2=2*B-1 := by omega
    have ih' := ih (2*B) (by omega) ht
    constructor
    · simp only [MergedDrain.guarded,hmin,hnext]
      exact ⟨hq,by omega,by omega,ih'.1⟩
    · have hcap : 2*(B-1)+1=2*B-1 := by omega
      simp only [drain,hcap,show ¬c.p≤2*B-1 by omega,ite_false,ih'.2,strictFinish,List.length_cons,Nat.pow_succ]
      rw [show 2*B*2^cs.length=B*(2^cs.length*2) by ac_rfl]
      rw [show c.q+(B-1)+1+0=c.q+B by omega]

theorem finishLower (B : Nat) (cs : List PC) (hB : 1≤B) (hg : strictBudget B cs) :
    pLower 3 (strictFinish B cs) := by
  induction cs generalizing B with
  | nil => simp [strictFinish,pLower]
  | cons c cs ih =>
    rcases hg with ⟨hp,hq,ht⟩
    intro z hz
    simp only [strictFinish,List.mem_cons] at hz
    rcases hz with rfl|hz
    · change 3≤c.p-(2*B-1); omega
    · exact ih (2*B) (by omega) ht z hz

theorem finishLength (B : Nat) (cs : List PC) : (strictFinish B cs).length=cs.length := by
  induction cs generalizing B with
  | nil => rfl
  | cons c cs ih => simp [strictFinish,ih]

theorem strictCross (b x B : Nat) (cs : List PC) (hx : 3≤x) (hp : pLower 3 cs)
    (hq : QBudget 2 (2*B) cs) (hb : 2*B*2^cs.length+2≤b) : strictBudget B (crossDirect b x cs) := by
  induction cs generalizing x B with
  | nil => simp [crossDirect,strictBudget] at hb ⊢; omega
  | cons c cs ih =>
    rcases hq with ⟨hc,ht⟩
    have hc' := hp c (by simp)
    have hpow : 2*(2*B)*2^cs.length=2*B*2^(cs.length+1) := by rw [Nat.pow_succ]; ac_rfl
    have hb' : 2*(2*B)*2^cs.length+2≤b := by rw [hpow]; simpa using hb
    refine ⟨by change 2*B+2≤c.q; omega,by change 2≤x-1; omega,?_⟩
    exact ih c.p (2*B) hc' (fun z hz => hp z (by simp [hz])) ht hb'

theorem decQBudget (k B : Nat) (cs : List PC) (hq : QBudget k B cs) : QBudget k B (dec cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih => exact ⟨hq.1,ih (2*B) hq.2⟩

theorem finishMod (b x B : Nat) (cs : List PC) (hx : 8≤x ∧ x%8=0) (hm : B%8=0)
    (hp : Survives8 cs) : qMod (strictFinish B (crossDirect b x cs)) := by
  induction cs generalizing x B with
  | nil =>
    intro c hc
    simp only [crossDirect,strictFinish,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    change (x-1+B)%8=7
    omega
  | cons c cs ih =>
    have hc := hp c (by simp)
    have ht : Survives8 cs := fun z hz => hp z (by simp [hz])
    have hi := ih c.p (2*B) ⟨hc.2,hc.1⟩ (by omega) ht
    intro z hz
    simp only [crossDirect,strictFinish,List.mem_cons] at hz
    rcases hz with rfl|hz
    · change (x-1+B)%8=7; omega
    · exact hi z hz

/-- The C drain's output Q values after its three fixed rows are computed
    from exactly the surviving mod-eight head of the B drain. -/
theorem finishHeadMod (b x B : Nat) (cs : List PC) (hm : B%8=0) (hp : Survives8 cs) :
    qMod (strictFinish B (crossDirect b x cs)).tail := by
  cases cs with
  | nil => simp [crossDirect,strictFinish,qMod]
  | cons c cs =>
    have hc := hp c (by simp)
    have ht : Survives8 cs := fun z hz => hp z (by simp [hz])
    exact finishMod b c.p (2*B) cs ⟨hc.2,hc.1⟩ (by omega) ht

end BB6Coverage.Agent41F421.EpochWords
