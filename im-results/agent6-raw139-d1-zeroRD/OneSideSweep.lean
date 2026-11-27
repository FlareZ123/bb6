import PackedSweepTrace
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent6OneSide
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent6SweepTrace BB6Coverage.Agent6PackedSweep

/-- Retain a finite left frame but allow the actual implicit zero tail on the right.
    The test rejects every read beyond the retained left frame. -/
def lstep (p : PartialMachine) (z : Z0) : Option Z0 :=
  if z.l.isEmpty then none else step0 p z

def lrun (p : PartialMachine) : Nat → Z0 → Option Z0
  | 0,z => some z
  | k+1,z => (lstep p z).bind (lrun p k)

def extL (z : Z0) (L : List Bool) : Z0 := ⟨z.q,z.l++L,z.r⟩

theorem lstep_ext (p : PartialMachine) (z u : Z0) (L : List Bool)
    (h : lstep p z = some u) : step0 p (extL z L) = some (extL u L) := by
  rcases z with ⟨q,l,r⟩
  cases l with
  | nil => simp [lstep] at h
  | cons a l =>
    simp only [lstep,List.isEmpty_cons,Bool.false_eq_true,ite_false] at h
    cases hp : (p (q,a)).bind id with
    | none => simp [step0,hp] at h
    | some mv =>
      simp [step0,hp] at h
      subst u
      cases hr : mv.right <;> simp [extL,step0,move0,hp,hr]

theorem lrun_ext (p : PartialMachine) (n : Nat) (z u : Z0) (L : List Bool)
    (h : lrun p n z = some u) : run0 p n (extL z L) = some (extL u L) := by
  induction n generalizing z with
  | zero => cases Option.some.inj h; rfl
  | succ n ih =>
    cases hs : lstep p z with
    | none => simp [lrun,hs] at h
    | some t =>
      have ht : lrun p n t = some u := by simpa only [lrun,hs,Option.bind_some] using h
      rw [run0,lstep_ext p z t L hs]
      exact ih t ht

def lapply (p : PartialMachine) (z : Z0) : Action → Option (Nat × Z0)
  | .raw k => (lrun p k z).map fun u => (k,u)
  | a => applyAction p z a

theorem lapply_ext (p : PartialMachine) (z z' : Z0) (a : Action) (k : Nat) (L0 : List Bool)
    (h : lapply p z a = some (k,z')) : run0 p k (extL z L0) = some (extL z' L0) := by
  cases a with
  | raw t =>
    cases hr : lrun p t z with
    | none => simp [lapply,hr] at h
    | some u => simp [lapply,hr] at h; obtain ⟨rfl,rfl⟩ := h; exact lrun_ext p t z u L0 hr
  | left lp rp I O t n =>
    simp only [lapply,applyAction] at h
    split at h
    next hs =>
      cases hl : removePrefix (lp++rep I n) z.l <;> cases hr : removePrefix rp z.r <;> simp [hl,hr] at h
      next L R =>
        obtain ⟨rfl,rfl⟩ := h
        have hL := removePrefix_sound hl
        have hR := removePrefix_sound hr
        have one : ∀ X Y, run0 p t ⟨z.q,lp++I++X,rp++Y⟩ = some ⟨z.q,lp++X,rp++O++Y⟩ := by
          intro X Y
          exact run_extend p t _ _ X Y hs
        have H := sweepL p z.q lp rp I O t one n (L++L0) R
        cases z with
        | mk q l r =>
          simp only [extL] at *
          try dsimp at hL hR ⊢ H
          rw [hL,hR]
          simpa only [List.append_assoc] using H
    next => contradiction
  | right lp rp I O t n =>
    simp only [lapply,applyAction] at h
    split at h
    next hs =>
      cases hl : removePrefix lp z.l <;> cases hr : removePrefix (rp++rep I n) z.r <;> simp [hl,hr] at h
      next L R =>
        obtain ⟨rfl,rfl⟩ := h
        have hL := removePrefix_sound hl
        have hR := removePrefix_sound hr
        have one : ∀ X Y, run0 p t ⟨z.q,lp++X,rp++I++Y⟩ = some ⟨z.q,lp++O++X,rp++Y⟩ := by
          intro X Y
          exact run_extend p t _ _ X Y hs
        have H := sweepR p z.q lp rp I O t one n (L++L0) R
        cases z with
        | mk q l r =>
          simp only [extL] at *
          try dsimp at hL hR ⊢ H
          rw [hL,hR]
          simpa only [List.append_assoc] using H
    next => contradiction

def leval (p : PartialMachine) : List Action → Z0 → Option (Nat × Z0)
  | [],z => some (0,z)
  | a::as,z => match lapply p z a with
    | none => none
    | some (n,t) => (leval p as t).map fun (m,u) => (n+m,u)

theorem leval_ext (p : PartialMachine) (as : List Action) (z z' : Z0) (n : Nat) (L : List Bool)
    (h : leval p as z = some (n,z')) : run0 p n (extL z L) = some (extL z' L) := by
  induction as generalizing z n with
  | nil => simp [leval] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons a as ih =>
    cases ha : lapply p z a with
    | none => simp [leval,ha] at h
    | some v =>
      rcases v with ⟨k,t⟩
      cases hs : leval p as t with
      | none => simp [leval,ha,hs] at h
      | some v =>
        rcases v with ⟨m,u⟩
        simp [leval,ha,hs] at h
        obtain ⟨rfl,rfl⟩ := h
        exact join0 (lapply_ext p z t a k L ha) (ih t m hs)

def plstep (p : PartialMachine) (z : PZ) : Option PZ :=
  if z.l.len = 0 then none else pstep p z

theorem plstep_enc (p : PartialMachine) (z : Z0) : plstep p (encZ z) = (lstep p z).map encZ := by
  cases h : z.l with
  | nil => simp [plstep,lstep,encZ,h,enc,empty]
  | cons b L =>
    have hlen : (encZ z).l.len ≠ 0 := by simp [encZ,enc_len,h]
    simp only [plstep,hlen,ite_false,lstep,h,List.isEmpty_cons,Bool.false_eq_true,pstep_enc]

def plrun (p : PartialMachine) : Nat → PZ → Option PZ
  | 0,z => some z
  | k+1,z => (plstep p z).bind (plrun p k)

theorem plrun_enc (p : PartialMachine) (n : Nat) (z : Z0) :
    plrun p n (encZ z) = (lrun p n z).map encZ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [plrun,plstep_enc,lrun]
    cases hs : lstep p z with
    | none => rfl
    | some t => exact ih t

def plapply (p : PartialMachine) (z : PZ) : Action → Option (Nat × PZ)
  | .raw k => (plrun p k z).map fun u => (k,u)
  | a => papply p z a

theorem plapply_enc (p : PartialMachine) (z : Z0) (a : Action) :
    plapply p (encZ z) a = (lapply p z a).map (fun (n,u) => (n,encZ u)) := by
  cases a with
  | raw k =>
    simp only [plapply,lapply,plrun_enc]
    cases lrun p k z <;> rfl
  | left lp rp I O k n => exact papply_enc p z (.left lp rp I O k n)
  | right lp rp I O k n => exact papply_enc p z (.right lp rp I O k n)

def pleval (p : PartialMachine) : List Action → PZ → Option (Nat × PZ)
  | [],z => some (0,z)
  | a::as,z => match plapply p z a with
    | none => none
    | some (n,t) => (pleval p as t).map fun (m,u) => (n+m,u)

theorem pleval_enc (p : PartialMachine) (as : List Action) (z : Z0) :
    pleval p as (encZ z) = (leval p as z).map (fun (n,u) => (n,encZ u)) := by
  induction as generalizing z with
  | nil => rfl
  | cons a as ih =>
    simp only [pleval,leval,plapply_enc]
    cases ha : lapply p z a with
    | none => rfl
    | some v =>
      rcases v with ⟨n,t⟩
      simp only [Option.map_some,ih]
      cases leval p as t <;> rfl

theorem encZ_injective {z u : Z0} (h : encZ z = encZ u) : z = u := by
  have hq := congrArg PZ.q h
  have hl := enc_injective (congrArg PZ.l h)
  have hr := enc_injective (congrArg PZ.r h)
  cases z; cases u
  simp [encZ] at hq hl hr
  congr

theorem reach_exact (p : PartialMachine) (n : Nat) (z : Z0) (h : Reach p n (encZ z)) :
    run0 p n ⟨0,[],[]⟩ = some z := by
  obtain ⟨u,hu,he⟩ := h
  rw [encZ_injective he] at hu
  exact hu

def ExtReach (p : PartialMachine) (a : Z0) (n : Nat) (b : PZ) : Prop :=
  ∃ z, encZ z = b ∧ ∀ L, run0 p n (extL a L) = some (extL z L)

theorem extReach0 (p : PartialMachine) (a : Z0) : ExtReach p a 0 (encZ a) := ⟨a,rfl,fun _ => rfl⟩

theorem extReach_extend {p : PartialMachine} {a : Z0} {n k : Nat} {b c : PZ} (as : List Action)
    (h : ExtReach p a n b) (hh : pleval p as b = some (k,c)) : ExtReach p a (n+k) c := by
  obtain ⟨z,rfl,hz⟩ := h
  rw [pleval_enc] at hh
  cases he : leval p as z with
  | none => simp [he] at hh
  | some v =>
    rcases v with ⟨m,u⟩
    simp [he] at hh
    obtain ⟨rfl,rfl⟩ := hh
    exact ⟨u,rfl,fun L => join0 (hz L) (leval_ext p as z u m L he)⟩

theorem extReach_exact (p : PartialMachine) (a b : Z0) (n : Nat)
    (h : ExtReach p a n (encZ b)) (L : List Bool) :
    run0 p n (extL a L) = some (extL b L) := by
  obtain ⟨z,he,hz⟩ := h
  rw [encZ_injective he] at hz
  exact hz L

theorem right_growth (p : PartialMachine) (q : Fin 6) (W V T : List Bool) (entry period : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some ⟨q,W++T,[]⟩)
    (hpos : 0 < period)
    (hcycle : ∀ L, run0 p period ⟨q,W++L,[]⟩ = some ⟨q,W++V++L,[]⟩)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let family (k : Nat) : Z0 := ⟨q,W++rep V k++T,[]⟩
  apply never_of_growth p family entry (fun _ => period)
  · simpa [family,rep] using first
  · intro; exact hpos
  · intro k
    simpa only [family,rep,List.append_assoc] using hcycle (rep V k++T)
  · exact hm

#print axioms right_growth
#print axioms extReach_exact
end BB6Coverage.Agent6OneSide
