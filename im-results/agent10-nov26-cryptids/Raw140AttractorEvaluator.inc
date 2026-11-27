/- Variant-sensitive accelerated execution on the upstream symbolic words.
   All macros are checked against the RESTRICTED table; single steps use the actual table.
   Concrete execution uses zero values for symbolic parameters. -/
abbrev CV := v5 0 0 0 0 0

structure CState where
  q : Fin 6
  right : Bool
  L : List SymLTok
  R : List SymRTok
  deriving DecidableEq, Repr

def ceval (s : CState) : Cfg (Fin 2) (Fin 6) :=
  if s.right then Cfg.headRight s.q (encSL CV s.L) (encSR CV s.R)
  else Cfg.headLeft s.q (encSL CV s.L) (encSR CV s.R)

def cpushL (b : Fin 2) (L : List SymLTok) :=
  if b = 0 then symPushZerosL 1 L else symPushOnesL 1 L

def cpushR (b : Fin 2) (R : List SymRTok) :=
  if b = 0 then symPushZerosR 1 R else symPushOnesR 1 R

theorem cpushL_spec {b : Fin 2} {L T : List SymLTok}
    (h : cpushL b L = some T) : encSL CV T = b >> encSL CV L := by
  fin_cases b
  · exact encSL_pushZerosL (v := CV) (by simpa [cpushL] using h)
  · exact encSL_pushOnesL (v := CV) (by simpa [cpushL] using h)

theorem cpushR_spec {b : Fin 2} {R T : List SymRTok}
    (h : cpushR b R = some T) : encSR CV T = b >> encSR CV R := by
  fin_cases b
  · exact encSR_pushZerosR (v := CV) (by simpa [cpushR] using h)
  · exact encSR_pushOnesR (v := CV) (by simpa [cpushR] using h)

def cflip (s : CState) : Option CState := do
  if s.right then
    let (b,R) ← symPopBitR s.R
    let L ← cpushL b s.L
    return ⟨s.q,false,L,R⟩
  else
    let (b,L) ← symPopBitL s.L
    let R ← cpushR b s.R
    return ⟨s.q,true,L,R⟩

theorem cflip_spec {s t : CState} (h : cflip s = some t) : ceval s = ceval t := by
  rcases s with ⟨q,d,L,R⟩
  cases d
  · cases hp : symPopBitL L with
    | none => simp [cflip,hp] at h
    | some p =>
      rcases p with ⟨b,L'⟩
      cases hw : cpushR b R with
      | none => simp [cflip,hp,hw] at h
      | some R' =>
        simp [cflip,hp,hw] at h
        subst t
        simp only [ceval, Bool.false_eq_true, if_false, if_true, Cfg.headLeft, Cfg.headRight,
          encSL_popBitL (v := CV) hp, cpushR_spec hw, ListBlank.head_cons, ListBlank.tail_cons]
  · cases hp : symPopBitR R with
    | none => simp [cflip,hp] at h
    | some p =>
      rcases p with ⟨b,R'⟩
      cases hw : cpushL b L with
      | none => simp [cflip,hp,hw] at h
      | some L' =>
        simp [cflip,hp,hw] at h
        subst t
        simp only [ceval, Bool.false_eq_true, if_false, if_true, Cfg.headLeft, Cfg.headRight,
          encSR_popBitR (v := CV) hp, cpushL_spec hw, ListBlank.head_cons, ListBlank.tail_cons]

def cstep (M : Machine (Fin 2) (Fin 6)) (s : CState) : Option CState := do
  if s.right then
    let (b,R) ← symPopBitR s.R
    match M s.q b with
    | some (some q, .write w .right) =>
      let L ← cpushL w s.L
      return ⟨q,true,L,R⟩
    | some (some q, .write w .left) =>
      let R' ← cpushR w R
      return ⟨q,false,s.L,R'⟩
    | _ => none
  else
    let (b,L) ← symPopBitL s.L
    match M s.q b with
    | some (some q, .write w .right) =>
      let L' ← cpushL w L
      return ⟨q,true,L',s.R⟩
    | some (some q, .write w .left) =>
      let R ← cpushR w s.R
      return ⟨q,false,L,R⟩
    | _ => none

theorem cstep_spec {M : Machine (Fin 2) (Fin 6)} {s t : CState}
    (h : cstep M s = some t) : step M (ceval s) = some (ceval t) := by
  rcases s with ⟨q,d,L,R⟩
  cases d
  · cases hp : symPopBitL L with
    | none => simp [cstep,hp] at h
    | some p =>
      rcases p with ⟨b,L'⟩
      cases hm : M q b with
      | none => simp [cstep,hp,hm] at h
      | some tr =>
        rcases tr with ⟨qn,stmt⟩
        cases qn with
        | none => cases stmt <;> simp [cstep,hp,hm] at h
        | some q' =>
          rcases stmt with ⟨w,dir⟩
          cases dir
          · cases hw : cpushR w R with
            | none => simp [cstep,hp,hm,hw] at h
            | some R' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSL_popBitL (v := CV) hp,
                cpushR_spec hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
          · cases hw : cpushL w L' with
            | none => simp [cstep,hp,hm,hw] at h
            | some L'' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSL_popBitL (v := CV) hp,
                cpushL_spec hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
  · cases hp : symPopBitR R with
    | none => simp [cstep,hp] at h
    | some p =>
      rcases p with ⟨b,R'⟩
      cases hm : M q b with
      | none => simp [cstep,hp,hm] at h
      | some tr =>
        rcases tr with ⟨qn,stmt⟩
        cases qn with
        | none => cases stmt <;> simp [cstep,hp,hm] at h
        | some q' =>
          rcases stmt with ⟨w,dir⟩
          cases dir
          · cases hw : cpushR w R' with
            | none => simp [cstep,hp,hm,hw] at h
            | some R'' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSR_popBitR (v := CV) hp,
                cpushR_spec hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]
          · cases hw : cpushL w L with
            | none => simp [cstep,hp,hm,hw] at h
            | some L' =>
              simp [cstep,hp,hm,hw] at h
              subst t
              simp [ceval,step,Cfg.headLeft,Cfg.headRight,encSR_popBitR (v := CV) hp,
                cpushL_spec hw,hm,Tape.write,Tape.move,ListBlank.head_cons,ListBlank.tail_cons]

def csym (s : CState) : Option SymState :=
  if s.q = 0 ∧ s.right = true then some (.mA,s.L,s.R)
  else if s.q = 3 ∧ s.right = false then some (.mD,s.L,s.R)
  else if s.q = 4 ∧ s.right = false then some (.mE,s.L,s.R)
  else none

theorem csym_spec {s : CState} {u : SymState} (h : csym s = some u) :
    ceval s = evalSym CV u := by
  rcases s with ⟨q,d,L,R⟩
  simp only [csym] at h
  split at h
  · rename_i hq
    rcases hq with ⟨rfl,rfl⟩
    cases h
    rfl
  · split at h
    · rename_i hq
      rcases hq with ⟨rfl,rfl⟩
      cases h
      rfl
    · split at h
      · rename_i hq
        rcases hq with ⟨rfl,rfl⟩
        cases h
        rfl
      · contradiction

def cofSym : SymState → Option CState
  | (.mA,L,R) => some ⟨0,true,L,R⟩
  | (.mD,L,R) => some ⟨3,false,L,R⟩
  | (.mE,L,R) => some ⟨4,false,L,R⟩
  | (.mHalt,_,_) => none

theorem cofSym_spec {u : SymState} {t : CState} (h : cofSym u = some t) :
    evalSym CV u = ceval t := by
  rcases u with ⟨m,L,R⟩
  cases m <;> cases h <;> rfl

def cmacro (s : CState) : Option CState := do
  let u ← csym s
  let v ← symStep u
  cofSym v

theorem cmacro_spec {s t : CState} (h : cmacro s = some t) :
    ReachesPlus target_tm (ceval s) (ceval t) := by
  cases hu : csym s with
  | none => simp [cmacro,hu] at h
  | some u =>
    cases hv : symStep u with
    | none => simp [cmacro,hu,hv] at h
    | some v =>
      have ht : cofSym v = some t := by simpa [cmacro,hu,hv] using h
      rw [csym_spec hu,← cofSym_spec ht]
      exact symStep_sound CV hv

def cnorm (s : CState) : Option CState :=
  if (s.q = 0 ∧ s.right = false) ∨ ((s.q = 3 ∨ s.q = 4) ∧ s.right = true)
  then cflip s else some s

theorem cnorm_spec {s t : CState} (h : cnorm s = some t) : ceval s = ceval t := by
  unfold cnorm at h
  split at h
  · exact cflip_spec h
  · cases h
    rfl

def cadvance (M : Machine (Fin 2) (Fin 6)) (s : CState) : Option CState := do
  let u ← cnorm s
  match cmacro u with
  | some v => some v
  | none => cstep M u

theorem cadvance_spec (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    {s t : CState} (h : cadvance M s = some t) :
    ReachesPlus M (ceval s) (ceval t) := by
  cases hu : cnorm s with
  | none => simp [cadvance,hu] at h
  | some u =>
    rw [cnorm_spec hu]
    cases hv : cmacro u with
    | none =>
      exact ReachesPlus.single (cstep_spec (by simpa [cadvance,hu,hv] using h))
    | some v =>
      have ht : v = t := by simpa [cadvance,hu,hv] using h
      subst t
      exact reachesPlus_ext M he (cmacro_spec hv)

def crun (M : Machine (Fin 2) (Fin 6)) : Nat → CState → Option CState
  | 0,s => some s
  | n+1,s => (cadvance M s).bind (crun M n)

theorem crun_spec (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    (n : Nat) {s t : CState} (h : crun M n s = some t) :
    ReachesStar M (ceval s) (ceval t) := by
  induction n generalizing s with
  | zero =>
    simp [crun] at h
    subst t
    exact ReachesStar.refl _ _
  | succ n ih =>
    cases hu : cadvance M s with
    | none => simp [crun,hu] at h
    | some u =>
      have hv : crun M n u = some t := by simpa [crun,hu] using h
      exact (cadvance_spec M he hu).to_star.trans (ih hv)

#print axioms crun_spec

def permAD (q : Fin 6) : Fin 6 := if q = 0 then 3 else if q = 3 then 0 else q
theorem permAD_inv (q : Fin 6) : permAD (permAD q) = q := by fin_cases q <;> rfl

def flipDir : Dir → Dir
  | .left => .right
  | .right => .left

def decodeMirrored (c : Nat) : Option (Option (Fin 6) × Stmt (Fin 2)) :=
  if c < 24 then
    some (some (permAD ⟨(c/4)%6, Nat.mod_lt _ (by decide)⟩),
      .write ⟨(c/2)%2, Nat.mod_lt _ (by decide)⟩ (if c%2 = 1 then .left else .right))
  else none

def cvariant (a f : Nat) : Machine (Fin 2) (Fin 6) :=
  fun q b => match target_tm q b with
  | some v => some v
  | none => if q = 3 ∧ b = 1 then decodeMirrored a
            else if q = 5 ∧ b = 0 then decodeMirrored f
            else none

theorem cvariant_ext (a f : Nat) : ExtendsRestricted (cvariant a f) := by
  intro q b v h
  simp [cvariant,h]

def cstart : CState := ⟨3,false,[],[]⟩

def cflatL : List SymLTok → List (Fin 2)
  | [] => []
  | .pair z o c :: ts => (pWord z o ^ (evalSymN CV c + 1)) ++ cflatL ts
  | .mid c :: ts => (wLM ^ (evalSymN CV c + 1)) ++ cflatL ts

def cflatR : List SymRTok → List (Fin 2)
  | [] => []
  | .pair z o c :: ts => (pWord z o ^ (evalSymN CV c + 1)) ++ cflatR ts
  | .mid c :: ts => (wRM ^ (evalSymN CV c + 1)) ++ cflatR ts

theorem cflatL_spec (L : List SymLTok) : encSL CV L = cflatL L +> default := by
  induction L with
  | nil => rfl
  | cons t ts ih => cases t <;> simp only [encSL,cflatL,ih,ListBlank.append_assoc]

theorem cflatR_spec (R : List SymRTok) : encSR CV R = cflatR R +> default := by
  induction R with
  | nil => rfl
  | cons t ts ih => cases t <;> simp only [encSR,cflatR,ih,ListBlank.append_assoc]

def clenL : List SymLTok → Nat
  | [] => 0
  | .pair z o c :: ts => (z+o+1)*(evalSymN CV c+1)+clenL ts
  | .mid c :: ts => 9*(evalSymN CV c+1)+clenL ts

def clenR : List SymRTok → Nat
  | [] => 0
  | .pair z o c :: ts => (z+o+1)*(evalSymN CV c+1)+clenR ts
  | .mid c :: ts => 9*(evalSymN CV c+1)+clenR ts

def ceq (s t : CState) : Bool :=
  decide (s.q = t.q ∧ s.right = t.right) &&
  decide (clenL s.L = clenL t.L ∧ clenR s.R = clenR t.R) &&
  decide (cflatL s.L = cflatL t.L ∧ cflatR s.R = cflatR t.R)

theorem ceq_spec {s t : CState} (h : ceq s t = true) : ceval s = ceval t := by
  rcases s with ⟨q,d,L,R⟩
  rcases t with ⟨q',d',L',R'⟩
  simp only [ceq,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨rfl,rfl⟩,_⟩,hl,hr⟩ := h
  simp only [ceval,cflatL_spec,cflatR_spec,hl,hr]

def convTarget (i : Fin 6) (A M R0 : Nat) : CState :=
  ⟨4,false,[.pair 0 0 symZero,.pair 2 0 (symConst (A-1)),.mid (symConst (M-1))] ++ symTail i,
    [.pair 1 1 (symConst (R0-1)),.pair 1 0 symZero]⟩

def cleanTarget (A B C : Nat) : CState :=
  ⟨4,false,[.pair 0 0 symZero,.pair 1 1 symZero],
    [.pair 1 1 symZero,.pair 2 0 symZero,.pair 1 1 (symConst (A-1)),.mid symZero,
      .pair 1 1 (symConst (B-1)),.pair 1 2 symZero,.pair 1 1 (symConst (C-1)),.pair 1 0 symZero]⟩

def mirCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map permAD, ⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

def mirMachine (M : Machine (Fin 2) (Fin 6)) : Machine (Fin 2) (Fin 6) :=
  fun q b => (M (permAD q) b).map (fun (qn,stmt) =>
    match stmt with | .write w d => (qn.map permAD,.write w (flipDir d)))

theorem mir_step {M : Machine (Fin 2) (Fin 6)} {c t : Cfg (Fin 2) (Fin 6)}
    (h : step M c = some t) : step (mirMachine M) (mirCfg c) = some (mirCfg t) := by
  rcases c with ⟨q,tape⟩
  cases q with
  | none => cases h
  | some q =>
    cases hm : M q tape.head with
    | none => simp [step,hm] at h
    | some tr =>
      rcases tr with ⟨qn,stmt⟩
      rcases stmt with ⟨w,d⟩
      cases d <;> simp [step,hm] at h <;> subst t <;>
        simp [step,mirCfg,mirMachine,permAD_inv,hm,flipDir,Tape.write,Tape.move]

theorem mir_multi (M : Machine (Fin 2) (Fin 6)) (n : Nat)
    {c t : Cfg (Fin 2) (Fin 6)} (h : multiStep M c n = some t) :
    multiStep (mirMachine M) (mirCfg c) n = some (mirCfg t) := by
  induction n generalizing c with
  | zero => cases h; rfl
  | succ n ih =>
    rw [multiStep_succ] at h ⊢
    cases hs : step M c with
    | none => simp [hs] at h
    | some u =>
      rw [hs,Option.bind_some] at h
      rw [mir_step hs,Option.bind_some]
      exact ih h

theorem mir_star {M : Machine (Fin 2) (Fin 6)} {c t : Cfg (Fin 2) (Fin 6)}
    (h : ReachesStar M c t) : ReachesStar (mirMachine M) (mirCfg c) (mirCfg t) := by
  obtain ⟨n,hn⟩ := h
  exact ⟨n,mir_multi M n hn⟩

theorem mir_plus {M : Machine (Fin 2) (Fin 6)} {c t : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus M c t) : ReachesPlus (mirMachine M) (mirCfg c) (mirCfg t) := by
  obtain ⟨n,hp,hn⟩ := h
  exact ⟨n,hp,mir_multi M n hn⟩

theorem cstart_mir : mirCfg (ceval cstart) = init [] := by
  rw [init_nil_eq_headRight]
  rfl

theorem c_entry_never (a f : Nat) {c : Cfg (Fin 2) (Fin 6)}
    (entry : ReachesStar (cvariant a f) (ceval cstart) c)
    (h : ReachesInvM c) : IsNotHalt (mirMachine (cvariant a f)) := by
  obtain ⟨u,hu,hI⟩ := restricted_entry_ext _ (cvariant_ext a f) c h
  let P : Cfg (Fin 2) (Fin 6) → Prop := fun v => ∃ w, InAttractor w ∧ mirCfg w = v
  have hentry := mir_star (entry.trans hu.to_star)
  rw [cstart_mir] at hentry
  apply IsNotHalt.of_reachesPlus_invariant (P := P) hentry
  · exact ⟨u,hI,rfl⟩
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := hv
    obtain ⟨w',hr,hI'⟩ := attractor_closed_ext _ (cvariant_ext a f) w hw
    exact ⟨mirCfg w',mir_plus hr,⟨w',hI',rfl⟩⟩

#print axioms c_entry_never
