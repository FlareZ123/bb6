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
