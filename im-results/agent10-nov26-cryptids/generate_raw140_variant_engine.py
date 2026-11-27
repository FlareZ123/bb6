"""Derive a NEW nine-row proof module from the pinned Apache-2.0 upstream proof.
The original upstream module and its trusted section are not edited or imported as a
claim about the restricted table. Every retained proof is elaborated again against
the explicit restricted semantics. Disallow all accelerators beginning with D1.
"""
import sys
from pathlib import Path

SRC="M_1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LAHHH"
DST="Raw140VariantEngine"
root=Path(sys.argv[1])
folder=root/"BusyBeaver/BB6/NonHalt"
s=(folder/(SRC+".lean")).read_text()
# Preserve copyright and all dependency declarations. Replace the explanatory
# header so the new module is not confused with the old blank-tape theorem.
i=s.index("/-!\n# Busy Beaver Machine")
j=s.index("open Mathlib Relation Nat Turing BusyBeaver",i)
s=s[:i]+"/-! # Restricted nine-transition attractor (derived proof; not the upstream goal). -/\n\n"+s[j:]
s=s.replace("BusyBeaver."+SRC,"BusyBeaver."+DST)
i=s.index("@[expose] public section")
j=s.index("@[expose] public section",i+1)
s=s[:i]+s[j:]
s=s.replace("-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)","-- New explicit restricted transition definition.")
s=s.replace("/-- Transition function for "+chr(96)+"1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---"+chr(96)+". -/","/-- The common nine-row mirrored subsystem; D1,F0,F1 are absent. -/")
def replace_once(old,new):
 global s
 assert s.count(old)==1,old
 s=s.replace(old,new)
replace_once("| 3, 1 => some (some 5, Stmt.write 0 Dir.left)","| 3, 1 => none")
replace_once("| 5, 0 => some (some 0, Stmt.write 0 Dir.left)","| 5, 0 => none")
def cut(a,b,replacement=""):
 global s
 i=s.index(a);j=s.index(b,i+len(a))
 s=s[:i]+replacement+s[j:]
cut("private theorem exit_d_11_halt","private theorem exit_d_01")
cut("private theorem step_dl_1_wZ","private theorem step_el_11_01")
i=s.index("| (.mD, L0, R0) =>",s.index("def symStepBase"))
j=s.index("        if l1 == 1 then\n",i)
k=s.index("\n        else\n",j)
s=s[:j]+"        if l1 == 1 then none"+s[k:]
i=s.index("  | mD =>",s.index("private theorem symStepBase_sound"))
j=s.index("    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb1))] at h;",i)
k=s.index("    · rw [(ite_eq_right_of_eq_false _ _ (eq_false hb1))] at h",j)
s=s[:j]+"    · rw [(ite_eq_left_of_eq_true _ _ (eq_true hb1))] at h; cases h\n"+s[k:]
i=s.index("def symTryDL1WZ")
j=s.index("def symTry",i+10)
s=s[:i]+"""def symTryDL1WZ (_L : List SymLTok) (_R : List SymRTok) : Option SymState := none

private theorem symTryDL1WZ_sound (v : Fin 5 → ℕ) {L : List SymLTok} {R : List SymRTok} {s' : SymState}
    (h : symTryDL1WZ L R = some s') :
    ReachesPlus target_tm (evalSym v (.mD, L, R)) (evalSym v s') := by
  simp [symTryDL1WZ] at h

"""+s[j:]
s=s[:s.index("/-! #### Stage 7:")]
s+="""
def ExtendsRestricted (M : Machine (Fin 2) (Fin 6)) : Prop :=
  ∀ q a v, target_tm q a = some v → M q a = some v

theorem step_ext (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    (c c' : Cfg (Fin 2) (Fin 6)) (h : step target_tm c = some c') :
    step M c = some c' := by
  rcases c with ⟨q,t⟩
  cases q with
  | none => cases h
  | some q =>
    cases htr : target_tm q t.head with
    | none => simp [step,htr] at h
    | some v => simpa only [step,htr,he q t.head v htr] using h

theorem multiStep_ext (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    (n : ℕ) (c c' : Cfg (Fin 2) (Fin 6)) (h : multiStep target_tm c n = some c') :
    multiStep M c n = some c' := by
  induction n generalizing c with
  | zero => exact h
  | succ n ih =>
    rw [multiStep_succ] at h ⊢
    cases hs : step target_tm c with
    | none => simp [hs] at h
    | some d =>
      rw [hs,Option.bind_some] at h
      rw [step_ext M he c d hs,Option.bind_some]
      exact ih d h

theorem reachesPlus_ext (M : Machine (Fin 2) (Fin 6)) (he : ExtendsRestricted M)
    {c c' : Cfg (Fin 2) (Fin 6)} (h : ReachesPlus target_tm c c') :
    ReachesPlus M c c' := by
  obtain ⟨n,hp,hn⟩ := h
  exact ⟨n,hp,multiStep_ext M he n c c' hn⟩

"""
s+="\n"+Path(sys.argv[2]).read_text()+"\n"
s+="\nend\nend BusyBeaver."+DST+"\n"
(folder/(DST+".lean")).write_text(s)
