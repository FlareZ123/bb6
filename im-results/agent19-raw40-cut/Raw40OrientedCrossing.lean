import CrossingGenerate
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent19OrientedCrossing
open BB6Coverage Agent50Zipper Agent42Crossing

-- Involutive state swap and spatial reflection. The state swap changes
-- the transformed blank entry state, not the original machine's root.
def qmap (swap : Bool) (q : Fin 6) : Fin 6 :=
  if swap then (if q = 0 then 2 else if q = 2 then 0 else q) else q

theorem qmap_inv (s : Bool) (q : Fin 6) : qmap s (qmap s q) = q := by
  cases s
  · rfl
  · by_cases h0 : q = 0
    · subst q; decide
    · by_cases h2 : q = 2
      · subst q; decide
      · simp [qmap,h0,h2]

def pos (flip : Bool) (h : Int) : Int := if flip then -h else h
def dir (flip : Bool) (d : Bool) : Bool := if flip then !d else d

theorem pos_inv (f : Bool) (h : Int) : pos f (pos f h) = h := by
  cases f <;> simp [pos]

theorem pos_eq (f : Bool) (x h : Int) : pos f x = h ↔ x = pos f h := by
  constructor
  · intro H
    have K := congrArg (pos f) H
    simpa only [pos_inv] using K
  · intro H
    rw [H,pos_inv]

theorem pos_move (f d : Bool) (h : Int) :
    pos f (h + (if dir f d then 1 else -1)) =
      pos f h + (if d then 1 else -1) := by
  cases f <;> cases d <;> simp [pos,dir] <;> omega

def orientMove (f s : Bool) (v : Move) : Move :=
  ⟨v.write,dir f v.right,qmap s v.next⟩

def orientConfig (f s : Bool) : Config → Config
  | ⟨q,h,t⟩ => ⟨qmap s q,pos f h,fun x => t (pos f x)⟩

def orientMachine (f s : Bool) (m : Machine) : Machine :=
  fun slot => (m (qmap s slot.1,slot.2)).map (orientMove f s)

def orientPartial (f s : Bool) (p : PartialMachine) : PartialMachine :=
  fun slot => (p (qmap s slot.1,slot.2)).map (Option.map (orientMove f s))

theorem orient_compatible (f s : Bool) (p : PartialMachine) (m : Machine)
    (hm : compatible p m) : compatible (orientPartial f s p) (orientMachine f s m) := by
  intro slot tr ht
  change (p (qmap s slot.1,slot.2)).map (Option.map (orientMove f s)) = some tr at ht
  cases hp : p (qmap s slot.1,slot.2) with
  | none => simp [hp] at ht
  | some v =>
    have htr : v.map (orientMove f s) = tr := by simpa [hp] using ht
    rw [← htr]
    unfold orientMachine
    rw [hm _ _ hp]

theorem read_orient (f s : Bool) (c : Config) :
    readSlot (orientConfig f s c) = (qmap s (readSlot c).1,(readSlot c).2) := by
  rcases c with ⟨q,h,t⟩
  simp [readSlot,orientConfig,pos_inv]

theorem move_orient (f s : Bool) (c : Config) (v : Move) :
    orientConfig f s (applyMove c (orientMove f s v)) =
      applyMove (orientConfig f s c) v := by
  rcases c with ⟨q,h,t⟩
  rcases v with ⟨w,d,q'⟩
  simp [orientConfig,orientMove,applyMove,qmap_inv,pos_eq]
  constructor
  · cases f <;> cases d <;> simp [pos,dir] <;> omega
  · rfl

theorem step_orient (f s : Bool) (m : Machine) (c : Config) :
    rawStep m (orientConfig f s c) =
      (rawStep (orientMachine f s m) c).map (orientConfig f s) := by
  unfold rawStep orientMachine
  rw [read_orient]
  cases H : m (qmap s (readSlot c).1,(readSlot c).2) <;>
    simp [H,move_orient]

theorem run_orient (f s : Bool) (m : Machine) (n : Nat) (c : Config) :
    run m n (orientConfig f s c) =
      (run (orientMachine f s m) n c).map (orientConfig f s) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [show n+1=1+n by omega,run_append,run_append]
    have hs : run m 1 (orientConfig f s c) =
        (run (orientMachine f s m) 1 c).map (orientConfig f s) := by
      simpa [run] using step_orient f s m c
    rw [hs]
    cases H : run (orientMachine f s m) 1 c with
    | none => rfl
    | some z => simpa using ih z

def initialZ (s : Bool) : Z := ⟨qmap s 0,0,[],[]⟩

theorem initial_orient (f s : Bool) :
    orientConfig f s (embed (initialZ s)) = blank := by
  cases f <;> simp [initialZ,embed,orientConfig,blank,pos,qmap_inv,atCell]

def entryOKFrom (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat) (h : Int) : Prop :=
  match zrun p entry init with
  | none => False
  | some z => z.q=0 ∧ z.h=h ∧ padEq z.l []=true ∧
      padEq z.r ((expand 0 c.right).map Cell.bit)=true

instance entryDecFrom (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat) (h : Int) :
    Decidable (entryOKFrom p c init entry h) :=
  match he : zrun p entry init with
  | none => by simp only [entryOKFrom,he]; infer_instance
  | some z => by simp only [entryOKFrom,he]; infer_instance

def checkedFrom (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat) (h : Int) : Prop :=
  certOK p c ∧ c.head.events ≠ [] ∧ inputBlank c ∧ recOK c ∧ entryOKFrom p c init entry h

instance checkedDecFrom (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat) (h : Int) :
    Decidable (checkedFrom p c init entry h) := by
  unfold checkedFrom; infer_instance

theorem entry_sound_from (p : PartialMachine) (c : Certificate) (init : Z) (entry : Nat) (h : Int)
    (he : entryOKFrom p c init entry h) (m : Machine) (hm : compatible p m) :
    run m entry (embed init) = some (family c h 0) := by
  cases hz : zrun p entry init with
  | none => simp [entryOKFrom,hz] at he
  | some z =>
    simp only [entryOKFrom,hz] at he
    have hf : embed z = family c h 0 :=
      embed_congr _ _ he.1 he.2.1 (padEq_sound _ _ he.2.2.1) (padEq_sound _ _ he.2.2.2)
    have H := zrun_sound p m hm entry init z hz
    rwa [hf] at H

-- Only the original blank starts in A. In the oriented machine the entry
-- is from initialZ s, while the repeated certificate starts in oriented A.
theorem never_oriented (f s : Bool) (p : PartialMachine) (c : Certificate)
    (entry : Nat) (h : Int)
    (hc : checkedFrom (orientPartial f s p) c (initialZ s) entry h)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨hcert,hn,hb,hr,he⟩ := hc
  have hcompat := orient_compatible f s p m hm
  have arbitrarily : ∀ n, ∃ k j, n≤k ∧
      run (orientMachine f s m) k (embed (initialZ s)) = some (family c j n) := by
    intro n
    induction n with
    | zero =>
      exact ⟨entry,h,by omega,entry_sound_from _ _ _ _ _ he _ hcompat⟩
    | succ n ih =>
      obtain ⟨k,j,hk,h1⟩ := ih
      obtain ⟨cost,j',hp,h2⟩ := recurrence _ _ hcert hn hb hr _ hcompat j n
      exact ⟨k+cost,j',by omega,by rw [run_append,h1]; exact h2⟩
  intro n
  obtain ⟨k,j,hk,h1⟩ := arbitrarily n
  have H := run_orient f s m k (embed (initialZ s))
  rw [initial_orient,h1] at H
  change run m k blank = some (orientConfig f s (family c j n)) at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases hh : run m n blank with
  | none => simp [hh] at H
  | some z => rfl

-- Untrusted constructor: the witness is judged by checkedFrom, not this code.
def constructFrom (p : PartialMachine) (init : Z) (entry period : Nat)
    (cuts : List (Nat × Nat)) : Option Certificate := do
  let z ← zrun p entry init
  let t ← buildRun p period (buildStart z)
  let full := t.l.reverse.map (fun c => c.finish false) ++
    t.c.finish true :: t.r.map (fun c => c.finish false)
  let k := ((t.l.length : Int)-t.h).toNat
  let head ← full[k]?
  return ⟨(full.take k).reverse,head,splitSegments 0 (full.drop (k+1)) cuts⟩

def witnessFrom (p : PartialMachine) (init : Z) (entry period : Nat)
    (cuts : List (Nat × Nat)) : Certificate :=
  (constructFrom p init entry period cuts).getD defaultCert

#print axioms run_orient
#print axioms never_oriented
end BB6Coverage.Agent19OrientedCrossing
