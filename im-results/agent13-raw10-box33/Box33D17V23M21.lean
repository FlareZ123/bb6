import Box33PrefixMacro

namespace BB6.Agent13.Box33D17V23M21
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep cfg ones rep_add)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

-- The only halt row is D1. These are the exact twelve source transitions.
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .A false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .C false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => none
  | .E,false => some (left .F true c)
  | .E,true => some (left .E true c)
  | .F,false => some (right .A true c)
  | .F,true => some (right .F true c)

abbrev run := BB6.Agent13.Box33PrefixMacro.run step
theorem run_add (m n : Nat) (c : C9Pair.Config) :
    run (m+n) c = (run m c).bind (run n) :=
  BB6.Agent13.Box33PrefixMacro.run_add step m n c
abbrev zeros := rep [false]
abbrev DB (l r : Stream) := cfg .A l (word [false,false] r)
abbrev SB (l r : Stream) := cfg .A l (push false r)
def LP (q : Q) (l r : Stream) : C9Pair.Config := ⟨q,pop l,l 0,r⟩

theorem enterD (l r : Stream) :
    run 4 (DB (push false l) r) = some (LP .E l (word [false,false,true] r)) := by
  simp [DB,LP,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right,word]

theorem enterS (l r : Stream) :
    run 4 (SB l (word [true,true] r)) = some (LP .E (push true l) (word [false,false] r)) := by
  simp [SB,LP,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right,word]

theorem eStep (l r : Stream) :
    run 1 (LP .E (push true l) r) = some (LP .E l (push true r)) := by
  simp [LP,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem aStep (l r : Stream) :
    run 1 (cfg .A l (push true r)) = some (cfg .A (push false l) r) := by
  simp [cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fStep (l r : Stream) :
    run 1 (cfg .F l (push true r)) = some (cfg .F (push true l) r) := by
  simp [cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right]

theorem eSweep (k : Nat) (l r : Stream) :
    run k (LP .E (ones k l) r) = some (LP .E l (ones k r)) := by
  induction k generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ k ih =>
    rw [run_add,show ones (k+1) l = ones k (push true l) from rep_add [true] k 1 l,
      ih,Option.bind_some]
    exact eStep l (ones k r)
theorem aSweep (k : Nat) (l r : Stream) :
    run k (cfg .A l (ones k r)) = some (cfg .A (zeros k l) r) := by
  induction k generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ k ih =>
    rw [run_add,show ones (k+1) r = ones k (push true r) from rep_add [true] k 1 r,
      ih,Option.bind_some]
    exact aStep (zeros k l) r
theorem fSweep (k : Nat) (l r : Stream) :
    run k (cfg .F l (ones k r)) = some (cfg .F (ones k l) r) := by
  induction k generalizing l r with
  | zero => simp [BB6.Agent13.Box33PrefixMacro.run,rep]
  | succ k ih =>
    rw [run_add,show ones (k+1) r = ones k (push true r) from rep_add [true] k 1 r,
      ih,Option.bind_some]
    exact fStep (ones k l) r

theorem turn0 (y r : Stream) :
    run 2 (LP .E (word [false,false] y) r) = some (cfg .A (push true y) (push true r)) := by
  simp [LP,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right,word]
theorem turn1 (y r : Stream) :
    run 1 (LP .E (word [false,true] y) r) = some (cfg .F y (word [true,true] r)) := by
  simp [LP,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right,word]
theorem fFinish (l r : Stream) :
    run 1 (cfg .F l (word [false,false] r)) = some (SB (push true l) r) := by
  simp [SB,cfg,BB6.Agent13.Box33PrefixMacro.run,step,left,right,word]

theorem finish0 (k : Nat) (y r : Stream) :
    run (k+3) (LP .E (word [false,false] y) (ones k (word [false,false] r))) =
    some (DB (zeros (k+1) (push true y)) r) := by
  rw [show k+3=2+(k+1) by omega,run_add,turn0,Option.bind_some]
  exact aSweep (k+1) (push true y) (word [false,false] r)
theorem finish1 (k : Nat) (y r : Stream) :
    run (k+4) (LP .E (word [false,true] y) (ones k (word [false,false] r))) =
    some (SB (ones (k+3) y) r) := by
  rw [show k+4=1+(k+2)+1 by omega,run_add,run_add,turn1,Option.bind_some]
  change ((run (k+2) (cfg .F y (ones (k+2) (word [false,false] r)))).bind (run 1)) = _
  rw [fSweep,Option.bind_some,fFinish]
  rfl

-- Four universally quantified return rules, not bounded simulations.
theorem d0 (k : Nat) (y r : Stream) :
    run (2*k+7) (DB (push false (ones k (word [false,false] y))) r) =
      some (DB (zeros (k+1) (push true y)) (push true r)) := by
  rw [show 2*k+7=4+k+(k+3) by omega,run_add,run_add,enterD,Option.bind_some,eSweep,Option.bind_some]
  exact finish0 k y (push true r)
theorem d1 (k : Nat) (y r : Stream) :
    run (2*k+8) (DB (push false (ones k (word [false,true] y))) r) =
      some (SB (ones (k+3) y) (push true r)) := by
  rw [show 2*k+8=4+k+(k+4) by omega,run_add,run_add,enterD,Option.bind_some,eSweep,Option.bind_some]
  exact finish1 k y (push true r)
theorem s0 (k : Nat) (y r : Stream) :
    run (2*k+9) (SB (ones k (word [false,false] y)) (word [true,true] r)) =
      some (DB (zeros (k+2) (push true y)) r) := by
  rw [show 2*k+9=4+(k+1)+(k+1+3) by omega,run_add,run_add,enterS,Option.bind_some]
  change ((run (k+1) (LP .E (ones (k+1) (word [false,false] y)) (word [false,false] r))).bind (run (k+1+3))) = _
  rw [eSweep,Option.bind_some]
  exact finish0 (k+1) y r
theorem s1 (k : Nat) (y r : Stream) :
    run (2*k+10) (SB (ones k (word [false,true] y)) (word [true,true] r)) =
      some (SB (ones (k+4) y) r) := by
  rw [show 2*k+10=4+(k+1)+(k+1+4) by omega,run_add,run_add,enterS,Option.bind_some]
  change ((run (k+1) (LP .E (ones (k+1) (word [false,true] y)) (word [false,false] r))).bind (run (k+1+4))) = _
  rw [eSweep,Option.bind_some]
  exact finish1 (k+1) y r

-- Every pair (a,c) stores positive run lengths a+1 and c+1.
def enc : List (Nat × Nat) → Stream
  | [] => z
  | (a,c)::xs => zeros (a+1) (ones (c+1) (enc xs))
inductive Phase where
  | double (xs : List (Nat × Nat)) (b : Nat)
  | single (c : Nat) (xs : List (Nat × Nat)) (b : Nat)
def phase : Phase → C9Pair.Config
  | .double xs b => DB (enc xs) (ones b z)
  | .single c xs b => SB (ones (c+1) (enc xs)) (ones b z)

-- Run parity credit. Leading zero gaps and internal gaps have opposite parity.
def leadWeight (a c : Nat) : Nat :=
  if a%2=0 then 1 else if c%2=0 then 2 else 3
def gapWeight (d e : Nat) : Nat :=
  if d%2=1 then 1 else if e%2=0 then 2 else 3
def singleWeight (c : Nat) : Nat := if c%2=0 then 3 else 4
def tailPot : List (Nat × Nat) → Nat
  | [] => 0
  | (d,e)::xs => gapWeight d e + tailPot xs
def dPot : List (Nat × Nat) → Nat
  | [] => 0
  | (a,c)::xs => leadWeight a c + tailPot xs
def sPot (c : Nat) (xs : List (Nat × Nat)) : Nat := singleWeight c + tailPot xs
def potential : Phase → Nat
  | .double xs _ => dPot xs
  | .single c xs _ => sPot c xs
def fuel : Phase → Nat
  | .double _ b | .single _ _ b => b
def valid (p : Phase) : Prop := potential p ≤ fuel p

-- All cases, including the exact empty left stack, in one return map.
def advance : Phase → Nat × Phase
  | .double [] b => (7,.double [(0,0)] (b+1))
  | .double [(0,c)] b => (2*(c+1)+7,.double [(c+1,0)] (b+1))
  | .double ((0,c)::(0,e)::ys) b => (2*(c+1)+8,.single (c+e+3) ys (b+1))
  | .double ((0,c)::(1,e)::ys) b => (2*(c+1)+7,.double ((c+1,e+1)::ys) (b+1))
  | .double ((0,c)::(d+2,e)::ys) b => (2*(c+1)+7,.double ((c+1,0)::(d,e)::ys) (b+1))
  | .double ((1,c)::xs) b => (8,.single (c+2) xs (b+1))
  | .double ((2,c)::xs) b => (7,.double ((0,c+1)::xs) (b+1))
  | .double ((a+3,c)::xs) b => (7,.double ((0,0)::(a,c)::xs) (b+1))
  | .single c [] b => (2*(c+1)+9,.double [(c+2,0)] (b-2))
  | .single c ((0,e)::ys) b => (2*(c+1)+10,.single (c+e+4) ys (b-2))
  | .single c ((1,e)::ys) b => (2*(c+1)+9,.double ((c+2,e+1)::ys) (b-2))
  | .single c ((d+2,e)::ys) b => (2*(c+1)+9,.double ((c+2,0)::(d,e)::ys) (b-2))

theorem parity (n : Nat) : n%2=0 ∨ n%2=1 := by omega
theorem singleFuel (c : Nat) (xs : List (Nat × Nat)) (b : Nat)
    (h : valid (.single c xs b)) : 2≤b := by
  change singleWeight c + tailPot xs ≤ b at h
  unfold singleWeight at h
  split at h <;> omega

theorem positive : ∀ p : Phase, 0 < (advance p).1
  | .double [] b => by simp [advance]; omega
  | .double [(0,c)] b => by simp [advance]; omega
  | .double ((0,c)::(0,e)::ys) b => by simp [advance]; omega
  | .double ((0,c)::(1,e)::ys) b => by simp [advance]; omega
  | .double ((0,c)::(d+2,e)::ys) b => by simp [advance]; omega
  | .double ((1,c)::xs) b => by simp [advance]; omega
  | .double ((2,c)::xs) b => by simp [advance]; omega
  | .double ((a+3,c)::xs) b => by simp [advance]; omega
  | .single c [] b => by simp [advance]; omega
  | .single c ((0,e)::ys) b => by simp [advance]; omega
  | .single c ((1,e)::ys) b => by simp [advance]; omega
  | .single c ((d+2,e)::ys) b => by simp [advance]; omega

theorem preserved : ∀ p : Phase, valid p → valid (advance p).2
  | .double [] b, hv => by
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod] at hv ⊢ <;> omega
  | .double [(0,c)] b, hv => by
    rcases parity c with hc|hc <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc] at hv ⊢ <;> omega
  | .double ((0,c)::(0,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,he] at hv ⊢ <;> omega
  | .double ((0,c)::(1,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,he] at hv ⊢ <;> omega
  | .double ((0,c)::(d+2,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity d with hd|hd <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,hd,he] at hv ⊢ <;> omega
  | .double ((1,c)::xs) b, hv => by
    rcases parity c with hc|hc <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc] at hv ⊢ <;> omega
  | .double ((2,c)::xs) b, hv => by
    rcases parity c with hc|hc <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc] at hv ⊢ <;> omega
  | .double ((a+3,c)::xs) b, hv => by
    rcases parity a with ha|ha <;> rcases parity c with hc|hc <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,ha,hc] at hv ⊢ <;> omega
  | .single c [] b, hv => by
    rcases parity c with hc|hc <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc] at hv ⊢ <;> omega
  | .single c ((0,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,he] at hv ⊢ <;> omega
  | .single c ((1,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,he] at hv ⊢ <;> omega
  | .single c ((d+2,e)::ys) b, hv => by
    rcases parity c with hc|hc <;> rcases parity d with hd|hd <;> rcases parity e with he|he <;>
    simp [valid,advance,potential,fuel,dPot,sPot,tailPot,leadWeight,gapWeight,singleWeight,Nat.add_mod,hc,hd,he] at hv ⊢ <;> omega

theorem sound : ∀ p : Phase, valid p → run (advance p).1 (phase p) = some (phase (advance p).2)
  | .double [] b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 0 z (ones b z)
  | .double [(0,c)] b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 (c+1) z (ones b z)
  | .double ((0,c)::(0,e)::ys) b, hv => by
    have hh := d1 (c+1) (ones e (enc ys)) (ones b z)
    have he : ones (c+1+3) (ones e (enc ys)) = ones (c+e+4) (enc ys) := by
      rw [←rep_add,show c+1+3+e=c+e+4 by omega]
    rw [he] at hh
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using hh
  | .double ((0,c)::(1,e)::ys) b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 (c+1) (ones (e+1) (enc ys)) (ones b z)
  | .double ((0,c)::(d+2,e)::ys) b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 (c+1) (enc ((d,e)::ys)) (ones b z)
  | .double ((1,c)::xs) b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d1 0 (ones c (enc xs)) (ones b z)
  | .double ((2,c)::xs) b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 0 (ones (c+1) (enc xs)) (ones b z)
  | .double ((a+3,c)::xs) b, hv => by
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using d0 0 (enc ((a,c)::xs)) (ones b z)
  | .single c [] b, hv => by
    have hb := singleFuel c [] b hv
    obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2,by omega⟩
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using s0 (c+1) z (ones n z)
  | .single c ((0,e)::ys) b, hv => by
    have hb := singleFuel c ((0,e)::ys) b hv
    obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2,by omega⟩
    have hh := s1 (c+1) (ones e (enc ys)) (ones n z)
    have he : ones (c+1+4) (ones e (enc ys)) = ones (c+e+5) (enc ys) := by
      rw [←rep_add,show c+1+4+e=c+e+5 by omega]
    rw [he] at hh
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using hh
  | .single c ((1,e)::ys) b, hv => by
    have hb := singleFuel c ((1,e)::ys) b hv
    obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2,by omega⟩
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using s0 (c+1) (ones (e+1) (enc ys)) (ones n z)
  | .single c ((d+2,e)::ys) b, hv => by
    have hb := singleFuel c ((d+2,e)::ys) b hv
    obtain ⟨n,rfl⟩ : ∃ n, b=n+2 := ⟨b-2,by omega⟩
    simpa [advance,phase,enc,DB,SB,ones,zeros,rep,word] using s0 (c+1) (enc ((d,e)::ys)) (ones n z)

theorem never_phase (n : Nat) (p : Phase) (hv : valid p) : run n (phase p) ≠ none := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    intro h
    have he := sound p hv
    have hp := positive p
    by_cases hn : n ≤ (advance p).1
    · rw [←show n+((advance p).1-n)=(advance p).1 by omega,run_add,h] at he
      contradiction
    · rw [←show (advance p).1+(n-(advance p).1)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) _ (preserved p hv) h

open BB6Coverage
open Box17 (index decode)
abbrev project := Box33Source.project false
def codes : List (Fin 25) := [8,2,11,10,1,13,17,0,23,19,4,24]
def table : Machine := fun s => decode (codes.getD (index s).val 0)
theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever table step project_step
  intro n
  have hv : valid (.double [] 0) := by decide
  have hn := never_phase n (.double [] 0) hv
  simpa [phase,enc,DB,cfg,word,ones,rep,project,Box33Source.project,BB6Coverage.blank,Box33Source.q] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never
#print axioms preserved
#print axioms sound
#print axioms compatible_never
end BB6.Agent13.Box33D17V23M21
