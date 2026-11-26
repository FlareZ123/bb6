import PackedRun122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29PackedRun
open BB6Coverage BB6Coverage.Agent31Pump

theorem pack_append (xs ys : List Bool) : pack (xs ++ ys) = pack xs + 2^xs.length * pack ys := by
  induction xs with
  | nil => simp [pack]
  | cons b bs ih =>
    simp only [List.cons_append,pack,List.length_cons,ih,Nat.pow_succ,Nat.mul_add]
    ac_rfl

theorem pack_surj (n : Nat) : ∃ xs, pack xs = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · exact ⟨[],by simp [pack,hz]⟩
    · obtain ⟨xs,hxs⟩ := ih (n/2) (Nat.div_lt_self (by omega) (by decide))
      refine ⟨(n%2 == 1)::xs,?_⟩
      rw [pack,hxs]
      by_cases hb : n%2 = 1
      · simp [hb,Bool.toNat]; omega
      · simp [show (n%2 == 1) = false by simp [hb],Bool.toNat]; omega

def prepend (xs : List Bool) (n : Nat) : Nat := pack xs + 2^xs.length * n

def pzip (q : Fin 6) (lp rp : List Bool) (l r : Nat) : PZ :=
  ⟨q,prepend lp l,prepend rp r⟩

theorem psweepR (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++L,rp++I++R⟩ = some ⟨q,lp++O++L,rp++R⟩)
    (n L R : Nat) : prun p (k*n) (pzip q lp (rp++rep I n) L R) =
      some (pzip q (lp++rep O n) rp L R) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj R
  have hs := sweepR p q lp rp I O k one n ls rs
  have H := (enc_run p (k*n) ⟨q,lp++ls,rp++rep I n++rs⟩).symm.trans (congrArg (Option.map enc) hs)
  simpa only [enc,Option.map_some,pzip,prepend,pack_append,hl,hr] using H

theorem psweepL (p : PartialMachine) (q : Fin 6) (lp rp I O : List Bool) (k : Nat)
    (one : ∀ L R : List Bool, run0 p k ⟨q,lp++I++L,rp++R⟩ = some ⟨q,lp++L,rp++O++R⟩)
    (n L R : Nat) : prun p (k*n) (pzip q (lp++rep I n) rp L R) =
      some (pzip q lp (rp++rep O n) L R) := by
  obtain ⟨ls,hl⟩ := pack_surj L
  obtain ⟨rs,hr⟩ := pack_surj R
  have hs := sweepL p q lp rp I O k one n ls rs
  have H := (enc_run p (k*n) ⟨q,lp++rep I n++ls,rp++rs⟩).symm.trans (congrArg (Option.map enc) hs)
  simpa only [enc,Option.map_some,pzip,prepend,pack_append,hl,hr] using H

#print axioms psweepR
#print axioms psweepL
end BB6Coverage.Agent29PackedRun
