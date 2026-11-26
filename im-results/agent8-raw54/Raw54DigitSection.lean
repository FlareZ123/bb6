import Raw54RAClosedCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.DigitSection
open BB6Coverage BB6Coverage.Agent31Pump

/-- Binary digit language with a fixed section frame and terminal word. -/
def enc (z o : List Bool) : List Bool → List Bool
  | [] => []
  | false::xs => z ++ enc z o xs
  | true::xs => o ++ enc z o xs

def sec (q : Fin 6) (L m z o e : List Bool) (xs : List Bool) : Z0 :=
  ⟨q,L,m ++ enc z o xs ++ e⟩

def advance (over : List Bool) : List Bool → List Bool
  | [] => over
  | false::xs => true::xs
  | true::xs => false::advance over xs

def cost (a b c d : Nat) : Nat → List Bool → Nat
  | k, [] => c*k+d
  | k, false::_ => a*k+b
  | k, true::xs => cost a b c d (k+1) xs

theorem carry (p : PartialMachine) (q : Fin 6) (L m z o e : List Bool)
    (over : List Bool) (a b c d : Nat)
    (stop : ∀ k T, run0 p (a*k+b) ⟨q,L,m ++ rep o k ++ z ++ T⟩ =
      some ⟨q,L,m ++ rep z k ++ o ++ T⟩)
    (overflow : ∀ k, run0 p (c*k+d) ⟨q,L,m ++ rep o k ++ e⟩ =
      some ⟨q,L,m ++ rep z k ++ enc z o over ++ e⟩)
    (xs : List Bool) (k : Nat) :
    run0 p (cost a b c d k xs) ⟨q,L,m ++ rep o k ++ enc z o xs ++ e⟩ =
      some ⟨q,L,m ++ rep z k ++ enc z o (advance over xs) ++ e⟩ := by
  induction xs generalizing k with
  | nil => simpa only [enc,advance,cost,List.nil_append,List.append_assoc,List.append_nil] using overflow k
  | cons x xs ih =>
    cases x
    · simpa only [enc,advance,cost,List.append_assoc] using stop k (enc z o xs ++ e)
    · have h := ih (k+1)
      simpa only [enc,advance,cost,rep,← rep_snoc o k,← rep_snoc z k,List.append_assoc] using h

theorem cost_pos (a b c d : Nat) (hb : 0 < b) (hd : 0 < d) (k : Nat) (xs : List Bool) :
    0 < cost a b c d k xs := by
  induction xs generalizing k with
  | nil => simp only [cost]; omega
  | cons x xs ih => cases x <;> simp only [cost]; omega; exact ih (k+1)

theorem never (p : PartialMachine) (q : Fin 6) (L m z o e : List Bool)
    (over init : List Bool) (entry a b c d : Nat)
    (first : run0 p entry ⟨0,[],[]⟩ = some (sec q L m z o e init))
    (hb : 0 < b) (hd : 0 < d)
    (stop : ∀ k T, run0 p (a*k+b) ⟨q,L,m ++ rep o k ++ z ++ T⟩ =
      some ⟨q,L,m ++ rep z k ++ o ++ T⟩)
    (overflow : ∀ k, run0 p (c*k+d) ⟨q,L,m ++ rep o k ++ e⟩ =
      some ⟨q,L,m ++ rep z k ++ enc z o over ++ e⟩)
    (M : Machine) (hm : compatible p M) : NeverHalts M := by
  apply BB6.Agent8Raw54.RAClosed.neverOfSection p (List Bool) (sec q L m z o e) init entry first _ M hm
  intro xs
  refine ⟨cost a b c d 0 xs, advance over xs, cost_pos a b c d hb hd 0 xs, ?_⟩
  simpa only [sec,rep,List.nil_append,List.append_assoc,List.append_nil] using carry p q L m z o e over a b c d stop overflow xs 0
#print axioms never
end BB6.Agent8Raw54.DigitSection
