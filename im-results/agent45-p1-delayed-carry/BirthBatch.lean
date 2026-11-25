import BirthBlock
namespace BB6.Agent45ReverseBlock
open BB6.Agent9BatchCarry (live terminal mem_batch)

/-- A certificate covers all genuine carries at q and excludes every earlier
    inspected central birth up to the start clock top. -/
def BlockVerified (F R top q : Nat) (xs : List Nat) : Prop :=
  (∀ c∈live q (F-q), c∈xs) ∧
  (∀ n, q≤n+4 → n+4≤top → n%2=0 → n≤R → (n+2)/2∉live (n+4) (F-(n+4)))

theorem block_start (F R : Nat) (hR : R+4<F) : BlockVerified F R F F (terminal F) := by
  constructor
  · simp [live]
  · intro n hlo hhi he hr; omega

def blockAdvance (F R k : Nat) (xs : List Nat) : Bool × List Nat :=
  (birthsChecked F k R xs, blockBack F k xs)

theorem verified_advance (F R top q k : Nat) (xs ys : List Nat)
    (hq : q≤F) (hk : k+4≤q) (hfit : 2^(k+2)≤q)
    (hc : BlockVerified F R top q xs) (h : blockAdvance q R k xs=(true,ys)) :
    BlockVerified F R top (q-k) ys := by
  have hb : birthsChecked q k R xs=true := congrArg Prod.fst h
  have hy : blockBack q k xs=ys := congrArg Prod.snd h
  have hpow : 2^(k+1)≤q := by rw [show k+2=k+1+1 by omega,Nat.pow_succ] at hfit; omega
  constructor
  · intro c hm
    have hh := blockBack_cover q k (F-q) xs (by omega) hpow hc.1 c
    rw [hy] at hh
    exact hh (by simpa [show k+(F-q)=F-(q-k) by omega] using hm)
  · intro n hlo hhi he hr
    by_cases hq' : n+4≤q
    · simpa [show q+(F-q)=F by omega] using birthsChecked_sound q k R (F-q) n xs hk hfit hc.1 hb hlo hq' he hr
    · exact hc.2 n (by omega) hhi he hr

/-- Local exact computations may cover many fitted blocks per kernel equality. -/
def advanceMany (R k q : Nat) (xs : List Nat) : Nat → Bool × List Nat
  | 0 => (true,xs)
  | d+1 =>
    let out := blockAdvance q R k xs
    if out.1 then advanceMany R k (q-k) out.2 d else (false,[])

theorem verified_many (F R top q k d : Nat) (xs ys : List Nat)
    (hq : q≤F) (hk : k*d+4≤q) (hfit : 2^(k+2)≤q-k*d+k)
    (hc : BlockVerified F R top q xs) (he : advanceMany R k q xs d=(true,ys)) :
    BlockVerified F R top (q-k*d) ys := by
  induction d generalizing q xs with
  | zero =>
    simp [advanceMany] at he
    subst ys
    simpa using hc
  | succ d ih =>
    simp only [Nat.mul_succ] at hk hfit ⊢
    simp only [advanceMany] at he
    split at he <;> rename_i hb
    · have h := verified_advance F R top q k xs (blockAdvance q R k xs).2 hq (by omega) (by omega) hc
          (by cases hp : blockAdvance q R k xs; simp [hp] at hb ⊢; exact hb)
      have hfit' : 2^(k+2)≤q-k-k*d+k := by omega
      have hh := ih (q-k) (blockAdvance q R k xs).2 (by omega) (by omega) hfit' h he
      simpa [show q-k-k*d=q-(k*d+k) by omega] using hh
    · simp at he

theorem batch_absent_of_verified (F R top lo q n : Nat) (xs : List Nat)
    (hq : q≤lo+4) (hR : R+4≤top) (ht : top≤F)
    (hlo : lo≤n) (hhi : n≤R) (cert : BlockVerified F R top q xs) :
    n∉BB6.Agent9BatchCarry.batch F lo := by
  intro h
  obtain ⟨_,_,he,hcenter⟩ := (mem_batch F lo n (by omega)).mp h
  exact cert.2 n (by omega) (by omega) he hhi hcenter

#print axioms verified_advance
#print axioms verified_many
#print axioms batch_absent_of_verified
end BB6.Agent45ReverseBlock
