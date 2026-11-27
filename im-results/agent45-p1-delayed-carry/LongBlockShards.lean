import LongBlockCover

namespace BB6.Agent45LongBlock
open BB6.Agent45ReverseBlock
open BB6.Agent45.DelayedCarry
open BB6.Agent9BatchCarry (packList packList_sound)

/-- Each bucket contains a base address and small relative positions. -/
def bucketMembers (bs : List (Nat × List Nat)) : List Nat :=
  bs.flatMap fun b => b.2.map (b.1+·)

def packBuckets : List (Nat × List Nat) → Nat
  | [] => 0
  | (b,xs)::bs => (packList xs <<< b) ||| packBuckets bs

theorem packBuckets_bit (bs : List (Nat × List Nat)) (c : Nat) :
    (packBuckets bs).testBit c=true ↔ c∈bucketMembers bs := by
  induction bs with
  | nil => simp [packBuckets,bucketMembers]
  | cons b bs ih =>
    obtain ⟨lo,xs⟩ := b
    simp only [packBuckets,bucketMembers,List.flatMap_cons,List.mem_append,Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,packList_sound,ih]
    apply or_congr _ Iff.rfl
    rw [List.mem_map]
    constructor
    · rintro ⟨hle,hm⟩
      exact ⟨c-lo,hm,by omega⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨by omega,by simpa using hx⟩

theorem live_bits_to_buckets (n B s k bits : Nat) (bs : List (Nat × List Nat))
    (hOld : LiveBits n B s k bits) (he : bits=packBuckets bs) :
    LiveList n B s k (bucketMembers bs) := by
  intro z c hw
  apply (packBuckets_bit bs c).mp
  rw [←he]
  exact hOld z c hw

/-- Linear adjacent-run deduplication. Membership is preserved even without
    a sorting hypothesis; mergeSort ensures that all duplicates are removed. -/
def dedupRuns : List Nat → List Nat
  | [] => []
  | x::xs => match dedupRuns xs with
    | [] => [x]
    | y::ys => if x=y then y::ys else x::y::ys

theorem mem_dedupRuns (xs : List Nat) (c : Nat) : c∈dedupRuns xs ↔ c∈xs := by
  induction xs with
  | nil => simp [dedupRuns]
  | cons x xs ih =>
    rw [dedupRuns]
    split
    · rename_i h
      simp [←ih,h]
    · rename_i y ys h
      by_cases hx : x=y
      · subst x; simp [←ih,h]
      · simp [hx,←ih,h]

def sortUnique (xs : List Nat) : List Nat := dedupRuns xs.mergeSort

theorem sortUnique_mem (xs : List Nat) (c : Nat) : c∈sortUnique xs ↔ c∈xs := by
  rw [sortUnique,mem_dedupRuns,List.mem_mergeSort]

def mergeUnique (xs ys : List Nat) : List Nat := dedupRuns (xs.merge ys)

theorem mergeUnique_mem (xs ys : List Nat) (c : Nat) :
    c∈mergeUnique xs ys ↔ c∈xs ∨ c∈ys := by
  rw [mergeUnique,mem_dedupRuns,List.mem_merge]

/-- A local reverse cover can be certified independently of every other shard. -/
def BlockShard (n B s j : Nat) (old new : List Nat) : Prop :=
  ∀ z c, z∈old → Walk (n+s+j+3) z (targetWord n s B j) c → c∈new

theorem block_shard_rows (L n B s j : Nat)
    (old new : List Nat) (rows : List WitnessRow)
    (hL : j≤2^L) (hrows : rows.map Prod.fst=old)
    (hcheck : rows.all (rowCheck L (n+s+j+3) j (targetDigits n s B j))=true)
    (hout : sortUnique (rowsOut (n+s+j+3) j rows)=new) :
    BlockShard n B s j old new := by
  intro z c hz hw
  rw [←hrows] at hz
  have hm := rows_cover L (n+s+j+3) (targetWord n s B j) rows
    (by simpa using hL) (by simpa [digits_targetWord] using hcheck) z c hz hw
  rw [targetWord_length] at hm
  rw [←hout]
  exact (sortUnique_mem _ c).mpr hm

theorem block_shard_merge (n B s j : Nat) (a b x y out : List Nat)
    (h1 : BlockShard n B s j a x) (h2 : BlockShard n B s j b y)
    (he : mergeUnique x y=out) : BlockShard n B s j (a++b) out := by
  intro z c hz hw
  rw [List.mem_append] at hz
  rw [←he,mergeUnique_mem]
  exact hz.elim (fun ha => Or.inl (h1 z c ha hw)) (fun hb => Or.inr (h2 z c hb hw))

theorem live_list_extend_shards (n B s j d : Nat) (old new old' : List Nat)
    (hOld : LiveList n B (s+j) d old)
    (hPartition : old=old')
    (hShard : BlockShard n B s j old' new) : LiveList n B s (j+d) new := by
  intro z c hw
  rw [targetWord_append] at hw
  obtain ⟨a,ht,hp⟩ := walk_split _ _ _ _ _ hw
  have ht' : Walk (n+(s+j)+d+3) z (targetWord n (s+j) B d) a := by simpa [Nat.add_assoc] using ht
  have hp' : Walk (n+s+j+3) a (targetWord n s B j) c := by
    simpa [show n+s+(j+d)+3-d=n+s+j+3 by omega] using hp
  have ha := hOld z a ht'
  rw [hPartition] at ha
  exact hShard a c ha hp'

#print axioms packBuckets_bit
#print axioms live_bits_to_buckets
#print axioms sortUnique_mem
#print axioms mergeUnique_mem
#print axioms block_shard_rows
#print axioms block_shard_merge
#print axioms live_list_extend_shards
end BB6.Agent45LongBlock
