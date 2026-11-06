import AdaptiveLanguage

namespace BB6.Agent8Adaptive
open BB6.Agent8FiniteBridge

/-- Convert a base dyadic graph into a finite closure certificate at arbitrary
statewise precision D-m. Unlike uniform K+M transfer, D only needs to
exceed the sum of each actual graph-node cost and its dyadic valuation. -/
theorem finite_adaptive_transfer (D M L0 zbase c r : Nat)
    (base : List (Nat × Nat))
    (hroot : (0,zbase)∈base)
    (hclosed : ∀ m z t v zp, (m,z)∈base → z=2^t*v →
       2*zp+1=L0+m+t+v → (m+t+1,zp)∈base)
    (hsmall : ∀ m z, (m,z)∈base → m≤M)
    (hM : M≤D)
    (hstate : ∀ m z, (m,z)∈base → ¬2^(D-m)∣z)
    (hnodiv : ∀ m z, (m,z)∈base → ¬1024∣z)
    (hbound : zbase+2^D*(c*r) ≤ (L0+16*2^D*r)+M) :
    ∃ nodes : List (Nat × Nat),
      (0,zbase+2^D*(c*r))∈nodes ∧
      (∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
        2*zp+1=(L0+16*2^D*r)+m+t+v →
        (m+t+1,zp)∈nodes) ∧
      (∀ m z, (m,z)∈nodes → m≤M) ∧
      (∀ m z, (m,z)∈nodes → ¬1024∣z) := by
  classical
  let S : Nat → Nat → Prop := fun m z => (m,z)∈base
  let T := lifted D r S
  let L := L0+16*2^D*r
  let nodes := listed M (L+M) T
  have hs : ∀ m z, S m z → m≤M := hsmall
  have hmod : ∀ m z, S m z → ¬2^(D-m)∣z := hstate
  have hn : ∀ m z, S m z → ¬1024∣z := hnodiv
  have hc : ∀ m z t v zp, S m z → z=2^t*v →
      2*zp+1=L0+m+t+v → S (m+t+1) zp := hclosed
  have ht_small := cost D r M S hs
  have ht_nodiv := no1024 D M r S hs hM hmod hn
  have ht_closed := closed D L0 r M S hs hM hmod hc
  refine ⟨nodes, ?_, ?_, ?_, ?_⟩
  · apply (mem_listed M (L+M) 0 (zbase+2^D*(c*r)) T).mpr
    refine ⟨by omega, ?_, ?_⟩
    · simpa [L] using hbound
    · exact root D r zbase c S hroot
  · intro m z t v zp hm hdiv hnext
    exact listed_closed L M T ht_small (by
      intro mm zz tt vv zzp hmem hd hnn
      exact ht_closed mm zz tt vv zzp hmem hd (by simpa [L] using hnn))
      m z t v zp hm hdiv hnext
  · intro m z hm
    exact (listed_bounds 10 L M T ht_small (by
      intro mm zz hmem
      simpa using ht_nodiv mm zz hmem) m z hm).1
  · intro m z hm
    have hbase : T m z := ((mem_listed M (L+M) m z T).mp hm).2.2
    exact ht_nodiv m z hbase

#print axioms finite_adaptive_transfer
end BB6.Agent8Adaptive
