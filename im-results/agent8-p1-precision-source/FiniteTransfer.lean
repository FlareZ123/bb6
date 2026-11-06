import PrecisionLanguage

namespace BB6.Agent8Precision
open BB6.Agent8FiniteBridge

/-- Every bounded-cost dyadic base graph yields a genuine finite-list
certificate for every perturbation at precision 2^(K+M). The produced list
is mathematically finite although a large-parameter instance is impractical
to enumerate, so the proof uses symbolic closure instead of evaluation. -/
theorem finite_precision_transfer (K M L0 zbase c r : Nat)
    (base : List (Nat × Nat))
    (hroot : (0,zbase) ∈ base)
    (hclosed : ∀ m z t v zp, (m,z)∈base → z=2^t*v →
       2*zp+1=L0+m+t+v → (m+t+1,zp)∈base)
    (hsmall : ∀ m z, (m,z)∈base → m≤M)
    (hnodiv : ∀ m z, (m,z)∈base → ¬2^K∣z)
    (hbound : zbase+2^(K+M)*(c*r) ≤ (L0+16*2^(K+M)*r)+M) :
    ∃ nodes : List (Nat × Nat),
      (0,zbase+2^(K+M)*(c*r))∈nodes ∧
      (∀ m z t v zp, (m,z)∈nodes → z=2^t*v →
        2*zp+1=(L0+16*2^(K+M)*r)+m+t+v →
        (m+t+1,zp)∈nodes) ∧
      (∀ m z, (m,z)∈nodes → m≤M) ∧
      (∀ m z, (m,z)∈nodes → ¬2^K∣z) := by
  classical
  let S : Nat → Nat → Prop := fun m z => (m,z)∈base
  let T := lifted K M r S
  let L := L0+16*2^(K+M)*r
  let nodes := listed M (L+M) T
  have hs : ∀ m z, S m z → m≤M := hsmall
  have hn : ∀ m z, S m z → ¬2^K∣z := hnodiv
  have hc : ∀ m z t v zp, S m z → z=2^t*v →
      2*zp+1=L0+m+t+v → S (m+t+1) zp := hclosed
  have ht_small := lifted_cost K M r S hs
  have ht_nodiv := lifted_nodiv K M r S hs hn
  have ht_closed := lifted_closed K M L0 r S hs hn hc
  refine ⟨nodes, ?_, ?_, ?_, ?_⟩
  · apply (mem_listed M (L+M) 0 (zbase+2^(K+M)*(c*r)) T).mpr
    refine ⟨by omega, ?_, ?_⟩
    · simpa [L] using hbound
    · exact lifted_root K M r zbase c S hroot
  · intro m z t v zp hm hdiv hnext
    exact listed_closed L M T ht_small (by
      intro mm zz tt vv zzp hmem hd hnn
      exact ht_closed mm zz tt vv zzp hmem hd (by simpa [L] using hnn))
      m z t v zp hm hdiv hnext
  · intro m z hm
    exact (listed_bounds K L M T ht_small ht_nodiv m z hm).1
  · intro m z hm
    have hbase : T m z := ((mem_listed M (L+M) m z T).mp hm).2.2
    exact ht_nodiv m z hbase

#print axioms finite_precision_transfer
end BB6.Agent8Precision
