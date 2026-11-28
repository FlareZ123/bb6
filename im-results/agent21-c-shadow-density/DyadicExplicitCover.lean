import DyadicCover

namespace BB6.Agent21Dyadic

/-- Fully explicit computable universal depth for 1/d sparse inverse-word
    cylinders. Even though the bound grows far too quickly to enumerate
    for large d, it depends ONLY on the requested density denominator;
    there are no hidden existential choices over affine parameters. -/
def sparseCertificateDepth (d:Nat):Nat :=
  FiniteTree.extinctionDepth (fun B=>F B+1) 2 d

/-- Quantitative constructive strengthening of sparse_cover: the modulus
    is the exact closed recursive expression sparseCertificateDepth d.
    This exposes a computable bound needed by all future exact modular
    cone checker density certificates. -/
theorem sparse_cover_explicit (d:Nat) (hd:0<d):
    ∀ (a:Affine), Admissible a→∃R:List Int,
      d*R.length≤2^(sparseCertificateDepth d) ∧
      ∀ t:Int, OpenAt (mass a t) (norm a t) (sparseCertificateDepth d) →
        t%P (sparseCertificateDepth d)∈R := by
  intro a h
  let n:=sparseCertificateDepth d
  have hn : d*FiniteTree.count (next a h)
      (FiniteTree.live (fun s=>weight s.pop)) n (root a)≤2^n := by
    exact FiniteTree.extinction_at (next a h)
      (fun s=>weight s.pop)
      (fun s=>step_supermean a s.n s.b s.pop h s.valid)
      (fun B=>F B+1)
      (fun B s hs=>amplify_population a h s B hs)
      (root a) d hd
  let L := (leaves (next a h) n (root a)).filter
    (fun s=>0<weight s.pop)
  refine ⟨L.map (fun s=>s.b),?_,?_⟩
  · simpa [L,List.length_map,leaf_count,n] using hn
  · intro t ho
    let b:=t%P n
    have hlo : 0≤b := Int.emod_nonneg _ (P_ne _)
    have hhi : b<P n := Int.emod_lt_of_pos _ (P_pos _)
    obtain ⟨bits,hbl,hdepth,hprefix⟩ :=
      chooseBits a h (root a) n b hlo hhi
    let s:=runBits (next a h) (root a) bits
    have hsn:s.n=n := by simpa [s,root] using hdepth
    have hsb:s.b=b := by simpa [s,root,P] using hprefix
    have hsopen: OpenAt (mass a s.b) (norm a s.b) s.n := by
      rw [hsn,hsb]
      exact affine_mod_open a h t n ho
    have hweight:=open_weight a s hsopen
    have hmem:s∈leaves (next a h) n (root a) := by
      rw [←hbl]
      exact run_mem_leaves _ _ _
    have hL:s∈L := by simp [L,hmem,hweight]
    exact List.mem_map.mpr ⟨s,hL,hsb⟩

#print axioms sparse_cover_explicit
end BB6.Agent21Dyadic
