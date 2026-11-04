import Root119BGrowStages
namespace BB6Root119

def growTape (t : Int → Bool) (h : Int) : Int → Bool :=
  setBit (setBit (setBit (setBit (setBit (setBit (setBit t
     (h-7) true) (h-6) true) (h-5) true) (h-4) true)
     (h-2) false) (h-1) false) h true

/-- The 16-step computed write stream has a seven-slot normal form. -/
theorem growStage16_normalized (t : Int → Bool) (h : Int) (hv : growHyp t h) :
  gs16 t h = ⟨.B, h-8, growTape t h⟩ := by
  obtain ⟨h0v,h1v,h2v,h3v,h4v,h5v,h6v,h7v⟩ := hv
  unfold gs16 growTape
  congr 1
  funext x
  have h3 : t (h-3) = true := h3v
  simp only [setBit]
  by_cases h0 : x = h <;>
    by_cases h1 : x = h-1 <;>
    by_cases h2 : x = h-2 <;>
    by_cases h3 : x = h-3 <;>
    by_cases h4 : x = h-4 <;>
    by_cases h5 : x = h-5 <;>
    by_cases h6 : x = h-6 <;>
    by_cases h7 : x = h-7 <;>
    simp_all <;> omega

/-- Exact all-tape B/0 16-step boundary expansion, including normal-form writes. -/
theorem grow16 (t : Int → Bool) (h : Int) (hv : growHyp t h) :
  run 16 (⟨.B,h,t⟩ : Conf) = some ⟨.B,h-8,growTape t h⟩ := by
  have hs := growStage16 t h hv
  simpa [gs0, growStage16_normalized t h hv] using hs

#print axioms BB6Root119.grow16
end BB6Root119
