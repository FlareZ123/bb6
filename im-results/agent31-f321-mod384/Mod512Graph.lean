import Mod512Core
import Mod512Chunk0
import Mod512Chunk1
import Mod512Chunk2
import Mod512Chunk3
import Mod512Chunk4
import Mod512Chunk5
import Mod512Chunk6
import Mod512Chunk7
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31F321Mod512
theorem closed_graph :
  ∀ x y : Fin 512, closedAt x.val y.val := by
  intro x y
  by_cases h0 : x.val < 64
  · simpa only [Nat.add_zero] using (chunk0 ⟨x.val, by omega⟩ y)
  · 
    by_cases h1 : x.val < 128
    · have hlt : x.val - 64 < 64 := by omega
      have hc := chunk1 ⟨x.val-64,hlt⟩ y
      have heq : x.val-64+64=x.val := by omega
      simpa only [Fin.val_mk,heq] using hc
    · 
      by_cases h2 : x.val < 192
      · have hlt : x.val - 128 < 64 := by omega
        have hc := chunk2 ⟨x.val-128,hlt⟩ y
        have heq : x.val-128+128=x.val := by omega
        simpa only [Fin.val_mk,heq] using hc
      · 
        by_cases h3 : x.val < 256
        · have hlt : x.val - 192 < 64 := by omega
          have hc := chunk3 ⟨x.val-192,hlt⟩ y
          have heq : x.val-192+192=x.val := by omega
          simpa only [Fin.val_mk,heq] using hc
        · 
          by_cases h4 : x.val < 320
          · have hlt : x.val - 256 < 64 := by omega
            have hc := chunk4 ⟨x.val-256,hlt⟩ y
            have heq : x.val-256+256=x.val := by omega
            simpa only [Fin.val_mk,heq] using hc
          · 
            by_cases h5 : x.val < 384
            · have hlt : x.val - 320 < 64 := by omega
              have hc := chunk5 ⟨x.val-320,hlt⟩ y
              have heq : x.val-320+320=x.val := by omega
              simpa only [Fin.val_mk,heq] using hc
            · 
              by_cases h6 : x.val < 448
              · have hlt : x.val - 384 < 64 := by omega
                have hc := chunk6 ⟨x.val-384,hlt⟩ y
                have heq : x.val-384+384=x.val := by omega
                simpa only [Fin.val_mk,heq] using hc
              · 
                by_cases h7 : x.val < 512
                · have hlt : x.val - 448 < 64 := by omega
                  have hc := chunk7 ⟨x.val-448,hlt⟩ y
                  have heq : x.val-448+448=x.val := by omega
                  simpa only [Fin.val_mk,heq] using hc
                · omega

#print axioms closed_graph
end BB6.Agent31F321Mod512
