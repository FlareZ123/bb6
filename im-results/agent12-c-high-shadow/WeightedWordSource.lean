import WeightedWord
import CRawCountBridge

namespace BB6.Agent12WeightedWord
open BB6.Agent12WordBlock BB6.Agent12Clock
open BB6.Agent47ThinCounted (Path)

/-- The ordinary block certificate composes directly with the existing
literal primitive-machine bridge, for arbitrary head position. -/
theorem block_raw_execution (rs : List Nat) (s : State)
    (hr : ∀ r ∈ rs, 1≤r)
    (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (hx : 0≤(run rs s).a)
    (hg : 20*(2:Int)^shift rs≤gap (run rs s)+4) (h : Int) :
    ∃ t w h', Path t w (enc s) (enc (run rs s)) ∧
      (t:Int)=(clocks rs s).1 ∧
      6*(w:Int)=(tableClock rs (parity s)).eval s.a s.m ∧
      BB6Coverage.run BB6.Agent47CRaw.cMachine w
        (BB6.Agent47CRaw.embed h (BB6.Agent47CRaw.enc (enc s))) =
      some (BB6.Agent47CRaw.embed h' (BB6.Agent47CRaw.enc (enc (run rs s)))) := by
  obtain ⟨t,w,hw,ht,hc⟩ := block_raw_certificate rs s hr hm hp hx hg
  obtain ⟨h',he⟩ := BB6.Agent47CRaw.raw_path hw h
  exact ⟨t,w,h',hw,ht,hc,he⟩

#print axioms block_raw_execution
end BB6.Agent12WeightedWord
