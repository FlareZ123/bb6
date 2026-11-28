import M44Check0
import M44Check1
import M44Check2
import M44Check3
import M44Check4
import M44Check5
import M44Check6
import M44Check7
import M44Check8
import M44Check9
import M44Check10
import M44Check11
import M44Check12
import M44Check13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 10000
namespace BB6.Agent38M44
theorem certClosed : closed cert := by
  intro q hq
  have h : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8 ∨ q=9 ∨ q=10 ∨ q=11 ∨ q=12 ∨ q=13 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact closed0
  · exact closed1
  · exact closed2
  · exact closed3
  · exact closed4
  · exact closed5
  · exact closed6
  · exact closed7
  · exact closed8
  · exact closed9
  · exact closed10
  · exact closed11
  · exact closed12
  · exact closed13
#print axioms certClosed
end BB6.Agent38M44
