import BusyBeaver.Bridge
import BusyBeaver.Calculi.HaltShared

/-!
Lightweight extraction of **only the actual transition table and state
names** from the pinned Cryptids F424 halting module at commit
3647718b5df22e1a61462dec0376bd204526285a.

The upstream machine file also contains 18 huge 4096-symbolic-step
`by decide +kernel` certificates. Those are not dependencies for
local exact primitive-rule soundness. Copying its 7-line machine
definition verbatim lets CI prove exact primitive-step lemmas against
the **identical encoded Turing machine**, without compiling the
entire unrelated giant source halting certificate.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

@[simp] theorem isVarA_tm : BusyBeaver.SymRunEngine.isVarA target_tm = true := rfl

namespace Solution

def A : Fin 6 := 4
def B : Fin 6 := 3
def C : Fin 6 := 0
def D : Fin 6 := 2
def E : Fin 6 := 5

end Solution
end BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
