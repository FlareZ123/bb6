import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent8Raw54.RBRun23
open BB6Coverage
open BB6Coverage.Agent16BiDFA (AState)
open BB6Coverage.Agent16BiDFA.TreeCheck (Tree)
open BB6Coverage.Agent1IndexedBiDFA

/-- Exact Raw54 RB holdout 23; F0 is not assigned. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none

/-- Run-length summary cap 3, parity thereafter; two left unary-one runs,
    three alternating right runs. Reachable push edges only. -/
def dl : Array Nat := #[0,8,0,5,0,0,0,6,0,7,1,9,1,10,1,11,1,12,2,13,2,14,2,15,2,16,3,17,3,18,3,19,3,20,4,13,4,14,4,15,4,16]
def dr : Array Nat := #[0,40,0,0,0,0,0,0,12,32,13,32,14,32,15,32,16,32,17,33,18,33,19,33,0,34,20,34,0,34,21,34,22,34,23,35,24,35,25,35,26,36,27,36,28,36,29,37,30,37,31,37,20,38,21,38,22,38,23,39,24,39,25,39,1,41,1,42,0,43,0,44,2,45,2,46,0,47,0,48,3,49,4,0,4,0,5,50,5,51,6,0,6,0,7,52,7,53,8,54,0,55,0,56,0,57,0,58,0,59,9,50,9,51,10,52,10,53,11,54]
def el : ERows := #[[(false,0)],
  [(false,5),(false,6),(false,7)],
  [(false,12)],
  [(false,13),(false,14),(false,15)],
  [(false,20)],
  [(true,1)],
  [(true,3)],
  [(true,4)],
  [(true,0)],
  [(true,5)],
  [(true,6)],
  [(true,7)],
  [(true,8)],
  [(true,9),(true,17)],
  [(true,10),(true,18)],
  [(true,11),(true,19)],
  [(true,12),(true,20)],
  [(true,13)],
  [(true,14)],
  [(true,15)],
  [(true,16)]]
def er : ERows := #[[(false,0)],
  [(false,32),(false,33)],
  [(false,36),(false,37)],
  [(false,40)],
  [(false,41),(false,42)],
  [(false,43),(false,44)],
  [(false,45),(false,46)],
  [(false,47),(false,48)],
  [(false,49)],
  [(false,55),(false,56)],
  [(false,57),(false,58)],
  [(false,59)],
  [(false,4)],
  [(false,5)],
  [(false,6)],
  [(false,7)],
  [(false,8)],
  [(false,9)],
  [(false,10)],
  [(false,11)],
  [(false,13),(false,26)],
  [(false,15),(false,27)],
  [(false,16),(false,28)],
  [(false,17),(false,29)],
  [(false,18),(false,30)],
  [(false,19),(false,31)],
  [(false,20)],
  [(false,21)],
  [(false,22)],
  [(false,23)],
  [(false,24)],
  [(false,25)],
  [(true,5),(true,7),(true,8)],
  [(true,9),(true,10),(true,11)],
  [(true,13),(true,15),(true,16)],
  [(true,17),(true,18),(true,19)],
  [(true,20),(true,21),(true,22)],
  [(true,23),(true,24),(true,25)],
  [(true,26),(true,27),(true,28)],
  [(true,29),(true,30),(true,31)],
  [(true,0)],
  [(true,32)],
  [(true,33)],
  [(true,34)],
  [(true,35)],
  [(true,36)],
  [(true,37)],
  [(true,38)],
  [(true,39)],
  [(true,40)],
  [(true,43),(true,55)],
  [(true,44),(true,56)],
  [(true,47),(true,57)],
  [(true,48),(true,58)],
  [(true,49),(true,59)],
  [(true,50)],
  [(true,51)],
  [(true,52)],
  [(true,53)],
  [(true,54)]]

def t6 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,5,0⟩ .empty) ⟨0,false,5,5⟩ (.node .empty ⟨0,false,5,7⟩ .empty)) ⟨0,false,5,8⟩ (.node (.node (.node .empty ⟨0,false,5,9⟩ .empty) ⟨0,false,5,10⟩ .empty) ⟨0,false,5,11⟩ (.node .empty ⟨0,false,5,20⟩ .empty))) ⟨0,false,5,21⟩ (.node (.node (.node (.node .empty ⟨0,false,5,22⟩ .empty) ⟨0,false,5,23⟩ .empty) ⟨0,false,5,24⟩ (.node .empty ⟨0,false,5,25⟩ .empty)) ⟨0,false,6,0⟩ (.node (.node (.node .empty ⟨0,false,6,5⟩ .empty) ⟨0,false,6,7⟩ .empty) ⟨0,false,6,8⟩ (.node .empty ⟨0,false,6,9⟩ .empty))))
def t7 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,6,11⟩ .empty) ⟨0,false,6,20⟩ .empty) ⟨0,false,6,21⟩ (.node .empty ⟨0,false,6,22⟩ .empty)) ⟨0,false,6,23⟩ (.node (.node (.node .empty ⟨0,false,6,24⟩ .empty) ⟨0,false,6,25⟩ .empty) ⟨0,false,7,0⟩ (.node .empty ⟨0,false,7,5⟩ .empty))) ⟨0,false,7,7⟩ (.node (.node (.node (.node .empty ⟨0,false,7,8⟩ .empty) ⟨0,false,7,9⟩ .empty) ⟨0,false,7,10⟩ (.node .empty ⟨0,false,7,11⟩ .empty)) ⟨0,false,7,20⟩ (.node (.node (.node .empty ⟨0,false,7,21⟩ .empty) ⟨0,false,7,22⟩ .empty) ⟨0,false,7,23⟩ (.node .empty ⟨0,false,7,24⟩ .empty))))
def t5 : Tree := .node t6 ⟨0,false,6,10⟩ t7
def t9 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,5,34⟩ .empty) ⟨0,true,5,35⟩ .empty) ⟨0,true,5,38⟩ (.node .empty ⟨0,true,5,39⟩ .empty)) ⟨0,true,5,40⟩ (.node (.node (.node .empty ⟨0,true,5,50⟩ .empty) ⟨0,true,5,51⟩ .empty) ⟨0,true,5,52⟩ (.node .empty ⟨0,true,5,53⟩ .empty))) ⟨0,true,5,54⟩ (.node (.node (.node (.node .empty ⟨0,true,6,34⟩ .empty) ⟨0,true,6,35⟩ .empty) ⟨0,true,6,38⟩ (.node .empty ⟨0,true,6,39⟩ .empty)) ⟨0,true,6,40⟩ (.node (.node (.node .empty ⟨0,true,6,50⟩ .empty) ⟨0,true,6,51⟩ .empty) ⟨0,true,6,52⟩ (.node .empty ⟨0,true,6,53⟩ .empty))))
def t10 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,7,34⟩ .empty) ⟨0,true,7,35⟩ .empty) ⟨0,true,7,38⟩ (.node .empty ⟨0,true,7,39⟩ .empty)) ⟨0,true,7,40⟩ (.node (.node (.node .empty ⟨0,true,7,50⟩ .empty) ⟨0,true,7,51⟩ .empty) ⟨0,true,7,52⟩ (.node .empty ⟨0,true,7,53⟩ .empty))) ⟨0,true,7,54⟩ (.node (.node (.node (.node .empty ⟨1,false,3,0⟩ .empty) ⟨1,false,3,13⟩ .empty) ⟨1,false,3,15⟩ (.node .empty ⟨1,false,3,16⟩ .empty)) ⟨1,false,3,17⟩ (.node (.node (.node .empty ⟨1,false,3,18⟩ .empty) ⟨1,false,3,19⟩ .empty) ⟨1,false,3,26⟩ (.node .empty ⟨1,false,3,27⟩ .empty))))
def t8 : Tree := .node t9 ⟨0,true,6,54⟩ t10
def t4 : Tree := .node t5 ⟨0,false,7,25⟩ t8
def t13 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,3,29⟩ .empty) ⟨1,false,3,30⟩ .empty) ⟨1,false,3,31⟩ (.node .empty ⟨1,false,3,43⟩ .empty)) ⟨1,false,3,44⟩ (.node (.node (.node .empty ⟨1,false,3,47⟩ .empty) ⟨1,false,3,48⟩ .empty) ⟨1,false,3,49⟩ (.node .empty ⟨1,false,3,55⟩ .empty))) ⟨1,false,3,56⟩ (.node (.node (.node (.node .empty ⟨1,false,3,57⟩ .empty) ⟨1,false,3,58⟩ .empty) ⟨1,false,3,59⟩ (.node .empty ⟨1,false,4,0⟩ .empty)) ⟨1,false,4,13⟩ (.node (.node (.node .empty ⟨1,false,4,15⟩ .empty) ⟨1,false,4,16⟩ .empty) ⟨1,false,4,17⟩ (.node .empty ⟨1,false,4,18⟩ .empty))))
def t14 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,4,26⟩ .empty) ⟨1,false,4,27⟩ .empty) ⟨1,false,4,28⟩ (.node .empty ⟨1,false,4,29⟩ .empty)) ⟨1,false,4,30⟩ (.node (.node (.node .empty ⟨1,false,4,31⟩ .empty) ⟨1,false,4,43⟩ .empty) ⟨1,false,4,44⟩ (.node .empty ⟨1,false,4,47⟩ .empty))) ⟨1,false,4,48⟩ (.node (.node (.node (.node .empty ⟨1,false,4,49⟩ .empty) ⟨1,false,4,55⟩ .empty) ⟨1,false,4,56⟩ (.node .empty ⟨1,false,4,57⟩ .empty)) ⟨1,false,4,58⟩ (.node (.node (.node .empty ⟨1,false,4,59⟩ .empty) ⟨1,false,8,0⟩ .empty) ⟨1,false,8,4⟩ (.node .empty ⟨1,false,8,6⟩ .empty))))
def t12 : Tree := .node t13 ⟨1,false,4,19⟩ t14
def t16 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,8,20⟩ .empty) ⟨1,false,8,21⟩ .empty) ⟨1,false,8,23⟩ (.node .empty ⟨1,false,8,24⟩ .empty)) ⟨1,false,8,25⟩ (.node (.node (.node .empty ⟨1,false,9,0⟩ .empty) ⟨1,false,9,13⟩ .empty) ⟨1,false,9,15⟩ (.node .empty ⟨1,false,9,16⟩ .empty))) ⟨1,false,9,17⟩ (.node (.node (.node (.node .empty ⟨1,false,9,18⟩ .empty) ⟨1,false,9,19⟩ .empty) ⟨1,false,9,26⟩ (.node .empty ⟨1,false,9,27⟩ .empty)) ⟨1,false,9,28⟩ (.node (.node (.node .empty ⟨1,false,9,29⟩ .empty) ⟨1,false,9,30⟩ .empty) ⟨1,false,9,31⟩ (.node .empty ⟨1,false,9,32⟩ .empty))))
def t17 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,9,36⟩ .empty) ⟨1,false,9,37⟩ .empty) ⟨1,false,9,40⟩ (.node .empty ⟨1,false,9,43⟩ .empty)) ⟨1,false,9,44⟩ (.node (.node (.node .empty ⟨1,false,9,47⟩ .empty) ⟨1,false,9,48⟩ .empty) ⟨1,false,9,49⟩ (.node .empty ⟨1,false,9,55⟩ .empty))) ⟨1,false,9,56⟩ (.node (.node (.node (.node .empty ⟨1,false,9,57⟩ .empty) ⟨1,false,9,58⟩ .empty) ⟨1,false,9,59⟩ (.node .empty ⟨1,false,10,0⟩ .empty)) ⟨1,false,10,13⟩ (.node (.node (.node .empty ⟨1,false,10,15⟩ .empty) ⟨1,false,10,16⟩ .empty) ⟨1,false,10,17⟩ (.node .empty ⟨1,false,10,18⟩ .empty))))
def t15 : Tree := .node t16 ⟨1,false,9,33⟩ t17
def t11 : Tree := .node t12 ⟨1,false,8,8⟩ t15
def t3 : Tree := .node t4 ⟨1,false,3,28⟩ t11
def t21 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,10,26⟩ .empty) ⟨1,false,10,27⟩ .empty) ⟨1,false,10,28⟩ (.node .empty ⟨1,false,10,29⟩ .empty)) ⟨1,false,10,30⟩ (.node (.node (.node .empty ⟨1,false,10,31⟩ .empty) ⟨1,false,10,32⟩ .empty) ⟨1,false,10,33⟩ (.node .empty ⟨1,false,10,36⟩ .empty))) ⟨1,false,10,37⟩ (.node (.node (.node (.node .empty ⟨1,false,10,40⟩ .empty) ⟨1,false,10,43⟩ .empty) ⟨1,false,10,44⟩ (.node .empty ⟨1,false,10,47⟩ .empty)) ⟨1,false,10,48⟩ (.node (.node (.node .empty ⟨1,false,10,49⟩ .empty) ⟨1,false,10,55⟩ .empty) ⟨1,false,10,56⟩ (.node .empty ⟨1,false,10,57⟩ .empty))))
def t22 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,10,59⟩ .empty) ⟨1,false,11,0⟩ .empty) ⟨1,false,11,13⟩ (.node .empty ⟨1,false,11,15⟩ .empty)) ⟨1,false,11,16⟩ (.node (.node (.node .empty ⟨1,false,11,17⟩ .empty) ⟨1,false,11,18⟩ .empty) ⟨1,false,11,19⟩ (.node .empty ⟨1,false,11,26⟩ .empty))) ⟨1,false,11,27⟩ (.node (.node (.node (.node .empty ⟨1,false,11,28⟩ .empty) ⟨1,false,11,29⟩ .empty) ⟨1,false,11,30⟩ (.node .empty ⟨1,false,11,31⟩ .empty)) ⟨1,false,11,32⟩ (.node (.node (.node .empty ⟨1,false,11,33⟩ .empty) ⟨1,false,11,36⟩ .empty) ⟨1,false,11,37⟩ (.node .empty ⟨1,false,11,40⟩ .empty))))
def t20 : Tree := .node t21 ⟨1,false,10,58⟩ t22
def t24 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,11,44⟩ .empty) ⟨1,false,11,47⟩ .empty) ⟨1,false,11,48⟩ (.node .empty ⟨1,false,11,49⟩ .empty)) ⟨1,false,11,55⟩ (.node (.node (.node .empty ⟨1,false,11,56⟩ .empty) ⟨1,false,11,57⟩ .empty) ⟨1,false,11,58⟩ (.node .empty ⟨1,false,11,59⟩ .empty))) ⟨1,false,16,13⟩ (.node (.node (.node (.node .empty ⟨1,false,16,15⟩ .empty) ⟨1,false,16,16⟩ .empty) ⟨1,false,16,17⟩ (.node .empty ⟨1,false,16,18⟩ .empty)) ⟨1,false,16,19⟩ (.node (.node (.node .empty ⟨1,false,16,26⟩ .empty) ⟨1,false,16,27⟩ .empty) ⟨1,false,16,28⟩ (.node .empty ⟨1,false,16,29⟩ .empty))))
def t25 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,16,31⟩ .empty) ⟨1,false,16,32⟩ .empty) ⟨1,false,16,33⟩ (.node .empty ⟨1,false,16,36⟩ .empty)) ⟨1,false,16,37⟩ (.node (.node (.node .empty ⟨1,false,16,40⟩ .empty) ⟨1,false,16,43⟩ .empty) ⟨1,false,16,44⟩ (.node .empty ⟨1,false,16,47⟩ .empty))) ⟨1,false,16,48⟩ (.node (.node (.node (.node .empty ⟨1,false,16,49⟩ .empty) ⟨1,false,16,55⟩ .empty) ⟨1,false,16,56⟩ (.node .empty ⟨1,false,16,57⟩ .empty)) ⟨1,false,16,58⟩ (.node (.node (.node .empty ⟨1,false,16,59⟩ .empty) ⟨1,false,17,13⟩ .empty) ⟨1,false,17,15⟩ (.node .empty ⟨1,false,17,16⟩ .empty))))
def t23 : Tree := .node t24 ⟨1,false,16,30⟩ t25
def t19 : Tree := .node t20 ⟨1,false,11,43⟩ t23
def t28 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,17,18⟩ .empty) ⟨1,false,17,19⟩ .empty) ⟨1,false,17,26⟩ (.node .empty ⟨1,false,17,27⟩ .empty)) ⟨1,false,17,28⟩ (.node (.node (.node .empty ⟨1,false,17,29⟩ .empty) ⟨1,false,17,30⟩ .empty) ⟨1,false,17,31⟩ (.node .empty ⟨1,false,17,32⟩ .empty))) ⟨1,false,17,33⟩ (.node (.node (.node (.node .empty ⟨1,false,17,36⟩ .empty) ⟨1,false,17,37⟩ .empty) ⟨1,false,17,40⟩ (.node .empty ⟨1,false,17,43⟩ .empty)) ⟨1,false,17,44⟩ (.node (.node (.node .empty ⟨1,false,17,47⟩ .empty) ⟨1,false,17,48⟩ .empty) ⟨1,false,17,49⟩ (.node .empty ⟨1,false,17,55⟩ .empty))))
def t29 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,17,57⟩ .empty) ⟨1,false,17,58⟩ .empty) ⟨1,false,17,59⟩ (.node .empty ⟨1,false,18,13⟩ .empty)) ⟨1,false,18,15⟩ (.node (.node (.node .empty ⟨1,false,18,16⟩ .empty) ⟨1,false,18,17⟩ .empty) ⟨1,false,18,18⟩ (.node .empty ⟨1,false,18,19⟩ .empty))) ⟨1,false,18,26⟩ (.node (.node (.node (.node .empty ⟨1,false,18,27⟩ .empty) ⟨1,false,18,28⟩ .empty) ⟨1,false,18,29⟩ (.node .empty ⟨1,false,18,30⟩ .empty)) ⟨1,false,18,31⟩ (.node (.node (.node .empty ⟨1,false,18,32⟩ .empty) ⟨1,false,18,33⟩ .empty) ⟨1,false,18,36⟩ (.node .empty ⟨1,false,18,37⟩ .empty))))
def t27 : Tree := .node t28 ⟨1,false,17,56⟩ t29
def t31 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,18,43⟩ .empty) ⟨1,false,18,44⟩ .empty) ⟨1,false,18,47⟩ (.node .empty ⟨1,false,18,48⟩ .empty)) ⟨1,false,18,49⟩ (.node (.node (.node .empty ⟨1,false,18,55⟩ .empty) ⟨1,false,18,56⟩ .empty) ⟨1,false,18,57⟩ (.node .empty ⟨1,false,18,58⟩ .empty))) ⟨1,false,18,59⟩ (.node (.node (.node (.node .empty ⟨1,false,19,13⟩ .empty) ⟨1,false,19,15⟩ .empty) ⟨1,false,19,16⟩ (.node .empty ⟨1,false,19,17⟩ .empty)) ⟨1,false,19,18⟩ (.node (.node (.node .empty ⟨1,false,19,19⟩ .empty) ⟨1,false,19,26⟩ .empty) ⟨1,false,19,27⟩ (.node .empty ⟨1,false,19,28⟩ .empty))))
def t32 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,19,30⟩ .empty) ⟨1,false,19,31⟩ .empty) ⟨1,false,19,32⟩ (.node .empty ⟨1,false,19,33⟩ .empty)) ⟨1,false,19,36⟩ (.node (.node (.node .empty ⟨1,false,19,37⟩ .empty) ⟨1,false,19,40⟩ .empty) ⟨1,false,19,43⟩ (.node .empty ⟨1,false,19,44⟩ .empty))) ⟨1,false,19,47⟩ (.node (.node (.node (.node .empty ⟨1,false,19,48⟩ .empty) ⟨1,false,19,49⟩ .empty) ⟨1,false,19,55⟩ (.node .empty ⟨1,false,19,56⟩ .empty)) ⟨1,false,19,57⟩ (.node (.node .empty ⟨1,false,19,58⟩ .empty) ⟨1,false,19,59⟩ (.node .empty ⟨1,true,1,0⟩ .empty))))
def t30 : Tree := .node t31 ⟨1,false,19,29⟩ t32
def t26 : Tree := .node t27 ⟨1,false,18,40⟩ t30
def t18 : Tree := .node t19 ⟨1,false,17,17⟩ t26
def t2 : Tree := .node t3 ⟨1,false,10,19⟩ t18
def t37 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,1,15⟩ .empty) ⟨1,true,1,16⟩ .empty) ⟨1,true,1,17⟩ (.node .empty ⟨1,true,1,18⟩ .empty)) ⟨1,true,1,19⟩ (.node (.node (.node .empty ⟨1,true,1,26⟩ .empty) ⟨1,true,1,27⟩ .empty) ⟨1,true,1,28⟩ (.node .empty ⟨1,true,1,29⟩ .empty))) ⟨1,true,1,30⟩ (.node (.node (.node (.node .empty ⟨1,true,1,31⟩ .empty) ⟨1,true,1,43⟩ .empty) ⟨1,true,1,44⟩ (.node .empty ⟨1,true,1,47⟩ .empty)) ⟨1,true,1,48⟩ (.node (.node (.node .empty ⟨1,true,1,49⟩ .empty) ⟨1,true,1,55⟩ .empty) ⟨1,true,1,56⟩ (.node .empty ⟨1,true,1,57⟩ .empty))))
def t38 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,1,59⟩ .empty) ⟨1,true,3,0⟩ .empty) ⟨1,true,3,13⟩ (.node .empty ⟨1,true,3,15⟩ .empty)) ⟨1,true,3,16⟩ (.node (.node (.node .empty ⟨1,true,3,17⟩ .empty) ⟨1,true,3,18⟩ .empty) ⟨1,true,3,19⟩ (.node .empty ⟨1,true,3,26⟩ .empty))) ⟨1,true,3,27⟩ (.node (.node (.node (.node .empty ⟨1,true,3,28⟩ .empty) ⟨1,true,3,29⟩ .empty) ⟨1,true,3,30⟩ (.node .empty ⟨1,true,3,31⟩ .empty)) ⟨1,true,3,43⟩ (.node (.node (.node .empty ⟨1,true,3,44⟩ .empty) ⟨1,true,3,47⟩ .empty) ⟨1,true,3,48⟩ (.node .empty ⟨1,true,3,49⟩ .empty))))
def t36 : Tree := .node t37 ⟨1,true,1,58⟩ t38
def t40 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,3,56⟩ .empty) ⟨1,true,3,57⟩ .empty) ⟨1,true,3,58⟩ (.node .empty ⟨1,true,3,59⟩ .empty)) ⟨1,true,4,0⟩ (.node (.node (.node .empty ⟨1,true,4,13⟩ .empty) ⟨1,true,4,15⟩ .empty) ⟨1,true,4,16⟩ (.node .empty ⟨1,true,4,17⟩ .empty))) ⟨1,true,4,18⟩ (.node (.node (.node (.node .empty ⟨1,true,4,19⟩ .empty) ⟨1,true,4,26⟩ .empty) ⟨1,true,4,27⟩ (.node .empty ⟨1,true,4,28⟩ .empty)) ⟨1,true,4,29⟩ (.node (.node (.node .empty ⟨1,true,4,30⟩ .empty) ⟨1,true,4,31⟩ .empty) ⟨1,true,4,43⟩ (.node .empty ⟨1,true,4,44⟩ .empty))))
def t41 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,4,48⟩ .empty) ⟨1,true,4,49⟩ .empty) ⟨1,true,4,55⟩ (.node .empty ⟨1,true,4,56⟩ .empty)) ⟨1,true,4,57⟩ (.node (.node (.node .empty ⟨1,true,4,58⟩ .empty) ⟨1,true,4,59⟩ .empty) ⟨2,false,6,0⟩ (.node .empty ⟨2,false,6,5⟩ .empty))) ⟨2,false,6,7⟩ (.node (.node (.node (.node .empty ⟨2,false,6,8⟩ .empty) ⟨2,false,6,9⟩ .empty) ⟨2,false,6,10⟩ (.node .empty ⟨2,false,6,11⟩ .empty)) ⟨2,false,6,20⟩ (.node (.node (.node .empty ⟨2,false,6,21⟩ .empty) ⟨2,false,6,22⟩ .empty) ⟨2,false,6,23⟩ (.node .empty ⟨2,false,6,24⟩ .empty))))
def t39 : Tree := .node t40 ⟨1,true,4,47⟩ t41
def t35 : Tree := .node t36 ⟨1,true,3,55⟩ t39
def t44 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,7,0⟩ .empty) ⟨2,false,7,5⟩ .empty) ⟨2,false,7,7⟩ (.node .empty ⟨2,false,7,8⟩ .empty)) ⟨2,false,7,9⟩ (.node (.node (.node .empty ⟨2,false,7,10⟩ .empty) ⟨2,false,7,11⟩ .empty) ⟨2,false,7,20⟩ (.node .empty ⟨2,false,7,21⟩ .empty))) ⟨2,false,7,22⟩ (.node (.node (.node (.node .empty ⟨2,false,7,23⟩ .empty) ⟨2,false,7,24⟩ .empty) ⟨2,false,7,25⟩ (.node .empty ⟨2,false,12,0⟩ .empty)) ⟨2,false,12,13⟩ (.node (.node (.node .empty ⟨2,false,12,15⟩ .empty) ⟨2,false,12,17⟩ .empty) ⟨2,false,12,18⟩ (.node .empty ⟨2,false,12,19⟩ .empty))))
def t45 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,12,27⟩ .empty) ⟨2,false,12,29⟩ .empty) ⟨2,false,12,30⟩ (.node .empty ⟨2,false,12,31⟩ .empty)) ⟨2,false,12,41⟩ (.node (.node (.node .empty ⟨2,false,12,42⟩ .empty) ⟨2,false,12,45⟩ .empty) ⟨2,false,12,46⟩ (.node .empty ⟨2,false,12,49⟩ .empty))) ⟨2,false,13,0⟩ (.node (.node (.node (.node .empty ⟨2,false,13,5⟩ .empty) ⟨2,false,13,7⟩ .empty) ⟨2,false,13,8⟩ (.node .empty ⟨2,false,13,9⟩ .empty)) ⟨2,false,13,10⟩ (.node (.node (.node .empty ⟨2,false,13,11⟩ .empty) ⟨2,false,13,20⟩ .empty) ⟨2,false,13,21⟩ (.node .empty ⟨2,false,13,22⟩ .empty))))
def t43 : Tree := .node t44 ⟨2,false,12,26⟩ t45
def t47 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,13,24⟩ .empty) ⟨2,false,13,25⟩ .empty) ⟨2,false,14,0⟩ (.node .empty ⟨2,false,14,5⟩ .empty)) ⟨2,false,14,7⟩ (.node (.node (.node .empty ⟨2,false,14,8⟩ .empty) ⟨2,false,14,9⟩ .empty) ⟨2,false,14,10⟩ (.node .empty ⟨2,false,14,11⟩ .empty))) ⟨2,false,14,20⟩ (.node (.node (.node (.node .empty ⟨2,false,14,21⟩ .empty) ⟨2,false,14,22⟩ .empty) ⟨2,false,14,23⟩ (.node .empty ⟨2,false,14,24⟩ .empty)) ⟨2,false,14,25⟩ (.node (.node (.node .empty ⟨2,false,15,0⟩ .empty) ⟨2,false,15,5⟩ .empty) ⟨2,false,15,7⟩ (.node .empty ⟨2,false,15,8⟩ .empty))))
def t48 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,15,10⟩ .empty) ⟨2,false,15,11⟩ .empty) ⟨2,false,15,20⟩ (.node .empty ⟨2,false,15,21⟩ .empty)) ⟨2,false,15,22⟩ (.node (.node (.node .empty ⟨2,false,15,23⟩ .empty) ⟨2,false,15,24⟩ .empty) ⟨2,false,15,25⟩ (.node .empty ⟨2,false,20,5⟩ .empty))) ⟨2,false,20,7⟩ (.node (.node (.node (.node .empty ⟨2,false,20,8⟩ .empty) ⟨2,false,20,9⟩ .empty) ⟨2,false,20,10⟩ (.node .empty ⟨2,false,20,11⟩ .empty)) ⟨2,false,20,20⟩ (.node (.node (.node .empty ⟨2,false,20,21⟩ .empty) ⟨2,false,20,22⟩ .empty) ⟨2,false,20,23⟩ (.node .empty ⟨2,false,20,24⟩ .empty))))
def t46 : Tree := .node t47 ⟨2,false,15,9⟩ t48
def t42 : Tree := .node t43 ⟨2,false,13,23⟩ t46
def t34 : Tree := .node t35 ⟨2,false,6,25⟩ t42
def t52 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,6,34⟩ .empty) ⟨2,true,6,35⟩ .empty) ⟨2,true,6,38⟩ (.node .empty ⟨2,true,6,39⟩ .empty)) ⟨2,true,6,40⟩ (.node (.node (.node .empty ⟨2,true,6,50⟩ .empty) ⟨2,true,6,51⟩ .empty) ⟨2,true,6,52⟩ (.node .empty ⟨2,true,6,53⟩ .empty))) ⟨2,true,6,54⟩ (.node (.node (.node (.node .empty ⟨2,true,7,34⟩ .empty) ⟨2,true,7,35⟩ .empty) ⟨2,true,7,38⟩ (.node .empty ⟨2,true,7,39⟩ .empty)) ⟨2,true,7,40⟩ (.node (.node (.node .empty ⟨2,true,7,50⟩ .empty) ⟨2,true,7,51⟩ .empty) ⟨2,true,7,52⟩ (.node .empty ⟨2,true,7,53⟩ .empty))))
def t53 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,13,0⟩ .empty) ⟨2,true,13,5⟩ .empty) ⟨2,true,13,7⟩ (.node .empty ⟨2,true,13,8⟩ .empty)) ⟨2,true,13,9⟩ (.node (.node (.node .empty ⟨2,true,13,10⟩ .empty) ⟨2,true,13,11⟩ .empty) ⟨2,true,13,20⟩ (.node .empty ⟨2,true,13,21⟩ .empty))) ⟨2,true,13,22⟩ (.node (.node (.node (.node .empty ⟨2,true,13,23⟩ .empty) ⟨2,true,13,24⟩ .empty) ⟨2,true,13,25⟩ (.node .empty ⟨2,true,13,34⟩ .empty)) ⟨2,true,13,35⟩ (.node (.node (.node .empty ⟨2,true,13,38⟩ .empty) ⟨2,true,13,39⟩ .empty) ⟨2,true,13,40⟩ (.node .empty ⟨2,true,13,50⟩ .empty))))
def t51 : Tree := .node t52 ⟨2,true,7,54⟩ t53
def t55 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,13,52⟩ .empty) ⟨2,true,13,53⟩ .empty) ⟨2,true,13,54⟩ (.node .empty ⟨2,true,14,0⟩ .empty)) ⟨2,true,14,5⟩ (.node (.node (.node .empty ⟨2,true,14,7⟩ .empty) ⟨2,true,14,8⟩ .empty) ⟨2,true,14,9⟩ (.node .empty ⟨2,true,14,10⟩ .empty))) ⟨2,true,14,11⟩ (.node (.node (.node (.node .empty ⟨2,true,14,20⟩ .empty) ⟨2,true,14,21⟩ .empty) ⟨2,true,14,22⟩ (.node .empty ⟨2,true,14,23⟩ .empty)) ⟨2,true,14,24⟩ (.node (.node (.node .empty ⟨2,true,14,25⟩ .empty) ⟨2,true,14,34⟩ .empty) ⟨2,true,14,35⟩ (.node .empty ⟨2,true,14,38⟩ .empty))))
def t56 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,14,40⟩ .empty) ⟨2,true,14,50⟩ .empty) ⟨2,true,14,51⟩ (.node .empty ⟨2,true,14,52⟩ .empty)) ⟨2,true,14,53⟩ (.node (.node (.node .empty ⟨2,true,14,54⟩ .empty) ⟨2,true,15,0⟩ .empty) ⟨2,true,15,5⟩ (.node .empty ⟨2,true,15,7⟩ .empty))) ⟨2,true,15,8⟩ (.node (.node (.node (.node .empty ⟨2,true,15,9⟩ .empty) ⟨2,true,15,10⟩ .empty) ⟨2,true,15,11⟩ (.node .empty ⟨2,true,15,20⟩ .empty)) ⟨2,true,15,21⟩ (.node (.node (.node .empty ⟨2,true,15,22⟩ .empty) ⟨2,true,15,23⟩ .empty) ⟨2,true,15,24⟩ (.node .empty ⟨2,true,15,25⟩ .empty))))
def t54 : Tree := .node t55 ⟨2,true,14,39⟩ t56
def t50 : Tree := .node t51 ⟨2,true,13,51⟩ t54
def t59 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,15,35⟩ .empty) ⟨2,true,15,38⟩ .empty) ⟨2,true,15,39⟩ (.node .empty ⟨2,true,15,40⟩ .empty)) ⟨2,true,15,50⟩ (.node (.node (.node .empty ⟨2,true,15,51⟩ .empty) ⟨2,true,15,52⟩ .empty) ⟨2,true,15,53⟩ (.node .empty ⟨2,true,15,54⟩ .empty))) ⟨2,true,20,0⟩ (.node (.node (.node (.node .empty ⟨2,true,20,5⟩ .empty) ⟨2,true,20,7⟩ .empty) ⟨2,true,20,8⟩ (.node .empty ⟨2,true,20,9⟩ .empty)) ⟨2,true,20,10⟩ (.node (.node (.node .empty ⟨2,true,20,11⟩ .empty) ⟨2,true,20,20⟩ .empty) ⟨2,true,20,21⟩ (.node .empty ⟨2,true,20,22⟩ .empty))))
def t60 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,20,24⟩ .empty) ⟨2,true,20,25⟩ .empty) ⟨2,true,20,34⟩ (.node .empty ⟨2,true,20,35⟩ .empty)) ⟨2,true,20,38⟩ (.node (.node (.node .empty ⟨2,true,20,39⟩ .empty) ⟨2,true,20,40⟩ .empty) ⟨2,true,20,50⟩ (.node .empty ⟨2,true,20,51⟩ .empty))) ⟨2,true,20,52⟩ (.node (.node (.node (.node .empty ⟨2,true,20,53⟩ .empty) ⟨2,true,20,54⟩ .empty) ⟨3,false,1,0⟩ (.node .empty ⟨3,false,1,13⟩ .empty)) ⟨3,false,1,15⟩ (.node (.node (.node .empty ⟨3,false,1,16⟩ .empty) ⟨3,false,1,17⟩ .empty) ⟨3,false,1,18⟩ (.node .empty ⟨3,false,1,19⟩ .empty))))
def t58 : Tree := .node t59 ⟨2,true,20,23⟩ t60
def t62 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,1,27⟩ .empty) ⟨3,false,1,28⟩ .empty) ⟨3,false,1,29⟩ (.node .empty ⟨3,false,1,30⟩ .empty)) ⟨3,false,1,31⟩ (.node (.node (.node .empty ⟨3,false,1,43⟩ .empty) ⟨3,false,1,44⟩ .empty) ⟨3,false,1,47⟩ (.node .empty ⟨3,false,1,48⟩ .empty))) ⟨3,false,1,49⟩ (.node (.node (.node (.node .empty ⟨3,false,1,55⟩ .empty) ⟨3,false,1,56⟩ .empty) ⟨3,false,1,57⟩ (.node .empty ⟨3,false,1,58⟩ .empty)) ⟨3,false,1,59⟩ (.node (.node (.node .empty ⟨3,false,2,0⟩ .empty) ⟨3,false,2,5⟩ .empty) ⟨3,false,2,7⟩ (.node .empty ⟨3,false,2,9⟩ .empty))))
def t63 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,2,11⟩ .empty) ⟨3,false,2,20⟩ .empty) ⟨3,false,2,21⟩ (.node .empty ⟨3,false,2,23⟩ .empty)) ⟨3,false,2,24⟩ (.node (.node (.node .empty ⟨3,false,2,25⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,3,13⟩ (.node .empty ⟨3,false,3,15⟩ .empty))) ⟨3,false,3,16⟩ (.node (.node (.node (.node .empty ⟨3,false,3,17⟩ .empty) ⟨3,false,3,18⟩ .empty) ⟨3,false,3,19⟩ (.node .empty ⟨3,false,3,26⟩ .empty)) ⟨3,false,3,27⟩ (.node (.node .empty ⟨3,false,3,28⟩ .empty) ⟨3,false,3,29⟩ (.node .empty ⟨3,false,3,30⟩ .empty))))
def t61 : Tree := .node t62 ⟨3,false,2,10⟩ t63
def t57 : Tree := .node t58 ⟨3,false,1,26⟩ t61
def t49 : Tree := .node t50 ⟨2,true,15,34⟩ t57
def t33 : Tree := .node t34 ⟨2,false,20,25⟩ t49
def t1 : Tree := .node t2 ⟨1,true,1,13⟩ t33
def t69 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,3,43⟩ .empty) ⟨3,false,3,44⟩ .empty) ⟨3,false,3,47⟩ (.node .empty ⟨3,false,3,48⟩ .empty)) ⟨3,false,3,49⟩ (.node (.node (.node .empty ⟨3,false,3,55⟩ .empty) ⟨3,false,3,56⟩ .empty) ⟨3,false,3,57⟩ (.node .empty ⟨3,false,3,58⟩ .empty))) ⟨3,false,3,59⟩ (.node (.node (.node (.node .empty ⟨3,false,4,13⟩ .empty) ⟨3,false,4,15⟩ .empty) ⟨3,false,4,16⟩ (.node .empty ⟨3,false,4,17⟩ .empty)) ⟨3,false,4,18⟩ (.node (.node (.node .empty ⟨3,false,4,19⟩ .empty) ⟨3,false,4,26⟩ .empty) ⟨3,false,4,27⟩ (.node .empty ⟨3,false,4,28⟩ .empty))))
def t70 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,4,30⟩ .empty) ⟨3,false,4,31⟩ .empty) ⟨3,false,4,43⟩ (.node .empty ⟨3,false,4,44⟩ .empty)) ⟨3,false,4,47⟩ (.node (.node (.node .empty ⟨3,false,4,48⟩ .empty) ⟨3,false,4,49⟩ .empty) ⟨3,false,4,55⟩ (.node .empty ⟨3,false,4,56⟩ .empty))) ⟨3,false,4,57⟩ (.node (.node (.node (.node .empty ⟨3,false,4,58⟩ .empty) ⟨3,false,4,59⟩ .empty) ⟨3,false,5,0⟩ (.node .empty ⟨3,false,5,5⟩ .empty)) ⟨3,false,5,7⟩ (.node (.node (.node .empty ⟨3,false,5,8⟩ .empty) ⟨3,false,5,9⟩ .empty) ⟨3,false,5,10⟩ (.node .empty ⟨3,false,5,11⟩ .empty))))
def t68 : Tree := .node t69 ⟨3,false,4,29⟩ t70
def t72 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,5,21⟩ .empty) ⟨3,false,5,22⟩ .empty) ⟨3,false,5,23⟩ (.node .empty ⟨3,false,5,24⟩ .empty)) ⟨3,false,5,25⟩ (.node (.node (.node .empty ⟨3,false,5,34⟩ .empty) ⟨3,false,5,35⟩ .empty) ⟨3,false,5,38⟩ (.node .empty ⟨3,false,5,39⟩ .empty))) ⟨3,false,5,40⟩ (.node (.node (.node (.node .empty ⟨3,false,5,50⟩ .empty) ⟨3,false,5,51⟩ .empty) ⟨3,false,5,52⟩ (.node .empty ⟨3,false,5,53⟩ .empty)) ⟨3,false,5,54⟩ (.node (.node (.node .empty ⟨3,false,6,0⟩ .empty) ⟨3,false,6,5⟩ .empty) ⟨3,false,6,7⟩ (.node .empty ⟨3,false,6,8⟩ .empty))))
def t73 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,6,10⟩ .empty) ⟨3,false,6,11⟩ .empty) ⟨3,false,6,20⟩ (.node .empty ⟨3,false,6,21⟩ .empty)) ⟨3,false,6,22⟩ (.node (.node (.node .empty ⟨3,false,6,23⟩ .empty) ⟨3,false,6,24⟩ .empty) ⟨3,false,6,25⟩ (.node .empty ⟨3,false,6,34⟩ .empty))) ⟨3,false,6,35⟩ (.node (.node (.node (.node .empty ⟨3,false,6,38⟩ .empty) ⟨3,false,6,39⟩ .empty) ⟨3,false,6,40⟩ (.node .empty ⟨3,false,6,50⟩ .empty)) ⟨3,false,6,51⟩ (.node (.node (.node .empty ⟨3,false,6,52⟩ .empty) ⟨3,false,6,53⟩ .empty) ⟨3,false,6,54⟩ (.node .empty ⟨3,false,7,0⟩ .empty))))
def t71 : Tree := .node t72 ⟨3,false,6,9⟩ t73
def t67 : Tree := .node t68 ⟨3,false,5,20⟩ t71
def t76 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,7,7⟩ .empty) ⟨3,false,7,8⟩ .empty) ⟨3,false,7,9⟩ (.node .empty ⟨3,false,7,10⟩ .empty)) ⟨3,false,7,11⟩ (.node (.node (.node .empty ⟨3,false,7,20⟩ .empty) ⟨3,false,7,21⟩ .empty) ⟨3,false,7,22⟩ (.node .empty ⟨3,false,7,23⟩ .empty))) ⟨3,false,7,24⟩ (.node (.node (.node (.node .empty ⟨3,false,7,25⟩ .empty) ⟨3,false,7,34⟩ .empty) ⟨3,false,7,35⟩ (.node .empty ⟨3,false,7,38⟩ .empty)) ⟨3,false,7,39⟩ (.node (.node (.node .empty ⟨3,false,7,40⟩ .empty) ⟨3,false,7,50⟩ .empty) ⟨3,false,7,51⟩ (.node .empty ⟨3,false,7,52⟩ .empty))))
def t77 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,7,54⟩ .empty) ⟨3,false,12,32⟩ .empty) ⟨3,false,12,33⟩ (.node .empty ⟨3,false,12,36⟩ .empty)) ⟨3,false,12,37⟩ (.node (.node (.node .empty ⟨3,false,12,40⟩ .empty) ⟨3,false,13,34⟩ .empty) ⟨3,false,13,35⟩ (.node .empty ⟨3,false,13,38⟩ .empty))) ⟨3,false,13,39⟩ (.node (.node (.node (.node .empty ⟨3,false,13,40⟩ .empty) ⟨3,false,13,50⟩ .empty) ⟨3,false,13,51⟩ (.node .empty ⟨3,false,13,52⟩ .empty)) ⟨3,false,13,53⟩ (.node (.node (.node .empty ⟨3,false,13,54⟩ .empty) ⟨3,false,14,34⟩ .empty) ⟨3,false,14,35⟩ (.node .empty ⟨3,false,14,38⟩ .empty))))
def t75 : Tree := .node t76 ⟨3,false,7,53⟩ t77
def t79 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,14,40⟩ .empty) ⟨3,false,14,50⟩ .empty) ⟨3,false,14,51⟩ (.node .empty ⟨3,false,14,52⟩ .empty)) ⟨3,false,14,53⟩ (.node (.node (.node .empty ⟨3,false,14,54⟩ .empty) ⟨3,false,15,34⟩ .empty) ⟨3,false,15,35⟩ (.node .empty ⟨3,false,15,38⟩ .empty))) ⟨3,false,15,39⟩ (.node (.node (.node (.node .empty ⟨3,false,15,40⟩ .empty) ⟨3,false,15,50⟩ .empty) ⟨3,false,15,51⟩ (.node .empty ⟨3,false,15,52⟩ .empty)) ⟨3,false,15,53⟩ (.node (.node (.node .empty ⟨3,false,15,54⟩ .empty) ⟨3,false,20,34⟩ .empty) ⟨3,false,20,35⟩ (.node .empty ⟨3,false,20,38⟩ .empty))))
def t80 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,20,50⟩ .empty) ⟨3,false,20,51⟩ .empty) ⟨3,false,20,52⟩ (.node .empty ⟨3,false,20,53⟩ .empty)) ⟨3,false,20,54⟩ (.node (.node (.node .empty ⟨3,true,1,32⟩ .empty) ⟨3,true,1,33⟩ .empty) ⟨3,true,1,36⟩ (.node .empty ⟨3,true,1,37⟩ .empty))) ⟨3,true,1,40⟩ (.node (.node (.node (.node .empty ⟨3,true,1,43⟩ .empty) ⟨3,true,1,44⟩ .empty) ⟨3,true,1,47⟩ (.node .empty ⟨3,true,1,48⟩ .empty)) ⟨3,true,1,49⟩ (.node (.node (.node .empty ⟨3,true,1,55⟩ .empty) ⟨3,true,1,56⟩ .empty) ⟨3,true,1,57⟩ (.node .empty ⟨3,true,1,58⟩ .empty))))
def t78 : Tree := .node t79 ⟨3,false,20,39⟩ t80
def t74 : Tree := .node t75 ⟨3,false,14,39⟩ t78
def t66 : Tree := .node t67 ⟨3,false,7,5⟩ t74
def t84 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,2,32⟩ .empty) ⟨3,true,2,33⟩ .empty) ⟨3,true,2,36⟩ (.node .empty ⟨3,true,2,37⟩ .empty)) ⟨3,true,2,40⟩ (.node (.node (.node .empty ⟨3,true,3,32⟩ .empty) ⟨3,true,3,33⟩ .empty) ⟨3,true,3,36⟩ (.node .empty ⟨3,true,3,37⟩ .empty))) ⟨3,true,3,40⟩ (.node (.node (.node (.node .empty ⟨3,true,3,43⟩ .empty) ⟨3,true,3,44⟩ .empty) ⟨3,true,3,47⟩ (.node .empty ⟨3,true,3,48⟩ .empty)) ⟨3,true,3,49⟩ (.node (.node (.node .empty ⟨3,true,3,55⟩ .empty) ⟨3,true,3,56⟩ .empty) ⟨3,true,3,57⟩ (.node .empty ⟨3,true,3,58⟩ .empty))))
def t85 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,4,32⟩ .empty) ⟨3,true,4,33⟩ .empty) ⟨3,true,4,36⟩ (.node .empty ⟨3,true,4,37⟩ .empty)) ⟨3,true,4,40⟩ (.node (.node (.node .empty ⟨3,true,4,43⟩ .empty) ⟨3,true,4,44⟩ .empty) ⟨3,true,4,47⟩ (.node .empty ⟨3,true,4,48⟩ .empty))) ⟨3,true,4,49⟩ (.node (.node (.node (.node .empty ⟨3,true,4,55⟩ .empty) ⟨3,true,4,56⟩ .empty) ⟨3,true,4,57⟩ (.node .empty ⟨3,true,4,58⟩ .empty)) ⟨3,true,4,59⟩ (.node (.node (.node .empty ⟨3,true,8,41⟩ .empty) ⟨3,true,8,42⟩ .empty) ⟨3,true,8,45⟩ (.node .empty ⟨3,true,8,46⟩ .empty))))
def t83 : Tree := .node t84 ⟨3,true,3,59⟩ t85
def t87 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,9,43⟩ .empty) ⟨3,true,9,44⟩ .empty) ⟨3,true,9,47⟩ (.node .empty ⟨3,true,9,48⟩ .empty)) ⟨3,true,9,49⟩ (.node (.node (.node .empty ⟨3,true,9,55⟩ .empty) ⟨3,true,9,56⟩ .empty) ⟨3,true,9,57⟩ (.node .empty ⟨3,true,9,58⟩ .empty))) ⟨3,true,9,59⟩ (.node (.node (.node (.node .empty ⟨3,true,10,43⟩ .empty) ⟨3,true,10,44⟩ .empty) ⟨3,true,10,47⟩ (.node .empty ⟨3,true,10,48⟩ .empty)) ⟨3,true,10,49⟩ (.node (.node (.node .empty ⟨3,true,10,55⟩ .empty) ⟨3,true,10,56⟩ .empty) ⟨3,true,10,57⟩ (.node .empty ⟨3,true,10,58⟩ .empty))))
def t88 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,11,43⟩ .empty) ⟨3,true,11,44⟩ .empty) ⟨3,true,11,47⟩ (.node .empty ⟨3,true,11,48⟩ .empty)) ⟨3,true,11,49⟩ (.node (.node (.node .empty ⟨3,true,11,55⟩ .empty) ⟨3,true,11,56⟩ .empty) ⟨3,true,11,57⟩ (.node .empty ⟨3,true,11,58⟩ .empty))) ⟨3,true,11,59⟩ (.node (.node (.node (.node .empty ⟨3,true,16,43⟩ .empty) ⟨3,true,16,44⟩ .empty) ⟨3,true,16,47⟩ (.node .empty ⟨3,true,16,48⟩ .empty)) ⟨3,true,16,55⟩ (.node (.node (.node .empty ⟨3,true,16,56⟩ .empty) ⟨3,true,16,57⟩ .empty) ⟨3,true,16,58⟩ (.node .empty ⟨3,true,16,59⟩ .empty))))
def t86 : Tree := .node t87 ⟨3,true,10,59⟩ t88
def t82 : Tree := .node t83 ⟨3,true,8,49⟩ t86
def t91 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,17,44⟩ .empty) ⟨3,true,17,47⟩ .empty) ⟨3,true,17,48⟩ (.node .empty ⟨3,true,17,49⟩ .empty)) ⟨3,true,17,55⟩ (.node (.node (.node .empty ⟨3,true,17,56⟩ .empty) ⟨3,true,17,57⟩ .empty) ⟨3,true,17,58⟩ (.node .empty ⟨3,true,17,59⟩ .empty))) ⟨3,true,18,43⟩ (.node (.node (.node (.node .empty ⟨3,true,18,44⟩ .empty) ⟨3,true,18,47⟩ .empty) ⟨3,true,18,48⟩ (.node .empty ⟨3,true,18,49⟩ .empty)) ⟨3,true,18,55⟩ (.node (.node (.node .empty ⟨3,true,18,56⟩ .empty) ⟨3,true,18,57⟩ .empty) ⟨3,true,18,58⟩ (.node .empty ⟨3,true,18,59⟩ .empty))))
def t92 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,19,44⟩ .empty) ⟨3,true,19,47⟩ .empty) ⟨3,true,19,48⟩ (.node .empty ⟨3,true,19,49⟩ .empty)) ⟨3,true,19,55⟩ (.node (.node (.node .empty ⟨3,true,19,56⟩ .empty) ⟨3,true,19,57⟩ .empty) ⟨3,true,19,58⟩ (.node .empty ⟨3,true,19,59⟩ .empty))) ⟨4,false,0,12⟩ (.node (.node (.node (.node .empty ⟨4,false,0,14⟩ .empty) ⟨4,false,0,16⟩ .empty) ⟨4,false,0,26⟩ (.node .empty ⟨4,false,0,27⟩ .empty)) ⟨4,false,0,29⟩ (.node (.node (.node .empty ⟨4,false,0,30⟩ .empty) ⟨4,false,0,31⟩ .empty) ⟨4,false,5,1⟩ (.node .empty ⟨4,false,5,2⟩ .empty))))
def t90 : Tree := .node t91 ⟨3,true,19,43⟩ t92
def t94 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,5,5⟩ .empty) ⟨4,false,5,7⟩ .empty) ⟨4,false,5,8⟩ (.node .empty ⟨4,false,5,9⟩ .empty)) ⟨4,false,5,10⟩ (.node (.node (.node .empty ⟨4,false,5,11⟩ .empty) ⟨4,false,5,20⟩ .empty) ⟨4,false,5,21⟩ (.node .empty ⟨4,false,5,22⟩ .empty))) ⟨4,false,5,23⟩ (.node (.node (.node (.node .empty ⟨4,false,5,24⟩ .empty) ⟨4,false,5,25⟩ .empty) ⟨4,false,6,1⟩ (.node .empty ⟨4,false,6,2⟩ .empty)) ⟨4,false,6,3⟩ (.node (.node (.node .empty ⟨4,false,6,5⟩ .empty) ⟨4,false,6,7⟩ .empty) ⟨4,false,6,8⟩ (.node .empty ⟨4,false,6,9⟩ .empty))))
def t95 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,6,11⟩ .empty) ⟨4,false,6,20⟩ .empty) ⟨4,false,6,21⟩ (.node .empty ⟨4,false,6,22⟩ .empty)) ⟨4,false,6,23⟩ (.node (.node (.node .empty ⟨4,false,6,24⟩ .empty) ⟨4,false,6,25⟩ .empty) ⟨4,false,7,1⟩ (.node .empty ⟨4,false,7,2⟩ .empty))) ⟨4,false,7,3⟩ (.node (.node (.node (.node .empty ⟨4,false,7,5⟩ .empty) ⟨4,false,7,7⟩ .empty) ⟨4,false,7,8⟩ (.node .empty ⟨4,false,7,9⟩ .empty)) ⟨4,false,7,10⟩ (.node (.node .empty ⟨4,false,7,11⟩ .empty) ⟨4,false,7,20⟩ (.node .empty ⟨4,false,7,21⟩ .empty))))
def t93 : Tree := .node t94 ⟨4,false,6,10⟩ t95
def t89 : Tree := .node t90 ⟨4,false,5,3⟩ t93
def t81 : Tree := .node t82 ⟨3,true,17,43⟩ t89
def t65 : Tree := .node t66 ⟨3,true,1,59⟩ t81
def t100 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,7,23⟩ .empty) ⟨4,false,7,24⟩ .empty) ⟨4,false,7,25⟩ (.node .empty ⟨4,false,12,1⟩ .empty)) ⟨4,false,12,2⟩ (.node (.node (.node .empty ⟨4,false,12,3⟩ .empty) ⟨4,false,13,1⟩ .empty) ⟨4,false,13,2⟩ (.node .empty ⟨4,false,13,3⟩ .empty))) ⟨4,false,13,5⟩ (.node (.node (.node (.node .empty ⟨4,false,13,7⟩ .empty) ⟨4,false,13,8⟩ .empty) ⟨4,false,13,9⟩ (.node .empty ⟨4,false,13,10⟩ .empty)) ⟨4,false,13,11⟩ (.node (.node (.node .empty ⟨4,false,13,20⟩ .empty) ⟨4,false,13,21⟩ .empty) ⟨4,false,13,22⟩ (.node .empty ⟨4,false,13,23⟩ .empty))))
def t101 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,13,25⟩ .empty) ⟨4,false,14,1⟩ .empty) ⟨4,false,14,2⟩ (.node .empty ⟨4,false,14,3⟩ .empty)) ⟨4,false,14,5⟩ (.node (.node (.node .empty ⟨4,false,14,7⟩ .empty) ⟨4,false,14,8⟩ .empty) ⟨4,false,14,9⟩ (.node .empty ⟨4,false,14,10⟩ .empty))) ⟨4,false,14,11⟩ (.node (.node (.node (.node .empty ⟨4,false,14,20⟩ .empty) ⟨4,false,14,21⟩ .empty) ⟨4,false,14,22⟩ (.node .empty ⟨4,false,14,23⟩ .empty)) ⟨4,false,14,24⟩ (.node (.node (.node .empty ⟨4,false,14,25⟩ .empty) ⟨4,false,15,1⟩ .empty) ⟨4,false,15,2⟩ (.node .empty ⟨4,false,15,3⟩ .empty))))
def t99 : Tree := .node t100 ⟨4,false,13,24⟩ t101
def t103 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,15,7⟩ .empty) ⟨4,false,15,8⟩ .empty) ⟨4,false,15,9⟩ (.node .empty ⟨4,false,15,10⟩ .empty)) ⟨4,false,15,11⟩ (.node (.node (.node .empty ⟨4,false,15,20⟩ .empty) ⟨4,false,15,21⟩ .empty) ⟨4,false,15,22⟩ (.node .empty ⟨4,false,15,23⟩ .empty))) ⟨4,false,15,24⟩ (.node (.node (.node (.node .empty ⟨4,false,15,25⟩ .empty) ⟨4,false,20,1⟩ .empty) ⟨4,false,20,2⟩ (.node .empty ⟨4,false,20,3⟩ .empty)) ⟨4,false,20,5⟩ (.node (.node (.node .empty ⟨4,false,20,7⟩ .empty) ⟨4,false,20,8⟩ .empty) ⟨4,false,20,9⟩ (.node .empty ⟨4,false,20,10⟩ .empty))))
def t104 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,20,20⟩ .empty) ⟨4,false,20,21⟩ .empty) ⟨4,false,20,22⟩ (.node .empty ⟨4,false,20,23⟩ .empty)) ⟨4,false,20,24⟩ (.node (.node (.node .empty ⟨4,false,20,25⟩ .empty) ⟨4,true,0,4⟩ .empty) ⟨4,true,0,6⟩ (.node .empty ⟨4,true,0,8⟩ .empty))) ⟨4,true,0,20⟩ (.node (.node (.node (.node .empty ⟨4,true,0,21⟩ .empty) ⟨4,true,0,23⟩ .empty) ⟨4,true,0,24⟩ (.node .empty ⟨4,true,0,25⟩ .empty)) ⟨4,true,1,13⟩ (.node (.node (.node .empty ⟨4,true,1,15⟩ .empty) ⟨4,true,1,16⟩ .empty) ⟨4,true,1,17⟩ (.node .empty ⟨4,true,1,18⟩ .empty))))
def t102 : Tree := .node t103 ⟨4,false,20,11⟩ t104
def t98 : Tree := .node t99 ⟨4,false,15,5⟩ t102
def t107 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,1,26⟩ .empty) ⟨4,true,1,27⟩ .empty) ⟨4,true,1,28⟩ (.node .empty ⟨4,true,1,29⟩ .empty)) ⟨4,true,1,30⟩ (.node (.node (.node .empty ⟨4,true,1,31⟩ .empty) ⟨4,true,3,13⟩ .empty) ⟨4,true,3,15⟩ (.node .empty ⟨4,true,3,16⟩ .empty))) ⟨4,true,3,17⟩ (.node (.node (.node (.node .empty ⟨4,true,3,18⟩ .empty) ⟨4,true,3,19⟩ .empty) ⟨4,true,3,26⟩ (.node .empty ⟨4,true,3,27⟩ .empty)) ⟨4,true,3,28⟩ (.node (.node (.node .empty ⟨4,true,3,29⟩ .empty) ⟨4,true,3,30⟩ .empty) ⟨4,true,3,31⟩ (.node .empty ⟨4,true,4,13⟩ .empty))))
def t108 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,4,16⟩ .empty) ⟨4,true,4,17⟩ .empty) ⟨4,true,4,18⟩ (.node .empty ⟨4,true,4,19⟩ .empty)) ⟨4,true,4,26⟩ (.node (.node (.node .empty ⟨4,true,4,27⟩ .empty) ⟨4,true,4,28⟩ .empty) ⟨4,true,4,29⟩ (.node .empty ⟨4,true,4,30⟩ .empty))) ⟨4,true,4,31⟩ (.node (.node (.node (.node .empty ⟨4,true,5,5⟩ .empty) ⟨4,true,5,7⟩ .empty) ⟨4,true,5,8⟩ (.node .empty ⟨4,true,5,9⟩ .empty)) ⟨4,true,5,10⟩ (.node (.node (.node .empty ⟨4,true,5,11⟩ .empty) ⟨4,true,5,20⟩ .empty) ⟨4,true,5,21⟩ (.node .empty ⟨4,true,5,22⟩ .empty))))
def t106 : Tree := .node t107 ⟨4,true,4,15⟩ t108
def t110 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,5,24⟩ .empty) ⟨4,true,5,25⟩ .empty) ⟨4,true,6,5⟩ (.node .empty ⟨4,true,6,7⟩ .empty)) ⟨4,true,6,8⟩ (.node (.node (.node .empty ⟨4,true,6,9⟩ .empty) ⟨4,true,6,10⟩ .empty) ⟨4,true,6,11⟩ (.node .empty ⟨4,true,6,20⟩ .empty))) ⟨4,true,6,21⟩ (.node (.node (.node (.node .empty ⟨4,true,6,22⟩ .empty) ⟨4,true,6,23⟩ .empty) ⟨4,true,6,24⟩ (.node .empty ⟨4,true,6,25⟩ .empty)) ⟨4,true,7,5⟩ (.node (.node (.node .empty ⟨4,true,7,7⟩ .empty) ⟨4,true,7,8⟩ .empty) ⟨4,true,7,9⟩ (.node .empty ⟨4,true,7,10⟩ .empty))))
def t111 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,7,20⟩ .empty) ⟨4,true,7,21⟩ .empty) ⟨4,true,7,22⟩ (.node .empty ⟨4,true,7,23⟩ .empty)) ⟨4,true,7,24⟩ (.node (.node (.node .empty ⟨4,true,7,25⟩ .empty) ⟨4,true,8,13⟩ .empty) ⟨4,true,8,15⟩ (.node .empty ⟨4,true,8,17⟩ .empty))) ⟨4,true,8,18⟩ (.node (.node (.node (.node .empty ⟨4,true,8,19⟩ .empty) ⟨4,true,8,26⟩ .empty) ⟨4,true,8,27⟩ (.node .empty ⟨4,true,8,29⟩ .empty)) ⟨4,true,8,30⟩ (.node (.node .empty ⟨4,true,8,31⟩ .empty) ⟨4,true,9,13⟩ (.node .empty ⟨4,true,9,15⟩ .empty))))
def t109 : Tree := .node t110 ⟨4,true,7,11⟩ t111
def t105 : Tree := .node t106 ⟨4,true,5,23⟩ t109
def t97 : Tree := .node t98 ⟨4,true,1,19⟩ t105
def t115 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,9,17⟩ .empty) ⟨4,true,9,18⟩ .empty) ⟨4,true,9,19⟩ (.node .empty ⟨4,true,9,26⟩ .empty)) ⟨4,true,9,27⟩ (.node (.node (.node .empty ⟨4,true,9,28⟩ .empty) ⟨4,true,9,29⟩ .empty) ⟨4,true,9,30⟩ (.node .empty ⟨4,true,9,31⟩ .empty))) ⟨4,true,10,13⟩ (.node (.node (.node (.node .empty ⟨4,true,10,15⟩ .empty) ⟨4,true,10,16⟩ .empty) ⟨4,true,10,17⟩ (.node .empty ⟨4,true,10,18⟩ .empty)) ⟨4,true,10,19⟩ (.node (.node (.node .empty ⟨4,true,10,26⟩ .empty) ⟨4,true,10,27⟩ .empty) ⟨4,true,10,28⟩ (.node .empty ⟨4,true,10,29⟩ .empty))))
def t116 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,10,31⟩ .empty) ⟨4,true,11,13⟩ .empty) ⟨4,true,11,15⟩ (.node .empty ⟨4,true,11,16⟩ .empty)) ⟨4,true,11,17⟩ (.node (.node (.node .empty ⟨4,true,11,18⟩ .empty) ⟨4,true,11,19⟩ .empty) ⟨4,true,11,26⟩ (.node .empty ⟨4,true,11,27⟩ .empty))) ⟨4,true,11,28⟩ (.node (.node (.node (.node .empty ⟨4,true,11,29⟩ .empty) ⟨4,true,11,30⟩ .empty) ⟨4,true,11,31⟩ (.node .empty ⟨4,true,12,5⟩ .empty)) ⟨4,true,12,7⟩ (.node (.node (.node .empty ⟨4,true,12,9⟩ .empty) ⟨4,true,12,10⟩ .empty) ⟨4,true,12,11⟩ (.node .empty ⟨4,true,12,20⟩ .empty))))
def t114 : Tree := .node t115 ⟨4,true,10,30⟩ t116
def t118 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,12,23⟩ .empty) ⟨4,true,12,24⟩ .empty) ⟨4,true,12,25⟩ (.node .empty ⟨4,true,13,5⟩ .empty)) ⟨4,true,13,7⟩ (.node (.node (.node .empty ⟨4,true,13,8⟩ .empty) ⟨4,true,13,9⟩ .empty) ⟨4,true,13,10⟩ (.node .empty ⟨4,true,13,11⟩ .empty))) ⟨4,true,13,20⟩ (.node (.node (.node (.node .empty ⟨4,true,13,21⟩ .empty) ⟨4,true,13,22⟩ .empty) ⟨4,true,13,23⟩ (.node .empty ⟨4,true,13,24⟩ .empty)) ⟨4,true,13,25⟩ (.node (.node (.node .empty ⟨4,true,14,5⟩ .empty) ⟨4,true,14,7⟩ .empty) ⟨4,true,14,8⟩ (.node .empty ⟨4,true,14,9⟩ .empty))))
def t119 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,14,11⟩ .empty) ⟨4,true,14,20⟩ .empty) ⟨4,true,14,21⟩ (.node .empty ⟨4,true,14,22⟩ .empty)) ⟨4,true,14,23⟩ (.node (.node (.node .empty ⟨4,true,14,24⟩ .empty) ⟨4,true,14,25⟩ .empty) ⟨4,true,15,5⟩ (.node .empty ⟨4,true,15,7⟩ .empty))) ⟨4,true,15,8⟩ (.node (.node (.node (.node .empty ⟨4,true,15,9⟩ .empty) ⟨4,true,15,10⟩ .empty) ⟨4,true,15,11⟩ (.node .empty ⟨4,true,15,20⟩ .empty)) ⟨4,true,15,21⟩ (.node (.node (.node .empty ⟨4,true,15,22⟩ .empty) ⟨4,true,15,23⟩ .empty) ⟨4,true,15,24⟩ (.node .empty ⟨4,true,15,25⟩ .empty))))
def t117 : Tree := .node t118 ⟨4,true,14,10⟩ t119
def t113 : Tree := .node t114 ⟨4,true,12,21⟩ t117
def t122 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,16,15⟩ .empty) ⟨4,true,16,17⟩ .empty) ⟨4,true,16,18⟩ (.node .empty ⟨4,true,16,19⟩ .empty)) ⟨4,true,16,26⟩ (.node (.node (.node .empty ⟨4,true,16,27⟩ .empty) ⟨4,true,16,29⟩ .empty) ⟨4,true,16,30⟩ (.node .empty ⟨4,true,16,31⟩ .empty))) ⟨4,true,17,13⟩ (.node (.node (.node (.node .empty ⟨4,true,17,15⟩ .empty) ⟨4,true,17,16⟩ .empty) ⟨4,true,17,17⟩ (.node .empty ⟨4,true,17,18⟩ .empty)) ⟨4,true,17,19⟩ (.node (.node (.node .empty ⟨4,true,17,26⟩ .empty) ⟨4,true,17,27⟩ .empty) ⟨4,true,17,28⟩ (.node .empty ⟨4,true,17,29⟩ .empty))))
def t123 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,17,31⟩ .empty) ⟨4,true,18,13⟩ .empty) ⟨4,true,18,15⟩ (.node .empty ⟨4,true,18,16⟩ .empty)) ⟨4,true,18,17⟩ (.node (.node (.node .empty ⟨4,true,18,18⟩ .empty) ⟨4,true,18,19⟩ .empty) ⟨4,true,18,26⟩ (.node .empty ⟨4,true,18,27⟩ .empty))) ⟨4,true,18,28⟩ (.node (.node (.node (.node .empty ⟨4,true,18,29⟩ .empty) ⟨4,true,18,30⟩ .empty) ⟨4,true,18,31⟩ (.node .empty ⟨4,true,19,13⟩ .empty)) ⟨4,true,19,15⟩ (.node (.node (.node .empty ⟨4,true,19,16⟩ .empty) ⟨4,true,19,17⟩ .empty) ⟨4,true,19,18⟩ (.node .empty ⟨4,true,19,19⟩ .empty))))
def t121 : Tree := .node t122 ⟨4,true,17,30⟩ t123
def t125 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,19,27⟩ .empty) ⟨4,true,19,28⟩ .empty) ⟨4,true,19,29⟩ (.node .empty ⟨4,true,19,30⟩ .empty)) ⟨4,true,19,31⟩ (.node (.node (.node .empty ⟨4,true,20,5⟩ .empty) ⟨4,true,20,7⟩ .empty) ⟨4,true,20,9⟩ (.node .empty ⟨4,true,20,10⟩ .empty))) ⟨4,true,20,11⟩ (.node (.node (.node (.node .empty ⟨4,true,20,20⟩ .empty) ⟨4,true,20,21⟩ .empty) ⟨4,true,20,23⟩ (.node .empty ⟨4,true,20,24⟩ .empty)) ⟨4,true,20,25⟩ (.node (.node (.node .empty ⟨5,true,1,0⟩ .empty) ⟨5,true,1,13⟩ .empty) ⟨5,true,1,15⟩ (.node .empty ⟨5,true,1,16⟩ .empty))))
def t126 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,1,18⟩ .empty) ⟨5,true,1,19⟩ .empty) ⟨5,true,1,26⟩ (.node .empty ⟨5,true,1,27⟩ .empty)) ⟨5,true,1,28⟩ (.node (.node (.node .empty ⟨5,true,1,29⟩ .empty) ⟨5,true,1,30⟩ .empty) ⟨5,true,1,31⟩ (.node .empty ⟨5,true,1,43⟩ .empty))) ⟨5,true,1,44⟩ (.node (.node (.node (.node .empty ⟨5,true,1,47⟩ .empty) ⟨5,true,1,48⟩ .empty) ⟨5,true,1,49⟩ (.node .empty ⟨5,true,1,55⟩ .empty)) ⟨5,true,1,56⟩ (.node (.node .empty ⟨5,true,1,57⟩ .empty) ⟨5,true,1,58⟩ (.node .empty ⟨5,true,1,59⟩ .empty))))
def t124 : Tree := .node t125 ⟨5,true,1,17⟩ t126
def t120 : Tree := .node t121 ⟨4,true,19,26⟩ t124
def t112 : Tree := .node t113 ⟨4,true,16,13⟩ t120
def t96 : Tree := .node t97 ⟨4,true,9,16⟩ t112
def t64 : Tree := .node t65 ⟨4,false,7,22⟩ t96
def t0 : Tree := .node t1 ⟨3,false,3,31⟩ t64

def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨dl,dr,el,er,t0⟩

theorem h6 : t6.all (stepOK table cert) = true := by decide

theorem h7 : t7.all (stepOK table cert) = true := by decide

theorem h5 : t5.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h6 h7

theorem h9 : t9.all (stepOK table cert) = true := by decide

theorem h10 : t10.all (stepOK table cert) = true := by decide

theorem h8 : t8.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h9 h10

theorem h4 : t4.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h5 h8

theorem h13 : t13.all (stepOK table cert) = true := by decide

theorem h14 : t14.all (stepOK table cert) = true := by decide

theorem h12 : t12.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h13 h14

theorem h16 : t16.all (stepOK table cert) = true := by decide

theorem h17 : t17.all (stepOK table cert) = true := by decide

theorem h15 : t15.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h16 h17

theorem h11 : t11.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h12 h15

theorem h3 : t3.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h4 h11

theorem h21 : t21.all (stepOK table cert) = true := by decide

theorem h22 : t22.all (stepOK table cert) = true := by decide

theorem h20 : t20.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h21 h22

theorem h24 : t24.all (stepOK table cert) = true := by decide

theorem h25 : t25.all (stepOK table cert) = true := by decide

theorem h23 : t23.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h24 h25

theorem h19 : t19.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h20 h23

theorem h28 : t28.all (stepOK table cert) = true := by decide

theorem h29 : t29.all (stepOK table cert) = true := by decide

theorem h27 : t27.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h28 h29

theorem h31 : t31.all (stepOK table cert) = true := by decide

theorem h32 : t32.all (stepOK table cert) = true := by decide

theorem h30 : t30.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h31 h32

theorem h26 : t26.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h27 h30

theorem h18 : t18.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h19 h26

theorem h2 : t2.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h3 h18

theorem h37 : t37.all (stepOK table cert) = true := by decide

theorem h38 : t38.all (stepOK table cert) = true := by decide

theorem h36 : t36.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h37 h38

theorem h40 : t40.all (stepOK table cert) = true := by decide

theorem h41 : t41.all (stepOK table cert) = true := by decide

theorem h39 : t39.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h40 h41

theorem h35 : t35.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h36 h39

theorem h44 : t44.all (stepOK table cert) = true := by decide

theorem h45 : t45.all (stepOK table cert) = true := by decide

theorem h43 : t43.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h44 h45

theorem h47 : t47.all (stepOK table cert) = true := by decide

theorem h48 : t48.all (stepOK table cert) = true := by decide

theorem h46 : t46.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h47 h48

theorem h42 : t42.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h43 h46

theorem h34 : t34.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h35 h42

theorem h52 : t52.all (stepOK table cert) = true := by decide

theorem h53 : t53.all (stepOK table cert) = true := by decide

theorem h51 : t51.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h52 h53

theorem h55 : t55.all (stepOK table cert) = true := by decide

theorem h56 : t56.all (stepOK table cert) = true := by decide

theorem h54 : t54.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h55 h56

theorem h50 : t50.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h51 h54

theorem h59 : t59.all (stepOK table cert) = true := by decide

theorem h60 : t60.all (stepOK table cert) = true := by decide

theorem h58 : t58.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h59 h60

theorem h62 : t62.all (stepOK table cert) = true := by decide

theorem h63 : t63.all (stepOK table cert) = true := by decide

theorem h61 : t61.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h62 h63

theorem h57 : t57.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h58 h61

theorem h49 : t49.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h50 h57

theorem h33 : t33.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h34 h49

theorem h1 : t1.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h2 h33

theorem h69 : t69.all (stepOK table cert) = true := by decide

theorem h70 : t70.all (stepOK table cert) = true := by decide

theorem h68 : t68.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h69 h70

theorem h72 : t72.all (stepOK table cert) = true := by decide

theorem h73 : t73.all (stepOK table cert) = true := by decide

theorem h71 : t71.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h72 h73

theorem h67 : t67.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h68 h71

theorem h76 : t76.all (stepOK table cert) = true := by decide

theorem h77 : t77.all (stepOK table cert) = true := by decide

theorem h75 : t75.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h76 h77

theorem h79 : t79.all (stepOK table cert) = true := by decide

theorem h80 : t80.all (stepOK table cert) = true := by decide

theorem h78 : t78.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h79 h80

theorem h74 : t74.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h75 h78

theorem h66 : t66.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h67 h74

theorem h84 : t84.all (stepOK table cert) = true := by decide

theorem h85 : t85.all (stepOK table cert) = true := by decide

theorem h83 : t83.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h84 h85

theorem h87 : t87.all (stepOK table cert) = true := by decide

theorem h88 : t88.all (stepOK table cert) = true := by decide

theorem h86 : t86.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h87 h88

theorem h82 : t82.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h83 h86

theorem h91 : t91.all (stepOK table cert) = true := by decide

theorem h92 : t92.all (stepOK table cert) = true := by decide

theorem h90 : t90.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h91 h92

theorem h94 : t94.all (stepOK table cert) = true := by decide

theorem h95 : t95.all (stepOK table cert) = true := by decide

theorem h93 : t93.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h94 h95

theorem h89 : t89.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h90 h93

theorem h81 : t81.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h82 h89

theorem h65 : t65.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h66 h81

theorem h100 : t100.all (stepOK table cert) = true := by decide

theorem h101 : t101.all (stepOK table cert) = true := by decide

theorem h99 : t99.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h100 h101

theorem h103 : t103.all (stepOK table cert) = true := by decide

theorem h104 : t104.all (stepOK table cert) = true := by decide

theorem h102 : t102.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h103 h104

theorem h98 : t98.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h99 h102

theorem h107 : t107.all (stepOK table cert) = true := by decide

theorem h108 : t108.all (stepOK table cert) = true := by decide

theorem h106 : t106.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h107 h108

theorem h110 : t110.all (stepOK table cert) = true := by decide

theorem h111 : t111.all (stepOK table cert) = true := by decide

theorem h109 : t109.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h110 h111

theorem h105 : t105.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h106 h109

theorem h97 : t97.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h98 h105

theorem h115 : t115.all (stepOK table cert) = true := by decide

theorem h116 : t116.all (stepOK table cert) = true := by decide

theorem h114 : t114.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h115 h116

theorem h118 : t118.all (stepOK table cert) = true := by decide

theorem h119 : t119.all (stepOK table cert) = true := by decide

theorem h117 : t117.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h118 h119

theorem h113 : t113.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h114 h117

theorem h122 : t122.all (stepOK table cert) = true := by decide

theorem h123 : t123.all (stepOK table cert) = true := by decide

theorem h121 : t121.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h122 h123

theorem h125 : t125.all (stepOK table cert) = true := by decide

theorem h126 : t126.all (stepOK table cert) = true := by decide

theorem h124 : t124.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h125 h126

theorem h120 : t120.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h121 h124

theorem h112 : t112.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h113 h120

theorem h96 : t96.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h97 h112

theorem h64 : t64.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h65 h96

theorem h0 : t0.all (stepOK table cert) = true :=
  Tree.all_node (by decide) h1 h64

theorem checked : cert.states.all (stepOK table cert) = true := h0

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm

#print axioms checked
#print axioms never
end BB6.Agent8Raw54.RBRun23
