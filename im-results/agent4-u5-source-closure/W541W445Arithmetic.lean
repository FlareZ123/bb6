import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

-- Residual congruence constants and inverse of 211 modulo 2048.
example : 211*1707+1360+22155*541 = 2048*6029 := by omega
example : 211*1547+1360+22155*445 = 2048*4974 := by omega
example : 211*22363 = 2048*2304+1 := by omega

-- The exact q-fan has only q=0,1 on both t-cylinders.
example (v : Nat) : (43*(1707+2048*v)-1)%16=8 := by omega
example (v : Nat) : (43*(1547+2048*v)-1)%16=8 := by omega

-- W541, q=0 chain: affine parent equations.
example (v : Nat) : (73398+88064*v)+(72544+87040*v)-2 = 145940+175104*v := by omega
example (v : Nat) : ((72544+87040*v)-2)/2 = 36271+43520*v := by omega
example (v : Nat) : ((145940+175104*v)+(36271+43520*v)-5)/2 = 91103+109312*v := by omega
example (v : Nat) : ((145940+175104*v)+3*(36271+43520*v)-9)/4 = 63686+76416*v := by omega
example (v : Nat) : (91103+109312*v)+(63686+76416*v)-2 = 154787+185728*v := by omega
example (v : Nat) : ((63686+76416*v)-2)/2 = 31842+38208*v := by omega
example (v : Nat) : (154787+185728*v)+(31842+38208*v)-2 = 186627+223936*v := by omega
example (v : Nat) : ((31842+38208*v)-2)/2 = 15920+19104*v := by omega
example (v : Nat) : (186627+223936*v)+(15920+19104*v)-2 = 202545+243040*v := by omega
example (v : Nat) : ((15920+19104*v)-2)/2 = 7959+9552*v := by omega
example (v : Nat) : ((202545+243040*v)+(7959+9552*v)-4)/2 = 105250+126296*v := by omega
example (v : Nat) : ((202545+243040*v)+3*(7959+9552*v)-10)/4 = 56603+67924*v := by omega

-- W541, q=1 chain.
example (v : Nat) : (18348+22016*v)+(100066+120064*v)-2 = 118412+142080*v := by omega
example (v : Nat) : ((100066+120064*v)-2)/2 = 50032+60032*v := by omega
example (v : Nat) : (118412+142080*v)+(50032+60032*v)-2 = 168442+202112*v := by omega
example (v : Nat) : ((50032+60032*v)-2)/2 = 25015+30016*v := by omega

-- W445, q=0 chain.
example (v : Nat) : (66518+88064*v)+(65744+87040*v)-2 = 132260+175104*v := by omega
example (v : Nat) : ((65744+87040*v)-2)/2 = 32871+43520*v := by omega
example (v : Nat) : ((132260+175104*v)+(32871+43520*v)-5)/2 = 82563+109312*v := by omega
example (v : Nat) : ((132260+175104*v)+3*(32871+43520*v)-9)/4 = 57716+76416*v := by omega

-- W445, q=1 chain.
example (v : Nat) : (16628+22016*v)+(90686+120064*v)-2 = 107312+142080*v := by omega
example (v : Nat) : ((90686+120064*v)-2)/2 = 45342+60032*v := by omega
example (v : Nat) : (107312+142080*v)+(45342+60032*v)-2 = 152652+202112*v := by omega
example (v : Nat) : ((45342+60032*v)-2)/2 = 22670+30016*v := by omega
example (v : Nat) : (152652+202112*v)+(22670+30016*v)-2 = 175320+232128*v := by omega
example (v : Nat) : ((22670+30016*v)-2)/2 = 11334+15008*v := by omega
example (v : Nat) : (175320+232128*v)+(11334+15008*v)-2 = 186652+247136*v := by omega
example (v : Nat) : ((11334+15008*v)-2)/2 = 5666+7504*v := by omega
example (v : Nat) : (186652+247136*v)+(5666+7504*v)-2 = 192316+254640*v := by omega
example (v : Nat) : ((5666+7504*v)-2)/2 = 2832+3752*v := by omega
example (v : Nat) : (192316+254640*v)+(2832+3752*v)-2 = 195146+258392*v := by omega
example (v : Nat) : ((2832+3752*v)-2)/2 = 1415+1876*v := by omega

-- W541 gate residues.
example (v : Nat) : ((73398+88064*v)+(72544+87040*v))%4=2 := by omega
example (v : Nat) : ((145940+175104*v)+(36271+43520*v)+1)%8=4 := by omega
example (v : Nat) : ((91103+109312*v)+(63686+76416*v))%8=5 := by omega
example (v : Nat) : ((154787+185728*v)+(31842+38208*v))%8=5 := by omega
example (v : Nat) : ((186627+223936*v)+(15920+19104*v))%8=3 := by omega
example (v : Nat) : ((202545+243040*v)+(7959+9552*v))%16=8 := by omega
example (v : Nat) : ((105250+126296*v)+(56603+67924*v))%4=1 := by omega
example (v : Nat) : ((18348+22016*v)+(100066+120064*v))%4=2 := by omega
example (v : Nat) : ((118412+142080*v)+(50032+60032*v))%8=4 := by omega
example (v : Nat) : ((168442+202112*v)+(25015+30016*v))%4=1 := by omega

-- W445 gate residues, including the exact sum-seven cylinder.
example (v : Nat) : ((66518+88064*v)+(65744+87040*v))%4=2 := by omega
example (v : Nat) : ((132260+175104*v)+(32871+43520*v)+1)%8=4 := by omega
example (v : Nat) : 12≤57716+76416*v := by omega
example (v : Nat) : ((82563+109312*v)+(57716+76416*v))%8=7 := by omega
example (v : Nat) : ((82563+109312*v)+(57716+76416*v)+1)%16=8 := by omega
example (v : Nat) : ((82563+109312*v)+(57716+76416*v)+1)%32=24 := by omega
example (v : Nat) : (82563+109312*v)%4=3 := by omega
example (v : Nat) : (57716+76416*v)%8=4 := by omega
example (v : Nat) : ((16628+22016*v)+(90686+120064*v))%4=2 := by omega
example (v : Nat) : ((107312+142080*v)+(45342+60032*v))%4=2 := by omega
example (v : Nat) : ((152652+202112*v)+(22670+30016*v))%4=2 := by omega
example (v : Nat) : ((175320+232128*v)+(11334+15008*v))%4=2 := by omega
example (v : Nat) : ((186652+247136*v)+(5666+7504*v))%4=2 := by omega
example (v : Nat) : ((192316+254640*v)+(2832+3752*v))%8=4 := by omega
example (v : Nat) : (1415+1876*v)%2=1 := by omega
example (v : Nat) : ((195146+258392*v)+(1415+1876*v))%4=1 := by omega
