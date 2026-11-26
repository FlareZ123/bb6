'use strict';
// Original source: d1d231afe3a5f6310ac9f956d5687b5a45d7a13d/BusyBeaver/BB6/Halt/M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.lean
// Pass the unchanged pinned Lean source as the first argument.
function calculate(a) {
 const rule=Object.fromEntries([...a.matchAll(/private theorem (tr_\d+)[\s\S]*?:\s*CarrySem false (false|true) (\d+)/g)].map(m=>[m[1],[m[2]==="true"?1:0,BigInt(m[3])]]));
 const chunk=(name,next)=>a.slice(a.indexOf("private theorem "+name),a.indexOf("private theorem "+next,a.indexOf("private theorem "+name)+1));
 const eat=chunk("eat_M06_2 (","eat_M06_2_pow"),tail=chunk("tail_era2_halts","encode_cp5_eq");
 const ops=s=>[...s.matchAll(/\b(tr_\d+)\s+\?_|th_spawn([12]) \.S(\d)|th_loop_(?:even|odd) (\d+)/g)].map(m=>m[1]?["rule",m[1]]:m[2]?["lift",Number(m[2])-1,Number(m[3])]:["loop",Number(m[4])]);
 const ea=ops(eat),ta=ops(tail),flat=ta.flatMap(op=>op[0]==="loop"?Array.from({length:op[1]},()=>ea).flat():[op]);
 const qPol=j=>[1,1,1,0,0,1,0,0][j];
 const table=[Array(8),Array(8)];
 for(const m of a.matchAll(/\| (false|true), \.S(\d) => \(km1( \+ 1)?, \.S(\d), (none|some (?:false|true)), (56|112) \* km1 \+ \(if isTop then (\d+) else (\d+)\)\)/g))table[Number(m[1]==="true")][Number(m[2])]=[Number(Boolean(m[3])),Number(m[4]),m[5]==="none"?-1:Number(m[5]==="some true"),Number(m[6]),Number(m[7]),Number(m[8])];
 if(Object.keys(rule).length!==54||ea.length!==15||ta.length!==200||table.some(x=>x.filter(Boolean).length!==8))throw Error("source shape");
 let q=0;
 const tagged=flat.map(o=>{let q0=q;if(o[0]==="rule"){if(rule[o[1]][0]!==q)throw Error("rule polarity "+o);q=1-q}else q=qPol(o[2]);return [q0,...o]});
 if(q!==1)throw Error("terminal polarity "+q);
 /** One primitive carry transition in the source's 16-state layer automaton. */
 function advance(top,p,j,k,r,q){let cost=0n,em=0;for(let i=0;i<r;i++){const [dk,j1,b,slope,cT,cN]=table[p][j];cost+=BigInt(slope)*k+BigInt(top?cT:cN);if(b!==-1){if(b!==q)throw Error("polarity");em++;q=1-q}k+=BigInt(dk);j=j1;p=1-p}return {p,j,k,q,cost,em}}
 /** Lift n alternating nonterminal child carries followed by one terminal child call. */
 function lift(top,p,j,k,n,c) {
   let q=qPol(j),z=advance(top,p,j,k,16,q),z1=advance(top,p,j,k+1n,16,q);
   if(z.p!==p||z.j!==j||z.k!==k+4n||z.em!==6||z.q!==q||z1.cost-z.cost!==1344n)throw Error("16-cycle");
   let Q=n/6n,rem=Number(n%6n),r=0;
   // Stop immediately before emission rem+1; include all preceding silent calls.
   let w=advance(top,p,j,k+4n*Q,0,q);
   for(;r<16;r++){let e=table[w.p][w.j][2];if(w.em===rem&&e!==-1)break;w=advance(top,p,j,k+4n*Q,r+1,q)}
   if(r===16||w.em!==rem||table[w.p][w.j][2]!==w.q)throw Error("terminal emission");
   let end=24n*(w.k+1n)+BigInt(w.p?(top?21:48):(top?33:60));
   if(w.p&&(w.j===1||w.j===4))end+=56n*w.k+63n+29n;
   let overhead=Q*z.cost+2688n*Q*(Q-1n)+w.cost;
   return [16n*Q+BigInt(r),c+overhead+end];
 }
 let n=0n,c=304n,lifts=0,rules=0;
 for(const [p,kind,arg,j] of tagged.reverse()){if(kind==="rule"){n++;c+=rule[arg][1];rules++}else{[n,c]=lift(false,p,j,BigInt(arg),n,c);lifts++}}
 const base={carries:n.toString(),moves:c.toString()};
 // The original is_halt_proof wraps S4 with polarity true, then S0 with polarity false at the top.
 [n,c]=lift(false,1,4,0n,n,c);[n,c]=lift(true,0,0,0n,n,c);
 return {rules,lifts,flatOps:flat.length,base,cp5ToHaltOrdinaryMoves:c.toString(),topNonterminalCarries:n.toString(),bits:c.toString(2).length,terminalQueryExcluded:true};
}
const fs = require('node:fs');
if (require.main === module) console.log(JSON.stringify(calculate(fs.readFileSync(process.argv[2], 'utf8')), null, 2));
module.exports = { calculate };
