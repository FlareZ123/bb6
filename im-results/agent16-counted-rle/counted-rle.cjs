// Counted replay of pinned upstream BusyBeaver.RleStackEngine.
// Usage: node counted-rle.cjs /path/to/cryptids
// BigInt arithmetic; exact original checkpoint equality is mandatory.
function countedRle(source, table) {
 const Z=c=>["z",c],D=v=>["d",v],K=(r,c)=>["k",r,c],min=(a,b)=>a<b?a:b;
 const push0=(c,L)=>c===0n?L:L[0]?.[0]==="z"?[Z(c+L[0][1]),...L.slice(1)]:[Z(c),...L];
 const pushK=(r,c,L)=>c===0n?L:L[0]?.[0]==="k"&&L[0][1]===r?[K(r,c+L[0][2]),...L.slice(1)]:[K(r,c),...L];
 const pushLd=(v,L)=>v===0n?push0(1n,L):v===1n&&L[0]?.[0]==="z"&&L[0][1]>=2n&&L[1]?.[0]==="d"&&L[1][1]===1n?[D(1n),...pushK(L[0][1]-2n,1n,L.slice(2))]:[D(v),...L];
 function pushRk(r,c,R){if(c===0n)return R;if(r>=1n&&R[0]?.[0]==="z"&&R[0][1]===r&&R[1]?.[0]==="d"&&R[1][1]===2n&&R[2]?.[0]==="d"&&R[2][1]===1n){c++;R=R.slice(3);}return pushK(r,c,R);}
 const pushRd=(v,R)=>v===0n?push0(1n,R):v===2n&&R[0]?.[0]==="d"&&R[0][1]===1n?pushRk(0n,1n,R.slice(1)):[D(v),...R];
 function pop(L,left){if(!L.length)return null;const [[t,a,b],...xs]=L;if(t==="d")return [a,xs];if(t==="z")return a===0n?pop(xs,left):[0n,a===1n?xs:[Z(a-1n),...xs]];if(b===0n)return pop(xs,left);const tail=b===1n?xs:[K(a,b-1n),...xs];return left?[0n,push0(a+1n,pushLd(1n,tail))]:a===0n?[2n,[D(1n),...tail]]:[0n,push0(a-1n,[D(2n),D(1n),...tail])];}
 const bump=(L,left)=>{const p=pop(L,left);return p?(left?pushLd:pushRd)(p[0]+1n,p[1]):[Z(1n)];};
 const pushSeg=(r,c,S)=>c===0n?S:S[0]?.[0]===r?[[r,c+S[0][1]],...S.slice(1)]:[[r,c],...S];
 const unpack=(c,S,b)=>[...(c===0n?[]:[Z(c)]),D(1n),...S.filter(x=>x[1]!==0n).map(x=>K(...x)),Z(b+2n)];
 function packTail(c,L){if(!L.length)return c>=2n?[[],c-2n]:null;const [[t,a,b],...xs]=L;if(t==="z")return packTail(c+a,xs);if(t==="d"){if(a!==1n||c<2n)return null;const p=packTail(0n,xs);return p?[pushSeg(c-2n,1n,p[0]),p[1]]:null;}if(b===0n)return packTail(c,xs);const p=packTail(0n,xs);return p?[pushSeg(c+a,1n,pushSeg(a,b-1n,p[0])),p[1]]:null;}
 function packHead(c,L){if(!L.length)return null;const [[t,a,b],...xs]=L;if(t==="z")return packHead(c+a,xs);if(t==="d"){if(a!==1n)return null;const p=packTail(0n,xs);return p?[c,p[0],p[1]]:null;}if(b===0n)return packHead(c,xs);const p=packTail(0n,xs);return p?[c+a+2n,pushSeg(a,b-1n,p[0]),p[1]]:null;}
 // Exact ordinary move counts, excluding halt query.
 const tri=q=>q*(q-1n)/2n,segCost=S=>S.reduce((a,[r,c])=>a+c*(6n*r+26n),0n);
 const drBot=k=>6n*k+14n,drBotZeros=(q,k)=>q*(6n*k+9n*q+9n);
 const drOne=(c,s,b)=>6n*c+s+6n*b+46n;
 const drZeros=(q,c,s,b)=>q*(6n*c+s+6n*b+50n+6n*(q-1n))+18n*tri(q);
 const rnilOne=(c,s,b)=>6n*c+s+6n*b+57n;
 const rnilZero=(q,s,b)=>q*(s+6n*b+57n+6n*(q-1n))+20n*tri(q);
 const p1Pow=(q,r,s,b)=>q*(10n*r+s+6n*b+75n+6n*(q-1n))+(6n*r+38n)*tri(q);
 const p2One=(r,s,b)=>r===0n?s+6n*b+73n:(()=>{let x=r-1n;return (x+2n)*(s+6n*b)+165n+116n*x+6n*x*x+18n*tri(x);})();
 const p2Pow=(q,r,s,b)=>q*p2One(r,s,b+(q-1n)*(r+1n))+(r+1n)*(18n*r+38n)*tri(q);
 const raw=(mode,L,R,cost,rule,halted=false)=>[{mode,L,R,halted},cost,rule];
 const clean=(mode,c,S,b,R,cost,rule)=>[{mode,c,S,b,R,halted:false},cost,rule];
 function brPop(L,R){const p=pop(R,false);if(!p)return raw("C",bump(L,true),[],1n,"BR_nil");const [d,R1]=p;if(d===0n)return raw("BR",push0(1n,L),R1,2n,"BR_zero");if(d===1n)return raw("DR0",L,bump(R1,false),4n,"BR_one");return raw("B",bump(L,true),pushRd(d-2n,R1),5n,"BR_add_two");}
 function rawStep({mode,L,R}){
  const canPack=mode==="DR0"||mode==="B"&&(!R.length||L[0]?.[0]==="d"&&L[0][1]===1n)||mode==="BR"&&!R.length;
  if(canPack){const p=packHead(0n,L);if(p&&p[2]>=1n)return clean(mode,...p,R,0n,"pack");}
  const [r0,r1]=R,[l0,l1]=L;
  switch(mode){
   case "B":{if(!r0)return raw("C",bump(L,true),[],1n,"B_nil");if(r0[0]==="z")return raw("B",push0(r0[1],L),R.slice(1),4n*r0[1],"B_zeros");const p=pop(R,false);if(!p)return raw("C",bump(L,true),[],1n,"B_nil");const [d,R1]=p;return d===0n?raw("B",push0(1n,L),R1,4n,"B_zero"):raw("BR",L,push0(1n,pushRd(d-1n,R1)),2n,"B_succ");}
   case "BR":{if(!r0)return raw("C",bump(L,true),[],1n,"BR_nil");if(r0[0]==="z")return raw("BR",push0(r0[1],L),R.slice(1),2n*r0[1],"BR_zeros");if(r0[0]==="k"){const [,r,m]=r0;if(m===0n)return raw("BR",L,R.slice(1),0n,"BR_empty_block");const p=pop(L,true);if(p&&p[0]===0n)return raw("BR",push0(3n,pushLd(1n,pushK(r,m-1n,push0(r,p[1])))),R.slice(1),m*(2n*r+15n),"BR_block");}return brPop(L,R);}
   case "DR0":{if(L.length===1&&l0[0]==="z"){const c=l0[1];if(r0?.[0]==="d"&&r0[1]===1n&&r1?.[0]==="z"){const q=r1[1];return raw("DR0",[Z(c+3n*q)],[D(1n),...R.slice(2)],drBotZeros(q,c),"DR0_bot_zeros");}return raw("BR",[Z(c+3n)],R,drBot(c),"DR0_bot");}const p=pop(L,true);if(!p)return raw("C",[D(1n)],R,3n,"DR0_nil");const [a,L1]=p;if(a===0n)return l0[0]==="z"?raw("DR0",L.slice(1),push0(l0[1],R),4n*l0[1],"DR0_zeros"):raw("DR0",L1,push0(1n,R),4n,"DR0_zero");return raw("C",pushLd(a-1n,L1),push0(1n,R),3n,"DR0_succ");}
   case "C":{if(l0?.[0]==="z"){const cz=l0[1];if(l1?.[0]==="k"&&cz===1n){const [,r,m]=l1;return raw("C",push0(1n,L.slice(2)),pushRk(r,m,R),m*(4n*r+11n),"C_block");}if(l1?.[0]==="d"&&cz>=4n&&l1[1]===1n){let r=cz-3n;return raw("C",push0(1n,L.slice(2)),pushRk(r,1n,R),4n*r+11n,"C_r_add_three");}if(L.length===1&&cz>=4n){let r=cz-4n;return raw("DR0",[],pushRk(r,1n,R),4n*r+12n,"C_bot_four");}}const p=pop(L,true);if(!p)return raw("DR0",[],R,1n,"C_nil");const [a,L1]=p;if(a>=2n)return raw("C",pushLd(a,L1),R,3n,"C_halt",true);const pp=pop(L1,true);if(a===0n){if(!pp)return raw("C",[],pushRd(1n,R),3n,"C_zero_nil");const [a1,L3]=pp;if(a1===0n)return raw("C",bump(L3,true),pushRd(1n,R),5n,"C_zero_zero");if(a1===1n)return raw("C",bump(bump(L3,true),true),push0(1n,bump(R,false)),17n,"C_zero_one");return raw("BR",pushLd(a1-2n,L3),push0(1n,pushRd(1n,R)),4n,"C_zero_add_two");}if(!pp)return raw("B",[Z(1n)],pushRd(1n,R),5n,"C_one_nil");const [a1,L3]=pp;if(a1===0n)return raw("DR0",L3,pushRd(2n,R),7n,"C_one_zero");return raw("C",pushLd(a1-1n,L3),pushRd(2n,R),6n,"C_one_succ");}
   default:throw Error("mode "+mode);
  }
 }
 function cleanStep({mode,c,S,b,R}){
  const [r0,r1,r2]=R,s=segCost(S),un=()=>raw(mode,unpack(c,S,b),R,0n,"unpack");
  const rnil=()=>c>=1n&&b>=1n?clean("B",1n,pushSeg(0n,b-1n,pushSeg(c-1n,1n,S)),0n,[],rnilOne(c-1n,s,b-1n)+rnilZero(b-1n,s+6n*(c-1n)+26n,0n),"RNIL"):un();
  const bPop=()=>{const p=pop(R,false);if(!p)return un();const [d,R1]=p;return d===0n?clean("B",c+1n,S,b,R1,4n,"B_zero"):clean("BR",c,S,b,push0(1n,pushRd(d-1n,R1)),2n,"B_succ");};
  if(mode==="C")return un();
  if(mode==="B"){
   if(!r0)return rnil();
   if(r0[0]==="z"){const cz=r0[1];if(r1?.[0]==="k"&&c===0n&&b>=1n&&cz===1n){const [,r,cnt]=r1,q=min(cnt,b);if(q>=1n)return clean("B",0n,pushSeg(r+3n,q,S),b-q,[Z(1n),...(cnt===q?[]:[K(r,cnt-q)]),...R.slice(2)],p1Pow(q,r,s,b-q),"P1");}return clean("B",c+cz,S,b,R.slice(1),4n*cz,"B_zeros");}
   if(r0[0]==="d"&&r1?.[0]==="d"&&r2?.[0]==="k"&&c===0n&&r0[1]===1n&&r1[1]===1n){const [,r,cnt]=r2,q=min(cnt,b/(r+1n));if(q>=1n)return clean("B",0n,pushSeg(4n*r+3n,q,S),b-q*(r+1n),[D(1n),D(1n),...(cnt===q?[]:[K(r,cnt-q)]),...R.slice(3)],p2Pow(q,r,s,b-q*(r+1n)),"P2");return clean("BR",c,S,b,push0(1n,pushRd(0n,R.slice(1))),2n,"B_succ");}
   return bPop();
  }
  if(mode==="BR"){if(!r0)return rnil();if(r0[0]==="z")return clean("BR",c+r0[1],S,b,R.slice(1),2n*r0[1],"BR_zeros");if(r0[0]==="k"){const [,r,m]=r0;return m>=1n&&c>=1n&&r+c>=3n?clean("BR",3n,pushSeg(r,m-1n,pushSeg(r+c-3n,1n,S)),b,R.slice(1),m*(2n*r+15n),"BR_block"):un();}const p=pop(R,false);if(!p)return un();const [d,R2]=p;if(d===0n)return clean("BR",c+1n,S,b,R2,2n,"BR_zero");if(d===1n)return clean("DR0",c,S,b,bump(R2,false),4n,"BR_one");return c>=3n?clean("B",0n,pushSeg(c-3n,1n,S),b,pushRd(d-2n,R2),5n,"BR_add_two"):un();}
  if(mode==="DR0"){if(b===0n)return un();if(r0?.[0]==="d"&&r0[1]===1n&&r1?.[0]==="z"){const rz=r1[1],q=min(rz,b);if(q>=1n)return clean("DR0",c+4n*q,S,b-q,[D(1n),...(rz===q?[]:[Z(rz-q)]),...R.slice(2)],drZeros(q,c,s,b-q),"DR0_clean_zeros");}return clean("BR",c+4n,S,b-1n,R,drOne(c,s,b-1n),"DR0_clean_one");}
  throw Error("mode "+mode);
 }
 const parseItems=s=>[...s.matchAll(/\.(z|d|k)\s+(\d+)(?:\s+(\d+))?/g)].map(m=>m[1]==="k"?K(BigInt(m[2]),BigInt(m[3])):[m[1],BigInt(m[2])]);
 function parseState(s){const m=s.match(/^\s*⟨\.(\w+),\s*\.(raw|clean)\s+([\s\S]*),\s*(false|true)⟩\s*$/);if(!m)throw Error("parse state");const [_,mode,t,rest,h]=m,arrays=[...rest.matchAll(/\[([^\]]*)\]/g)];if(arrays.length!==2)throw Error("bad arrays");const R=parseItems(arrays[1][1]),halted=h==="true";if(t==="raw")return {mode,L:parseItems(arrays[0][1]),R,halted};const c=BigInt(rest.slice(0,arrays[0].index).trim()),S=[...arrays[0][1].matchAll(/\(\s*(\d+)\s*,\s*(\d+)\s*\)/g)].map(x=>[BigInt(x[1]),BigInt(x[2])]),b=BigInt(rest.slice(arrays[0].index+arrays[0][0].length,arrays[1].index).replace(/[\s,]/g,""));return {mode,c,S,b,R,halted};}
 const str=o=>JSON.stringify(o,(_,v)=>typeof v==="bigint"?v.toString():v);
 const ckpts=new Map([...source.matchAll(/def ckpt(\d+) : RleFullState :=\s*(⟨[\s\S]*?⟩)/g)].map(m=>[Number(m[1]),parseState(m[2])]));
 const chunks=[...source.matchAll(/theorem chunk_\d+ : \(?runBatches (\d+) ckpt(\d+)\)?(?:\s*=\s*ckpt(\d+)|\.halted = true)/g)].map(m=>[Number(m[1]),Number(m[2]),m[3]===undefined?null:Number(m[3])]);
 if(ckpts.size<2||chunks.length!==ckpts.size)throw Error("unexpected checkpoint or chunk count");
 let state=ckpts.get(0),total=1n,steps=0,executed=0;const report=[],branches={};
 for(const [n,from,to] of chunks){if(str(state)!==str(ckpts.get(from)))throw Error("checkpoint start mismatch "+from);let chunkCost=0n;for(let i=0;i<25*n;i++){steps++;if(state.halted)continue;const [s,cost,rule]=Object.hasOwn(state,"L")?rawStep(state):cleanStep(state);if(cost<0n)throw Error("negative cost");state=s;chunkCost+=cost;executed++;branches[rule]=(branches[rule]||0)+1;}total+=chunkCost;if(to===null?!state.halted:str(state)!==str(ckpts.get(to)))throw Error("checkpoint end mismatch "+from+" -> "+to);report.push({from,to,batches:n,chunkCost:chunkCost.toString(),cumulativeOrdinaryMoves:total.toString()});}
 return {table,steps,executed,ordinaryMoves:total.toString(),haltScore:(total+1n).toString(),weightedUpperBound:(total+6n).toString(),report,branches};
}
if (require.main === module) {
 const fs = require("node:fs");
 const path = require("node:path");
 const root = process.argv[2];
 if (!root) throw Error("Usage: node counted-rle.cjs /path/to/cryptids");
 const tables = ["1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH","1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH"];
 console.log(JSON.stringify(tables.map(table => countedRle(fs.readFileSync(path.join(root, "BusyBeaver", "BB6", "Halt", "M_"+table+".lean"), "utf8"), table)), null, 2));
}
module.exports = { countedRle };
