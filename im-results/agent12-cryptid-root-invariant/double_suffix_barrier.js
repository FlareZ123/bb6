// Reproduce the 19,656 source-transcription endpoint/cost comparisons.
// No inferred affine acceleration. Run: node double_suffix_barrier.js
const m=require("./affine_stack_replay.js")();
const cost=(blocks,d=0)=>{
  let t=0n;
  for(const b of blocks){
    if(b==="0"){t+=2n;d=0}
    else if(b==="10"){t+=5n;d=1}
    else if(b==="1100"){t+=46n+6n*BigInt(d);d=1}
    else throw Error("invalid block");
  }
  return t+43n+6n*BigInt(d);
};
const run=s=>{
  let t=0n;
  for(let i=0;i<10000;i++){
    let a=m.advance(s);s=a.s;t+=a.cost;
    if(a.halt)return t;
  }
  throw Error("timeout");
};
function check(got,want,context){
  if(got!==want)throw Error(JSON.stringify({...context,got:String(got),want:String(want)}));
}
let counts={CR:0,tCR:0,G:0};
const grammar=["0","10","1100"];
let words=[[]];
for(let i=0;i<5;i++)words=words.concat(words.filter(x=>x.length===i).flatMap(x=>grammar.map(b=>[...x,b])));
for(const blocks of words){
  let P=blocks.join("").split("").map(Number);
  for(let d of [0,1])for(let a of [2,3,4,17])for(let L of [[],[0,2,1],[1,1,999]]){
    let s={q:"CR",L:m.rle([...P,1,1,1,...L]),R:m.rle([...Array(d).fill(0),a,0,1,9]),K:[]};
    check(run(s),cost(blocks,d),{blocks,d,a,L});counts.CR++;
  }
  for(let d of [0,1])for(let a of [3,4,17])for(let L of [[],[0,2,1],[1,1,999]]){
    let s={q:"tCR",L:m.rle([...P,1,1,1,...L]),K:m.rle([...Array(d).fill(1),a,0,1,9]),R:m.rle([5,0,4])};
    check(run(s),cost(blocks,d),{blocks,d,a,L});counts.tCR++;
  }
  for(let M of [1,5,29])for(let w of ["","0","1","00110101"]){
    let U=w+"111"+P.slice().reverse().join("");
    let s={q:"CR",L:m.rle([0]),R:m.rle([...Array(M).fill(0),...U.split("").map(Number)]),K:[]};
    let want=2n*BigInt(M)+26n+U.split("").reduce((x,b)=>x+(b==="1"?7n:2n),0n)+cost(blocks);
    check(run(s),want,{blocks,M,w});counts.G++;
  }
}
console.log(JSON.stringify({words:words.length,counts}));
