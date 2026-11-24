"use strict";
// Independently generate seven-parent exact trie and candidate SideCycle data.
// Run node replay_seven.cjs > seven-side-data.lean
const PATHS = {
  "pilot": [
    [
      1,
      "B0",
      "1RC"
    ],
    [
      2,
      "C0",
      "0RD"
    ],
    [
      3,
      "D0",
      "1LD"
    ],
    [
      5,
      "D1",
      "1RE"
    ],
    [
      6,
      "E1",
      "0LB"
    ],
    [
      7,
      "B1",
      "1LF"
    ],
    [
      8,
      "F1",
      "0LA"
    ],
    [
      11,
      "C1",
      "0RB"
    ],
    [
      21,
      "F0",
      "0LE"
    ]
  ],
  "r1": [
    [
      1,
      "B0",
      "1LC"
    ],
    [
      2,
      "C1",
      "0LD"
    ],
    [
      3,
      "D0",
      "1LC"
    ],
    [
      4,
      "C0",
      "0LE"
    ],
    [
      5,
      "E0",
      "0RA"
    ],
    [
      7,
      "B1",
      "0RB"
    ],
    [
      10,
      "E1",
      "1LF"
    ],
    [
      11,
      "F0",
      "1LA"
    ],
    [
      49,
      "A1",
      "0LC"
    ]
  ],
  "r2": [
    [
      1,
      "B0",
      "0RC"
    ],
    [
      2,
      "C0",
      "1LA"
    ],
    [
      4,
      "B1",
      "0LD"
    ],
    [
      5,
      "D1",
      "1LD"
    ],
    [
      7,
      "D0",
      "1LE"
    ],
    [
      8,
      "E0",
      "1LB"
    ],
    [
      10,
      "C1",
      "1RF"
    ],
    [
      11,
      "F1",
      "1RA"
    ],
    [
      12,
      "A1",
      "0RA"
    ]
  ],
  "r3": [
    [
      1,
      "B0",
      "0RC"
    ],
    [
      2,
      "C0",
      "1LD"
    ],
    [
      3,
      "D0",
      "1LB"
    ],
    [
      4,
      "B1",
      "0LE"
    ],
    [
      5,
      "E0",
      "1LD"
    ],
    [
      8,
      "C1",
      "1RF"
    ],
    [
      9,
      "F1",
      "1RA"
    ],
    [
      12,
      "E1",
      "1LE"
    ],
    [
      20,
      "A1",
      "0RA"
    ]
  ],
  "r4": [
    [
      1,
      "B0",
      "1RC"
    ],
    [
      2,
      "C0",
      "0LD"
    ],
    [
      3,
      "D1",
      "1LE"
    ],
    [
      4,
      "E1",
      "0LB"
    ],
    [
      8,
      "E0",
      "1LD"
    ],
    [
      9,
      "D0",
      "1RA"
    ],
    [
      10,
      "A1",
      "0RA"
    ],
    [
      13,
      "B1",
      "0LC"
    ],
    [
      14,
      "C1",
      "1RF"
    ]
  ],
  "r5": [
    [
      1,
      "B0",
      "0LC"
    ],
    [
      2,
      "C1",
      "1LD"
    ],
    [
      3,
      "D0",
      "0LB"
    ],
    [
      5,
      "C0",
      "1RC"
    ],
    [
      9,
      "D1",
      "1LE"
    ],
    [
      10,
      "E1",
      "0RC"
    ],
    [
      13,
      "B1",
      "0RA"
    ],
    [
      16,
      "A1",
      "1RA"
    ],
    [
      21,
      "E0",
      "1LF"
    ]
  ],
  "r6": [
    [
      1,
      "B0",
      "1RC"
    ],
    [
      2,
      "C0",
      "0LD"
    ],
    [
      3,
      "D1",
      "1LE"
    ],
    [
      4,
      "E1",
      "1LF"
    ],
    [
      5,
      "F0",
      "1LC"
    ],
    [
      7,
      "D0",
      "1RF"
    ],
    [
      9,
      "C1",
      "0RA"
    ],
    [
      10,
      "A1",
      "1RA"
    ],
    [
      19,
      "F1",
      "0LF"
    ]
  ]
};
function generate(PATHS) {
 const MOVES=[..."ABCDEF"].flatMap(q=>[..."01"].flatMap(b=>[..."LR"].map(d=>b+d+q)));
 const SLOTS=[..."ABCDEF"].flatMap(q=>[..."01"].map(b=>q+b));
 function assert(x,msg){if(!x)throw new Error(msg)}
 function encode(t){return SLOTS.map(s=>t[s]??"---").join("")}
 function firstHole(t,cap=1000){let q="A",h=0,ones=new Set();for(let n=0;n<=cap;n++){const s=q+Number(ones.has(h)),mv=t[s];if(!mv)return [n,s];if(mv[0]==="1")ones.add(h);else ones.delete(h);h+=mv[1]==="R"?1:-1;q=mv[2]}return null}
 const prefix=new Map(), terminal=new Set();
 for(const [name,path] of Object.entries(PATHS)){
  let a=[],t={A0:"1RB"};
  for(const [n,s,mv] of path){
   assert(JSON.stringify(firstHole(t))===JSON.stringify([n,s]),"bad first hole "+name+" "+n);
   const k=a.join("/"),old=prefix.get(k);
   if(old)assert(old.n===n&&old.s===s&&encode(old.t)===encode(t),"prefix mismatch");
   else prefix.set(k,{n,s,t:{...t}});
   t[s]=mv;a.push(mv);
  }
  const k=a.join("/");assert(!terminal.has(k),"duplicate terminal");terminal.add(k);
 }
 const residual=[];
 function visit(a,t){const k=a.join("/");if(terminal.has(k))return;const p=prefix.get(k);if(!p){residual.push({address:a,table:t});return}assert(encode(p.t)===encode(t),"bad trie table");for(const mv of MOVES)visit([...a,mv],{...t,[p.s]:mv})}
 visit([],{A0:"1RB"});assert(residual.length===1+23*prefix.size-terminal.size,"leaf count");
 function same(a,b){return a.size===b.size&&[...a].every(x=>b.has(x))}
 function findCycle(t,cap=300){
  let q="A",h=0,ones=new Set(),history=[];
  for(let n=0;n<=cap;n++){
   let lo=h,hi=h;
   for(let i=n-1;i>=0;i--){const c=history[i];lo=Math.min(lo,c.h);hi=Math.max(hi,c.h);if(c.q!==q)continue;const d=h-c.h;
    if(d>=0&&same(new Set([...c.ones].filter(x=>x>=lo).map(x=>x+d)),new Set([...ones].filter(y=>y-d>=lo))))return [i,n-i,true,lo];
    if(d<=0&&same(new Set([...c.ones].filter(x=>x<=hi).map(x=>x+d)),new Set([...ones].filter(y=>y-d<=hi))))return [i,n-i,false,hi];
   }
   history.push({q,h,ones:new Set(ones)});
   const mv=t[q+Number(ones.has(h))];if(!mv)return null;
   if(mv[0]==="1")ones.add(h);else ones.delete(h);h+=mv[1]==="R"?1:-1;q=mv[2];
  }return null;
 }
 const witnesses=residual.flatMap(({table})=>{const w=findCycle(table);return w?[{rows:SLOTS.map(s=>table[s]?MOVES.indexOf(table[s])+1:0),w}]:[]});
 const chunks=[];for(let i=0;i<witnesses.length;i+=12)chunks.push(witnesses.slice(i,i+12));
 let data="";
 for(let i=0;i<chunks.length;i++){
  data+=`def chunk${i} : List SideWitness := [\n`;
  data+=chunks[i].map(({rows,w})=>`  ⟨[${rows.join(", ")}],${w[0]},${w[1]},${w[2]},(${w[3]})⟩`).join(",\n");
  data+=`\n]\ntheorem chunk${i}_checked : chunk${i}.all SideWitness.check = true := by decide\n\n`;
 }
 data+="def witnesses : List SideWitness := "+chunks.map((_,i)=>`chunk${i}`).join(" ++ ")+"\n";
 data+="theorem witnesses_checked : witnesses.all SideWitness.check = true := by\n  simp only [witnesses,List.all_append,"+chunks.map((_,i)=>`chunk${i}_checked`).join(",")+",Bool.true_and]\n";
 return {data,witnesses,residual,prefix:prefix.size,terminal:terminal.size};
}
const out=generate(PATHS);
console.error(JSON.stringify({prefix:out.prefix,terminal:out.terminal,residual:out.residual.length,witnesses:out.witnesses.length}));
process.stdout.write(out.data);
