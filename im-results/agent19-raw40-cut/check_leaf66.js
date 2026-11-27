// Literal blank entry; no acceleration, no missing transition allowed.
const table="1RB0LA_1RC0RE_0RD1LC_1LD1LA_---0RF_1RA1RF";
const rows=table.split("_"), ones=new Set();
let q=0,h=0;
for(let t=0;t<93860;t++){
 const s=rows[q].slice(ones.has(h)?3:0,ones.has(h)?6:3);
 if(s==="---")throw Error("hole at "+t);
 if(s[0]==="1")ones.add(h);else ones.delete(h);
 h+=s[1]==="R"?1:-1;q=s.charCodeAt(2)-65;
}
const want=new Set();
for(let i=1;i<=11;i++)want.add(h-2*i);
for(let i=1;i<=63;i++)want.add(h+i);
if(q!==0||h!==10||ones.size!==want.size||[...want].some(x=>!ones.has(x)))throw Error("wrong entry");
console.log("PASS: 93860 assigned moves, A0, head 10, left (01)^11, right 1^63");
