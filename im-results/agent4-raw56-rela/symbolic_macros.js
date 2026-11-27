// Symbolic finite-macro verifier. Run with Node, or new Function(source)().
const assert=(x,m)=>{if(!x)throw Error(m)};
function machine(t){return t.replaceAll("_","").match(/.../g)}
function run(t,z,k){
 const p=machine(t);
 for(let i=0;i<k;i++){
  const [q,l,r]=z; const a=l[0]||"0";
  assert(a==="0"||a==="1","read variable tail: "+JSON.stringify(z));
  const v=p[2*q+Number(a)]; assert(v!=="---","hole: "+JSON.stringify(z));
  const [w,d,s]=v, q1=s.charCodeAt(0)-65;
  if(d==="L")z=[q1,l.slice(1),w+r];
  else{const b=r[0]||"0"; assert(b==="0"||b==="1","read variable tail: "+JSON.stringify(z));z=[q1,b+w+l.slice(1),r.slice(1)];}
 }
 return z;
}
let checked=0;
function eq(t,k,z,w){assert(JSON.stringify(run(t,z,k))===JSON.stringify(w),t+" "+k+" "+JSON.stringify(z));checked++}
for(const [a,f,l,o] of [["0LF","1LA",4,"1010"],["1LF","0LA",4,"0101"],["1LF","0RD",8,"0101"]]){
 for(const b of ["0LC","0RE","1RB"]){
  const t="1RB"+a+"_1RC"+b+"_0RD1RA_1LD1LE_0LA1RE_---"+f,r=b==="1RB"?4:6;
  eq(t,11,[0,"",""],[0,"1111","0"]);
  eq(t,l,[0,"1111X","Y"],[0,"X",o+"Y"]);
  eq(t,r,[0,"0X","1010Y"],[0,"01111X","Y"]);
  if(a==="0LF"){
   eq(t,r,[0,"","1010Y"],[0,"01111","Y"]);
   eq(t,11,[0,"0X","0"],[0,"1111X","0"]);
  }else{
   eq(t,3,[0,"","010Y"],[0,"0111","Y"]);
   eq(t,b==="1RB"?12:14,[0,"0X","10"],[0,"11111X","0"]);
  }
 }
}
{
const t="1RB1LF_1RC---_0RD0RB_1LD1LE_0LA1RE_0RF0RD";
eq(t,11,[0,"",""],[0,"1111","0"]);
eq(t,8,[0,"1111X","Y"],[0,"X","0101Y"]);
eq(t,2,[0,"","01Y"],[2,"111","Y"]);
eq(t,4,[2,"11X","0101Y"],[2,"110101X","Y"]);
eq(t,9,[2,"11X","010"],[0,"101X","0111"]);
eq(t,8,[0,"1010X","0Y"],[0,"X","01111Y"]);
eq(t,7,[0,"1011","0Y"],[4,"1","1111Y"]);
eq(t,4,[4,"1X","1111Y"],[4,"11111X","Y"]);
eq(t,5,[4,"1X","111"],[0,"1111X","0"]);
}
{
const t="1RB1LC_1RC0RF_0RD0RA_1LD1LE_0LA1RE_1RD---";
eq(t,53,[0,"",""],[0,"11101011","0"]);
eq(t,10,[0,"1110X","Y"],[0,"X","0101Y"]);
eq(t,10,[0,"1011X","Y"],[0,"X","0101Y"]);
eq(t,3,[0,"","010Y"],[0,"0011","Y"]);
eq(t,16,[0,"0011X","1010Y"],[0,"00111011X","Y"]);
eq(t,6,[0,"0011X","10"],[0,"1011X","011"]);
eq(t,8,[0,"0011X","1011"],[0,"11101011X","0"]);
}
if(typeof console!=="undefined")console.log("symbolic identities checked",checked);
if(typeof module!=="undefined")module.exports=checked;
