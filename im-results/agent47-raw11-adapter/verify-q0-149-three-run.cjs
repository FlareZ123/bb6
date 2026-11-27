"use strict";
// Exact local symbolic verifier; the unbounded induction is in q0-149-three-run-proof.md.
const tables=[
  "1RB1LC_1RC0LF_0LA0RD_1RA1RE_1LF1RD_---0LB",
  "1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1LC0LF",
  "1RB1LC_1RC---_0LA0RD_1RA1RE_1LF1RD_1RC0LF"
];
const rules=[
  [
    "enter",
    "A 1X 0Y",
    "C X 10Y",
    1,
    1,
    1
  ],
  [
    "sweep",
    "C 1X 10Y",
    "C X 101Y",
    7,
    5,
    7
  ],
  [
    "cross",
    "C 0X Y",
    "A X 0Y",
    1,
    1,
    1
  ],
  [
    "prep",
    "C 00X 101Y",
    "D 10011X Y",
    7,
    7,
    7
  ],
  [
    "dpair",
    "D 1X 11Y",
    "D 111X Y",
    2,
    2,
    2
  ],
  [
    "evenEnd",
    "D 1X 10Y",
    "D 011X Y",
    2,
    2,
    2
  ],
  [
    "oddEnd",
    "D 1X 0Y",
    "E 01X Y",
    1,
    1,
    1
  ],
  [
    "e0",
    "E 0X Y",
    "F X 1Y",
    1,
    1,
    1
  ],
  [
    "fpair",
    "F 11X Y",
    "F X 00Y",
    2,
    2,
    2
  ],
  [
    "fstop2",
    "F 100X Y",
    "A X 010Y",
    5,
    3,
    5
  ],
  [
    "fstop1",
    "F 10X Y",
    "C X 10Y",
    4,
    2,
    4
  ],
  [
    "d000",
    "D 0X 000Y",
    "A 111X 0Y",
    4,
    4,
    4
  ],
  [
    "d1",
    "D 0X 1Y",
    "A 11X Y",
    1,
    1,
    1
  ],
  [
    "d001",
    "D 0X 001Y",
    "C 1111X Y",
    3,
    3,
    3
  ],
  [
    "c1z",
    "C 1X 0Y",
    "D 00X Y",
    1,
    1,
    1
  ],
  [
    "c1o",
    "C 1X 1Y",
    "D 10X Y",
    1,
    1,
    1
  ],
  [
    "special",
    "D 0X 111110Y",
    "F 111110X 1Y",
    9,
    9,
    9
  ]
];
function verify(tables,rules,report){
const assert=(c,msg)=>{if(!c)throw Error(msg)};
const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const trim=s=>s.replace(/0+$/,""),norm=z=>[z[0],trim(z[1]),trim(z[2])];
const U=n=>"1".repeat(n), Z=n=>"0".repeat(n);
const T=(x,y)=>["A",U(y)+"00"+U(x),""],S=(x,b,w)=>["C","00"+U(x),"10"+U(b)+w];
const byName=Object.fromEntries(rules.map(([name,src,dst,...ns])=>[name,[src.split(" "),dst.split(" "),ns]]));
function step(t,[q,l,r],symbolic){
 if(!symbolic){l=l||"0";r=r||"0";}
 assert(/^[01]/.test(l),"unknown left");let s=t[2*(q.charCodeAt(0)-65)+Number(l[0])];assert(s!=="---","hole");
 if(s[1]==="L")return[s[2],l.slice(1),s[0]+r];
 assert(/^[01]/.test(r),"unknown right");return[s[2],r[0]+s[0]+l.slice(1),r.slice(1)];
}
for(let j=0;j<tables.length;j++){
 const t=tables[j].replaceAll("_","").match(/.{3}/g);
 for(const [name,[src,dst,ns]] of Object.entries(byName)){let z=src;for(let i=0;i<ns[j];i++)z=step(t,z,true);assert(eq(z,dst),"symbolic "+name+" "+j);}
 let z=["A","",""],seed=[43,37,43][j];for(let i=0;i<seed;i++)z=norm(step(t,z,false));assert(eq(norm(z),T(2,4)),"seed");
 let cost=0;
 function apply(name){
  const [src,dst,ns]=byName[name];assert(z[0]===src[0],"state "+name);
  const subst={};
  for(let i=1;i<=2;i++){const mark=src[i].at(-1),pre=src[i].slice(0,-1),w=z[i].padEnd(Math.max(z[i].length,pre.length),"0");assert(w.startsWith(pre),"prefix "+name+" "+JSON.stringify(z));subst[mark]=w.slice(pre.length);}
  z=norm([dst[0],...dst.slice(1).map(w=>w.slice(0,-1)+subst[w.at(-1)])]);cost+=ns[j];
 }
 function rep(name,n){assert(Number.isSafeInteger(n)&&n>=0,"bad exponent");for(let i=0;i<n;i++)apply(name);}
 function expect(w){assert(eq(norm(z),norm(w)),JSON.stringify({z,w,j}));}
 function left(n){apply("enter");rep("sweep",n-1);}
 function odd(x,b,u){assert(b%2===1,"odd");expect(S(x,b,"0"+u));apply("prep");rep("dpair",(b-1)/2);apply("oddEnd");apply("e0");rep("fpair",(b-1)/2);apply("fstop2");left(x+2);expect(S(0,x+2,Z(b)+"1"+u));}
 function even(x,b,u){assert(b>0&&b%2===0,"even");expect(S(x,b,"0"+u));apply("prep");rep("dpair",b/2-1);apply("evenEnd");}
 function reduce(x,b,c,d,n){for(let i=0;i<n;i++){assert(c>=4,"reduce");even(x,b,Z(c-1)+U(d));apply("d000");left(b+3);x+=2;b+=2;c-=4;expect(S(x,b,Z(c)+U(d)));}}
 function end(x,b){even(x,b,"1");apply("d1");expect(T(x+2,b+2));}
 function turn3(x,b,d){even(x,b,"00"+U(d));apply("d001");if(d===1){apply("c1z");}else{assert(d%2===1,"odd marker");apply("c1o");rep("dpair",(d-3)/2);apply("evenEnd");}apply("d000");left(d+2);apply("cross");left(b+3);expect(S(x+2,b+3,"0"+U(d+1)));}
 function turn5(x,b){even(x,b,U(5));apply("special");rep("fpair",2);apply("fstop1");rep("sweep",b);expect(S(x+2,b,"00001"));}
 function exceptional(x){assert(x%2===0,"exceptional");turn3(x,2*x+4,1);odd(x+2,2*x+7,U(2));reduce(0,x+4,2*x+7,3,x/2+1);turn3(x+2,2*x+6,3);odd(x+4,2*x+9,U(4));reduce(0,x+6,2*x+9,5,x/2+2);turn5(x+4,2*x+10);reduce(x+6,2*x+10,4,1,1);odd(x+8,2*x+13,"");reduce(0,x+10,2*x+13,1,x/2+3);end(x+6,2*x+16);expect(T(x+8,2*x+18));}
 for(let k=0;k<12;k++){if(k>0){expect(T(8*k,16*k+2));left(16*k+2);odd(8*k,16*k+1,"");reduce(0,8*k+2,16*k+1,1,4*k);end(8*k,16*k+2);}expect(T(8*k+2,16*k+4));left(16*k+4);odd(8*k+2,16*k+3,"");reduce(0,8*k+4,16*k+3,1,4*k);exceptional(8*k);}
 report(`machine ${[11,16,17][j]}: ${rules.length} exact symbolic local identities, seed ${seed}, 12 composed cycles, ${cost} primitive steps`);
}
}
if(require.main===module)verify(tables,rules,console.log);
module.exports={tables,rules,verify};
