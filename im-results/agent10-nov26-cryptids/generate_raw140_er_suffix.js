// Generate the exact local Lean certificates. Node.js, no dependencies.
const fs=require("fs"),path=require("path");
function exits(f){
 const t=[7,f===24?24:23,11,12,15,1,6,18,4,17,f,24],e={};
 for(let q=0;q<6;q++)for(let d=0;d<2;d++)for(let a=0;a<8;a++){
  let p=d?0:2,b=a,r=q,k=0;
  while(p>=0&&p<3&&k<145){let c=t[2*r+((b>>p)&1)];if(c===24)break;
   b=(b&~(1<<p))|(((c>>1)&1)<<p);r=c>>2;p+=(c&1)?1:-1;k++}
  if(p<0||p>=3)e[[q,d,a]]=[r,p>=3?1:0,b,k];
 }return e;
}
function add(a,b){return [a[0]+b[0],a[1]+b[1]]}
function count(s){return s===undefined?[0,1]:s.startsWith("p")?[1,s.length===1?0:+s.slice(2)]:[0,+s]}
function ct(c){if(!c[0])return ""+c[1];if(c[0]!==1)throw Error("bad count "+c);return c[1]?"(p+"+c[1]+")":"p"}
function push(S,a,c){if(!S.length&&a===0)return;if(S.length&&Array.isArray(S[0])&&S[0][0]===a){S[0]=[a,add(S[0][1],c)];return}S.unshift([a,c]);}
function parse(s){let S=[];for(let a of s.trim().split(/ +/).filter(Boolean).reverse()){if(a==="X"||a==="Y")S.unshift(a);else{let [b,c]=a.split("^");push(S,+b,count(c))}}return S}
function pop(S,a,c){let A=S.slice();if(!A.length){if(a!==0||c[0]||c[1]!==1)throw Error("bad blank");return A}if(!Array.isArray(A[0])||A[0][0]!==a)throw Error("bad pop "+JSON.stringify({S,a,c}));let d=[A[0][1][0]-c[0],A[0][1][1]-c[1]];if(d.some(x=>x<0))throw Error("negative symbolic");A.shift();if(d[0]||d[1])A.unshift([a,d]);return A}
function fmt(S){if(!S.length)return "[]";if(typeof S[0]==="string"){if(S.length!==1)throw Error("marker internal");return S[0]}let [a,c]=S[0],R=fmt(S.slice(1));if(c[0])return S.length===1?"(U "+a+" "+ct(c)+")":"(U "+a+" "+ct(c)+" ++ "+R+")";return "("+Array(c[1]).fill("S "+a).join(" :: ")+" :: "+R+")"}
function cfg(q,d,L,R){return "boundary "+q+" "+(d?"true":"false")+" "+fmt(L)+" "+fmt(R)}
function rule(name,table,L0,R0,q,d,L1,R1,q1,d1,seq){
 let L=parse(L0),R=parse(R0),start=cfg(q,d,L,R),costs=[],body=[],E=exits(table),M=table===24?"base":table===4?"M4":"M13";
 for(let [i,tok] of seq.trim().split(/ +/).entries()){let [src,n]=tok.split("^"),c=count(n),a=+src[2];if(q!=="ABCDEF".indexOf(src[0])||d!==(src[1]==="R"?1:0))throw Error(name+" state "+tok);let e=E[[q,d,a]];if(!e)throw Error(name+" undefined "+tok);let [r,z,b,k]=e,pre=cfg(q,d,L,R),LL=d?L:pop(L,a,c),RR=d?pop(R,a,c):R,LL1=LL.slice(),RR1=RR.slice();push(z?LL1:RR1,b,c);let post=cfg(r,z,LL1,RR1),lemma,co;
 if(n!==undefined){if(q!==r||d!==z)throw Error("bad sweep");lemma="sweep"+src[1]+" "+M+" "+q+" (S "+a+") (S "+b+") "+k+" "+ct(c)+" "+fmt(LL)+" "+fmt(RR)+" (by rfl)";co="("+ct(c)+"*"+k+")"}else{lemma="step"+src[1]+" "+M+" "+q+" "+r+" "+(z?"true":"false")+" (S "+a+") (S "+b+") "+k+" "+fmt(LL)+" "+fmt(RR)+" (by rfl)";co=""+k}
 body.push("  have h"+i+" : run "+M+" "+co+" ("+pre+") = some ("+post+") := by\n    simpa only [U, List.replicate_succ, List.replicate_zero, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using "+lemma);costs.push(co);L=LL1;R=RR1;q=r;d=z;
 }
 let goal=cfg(q1,d1,parse(L1),parse(R1));if(cfg(q,d,L,R)!==goal)throw Error(name+" got "+cfg(q,d,L,R)+" expected "+goal);
 let vars=(seq.includes("^p")?" (p : Nat)":"")+([L0,R0].join(" ").includes("X")?" (X : List Sym)":"")+([L0,R0].join(" ").includes("Y")?" (Y : List Sym)":"");
 let sum=costs.join("+"),expr="h0";for(let i=1;i<costs.length;i++)expr="(join "+expr+" h"+i+")";
 return "theorem "+name+vars+" : run "+M+" ("+sum+") ("+start+") = some ("+goal+") := by\n"+body.join("\n")+"\n  exact "+expr+"\n";
}
const rules=[["prep542",24,"1 X","5 4 2",4,1,"3 3 X","5 2",4,0,"ER5 ER4 BL1 CR4 DL5 DL1 AR4 AR6"],["prep152",24,"1 X","1 5 2",4,1,"3 3 X","1 2 1",4,0,"ER1 EL1 DR5 EL7 ER5 ER5 ER2 BL1 CR2 DR0 BL6 BL5 DL1 AR2"],["prep1121",24,"1 X","1 1 2 1",4,1,"3 X","5 2 1 5",4,0,"ER1 EL1 DR5 EL7 ER5 ER1 EL1 DR5 EL7 ER5 ER2 BL1 CR2 DR1 EL6 ER1 EL2 BL5 DL3"],["prep5215",24,"1 X","5 2 1 5",4,1,"3 X","1 1 5 5",4,0,"ER5 ER2 BL1 CR2 DR1 EL6 ER1 EL2 BL5 DL1 AR2"],["prep1155",24,"1 X","1 1 5 5",4,1,"3 3 3 X","5 1 1",4,0,"ER1 EL1 DR5 EL7 ER5 ER1 EL1 DR5 EL7 ER5 ER5 ER5 ER0 BL1 CR0 DL5 DL1 AR4 AR2 EL3 EL3 EL1 DR1 EL7 ER1"],["prep11511",24,"1 X","1 1 5 1 1",4,1,"3 3 3 X","5 5 4 2",4,0,"ER1 EL1 DR5 EL7 ER5 ER1 EL1 DR5 EL7 ER5 ER5 ER1 EL1 DR5 EL7 ER5 ER1 EL1 DR5 EL7 ER5 ER0 BL1 CR0 DL5 DL3 EL3 EL1 DR1 EL7 ER1"]];
rules.push(["tripLoop",24,"3 3 3 1 3 3 X","1 Y",4,1,"3 3 3 X","1 1 1 5 Y",4,1,"ER1 EL3^3 EL1 DR1 EL7"]);
rules.push(["finishBank",24,"3^p+3 2","1 1 1 5 Y",4,1,"3^p+11 2","Y",0,1,"ER1 EL3^p+3 EL2 BL0 CR1^p+4 CR5 BL6^p+4 BL4 BR2^p+5 BR1 DL5^p+6 DL0 AR4^p+6 AR0 DR1 EL7 ER1 EL3^p+7 EL2 BL0 CR1^p+8 CR5 BL6^p+8 BL4 BR2^p+9 BR5 DL5^p+10 DL0 AR4^p+11"]);
rules.push(["finish42",24,"3^3 2 5 3^p+1 2","1 1 1 5 Y",4,1,"3^p+13 2","1 1 5 Y",0,1,"ER1 EL3^3 EL2 BL5 DL3 EL3^p EL2 BL0 CR1^p+1 CR5 BL6^p+1 BL4 BR2^p+3 BR1 DL5^p+4 DL0 AR4^p+4 AR0 DR1 EL7 ER1 EL3^p+5 EL2 BL0 CR1^p+6 CR5 BL6^p+6 BL4 BR2^p+7 BR1 DL5^p+8 DL0 AR4^p+8 AR0 DR1 EL7 ER1 EL3^p+9 EL2 BL0 CR1^p+10 CR5 BL6^p+10 BL4 BR2^p+11 BR5 DL5^p+12 DL0 AR4^p+13"]);
const output='import Raw140ExtraCore\nnamespace Raw140ERSuffixLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra\nset_option maxRecDepth 4096\nset_option maxHeartbeats 1000000\n'+rules.map(x=>rule(...x)).join('\n')+'\nend Raw140ERSuffixLocal\n';
fs.writeFileSync(path.join(__dirname,"Raw140ERSuffixLocal.lean"),output);
