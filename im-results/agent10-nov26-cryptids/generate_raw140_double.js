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
 body.push("  have h"+i+" : run "+M+" "+co+" ("+pre+") = some ("+post+") := by\n    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using "+lemma);costs.push(co);L=LL1;R=RR1;q=r;d=z;
 }
 let goal=cfg(q1,d1,parse(L1),parse(R1));if(cfg(q,d,L,R)!==goal)throw Error(name+" got "+cfg(q,d,L,R)+" expected "+goal);
 let vars=(seq.includes("^p")?" (p : Nat)":"")+([L0,R0].join(" ").includes("X")?" (X : List Sym)":"")+([L0,R0].join(" ").includes("Y")?" (Y : List Sym)":"");
 let sum=costs.join("+"),expr="h0";for(let i=1;i<costs.length;i++)expr="(join "+expr+" h"+i+")";
 return "theorem "+name+vars+" : run "+M+" ("+sum+") ("+start+") = some ("+goal+") := by\n"+body.join("\n")+"\n  exact "+expr+"\n";
}
const rules=[];
function a(...xs){rules.push(rule(...xs))}
for(let b of [4,6]){
 a("forward4_"+b,24,"4 X","4 "+b+" Y",2,1,"4 5 X",b+" Y",2,1,"CR4 DL4 ER6 BL1 CR6 ER"+b+" BL0");
 a("forward6_"+b,24,"4 X","6 "+b+" Y",2,1,"4 4 X",b+" Y",2,1,"CR6 ER"+b+" BL0");
 a("lift_"+b,24,"6 X",b+" Y",3,0,"4 X",b+" Y",2,1,"DL6 ER"+b+" BL0");
}
a("reverse4",24,"5 5 X","Y",3,0,"5 X","4 Y",3,0,"DL5");
a("reverse6",24,"5 4 X","Y",3,0,"5 X","6 Y",3,0,"DL5 DL4 ER4 BL1 CR4");
const ss=["62","64","6221","6421","6405","62542"],ds=["64","6221","6421","6405","62542","64462"],ps=[
"CR6 ER2 BL0 CR2 DR0 BL6 BL4 BR2 BR1 DL5 DL5 DL4 ER4 BL1 CR4",
"CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER0 BL0 CR0 DL4 ER2 BL1 CR2 DR0 BL6 BL5 DL5 DL4 ER4 BL1 CR4",
"CR6 ER2 BL0 CR2 DR2 BL6 BL4 BR2 BR3 DL5 DL5 DL4 ER4 BL1 CR4",
"CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER2 BL0 CR2 DR1 EL6 ER1 EL2 BL4 BR1 DL5 DL5 DL4 ER4 BL1 CR4",
"CR6 ER4 BL0 CR4 DL4 ER6 BL1 CR6 ER0 BL0 CR0 DL4 ER2 BL1 CR2 DR5 EL6 ER5 ER0 BL1 CR0 DL5 DL2 BL5 DL5 DL4 ER4 BL1 CR4",
"CR6 ER2 BL0 CR2 DR5 EL6 ER5 ER4 BL1 CR4 DL5 DL2 BL4 BR5 DL5 DL4 ER4 BL1 CR4"];
for(let i=0;i<ss.length;i++)a("tail"+ss[i],24,"4 X",ss[i].split("").join(" "),2,1,"5 X",ds[i].split("").join(" "),3,0,ps[i]);
a("dEnd",24,"4","4 Y",3,0,"","4 6 Y",3,0,"DL4 ER4 BL1 CR4 DL5");
a("eTwo",24,"5 X","4 4 Y",1,1,"5 5 X","6 Y",3,0,"BR4 ER4 BL1 CR4");
a("eOne",24,"5 X","4 6 4 Y",1,1,"4 5 5 X","4 Y",2,1,"BR4 ER6 BL1 CR6 ER4 BL0");
a("f13start",24,"X","6 4 Y",2,1,"4 X","4 Y",2,1,"CR6 ER4 BL0");
a("cr4turn",24,"X","4 Y",2,1,"X","6 Y",3,0,"CR4");
a("reset4",4,"5 X","6 4 4 Y",1,1,"5 X","2 4 4 Y",3,0,"BR6 FR4 BL5");
a("reset13",13,"5 X","6 4 4 6 Y",1,1,"5 5 5 X","2 6 Y",3,0,"BR6 FR4 FR4 FR6 BL5");
a("convert1",24,"5^p","2 Y",3,0,"6^p+2 4","Y",2,1,"DL5^p DL0 AR4^p AR2 EL3^p EL2 BL0 CR1^p+2");
a("convert2",24,"","4^p 6 Y",3,0,"5^p+3","Y",1,1,"DL0 AR4^p AR6 EL3^p EL2 BL0 CR1^p+1 CR5 BL6^p+1 BL4 BR2^p+2");
const output="import Raw140ExtraCore\nnamespace Raw140Double\nopen BB6BlockFAR Raw140Orbit Raw140Extra\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ndef M4 : Table := fill (some ⟨true,true,5⟩) (some ⟨false,false,1⟩)\ndef M13 : Table := fill (some ⟨true,true,5⟩) (some ⟨false,true,3⟩)\n"+rules.join("\n")+"\n#print axioms convert1\n#print axioms convert2\n#print axioms tail6405\nend Raw140Double\n";
fs.writeFileSync(path.join(__dirname,"Raw140DoubleLocal.lean"),output);
