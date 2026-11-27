// Discover a finite affine path with two concrete exponents, then certify
// every symbolic stack operation using rule() (not numerical extrapolation).
const fs=require("fs"),path=require("path");
const {rule,exits}=require("./generate_raw140_variant_transfer.js");
function instantiate(w,p) {
  return w.trim().split(/ +/).filter(Boolean).map(tok=>{
    if(tok==="X")return "8";if(tok==="Y")return "9";
    const [b,n]=tok.split("^");
    const k=n===undefined?1:n.startsWith("p")?p+(n.length===1?0:+n.slice(2)):+n;
    return b.repeat(k);
  }).join("");
}
function find(table,L0,R0,q0,d0,L1,R1,q1,d1,p){
  let q=q0,d=d0,L=instantiate(L0,p),R=instantiate(R0,p);
  const l=instantiate(L1,p),r=instantiate(R1,p),E=exits(table),seq=[];
  let cost=0;
  for(let i=0;i<10000;i++){
    if(q===q1&&d===d1&&L===l&&R===r)return {seq,cost};
    const S=d?R:L,a=+(S[0]||0);
    if(a>=8)throw Error("opaque context read");
    const e=E[[q,d,a]];if(!e)throw Error("undefined");
    let m=1;
    if(e[0]===q&&e[1]===d&&S.length)while(S[m]===S[0])m++;
    if(d)R=R.slice(m);else L=L.slice(m);
    seq.push(["ABCDEF"[q]+(d?"R":"L")+a,m]);
    const [n,z,b,k]=e;q=n;d=z;cost+=m*k;
    const v=String(b).repeat(m);
    if(d){if(L||b)L=v+L}else if(R||b)R=v+R;
  }
  throw Error("no endpoint");
}
function derive(name,table,...args){
  const a=find(table,...args,20),b=find(table,...args,21);
  if(a.seq.length!==b.seq.length)throw Error(name+" path lengths");
  const seq=a.seq.map(([s,m],i)=>{
    const [t,n]=b.seq[i];
    if(s!==t||n-m<0||n-m>1)throw Error(name+" differing path");
    if(n===m)return s+(m===1?"":"^"+m);
    if(m<20)throw Error(name+" negative affine count");
    return s+"^p"+(m===20?"":"+"+(m-20));
  }).join(" ");
  console.log(name,"cost",(b.cost-a.cost)+"p+"+(a.cost-20*(b.cost-a.cost)));
  return rule(name,table,...args,seq);
}
const specs=[
  [
    "oddInit",
    "base",
    "3^p+1",
    "1 Y",
    4,
    1,
    "2",
    "1^p+1 5 Y",
    4,
    1
  ],
  [
    "oddStart",
    "base",
    "2",
    "1 1 Y",
    4,
    1,
    "3^3 2",
    "0 Y",
    0,
    1
  ],
  [
    "oddPump",
    "base",
    "3^p 2",
    "0 1 1 Y",
    0,
    1,
    "3^p+4 2",
    "0 Y",
    0,
    1
  ],
  [
    "oddFinish",
    "base",
    "3^p 2",
    "0 1 5 Y",
    0,
    1,
    "3^p+5 2",
    "Y",
    0,
    1
  ],
  [
    "erTwo",
    "base",
    "3^p 2",
    "1 1 Y",
    4,
    1,
    "3^p+3 2",
    "0 Y",
    0,
    1
  ],
  [
    "erOne",
    "base",
    "3^p 2",
    "1 Y",
    4,
    1,
    "5^p+3",
    "Y",
    1,
    1
  ],
  [
    "bOne",
    "base",
    "5^p",
    "1 Y",
    1,
    1,
    "3^p 2",
    "0 Y",
    0,
    1
  ],
  [
    "ar055",
    "base",
    "3^p 2",
    "0 5 5 Y",
    0,
    1,
    "1 1 3^p+1 2",
    "Y",
    4,
    1
  ],
  [
    "ar05",
    "base",
    "3^p 2",
    "0 5 Y",
    0,
    1,
    "1 3^p+1 2",
    "Y",
    4,
    1
  ]
];
let out="import Raw140VariantTransfer\nnamespace Raw14042DExitAffine\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n";
out+=specs.map(x=>derive(...x)).join("\n")+"\n"+specs.map(x=>"#print axioms "+x[0]).join("\n")+"\nend Raw14042DExitAffine\n";
fs.writeFileSync(path.join(__dirname,"Raw14042DExitAffine.lean"),out);
