"use strict";
const rows=[
["11","01","1","0101"],
["1","01","0","010001"],
["0","01","101","01"],
["11","010001","1","01010001"],
["101","01010001","0","0110001010001"],
["0","0110001010001","101100101","01001"],
["101","01001","0","0110001001"],
["0","0110001001","01100101","1001"]
];
const parse=s=>BigInt("0b"+[...s].reverse().join(""));
const near=x=>[...x.toString(2)].reverse().join("");
const run1=x=>{const t=x+1n;return (t&-t).toString(2).length-1};
function next(l,r){let a=run1(l),phase="B";
 if(a%2===0){l=(l>>BigInt(a+1)<<2n)|2n;r<<=BigInt(a);phase="D"}
 else{l>>=BigInt(a+1);r<<=BigInt(a+1);let k=run1(l);l>>=BigInt(k+1);r=(r<<BigInt(k+1))|((1n<<BigInt(k+1))-1n);if(l&1n){l=(l>>1n<<2n)|2n;phase="D"}else{l>>=1n;r<<=1n}}
 if(phase==="B")return{l,r};
 for(;;){const x=Number(r&15n);
 if((x&7)===7){l=(l<<3n)|2n;r>>=3n;continue}
 if(!(x&1)){if(x&2){l=(l<<2n)|2n;r>>=2n;continue}return{l:l>>1n,r:((r>>2n)<<2n)|2n}}
 if(x&2){l=(l<<3n)|10n;r>>=3n;continue}
 if(x&4){if(x&8){l=(l<<4n)|10n;r>>=4n;continue}return{l:(l<<1n)|1n,r:((r>>4n)<<2n)|2n}}
 if(x&8)return{halt:true,l,r};
 l=(l<<4n)|6n;r>>=4n;
 }
}
const L=new Set(["11"]),R=new Set(["01"]);
for(let i=0;i<rows.length;i++){const [l,r,a,b]=rows[i];if(!L.has(l)||!R.has(r))throw Error("nonproduct premise "+i);const z=next(parse(l),parse(r));if(near(z.l)!==a||near(z.r)!==b||!!z.halt!==(i===rows.length-1))throw Error("incorrect row "+i);L.add(a);R.add(b)}
console.log("All 8 exact section rows checked; last is fatal in product closure, not actual orbit.");
module.exports=next;
