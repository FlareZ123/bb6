const {rule}=require('./generate_raw140_variant_transfer.js');
const specs=[
 ["cMarker","base","","4^p 6 4 0 5 1 Y",3,0,"3^p+8 2","0 Y",0,1,"DL0 AR4^p AR6 EL3^p EL2 BL0 CR1^p+1 CR5 BL6^p+1 BL4 BR2^p+2 BR4 ER0 BL1 CR0 DL5^p+4 DL0 AR4^p+4 AR2 EL3^p+4 EL2 BL0 CR1^p+6 CR5 BL6^p+6 BL4 BR2^p+7 BR1 DL5^p+8 DL0 AR4^p+8"],
 ["bOddFinish","base","3^p 2","0 1 2 3 Y",0,1,"3^p+5 2","2 Y",0,1,"AR0 DR1 EL7 ER1 EL3^p+1 EL2 BL0 CR1^p+2 CR5 BL6^p+2 BL4 BR2^p+4 BR3 DL5^p+5 DL0 AR4^p+5"],
 ["bInit","base","5","2 2 1 Y",1,1,"3^3 2","0 Y",0,1,"BR2^2 BR1 DL5^3 DL0 AR4^3"]
];
console.log('import Raw140VariantTransfer\nnamespace Raw14042MixedExitLocal\nopen BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000');
for(const spec of specs) console.log(rule(...spec));
console.log('end Raw14042MixedExitLocal');
