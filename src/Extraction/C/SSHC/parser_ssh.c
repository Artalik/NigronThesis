#include "SSH.h"
DEFINE_PAIR(09, SSHPacket, 04, span);
//DEFINE_OPTION(span);
int local1(span *bin, SSHPacket *var597) {
  uint64_t var29 = bin->length;
  span var30;
  if (1 <= var29) {
    span var31;
    take(bin, 1, &var31);
    var30 = var31;
  } else {
    return 0;
  }
  uint8_t var32;
  var32 = var30.pos[0];
  SSHPacket var33;
  switch (var32) {

  case 31: {
    uint64_t var34 = bin->length;
    span var35;
    if (1 <= var34) {
      span var36;
      take(bin, 1, &var36);
      var35 = var36;
    } else {
      return 0;
    }
    uint8_t var37;
    var37 = var35.pos[0];
    uint64_t var38 = bin->length;
    span var39;
    if (1 <= var38) {
      span var40;
      take(bin, 1, &var40);
      var39 = var40;
    } else {
      return 0;
    }
    uint8_t var41;
    var41 = var39.pos[0];
    uint16_t var42 = ((((uint16_t)var37) << 8) | (var41));
    uint64_t var43 = bin->length;
    span var44;
    if (1 <= var43) {
      span var45;
      take(bin, 1, &var45);
      var44 = var45;
    } else {
      return 0;
    }
    uint8_t var46;
    var46 = var44.pos[0];
    uint64_t var47 = bin->length;
    span var48;
    if (1 <= var47) {
      span var49;
      take(bin, 1, &var49);
      var48 = var49;
    } else {
      return 0;
    }
    uint8_t var50;
    var50 = var48.pos[0];
    uint16_t var51 = ((((uint16_t)var46) << 8) | (var50));
    uint32_t var52 = ((((uint32_t)var42) << 16) | (var51));
    uint64_t var53 = var52;
    uint64_t var54 = bin->length;
    span var55;
    if (var53 <= var54) {
      span var56;
      take(bin, var53, &var56);
      var55 = var56;
    } else {
      return 0;
    }
    uint64_t var57 = bin->length;
    span var58;
    if (1 <= var57) {
      span var59;
      take(bin, 1, &var59);
      var58 = var59;
    } else {
      return 0;
    }
    uint8_t var60;
    var60 = var58.pos[0];
    uint64_t var61 = bin->length;
    span var62;
    if (1 <= var61) {
      span var63;
      take(bin, 1, &var63);
      var62 = var63;
    } else {
      return 0;
    }
    uint8_t var64;
    var64 = var62.pos[0];
    uint16_t var65 = ((((uint16_t)var60) << 8) | (var64));
    uint64_t var66 = bin->length;
    span var67;
    if (1 <= var66) {
      span var68;
      take(bin, 1, &var68);
      var67 = var68;
    } else {
      return 0;
    }
    uint8_t var69;
    var69 = var67.pos[0];
    uint64_t var70 = bin->length;
    span var71;
    if (1 <= var70) {
      span var72;
      take(bin, 1, &var72);
      var71 = var72;
    } else {
      return 0;
    }
    uint8_t var73;
    var73 = var71.pos[0];
    uint16_t var74 = ((((uint16_t)var69) << 8) | (var73));
    uint32_t var75 = ((((uint32_t)var65) << 16) | (var74));
    uint64_t var76 = var75;
    uint64_t var77 = bin->length;
    span var78;
    if (var76 <= var77) {
      span var79;
      take(bin, var76, &var79);
      var78 = var79;
    } else {
      return 0;
    }
    uint64_t var80 = bin->length;
    span var81;
    if (1 <= var80) {
      span var82;
      take(bin, 1, &var82);
      var81 = var82;
    } else {
      return 0;
    }
    uint8_t var83;
    var83 = var81.pos[0];
    uint64_t var84 = bin->length;
    span var85;
    if (1 <= var84) {
      span var86;
      take(bin, 1, &var86);
      var85 = var86;
    } else {
      return 0;
    }
    uint8_t var87;
    var87 = var85.pos[0];
    uint16_t var88 = ((((uint16_t)var83) << 8) | (var87));
    uint64_t var89 = bin->length;
    span var90;
    if (1 <= var89) {
      span var91;
      take(bin, 1, &var91);
      var90 = var91;
    } else {
      return 0;
    }
    uint8_t var92;
    var92 = var90.pos[0];
    uint64_t var93 = bin->length;
    span var94;
    if (1 <= var93) {
      span var95;
      take(bin, 1, &var95);
      var94 = var95;
    } else {
      return 0;
    }
    uint8_t var96;
    var96 = var94.pos[0];
    uint16_t var97 = ((((uint16_t)var92) << 8) | (var96));
    uint32_t var98 = ((((uint32_t)var88) << 16) | (var97));
    uint64_t var99 = var98;
    uint64_t var100 = bin->length;
    span var101;
    if (var99 <= var100) {
      span var102;
      take(bin, var99, &var102);
      var101 = var102;
    } else {
      return 0;
    }
    SSHPacket var103;
    create_DiffieHellmanReply(var55, var78, var101, &var103);
    var33 = var103;
    break;
  }
  case 30: {
    uint64_t var104 = bin->length;
    span var105;
    if (1 <= var104) {
      span var106;
      take(bin, 1, &var106);
      var105 = var106;
    } else {
      return 0;
    }
    uint8_t var107;
    var107 = var105.pos[0];
    uint64_t var108 = bin->length;
    span var109;
    if (1 <= var108) {
      span var110;
      take(bin, 1, &var110);
      var109 = var110;
    } else {
      return 0;
    }
    uint8_t var111;
    var111 = var109.pos[0];
    uint16_t var112 = ((((uint16_t)var107) << 8) | (var111));
    uint64_t var113 = bin->length;
    span var114;
    if (1 <= var113) {
      span var115;
      take(bin, 1, &var115);
      var114 = var115;
    } else {
      return 0;
    }
    uint8_t var116;
    var116 = var114.pos[0];
    uint64_t var117 = bin->length;
    span var118;
    if (1 <= var117) {
      span var119;
      take(bin, 1, &var119);
      var118 = var119;
    } else {
      return 0;
    }
    uint8_t var120;
    var120 = var118.pos[0];
    uint16_t var121 = ((((uint16_t)var116) << 8) | (var120));
    uint32_t var122 = ((((uint32_t)var112) << 16) | (var121));
    uint64_t var123 = var122;
    uint64_t var124 = bin->length;
    span var125;
    if (var123 <= var124) {
      span var126;
      take(bin, var123, &var126);
      var125 = var126;
    } else {
      return 0;
    }
    SSHPacket var127;
    create_DiffieHellmanInit(var125, &var127);
    var33 = var127;
    break;
  }
  case 21: {
    SSHPacket var128;
    create_NewKeys(&var128);
    var33 = var128;
    break;
  }
  case 20: {
    uint64_t var129 = bin->length;
    span var130;
    if (16 <= var129) {
      span var131;
      take(bin, 16, &var131);
      var130 = var131;
    } else {
      return 0;
    }
    uint64_t var132 = bin->length;
    span var133;
    if (1 <= var132) {
      span var134;
      take(bin, 1, &var134);
      var133 = var134;
    } else {
      return 0;
    }
    uint8_t var135;
    var135 = var133.pos[0];
    uint64_t var136 = bin->length;
    span var137;
    if (1 <= var136) {
      span var138;
      take(bin, 1, &var138);
      var137 = var138;
    } else {
      return 0;
    }
    uint8_t var139;
    var139 = var137.pos[0];
    uint16_t var140 = ((((uint16_t)var135) << 8) | (var139));
    uint64_t var141 = bin->length;
    span var142;
    if (1 <= var141) {
      span var143;
      take(bin, 1, &var143);
      var142 = var143;
    } else {
      return 0;
    }
    uint8_t var144;
    var144 = var142.pos[0];
    uint64_t var145 = bin->length;
    span var146;
    if (1 <= var145) {
      span var147;
      take(bin, 1, &var147);
      var146 = var147;
    } else {
      return 0;
    }
    uint8_t var148;
    var148 = var146.pos[0];
    uint16_t var149 = ((((uint16_t)var144) << 8) | (var148));
    uint32_t var150 = ((((uint32_t)var140) << 16) | (var149));
    uint64_t var151 = var150;
    uint64_t var152 = bin->length;
    span var153;
    if (var151 <= var152) {
      span var154;
      take(bin, var151, &var154);
      var153 = var154;
    } else {
      return 0;
    }
    uint64_t var155 = bin->length;
    span var156;
    if (1 <= var155) {
      span var157;
      take(bin, 1, &var157);
      var156 = var157;
    } else {
      return 0;
    }
    uint8_t var158;
    var158 = var156.pos[0];
    uint64_t var159 = bin->length;
    span var160;
    if (1 <= var159) {
      span var161;
      take(bin, 1, &var161);
      var160 = var161;
    } else {
      return 0;
    }
    uint8_t var162;
    var162 = var160.pos[0];
    uint16_t var163 = ((((uint16_t)var158) << 8) | (var162));
    uint64_t var164 = bin->length;
    span var165;
    if (1 <= var164) {
      span var166;
      take(bin, 1, &var166);
      var165 = var166;
    } else {
      return 0;
    }
    uint8_t var167;
    var167 = var165.pos[0];
    uint64_t var168 = bin->length;
    span var169;
    if (1 <= var168) {
      span var170;
      take(bin, 1, &var170);
      var169 = var170;
    } else {
      return 0;
    }
    uint8_t var171;
    var171 = var169.pos[0];
    uint16_t var172 = ((((uint16_t)var167) << 8) | (var171));
    uint32_t var173 = ((((uint32_t)var163) << 16) | (var172));
    uint64_t var174 = var173;
    uint64_t var175 = bin->length;
    span var176;
    if (var174 <= var175) {
      span var177;
      take(bin, var174, &var177);
      var176 = var177;
    } else {
      return 0;
    }
    uint64_t var178 = bin->length;
    span var179;
    if (1 <= var178) {
      span var180;
      take(bin, 1, &var180);
      var179 = var180;
    } else {
      return 0;
    }
    uint8_t var181;
    var181 = var179.pos[0];
    uint64_t var182 = bin->length;
    span var183;
    if (1 <= var182) {
      span var184;
      take(bin, 1, &var184);
      var183 = var184;
    } else {
      return 0;
    }
    uint8_t var185;
    var185 = var183.pos[0];
    uint16_t var186 = ((((uint16_t)var181) << 8) | (var185));
    uint64_t var187 = bin->length;
    span var188;
    if (1 <= var187) {
      span var189;
      take(bin, 1, &var189);
      var188 = var189;
    } else {
      return 0;
    }
    uint8_t var190;
    var190 = var188.pos[0];
    uint64_t var191 = bin->length;
    span var192;
    if (1 <= var191) {
      span var193;
      take(bin, 1, &var193);
      var192 = var193;
    } else {
      return 0;
    }
    uint8_t var194;
    var194 = var192.pos[0];
    uint16_t var195 = ((((uint16_t)var190) << 8) | (var194));
    uint32_t var196 = ((((uint32_t)var186) << 16) | (var195));
    uint64_t var197 = var196;
    uint64_t var198 = bin->length;
    span var199;
    if (var197 <= var198) {
      span var200;
      take(bin, var197, &var200);
      var199 = var200;
    } else {
      return 0;
    }
    uint64_t var201 = bin->length;
    span var202;
    if (1 <= var201) {
      span var203;
      take(bin, 1, &var203);
      var202 = var203;
    } else {
      return 0;
    }
    uint8_t var204;
    var204 = var202.pos[0];
    uint64_t var205 = bin->length;
    span var206;
    if (1 <= var205) {
      span var207;
      take(bin, 1, &var207);
      var206 = var207;
    } else {
      return 0;
    }
    uint8_t var208;
    var208 = var206.pos[0];
    uint16_t var209 = ((((uint16_t)var204) << 8) | (var208));
    uint64_t var210 = bin->length;
    span var211;
    if (1 <= var210) {
      span var212;
      take(bin, 1, &var212);
      var211 = var212;
    } else {
      return 0;
    }
    uint8_t var213;
    var213 = var211.pos[0];
    uint64_t var214 = bin->length;
    span var215;
    if (1 <= var214) {
      span var216;
      take(bin, 1, &var216);
      var215 = var216;
    } else {
      return 0;
    }
    uint8_t var217;
    var217 = var215.pos[0];
    uint16_t var218 = ((((uint16_t)var213) << 8) | (var217));
    uint32_t var219 = ((((uint32_t)var209) << 16) | (var218));
    uint64_t var220 = var219;
    uint64_t var221 = bin->length;
    span var222;
    if (var220 <= var221) {
      span var223;
      take(bin, var220, &var223);
      var222 = var223;
    } else {
      return 0;
    }
    uint64_t var224 = bin->length;
    span var225;
    if (1 <= var224) {
      span var226;
      take(bin, 1, &var226);
      var225 = var226;
    } else {
      return 0;
    }
    uint8_t var227;
    var227 = var225.pos[0];
    uint64_t var228 = bin->length;
    span var229;
    if (1 <= var228) {
      span var230;
      take(bin, 1, &var230);
      var229 = var230;
    } else {
      return 0;
    }
    uint8_t var231;
    var231 = var229.pos[0];
    uint16_t var232 = ((((uint16_t)var227) << 8) | (var231));
    uint64_t var233 = bin->length;
    span var234;
    if (1 <= var233) {
      span var235;
      take(bin, 1, &var235);
      var234 = var235;
    } else {
      return 0;
    }
    uint8_t var236;
    var236 = var234.pos[0];
    uint64_t var237 = bin->length;
    span var238;
    if (1 <= var237) {
      span var239;
      take(bin, 1, &var239);
      var238 = var239;
    } else {
      return 0;
    }
    uint8_t var240;
    var240 = var238.pos[0];
    uint16_t var241 = ((((uint16_t)var236) << 8) | (var240));
    uint32_t var242 = ((((uint32_t)var232) << 16) | (var241));
    uint64_t var243 = var242;
    uint64_t var244 = bin->length;
    span var245;
    if (var243 <= var244) {
      span var246;
      take(bin, var243, &var246);
      var245 = var246;
    } else {
      return 0;
    }
    uint64_t var247 = bin->length;
    span var248;
    if (1 <= var247) {
      span var249;
      take(bin, 1, &var249);
      var248 = var249;
    } else {
      return 0;
    }
    uint8_t var250;
    var250 = var248.pos[0];
    uint64_t var251 = bin->length;
    span var252;
    if (1 <= var251) {
      span var253;
      take(bin, 1, &var253);
      var252 = var253;
    } else {
      return 0;
    }
    uint8_t var254;
    var254 = var252.pos[0];
    uint16_t var255 = ((((uint16_t)var250) << 8) | (var254));
    uint64_t var256 = bin->length;
    span var257;
    if (1 <= var256) {
      span var258;
      take(bin, 1, &var258);
      var257 = var258;
    } else {
      return 0;
    }
    uint8_t var259;
    var259 = var257.pos[0];
    uint64_t var260 = bin->length;
    span var261;
    if (1 <= var260) {
      span var262;
      take(bin, 1, &var262);
      var261 = var262;
    } else {
      return 0;
    }
    uint8_t var263;
    var263 = var261.pos[0];
    uint16_t var264 = ((((uint16_t)var259) << 8) | (var263));
    uint32_t var265 = ((((uint32_t)var255) << 16) | (var264));
    uint64_t var266 = var265;
    uint64_t var267 = bin->length;
    span var268;
    if (var266 <= var267) {
      span var269;
      take(bin, var266, &var269);
      var268 = var269;
    } else {
      return 0;
    }
    uint64_t var270 = bin->length;
    span var271;
    if (1 <= var270) {
      span var272;
      take(bin, 1, &var272);
      var271 = var272;
    } else {
      return 0;
    }
    uint8_t var273;
    var273 = var271.pos[0];
    uint64_t var274 = bin->length;
    span var275;
    if (1 <= var274) {
      span var276;
      take(bin, 1, &var276);
      var275 = var276;
    } else {
      return 0;
    }
    uint8_t var277;
    var277 = var275.pos[0];
    uint16_t var278 = ((((uint16_t)var273) << 8) | (var277));
    uint64_t var279 = bin->length;
    span var280;
    if (1 <= var279) {
      span var281;
      take(bin, 1, &var281);
      var280 = var281;
    } else {
      return 0;
    }
    uint8_t var282;
    var282 = var280.pos[0];
    uint64_t var283 = bin->length;
    span var284;
    if (1 <= var283) {
      span var285;
      take(bin, 1, &var285);
      var284 = var285;
    } else {
      return 0;
    }
    uint8_t var286;
    var286 = var284.pos[0];
    uint16_t var287 = ((((uint16_t)var282) << 8) | (var286));
    uint32_t var288 = ((((uint32_t)var278) << 16) | (var287));
    uint64_t var289 = var288;
    uint64_t var290 = bin->length;
    span var291;
    if (var289 <= var290) {
      span var292;
      take(bin, var289, &var292);
      var291 = var292;
    } else {
      return 0;
    }
    uint64_t var293 = bin->length;
    span var294;
    if (1 <= var293) {
      span var295;
      take(bin, 1, &var295);
      var294 = var295;
    } else {
      return 0;
    }
    uint8_t var296;
    var296 = var294.pos[0];
    uint64_t var297 = bin->length;
    span var298;
    if (1 <= var297) {
      span var299;
      take(bin, 1, &var299);
      var298 = var299;
    } else {
      return 0;
    }
    uint8_t var300;
    var300 = var298.pos[0];
    uint16_t var301 = ((((uint16_t)var296) << 8) | (var300));
    uint64_t var302 = bin->length;
    span var303;
    if (1 <= var302) {
      span var304;
      take(bin, 1, &var304);
      var303 = var304;
    } else {
      return 0;
    }
    uint8_t var305;
    var305 = var303.pos[0];
    uint64_t var306 = bin->length;
    span var307;
    if (1 <= var306) {
      span var308;
      take(bin, 1, &var308);
      var307 = var308;
    } else {
      return 0;
    }
    uint8_t var309;
    var309 = var307.pos[0];
    uint16_t var310 = ((((uint16_t)var305) << 8) | (var309));
    uint32_t var311 = ((((uint32_t)var301) << 16) | (var310));
    uint64_t var312 = var311;
    uint64_t var313 = bin->length;
    span var314;
    if (var312 <= var313) {
      span var315;
      take(bin, var312, &var315);
      var314 = var315;
    } else {
      return 0;
    }
    uint64_t var316 = bin->length;
    span var317;
    if (1 <= var316) {
      span var318;
      take(bin, 1, &var318);
      var317 = var318;
    } else {
      return 0;
    }
    uint8_t var319;
    var319 = var317.pos[0];
    uint64_t var320 = bin->length;
    span var321;
    if (1 <= var320) {
      span var322;
      take(bin, 1, &var322);
      var321 = var322;
    } else {
      return 0;
    }
    uint8_t var323;
    var323 = var321.pos[0];
    uint16_t var324 = ((((uint16_t)var319) << 8) | (var323));
    uint64_t var325 = bin->length;
    span var326;
    if (1 <= var325) {
      span var327;
      take(bin, 1, &var327);
      var326 = var327;
    } else {
      return 0;
    }
    uint8_t var328;
    var328 = var326.pos[0];
    uint64_t var329 = bin->length;
    span var330;
    if (1 <= var329) {
      span var331;
      take(bin, 1, &var331);
      var330 = var331;
    } else {
      return 0;
    }
    uint8_t var332;
    var332 = var330.pos[0];
    uint16_t var333 = ((((uint16_t)var328) << 8) | (var332));
    uint32_t var334 = ((((uint32_t)var324) << 16) | (var333));
    uint64_t var335 = var334;
    uint64_t var336 = bin->length;
    span var337;
    if (var335 <= var336) {
      span var338;
      take(bin, var335, &var338);
      var337 = var338;
    } else {
      return 0;
    }
    uint64_t var339 = bin->length;
    span var340;
    if (1 <= var339) {
      span var341;
      take(bin, 1, &var341);
      var340 = var341;
    } else {
      return 0;
    }
    uint8_t var342;
    var342 = var340.pos[0];
    uint64_t var343 = bin->length;
    span var344;
    if (1 <= var343) {
      span var345;
      take(bin, 1, &var345);
      var344 = var345;
    } else {
      return 0;
    }
    uint8_t var346;
    var346 = var344.pos[0];
    uint16_t var347 = ((((uint16_t)var342) << 8) | (var346));
    uint64_t var348 = bin->length;
    span var349;
    if (1 <= var348) {
      span var350;
      take(bin, 1, &var350);
      var349 = var350;
    } else {
      return 0;
    }
    uint8_t var351;
    var351 = var349.pos[0];
    uint64_t var352 = bin->length;
    span var353;
    if (1 <= var352) {
      span var354;
      take(bin, 1, &var354);
      var353 = var354;
    } else {
      return 0;
    }
    uint8_t var355;
    var355 = var353.pos[0];
    uint16_t var356 = ((((uint16_t)var351) << 8) | (var355));
    uint32_t var357 = ((((uint32_t)var347) << 16) | (var356));
    uint64_t var358 = var357;
    uint64_t var359 = bin->length;
    span var360;
    if (var358 <= var359) {
      span var361;
      take(bin, var358, &var361);
      var360 = var361;
    } else {
      return 0;
    }
    uint64_t var362 = bin->length;
    span var363;
    if (1 <= var362) {
      span var364;
      take(bin, 1, &var364);
      var363 = var364;
    } else {
      return 0;
    }
    uint8_t var365;
    var365 = var363.pos[0];
    uint64_t var366 = bin->length;
    span var367;
    if (1 <= var366) {
      span var368;
      take(bin, 1, &var368);
      var367 = var368;
    } else {
      return 0;
    }
    uint8_t var369;
    var369 = var367.pos[0];
    uint64_t var370 = bin->length;
    span var371;
    if (1 <= var370) {
      span var372;
      take(bin, 1, &var372);
      var371 = var372;
    } else {
      return 0;
    }
    uint8_t var373;
    var373 = var371.pos[0];
    uint16_t var374 = ((((uint16_t)var369) << 8) | (var373));
    uint64_t var375 = bin->length;
    span var376;
    if (1 <= var375) {
      span var377;
      take(bin, 1, &var377);
      var376 = var377;
    } else {
      return 0;
    }
    uint8_t var378;
    var378 = var376.pos[0];
    uint64_t var379 = bin->length;
    span var380;
    if (1 <= var379) {
      span var381;
      take(bin, 1, &var381);
      var380 = var381;
    } else {
      return 0;
    }
    uint8_t var382;
    var382 = var380.pos[0];
    uint16_t var383 = ((((uint16_t)var378) << 8) | (var382));
    uint32_t var384 = ((((uint32_t)var374) << 16) | (var383));
    SSHPacket var385;
    create_KeyExchange(var130, var153, var176, var199, var222, var245, var268,
                       var291, var314, var337, var360, var365, &var385);
    var33 = var385;
    break;
  }
  case 6: {
    uint64_t var386 = bin->length;
    span var387;
    if (1 <= var386) {
      span var388;
      take(bin, 1, &var388);
      var387 = var388;
    } else {
      return 0;
    }
    uint8_t var389;
    var389 = var387.pos[0];
    uint64_t var390 = bin->length;
    span var391;
    if (1 <= var390) {
      span var392;
      take(bin, 1, &var392);
      var391 = var392;
    } else {
      return 0;
    }
    uint8_t var393;
    var393 = var391.pos[0];
    uint16_t var394 = ((((uint16_t)var389) << 8) | (var393));
    uint64_t var395 = bin->length;
    span var396;
    if (1 <= var395) {
      span var397;
      take(bin, 1, &var397);
      var396 = var397;
    } else {
      return 0;
    }
    uint8_t var398;
    var398 = var396.pos[0];
    uint64_t var399 = bin->length;
    span var400;
    if (1 <= var399) {
      span var401;
      take(bin, 1, &var401);
      var400 = var401;
    } else {
      return 0;
    }
    uint8_t var402;
    var402 = var400.pos[0];
    uint16_t var403 = ((((uint16_t)var398) << 8) | (var402));
    uint32_t var404 = ((((uint32_t)var394) << 16) | (var403));
    uint64_t var405 = var404;
    uint64_t var406 = bin->length;
    span var407;
    if (var405 <= var406) {
      span var408;
      take(bin, var405, &var408);
      var407 = var408;
    } else {
      return 0;
    }
    SSHPacket var409;
    create_ServiceAccept(var407, &var409);
    var33 = var409;
    break;
  }
  case 5: {
    uint64_t var410 = bin->length;
    span var411;
    if (1 <= var410) {
      span var412;
      take(bin, 1, &var412);
      var411 = var412;
    } else {
      return 0;
    }
    uint8_t var413;
    var413 = var411.pos[0];
    uint64_t var414 = bin->length;
    span var415;
    if (1 <= var414) {
      span var416;
      take(bin, 1, &var416);
      var415 = var416;
    } else {
      return 0;
    }
    uint8_t var417;
    var417 = var415.pos[0];
    uint16_t var418 = ((((uint16_t)var413) << 8) | (var417));
    uint64_t var419 = bin->length;
    span var420;
    if (1 <= var419) {
      span var421;
      take(bin, 1, &var421);
      var420 = var421;
    } else {
      return 0;
    }
    uint8_t var422;
    var422 = var420.pos[0];
    uint64_t var423 = bin->length;
    span var424;
    if (1 <= var423) {
      span var425;
      take(bin, 1, &var425);
      var424 = var425;
    } else {
      return 0;
    }
    uint8_t var426;
    var426 = var424.pos[0];
    uint16_t var427 = ((((uint16_t)var422) << 8) | (var426));
    uint32_t var428 = ((((uint32_t)var418) << 16) | (var427));
    uint64_t var429 = var428;
    uint64_t var430 = bin->length;
    span var431;
    if (var429 <= var430) {
      span var432;
      take(bin, var429, &var432);
      var431 = var432;
    } else {
      return 0;
    }
    SSHPacket var433;
    create_ServiceRequest(var431, &var433);
    var33 = var433;
    break;
  }
  case 4: {
    uint64_t var434 = bin->length;
    span var435;
    if (1 <= var434) {
      span var436;
      take(bin, 1, &var436);
      var435 = var436;
    } else {
      return 0;
    }
    uint8_t var437;
    var437 = var435.pos[0];
    uint64_t var438 = bin->length;
    span var439;
    if (1 <= var438) {
      span var440;
      take(bin, 1, &var440);
      var439 = var440;
    } else {
      return 0;
    }
    uint8_t var441;
    var441 = var439.pos[0];
    uint64_t var442 = bin->length;
    span var443;
    if (1 <= var442) {
      span var444;
      take(bin, 1, &var444);
      var443 = var444;
    } else {
      return 0;
    }
    uint8_t var445;
    var445 = var443.pos[0];
    uint16_t var446 = ((((uint16_t)var441) << 8) | (var445));
    uint64_t var447 = bin->length;
    span var448;
    if (1 <= var447) {
      span var449;
      take(bin, 1, &var449);
      var448 = var449;
    } else {
      return 0;
    }
    uint8_t var450;
    var450 = var448.pos[0];
    uint64_t var451 = bin->length;
    span var452;
    if (1 <= var451) {
      span var453;
      take(bin, 1, &var453);
      var452 = var453;
    } else {
      return 0;
    }
    uint8_t var454;
    var454 = var452.pos[0];
    uint16_t var455 = ((((uint16_t)var450) << 8) | (var454));
    uint32_t var456 = ((((uint32_t)var446) << 16) | (var455));
    uint64_t var457 = var456;
    uint64_t var458 = bin->length;
    span var459;
    if (var457 <= var458) {
      span var460;
      take(bin, var457, &var460);
      var459 = var460;
    } else {
      return 0;
    }
    uint64_t var461 = bin->length;
    span var462;
    if (1 <= var461) {
      span var463;
      take(bin, 1, &var463);
      var462 = var463;
    } else {
      return 0;
    }
    uint8_t var464;
    var464 = var462.pos[0];
    uint64_t var465 = bin->length;
    span var466;
    if (1 <= var465) {
      span var467;
      take(bin, 1, &var467);
      var466 = var467;
    } else {
      return 0;
    }
    uint8_t var468;
    var468 = var466.pos[0];
    uint16_t var469 = ((((uint16_t)var464) << 8) | (var468));
    uint64_t var470 = bin->length;
    span var471;
    if (1 <= var470) {
      span var472;
      take(bin, 1, &var472);
      var471 = var472;
    } else {
      return 0;
    }
    uint8_t var473;
    var473 = var471.pos[0];
    uint64_t var474 = bin->length;
    span var475;
    if (1 <= var474) {
      span var476;
      take(bin, 1, &var476);
      var475 = var476;
    } else {
      return 0;
    }
    uint8_t var477;
    var477 = var475.pos[0];
    uint16_t var478 = ((((uint16_t)var473) << 8) | (var477));
    uint32_t var479 = ((((uint32_t)var469) << 16) | (var478));
    uint64_t var480 = var479;
    uint64_t var481 = bin->length;
    span var482;
    if (var480 <= var481) {
      span var483;
      take(bin, var480, &var483);
      var482 = var483;
    } else {
      return 0;
    }
    bool var484 = 0 < var437;
    SSHPacket var485;
    create_Debug(var484, var459, var482, &var485);
    var33 = var485;
    break;
  }
  case 3: {
    uint64_t var486 = bin->length;
    span var487;
    if (1 <= var486) {
      span var488;
      take(bin, 1, &var488);
      var487 = var488;
    } else {
      return 0;
    }
    uint8_t var489;
    var489 = var487.pos[0];
    uint64_t var490 = bin->length;
    span var491;
    if (1 <= var490) {
      span var492;
      take(bin, 1, &var492);
      var491 = var492;
    } else {
      return 0;
    }
    uint8_t var493;
    var493 = var491.pos[0];
    uint16_t var494 = ((((uint16_t)var489) << 8) | (var493));
    uint64_t var495 = bin->length;
    span var496;
    if (1 <= var495) {
      span var497;
      take(bin, 1, &var497);
      var496 = var497;
    } else {
      return 0;
    }
    uint8_t var498;
    var498 = var496.pos[0];
    uint64_t var499 = bin->length;
    span var500;
    if (1 <= var499) {
      span var501;
      take(bin, 1, &var501);
      var500 = var501;
    } else {
      return 0;
    }
    uint8_t var502;
    var502 = var500.pos[0];
    uint16_t var503 = ((((uint16_t)var498) << 8) | (var502));
    uint32_t var504 = ((((uint32_t)var494) << 16) | (var503));
    SSHPacket var505;
    create_Unimplemented(var504, &var505);
    var33 = var505;
    break;
  }
  case 2: {
    uint64_t var506 = bin->length;
    span var507;
    if (1 <= var506) {
      span var508;
      take(bin, 1, &var508);
      var507 = var508;
    } else {
      return 0;
    }
    uint8_t var509;
    var509 = var507.pos[0];
    uint64_t var510 = bin->length;
    span var511;
    if (1 <= var510) {
      span var512;
      take(bin, 1, &var512);
      var511 = var512;
    } else {
      return 0;
    }
    uint8_t var513;
    var513 = var511.pos[0];
    uint16_t var514 = ((((uint16_t)var509) << 8) | (var513));
    uint64_t var515 = bin->length;
    span var516;
    if (1 <= var515) {
      span var517;
      take(bin, 1, &var517);
      var516 = var517;
    } else {
      return 0;
    }
    uint8_t var518;
    var518 = var516.pos[0];
    uint64_t var519 = bin->length;
    span var520;
    if (1 <= var519) {
      span var521;
      take(bin, 1, &var521);
      var520 = var521;
    } else {
      return 0;
    }
    uint8_t var522;
    var522 = var520.pos[0];
    uint16_t var523 = ((((uint16_t)var518) << 8) | (var522));
    uint32_t var524 = ((((uint32_t)var514) << 16) | (var523));
    uint64_t var525 = var524;
    uint64_t var526 = bin->length;
    span var527;
    if (var525 <= var526) {
      span var528;
      take(bin, var525, &var528);
      var527 = var528;
    } else {
      return 0;
    }
    SSHPacket var529;
    create_Ignore(var527, &var529);
    var33 = var529;
    break;
  }
  case 1: {
    uint64_t var530 = bin->length;
    span var531;
    if (1 <= var530) {
      span var532;
      take(bin, 1, &var532);
      var531 = var532;
    } else {
      return 0;
    }
    uint8_t var533;
    var533 = var531.pos[0];
    uint64_t var534 = bin->length;
    span var535;
    if (1 <= var534) {
      span var536;
      take(bin, 1, &var536);
      var535 = var536;
    } else {
      return 0;
    }
    uint8_t var537;
    var537 = var535.pos[0];
    uint16_t var538 = ((((uint16_t)var533) << 8) | (var537));
    uint64_t var539 = bin->length;
    span var540;
    if (1 <= var539) {
      span var541;
      take(bin, 1, &var541);
      var540 = var541;
    } else {
      return 0;
    }
    uint8_t var542;
    var542 = var540.pos[0];
    uint64_t var543 = bin->length;
    span var544;
    if (1 <= var543) {
      span var545;
      take(bin, 1, &var545);
      var544 = var545;
    } else {
      return 0;
    }
    uint8_t var546;
    var546 = var544.pos[0];
    uint16_t var547 = ((((uint16_t)var542) << 8) | (var546));
    uint32_t var548 = ((((uint32_t)var538) << 16) | (var547));
    uint64_t var549 = bin->length;
    span var550;
    if (1 <= var549) {
      span var551;
      take(bin, 1, &var551);
      var550 = var551;
    } else {
      return 0;
    }
    uint8_t var552;
    var552 = var550.pos[0];
    uint64_t var553 = bin->length;
    span var554;
    if (1 <= var553) {
      span var555;
      take(bin, 1, &var555);
      var554 = var555;
    } else {
      return 0;
    }
    uint8_t var556;
    var556 = var554.pos[0];
    uint16_t var557 = ((((uint16_t)var552) << 8) | (var556));
    uint64_t var558 = bin->length;
    span var559;
    if (1 <= var558) {
      span var560;
      take(bin, 1, &var560);
      var559 = var560;
    } else {
      return 0;
    }
    uint8_t var561;
    var561 = var559.pos[0];
    uint64_t var562 = bin->length;
    span var563;
    if (1 <= var562) {
      span var564;
      take(bin, 1, &var564);
      var563 = var564;
    } else {
      return 0;
    }
    uint8_t var565;
    var565 = var563.pos[0];
    uint16_t var566 = ((((uint16_t)var561) << 8) | (var565));
    uint32_t var567 = ((((uint32_t)var557) << 16) | (var566));
    uint64_t var568 = var567;
    uint64_t var569 = bin->length;
    span var570;
    if (var568 <= var569) {
      span var571;
      take(bin, var568, &var571);
      var570 = var571;
    } else {
      return 0;
    }
    uint64_t var572 = bin->length;
    span var573;
    if (1 <= var572) {
      span var574;
      take(bin, 1, &var574);
      var573 = var574;
    } else {
      return 0;
    }
    uint8_t var575;
    var575 = var573.pos[0];
    uint64_t var576 = bin->length;
    span var577;
    if (1 <= var576) {
      span var578;
      take(bin, 1, &var578);
      var577 = var578;
    } else {
      return 0;
    }
    uint8_t var579;
    var579 = var577.pos[0];
    uint16_t var580 = ((((uint16_t)var575) << 8) | (var579));
    uint64_t var581 = bin->length;
    span var582;
    if (1 <= var581) {
      span var583;
      take(bin, 1, &var583);
      var582 = var583;
    } else {
      return 0;
    }
    uint8_t var584;
    var584 = var582.pos[0];
    uint64_t var585 = bin->length;
    span var586;
    if (1 <= var585) {
      span var587;
      take(bin, 1, &var587);
      var586 = var587;
    } else {
      return 0;
    }
    uint8_t var588;
    var588 = var586.pos[0];
    uint16_t var589 = ((((uint16_t)var584) << 8) | (var588));
    uint32_t var590 = ((((uint32_t)var580) << 16) | (var589));
    uint64_t var591 = var590;
    uint64_t var592 = bin->length;
    span var593;
    if (var591 <= var592) {
      span var594;
      take(bin, var591, &var594);
      var593 = var594;
    } else {
      return 0;
    }
    SSHPacket var595;
    create_Disconnect(var548, var570, var593, &var595);
    var33 = var595;
    break;
  }
  default: {
    return 0;
  }
  }

  *var597 = var33;
  return 1;
}

int parse_ssh_packet(span *bin, pair_09SSHPacket04span *var1) {
  uint64_t var2 = bin->length;
  span var3;
  if (1 <= var2) {
    span var4;
    take(bin, 1, &var4);
    var3 = var4;
  } else {
    return 0;
  }
  uint8_t var5;
  var5 = var3.pos[0];
  uint64_t var6 = bin->length;
  span var7;
  if (1 <= var6) {
    span var8;
    take(bin, 1, &var8);
    var7 = var8;
  } else {
    return 0;
  }
  uint8_t var9;
  var9 = var7.pos[0];
  uint16_t var10 = ((((uint16_t)var5) << 8) | (var9));
  uint64_t var11 = bin->length;
  span var12;
  if (1 <= var11) {
    span var13;
    take(bin, 1, &var13);
    var12 = var13;
  } else {
    return 0;
  }
  uint8_t var14;
  var14 = var12.pos[0];
  uint64_t var15 = bin->length;
  span var16;
  if (1 <= var15) {
    span var17;
    take(bin, 1, &var17);
    var16 = var17;
  } else {
    return 0;
  }
  uint8_t var18;
  var18 = var16.pos[0];
  uint16_t var19 = ((((uint16_t)var14) << 8) | (var18));
  uint32_t var20 = ((((uint32_t)var10) << 16) | (var19));
  uint64_t var21 = bin->length;
  span var22;
  if (1 <= var21) {
    span var23;
    take(bin, 1, &var23);
    var22 = var23;
  } else {
    return 0;
  }
  uint8_t var24;
  var24 = var22.pos[0];
  pair_09SSHPacket04span var25;
  if (var20 < var24 + 1) {
    return 0;
  } else {
    uint64_t var26 = bin->length;
    span var27;
    if (var20 - var24 - 1 <= var26) {
      span var28;
      take(bin, var20 - var24 - 1, &var28);
      var27 = var28;
    } else {
      return 0;
    }
    option_span var596;
    var596.ok = true;
    var596.val = var27;
    SSHPacket var597;
    if (var596.ok) {
      span var598 = var596.val;
      if (!local1(&(var596.val), &var597))
        return 0;
      var596.val = var598;
    } else {
      span var598;
      get(bin, &var598);
      if (!local1(bin, &var597))
        return 0;
      set(bin, var598);
    }
    uint64_t var599 = bin->length;
    span var600;
    if (var24 <= var599) {
      span var601;
      take(bin, var24, &var601);
      var600 = var601;
    } else {
      return 0;
    }
    pair_09SSHPacket04span var603;
    var603.fst = var597;
    var603.snd = var600;
    pair_09SSHPacket04span var602 = var603;
    var25 = var602;
  }
  *var1 = var25;
  return 1;
}
