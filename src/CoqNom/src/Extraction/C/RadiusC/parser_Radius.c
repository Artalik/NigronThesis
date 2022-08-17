#include "Radius.h"

DEFINE_OPTION(span);
DEFINE_OPTION(uint64_t);
//DEFINE_OPTION(Vector_radius_attribute);
int local1(span *bin, radius_attribute *var108) {
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
  uint64_t var97 = bin->length;
  span var98;
  if (1 <= var97) {
    span var99;
    take(bin, 1, &var99);
    var98 = var99;
  } else {
    return 0;
  }
  uint8_t var100;
  var100 = var98.pos[0];
  uint64_t var101 = bin->length;
  span var102;
  if (1 <= var101) {
    span var103;
    take(bin, 1, &var103);
    var102 = var103;
  } else {
    return 0;
  }
  uint8_t var104;
  var104 = var102.pos[0];
  ipv4 var105;
  create_ipv4(var92, var96, var100, var104, &var105);
  radius_attribute var106;
  create_FramedIPNetmask(var105, &var106);
  *var108 = var106;
  return 1;
}

int local2(span *bin, radius_attribute *var248) {
  uint64_t var229 = bin->length;
  span var230;
  if (1 <= var229) {
    span var231;
    take(bin, 1, &var231);
    var230 = var231;
  } else {
    return 0;
  }
  uint8_t var232;
  var232 = var230.pos[0];
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
  uint64_t var241 = bin->length;
  span var242;
  if (1 <= var241) {
    span var243;
    take(bin, 1, &var243);
    var242 = var243;
  } else {
    return 0;
  }
  uint8_t var244;
  var244 = var242.pos[0];
  ipv4 var245;
  create_ipv4(var232, var236, var240, var244, &var245);
  radius_attribute var246;
  create_FramedIPAddress(var245, &var246);
  *var248 = var246;
  return 1;
}

int local3(span *bin, radius_attribute *var272) {
  uint64_t var253 = bin->length;
  span var254;
  if (1 <= var253) {
    span var255;
    take(bin, 1, &var255);
    var254 = var255;
  } else {
    return 0;
  }
  uint8_t var256;
  var256 = var254.pos[0];
  uint64_t var257 = bin->length;
  span var258;
  if (1 <= var257) {
    span var259;
    take(bin, 1, &var259);
    var258 = var259;
  } else {
    return 0;
  }
  uint8_t var260;
  var260 = var258.pos[0];
  uint64_t var261 = bin->length;
  span var262;
  if (1 <= var261) {
    span var263;
    take(bin, 1, &var263);
    var262 = var263;
  } else {
    return 0;
  }
  uint8_t var264;
  var264 = var262.pos[0];
  uint64_t var265 = bin->length;
  span var266;
  if (1 <= var265) {
    span var267;
    take(bin, 1, &var267);
    var266 = var267;
  } else {
    return 0;
  }
  uint8_t var268;
  var268 = var266.pos[0];
  ipv4 var269;
  create_ipv4(var256, var260, var264, var268, &var269);
  radius_attribute var270;
  create_NasIPAddress(var269, &var270);
  *var272 = var270;
  return 1;
}

int local4(span *bin, radius_attribute *var284, uint8_t var30) {
  radius_attribute var39;
  switch (var30) {

  case 31: {
    uint64_t var40 = bin->length;
    span var41;
    take(bin, var40, &var41);
    radius_attribute var42;
    create_CallingStationId(var41, &var42);
    var39 = var42;
    break;
  }
  case 11: {
    uint64_t var43 = bin->length;
    span var44;
    take(bin, var43, &var44);
    radius_attribute var45;
    create_FilterId(var44, &var45);
    var39 = var45;
    break;
  }
  case 7: {
    uint64_t var46 = bin->length;
    span var47;
    if (1 <= var46) {
      span var48;
      take(bin, 1, &var48);
      var47 = var48;
    } else {
      return 0;
    }
    uint8_t var49;
    var49 = var47.pos[0];
    uint64_t var50 = bin->length;
    span var51;
    if (1 <= var50) {
      span var52;
      take(bin, 1, &var52);
      var51 = var52;
    } else {
      return 0;
    }
    uint8_t var53;
    var53 = var51.pos[0];
    uint16_t var54 = ((((uint16_t)var49) << 8) | (var53));
    uint64_t var55 = bin->length;
    span var56;
    if (1 <= var55) {
      span var57;
      take(bin, 1, &var57);
      var56 = var57;
    } else {
      return 0;
    }
    uint8_t var58;
    var58 = var56.pos[0];
    uint64_t var59 = bin->length;
    span var60;
    if (1 <= var59) {
      span var61;
      take(bin, 1, &var61);
      var60 = var61;
    } else {
      return 0;
    }
    uint8_t var62;
    var62 = var60.pos[0];
    uint16_t var63 = ((((uint16_t)var58) << 8) | (var62));
    uint32_t var64 = ((((uint32_t)var54) << 16) | (var63));
    radius_attribute var65;
    create_Protocol(var64, &var65);
    var39 = var65;
    break;
  }
  case 13: {
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
    uint64_t var75 = bin->length;
    span var76;
    if (1 <= var75) {
      span var77;
      take(bin, 1, &var77);
      var76 = var77;
    } else {
      return 0;
    }
    uint8_t var78;
    var78 = var76.pos[0];
    uint64_t var79 = bin->length;
    span var80;
    if (1 <= var79) {
      span var81;
      take(bin, 1, &var81);
      var80 = var81;
    } else {
      return 0;
    }
    uint8_t var82;
    var82 = var80.pos[0];
    uint16_t var83 = ((((uint16_t)var78) << 8) | (var82));
    uint32_t var84 = ((((uint32_t)var74) << 16) | (var83));
    radius_attribute var85;
    create_Compression(var84, &var85);
    var39 = var85;
    break;
  }
  case 9: {
    uint64_t var86 = bin->length;
    span var87;
    if (4 <= var86) {
      span var88;
      take(bin, 4, &var88);
      var87 = var88;
    } else {
      return 0;
    }
    option_span var107;
    var107.ok = true;
    var107.val = var87;
    radius_attribute var108;
    if (var107.ok) {
      span var109 = var107.val;
      if (!local1(&(var107.val), &var108))
        return 0;
      var107.val = var109;
    } else {
      span var109;
      get(bin, &var109);
      if (!local1(bin, &var108))
        return 0;
      set(bin, var109);
    }
    var39 = var108;
    break;
  }
  case 5: {
    uint64_t var110 = bin->length;
    span var111;
    if (1 <= var110) {
      span var112;
      take(bin, 1, &var112);
      var111 = var112;
    } else {
      return 0;
    }
    uint8_t var113;
    var113 = var111.pos[0];
    uint64_t var114 = bin->length;
    span var115;
    if (1 <= var114) {
      span var116;
      take(bin, 1, &var116);
      var115 = var116;
    } else {
      return 0;
    }
    uint8_t var117;
    var117 = var115.pos[0];
    uint16_t var118 = ((((uint16_t)var113) << 8) | (var117));
    uint64_t var119 = bin->length;
    span var120;
    if (1 <= var119) {
      span var121;
      take(bin, 1, &var121);
      var120 = var121;
    } else {
      return 0;
    }
    uint8_t var122;
    var122 = var120.pos[0];
    uint64_t var123 = bin->length;
    span var124;
    if (1 <= var123) {
      span var125;
      take(bin, 1, &var125);
      var124 = var125;
    } else {
      return 0;
    }
    uint8_t var126;
    var126 = var124.pos[0];
    uint16_t var127 = ((((uint16_t)var122) << 8) | (var126));
    uint32_t var128 = ((((uint32_t)var118) << 16) | (var127));
    radius_attribute var129;
    create_NasPort(var128, &var129);
    var39 = var129;
    break;
  }
  case 3: {
    uint64_t var130 = bin->length;
    radius_attribute var131;
    if (var130 < 2) {
      return 0;
    } else {
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
      take(bin, var136, &var137);
      radius_attribute var138;
      create_ChapPassword(var135, var137, &var138);
      var131 = var138;
    }
    var39 = var131;
    break;
  }
  case 30: {
    uint64_t var139 = bin->length;
    span var140;
    take(bin, var139, &var140);
    radius_attribute var141;
    create_CalledStationId(var140, &var141);
    var39 = var141;
    break;
  }
  case 26: {
    uint64_t var142 = bin->length;
    radius_attribute var143;
    if (var142 < 5) {
      return 0;
    } else {
      uint64_t var144 = bin->length;
      span var145;
      if (1 <= var144) {
        span var146;
        take(bin, 1, &var146);
        var145 = var146;
      } else {
        return 0;
      }
      uint8_t var147;
      var147 = var145.pos[0];
      uint64_t var148 = bin->length;
      span var149;
      if (1 <= var148) {
        span var150;
        take(bin, 1, &var150);
        var149 = var150;
      } else {
        return 0;
      }
      uint8_t var151;
      var151 = var149.pos[0];
      uint16_t var152 = ((((uint16_t)var147) << 8) | (var151));
      uint64_t var153 = bin->length;
      span var154;
      if (1 <= var153) {
        span var155;
        take(bin, 1, &var155);
        var154 = var155;
      } else {
        return 0;
      }
      uint8_t var156;
      var156 = var154.pos[0];
      uint64_t var157 = bin->length;
      span var158;
      if (1 <= var157) {
        span var159;
        take(bin, 1, &var159);
        var158 = var159;
      } else {
        return 0;
      }
      uint8_t var160;
      var160 = var158.pos[0];
      uint16_t var161 = ((((uint16_t)var156) << 8) | (var160));
      uint32_t var162 = ((((uint32_t)var152) << 16) | (var161));
      uint64_t var163 = bin->length;
      span var164;
      take(bin, var163, &var164);
      radius_attribute var165;
      create_VendorSpecific(var162, var164, &var165);
      var143 = var165;
    }
    var39 = var143;
    break;
  }
  case 10: {
    uint64_t var166 = bin->length;
    span var167;
    if (1 <= var166) {
      span var168;
      take(bin, 1, &var168);
      var167 = var168;
    } else {
      return 0;
    }
    uint8_t var169;
    var169 = var167.pos[0];
    uint64_t var170 = bin->length;
    span var171;
    if (1 <= var170) {
      span var172;
      take(bin, 1, &var172);
      var171 = var172;
    } else {
      return 0;
    }
    uint8_t var173;
    var173 = var171.pos[0];
    uint16_t var174 = ((((uint16_t)var169) << 8) | (var173));
    uint64_t var175 = bin->length;
    span var176;
    if (1 <= var175) {
      span var177;
      take(bin, 1, &var177);
      var176 = var177;
    } else {
      return 0;
    }
    uint8_t var178;
    var178 = var176.pos[0];
    uint64_t var179 = bin->length;
    span var180;
    if (1 <= var179) {
      span var181;
      take(bin, 1, &var181);
      var180 = var181;
    } else {
      return 0;
    }
    uint8_t var182;
    var182 = var180.pos[0];
    uint16_t var183 = ((((uint16_t)var178) << 8) | (var182));
    uint32_t var184 = ((((uint32_t)var174) << 16) | (var183));
    radius_attribute var185;
    create_Routing(var184, &var185);
    var39 = var185;
    break;
  }
  case 6: {
    uint64_t var186 = bin->length;
    span var187;
    if (1 <= var186) {
      span var188;
      take(bin, 1, &var188);
      var187 = var188;
    } else {
      return 0;
    }
    uint8_t var189;
    var189 = var187.pos[0];
    uint64_t var190 = bin->length;
    span var191;
    if (1 <= var190) {
      span var192;
      take(bin, 1, &var192);
      var191 = var192;
    } else {
      return 0;
    }
    uint8_t var193;
    var193 = var191.pos[0];
    uint16_t var194 = ((((uint16_t)var189) << 8) | (var193));
    uint64_t var195 = bin->length;
    span var196;
    if (1 <= var195) {
      span var197;
      take(bin, 1, &var197);
      var196 = var197;
    } else {
      return 0;
    }
    uint8_t var198;
    var198 = var196.pos[0];
    uint64_t var199 = bin->length;
    span var200;
    if (1 <= var199) {
      span var201;
      take(bin, 1, &var201);
      var200 = var201;
    } else {
      return 0;
    }
    uint8_t var202;
    var202 = var200.pos[0];
    uint16_t var203 = ((((uint16_t)var198) << 8) | (var202));
    uint32_t var204 = ((((uint32_t)var194) << 16) | (var203));
    radius_attribute var205;
    create_Service(var204, &var205);
    var39 = var205;
    break;
  }
  case 12: {
    uint64_t var206 = bin->length;
    span var207;
    if (1 <= var206) {
      span var208;
      take(bin, 1, &var208);
      var207 = var208;
    } else {
      return 0;
    }
    uint8_t var209;
    var209 = var207.pos[0];
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
    uint16_t var214 = ((((uint16_t)var209) << 8) | (var213));
    uint64_t var215 = bin->length;
    span var216;
    if (1 <= var215) {
      span var217;
      take(bin, 1, &var217);
      var216 = var217;
    } else {
      return 0;
    }
    uint8_t var218;
    var218 = var216.pos[0];
    uint64_t var219 = bin->length;
    span var220;
    if (1 <= var219) {
      span var221;
      take(bin, 1, &var221);
      var220 = var221;
    } else {
      return 0;
    }
    uint8_t var222;
    var222 = var220.pos[0];
    uint16_t var223 = ((((uint16_t)var218) << 8) | (var222));
    uint32_t var224 = ((((uint32_t)var214) << 16) | (var223));
    radius_attribute var225;
    create_FramedMTU(var224, &var225);
    var39 = var225;
    break;
  }
  case 8: {
    uint64_t var226 = bin->length;
    span var227;
    if (4 <= var226) {
      span var228;
      take(bin, 4, &var228);
      var227 = var228;
    } else {
      return 0;
    }
    option_span var247;
    var247.ok = true;
    var247.val = var227;
    radius_attribute var248;
    if (var247.ok) {
      span var249 = var247.val;
      if (!local2(&(var247.val), &var248))
        return 0;
      var247.val = var249;
    } else {
      span var249;
      get(bin, &var249);
      if (!local2(bin, &var248))
        return 0;
      set(bin, var249);
    }
    var39 = var248;
    break;
  }
  case 4: {
    uint64_t var250 = bin->length;
    span var251;
    if (4 <= var250) {
      span var252;
      take(bin, 4, &var252);
      var251 = var252;
    } else {
      return 0;
    }
    option_span var271;
    var271.ok = true;
    var271.val = var251;
    radius_attribute var272;
    if (var271.ok) {
      span var273 = var271.val;
      if (!local3(&(var271.val), &var272))
        return 0;
      var271.val = var273;
    } else {
      span var273;
      get(bin, &var273);
      if (!local3(bin, &var272))
        return 0;
      set(bin, var273);
    }
    var39 = var272;
    break;
  }
  case 2: {
    uint64_t var274 = bin->length;
    span var275;
    take(bin, var274, &var275);
    radius_attribute var276;
    create_UserPassword(var275, &var276);
    var39 = var276;
    break;
  }
  case 1: {
    uint64_t var277 = bin->length;
    span var278;
    take(bin, var277, &var278);
    radius_attribute var279;
    create_UserName(var278, &var279);
    var39 = var279;
    break;
  }
  default: {
    uint64_t var280 = bin->length;
    span var281;
    take(bin, var280, &var281);
    radius_attribute var282;
    create_Unknown(var30, var281, &var282);
    var39 = var282;
    break;
  }
  }

  *var284 = var39;
  return 1;
}

int local5(span *bin, radius_attribute *var375) {
  uint64_t var356 = bin->length;
  span var357;
  if (1 <= var356) {
    span var358;
    take(bin, 1, &var358);
    var357 = var358;
  } else {
    return 0;
  }
  uint8_t var359;
  var359 = var357.pos[0];
  uint64_t var360 = bin->length;
  span var361;
  if (1 <= var360) {
    span var362;
    take(bin, 1, &var362);
    var361 = var362;
  } else {
    return 0;
  }
  uint8_t var363;
  var363 = var361.pos[0];
  uint64_t var364 = bin->length;
  span var365;
  if (1 <= var364) {
    span var366;
    take(bin, 1, &var366);
    var365 = var366;
  } else {
    return 0;
  }
  uint8_t var367;
  var367 = var365.pos[0];
  uint64_t var368 = bin->length;
  span var369;
  if (1 <= var368) {
    span var370;
    take(bin, 1, &var370);
    var369 = var370;
  } else {
    return 0;
  }
  uint8_t var371;
  var371 = var369.pos[0];
  ipv4 var372;
  create_ipv4(var359, var363, var367, var371, &var372);
  radius_attribute var373;
  create_FramedIPNetmask(var372, &var373);
  *var375 = var373;
  return 1;
}

int local6(span *bin, radius_attribute *var515) {
  uint64_t var496 = bin->length;
  span var497;
  if (1 <= var496) {
    span var498;
    take(bin, 1, &var498);
    var497 = var498;
  } else {
    return 0;
  }
  uint8_t var499;
  var499 = var497.pos[0];
  uint64_t var500 = bin->length;
  span var501;
  if (1 <= var500) {
    span var502;
    take(bin, 1, &var502);
    var501 = var502;
  } else {
    return 0;
  }
  uint8_t var503;
  var503 = var501.pos[0];
  uint64_t var504 = bin->length;
  span var505;
  if (1 <= var504) {
    span var506;
    take(bin, 1, &var506);
    var505 = var506;
  } else {
    return 0;
  }
  uint8_t var507;
  var507 = var505.pos[0];
  uint64_t var508 = bin->length;
  span var509;
  if (1 <= var508) {
    span var510;
    take(bin, 1, &var510);
    var509 = var510;
  } else {
    return 0;
  }
  uint8_t var511;
  var511 = var509.pos[0];
  ipv4 var512;
  create_ipv4(var499, var503, var507, var511, &var512);
  radius_attribute var513;
  create_FramedIPAddress(var512, &var513);
  *var515 = var513;
  return 1;
}

int local7(span *bin, radius_attribute *var539) {
  uint64_t var520 = bin->length;
  span var521;
  if (1 <= var520) {
    span var522;
    take(bin, 1, &var522);
    var521 = var522;
  } else {
    return 0;
  }
  uint8_t var523;
  var523 = var521.pos[0];
  uint64_t var524 = bin->length;
  span var525;
  if (1 <= var524) {
    span var526;
    take(bin, 1, &var526);
    var525 = var526;
  } else {
    return 0;
  }
  uint8_t var527;
  var527 = var525.pos[0];
  uint64_t var528 = bin->length;
  span var529;
  if (1 <= var528) {
    span var530;
    take(bin, 1, &var530);
    var529 = var530;
  } else {
    return 0;
  }
  uint8_t var531;
  var531 = var529.pos[0];
  uint64_t var532 = bin->length;
  span var533;
  if (1 <= var532) {
    span var534;
    take(bin, 1, &var534);
    var533 = var534;
  } else {
    return 0;
  }
  uint8_t var535;
  var535 = var533.pos[0];
  ipv4 var536;
  create_ipv4(var523, var527, var531, var535, &var536);
  radius_attribute var537;
  create_NasIPAddress(var536, &var537);
  *var539 = var537;
  return 1;
}

int local8(span *bin, radius_attribute *var551, uint8_t var297) {
  radius_attribute var306;
  switch (var297) {

  case 31: {
    uint64_t var307 = bin->length;
    span var308;
    take(bin, var307, &var308);
    radius_attribute var309;
    create_CallingStationId(var308, &var309);
    var306 = var309;
    break;
  }
  case 11: {
    uint64_t var310 = bin->length;
    span var311;
    take(bin, var310, &var311);
    radius_attribute var312;
    create_FilterId(var311, &var312);
    var306 = var312;
    break;
  }
  case 7: {
    uint64_t var313 = bin->length;
    span var314;
    if (1 <= var313) {
      span var315;
      take(bin, 1, &var315);
      var314 = var315;
    } else {
      return 0;
    }
    uint8_t var316;
    var316 = var314.pos[0];
    uint64_t var317 = bin->length;
    span var318;
    if (1 <= var317) {
      span var319;
      take(bin, 1, &var319);
      var318 = var319;
    } else {
      return 0;
    }
    uint8_t var320;
    var320 = var318.pos[0];
    uint16_t var321 = ((((uint16_t)var316) << 8) | (var320));
    uint64_t var322 = bin->length;
    span var323;
    if (1 <= var322) {
      span var324;
      take(bin, 1, &var324);
      var323 = var324;
    } else {
      return 0;
    }
    uint8_t var325;
    var325 = var323.pos[0];
    uint64_t var326 = bin->length;
    span var327;
    if (1 <= var326) {
      span var328;
      take(bin, 1, &var328);
      var327 = var328;
    } else {
      return 0;
    }
    uint8_t var329;
    var329 = var327.pos[0];
    uint16_t var330 = ((((uint16_t)var325) << 8) | (var329));
    uint32_t var331 = ((((uint32_t)var321) << 16) | (var330));
    radius_attribute var332;
    create_Protocol(var331, &var332);
    var306 = var332;
    break;
  }
  case 13: {
    uint64_t var333 = bin->length;
    span var334;
    if (1 <= var333) {
      span var335;
      take(bin, 1, &var335);
      var334 = var335;
    } else {
      return 0;
    }
    uint8_t var336;
    var336 = var334.pos[0];
    uint64_t var337 = bin->length;
    span var338;
    if (1 <= var337) {
      span var339;
      take(bin, 1, &var339);
      var338 = var339;
    } else {
      return 0;
    }
    uint8_t var340;
    var340 = var338.pos[0];
    uint16_t var341 = ((((uint16_t)var336) << 8) | (var340));
    uint64_t var342 = bin->length;
    span var343;
    if (1 <= var342) {
      span var344;
      take(bin, 1, &var344);
      var343 = var344;
    } else {
      return 0;
    }
    uint8_t var345;
    var345 = var343.pos[0];
    uint64_t var346 = bin->length;
    span var347;
    if (1 <= var346) {
      span var348;
      take(bin, 1, &var348);
      var347 = var348;
    } else {
      return 0;
    }
    uint8_t var349;
    var349 = var347.pos[0];
    uint16_t var350 = ((((uint16_t)var345) << 8) | (var349));
    uint32_t var351 = ((((uint32_t)var341) << 16) | (var350));
    radius_attribute var352;
    create_Compression(var351, &var352);
    var306 = var352;
    break;
  }
  case 9: {
    uint64_t var353 = bin->length;
    span var354;
    if (4 <= var353) {
      span var355;
      take(bin, 4, &var355);
      var354 = var355;
    } else {
      return 0;
    }
    option_span var374;
    var374.ok = true;
    var374.val = var354;
    radius_attribute var375;
    if (var374.ok) {
      span var376 = var374.val;
      if (!local5(&(var374.val), &var375))
        return 0;
      var374.val = var376;
    } else {
      span var376;
      get(bin, &var376);
      if (!local5(bin, &var375))
        return 0;
      set(bin, var376);
    }
    var306 = var375;
    break;
  }
  case 5: {
    uint64_t var377 = bin->length;
    span var378;
    if (1 <= var377) {
      span var379;
      take(bin, 1, &var379);
      var378 = var379;
    } else {
      return 0;
    }
    uint8_t var380;
    var380 = var378.pos[0];
    uint64_t var381 = bin->length;
    span var382;
    if (1 <= var381) {
      span var383;
      take(bin, 1, &var383);
      var382 = var383;
    } else {
      return 0;
    }
    uint8_t var384;
    var384 = var382.pos[0];
    uint16_t var385 = ((((uint16_t)var380) << 8) | (var384));
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
    uint32_t var395 = ((((uint32_t)var385) << 16) | (var394));
    radius_attribute var396;
    create_NasPort(var395, &var396);
    var306 = var396;
    break;
  }
  case 3: {
    uint64_t var397 = bin->length;
    radius_attribute var398;
    if (var397 < 2) {
      return 0;
    } else {
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
      uint64_t var403 = bin->length;
      span var404;
      take(bin, var403, &var404);
      radius_attribute var405;
      create_ChapPassword(var402, var404, &var405);
      var398 = var405;
    }
    var306 = var398;
    break;
  }
  case 30: {
    uint64_t var406 = bin->length;
    span var407;
    take(bin, var406, &var407);
    radius_attribute var408;
    create_CalledStationId(var407, &var408);
    var306 = var408;
    break;
  }
  case 26: {
    uint64_t var409 = bin->length;
    radius_attribute var410;
    if (var409 < 5) {
      return 0;
    } else {
      uint64_t var411 = bin->length;
      span var412;
      if (1 <= var411) {
        span var413;
        take(bin, 1, &var413);
        var412 = var413;
      } else {
        return 0;
      }
      uint8_t var414;
      var414 = var412.pos[0];
      uint64_t var415 = bin->length;
      span var416;
      if (1 <= var415) {
        span var417;
        take(bin, 1, &var417);
        var416 = var417;
      } else {
        return 0;
      }
      uint8_t var418;
      var418 = var416.pos[0];
      uint16_t var419 = ((((uint16_t)var414) << 8) | (var418));
      uint64_t var420 = bin->length;
      span var421;
      if (1 <= var420) {
        span var422;
        take(bin, 1, &var422);
        var421 = var422;
      } else {
        return 0;
      }
      uint8_t var423;
      var423 = var421.pos[0];
      uint64_t var424 = bin->length;
      span var425;
      if (1 <= var424) {
        span var426;
        take(bin, 1, &var426);
        var425 = var426;
      } else {
        return 0;
      }
      uint8_t var427;
      var427 = var425.pos[0];
      uint16_t var428 = ((((uint16_t)var423) << 8) | (var427));
      uint32_t var429 = ((((uint32_t)var419) << 16) | (var428));
      uint64_t var430 = bin->length;
      span var431;
      take(bin, var430, &var431);
      radius_attribute var432;
      create_VendorSpecific(var429, var431, &var432);
      var410 = var432;
    }
    var306 = var410;
    break;
  }
  case 10: {
    uint64_t var433 = bin->length;
    span var434;
    if (1 <= var433) {
      span var435;
      take(bin, 1, &var435);
      var434 = var435;
    } else {
      return 0;
    }
    uint8_t var436;
    var436 = var434.pos[0];
    uint64_t var437 = bin->length;
    span var438;
    if (1 <= var437) {
      span var439;
      take(bin, 1, &var439);
      var438 = var439;
    } else {
      return 0;
    }
    uint8_t var440;
    var440 = var438.pos[0];
    uint16_t var441 = ((((uint16_t)var436) << 8) | (var440));
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
    uint64_t var446 = bin->length;
    span var447;
    if (1 <= var446) {
      span var448;
      take(bin, 1, &var448);
      var447 = var448;
    } else {
      return 0;
    }
    uint8_t var449;
    var449 = var447.pos[0];
    uint16_t var450 = ((((uint16_t)var445) << 8) | (var449));
    uint32_t var451 = ((((uint32_t)var441) << 16) | (var450));
    radius_attribute var452;
    create_Routing(var451, &var452);
    var306 = var452;
    break;
  }
  case 6: {
    uint64_t var453 = bin->length;
    span var454;
    if (1 <= var453) {
      span var455;
      take(bin, 1, &var455);
      var454 = var455;
    } else {
      return 0;
    }
    uint8_t var456;
    var456 = var454.pos[0];
    uint64_t var457 = bin->length;
    span var458;
    if (1 <= var457) {
      span var459;
      take(bin, 1, &var459);
      var458 = var459;
    } else {
      return 0;
    }
    uint8_t var460;
    var460 = var458.pos[0];
    uint16_t var461 = ((((uint16_t)var456) << 8) | (var460));
    uint64_t var462 = bin->length;
    span var463;
    if (1 <= var462) {
      span var464;
      take(bin, 1, &var464);
      var463 = var464;
    } else {
      return 0;
    }
    uint8_t var465;
    var465 = var463.pos[0];
    uint64_t var466 = bin->length;
    span var467;
    if (1 <= var466) {
      span var468;
      take(bin, 1, &var468);
      var467 = var468;
    } else {
      return 0;
    }
    uint8_t var469;
    var469 = var467.pos[0];
    uint16_t var470 = ((((uint16_t)var465) << 8) | (var469));
    uint32_t var471 = ((((uint32_t)var461) << 16) | (var470));
    radius_attribute var472;
    create_Service(var471, &var472);
    var306 = var472;
    break;
  }
  case 12: {
    uint64_t var473 = bin->length;
    span var474;
    if (1 <= var473) {
      span var475;
      take(bin, 1, &var475);
      var474 = var475;
    } else {
      return 0;
    }
    uint8_t var476;
    var476 = var474.pos[0];
    uint64_t var477 = bin->length;
    span var478;
    if (1 <= var477) {
      span var479;
      take(bin, 1, &var479);
      var478 = var479;
    } else {
      return 0;
    }
    uint8_t var480;
    var480 = var478.pos[0];
    uint16_t var481 = ((((uint16_t)var476) << 8) | (var480));
    uint64_t var482 = bin->length;
    span var483;
    if (1 <= var482) {
      span var484;
      take(bin, 1, &var484);
      var483 = var484;
    } else {
      return 0;
    }
    uint8_t var485;
    var485 = var483.pos[0];
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
    uint16_t var490 = ((((uint16_t)var485) << 8) | (var489));
    uint32_t var491 = ((((uint32_t)var481) << 16) | (var490));
    radius_attribute var492;
    create_FramedMTU(var491, &var492);
    var306 = var492;
    break;
  }
  case 8: {
    uint64_t var493 = bin->length;
    span var494;
    if (4 <= var493) {
      span var495;
      take(bin, 4, &var495);
      var494 = var495;
    } else {
      return 0;
    }
    option_span var514;
    var514.ok = true;
    var514.val = var494;
    radius_attribute var515;
    if (var514.ok) {
      span var516 = var514.val;
      if (!local6(&(var514.val), &var515))
        return 0;
      var514.val = var516;
    } else {
      span var516;
      get(bin, &var516);
      if (!local6(bin, &var515))
        return 0;
      set(bin, var516);
    }
    var306 = var515;
    break;
  }
  case 4: {
    uint64_t var517 = bin->length;
    span var518;
    if (4 <= var517) {
      span var519;
      take(bin, 4, &var519);
      var518 = var519;
    } else {
      return 0;
    }
    option_span var538;
    var538.ok = true;
    var538.val = var518;
    radius_attribute var539;
    if (var538.ok) {
      span var540 = var538.val;
      if (!local7(&(var538.val), &var539))
        return 0;
      var538.val = var540;
    } else {
      span var540;
      get(bin, &var540);
      if (!local7(bin, &var539))
        return 0;
      set(bin, var540);
    }
    var306 = var539;
    break;
  }
  case 2: {
    uint64_t var541 = bin->length;
    span var542;
    take(bin, var541, &var542);
    radius_attribute var543;
    create_UserPassword(var542, &var543);
    var306 = var543;
    break;
  }
  case 1: {
    uint64_t var544 = bin->length;
    span var545;
    take(bin, var544, &var545);
    radius_attribute var546;
    create_UserName(var545, &var546);
    var306 = var546;
    break;
  }
  default: {
    uint64_t var547 = bin->length;
    span var548;
    take(bin, var547, &var548);
    radius_attribute var549;
    create_Unknown(var297, var548, &var549);
    var306 = var549;
    break;
  }
  }

  *var551 = var306;
  return 1;
}

int fun_repeat1(span *bin, Vector_radius_attribute var289,
                Vector_radius_attribute *var292) {
  uint64_t var293 = bin->length;
  uint64_t var294 = bin->length;
  span var295;
  if (1 <= var294) {
    span var296;
    take(bin, 1, &var296);
    var295 = var296;
  } else {
    return 0;
  }
  uint8_t var297;
  var297 = var295.pos[0];
  uint64_t var298 = bin->length;
  span var299;
  if (1 <= var298) {
    span var300;
    take(bin, 1, &var300);
    var299 = var300;
  } else {
    return 0;
  }
  uint8_t var301;
  var301 = var299.pos[0];
  uint8_t var302;
  if (2 <= var301) {
    var302 = var301;
  } else {
    return 0;
  }
  uint64_t var303 = bin->length;
  span var304;
  if (var302 - 2 <= var303) {
    span var305;
    take(bin, var302 - 2, &var305);
    var304 = var305;
  } else {
    return 0;
  }
  option_span var550;
  var550.ok = true;
  var550.val = var304;
  radius_attribute var551;
  if (var550.ok) {
    span var552 = var550.val;
    if (!local8(&(var550.val), &var551, var297))
      return 0;
    var550.val = var552;
  } else {
    span var552;
    get(bin, &var552);
    if (!local8(bin, &var551, var297))
      return 0;
    set(bin, var552);
  }
  uint64_t var553 = bin->length;
  Vector_radius_attribute var554;
  if (var293 == var553) {
    return 0;
  } else {
    Vector_radius_attribute_add(&var289, var551);
    Vector_radius_attribute var555 = var289;
    var554 = var555;
  }
  *var292 = var554;
  return 1;
}

int repeat1(span *bin, option_uint64_t var288, Vector_radius_attribute var289,
            Vector_radius_attribute *var292) {
  if (var288.ok) {
    for (int v = 0; v < var288.val; v++) {
      var289 = *var292;
      if (!fun_repeat1(bin, var289, var292))
        return 0;
    }
    *var292 = var289;
  } else {
    while (true) {
      var289 = *var292;
      if (!fun_repeat1(bin, var289, var292)) {
        *var292 = var289;
        return 1;
      }
    }
  }
  return 1;
}

int local9(span *bin, Vector_radius_attribute *var557) {
  uint64_t var26 = bin->length;
  uint64_t var27 = bin->length;
  span var28;
  if (1 <= var27) {
    span var29;
    take(bin, 1, &var29);
    var28 = var29;
  } else {
    return 0;
  }
  uint8_t var30;
  var30 = var28.pos[0];
  uint64_t var31 = bin->length;
  span var32;
  if (1 <= var31) {
    span var33;
    take(bin, 1, &var33);
    var32 = var33;
  } else {
    return 0;
  }
  uint8_t var34;
  var34 = var32.pos[0];
  uint8_t var35;
  if (2 <= var34) {
    var35 = var34;
  } else {
    return 0;
  }
  uint64_t var36 = bin->length;
  span var37;
  if (var35 - 2 <= var36) {
    span var38;
    take(bin, var35 - 2, &var38);
    var37 = var38;
  } else {
    return 0;
  }
  option_span var283;
  var283.ok = true;
  var283.val = var37;
  radius_attribute var284;
  if (var283.ok) {
    span var285 = var283.val;
    if (!local4(&(var283.val), &var284, var30))
      return 0;
    var283.val = var285;
  } else {
    span var285;
    get(bin, &var285);
    if (!local4(bin, &var284, var30))
      return 0;
    set(bin, var285);
  }
  uint64_t var286 = bin->length;
  Vector_radius_attribute var287;
  if (var26 == var286) {
    return 0;
  } else {
    option_uint64_t var288;
    var288.ok = false;
    Vector_radius_attribute var291;
    Vector_radius_attribute_make(2, &var291);
    Vector_radius_attribute var290 = var291;
    Vector_radius_attribute_add(&var290, var284);
    Vector_radius_attribute var289 = var290;
    Vector_radius_attribute var292 = var289;
    if (!repeat1(bin, var288, var289, &var292))
      return 0;
    var287 = var292;
  }
  *var557 = var287;
  return 1;
}

int parse_radius(span *bin, radius_data *var1) {
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
  uint64_t var10 = bin->length;
  span var11;
  if (1 <= var10) {
    span var12;
    take(bin, 1, &var12);
    var11 = var12;
  } else {
    return 0;
  }
  uint8_t var13;
  var13 = var11.pos[0];
  uint64_t var14 = bin->length;
  span var15;
  if (1 <= var14) {
    span var16;
    take(bin, 1, &var16);
    var15 = var16;
  } else {
    return 0;
  }
  uint8_t var17;
  var17 = var15.pos[0];
  uint16_t var18 = ((((uint16_t)var13) << 8) | (var17));
  uint64_t var19 = bin->length;
  span var20;
  if (16 <= var19) {
    span var21;
    take(bin, 16, &var21);
    var20 = var21;
  } else {
    return 0;
  }
  option_Vector_radius_attribute var22;
  if (20 < var18) {
    uint64_t var23 = bin->length;
    span var24;
    if (var18 - 20 <= var23) {
      span var25;
      take(bin, var18 - 20, &var25);
      var24 = var25;
    } else {
      return 0;
    }
    option_span var556;
    var556.ok = true;
    var556.val = var24;
    Vector_radius_attribute var557;
    if (var556.ok) {
      span var558 = var556.val;
      if (!local9(&(var556.val), &var557))
        return 0;
      var556.val = var558;
    } else {
      span var558;
      get(bin, &var558);
      if (!local9(bin, &var557))
        return 0;
      set(bin, var558);
    }
    option_Vector_radius_attribute var560;
    var560.ok = true;
    var560.val = var557;
    option_Vector_radius_attribute var559 = var560;
    var22 = var559;
  } else {
    option_Vector_radius_attribute var562;
    var562.ok = false;
    option_Vector_radius_attribute var561 = var562;
    var22 = var561;
  }
  radius_data var563;
  create_RadiusData(var5, var9, var18, var20, var22, &var563);
  *var1 = var563;
  return 1;
}
