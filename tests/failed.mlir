module {
  func.func @predict_online_4(%arg0: tensor<?x50x17xf16>, %arg1: tensor<?x50x17xf16>, %arg2: tensor<?x50x17xf16>, %arg3: tensor<?x50x17xf16>, %arg4: tensor<?x50x49xf16>, %arg5: tensor<?x10x49xf16>, %arg6: tensor<?x50x33xf16>, %arg7: tensor<?x1x10xf32>, %arg8: tensor<?x1x60xf32>, %arg9: tensor<?x1x64xf32>, %arg10: tensor<?x1x50xf32>, %arg11: tensor<?x1x30xf32>, %arg12: tensor<?x1x50xf32>, %arg13: tensor<?x1x30xf32>, %arg14: tensor<?x1x50xf32>, %arg15: tensor<?x1x50xf32>, %arg16: tensor<?x1x30xf32>, %arg17: tensor<?x1x30xf32>, %arg18: tensor<?x50x16xf32>, %arg19: tensor<?x32xf32>, %arg20: tensor<?x32xf32>, %arg21: tensor<?x32xf32>, %arg22: tensor<?x16xf32>, %arg23: tensor<?x16xf32>, %arg24: tensor<?x8xf32>, %arg25: tensor<?x8xf32>, %arg26: tensor<?x16xf32>, %arg27: tensor<?x16xf32>, %arg28: tensor<?x16xf32>, %arg29: tensor<?x4xf32>, %arg30: tensor<?x4xf32>, %arg31: tensor<?x4xf32>, %arg32: tensor<?x4xf32>, %arg33: tensor<?x4xf32>, %arg34: tensor<?x4xf32>, %arg35: tensor<?x4xf32>, %arg36: tensor<?x4xf32>, %arg37: tensor<?x4xf32>, %arg38: tensor<?x4xf32>, %arg39: tensor<?x4xf32>, %arg40: tensor<284x128xf32>, %arg41: tensor<128xf32>, %arg42: tensor<128x167xf32>, %arg43: tensor<167xf32>, %arg44: tensor<?x167xf32>, %arg45: tensor<167x256xf32>, %arg46: tensor<256xf32>, %arg47: tensor<284x128xf32>, %arg48: tensor<128xf32>, %arg49: tensor<128x256xf32>, %arg50: tensor<256xf32>, %arg51: tensor<256x64xf32>, %arg52: tensor<64xf32>, %arg53: tensor<284x128xf32>, %arg54: tensor<128xf32>, %arg55: tensor<128x64xf32>, %arg56: tensor<64xf32>, %arg57: tensor<3x284x128xf32>, %arg58: tensor<3x1x128xf32>, %arg59: tensor<128x8821xf32>, %arg60: tensor<8821xf32>, %arg61: tensor<128x2439xf32>, %arg62: tensor<2439xf32>, %arg63: tensor<128x8821xf32>, %arg64: tensor<8821xf32>, %arg65: tensor<284x128xf32>, %arg66: tensor<128xf32>, %arg67: tensor<128x1669xf32>, %arg68: tensor<1669xf32>, %arg69: tensor<284x128xf32>, %arg70: tensor<128xf32>, %arg71: tensor<128x794xf32>, %arg72: tensor<794xf32>, %arg73: tensor<284x128xf32>, %arg74: tensor<128xf32>, %arg75: tensor<128x899xf32>, %arg76: tensor<899xf32>, %arg77: tensor<284x128xf32>, %arg78: tensor<128xf32>, %arg79: tensor<128x451xf32>, %arg80: tensor<451xf32>, %arg81: tensor<284x128xf32>, %arg82: tensor<128xf32>, %arg83: tensor<128x115xf32>, %arg84: tensor<115xf32>, %arg85: tensor<?x37x32xf32>, %arg86: tensor<?x37x32xf32>, %arg87: tensor<?x30x68xf32>, %arg88: tensor<?x30x104xf32>, %arg89: tensor<?x10x116xf32>, %arg90: tensor<1x1x116xf32>, %arg91: tensor<?x50x116xf32>, %arg92: tensor<?x26x50xf32>, %arg93: tensor<1x1x50xf32>, %arg94: tensor<?x116x50xf32>, %arg95: tensor<232x64xf32>, %arg96: tensor<64xf32>, %arg97: tensor<?x10x124xf32>, %arg98: tensor<1x1x124xf32>, %arg99: tensor<?x50x124xf32>, %arg100: tensor<?x28x50xf32>, %arg101: tensor<1x1x50xf32>, %arg102: tensor<?x124x50xf32>, %arg103: tensor<248x64xf32>, %arg104: tensor<64xf32>, %arg105: tensor<?x50x108xf32>, %arg106: tensor<?x5x124xf32>, %arg107: tensor<1x1x124xf32>, %arg108: tensor<?x30x124xf32>, %arg109: tensor<?x28x30xf32>, %arg110: tensor<1x1x30xf32>, %arg111: tensor<?x124x30xf32>, %arg112: tensor<248x64xf32>, %arg113: tensor<64xf32>, %arg114: tensor<?x60x88xf32>, %arg115: tensor<?x12x88xf32>, %arg116: tensor<1x1x88xf32>, %arg117: tensor<?x60x88xf32>, %arg118: tensor<?x19x60xf32>, %arg119: tensor<1x1x60xf32>, %arg120: tensor<?x88x60xf32>, %arg121: tensor<176x80xf32>, %arg122: tensor<80xf32>, %arg123: tensor<?x13x128xf32>, %arg124: tensor<1x1x128xf32>, %arg125: tensor<?x64x128xf32>, %arg126: tensor<?x29x64xf32>, %arg127: tensor<1x1x64xf32>, %arg128: tensor<?x128x64xf32>, %arg129: tensor<256x80xf32>, %arg130: tensor<80xf32>, %arg131: tensor<?x30x32xf32>, %arg132: tensor<?x1x32xf32>, %arg133: tensor<?x30x32xf32>, %arg134: tensor<?x50x32xf32>, %arg135: tensor<?x1x32xf32>, %arg136: tensor<?x50x32xf32>, %arg137: tensor<?x30x32xf32>, %arg138: tensor<?x1x32xf32>, %arg139: tensor<?x30x32xf32>, %arg140: tensor<?x50x32xf32>, %arg141: tensor<?x1x32xf32>, %arg142: tensor<?x50x32xf32>, %arg143: tensor<?x10x32xf32>, %arg144: tensor<?x1x32xf32>, %arg145: tensor<?x10x32xf32>, %arg146: tensor<?x1x64xf32>, %arg147: tensor<?x60x64xf32>, %arg148: tensor<110x128xf32>, %arg149: tensor<128xf32>, %arg150: tensor<128x64xf32>, %arg151: tensor<64xf32>, %arg152: tensor<64x64xf32>, %arg153: tensor<64xf32>, %arg154: tensor<64x32xf32>, %arg155: tensor<32xf32>, %arg156: tensor<90x128xf32>, %arg157: tensor<128xf32>, %arg158: tensor<128x64xf32>, %arg159: tensor<64xf32>, %arg160: tensor<64x64xf32>, %arg161: tensor<64xf32>, %arg162: tensor<64x32xf32>, %arg163: tensor<32xf32>, %arg164: tensor<?x60x64xf32>, %arg165: tensor<?x60x24xf32>, %arg166: tensor<?x60x24xf32>, %arg167: tensor<?x1x24xf32>, %arg168: tensor<?x1x24xf32>, %arg169: tensor<?x60x24xf32>, %arg170: tensor<?x60x24xf32>, %arg171: tensor<?x60x12xf32>, %arg172: tensor<?x60x12xf32>, %arg173: tensor<?x1x12xf32>, %arg174: tensor<?x1x12xf32>, %arg175: tensor<?x60x12xf32>, %arg176: tensor<?x60x12xf32>, %arg177: tensor<?x60x6xf32>, %arg178: tensor<?x60x6xf32>, %arg179: tensor<?x1x6xf32>, %arg180: tensor<?x1x6xf32>, %arg181: tensor<?x60x6xf32>, %arg182: tensor<?x60x6xf32>, %arg183: tensor<?x1x512xf32>, %arg184: tensor<?x1x512xf32>, %arg185: tensor<?x64x24xf32>, %arg186: tensor<?x64x24xf32>, %arg187: tensor<?x1x24xf32>, %arg188: tensor<?x1x24xf32>, %arg189: tensor<?x64x24xf32>, %arg190: tensor<?x64x24xf32>, %arg191: tensor<?x64x12xf32>, %arg192: tensor<?x64x12xf32>, %arg193: tensor<?x1x12xf32>, %arg194: tensor<?x1x12xf32>, %arg195: tensor<?x64x12xf32>, %arg196: tensor<?x64x12xf32>, %arg197: tensor<?x64x6xf32>, %arg198: tensor<?x64x6xf32>, %arg199: tensor<?x1x6xf32>, %arg200: tensor<?x1x6xf32>, %arg201: tensor<?x64x6xf32>, %arg202: tensor<?x64x6xf32>, %arg203: tensor<?x1x64xf32>, %arg204: tensor<?x64x64xf32>, %arg205: tensor<114x128xf32>, %arg206: tensor<128xf32>, %arg207: tensor<128x64xf32>, %arg208: tensor<64xf32>, %arg209: tensor<64x64xf32>, %arg210: tensor<64xf32>, %arg211: tensor<64x32xf32>, %arg212: tensor<32xf32>, %arg213: tensor<94x128xf32>, %arg214: tensor<128xf32>, %arg215: tensor<128x64xf32>, %arg216: tensor<64xf32>, %arg217: tensor<64x64xf32>, %arg218: tensor<64xf32>, %arg219: tensor<64x32xf32>, %arg220: tensor<32xf32>, %arg221: tensor<?x64x64xf32>, %arg222: tensor<?x64x32xf32>, %arg223: tensor<?x64x32xf32>, %arg224: tensor<?x1x32xf32>, %arg225: tensor<?x1x32xf32>, %arg226: tensor<?x64x32xf32>, %arg227: tensor<?x64x32xf32>, %arg228: tensor<?x30x32xf32>, %arg229: tensor<?x1x32xf32>, %arg230: tensor<?x30x32xf32>, %arg231: tensor<?x50x32xf32>, %arg232: tensor<?x1x32xf32>, %arg233: tensor<?x50x32xf32>, %arg234: tensor<?x50x16xf32>, %arg235: tensor<?x1x16xf32>, %arg236: tensor<?x50x16xf32>, %arg237: tensor<?x50x8xf32>, %arg238: tensor<?x1x8xf32>, %arg239: tensor<?x50x8xf32>, %arg240: tensor<?x50x64xf32>, %arg241: tensor<?x1x64xf32>, %arg242: tensor<100x128xf32>, %arg243: tensor<128xf32>, %arg244: tensor<128x64xf32>, %arg245: tensor<64xf32>, %arg246: tensor<64x64xf32>, %arg247: tensor<64xf32>, %arg248: tensor<64x32xf32>, %arg249: tensor<32xf32>, %arg250: tensor<80x128xf32>, %arg251: tensor<128xf32>, %arg252: tensor<128x64xf32>, %arg253: tensor<64xf32>, %arg254: tensor<64x64xf32>, %arg255: tensor<64xf32>, %arg256: tensor<64x32xf32>, %arg257: tensor<32xf32>, %arg258: tensor<?x50x64xf32>, %arg259: tensor<?x30x32xf32>, %arg260: tensor<?x1x32xf32>, %arg261: tensor<?x30x32xf32>, %arg262: tensor<?x30x16xf32>, %arg263: tensor<?x1x16xf32>, %arg264: tensor<?x30x16xf32>, %arg265: tensor<?x30x8xf32>, %arg266: tensor<?x1x8xf32>, %arg267: tensor<?x30x8xf32>, %arg268: tensor<?x30x64xf32>, %arg269: tensor<?x1x64xf32>, %arg270: tensor<?x30x64xf32>, %arg271: tensor<?x50x32xf32>, %arg272: tensor<?x1x32xf32>, %arg273: tensor<?x50x32xf32>, %arg274: tensor<?x50x16xf32>, %arg275: tensor<?x1x16xf32>, %arg276: tensor<?x50x16xf32>, %arg277: tensor<?x50x8xf32>, %arg278: tensor<?x1x8xf32>, %arg279: tensor<?x50x8xf32>, %arg280: tensor<?x50x64xf32>, %arg281: tensor<?x1x64xf32>, %arg282: tensor<?x50x64xf32>, %arg283: tensor<?x11x16xf32>, %arg284: tensor<?x10x16xf32>, %arg285: tensor<?x11x16xf32>, %arg286: tensor<?x10x16xf32>, %arg287: tensor<?x13x16xf32>, %arg288: tensor<?x12x16xf32>, %arg289: tensor<?x16x5xf32>, %arg290: tensor<?x16x4xf32>, %arg291: tensor<?x16x4xf32>, %arg292: tensor<?x64xf32>, %arg293: tensor<?x64xf32>, %arg294: tensor<?x64xf32>, %arg295: tensor<?x64xf32>, %arg296: tensor<?x64xf32>, %arg297: tensor<?x64xf32>, %arg298: tensor<?x32xf32>, %arg299: tensor<?x32xf32>, %arg300: tensor<?x32xf32>, %arg301: tensor<?x180xf32>, %arg302: tensor<?x16xf32>, %arg303: tensor<?x32xf32>, %arg304: tensor<?x16xf32>, %arg305: tensor<?x4xf32>, %arg306: tensor<?x8xf32>, %arg307: tensor<?x4xf32>, %arg308: tensor<?x4xf32>, %arg309: tensor<?x4xf32>, %arg310: tensor<?x4xf32>, %arg311: tensor<?x4xf32>, %arg312: tensor<?x4xf32>, %arg313: tensor<?x8xf32>, %arg314: tensor<?x4xf32>, %arg315: tensor<?x8xf32>, %arg316: tensor<?x8xf32>, %arg317: tensor<?x4xf32>, %arg318: tensor<?x4xf32>, %arg319: tensor<?x4xf32>, %arg320: tensor<?x4xf32>, %arg321: tensor<?x4xf32>, %arg322: tensor<?x4xf32>, %arg323: tensor<?x4xf32>, %arg324: tensor<?x8xf32>, %arg325: tensor<?x8xf32>, %arg326: tensor<?x8xf32>, %arg327: tensor<?x4xf32>, %arg328: tensor<?x8xf32>, %arg329: tensor<?x8xf32>, %arg330: tensor<?x4xf32>, %arg331: tensor<?x8xf32>, %arg332: tensor<?x8xf32>, %arg333: tensor<?x8xf32>, %arg334: tensor<?x8xf32>, %arg335: tensor<?x4xf32>, %arg336: tensor<?x8xf32>, %arg337: tensor<?x4xf32>, %arg338: tensor<?x4xf32>, %arg339: tensor<?x8xf32>, %arg340: tensor<?x4xf32>, %arg341: tensor<?x4xf32>, %arg342: tensor<?x16xf32>, %arg343: tensor<?x16xf32>, %arg344: tensor<?x16xf32>, %arg345: tensor<?x32xf32>, %arg346: tensor<?x32xf32>, %arg347: tensor<?x32xf32>, %arg348: tensor<?x32xf32>, %arg349: tensor<?x4xf32>, %arg350: tensor<?x4xf32>, %arg351: tensor<?x4xf32>, %arg352: tensor<?x4xf32>, %arg353: tensor<?x4xf32>, %arg354: tensor<?x4xf32>, %arg355: tensor<?x4xf32>, %arg356: tensor<?x4xf32>, %arg357: tensor<?x4xf32>, %arg358: tensor<?x4xf32>, %arg359: tensor<?x4xf32>, %arg360: tensor<?x4xf32>, %arg361: tensor<?x4xf32>, %arg362: tensor<?x4xf32>, %arg363: tensor<?x8xf32>, %arg364: tensor<?x8xf32>, %arg365: tensor<?x8xf32>, %arg366: tensor<?x8xf32>, %arg367: tensor<?x8xf32>, %arg368: tensor<?x8xf32>, %arg369: tensor<?x8xf32>, %arg370: tensor<?x76xf32>, %arg371: tensor<?x4xf32>, %arg372: tensor<?x4xf32>, %arg373: tensor<?x4xf32>, %arg374: tensor<?x4xf32>, %arg375: tensor<?x8xf32>, %arg376: tensor<?x8xf32>, %arg377: tensor<?x8xf32>, %arg378: tensor<?x8xf32>, %arg379: tensor<?x8xf32>, %arg380: tensor<?x4xf32>, %arg381: tensor<?x4xf32>, %arg382: tensor<?x4xf32>, %arg383: tensor<?x4xf32>, %arg384: tensor<?x4xf32>, %arg385: tensor<?x4xf32>, %arg386: tensor<?x8xf32>, %arg387: tensor<?x8xf32>, %arg388: tensor<?x8xf32>, %arg389: tensor<?x8xf32>, %arg390: tensor<?x8xf32>, %arg391: tensor<?x8xf32>, %arg392: tensor<?x8xf32>, %arg393: tensor<?x8xf32>, %arg394: tensor<?x8xf32>, %arg395: tensor<?x8xf32>, %arg396: tensor<?x8xf32>, %arg397: tensor<?x8xf32>, %arg398: tensor<?x8xf32>, %arg399: tensor<?x8xf32>, %arg400: tensor<?x8xf32>, %arg401: tensor<?x8xf32>, %arg402: tensor<?x8xf32>, %arg403: tensor<?x8xf32>, %arg404: tensor<?x8xf32>, %arg405: tensor<?x8xf32>, %arg406: tensor<?x8xf32>, %arg407: tensor<?x8xf32>, %arg408: tensor<?x8xf32>, %arg409: tensor<?x8xf32>, %arg410: tensor<?x8xf32>, %arg411: tensor<?x8xf32>, %arg412: tensor<?x8xf32>, %arg413: tensor<?x16xf32>, %arg414: tensor<?x48xf32>, %arg415: tensor<?x16xf32>, %arg416: tensor<?x16xf32>, %arg417: tensor<?x8xf32>, %arg418: tensor<?x8xf32>, %arg419: tensor<?x8xf32>, %arg420: tensor<?x8xf32>, %arg421: tensor<?x8xf32>, %arg422: tensor<?x8xf32>, %arg423: tensor<?x8xf32>, %arg424: tensor<?x8xf32>, %arg425: tensor<?x8xf32>, %arg426: tensor<?x8xf32>, %arg427: tensor<?x8xf32>, %arg428: tensor<?x8xf32>, %arg429: tensor<?x8xf32>, %arg430: tensor<?x8xf32>, %arg431: tensor<?x8xf32>, %arg432: tensor<?x8xf32>, %arg433: tensor<?x8xf32>, %arg434: tensor<?x8xf32>, %arg435: tensor<?x8xf32>, %arg436: tensor<?x8xf32>, %arg437: tensor<?x8xf32>, %arg438: tensor<?x8xf32>, %arg439: tensor<?x8xf32>, %arg440: tensor<?x8xf32>, %arg441: tensor<?x8xf32>, %arg442: tensor<?x8xf32>, %arg443: tensor<?x8xf32>, %arg444: tensor<?x8xf32>, %arg445: tensor<?x48xf32>, %arg446: tensor<?x48xf32>, %arg447: tensor<?x92xf32>, %arg448: tensor<?x64xf32>, %arg449: tensor<?x48xf32>, %arg450: tensor<?x48xf32>, %arg451: tensor<?x48xf32>, %arg452: tensor<?x16xf32>, %arg453: tensor<?x32xf32>, %arg454: tensor<?x32xf32>, %arg455: tensor<?x16xf32>, %arg456: tensor<?x4xf32>, %arg457: tensor<?x8xf32>, %arg458: tensor<?x4xf32>, %arg459: tensor<?x4xf32>, %arg460: tensor<?x4xf32>, %arg461: tensor<?x4xf32>, %arg462: tensor<?x4xf32>, %arg463: tensor<?x4xf32>, %arg464: tensor<?x8xf32>, %arg465: tensor<?x4xf32>, %arg466: tensor<?x8xf32>, %arg467: tensor<?x8xf32>, %arg468: tensor<?x4xf32>, %arg469: tensor<?x4xf32>, %arg470: tensor<?x4xf32>, %arg471: tensor<?x4xf32>, %arg472: tensor<?x4xf32>, %arg473: tensor<?x4xf32>, %arg474: tensor<?x4xf32>, %arg475: tensor<?x8xf32>, %arg476: tensor<?x8xf32>, %arg477: tensor<?x8xf32>, %arg478: tensor<?x4xf32>, %arg479: tensor<?x8xf32>, %arg480: tensor<?x8xf32>, %arg481: tensor<?x4xf32>, %arg482: tensor<?x8xf32>, %arg483: tensor<?x8xf32>, %arg484: tensor<?x8xf32>, %arg485: tensor<?x8xf32>, %arg486: tensor<?x4xf32>, %arg487: tensor<?x8xf32>, %arg488: tensor<?x4xf32>, %arg489: tensor<?x4xf32>, %arg490: tensor<?x8xf32>, %arg491: tensor<?x4xf32>, %arg492: tensor<?x4xf32>, %arg493: tensor<?x16xf32>, %arg494: tensor<?x16xf32>, %arg495: tensor<?x16xf32>, %arg496: tensor<?x16xf32>, %arg497: tensor<?x16xf32>, %arg498: tensor<?x16xf32>, %arg499: tensor<?x16xf32>, %arg500: tensor<?x16xf32>, %arg501: tensor<?x8xf32>, %arg502: tensor<?x96xf32>, %arg503: tensor<?x96xf32>, %arg504: tensor<?x96xf32>, %arg505: tensor<?x128xf32>, %arg506: tensor<?x128xf32>, %arg507: tensor<?x128xf32>, %arg508: tensor<?x128xf32>, %arg509: tensor<?x128xf32>, %arg510: tensor<?x128xf32>, %arg511: tensor<?x120xf32>, %arg512: tensor<5x8821x348xf32>, %arg513: tensor<5x1x348xf32>, %arg514: tensor<348x348xf32>, %arg515: tensor<1x348xf32>, %arg516: tensor<5x2439x238xf32>, %arg517: tensor<5x1x238xf32>, %arg518: tensor<238x238xf32>, %arg519: tensor<1x238xf32>, %arg520: tensor<5x1669x113xf32>, %arg521: tensor<5x1x113xf32>, %arg522: tensor<113x113xf32>, %arg523: tensor<1x113xf32>, %arg524: tensor<794x452xf32>, %arg525: tensor<452xf32>, %arg526: tensor<5x8821x128xf32>, %arg527: tensor<5x1x128xf32>, %arg528: tensor<128x128xf32>, %arg529: tensor<1x128xf32>, %arg530: tensor<5x899x64xf32>, %arg531: tensor<5x1x64xf32>, %arg532: tensor<64x64xf32>, %arg533: tensor<1x64xf32>, %arg534: tensor<5x451x16xf32>, %arg535: tensor<5x1x16xf32>, %arg536: tensor<16x16xf32>, %arg537: tensor<1x16xf32>, %arg538: tensor<115x64xf32>, %arg539: tensor<64xf32>, %arg540: tensor<?x1xf32>, %arg541: tensor<14x129x64xf32>, %arg542: tensor<14x1x64xf32>, %arg543: tensor<8821x2592xf32>, %arg544: tensor<2592xf32>) -> (tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x2592xf32>, tensor<?x3408xf32>) attributes {SimpleFusion, _symbolic_batch_dim = {"operand#0" = [1], "operand#1" = [1], "operand#10" = [1], "operand#100" = [1], "operand#101" = [], "operand#102" = [1], "operand#103" = [], "operand#104" = [], "operand#105" = [1], "operand#106" = [1], "operand#107" = [], "operand#108" = [1], "operand#109" = [1], "operand#11" = [1], "operand#110" = [], "operand#111" = [1], "operand#112" = [], "operand#113" = [], "operand#114" = [1], "operand#115" = [1], "operand#116" = [], "operand#117" = [1], "operand#118" = [1], "operand#119" = [], "operand#12" = [1], "operand#120" = [1], "operand#121" = [], "operand#122" = [], "operand#123" = [1], "operand#124" = [], "operand#125" = [1], "operand#126" = [1], "operand#127" = [], "operand#128" = [1], "operand#129" = [], "operand#13" = [1], "operand#130" = [], "operand#131" = [1], "operand#132" = [1], "operand#133" = [1], "operand#134" = [1], "operand#135" = [1], "operand#136" = [1], "operand#137" = [1], "operand#138" = [1], "operand#139" = [1], "operand#14" = [1], "operand#140" = [1], "operand#141" = [1], "operand#142" = [1], "operand#143" = [1], "operand#144" = [1], "operand#145" = [1], "operand#146" = [1], "operand#147" = [1], "operand#148" = [], "operand#149" = [], "operand#15" = [1], "operand#150" = [], "operand#151" = [], "operand#152" = [], "operand#153" = [], "operand#154" = [], "operand#155" = [], "operand#156" = [], "operand#157" = [], "operand#158" = [], "operand#159" = [], "operand#16" = [1], "operand#160" = [], "operand#161" = [], "operand#162" = [], "operand#163" = [], "operand#164" = [1], "operand#165" = [1], "operand#166" = [1], "operand#167" = [1], "operand#168" = [1], "operand#169" = [1], "operand#17" = [1], "operand#170" = [1], "operand#171" = [1], "operand#172" = [1], "operand#173" = [1], "operand#174" = [1], "operand#175" = [1], "operand#176" = [1], "operand#177" = [1], "operand#178" = [1], "operand#179" = [1], "operand#18" = [1], "operand#180" = [1], "operand#181" = [1], "operand#182" = [1], "operand#183" = [1], "operand#184" = [1], "operand#185" = [1], "operand#186" = [1], "operand#187" = [1], "operand#188" = [1], "operand#189" = [1], "operand#19" = [1], "operand#190" = [1], "operand#191" = [1], "operand#192" = [1], "operand#193" = [1], "operand#194" = [1], "operand#195" = [1], "operand#196" = [1], "operand#197" = [1], "operand#198" = [1], "operand#199" = [1], "operand#2" = [1], "operand#20" = [1], "operand#200" = [1], "operand#201" = [1], "operand#202" = [1], "operand#203" = [1], "operand#204" = [1], "operand#205" = [], "operand#206" = [], "operand#207" = [], "operand#208" = [], "operand#209" = [], "operand#21" = [1], "operand#210" = [], "operand#211" = [], "operand#212" = [], "operand#213" = [], "operand#214" = [], "operand#215" = [], "operand#216" = [], "operand#217" = [], "operand#218" = [], "operand#219" = [], "operand#22" = [1], "operand#220" = [], "operand#221" = [1], "operand#222" = [1], "operand#223" = [1], "operand#224" = [1], "operand#225" = [1], "operand#226" = [1], "operand#227" = [1], "operand#228" = [1], "operand#229" = [1], "operand#23" = [1], "operand#230" = [1], "operand#231" = [1], "operand#232" = [1], "operand#233" = [1], "operand#234" = [1], "operand#235" = [1], "operand#236" = [1], "operand#237" = [1], "operand#238" = [1], "operand#239" = [1], "operand#24" = [1], "operand#240" = [1], "operand#241" = [1], "operand#242" = [], "operand#243" = [], "operand#244" = [], "operand#245" = [], "operand#246" = [], "operand#247" = [], "operand#248" = [], "operand#249" = [], "operand#25" = [1], "operand#250" = [], "operand#251" = [], "operand#252" = [], "operand#253" = [], "operand#254" = [], "operand#255" = [], "operand#256" = [], "operand#257" = [], "operand#258" = [1], "operand#259" = [1], "operand#26" = [1], "operand#260" = [1], "operand#261" = [1], "operand#262" = [1], "operand#263" = [1], "operand#264" = [1], "operand#265" = [1], "operand#266" = [1], "operand#267" = [1], "operand#268" = [1], "operand#269" = [1], "operand#27" = [1], "operand#270" = [1], "operand#271" = [1], "operand#272" = [1], "operand#273" = [1], "operand#274" = [1], "operand#275" = [1], "operand#276" = [1], "operand#277" = [1], "operand#278" = [1], "operand#279" = [1], "operand#28" = [1], "operand#280" = [1], "operand#281" = [1], "operand#282" = [1], "operand#283" = [1], "operand#284" = [1], "operand#285" = [1], "operand#286" = [1], "operand#287" = [1], "operand#288" = [1], "operand#289" = [1], "operand#29" = [1], "operand#290" = [1], "operand#291" = [1], "operand#292" = [1], "operand#293" = [1], "operand#294" = [1], "operand#295" = [1], "operand#296" = [1], "operand#297" = [1], "operand#298" = [1], "operand#299" = [1], "operand#3" = [1], "operand#30" = [1], "operand#300" = [1], "operand#301" = [1], "operand#302" = [1], "operand#303" = [1], "operand#304" = [1], "operand#305" = [1], "operand#306" = [1], "operand#307" = [1], "operand#308" = [1], "operand#309" = [1], "operand#31" = [1], "operand#310" = [1], "operand#311" = [1], "operand#312" = [1], "operand#313" = [1], "operand#314" = [1], "operand#315" = [1], "operand#316" = [1], "operand#317" = [1], "operand#318" = [1], "operand#319" = [1], "operand#32" = [1], "operand#320" = [1], "operand#321" = [1], "operand#322" = [1], "operand#323" = [1], "operand#324" = [1], "operand#325" = [1], "operand#326" = [1], "operand#327" = [1], "operand#328" = [1], "operand#329" = [1], "operand#33" = [1], "operand#330" = [1], "operand#331" = [1], "operand#332" = [1], "operand#333" = [1], "operand#334" = [1], "operand#335" = [1], "operand#336" = [1], "operand#337" = [1], "operand#338" = [1], "operand#339" = [1], "operand#34" = [1], "operand#340" = [1], "operand#341" = [1], "operand#342" = [1], "operand#343" = [1], "operand#344" = [1], "operand#345" = [1], "operand#346" = [1], "operand#347" = [1], "operand#348" = [1], "operand#349" = [1], "operand#35" = [1], "operand#350" = [1], "operand#351" = [1], "operand#352" = [1], "operand#353" = [1], "operand#354" = [1], "operand#355" = [1], "operand#356" = [1], "operand#357" = [1], "operand#358" = [1], "operand#359" = [1], "operand#36" = [1], "operand#360" = [1], "operand#361" = [1], "operand#362" = [1], "operand#363" = [1], "operand#364" = [1], "operand#365" = [1], "operand#366" = [1], "operand#367" = [1], "operand#368" = [1], "operand#369" = [1], "operand#37" = [1], "operand#370" = [1], "operand#371" = [1], "operand#372" = [1], "operand#373" = [1], "operand#374" = [1], "operand#375" = [1], "operand#376" = [1], "operand#377" = [1], "operand#378" = [1], "operand#379" = [1], "operand#38" = [1], "operand#380" = [1], "operand#381" = [1], "operand#382" = [1], "operand#383" = [1], "operand#384" = [1], "operand#385" = [1], "operand#386" = [1], "operand#387" = [1], "operand#388" = [1], "operand#389" = [1], "operand#39" = [1], "operand#390" = [1], "operand#391" = [1], "operand#392" = [1], "operand#393" = [1], "operand#394" = [1], "operand#395" = [1], "operand#396" = [1], "operand#397" = [1], "operand#398" = [1], "operand#399" = [1], "operand#4" = [1], "operand#40" = [], "operand#400" = [1], "operand#401" = [1], "operand#402" = [1], "operand#403" = [1], "operand#404" = [1], "operand#405" = [1], "operand#406" = [1], "operand#407" = [1], "operand#408" = [1], "operand#409" = [1], "operand#41" = [], "operand#410" = [1], "operand#411" = [1], "operand#412" = [1], "operand#413" = [1], "operand#414" = [1], "operand#415" = [1], "operand#416" = [1], "operand#417" = [1], "operand#418" = [1], "operand#419" = [1], "operand#42" = [], "operand#420" = [1], "operand#421" = [1], "operand#422" = [1], "operand#423" = [1], "operand#424" = [1], "operand#425" = [1], "operand#426" = [1], "operand#427" = [1], "operand#428" = [1], "operand#429" = [1], "operand#43" = [], "operand#430" = [1], "operand#431" = [1], "operand#432" = [1], "operand#433" = [1], "operand#434" = [1], "operand#435" = [1], "operand#436" = [1], "operand#437" = [1], "operand#438" = [1], "operand#439" = [1], "operand#44" = [1], "operand#440" = [1], "operand#441" = [1], "operand#442" = [1], "operand#443" = [1], "operand#444" = [1], "operand#445" = [1], "operand#446" = [1], "operand#447" = [1], "operand#448" = [1], "operand#449" = [1], "operand#45" = [], "operand#450" = [1], "operand#451" = [1], "operand#452" = [1], "operand#453" = [1], "operand#454" = [1], "operand#455" = [1], "operand#456" = [1], "operand#457" = [1], "operand#458" = [1], "operand#459" = [1], "operand#46" = [], "operand#460" = [1], "operand#461" = [1], "operand#462" = [1], "operand#463" = [1], "operand#464" = [1], "operand#465" = [1], "operand#466" = [1], "operand#467" = [1], "operand#468" = [1], "operand#469" = [1], "operand#47" = [], "operand#470" = [1], "operand#471" = [1], "operand#472" = [1], "operand#473" = [1], "operand#474" = [1], "operand#475" = [1], "operand#476" = [1], "operand#477" = [1], "operand#478" = [1], "operand#479" = [1], "operand#48" = [], "operand#480" = [1], "operand#481" = [1], "operand#482" = [1], "operand#483" = [1], "operand#484" = [1], "operand#485" = [1], "operand#486" = [1], "operand#487" = [1], "operand#488" = [1], "operand#489" = [1], "operand#49" = [], "operand#490" = [1], "operand#491" = [1], "operand#492" = [1], "operand#493" = [1], "operand#494" = [1], "operand#495" = [1], "operand#496" = [1], "operand#497" = [1], "operand#498" = [1], "operand#499" = [1], "operand#5" = [1], "operand#50" = [], "operand#500" = [1], "operand#501" = [1], "operand#502" = [1], "operand#503" = [1], "operand#504" = [1], "operand#505" = [1], "operand#506" = [1], "operand#507" = [1], "operand#508" = [1], "operand#509" = [1], "operand#51" = [], "operand#510" = [1], "operand#511" = [], "operand#512" = [], "operand#513" = [], "operand#514" = [], "operand#515" = [], "operand#516" = [], "operand#517" = [], "operand#518" = [], "operand#519" = [], "operand#52" = [], "operand#520" = [], "operand#521" = [], "operand#522" = [], "operand#523" = [], "operand#524" = [], "operand#525" = [], "operand#526" = [], "operand#527" = [], "operand#528" = [], "operand#529" = [], "operand#53" = [], "operand#530" = [], "operand#531" = [], "operand#532" = [], "operand#533" = [], "operand#534" = [], "operand#535" = [], "operand#536" = [], "operand#537" = [], "operand#538" = [], "operand#539" = [], "operand#54" = [], "operand#540" = [1], "operand#541" = [], "operand#542" = [], "operand#543" = [], "operand#544" = [], "operand#55" = [], "operand#56" = [], "operand#57" = [], "operand#58" = [], "operand#59" = [], "operand#6" = [1], "operand#60" = [], "operand#61" = [], "operand#62" = [], "operand#63" = [], "operand#64" = [], "operand#65" = [], "operand#66" = [], "operand#67" = [], "operand#68" = [], "operand#69" = [], "operand#7" = [1], "operand#70" = [], "operand#71" = [], "operand#72" = [], "operand#73" = [], "operand#74" = [], "operand#75" = [], "operand#76" = [], "operand#77" = [], "operand#78" = [], "operand#79" = [], "operand#8" = [1], "operand#80" = [], "operand#81" = [], "operand#82" = [], "operand#83" = [], "operand#84" = [], "operand#85" = [1], "operand#86" = [1], "operand#87" = [1], "operand#88" = [1], "operand#89" = [1], "operand#9" = [1], "operand#90" = [], "operand#91" = [1], "operand#92" = [1], "operand#93" = [], "operand#94" = [1], "operand#95" = [], "operand#96" = [], "operand#97" = [1], "operand#98" = [], "operand#99" = [1]}} {
    %c = stablehlo.constant dense<[[0, 0], [0, 15]]> : tensor<2x2xi32>
    %cst = stablehlo.constant dense<0.176776692> : tensor<f32>
    %cst_0 = stablehlo.constant dense<2.000000e-01> : tensor<f32>
    %cst_1 = stablehlo.constant dense<0.408248276> : tensor<f32>
    %cst_2 = stablehlo.constant dense<0.353553385> : tensor<f32>
    %cst_3 = stablehlo.constant dense<0.288675129> : tensor<f32>
    %cst_4 = stablehlo.constant dense<2.500000e-01> : tensor<f32>
    %cst_5 = stablehlo.constant dense<0.204124138> : tensor<f32>
    %cst_6 = stablehlo.constant dense<1.250000e-01> : tensor<f32>
    %c_7 = stablehlo.constant dense<[[0, 0], [24, 24], [0, 0]]> : tensor<3x2xi32>
    %c_8 = stablehlo.constant dense<[[0, 0], [34, 35], [0, 0]]> : tensor<3x2xi32>
    %c_9 = stablehlo.constant dense<[[0, 0], [25, 26], [0, 0]]> : tensor<3x2xi32>
    %c_10 = stablehlo.constant dense<[[0, 0], [49, 50], [0, 0]]> : tensor<3x2xi32>
    %cst_11 = stablehlo.constant dense<1.000000e+00> : tensor<f32>
    %cst_12 = stablehlo.constant dense<2.000000e+00> : tensor<f32>
    %cst_13 = stablehlo.constant dense<5.000000e+00> : tensor<f32>
    %cst_14 = stablehlo.constant dense<1.000000e-01> : tensor<f32>
    %cst_15 = stablehlo.constant dense<1.000000e+01> : tensor<f32>
    %cst_16 = stablehlo.constant dense<-3.276700e+04> : tensor<f32>
    %c_17 = stablehlo.constant dense<[[0, 0], [20, 20], [0, 0]]> : tensor<3x2xi32>
    %c_18 = stablehlo.constant dense<[[0, 0], [45, 45], [0, 0]]> : tensor<3x2xi32>
    %c_19 = stablehlo.constant dense<[[0, 0], [12, 13], [0, 0]]> : tensor<3x2xi32>
    %c_20 = stablehlo.constant dense<[[0, 0], [48, 48], [0, 0]]> : tensor<3x2xi32>
    %c1184 = shape.const_size 1184
    %c32 = shape.const_size 32
    %c64 = shape.const_size 64
    %c1 = arith.constant 1 : index
    %c0 = arith.constant 0 : index
    %cst_21 = stablehlo.constant dense<-0.000000e+00> : tensor<f32>
    %cst_22 = stablehlo.constant dense<0.000000e+00> : tensor<f32>
    %c-2 = arith.constant -2 : index
    %c3_i32 = arith.constant 3 : i32
    %c1_i32 = arith.constant 1 : i32
    %c128_i32 = arith.constant 128 : i32
    %c2_i32 = arith.constant 2 : i32
    %cst_23 = stablehlo.constant dense<0xFF800000> : tensor<f32>
    %c5_i32 = arith.constant 5 : i32
    %c348_i32 = arith.constant 348 : i32
    %c4_i32 = arith.constant 4 : i32
    %c238_i32 = arith.constant 238 : i32
    %c113_i32 = arith.constant 113 : i32
    %c64_i32 = arith.constant 64 : i32
    %c16_i32 = arith.constant 16 : i32
    %c14_i32 = arith.constant 14 : i32
    %c6_i32 = arith.constant 6 : i32
    %c7_i32 = arith.constant 7 : i32
    %c8_i32 = arith.constant 8 : i32
    %c9_i32 = arith.constant 9 : i32
    %c10_i32 = arith.constant 10 : i32
    %c11_i32 = arith.constant 11 : i32
    %c12_i32 = arith.constant 12 : i32
    %c13_i32 = arith.constant 13 : i32
    %c50 = arith.constant 50 : index
    %c49 = arith.constant 49 : index
    %cst_24 = arith.constant dense<[0, 0, 1]> : tensor<3xindex>
    %cst_25 = arith.constant dense<1> : tensor<3xindex>
    %c10 = arith.constant 10 : index
    %c17 = arith.constant 17 : index
    %c33 = arith.constant 33 : index
    %cst_26 = arith.constant dense<[0, 0, 17]> : tensor<3xindex>
    %0 = shape.const_shape [3] : !shape.shape
    %1 = shape.const_shape [3, 1, 128] : tensor<3xindex>
    %cst_27 = arith.constant dense<1> : tensor<3xi32>
    %cst_28 = arith.constant dense<0> : tensor<3xi32>
    %cst_29 = arith.constant dense<[1, 0, 0]> : tensor<3xi32>
    %cst_30 = arith.constant dense<[2, 0, 0]> : tensor<3xi32>
    %2 = shape.const_shape [1, 1, 116] : tensor<3xindex>
    %c_31 = stablehlo.constant dense<0> : tensor<3xi32>
    %3 = shape.const_shape [1, 1, 50] : tensor<3xindex>
    %4 = shape.const_shape [1, 1, 124] : tensor<3xindex>
    %5 = shape.const_shape [1, 1, 30] : tensor<3xindex>
    %6 = shape.const_shape [1, 1, 88] : tensor<3xindex>
    %7 = shape.const_shape [1, 1, 60] : tensor<3xindex>
    %8 = shape.const_shape [1, 1, 128] : tensor<3xindex>
    %9 = shape.const_shape [1, 1, 64] : tensor<3xindex>
    %c30 = arith.constant 30 : index
    %c32_32 = arith.constant 32 : index
    %c2 = arith.constant 2 : index
    %c64_33 = arith.constant 64 : index
    %c16 = arith.constant 16 : index
    %c8 = arith.constant 8 : index
    %10 = shape.const_shape [5] : !shape.shape
    %11 = shape.const_shape [5, 1, 348] : tensor<3xindex>
    %cst_34 = arith.constant dense<[3, 0, 0]> : tensor<3xi32>
    %cst_35 = arith.constant dense<[4, 0, 0]> : tensor<3xi32>
    %12 = shape.const_shape [1, 348] : tensor<2xindex>
    %13 = shape.const_shape [5, 1, 238] : tensor<3xindex>
    %14 = shape.const_shape [1, 238] : tensor<2xindex>
    %15 = shape.const_shape [5, 1, 113] : tensor<3xindex>
    %16 = shape.const_shape [1, 113] : tensor<2xindex>
    %17 = shape.const_shape [5, 1, 128] : tensor<3xindex>
    %18 = shape.const_shape [1, 128] : tensor<2xindex>
    %19 = shape.const_shape [5, 1, 64] : tensor<3xindex>
    %20 = shape.const_shape [1, 64] : tensor<2xindex>
    %21 = shape.const_shape [5, 1, 16] : tensor<3xindex>
    %22 = shape.const_shape [1, 16] : tensor<2xindex>
    %23 = shape.const_shape [14] : !shape.shape
    %24 = shape.const_shape [14, 1, 64] : tensor<3xindex>
    %cst_36 = arith.constant dense<[5, 0, 0]> : tensor<3xi32>
    %cst_37 = arith.constant dense<[6, 0, 0]> : tensor<3xi32>
    %cst_38 = arith.constant dense<[7, 0, 0]> : tensor<3xi32>
    %cst_39 = arith.constant dense<[8, 0, 0]> : tensor<3xi32>
    %cst_40 = arith.constant dense<[9, 0, 0]> : tensor<3xi32>
    %cst_41 = arith.constant dense<[10, 0, 0]> : tensor<3xi32>
    %cst_42 = arith.constant dense<[11, 0, 0]> : tensor<3xi32>
    %cst_43 = arith.constant dense<[12, 0, 0]> : tensor<3xi32>
    %cst_44 = arith.constant dense<[13, 0, 0]> : tensor<3xi32>
    %c_45 = stablehlo.constant dense<0> : tensor<2xi32>
    %25 = stablehlo.convert %arg0 : (tensor<?x50x17xf16>) -> tensor<?x50x17xf32>
    %26 = stablehlo.convert %arg1 : (tensor<?x50x17xf16>) -> tensor<?x50x17xf32>
    %27 = stablehlo.convert %arg2 : (tensor<?x50x17xf16>) -> tensor<?x50x17xf32>
    %28 = stablehlo.convert %arg3 : (tensor<?x50x17xf16>) -> tensor<?x50x17xf32>
    %29 = stablehlo.convert %arg4 : (tensor<?x50x49xf16>) -> tensor<?x50x49xf32>
    %30 = stablehlo.convert %arg5 : (tensor<?x10x49xf16>) -> tensor<?x10x49xf32>
    %31 = stablehlo.convert %arg6 : (tensor<?x50x33xf16>) -> tensor<?x50x33xf32>
    %32 = shape.shape_of %arg7 : tensor<?x1x10xf32> -> tensor<3xindex>
    %33 = stablehlo.dynamic_broadcast_in_dim %cst_11, %32, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x10xf32>
    %34 = stablehlo.subtract %33, %arg7 : tensor<?x1x10xf32>
    %35 = shape.shape_of %arg8 : tensor<?x1x60xf32> -> tensor<3xindex>
    %36 = stablehlo.dynamic_broadcast_in_dim %cst_11, %35, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %37 = stablehlo.subtract %36, %arg8 : tensor<?x1x60xf32>
    %38 = shape.shape_of %arg9 : tensor<?x1x64xf32> -> tensor<3xindex>
    %39 = stablehlo.dynamic_broadcast_in_dim %cst_11, %38, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %40 = stablehlo.subtract %39, %arg9 : tensor<?x1x64xf32>
    %41 = shape.shape_of %arg10 : tensor<?x1x50xf32> -> tensor<3xindex>
    %42 = stablehlo.dynamic_broadcast_in_dim %cst_11, %41, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %43 = stablehlo.subtract %42, %arg10 : tensor<?x1x50xf32>
    %44 = shape.shape_of %arg11 : tensor<?x1x30xf32> -> tensor<3xindex>
    %45 = stablehlo.dynamic_broadcast_in_dim %cst_11, %44, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %46 = stablehlo.subtract %45, %arg11 : tensor<?x1x30xf32>
    %47 = shape.shape_of %arg12 : tensor<?x1x50xf32> -> tensor<3xindex>
    %48 = stablehlo.dynamic_broadcast_in_dim %cst_11, %47, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %49 = stablehlo.subtract %48, %arg12 : tensor<?x1x50xf32>
    %50 = shape.shape_of %arg13 : tensor<?x1x30xf32> -> tensor<3xindex>
    %51 = stablehlo.dynamic_broadcast_in_dim %cst_11, %50, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %52 = stablehlo.subtract %51, %arg13 : tensor<?x1x30xf32>
    %53 = shape.shape_of %arg14 : tensor<?x1x50xf32> -> tensor<3xindex>
    %54 = stablehlo.dynamic_broadcast_in_dim %cst_11, %53, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %55 = stablehlo.subtract %54, %arg14 : tensor<?x1x50xf32>
    %56 = shape.shape_of %arg15 : tensor<?x1x50xf32> -> tensor<3xindex>
    %57 = stablehlo.dynamic_broadcast_in_dim %cst_11, %56, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %58 = stablehlo.subtract %57, %arg15 : tensor<?x1x50xf32>
    %59 = shape.shape_of %arg16 : tensor<?x1x30xf32> -> tensor<3xindex>
    %60 = stablehlo.dynamic_broadcast_in_dim %cst_11, %59, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %61 = stablehlo.subtract %60, %arg16 : tensor<?x1x30xf32>
    %62 = shape.shape_of %arg17 : tensor<?x1x30xf32> -> tensor<3xindex>
    %63 = stablehlo.dynamic_broadcast_in_dim %cst_11, %62, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %64 = stablehlo.subtract %63, %arg17 : tensor<?x1x30xf32>
    %65 = shape.shape_of %34 : tensor<?x1x10xf32> -> tensor<3xindex>
    %66 = stablehlo.dynamic_broadcast_in_dim %cst_16, %65, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x10xf32>
    %67 = stablehlo.multiply %34, %66 : tensor<?x1x10xf32>
    %68 = shape.shape_of %46 : tensor<?x1x30xf32> -> tensor<3xindex>
    %69 = stablehlo.dynamic_broadcast_in_dim %cst_16, %68, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %70 = stablehlo.multiply %46, %69 : tensor<?x1x30xf32>
    %71 = shape.shape_of %64 : tensor<?x1x30xf32> -> tensor<3xindex>
    %72 = stablehlo.dynamic_broadcast_in_dim %cst_16, %71, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %73 = stablehlo.multiply %64, %72 : tensor<?x1x30xf32>
    %74 = shape.shape_of %37 : tensor<?x1x60xf32> -> tensor<3xindex>
    %75 = stablehlo.dynamic_broadcast_in_dim %cst_16, %74, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %76 = stablehlo.multiply %37, %75 : tensor<?x1x60xf32>
    %77 = shape.shape_of %40 : tensor<?x1x64xf32> -> tensor<3xindex>
    %78 = stablehlo.dynamic_broadcast_in_dim %cst_16, %77, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %79 = stablehlo.multiply %40, %78 : tensor<?x1x64xf32>
    %80 = shape.shape_of %43 : tensor<?x1x50xf32> -> tensor<3xindex>
    %81 = stablehlo.dynamic_broadcast_in_dim %cst_16, %80, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %82 = stablehlo.multiply %43, %81 : tensor<?x1x50xf32>
    %83 = shape.shape_of %49 : tensor<?x1x50xf32> -> tensor<3xindex>
    %84 = stablehlo.dynamic_broadcast_in_dim %cst_16, %83, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %85 = stablehlo.multiply %49, %84 : tensor<?x1x50xf32>
    %86 = shape.shape_of %52 : tensor<?x1x30xf32> -> tensor<3xindex>
    %87 = stablehlo.dynamic_broadcast_in_dim %cst_16, %86, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %88 = stablehlo.multiply %52, %87 : tensor<?x1x30xf32>
    %89 = shape.shape_of %55 : tensor<?x1x50xf32> -> tensor<3xindex>
    %90 = stablehlo.dynamic_broadcast_in_dim %cst_16, %89, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %91 = stablehlo.multiply %55, %90 : tensor<?x1x50xf32>
    %92 = shape.shape_of %58 : tensor<?x1x50xf32> -> tensor<3xindex>
    %93 = stablehlo.dynamic_broadcast_in_dim %cst_16, %92, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x50xf32>
    %94 = stablehlo.multiply %58, %93 : tensor<?x1x50xf32>
    %95 = shape.shape_of %61 : tensor<?x1x30xf32> -> tensor<3xindex>
    %96 = stablehlo.dynamic_broadcast_in_dim %cst_16, %95, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x30xf32>
    %97 = stablehlo.multiply %61, %96 : tensor<?x1x30xf32>
    %dim = tensor.dim %29, %c0 : tensor<?x50x49xf32>
    %from_elements = tensor.from_elements %dim, %c50, %c49 : tensor<3xindex>
    %98 = stablehlo.real_dynamic_slice %29, %cst_24, %from_elements, %cst_25 : (tensor<?x50x49xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x48xf32>
    %99 = stablehlo.reduce(%98 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x48xf32>, tensor<f32>) -> tensor<?x48xf32>
    %dim_46 = tensor.dim %30, %c0 : tensor<?x10x49xf32>
    %from_elements_47 = tensor.from_elements %dim_46, %c10, %c49 : tensor<3xindex>
    %100 = stablehlo.real_dynamic_slice %30, %cst_24, %from_elements_47, %cst_25 : (tensor<?x10x49xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x10x48xf32>
    %101 = stablehlo.reduce(%100 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x10x48xf32>, tensor<f32>) -> tensor<?x48xf32>
    %dim_48 = tensor.dim %28, %c0 : tensor<?x50x17xf32>
    %from_elements_49 = tensor.from_elements %dim_48, %c50, %c17 : tensor<3xindex>
    %102 = stablehlo.real_dynamic_slice %28, %cst_24, %from_elements_49, %cst_25 : (tensor<?x50x17xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x16xf32>
    %103 = stablehlo.reduce(%102 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %104 = stablehlo.reduce(%arg18 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %dim_50 = tensor.dim %31, %c0 : tensor<?x50x33xf32>
    %from_elements_51 = tensor.from_elements %dim_50, %c50, %c33 : tensor<3xindex>
    %105 = stablehlo.real_dynamic_slice %31, %cst_26, %from_elements_51, %cst_25 : (tensor<?x50x33xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x16xf32>
    %106 = stablehlo.reduce(%105 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %107 = stablehlo.concatenate %arg19, %arg20, %arg21, %arg22, %arg23, %arg24, %arg25, %arg26, %arg27, %arg28, %arg29, %arg30, %arg31, %arg32, %arg33, %arg34, %arg35, %arg36, %arg37, %arg38, %arg39, %103, %104, %106, dim = 1 : (tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>) -> tensor<?x284xf32>
    %108 = stablehlo.dot %107, %arg40, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %109 = shape.shape_of %108 : tensor<?x128xf32> -> tensor<2xindex>
    %110 = stablehlo.dynamic_broadcast_in_dim %arg41, %109, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %111 = stablehlo.add %108, %110 : tensor<?x128xf32>
    %112 = shape.shape_of %111 : tensor<?x128xf32> -> tensor<2xindex>
    %113 = stablehlo.dynamic_broadcast_in_dim %cst_22, %112, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %114 = stablehlo.maximum %111, %113 : tensor<?x128xf32>
    %115 = stablehlo.dot %114, %arg42, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x167xf32>) -> tensor<?x167xf32>
    %116 = shape.shape_of %115 : tensor<?x167xf32> -> tensor<2xindex>
    %117 = stablehlo.dynamic_broadcast_in_dim %arg43, %116, dims = [1] : (tensor<167xf32>, tensor<2xindex>) -> tensor<?x167xf32>
    %118 = stablehlo.add %115, %117 : tensor<?x167xf32>
    %119 = stablehlo.logistic %118 : tensor<?x167xf32>
    %120 = shape.shape_of %119 : tensor<?x167xf32> -> tensor<2xindex>
    %121 = stablehlo.dynamic_broadcast_in_dim %cst_12, %120, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x167xf32>
    %122 = stablehlo.multiply %119, %121 : tensor<?x167xf32>
    %123 = shape.shape_of %arg44 : tensor<?x167xf32> -> tensor<2xindex>
    %124 = shape.shape_of %122 : tensor<?x167xf32> -> tensor<2xindex>
    %125 = shape.broadcast %123, %124 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %126 = stablehlo.dynamic_broadcast_in_dim %arg44, %125, dims = [0, 1] : (tensor<?x167xf32>, tensor<2xindex>) -> tensor<?x167xf32>
    %127 = stablehlo.dynamic_broadcast_in_dim %122, %125, dims = [0, 1] : (tensor<?x167xf32>, tensor<2xindex>) -> tensor<?x167xf32>
    %128 = stablehlo.multiply %126, %127 : tensor<?x167xf32>
    %129 = stablehlo.dot %128, %arg45, precision = [DEFAULT, DEFAULT] : (tensor<?x167xf32>, tensor<167x256xf32>) -> tensor<?x256xf32>
    %130 = shape.shape_of %129 : tensor<?x256xf32> -> tensor<2xindex>
    %131 = stablehlo.dynamic_broadcast_in_dim %arg46, %130, dims = [1] : (tensor<256xf32>, tensor<2xindex>) -> tensor<?x256xf32>
    %132 = stablehlo.add %129, %131 : tensor<?x256xf32>
    %133 = shape.shape_of %132 : tensor<?x256xf32> -> tensor<2xindex>
    %134 = stablehlo.dynamic_broadcast_in_dim %cst_22, %133, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x256xf32>
    %135 = stablehlo.maximum %132, %134 : tensor<?x256xf32>
    %136 = stablehlo.dot %107, %arg47, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %137 = shape.shape_of %136 : tensor<?x128xf32> -> tensor<2xindex>
    %138 = stablehlo.dynamic_broadcast_in_dim %arg48, %137, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %139 = stablehlo.add %136, %138 : tensor<?x128xf32>
    %140 = shape.shape_of %139 : tensor<?x128xf32> -> tensor<2xindex>
    %141 = stablehlo.dynamic_broadcast_in_dim %cst_22, %140, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %142 = stablehlo.maximum %139, %141 : tensor<?x128xf32>
    %143 = stablehlo.dot %142, %arg49, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x256xf32>) -> tensor<?x256xf32>
    %144 = shape.shape_of %143 : tensor<?x256xf32> -> tensor<2xindex>
    %145 = stablehlo.dynamic_broadcast_in_dim %arg50, %144, dims = [1] : (tensor<256xf32>, tensor<2xindex>) -> tensor<?x256xf32>
    %146 = stablehlo.add %143, %145 : tensor<?x256xf32>
    %147 = stablehlo.logistic %146 : tensor<?x256xf32>
    %148 = shape.shape_of %147 : tensor<?x256xf32> -> tensor<2xindex>
    %149 = stablehlo.dynamic_broadcast_in_dim %cst_12, %148, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x256xf32>
    %150 = stablehlo.multiply %147, %149 : tensor<?x256xf32>
    %151 = shape.shape_of %150 : tensor<?x256xf32> -> tensor<2xindex>
    %152 = shape.shape_of %135 : tensor<?x256xf32> -> tensor<2xindex>
    %153 = shape.broadcast %151, %152 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %154 = stablehlo.dynamic_broadcast_in_dim %150, %153, dims = [0, 1] : (tensor<?x256xf32>, tensor<2xindex>) -> tensor<?x256xf32>
    %155 = stablehlo.dynamic_broadcast_in_dim %135, %153, dims = [0, 1] : (tensor<?x256xf32>, tensor<2xindex>) -> tensor<?x256xf32>
    %156 = stablehlo.multiply %154, %155 : tensor<?x256xf32>
    %157 = stablehlo.dot %156, %arg51, precision = [DEFAULT, DEFAULT] : (tensor<?x256xf32>, tensor<256x64xf32>) -> tensor<?x64xf32>
    %158 = shape.shape_of %157 : tensor<?x64xf32> -> tensor<2xindex>
    %159 = stablehlo.dynamic_broadcast_in_dim %arg52, %158, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %160 = stablehlo.add %157, %159 : tensor<?x64xf32>
    %161 = stablehlo.dot %107, %arg53, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %162 = shape.shape_of %161 : tensor<?x128xf32> -> tensor<2xindex>
    %163 = stablehlo.dynamic_broadcast_in_dim %arg54, %162, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %164 = stablehlo.add %161, %163 : tensor<?x128xf32>
    %165 = shape.shape_of %164 : tensor<?x128xf32> -> tensor<2xindex>
    %166 = stablehlo.dynamic_broadcast_in_dim %cst_22, %165, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %167 = stablehlo.maximum %164, %166 : tensor<?x128xf32>
    %168 = stablehlo.dot %167, %arg55, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %169 = shape.shape_of %168 : tensor<?x64xf32> -> tensor<2xindex>
    %170 = stablehlo.dynamic_broadcast_in_dim %arg56, %169, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %171 = stablehlo.add %168, %170 : tensor<?x64xf32>
    %172 = stablehlo.logistic %171 : tensor<?x64xf32>
    %173 = shape.shape_of %172 : tensor<?x64xf32> -> tensor<2xindex>
    %174 = stablehlo.dynamic_broadcast_in_dim %cst_12, %173, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %175 = stablehlo.multiply %172, %174 : tensor<?x64xf32>
    %176 = shape.shape_of %160 : tensor<?x64xf32> -> tensor<2xindex>
    %177 = shape.shape_of %175 : tensor<?x64xf32> -> tensor<2xindex>
    %178 = shape.broadcast %176, %177 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %179 = stablehlo.dynamic_broadcast_in_dim %160, %178, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %180 = stablehlo.dynamic_broadcast_in_dim %175, %178, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %181 = stablehlo.multiply %179, %180 : tensor<?x64xf32>
    %182 = shape.shape_of %107 : tensor<?x284xf32> -> tensor<2xindex>
    %head, %tail = "shape.split_at"(%182, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %183 = shape.broadcast %head, %0 : !shape.shape, !shape.shape -> !shape.shape
    %184 = shape.concat %183, %tail : !shape.shape, !shape.shape -> !shape.shape
    %185 = shape.to_extent_tensor %184 : !shape.shape -> tensor<3xindex>
    %186 = stablehlo.dynamic_broadcast_in_dim %107, %185, dims = [1, 2] : (tensor<?x284xf32>, tensor<3xindex>) -> tensor<3x?x284xf32>
    %187 = stablehlo.dot_general %186, %arg57, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<3x?x284xf32>, tensor<3x284x128xf32>) -> tensor<3x?x128xf32>
    %188 = shape.shape_of %187 : tensor<3x?x128xf32> -> tensor<3xindex>
    %189 = shape.broadcast %188, %1 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %190 = stablehlo.dynamic_broadcast_in_dim %187, %189, dims = [0, 1, 2] : (tensor<3x?x128xf32>, tensor<3xindex>) -> tensor<3x?x128xf32>
    %191 = stablehlo.dynamic_broadcast_in_dim %arg58, %189, dims = [0, 1, 2] : (tensor<3x1x128xf32>, tensor<3xindex>) -> tensor<3x?x128xf32>
    %192 = stablehlo.add %190, %191 : tensor<3x?x128xf32>
    %193 = shape.shape_of %192 : tensor<3x?x128xf32> -> tensor<3xindex>
    %194 = stablehlo.dynamic_broadcast_in_dim %cst_22, %193, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<3x?x128xf32>
    %195 = stablehlo.maximum %192, %194 : tensor<3x?x128xf32>
    %dim_52 = tensor.dim %195, %c1 : tensor<3x?x128xf32>
    %196 = arith.index_cast %dim_52 : index to i32
    %from_elements_53 = tensor.from_elements %c1_i32, %196, %c128_i32 : tensor<3xi32>
    %197 = stablehlo.real_dynamic_slice %195, %cst_28, %from_elements_53, %cst_27 : (tensor<3x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed = tensor.collapse_shape %197 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_54 = tensor.from_elements %c2_i32, %196, %c128_i32 : tensor<3xi32>
    %198 = stablehlo.real_dynamic_slice %195, %cst_29, %from_elements_54, %cst_27 : (tensor<3x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_55 = tensor.collapse_shape %198 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_56 = tensor.from_elements %c3_i32, %196, %c128_i32 : tensor<3xi32>
    %199 = stablehlo.real_dynamic_slice %195, %cst_30, %from_elements_56, %cst_27 : (tensor<3x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_57 = tensor.collapse_shape %199 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %200 = stablehlo.dot %collapsed_55, %arg59, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x8821xf32>) -> tensor<?x8821xf32>
    %201 = shape.shape_of %200 : tensor<?x8821xf32> -> tensor<2xindex>
    %202 = stablehlo.dynamic_broadcast_in_dim %arg60, %201, dims = [1] : (tensor<8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %203 = stablehlo.add %200, %202 : tensor<?x8821xf32>
    %204 = stablehlo.logistic %203 : tensor<?x8821xf32>
    %205 = shape.shape_of %204 : tensor<?x8821xf32> -> tensor<2xindex>
    %206 = stablehlo.dynamic_broadcast_in_dim %cst_12, %205, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %207 = stablehlo.multiply %204, %206 : tensor<?x8821xf32>
    %208 = stablehlo.dot %collapsed_57, %arg61, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x2439xf32>) -> tensor<?x2439xf32>
    %209 = shape.shape_of %208 : tensor<?x2439xf32> -> tensor<2xindex>
    %210 = stablehlo.dynamic_broadcast_in_dim %arg62, %209, dims = [1] : (tensor<2439xf32>, tensor<2xindex>) -> tensor<?x2439xf32>
    %211 = stablehlo.add %208, %210 : tensor<?x2439xf32>
    %212 = stablehlo.logistic %211 : tensor<?x2439xf32>
    %213 = shape.shape_of %212 : tensor<?x2439xf32> -> tensor<2xindex>
    %214 = stablehlo.dynamic_broadcast_in_dim %cst_12, %213, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x2439xf32>
    %215 = stablehlo.multiply %212, %214 : tensor<?x2439xf32>
    %216 = stablehlo.dot %collapsed, %arg63, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x8821xf32>) -> tensor<?x8821xf32>
    %217 = shape.shape_of %216 : tensor<?x8821xf32> -> tensor<2xindex>
    %218 = stablehlo.dynamic_broadcast_in_dim %arg64, %217, dims = [1] : (tensor<8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %219 = stablehlo.add %216, %218 : tensor<?x8821xf32>
    %220 = stablehlo.logistic %219 : tensor<?x8821xf32>
    %221 = shape.shape_of %220 : tensor<?x8821xf32> -> tensor<2xindex>
    %222 = stablehlo.dynamic_broadcast_in_dim %cst_12, %221, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %223 = stablehlo.multiply %220, %222 : tensor<?x8821xf32>
    %224 = stablehlo.dot %107, %arg65, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %225 = shape.shape_of %224 : tensor<?x128xf32> -> tensor<2xindex>
    %226 = stablehlo.dynamic_broadcast_in_dim %arg66, %225, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %227 = stablehlo.add %224, %226 : tensor<?x128xf32>
    %228 = shape.shape_of %227 : tensor<?x128xf32> -> tensor<2xindex>
    %229 = stablehlo.dynamic_broadcast_in_dim %cst_22, %228, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %230 = stablehlo.maximum %227, %229 : tensor<?x128xf32>
    %231 = stablehlo.dot %230, %arg67, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x1669xf32>) -> tensor<?x1669xf32>
    %232 = shape.shape_of %231 : tensor<?x1669xf32> -> tensor<2xindex>
    %233 = stablehlo.dynamic_broadcast_in_dim %arg68, %232, dims = [1] : (tensor<1669xf32>, tensor<2xindex>) -> tensor<?x1669xf32>
    %234 = stablehlo.add %231, %233 : tensor<?x1669xf32>
    %235 = stablehlo.logistic %234 : tensor<?x1669xf32>
    %236 = shape.shape_of %235 : tensor<?x1669xf32> -> tensor<2xindex>
    %237 = stablehlo.dynamic_broadcast_in_dim %cst_12, %236, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1669xf32>
    %238 = stablehlo.multiply %235, %237 : tensor<?x1669xf32>
    %239 = stablehlo.dot %107, %arg69, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %240 = shape.shape_of %239 : tensor<?x128xf32> -> tensor<2xindex>
    %241 = stablehlo.dynamic_broadcast_in_dim %arg70, %240, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %242 = stablehlo.add %239, %241 : tensor<?x128xf32>
    %243 = shape.shape_of %242 : tensor<?x128xf32> -> tensor<2xindex>
    %244 = stablehlo.dynamic_broadcast_in_dim %cst_22, %243, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %245 = stablehlo.maximum %242, %244 : tensor<?x128xf32>
    %246 = stablehlo.dot %245, %arg71, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x794xf32>) -> tensor<?x794xf32>
    %247 = shape.shape_of %246 : tensor<?x794xf32> -> tensor<2xindex>
    %248 = stablehlo.dynamic_broadcast_in_dim %arg72, %247, dims = [1] : (tensor<794xf32>, tensor<2xindex>) -> tensor<?x794xf32>
    %249 = stablehlo.add %246, %248 : tensor<?x794xf32>
    %250 = stablehlo.logistic %249 : tensor<?x794xf32>
    %251 = shape.shape_of %250 : tensor<?x794xf32> -> tensor<2xindex>
    %252 = stablehlo.dynamic_broadcast_in_dim %cst_12, %251, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x794xf32>
    %253 = stablehlo.multiply %250, %252 : tensor<?x794xf32>
    %254 = stablehlo.dot %107, %arg73, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %255 = shape.shape_of %254 : tensor<?x128xf32> -> tensor<2xindex>
    %256 = stablehlo.dynamic_broadcast_in_dim %arg74, %255, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %257 = stablehlo.add %254, %256 : tensor<?x128xf32>
    %258 = shape.shape_of %257 : tensor<?x128xf32> -> tensor<2xindex>
    %259 = stablehlo.dynamic_broadcast_in_dim %cst_22, %258, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %260 = stablehlo.maximum %257, %259 : tensor<?x128xf32>
    %261 = stablehlo.dot %260, %arg75, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x899xf32>) -> tensor<?x899xf32>
    %262 = shape.shape_of %261 : tensor<?x899xf32> -> tensor<2xindex>
    %263 = stablehlo.dynamic_broadcast_in_dim %arg76, %262, dims = [1] : (tensor<899xf32>, tensor<2xindex>) -> tensor<?x899xf32>
    %264 = stablehlo.add %261, %263 : tensor<?x899xf32>
    %265 = stablehlo.logistic %264 : tensor<?x899xf32>
    %266 = shape.shape_of %265 : tensor<?x899xf32> -> tensor<2xindex>
    %267 = stablehlo.dynamic_broadcast_in_dim %cst_12, %266, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x899xf32>
    %268 = stablehlo.multiply %265, %267 : tensor<?x899xf32>
    %269 = stablehlo.dot %107, %arg77, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %270 = shape.shape_of %269 : tensor<?x128xf32> -> tensor<2xindex>
    %271 = stablehlo.dynamic_broadcast_in_dim %arg78, %270, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %272 = stablehlo.add %269, %271 : tensor<?x128xf32>
    %273 = shape.shape_of %272 : tensor<?x128xf32> -> tensor<2xindex>
    %274 = stablehlo.dynamic_broadcast_in_dim %cst_22, %273, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %275 = stablehlo.maximum %272, %274 : tensor<?x128xf32>
    %276 = stablehlo.dot %275, %arg79, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x451xf32>) -> tensor<?x451xf32>
    %277 = shape.shape_of %276 : tensor<?x451xf32> -> tensor<2xindex>
    %278 = stablehlo.dynamic_broadcast_in_dim %arg80, %277, dims = [1] : (tensor<451xf32>, tensor<2xindex>) -> tensor<?x451xf32>
    %279 = stablehlo.add %276, %278 : tensor<?x451xf32>
    %280 = stablehlo.logistic %279 : tensor<?x451xf32>
    %281 = shape.shape_of %280 : tensor<?x451xf32> -> tensor<2xindex>
    %282 = stablehlo.dynamic_broadcast_in_dim %cst_12, %281, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x451xf32>
    %283 = stablehlo.multiply %280, %282 : tensor<?x451xf32>
    %284 = stablehlo.dot %107, %arg81, precision = [DEFAULT, DEFAULT] : (tensor<?x284xf32>, tensor<284x128xf32>) -> tensor<?x128xf32>
    %285 = shape.shape_of %284 : tensor<?x128xf32> -> tensor<2xindex>
    %286 = stablehlo.dynamic_broadcast_in_dim %arg82, %285, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %287 = stablehlo.add %284, %286 : tensor<?x128xf32>
    %288 = shape.shape_of %287 : tensor<?x128xf32> -> tensor<2xindex>
    %289 = stablehlo.dynamic_broadcast_in_dim %cst_22, %288, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %290 = stablehlo.maximum %287, %289 : tensor<?x128xf32>
    %291 = stablehlo.dot %290, %arg83, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x115xf32>) -> tensor<?x115xf32>
    %292 = shape.shape_of %291 : tensor<?x115xf32> -> tensor<2xindex>
    %293 = stablehlo.dynamic_broadcast_in_dim %arg84, %292, dims = [1] : (tensor<115xf32>, tensor<2xindex>) -> tensor<?x115xf32>
    %294 = stablehlo.add %291, %293 : tensor<?x115xf32>
    %295 = stablehlo.logistic %294 : tensor<?x115xf32>
    %296 = shape.shape_of %295 : tensor<?x115xf32> -> tensor<2xindex>
    %297 = stablehlo.dynamic_broadcast_in_dim %cst_12, %296, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x115xf32>
    %298 = stablehlo.multiply %295, %297 : tensor<?x115xf32>
    %dim_58 = tensor.dim %25, %c0 : tensor<?x50x17xf32>
    %from_elements_59 = tensor.from_elements %dim_58, %c50, %c17 : tensor<3xindex>
    %299 = stablehlo.real_dynamic_slice %25, %cst_24, %from_elements_59, %cst_25 : (tensor<?x50x17xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x16xf32>
    %300 = stablehlo.reduce(%299 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %dim_60 = tensor.dim %26, %c0 : tensor<?x50x17xf32>
    %from_elements_61 = tensor.from_elements %dim_60, %c50, %c17 : tensor<3xindex>
    %301 = stablehlo.real_dynamic_slice %26, %cst_24, %from_elements_61, %cst_25 : (tensor<?x50x17xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x16xf32>
    %302 = stablehlo.reduce(%301 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %dim_62 = tensor.dim %27, %c0 : tensor<?x50x17xf32>
    %from_elements_63 = tensor.from_elements %dim_62, %c50, %c17 : tensor<3xindex>
    %303 = stablehlo.real_dynamic_slice %27, %cst_24, %from_elements_63, %cst_25 : (tensor<?x50x17xf32>, tensor<3xindex>, tensor<3xindex>, tensor<3xindex>) -> tensor<?x50x16xf32>
    %304 = stablehlo.reduce(%303 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x16xf32>, tensor<f32>) -> tensor<?x16xf32>
    %305 = shape.shape_of %arg85 : tensor<?x37x32xf32> -> tensor<3xindex>
    %306 = shape.num_elements %305 : tensor<3xindex> -> index
    %307 = shape.index_to_size %306
    %308 = shape.div %307, %c1184 : !shape.size, !shape.size -> !shape.size
    %309 = shape.from_extents %308, %c1184 : !shape.size, !shape.size
    %310 = shape.to_extent_tensor %309 : !shape.shape -> tensor<2xindex>
    %collapsed_64 = tensor.collapse_shape %arg85 [[0], [1, 2]] : tensor<?x37x32xf32> into tensor<?x1184xf32>
    %311 = shape.shape_of %arg86 : tensor<?x37x32xf32> -> tensor<3xindex>
    %312 = shape.num_elements %311 : tensor<3xindex> -> index
    %313 = shape.index_to_size %312
    %314 = shape.div %313, %c1184 : !shape.size, !shape.size -> !shape.size
    %315 = shape.from_extents %314, %c1184 : !shape.size, !shape.size
    %316 = shape.to_extent_tensor %315 : !shape.shape -> tensor<2xindex>
    %collapsed_65 = tensor.collapse_shape %arg86 [[0], [1, 2]] : tensor<?x37x32xf32> into tensor<?x1184xf32>
    %317 = shape.broadcast %310, %316 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %318 = stablehlo.dynamic_broadcast_in_dim %collapsed_64, %317, dims = [0, 1] : (tensor<?x1184xf32>, tensor<2xindex>) -> tensor<?x1184xf32>
    %319 = stablehlo.dynamic_broadcast_in_dim %collapsed_65, %317, dims = [0, 1] : (tensor<?x1184xf32>, tensor<2xindex>) -> tensor<?x1184xf32>
    %320 = stablehlo.add %318, %319 : tensor<?x1184xf32>
    %321 = stablehlo.reduce(%arg87 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x30x68xf32>, tensor<f32>) -> tensor<?x68xf32>
    %322 = stablehlo.reduce(%arg88 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x30x104xf32>, tensor<f32>) -> tensor<?x104xf32>
    %323 = shape.shape_of %arg89 : tensor<?x10x116xf32> -> tensor<3xindex>
    %324 = shape.broadcast %323, %2 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %325 = stablehlo.dynamic_broadcast_in_dim %arg89, %324, dims = [0, 1, 2] : (tensor<?x10x116xf32>, tensor<3xindex>) -> tensor<?x10x116xf32>
    %326 = stablehlo.dynamic_broadcast_in_dim %arg90, %324, dims = [0, 1, 2] : (tensor<1x1x116xf32>, tensor<3xindex>) -> tensor<?x10x116xf32>
    %327 = stablehlo.add %325, %326 : tensor<?x10x116xf32>
    %328 = stablehlo.transpose %c_17, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %329 = stablehlo.reshape %328 : (tensor<2x3xi32>) -> tensor<6xi32>
    %330 = stablehlo.slice %329 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %331 = stablehlo.slice %329 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %332 = stablehlo.dynamic_pad %327, %cst_22, %330, %331, %c_31 : (tensor<?x10x116xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x50x116xf32>
    %333 = shape.shape_of %arg91 : tensor<?x50x116xf32> -> tensor<3xindex>
    %334 = shape.shape_of %332 : tensor<?x50x116xf32> -> tensor<3xindex>
    %335 = shape.broadcast %333, %334 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %336 = stablehlo.dynamic_broadcast_in_dim %arg91, %335, dims = [0, 1, 2] : (tensor<?x50x116xf32>, tensor<3xindex>) -> tensor<?x50x116xf32>
    %337 = stablehlo.dynamic_broadcast_in_dim %332, %335, dims = [0, 1, 2] : (tensor<?x50x116xf32>, tensor<3xindex>) -> tensor<?x50x116xf32>
    %338 = stablehlo.add %336, %337 : tensor<?x50x116xf32>
    %339 = stablehlo.logistic %338 : tensor<?x50x116xf32>
    %340 = shape.shape_of %338 : tensor<?x50x116xf32> -> tensor<3xindex>
    %341 = shape.shape_of %339 : tensor<?x50x116xf32> -> tensor<3xindex>
    %342 = shape.broadcast %340, %341 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %343 = stablehlo.dynamic_broadcast_in_dim %338, %342, dims = [0, 1, 2] : (tensor<?x50x116xf32>, tensor<3xindex>) -> tensor<?x50x116xf32>
    %344 = stablehlo.dynamic_broadcast_in_dim %339, %342, dims = [0, 1, 2] : (tensor<?x50x116xf32>, tensor<3xindex>) -> tensor<?x50x116xf32>
    %345 = stablehlo.multiply %343, %344 : tensor<?x50x116xf32>
    %346 = stablehlo.reduce(%345 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x116xf32>, tensor<f32>) -> tensor<?x116xf32>
    %347 = shape.shape_of %arg92 : tensor<?x26x50xf32> -> tensor<3xindex>
    %348 = shape.broadcast %347, %3 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %349 = stablehlo.dynamic_broadcast_in_dim %arg92, %348, dims = [0, 1, 2] : (tensor<?x26x50xf32>, tensor<3xindex>) -> tensor<?x26x50xf32>
    %350 = stablehlo.dynamic_broadcast_in_dim %arg93, %348, dims = [0, 1, 2] : (tensor<1x1x50xf32>, tensor<3xindex>) -> tensor<?x26x50xf32>
    %351 = stablehlo.add %349, %350 : tensor<?x26x50xf32>
    %352 = stablehlo.transpose %c_18, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %353 = stablehlo.reshape %352 : (tensor<2x3xi32>) -> tensor<6xi32>
    %354 = stablehlo.slice %353 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %355 = stablehlo.slice %353 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %356 = stablehlo.dynamic_pad %351, %cst_22, %354, %355, %c_31 : (tensor<?x26x50xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x116x50xf32>
    %357 = shape.shape_of %356 : tensor<?x116x50xf32> -> tensor<3xindex>
    %358 = shape.shape_of %arg94 : tensor<?x116x50xf32> -> tensor<3xindex>
    %359 = shape.broadcast %357, %358 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %360 = stablehlo.dynamic_broadcast_in_dim %356, %359, dims = [0, 1, 2] : (tensor<?x116x50xf32>, tensor<3xindex>) -> tensor<?x116x50xf32>
    %361 = stablehlo.dynamic_broadcast_in_dim %arg94, %359, dims = [0, 1, 2] : (tensor<?x116x50xf32>, tensor<3xindex>) -> tensor<?x116x50xf32>
    %362 = stablehlo.add %360, %361 : tensor<?x116x50xf32>
    %363 = stablehlo.logistic %362 : tensor<?x116x50xf32>
    %364 = shape.shape_of %362 : tensor<?x116x50xf32> -> tensor<3xindex>
    %365 = shape.shape_of %363 : tensor<?x116x50xf32> -> tensor<3xindex>
    %366 = shape.broadcast %364, %365 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %367 = stablehlo.dynamic_broadcast_in_dim %362, %366, dims = [0, 1, 2] : (tensor<?x116x50xf32>, tensor<3xindex>) -> tensor<?x116x50xf32>
    %368 = stablehlo.dynamic_broadcast_in_dim %363, %366, dims = [0, 1, 2] : (tensor<?x116x50xf32>, tensor<3xindex>) -> tensor<?x116x50xf32>
    %369 = stablehlo.multiply %367, %368 : tensor<?x116x50xf32>
    %370 = stablehlo.transpose %369, dims = [0, 2, 1] : (tensor<?x116x50xf32>) -> tensor<?x50x116xf32>
    %371 = stablehlo.reduce(%370 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x116xf32>, tensor<f32>) -> tensor<?x116xf32>
    %372 = stablehlo.concatenate %346, %371, dim = 1 : (tensor<?x116xf32>, tensor<?x116xf32>) -> tensor<?x232xf32>
    %373 = stablehlo.dot %372, %arg95, precision = [DEFAULT, DEFAULT] : (tensor<?x232xf32>, tensor<232x64xf32>) -> tensor<?x64xf32>
    %374 = shape.shape_of %373 : tensor<?x64xf32> -> tensor<2xindex>
    %375 = stablehlo.dynamic_broadcast_in_dim %arg96, %374, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %376 = stablehlo.add %373, %375 : tensor<?x64xf32>
    %377 = shape.shape_of %arg97 : tensor<?x10x124xf32> -> tensor<3xindex>
    %378 = shape.broadcast %377, %4 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %379 = stablehlo.dynamic_broadcast_in_dim %arg97, %378, dims = [0, 1, 2] : (tensor<?x10x124xf32>, tensor<3xindex>) -> tensor<?x10x124xf32>
    %380 = stablehlo.dynamic_broadcast_in_dim %arg98, %378, dims = [0, 1, 2] : (tensor<1x1x124xf32>, tensor<3xindex>) -> tensor<?x10x124xf32>
    %381 = stablehlo.add %379, %380 : tensor<?x10x124xf32>
    %382 = stablehlo.dynamic_pad %381, %cst_22, %330, %331, %c_31 : (tensor<?x10x124xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x50x124xf32>
    %383 = shape.shape_of %arg99 : tensor<?x50x124xf32> -> tensor<3xindex>
    %384 = shape.shape_of %382 : tensor<?x50x124xf32> -> tensor<3xindex>
    %385 = shape.broadcast %383, %384 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %386 = stablehlo.dynamic_broadcast_in_dim %arg99, %385, dims = [0, 1, 2] : (tensor<?x50x124xf32>, tensor<3xindex>) -> tensor<?x50x124xf32>
    %387 = stablehlo.dynamic_broadcast_in_dim %382, %385, dims = [0, 1, 2] : (tensor<?x50x124xf32>, tensor<3xindex>) -> tensor<?x50x124xf32>
    %388 = stablehlo.add %386, %387 : tensor<?x50x124xf32>
    %389 = stablehlo.logistic %388 : tensor<?x50x124xf32>
    %390 = shape.shape_of %388 : tensor<?x50x124xf32> -> tensor<3xindex>
    %391 = shape.shape_of %389 : tensor<?x50x124xf32> -> tensor<3xindex>
    %392 = shape.broadcast %390, %391 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %393 = stablehlo.dynamic_broadcast_in_dim %388, %392, dims = [0, 1, 2] : (tensor<?x50x124xf32>, tensor<3xindex>) -> tensor<?x50x124xf32>
    %394 = stablehlo.dynamic_broadcast_in_dim %389, %392, dims = [0, 1, 2] : (tensor<?x50x124xf32>, tensor<3xindex>) -> tensor<?x50x124xf32>
    %395 = stablehlo.multiply %393, %394 : tensor<?x50x124xf32>
    %396 = stablehlo.reduce(%395 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x124xf32>, tensor<f32>) -> tensor<?x124xf32>
    %397 = shape.shape_of %arg100 : tensor<?x28x50xf32> -> tensor<3xindex>
    %398 = shape.broadcast %397, %3 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %399 = stablehlo.dynamic_broadcast_in_dim %arg100, %398, dims = [0, 1, 2] : (tensor<?x28x50xf32>, tensor<3xindex>) -> tensor<?x28x50xf32>
    %400 = stablehlo.dynamic_broadcast_in_dim %arg101, %398, dims = [0, 1, 2] : (tensor<1x1x50xf32>, tensor<3xindex>) -> tensor<?x28x50xf32>
    %401 = stablehlo.add %399, %400 : tensor<?x28x50xf32>
    %402 = stablehlo.transpose %c_20, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %403 = stablehlo.reshape %402 : (tensor<2x3xi32>) -> tensor<6xi32>
    %404 = stablehlo.slice %403 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %405 = stablehlo.slice %403 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %406 = stablehlo.dynamic_pad %401, %cst_22, %404, %405, %c_31 : (tensor<?x28x50xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x124x50xf32>
    %407 = shape.shape_of %406 : tensor<?x124x50xf32> -> tensor<3xindex>
    %408 = shape.shape_of %arg102 : tensor<?x124x50xf32> -> tensor<3xindex>
    %409 = shape.broadcast %407, %408 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %410 = stablehlo.dynamic_broadcast_in_dim %406, %409, dims = [0, 1, 2] : (tensor<?x124x50xf32>, tensor<3xindex>) -> tensor<?x124x50xf32>
    %411 = stablehlo.dynamic_broadcast_in_dim %arg102, %409, dims = [0, 1, 2] : (tensor<?x124x50xf32>, tensor<3xindex>) -> tensor<?x124x50xf32>
    %412 = stablehlo.add %410, %411 : tensor<?x124x50xf32>
    %413 = stablehlo.logistic %412 : tensor<?x124x50xf32>
    %414 = shape.shape_of %412 : tensor<?x124x50xf32> -> tensor<3xindex>
    %415 = shape.shape_of %413 : tensor<?x124x50xf32> -> tensor<3xindex>
    %416 = shape.broadcast %414, %415 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %417 = stablehlo.dynamic_broadcast_in_dim %412, %416, dims = [0, 1, 2] : (tensor<?x124x50xf32>, tensor<3xindex>) -> tensor<?x124x50xf32>
    %418 = stablehlo.dynamic_broadcast_in_dim %413, %416, dims = [0, 1, 2] : (tensor<?x124x50xf32>, tensor<3xindex>) -> tensor<?x124x50xf32>
    %419 = stablehlo.multiply %417, %418 : tensor<?x124x50xf32>
    %420 = stablehlo.transpose %419, dims = [0, 2, 1] : (tensor<?x124x50xf32>) -> tensor<?x50x124xf32>
    %421 = stablehlo.reduce(%420 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x124xf32>, tensor<f32>) -> tensor<?x124xf32>
    %422 = stablehlo.concatenate %396, %421, dim = 1 : (tensor<?x124xf32>, tensor<?x124xf32>) -> tensor<?x248xf32>
    %423 = stablehlo.dot %422, %arg103, precision = [DEFAULT, DEFAULT] : (tensor<?x248xf32>, tensor<248x64xf32>) -> tensor<?x64xf32>
    %424 = shape.shape_of %423 : tensor<?x64xf32> -> tensor<2xindex>
    %425 = stablehlo.dynamic_broadcast_in_dim %arg104, %424, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %426 = stablehlo.add %423, %425 : tensor<?x64xf32>
    %427 = stablehlo.reduce(%arg105 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x50x108xf32>, tensor<f32>) -> tensor<?x108xf32>
    %428 = shape.shape_of %arg106 : tensor<?x5x124xf32> -> tensor<3xindex>
    %429 = shape.broadcast %428, %4 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %430 = stablehlo.dynamic_broadcast_in_dim %arg106, %429, dims = [0, 1, 2] : (tensor<?x5x124xf32>, tensor<3xindex>) -> tensor<?x5x124xf32>
    %431 = stablehlo.dynamic_broadcast_in_dim %arg107, %429, dims = [0, 1, 2] : (tensor<1x1x124xf32>, tensor<3xindex>) -> tensor<?x5x124xf32>
    %432 = stablehlo.add %430, %431 : tensor<?x5x124xf32>
    %433 = stablehlo.transpose %c_19, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %434 = stablehlo.reshape %433 : (tensor<2x3xi32>) -> tensor<6xi32>
    %435 = stablehlo.slice %434 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %436 = stablehlo.slice %434 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %437 = stablehlo.dynamic_pad %432, %cst_22, %435, %436, %c_31 : (tensor<?x5x124xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x30x124xf32>
    %438 = shape.shape_of %arg108 : tensor<?x30x124xf32> -> tensor<3xindex>
    %439 = shape.shape_of %437 : tensor<?x30x124xf32> -> tensor<3xindex>
    %440 = shape.broadcast %438, %439 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %441 = stablehlo.dynamic_broadcast_in_dim %arg108, %440, dims = [0, 1, 2] : (tensor<?x30x124xf32>, tensor<3xindex>) -> tensor<?x30x124xf32>
    %442 = stablehlo.dynamic_broadcast_in_dim %437, %440, dims = [0, 1, 2] : (tensor<?x30x124xf32>, tensor<3xindex>) -> tensor<?x30x124xf32>
    %443 = stablehlo.add %441, %442 : tensor<?x30x124xf32>
    %444 = stablehlo.logistic %443 : tensor<?x30x124xf32>
    %445 = shape.shape_of %443 : tensor<?x30x124xf32> -> tensor<3xindex>
    %446 = shape.shape_of %444 : tensor<?x30x124xf32> -> tensor<3xindex>
    %447 = shape.broadcast %445, %446 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %448 = stablehlo.dynamic_broadcast_in_dim %443, %447, dims = [0, 1, 2] : (tensor<?x30x124xf32>, tensor<3xindex>) -> tensor<?x30x124xf32>
    %449 = stablehlo.dynamic_broadcast_in_dim %444, %447, dims = [0, 1, 2] : (tensor<?x30x124xf32>, tensor<3xindex>) -> tensor<?x30x124xf32>
    %450 = stablehlo.multiply %448, %449 : tensor<?x30x124xf32>
    %451 = stablehlo.reduce(%450 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x30x124xf32>, tensor<f32>) -> tensor<?x124xf32>
    %452 = shape.shape_of %arg109 : tensor<?x28x30xf32> -> tensor<3xindex>
    %453 = shape.broadcast %452, %5 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %454 = stablehlo.dynamic_broadcast_in_dim %arg109, %453, dims = [0, 1, 2] : (tensor<?x28x30xf32>, tensor<3xindex>) -> tensor<?x28x30xf32>
    %455 = stablehlo.dynamic_broadcast_in_dim %arg110, %453, dims = [0, 1, 2] : (tensor<1x1x30xf32>, tensor<3xindex>) -> tensor<?x28x30xf32>
    %456 = stablehlo.add %454, %455 : tensor<?x28x30xf32>
    %457 = stablehlo.dynamic_pad %456, %cst_22, %404, %405, %c_31 : (tensor<?x28x30xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x124x30xf32>
    %458 = shape.shape_of %457 : tensor<?x124x30xf32> -> tensor<3xindex>
    %459 = shape.shape_of %arg111 : tensor<?x124x30xf32> -> tensor<3xindex>
    %460 = shape.broadcast %458, %459 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %461 = stablehlo.dynamic_broadcast_in_dim %457, %460, dims = [0, 1, 2] : (tensor<?x124x30xf32>, tensor<3xindex>) -> tensor<?x124x30xf32>
    %462 = stablehlo.dynamic_broadcast_in_dim %arg111, %460, dims = [0, 1, 2] : (tensor<?x124x30xf32>, tensor<3xindex>) -> tensor<?x124x30xf32>
    %463 = stablehlo.add %461, %462 : tensor<?x124x30xf32>
    %464 = stablehlo.logistic %463 : tensor<?x124x30xf32>
    %465 = shape.shape_of %463 : tensor<?x124x30xf32> -> tensor<3xindex>
    %466 = shape.shape_of %464 : tensor<?x124x30xf32> -> tensor<3xindex>
    %467 = shape.broadcast %465, %466 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %468 = stablehlo.dynamic_broadcast_in_dim %463, %467, dims = [0, 1, 2] : (tensor<?x124x30xf32>, tensor<3xindex>) -> tensor<?x124x30xf32>
    %469 = stablehlo.dynamic_broadcast_in_dim %464, %467, dims = [0, 1, 2] : (tensor<?x124x30xf32>, tensor<3xindex>) -> tensor<?x124x30xf32>
    %470 = stablehlo.multiply %468, %469 : tensor<?x124x30xf32>
    %471 = stablehlo.transpose %470, dims = [0, 2, 1] : (tensor<?x124x30xf32>) -> tensor<?x30x124xf32>
    %472 = stablehlo.reduce(%471 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x30x124xf32>, tensor<f32>) -> tensor<?x124xf32>
    %473 = stablehlo.concatenate %451, %472, dim = 1 : (tensor<?x124xf32>, tensor<?x124xf32>) -> tensor<?x248xf32>
    %474 = stablehlo.dot %473, %arg112, precision = [DEFAULT, DEFAULT] : (tensor<?x248xf32>, tensor<248x64xf32>) -> tensor<?x64xf32>
    %475 = shape.shape_of %474 : tensor<?x64xf32> -> tensor<2xindex>
    %476 = stablehlo.dynamic_broadcast_in_dim %arg113, %475, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %477 = stablehlo.add %474, %476 : tensor<?x64xf32>
    %478 = stablehlo.reduce(%arg114 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x60x88xf32>, tensor<f32>) -> tensor<?x88xf32>
    %479 = shape.shape_of %arg115 : tensor<?x12x88xf32> -> tensor<3xindex>
    %480 = shape.broadcast %479, %6 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %481 = stablehlo.dynamic_broadcast_in_dim %arg115, %480, dims = [0, 1, 2] : (tensor<?x12x88xf32>, tensor<3xindex>) -> tensor<?x12x88xf32>
    %482 = stablehlo.dynamic_broadcast_in_dim %arg116, %480, dims = [0, 1, 2] : (tensor<1x1x88xf32>, tensor<3xindex>) -> tensor<?x12x88xf32>
    %483 = stablehlo.add %481, %482 : tensor<?x12x88xf32>
    %484 = stablehlo.transpose %c_7, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %485 = stablehlo.reshape %484 : (tensor<2x3xi32>) -> tensor<6xi32>
    %486 = stablehlo.slice %485 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %487 = stablehlo.slice %485 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %488 = stablehlo.dynamic_pad %483, %cst_22, %486, %487, %c_31 : (tensor<?x12x88xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x60x88xf32>
    %489 = shape.shape_of %488 : tensor<?x60x88xf32> -> tensor<3xindex>
    %490 = shape.shape_of %arg117 : tensor<?x60x88xf32> -> tensor<3xindex>
    %491 = shape.broadcast %489, %490 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %492 = stablehlo.dynamic_broadcast_in_dim %488, %491, dims = [0, 1, 2] : (tensor<?x60x88xf32>, tensor<3xindex>) -> tensor<?x60x88xf32>
    %493 = stablehlo.dynamic_broadcast_in_dim %arg117, %491, dims = [0, 1, 2] : (tensor<?x60x88xf32>, tensor<3xindex>) -> tensor<?x60x88xf32>
    %494 = stablehlo.add %492, %493 : tensor<?x60x88xf32>
    %495 = stablehlo.logistic %494 : tensor<?x60x88xf32>
    %496 = shape.shape_of %494 : tensor<?x60x88xf32> -> tensor<3xindex>
    %497 = shape.shape_of %495 : tensor<?x60x88xf32> -> tensor<3xindex>
    %498 = shape.broadcast %496, %497 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %499 = stablehlo.dynamic_broadcast_in_dim %494, %498, dims = [0, 1, 2] : (tensor<?x60x88xf32>, tensor<3xindex>) -> tensor<?x60x88xf32>
    %500 = stablehlo.dynamic_broadcast_in_dim %495, %498, dims = [0, 1, 2] : (tensor<?x60x88xf32>, tensor<3xindex>) -> tensor<?x60x88xf32>
    %501 = stablehlo.multiply %499, %500 : tensor<?x60x88xf32>
    %502 = stablehlo.reduce(%501 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x60x88xf32>, tensor<f32>) -> tensor<?x88xf32>
    %503 = shape.shape_of %arg118 : tensor<?x19x60xf32> -> tensor<3xindex>
    %504 = shape.broadcast %503, %7 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %505 = stablehlo.dynamic_broadcast_in_dim %arg118, %504, dims = [0, 1, 2] : (tensor<?x19x60xf32>, tensor<3xindex>) -> tensor<?x19x60xf32>
    %506 = stablehlo.dynamic_broadcast_in_dim %arg119, %504, dims = [0, 1, 2] : (tensor<1x1x60xf32>, tensor<3xindex>) -> tensor<?x19x60xf32>
    %507 = stablehlo.add %505, %506 : tensor<?x19x60xf32>
    %508 = stablehlo.transpose %c_8, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %509 = stablehlo.reshape %508 : (tensor<2x3xi32>) -> tensor<6xi32>
    %510 = stablehlo.slice %509 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %511 = stablehlo.slice %509 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %512 = stablehlo.dynamic_pad %507, %cst_22, %510, %511, %c_31 : (tensor<?x19x60xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x88x60xf32>
    %513 = shape.shape_of %512 : tensor<?x88x60xf32> -> tensor<3xindex>
    %514 = shape.shape_of %arg120 : tensor<?x88x60xf32> -> tensor<3xindex>
    %515 = shape.broadcast %513, %514 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %516 = stablehlo.dynamic_broadcast_in_dim %512, %515, dims = [0, 1, 2] : (tensor<?x88x60xf32>, tensor<3xindex>) -> tensor<?x88x60xf32>
    %517 = stablehlo.dynamic_broadcast_in_dim %arg120, %515, dims = [0, 1, 2] : (tensor<?x88x60xf32>, tensor<3xindex>) -> tensor<?x88x60xf32>
    %518 = stablehlo.add %516, %517 : tensor<?x88x60xf32>
    %519 = stablehlo.logistic %518 : tensor<?x88x60xf32>
    %520 = shape.shape_of %518 : tensor<?x88x60xf32> -> tensor<3xindex>
    %521 = shape.shape_of %519 : tensor<?x88x60xf32> -> tensor<3xindex>
    %522 = shape.broadcast %520, %521 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %523 = stablehlo.dynamic_broadcast_in_dim %518, %522, dims = [0, 1, 2] : (tensor<?x88x60xf32>, tensor<3xindex>) -> tensor<?x88x60xf32>
    %524 = stablehlo.dynamic_broadcast_in_dim %519, %522, dims = [0, 1, 2] : (tensor<?x88x60xf32>, tensor<3xindex>) -> tensor<?x88x60xf32>
    %525 = stablehlo.multiply %523, %524 : tensor<?x88x60xf32>
    %526 = stablehlo.transpose %525, dims = [0, 2, 1] : (tensor<?x88x60xf32>) -> tensor<?x60x88xf32>
    %527 = stablehlo.reduce(%526 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x60x88xf32>, tensor<f32>) -> tensor<?x88xf32>
    %528 = stablehlo.concatenate %502, %527, dim = 1 : (tensor<?x88xf32>, tensor<?x88xf32>) -> tensor<?x176xf32>
    %529 = stablehlo.dot %528, %arg121, precision = [DEFAULT, DEFAULT] : (tensor<?x176xf32>, tensor<176x80xf32>) -> tensor<?x80xf32>
    %530 = shape.shape_of %529 : tensor<?x80xf32> -> tensor<2xindex>
    %531 = stablehlo.dynamic_broadcast_in_dim %arg122, %530, dims = [1] : (tensor<80xf32>, tensor<2xindex>) -> tensor<?x80xf32>
    %532 = stablehlo.add %529, %531 : tensor<?x80xf32>
    %533 = shape.shape_of %arg123 : tensor<?x13x128xf32> -> tensor<3xindex>
    %534 = shape.broadcast %533, %8 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %535 = stablehlo.dynamic_broadcast_in_dim %arg123, %534, dims = [0, 1, 2] : (tensor<?x13x128xf32>, tensor<3xindex>) -> tensor<?x13x128xf32>
    %536 = stablehlo.dynamic_broadcast_in_dim %arg124, %534, dims = [0, 1, 2] : (tensor<1x1x128xf32>, tensor<3xindex>) -> tensor<?x13x128xf32>
    %537 = stablehlo.add %535, %536 : tensor<?x13x128xf32>
    %538 = stablehlo.transpose %c_9, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %539 = stablehlo.reshape %538 : (tensor<2x3xi32>) -> tensor<6xi32>
    %540 = stablehlo.slice %539 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %541 = stablehlo.slice %539 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %542 = stablehlo.dynamic_pad %537, %cst_22, %540, %541, %c_31 : (tensor<?x13x128xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x64x128xf32>
    %543 = shape.shape_of %542 : tensor<?x64x128xf32> -> tensor<3xindex>
    %544 = shape.shape_of %arg125 : tensor<?x64x128xf32> -> tensor<3xindex>
    %545 = shape.broadcast %543, %544 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %546 = stablehlo.dynamic_broadcast_in_dim %542, %545, dims = [0, 1, 2] : (tensor<?x64x128xf32>, tensor<3xindex>) -> tensor<?x64x128xf32>
    %547 = stablehlo.dynamic_broadcast_in_dim %arg125, %545, dims = [0, 1, 2] : (tensor<?x64x128xf32>, tensor<3xindex>) -> tensor<?x64x128xf32>
    %548 = stablehlo.add %546, %547 : tensor<?x64x128xf32>
    %549 = stablehlo.logistic %548 : tensor<?x64x128xf32>
    %550 = shape.shape_of %548 : tensor<?x64x128xf32> -> tensor<3xindex>
    %551 = shape.shape_of %549 : tensor<?x64x128xf32> -> tensor<3xindex>
    %552 = shape.broadcast %550, %551 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %553 = stablehlo.dynamic_broadcast_in_dim %548, %552, dims = [0, 1, 2] : (tensor<?x64x128xf32>, tensor<3xindex>) -> tensor<?x64x128xf32>
    %554 = stablehlo.dynamic_broadcast_in_dim %549, %552, dims = [0, 1, 2] : (tensor<?x64x128xf32>, tensor<3xindex>) -> tensor<?x64x128xf32>
    %555 = stablehlo.multiply %553, %554 : tensor<?x64x128xf32>
    %556 = stablehlo.reduce(%555 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x64x128xf32>, tensor<f32>) -> tensor<?x128xf32>
    %557 = shape.shape_of %arg126 : tensor<?x29x64xf32> -> tensor<3xindex>
    %558 = shape.broadcast %557, %9 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %559 = stablehlo.dynamic_broadcast_in_dim %arg126, %558, dims = [0, 1, 2] : (tensor<?x29x64xf32>, tensor<3xindex>) -> tensor<?x29x64xf32>
    %560 = stablehlo.dynamic_broadcast_in_dim %arg127, %558, dims = [0, 1, 2] : (tensor<1x1x64xf32>, tensor<3xindex>) -> tensor<?x29x64xf32>
    %561 = stablehlo.add %559, %560 : tensor<?x29x64xf32>
    %562 = stablehlo.transpose %c_10, dims = [1, 0] : (tensor<3x2xi32>) -> tensor<2x3xi32>
    %563 = stablehlo.reshape %562 : (tensor<2x3xi32>) -> tensor<6xi32>
    %564 = stablehlo.slice %563 [0:3] : (tensor<6xi32>) -> tensor<3xi32>
    %565 = stablehlo.slice %563 [3:6] : (tensor<6xi32>) -> tensor<3xi32>
    %566 = stablehlo.dynamic_pad %561, %cst_22, %564, %565, %c_31 : (tensor<?x29x64xf32>, tensor<f32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<?x128x64xf32>
    %567 = shape.shape_of %566 : tensor<?x128x64xf32> -> tensor<3xindex>
    %568 = shape.shape_of %arg128 : tensor<?x128x64xf32> -> tensor<3xindex>
    %569 = shape.broadcast %567, %568 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %570 = stablehlo.dynamic_broadcast_in_dim %566, %569, dims = [0, 1, 2] : (tensor<?x128x64xf32>, tensor<3xindex>) -> tensor<?x128x64xf32>
    %571 = stablehlo.dynamic_broadcast_in_dim %arg128, %569, dims = [0, 1, 2] : (tensor<?x128x64xf32>, tensor<3xindex>) -> tensor<?x128x64xf32>
    %572 = stablehlo.add %570, %571 : tensor<?x128x64xf32>
    %573 = stablehlo.logistic %572 : tensor<?x128x64xf32>
    %574 = shape.shape_of %572 : tensor<?x128x64xf32> -> tensor<3xindex>
    %575 = shape.shape_of %573 : tensor<?x128x64xf32> -> tensor<3xindex>
    %576 = shape.broadcast %574, %575 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %577 = stablehlo.dynamic_broadcast_in_dim %572, %576, dims = [0, 1, 2] : (tensor<?x128x64xf32>, tensor<3xindex>) -> tensor<?x128x64xf32>
    %578 = stablehlo.dynamic_broadcast_in_dim %573, %576, dims = [0, 1, 2] : (tensor<?x128x64xf32>, tensor<3xindex>) -> tensor<?x128x64xf32>
    %579 = stablehlo.multiply %577, %578 : tensor<?x128x64xf32>
    %580 = stablehlo.transpose %579, dims = [0, 2, 1] : (tensor<?x128x64xf32>) -> tensor<?x64x128xf32>
    %581 = stablehlo.reduce(%580 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x64x128xf32>, tensor<f32>) -> tensor<?x128xf32>
    %582 = stablehlo.concatenate %556, %581, dim = 1 : (tensor<?x128xf32>, tensor<?x128xf32>) -> tensor<?x256xf32>
    %583 = stablehlo.dot %582, %arg129, precision = [DEFAULT, DEFAULT] : (tensor<?x256xf32>, tensor<256x80xf32>) -> tensor<?x80xf32>
    %584 = shape.shape_of %583 : tensor<?x80xf32> -> tensor<2xindex>
    %585 = stablehlo.dynamic_broadcast_in_dim %arg130, %584, dims = [1] : (tensor<80xf32>, tensor<2xindex>) -> tensor<?x80xf32>
    %586 = stablehlo.add %583, %585 : tensor<?x80xf32>
    %dim_66 = tensor.dim %arg131, %c0 : tensor<?x30x32xf32>
    %from_elements_67 = tensor.from_elements %c1, %dim_66, %c30, %c32_32 : tensor<4xindex>
    %dim_68 = tensor.dim %arg131, %c0 : tensor<?x30x32xf32>
    %expanded = tensor.expand_shape %arg131 [[0, 1], [2], [3]] output_shape [1, %dim_68, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %dim_69 = tensor.dim %arg132, %c0 : tensor<?x1x32xf32>
    %from_elements_70 = tensor.from_elements %c1, %dim_69, %c1, %c32_32 : tensor<4xindex>
    %dim_71 = tensor.dim %arg132, %c0 : tensor<?x1x32xf32>
    %expanded_72 = tensor.expand_shape %arg132 [[0, 1], [2], [3]] output_shape [1, %dim_71, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_73, %tail_74 = "shape.split_at"(%from_elements_70, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_75, %tail_76 = "shape.split_at"(%from_elements_67, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %587 = shape.broadcast %head_73, %head_75 : !shape.shape, !shape.shape -> !shape.shape
    %588 = shape.concat %587, %tail_74 : !shape.shape, !shape.shape -> !shape.shape
    %589 = shape.to_extent_tensor %588 : !shape.shape -> tensor<4xindex>
    %590 = stablehlo.dynamic_broadcast_in_dim %expanded_72, %589, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %591 = shape.concat %587, %tail_76 : !shape.shape, !shape.shape -> !shape.shape
    %592 = shape.to_extent_tensor %591 : !shape.shape -> tensor<4xindex>
    %593 = stablehlo.dynamic_broadcast_in_dim %expanded, %592, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %594 = stablehlo.dot_general %590, %593, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x30xf32>
    %595 = shape.shape_of %594 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %596 = stablehlo.dynamic_broadcast_in_dim %cst, %595, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %597 = stablehlo.multiply %594, %596 : tensor<1x?x1x30xf32>
    %598 = shape.shape_of %70 : tensor<?x1x30xf32> -> tensor<3xindex>
    %599 = shape.shape_of %597 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %600 = shape.broadcast %598, %599 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %601 = stablehlo.dynamic_broadcast_in_dim %70, %600, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %602 = stablehlo.dynamic_broadcast_in_dim %597, %600, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %603 = stablehlo.add %601, %602 : tensor<1x?x1x30xf32>
    %604 = stablehlo.reduce(%603 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_77 = tensor.dim %604, %c1 : tensor<1x?x1xf32>
    %from_elements_78 = tensor.from_elements %c1, %dim_77, %c1, %c1 : tensor<4xindex>
    %dim_79 = tensor.dim %604, %c1 : tensor<1x?x1xf32>
    %expanded_80 = tensor.expand_shape %604 [[0], [1], [2, 3]] output_shape [1, %dim_79, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %605 = shape.shape_of %603 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %606 = shape.broadcast %605, %from_elements_78 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %607 = stablehlo.dynamic_broadcast_in_dim %603, %606, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %608 = stablehlo.dynamic_broadcast_in_dim %expanded_80, %606, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %609 = stablehlo.subtract %607, %608 : tensor<1x?x1x30xf32>
    %610 = stablehlo.exponential %609 : tensor<1x?x1x30xf32>
    %611 = stablehlo.reduce(%610 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_81 = tensor.dim %611, %c1 : tensor<1x?x1xf32>
    %from_elements_82 = tensor.from_elements %c1, %dim_81, %c1, %c1 : tensor<4xindex>
    %dim_83 = tensor.dim %611, %c1 : tensor<1x?x1xf32>
    %expanded_84 = tensor.expand_shape %611 [[0], [1], [2, 3]] output_shape [1, %dim_83, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %612 = shape.shape_of %610 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %613 = shape.broadcast %612, %from_elements_82 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %614 = stablehlo.dynamic_broadcast_in_dim %610, %613, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %615 = stablehlo.dynamic_broadcast_in_dim %expanded_84, %613, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %616 = stablehlo.divide %614, %615 : tensor<1x?x1x30xf32>
    %dim_85 = tensor.dim %arg133, %c0 : tensor<?x30x32xf32>
    %from_elements_86 = tensor.from_elements %c1, %dim_85, %c30, %c32_32 : tensor<4xindex>
    %dim_87 = tensor.dim %arg133, %c0 : tensor<?x30x32xf32>
    %expanded_88 = tensor.expand_shape %arg133 [[0, 1], [2], [3]] output_shape [1, %dim_87, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %617 = shape.shape_of %616 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_89, %tail_90 = "shape.split_at"(%617, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_91, %tail_92 = "shape.split_at"(%from_elements_86, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %618 = shape.broadcast %head_89, %head_91 : !shape.shape, !shape.shape -> !shape.shape
    %619 = shape.concat %618, %tail_90 : !shape.shape, !shape.shape -> !shape.shape
    %620 = shape.to_extent_tensor %619 : !shape.shape -> tensor<4xindex>
    %621 = stablehlo.dynamic_broadcast_in_dim %616, %620, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %622 = shape.concat %618, %tail_92 : !shape.shape, !shape.shape -> !shape.shape
    %623 = shape.to_extent_tensor %622 : !shape.shape -> tensor<4xindex>
    %624 = stablehlo.dynamic_broadcast_in_dim %expanded_88, %623, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %625 = stablehlo.dot_general %621, %624, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x32xf32>
    %626 = stablehlo.transpose %625, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_93 = tensor.collapse_shape %626 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_94 = tensor.dim %arg134, %c0 : tensor<?x50x32xf32>
    %from_elements_95 = tensor.from_elements %c1, %dim_94, %c50, %c32_32 : tensor<4xindex>
    %dim_96 = tensor.dim %arg134, %c0 : tensor<?x50x32xf32>
    %expanded_97 = tensor.expand_shape %arg134 [[0, 1], [2], [3]] output_shape [1, %dim_96, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %dim_98 = tensor.dim %arg135, %c0 : tensor<?x1x32xf32>
    %from_elements_99 = tensor.from_elements %c1, %dim_98, %c1, %c32_32 : tensor<4xindex>
    %dim_100 = tensor.dim %arg135, %c0 : tensor<?x1x32xf32>
    %expanded_101 = tensor.expand_shape %arg135 [[0, 1], [2], [3]] output_shape [1, %dim_100, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_102, %tail_103 = "shape.split_at"(%from_elements_99, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_104, %tail_105 = "shape.split_at"(%from_elements_95, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %627 = shape.broadcast %head_102, %head_104 : !shape.shape, !shape.shape -> !shape.shape
    %628 = shape.concat %627, %tail_103 : !shape.shape, !shape.shape -> !shape.shape
    %629 = shape.to_extent_tensor %628 : !shape.shape -> tensor<4xindex>
    %630 = stablehlo.dynamic_broadcast_in_dim %expanded_101, %629, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %631 = shape.concat %627, %tail_105 : !shape.shape, !shape.shape -> !shape.shape
    %632 = shape.to_extent_tensor %631 : !shape.shape -> tensor<4xindex>
    %633 = stablehlo.dynamic_broadcast_in_dim %expanded_97, %632, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %634 = stablehlo.dot_general %630, %633, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x50xf32>
    %635 = shape.shape_of %634 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %636 = stablehlo.dynamic_broadcast_in_dim %cst, %635, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %637 = stablehlo.multiply %634, %636 : tensor<1x?x1x50xf32>
    %638 = shape.shape_of %91 : tensor<?x1x50xf32> -> tensor<3xindex>
    %639 = shape.shape_of %637 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %640 = shape.broadcast %638, %639 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %641 = stablehlo.dynamic_broadcast_in_dim %91, %640, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %642 = stablehlo.dynamic_broadcast_in_dim %637, %640, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %643 = stablehlo.add %641, %642 : tensor<1x?x1x50xf32>
    %644 = stablehlo.reduce(%643 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_106 = tensor.dim %644, %c1 : tensor<1x?x1xf32>
    %from_elements_107 = tensor.from_elements %c1, %dim_106, %c1, %c1 : tensor<4xindex>
    %dim_108 = tensor.dim %644, %c1 : tensor<1x?x1xf32>
    %expanded_109 = tensor.expand_shape %644 [[0], [1], [2, 3]] output_shape [1, %dim_108, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %645 = shape.shape_of %643 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %646 = shape.broadcast %645, %from_elements_107 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %647 = stablehlo.dynamic_broadcast_in_dim %643, %646, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %648 = stablehlo.dynamic_broadcast_in_dim %expanded_109, %646, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %649 = stablehlo.subtract %647, %648 : tensor<1x?x1x50xf32>
    %650 = stablehlo.exponential %649 : tensor<1x?x1x50xf32>
    %651 = stablehlo.reduce(%650 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_110 = tensor.dim %651, %c1 : tensor<1x?x1xf32>
    %from_elements_111 = tensor.from_elements %c1, %dim_110, %c1, %c1 : tensor<4xindex>
    %dim_112 = tensor.dim %651, %c1 : tensor<1x?x1xf32>
    %expanded_113 = tensor.expand_shape %651 [[0], [1], [2, 3]] output_shape [1, %dim_112, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %652 = shape.shape_of %650 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %653 = shape.broadcast %652, %from_elements_111 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %654 = stablehlo.dynamic_broadcast_in_dim %650, %653, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %655 = stablehlo.dynamic_broadcast_in_dim %expanded_113, %653, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %656 = stablehlo.divide %654, %655 : tensor<1x?x1x50xf32>
    %dim_114 = tensor.dim %arg136, %c0 : tensor<?x50x32xf32>
    %from_elements_115 = tensor.from_elements %c1, %dim_114, %c50, %c32_32 : tensor<4xindex>
    %dim_116 = tensor.dim %arg136, %c0 : tensor<?x50x32xf32>
    %expanded_117 = tensor.expand_shape %arg136 [[0, 1], [2], [3]] output_shape [1, %dim_116, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %657 = shape.shape_of %656 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_118, %tail_119 = "shape.split_at"(%657, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_120, %tail_121 = "shape.split_at"(%from_elements_115, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %658 = shape.broadcast %head_118, %head_120 : !shape.shape, !shape.shape -> !shape.shape
    %659 = shape.concat %658, %tail_119 : !shape.shape, !shape.shape -> !shape.shape
    %660 = shape.to_extent_tensor %659 : !shape.shape -> tensor<4xindex>
    %661 = stablehlo.dynamic_broadcast_in_dim %656, %660, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %662 = shape.concat %658, %tail_121 : !shape.shape, !shape.shape -> !shape.shape
    %663 = shape.to_extent_tensor %662 : !shape.shape -> tensor<4xindex>
    %664 = stablehlo.dynamic_broadcast_in_dim %expanded_117, %663, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %665 = stablehlo.dot_general %661, %664, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x32xf32>
    %666 = stablehlo.transpose %665, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_122 = tensor.collapse_shape %666 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_123 = tensor.dim %arg137, %c0 : tensor<?x30x32xf32>
    %from_elements_124 = tensor.from_elements %c1, %dim_123, %c30, %c32_32 : tensor<4xindex>
    %dim_125 = tensor.dim %arg137, %c0 : tensor<?x30x32xf32>
    %expanded_126 = tensor.expand_shape %arg137 [[0, 1], [2], [3]] output_shape [1, %dim_125, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %dim_127 = tensor.dim %arg138, %c0 : tensor<?x1x32xf32>
    %from_elements_128 = tensor.from_elements %c1, %dim_127, %c1, %c32_32 : tensor<4xindex>
    %dim_129 = tensor.dim %arg138, %c0 : tensor<?x1x32xf32>
    %expanded_130 = tensor.expand_shape %arg138 [[0, 1], [2], [3]] output_shape [1, %dim_129, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_131, %tail_132 = "shape.split_at"(%from_elements_128, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_133, %tail_134 = "shape.split_at"(%from_elements_124, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %667 = shape.broadcast %head_131, %head_133 : !shape.shape, !shape.shape -> !shape.shape
    %668 = shape.concat %667, %tail_132 : !shape.shape, !shape.shape -> !shape.shape
    %669 = shape.to_extent_tensor %668 : !shape.shape -> tensor<4xindex>
    %670 = stablehlo.dynamic_broadcast_in_dim %expanded_130, %669, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %671 = shape.concat %667, %tail_134 : !shape.shape, !shape.shape -> !shape.shape
    %672 = shape.to_extent_tensor %671 : !shape.shape -> tensor<4xindex>
    %673 = stablehlo.dynamic_broadcast_in_dim %expanded_126, %672, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %674 = stablehlo.dot_general %670, %673, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x30xf32>
    %675 = shape.shape_of %674 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %676 = stablehlo.dynamic_broadcast_in_dim %cst, %675, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %677 = stablehlo.multiply %674, %676 : tensor<1x?x1x30xf32>
    %678 = shape.shape_of %97 : tensor<?x1x30xf32> -> tensor<3xindex>
    %679 = shape.shape_of %677 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %680 = shape.broadcast %678, %679 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %681 = stablehlo.dynamic_broadcast_in_dim %97, %680, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %682 = stablehlo.dynamic_broadcast_in_dim %677, %680, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %683 = stablehlo.add %681, %682 : tensor<1x?x1x30xf32>
    %684 = stablehlo.reduce(%683 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_135 = tensor.dim %684, %c1 : tensor<1x?x1xf32>
    %from_elements_136 = tensor.from_elements %c1, %dim_135, %c1, %c1 : tensor<4xindex>
    %dim_137 = tensor.dim %684, %c1 : tensor<1x?x1xf32>
    %expanded_138 = tensor.expand_shape %684 [[0], [1], [2, 3]] output_shape [1, %dim_137, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %685 = shape.shape_of %683 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %686 = shape.broadcast %685, %from_elements_136 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %687 = stablehlo.dynamic_broadcast_in_dim %683, %686, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %688 = stablehlo.dynamic_broadcast_in_dim %expanded_138, %686, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %689 = stablehlo.subtract %687, %688 : tensor<1x?x1x30xf32>
    %690 = stablehlo.exponential %689 : tensor<1x?x1x30xf32>
    %691 = stablehlo.reduce(%690 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_139 = tensor.dim %691, %c1 : tensor<1x?x1xf32>
    %from_elements_140 = tensor.from_elements %c1, %dim_139, %c1, %c1 : tensor<4xindex>
    %dim_141 = tensor.dim %691, %c1 : tensor<1x?x1xf32>
    %expanded_142 = tensor.expand_shape %691 [[0], [1], [2, 3]] output_shape [1, %dim_141, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %692 = shape.shape_of %690 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %693 = shape.broadcast %692, %from_elements_140 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %694 = stablehlo.dynamic_broadcast_in_dim %690, %693, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %695 = stablehlo.dynamic_broadcast_in_dim %expanded_142, %693, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %696 = stablehlo.divide %694, %695 : tensor<1x?x1x30xf32>
    %697 = stablehlo.transpose %683, dims = [1, 0, 2, 3] : (tensor<1x?x1x30xf32>) -> tensor<?x1x1x30xf32>
    %collapsed_143 = tensor.collapse_shape %697 [[0], [1, 2, 3]] : tensor<?x1x1x30xf32> into tensor<?x30xf32>
    %dim_144 = tensor.dim %arg139, %c0 : tensor<?x30x32xf32>
    %from_elements_145 = tensor.from_elements %c1, %dim_144, %c30, %c32_32 : tensor<4xindex>
    %dim_146 = tensor.dim %arg139, %c0 : tensor<?x30x32xf32>
    %expanded_147 = tensor.expand_shape %arg139 [[0, 1], [2], [3]] output_shape [1, %dim_146, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %698 = shape.shape_of %696 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_148, %tail_149 = "shape.split_at"(%698, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_150, %tail_151 = "shape.split_at"(%from_elements_145, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %699 = shape.broadcast %head_148, %head_150 : !shape.shape, !shape.shape -> !shape.shape
    %700 = shape.concat %699, %tail_149 : !shape.shape, !shape.shape -> !shape.shape
    %701 = shape.to_extent_tensor %700 : !shape.shape -> tensor<4xindex>
    %702 = stablehlo.dynamic_broadcast_in_dim %696, %701, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %703 = shape.concat %699, %tail_151 : !shape.shape, !shape.shape -> !shape.shape
    %704 = shape.to_extent_tensor %703 : !shape.shape -> tensor<4xindex>
    %705 = stablehlo.dynamic_broadcast_in_dim %expanded_147, %704, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %706 = stablehlo.dot_general %702, %705, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x32xf32>
    %707 = stablehlo.transpose %706, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %708 = shape.shape_of %707 : tensor<?x1x1x32xf32> -> tensor<4xindex>
    %709 = shape.num_elements %708 : tensor<4xindex> -> index
    %710 = shape.index_to_size %709
    %711 = shape.div %710, %c32 : !shape.size, !shape.size -> !shape.size
    %712 = shape.from_extents %711, %c32 : !shape.size, !shape.size
    %713 = shape.to_extent_tensor %712 : !shape.shape -> tensor<2xindex>
    %collapsed_152 = tensor.collapse_shape %707 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_153 = tensor.dim %arg140, %c0 : tensor<?x50x32xf32>
    %from_elements_154 = tensor.from_elements %c1, %dim_153, %c50, %c32_32 : tensor<4xindex>
    %dim_155 = tensor.dim %arg140, %c0 : tensor<?x50x32xf32>
    %expanded_156 = tensor.expand_shape %arg140 [[0, 1], [2], [3]] output_shape [1, %dim_155, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %dim_157 = tensor.dim %arg141, %c0 : tensor<?x1x32xf32>
    %from_elements_158 = tensor.from_elements %c1, %dim_157, %c1, %c32_32 : tensor<4xindex>
    %dim_159 = tensor.dim %arg141, %c0 : tensor<?x1x32xf32>
    %expanded_160 = tensor.expand_shape %arg141 [[0, 1], [2], [3]] output_shape [1, %dim_159, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_161, %tail_162 = "shape.split_at"(%from_elements_158, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_163, %tail_164 = "shape.split_at"(%from_elements_154, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %714 = shape.broadcast %head_161, %head_163 : !shape.shape, !shape.shape -> !shape.shape
    %715 = shape.concat %714, %tail_162 : !shape.shape, !shape.shape -> !shape.shape
    %716 = shape.to_extent_tensor %715 : !shape.shape -> tensor<4xindex>
    %717 = stablehlo.dynamic_broadcast_in_dim %expanded_160, %716, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %718 = shape.concat %714, %tail_164 : !shape.shape, !shape.shape -> !shape.shape
    %719 = shape.to_extent_tensor %718 : !shape.shape -> tensor<4xindex>
    %720 = stablehlo.dynamic_broadcast_in_dim %expanded_156, %719, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %721 = stablehlo.dot_general %717, %720, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x50xf32>
    %722 = shape.shape_of %721 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %723 = stablehlo.dynamic_broadcast_in_dim %cst, %722, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %724 = stablehlo.multiply %721, %723 : tensor<1x?x1x50xf32>
    %725 = shape.shape_of %94 : tensor<?x1x50xf32> -> tensor<3xindex>
    %726 = shape.shape_of %724 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %727 = shape.broadcast %725, %726 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %728 = stablehlo.dynamic_broadcast_in_dim %94, %727, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %729 = stablehlo.dynamic_broadcast_in_dim %724, %727, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %730 = stablehlo.add %728, %729 : tensor<1x?x1x50xf32>
    %731 = stablehlo.reduce(%730 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_165 = tensor.dim %731, %c1 : tensor<1x?x1xf32>
    %from_elements_166 = tensor.from_elements %c1, %dim_165, %c1, %c1 : tensor<4xindex>
    %dim_167 = tensor.dim %731, %c1 : tensor<1x?x1xf32>
    %expanded_168 = tensor.expand_shape %731 [[0], [1], [2, 3]] output_shape [1, %dim_167, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %732 = shape.shape_of %730 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %733 = shape.broadcast %732, %from_elements_166 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %734 = stablehlo.dynamic_broadcast_in_dim %730, %733, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %735 = stablehlo.dynamic_broadcast_in_dim %expanded_168, %733, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %736 = stablehlo.subtract %734, %735 : tensor<1x?x1x50xf32>
    %737 = stablehlo.exponential %736 : tensor<1x?x1x50xf32>
    %738 = stablehlo.reduce(%737 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_169 = tensor.dim %738, %c1 : tensor<1x?x1xf32>
    %from_elements_170 = tensor.from_elements %c1, %dim_169, %c1, %c1 : tensor<4xindex>
    %dim_171 = tensor.dim %738, %c1 : tensor<1x?x1xf32>
    %expanded_172 = tensor.expand_shape %738 [[0], [1], [2, 3]] output_shape [1, %dim_171, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %739 = shape.shape_of %737 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %740 = shape.broadcast %739, %from_elements_170 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %741 = stablehlo.dynamic_broadcast_in_dim %737, %740, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %742 = stablehlo.dynamic_broadcast_in_dim %expanded_172, %740, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %743 = stablehlo.divide %741, %742 : tensor<1x?x1x50xf32>
    %744 = stablehlo.transpose %730, dims = [1, 0, 2, 3] : (tensor<1x?x1x50xf32>) -> tensor<?x1x1x50xf32>
    %collapsed_173 = tensor.collapse_shape %744 [[0], [1, 2, 3]] : tensor<?x1x1x50xf32> into tensor<?x50xf32>
    %dim_174 = tensor.dim %arg142, %c0 : tensor<?x50x32xf32>
    %from_elements_175 = tensor.from_elements %c1, %dim_174, %c50, %c32_32 : tensor<4xindex>
    %dim_176 = tensor.dim %arg142, %c0 : tensor<?x50x32xf32>
    %expanded_177 = tensor.expand_shape %arg142 [[0, 1], [2], [3]] output_shape [1, %dim_176, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %745 = shape.shape_of %743 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_178, %tail_179 = "shape.split_at"(%745, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_180, %tail_181 = "shape.split_at"(%from_elements_175, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %746 = shape.broadcast %head_178, %head_180 : !shape.shape, !shape.shape -> !shape.shape
    %747 = shape.concat %746, %tail_179 : !shape.shape, !shape.shape -> !shape.shape
    %748 = shape.to_extent_tensor %747 : !shape.shape -> tensor<4xindex>
    %749 = stablehlo.dynamic_broadcast_in_dim %743, %748, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %750 = shape.concat %746, %tail_181 : !shape.shape, !shape.shape -> !shape.shape
    %751 = shape.to_extent_tensor %750 : !shape.shape -> tensor<4xindex>
    %752 = stablehlo.dynamic_broadcast_in_dim %expanded_177, %751, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %753 = stablehlo.dot_general %749, %752, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x32xf32>
    %754 = stablehlo.transpose %753, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %755 = shape.shape_of %754 : tensor<?x1x1x32xf32> -> tensor<4xindex>
    %756 = shape.num_elements %755 : tensor<4xindex> -> index
    %757 = shape.index_to_size %756
    %758 = shape.div %757, %c32 : !shape.size, !shape.size -> !shape.size
    %759 = shape.from_extents %758, %c32 : !shape.size, !shape.size
    %760 = shape.to_extent_tensor %759 : !shape.shape -> tensor<2xindex>
    %collapsed_182 = tensor.collapse_shape %754 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_183 = tensor.dim %arg143, %c0 : tensor<?x10x32xf32>
    %from_elements_184 = tensor.from_elements %c1, %dim_183, %c10, %c32_32 : tensor<4xindex>
    %dim_185 = tensor.dim %arg143, %c0 : tensor<?x10x32xf32>
    %expanded_186 = tensor.expand_shape %arg143 [[0, 1], [2], [3]] output_shape [1, %dim_185, 10, 32] : tensor<?x10x32xf32> into tensor<1x?x10x32xf32>
    %dim_187 = tensor.dim %arg144, %c0 : tensor<?x1x32xf32>
    %from_elements_188 = tensor.from_elements %c1, %dim_187, %c1, %c32_32 : tensor<4xindex>
    %dim_189 = tensor.dim %arg144, %c0 : tensor<?x1x32xf32>
    %expanded_190 = tensor.expand_shape %arg144 [[0, 1], [2], [3]] output_shape [1, %dim_189, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_191, %tail_192 = "shape.split_at"(%from_elements_188, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_193, %tail_194 = "shape.split_at"(%from_elements_184, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %761 = shape.broadcast %head_191, %head_193 : !shape.shape, !shape.shape -> !shape.shape
    %762 = shape.concat %761, %tail_192 : !shape.shape, !shape.shape -> !shape.shape
    %763 = shape.to_extent_tensor %762 : !shape.shape -> tensor<4xindex>
    %764 = stablehlo.dynamic_broadcast_in_dim %expanded_190, %763, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %765 = shape.concat %761, %tail_194 : !shape.shape, !shape.shape -> !shape.shape
    %766 = shape.to_extent_tensor %765 : !shape.shape -> tensor<4xindex>
    %767 = stablehlo.dynamic_broadcast_in_dim %expanded_186, %766, dims = [0, 1, 2, 3] : (tensor<1x?x10x32xf32>, tensor<4xindex>) -> tensor<1x?x10x32xf32>
    %768 = stablehlo.dot_general %764, %767, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x10x32xf32>) -> tensor<1x?x1x10xf32>
    %769 = shape.shape_of %768 : tensor<1x?x1x10xf32> -> tensor<4xindex>
    %770 = stablehlo.dynamic_broadcast_in_dim %cst, %769, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %771 = stablehlo.multiply %768, %770 : tensor<1x?x1x10xf32>
    %772 = shape.shape_of %67 : tensor<?x1x10xf32> -> tensor<3xindex>
    %773 = shape.shape_of %771 : tensor<1x?x1x10xf32> -> tensor<4xindex>
    %774 = shape.broadcast %772, %773 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %775 = stablehlo.dynamic_broadcast_in_dim %67, %774, dims = [1, 2, 3] : (tensor<?x1x10xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %776 = stablehlo.dynamic_broadcast_in_dim %771, %774, dims = [0, 1, 2, 3] : (tensor<1x?x1x10xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %777 = stablehlo.add %775, %776 : tensor<1x?x1x10xf32>
    %778 = stablehlo.reduce(%777 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x10xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_195 = tensor.dim %778, %c1 : tensor<1x?x1xf32>
    %from_elements_196 = tensor.from_elements %c1, %dim_195, %c1, %c1 : tensor<4xindex>
    %dim_197 = tensor.dim %778, %c1 : tensor<1x?x1xf32>
    %expanded_198 = tensor.expand_shape %778 [[0], [1], [2, 3]] output_shape [1, %dim_197, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %779 = shape.shape_of %777 : tensor<1x?x1x10xf32> -> tensor<4xindex>
    %780 = shape.broadcast %779, %from_elements_196 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %781 = stablehlo.dynamic_broadcast_in_dim %777, %780, dims = [0, 1, 2, 3] : (tensor<1x?x1x10xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %782 = stablehlo.dynamic_broadcast_in_dim %expanded_198, %780, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %783 = stablehlo.subtract %781, %782 : tensor<1x?x1x10xf32>
    %784 = stablehlo.exponential %783 : tensor<1x?x1x10xf32>
    %785 = stablehlo.reduce(%784 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x10xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_199 = tensor.dim %785, %c1 : tensor<1x?x1xf32>
    %from_elements_200 = tensor.from_elements %c1, %dim_199, %c1, %c1 : tensor<4xindex>
    %dim_201 = tensor.dim %785, %c1 : tensor<1x?x1xf32>
    %expanded_202 = tensor.expand_shape %785 [[0], [1], [2, 3]] output_shape [1, %dim_201, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %786 = shape.shape_of %784 : tensor<1x?x1x10xf32> -> tensor<4xindex>
    %787 = shape.broadcast %786, %from_elements_200 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %788 = stablehlo.dynamic_broadcast_in_dim %784, %787, dims = [0, 1, 2, 3] : (tensor<1x?x1x10xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %789 = stablehlo.dynamic_broadcast_in_dim %expanded_202, %787, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %790 = stablehlo.divide %788, %789 : tensor<1x?x1x10xf32>
    %dim_203 = tensor.dim %arg145, %c0 : tensor<?x10x32xf32>
    %from_elements_204 = tensor.from_elements %c1, %dim_203, %c10, %c32_32 : tensor<4xindex>
    %dim_205 = tensor.dim %arg145, %c0 : tensor<?x10x32xf32>
    %expanded_206 = tensor.expand_shape %arg145 [[0, 1], [2], [3]] output_shape [1, %dim_205, 10, 32] : tensor<?x10x32xf32> into tensor<1x?x10x32xf32>
    %791 = shape.shape_of %790 : tensor<1x?x1x10xf32> -> tensor<4xindex>
    %head_207, %tail_208 = "shape.split_at"(%791, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_209, %tail_210 = "shape.split_at"(%from_elements_204, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %792 = shape.broadcast %head_207, %head_209 : !shape.shape, !shape.shape -> !shape.shape
    %793 = shape.concat %792, %tail_208 : !shape.shape, !shape.shape -> !shape.shape
    %794 = shape.to_extent_tensor %793 : !shape.shape -> tensor<4xindex>
    %795 = stablehlo.dynamic_broadcast_in_dim %790, %794, dims = [0, 1, 2, 3] : (tensor<1x?x1x10xf32>, tensor<4xindex>) -> tensor<1x?x1x10xf32>
    %796 = shape.concat %792, %tail_210 : !shape.shape, !shape.shape -> !shape.shape
    %797 = shape.to_extent_tensor %796 : !shape.shape -> tensor<4xindex>
    %798 = stablehlo.dynamic_broadcast_in_dim %expanded_206, %797, dims = [0, 1, 2, 3] : (tensor<1x?x10x32xf32>, tensor<4xindex>) -> tensor<1x?x10x32xf32>
    %799 = stablehlo.dot_general %795, %798, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x10xf32>, tensor<1x?x10x32xf32>) -> tensor<1x?x1x32xf32>
    %800 = stablehlo.transpose %799, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_211 = tensor.collapse_shape %800 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %801 = shape.shape_of %arg146 : tensor<?x1x64xf32> -> tensor<3xindex>
    %802 = shape.shape_of %arg147 : tensor<?x60x64xf32> -> tensor<3xindex>
    %head_212, %tail_213 = "shape.split_at"(%801, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_214, %tail_215 = "shape.split_at"(%802, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %803 = shape.broadcast %head_212, %head_214 : !shape.shape, !shape.shape -> !shape.shape
    %804 = shape.concat %803, %tail_213 : !shape.shape, !shape.shape -> !shape.shape
    %805 = shape.to_extent_tensor %804 : !shape.shape -> tensor<3xindex>
    %806 = stablehlo.dynamic_broadcast_in_dim %arg146, %805, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %807 = shape.concat %803, %tail_215 : !shape.shape, !shape.shape -> !shape.shape
    %808 = shape.to_extent_tensor %807 : !shape.shape -> tensor<3xindex>
    %809 = stablehlo.dynamic_broadcast_in_dim %arg147, %808, dims = [0, 1, 2] : (tensor<?x60x64xf32>, tensor<3xindex>) -> tensor<?x60x64xf32>
    %810 = stablehlo.dot_general %806, %809, batching_dims = [0] x [0], contracting_dims = [2] x [2], precision = [DEFAULT, DEFAULT] : (tensor<?x1x64xf32>, tensor<?x60x64xf32>) -> tensor<?x1x60xf32>
    %811 = shape.shape_of %810 : tensor<?x1x60xf32> -> tensor<3xindex>
    %812 = stablehlo.dynamic_broadcast_in_dim %cst_6, %811, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %813 = stablehlo.multiply %810, %812 : tensor<?x1x60xf32>
    %814 = shape.shape_of %76 : tensor<?x1x60xf32> -> tensor<3xindex>
    %815 = shape.shape_of %813 : tensor<?x1x60xf32> -> tensor<3xindex>
    %816 = shape.broadcast %814, %815 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %817 = stablehlo.dynamic_broadcast_in_dim %76, %816, dims = [0, 1, 2] : (tensor<?x1x60xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %818 = stablehlo.dynamic_broadcast_in_dim %813, %816, dims = [0, 1, 2] : (tensor<?x1x60xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %819 = stablehlo.add %817, %818 : tensor<?x1x60xf32>
    %dim_216 = tensor.dim %819, %c0 : tensor<?x1x60xf32>
    %expanded_217 = tensor.expand_shape %819 [[0, 1], [2], [3]] output_shape [1, %dim_216, 1, 60] : tensor<?x1x60xf32> into tensor<1x?x1x60xf32>
    %820 = stablehlo.transpose %expanded_217, dims = [1, 0, 2, 3] : (tensor<1x?x1x60xf32>) -> tensor<?x1x1x60xf32>
    %collapsed_218 = tensor.collapse_shape %820 [[0], [1, 2, 3]] : tensor<?x1x1x60xf32> into tensor<?x60xf32>
    %821 = stablehlo.concatenate %collapsed_218, %collapsed_173, dim = 1 : (tensor<?x60xf32>, tensor<?x50xf32>) -> tensor<?x110xf32>
    %822 = stablehlo.dot %821, %arg148, precision = [DEFAULT, DEFAULT] : (tensor<?x110xf32>, tensor<110x128xf32>) -> tensor<?x128xf32>
    %823 = shape.shape_of %822 : tensor<?x128xf32> -> tensor<2xindex>
    %824 = stablehlo.dynamic_broadcast_in_dim %arg149, %823, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %825 = stablehlo.add %822, %824 : tensor<?x128xf32>
    %826 = stablehlo.logistic %825 : tensor<?x128xf32>
    %827 = shape.shape_of %825 : tensor<?x128xf32> -> tensor<2xindex>
    %828 = shape.shape_of %826 : tensor<?x128xf32> -> tensor<2xindex>
    %829 = shape.broadcast %827, %828 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %830 = stablehlo.dynamic_broadcast_in_dim %825, %829, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %831 = stablehlo.dynamic_broadcast_in_dim %826, %829, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %832 = stablehlo.multiply %830, %831 : tensor<?x128xf32>
    %833 = stablehlo.dot %832, %arg150, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %834 = shape.shape_of %833 : tensor<?x64xf32> -> tensor<2xindex>
    %835 = stablehlo.dynamic_broadcast_in_dim %arg151, %834, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %836 = stablehlo.add %833, %835 : tensor<?x64xf32>
    %837 = stablehlo.dot %836, %arg152, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %838 = shape.shape_of %837 : tensor<?x64xf32> -> tensor<2xindex>
    %839 = stablehlo.dynamic_broadcast_in_dim %arg153, %838, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %840 = stablehlo.add %837, %839 : tensor<?x64xf32>
    %841 = stablehlo.logistic %840 : tensor<?x64xf32>
    %842 = shape.shape_of %841 : tensor<?x64xf32> -> tensor<2xindex>
    %843 = stablehlo.dynamic_broadcast_in_dim %cst_12, %842, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %844 = stablehlo.multiply %841, %843 : tensor<?x64xf32>
    %845 = stablehlo.dot %836, %arg154, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %846 = shape.shape_of %845 : tensor<?x32xf32> -> tensor<2xindex>
    %847 = stablehlo.dynamic_broadcast_in_dim %arg155, %846, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %848 = stablehlo.add %845, %847 : tensor<?x32xf32>
    %849 = stablehlo.logistic %848 : tensor<?x32xf32>
    %850 = shape.shape_of %849 : tensor<?x32xf32> -> tensor<2xindex>
    %851 = stablehlo.dynamic_broadcast_in_dim %cst_12, %850, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %852 = stablehlo.multiply %849, %851 : tensor<?x32xf32>
    %853 = shape.shape_of %852 : tensor<?x32xf32> -> tensor<2xindex>
    %854 = shape.broadcast %760, %853 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %855 = stablehlo.dynamic_broadcast_in_dim %collapsed_182, %854, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %856 = stablehlo.dynamic_broadcast_in_dim %852, %854, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %857 = stablehlo.multiply %855, %856 : tensor<?x32xf32>
    %858 = stablehlo.concatenate %collapsed_218, %collapsed_143, dim = 1 : (tensor<?x60xf32>, tensor<?x30xf32>) -> tensor<?x90xf32>
    %859 = stablehlo.dot %858, %arg156, precision = [DEFAULT, DEFAULT] : (tensor<?x90xf32>, tensor<90x128xf32>) -> tensor<?x128xf32>
    %860 = shape.shape_of %859 : tensor<?x128xf32> -> tensor<2xindex>
    %861 = stablehlo.dynamic_broadcast_in_dim %arg157, %860, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %862 = stablehlo.add %859, %861 : tensor<?x128xf32>
    %863 = stablehlo.logistic %862 : tensor<?x128xf32>
    %864 = shape.shape_of %862 : tensor<?x128xf32> -> tensor<2xindex>
    %865 = shape.shape_of %863 : tensor<?x128xf32> -> tensor<2xindex>
    %866 = shape.broadcast %864, %865 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %867 = stablehlo.dynamic_broadcast_in_dim %862, %866, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %868 = stablehlo.dynamic_broadcast_in_dim %863, %866, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %869 = stablehlo.multiply %867, %868 : tensor<?x128xf32>
    %870 = stablehlo.dot %869, %arg158, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %871 = shape.shape_of %870 : tensor<?x64xf32> -> tensor<2xindex>
    %872 = stablehlo.dynamic_broadcast_in_dim %arg159, %871, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %873 = stablehlo.add %870, %872 : tensor<?x64xf32>
    %874 = stablehlo.dot %873, %arg160, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %875 = shape.shape_of %874 : tensor<?x64xf32> -> tensor<2xindex>
    %876 = stablehlo.dynamic_broadcast_in_dim %arg161, %875, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %877 = stablehlo.add %874, %876 : tensor<?x64xf32>
    %878 = stablehlo.logistic %877 : tensor<?x64xf32>
    %879 = shape.shape_of %878 : tensor<?x64xf32> -> tensor<2xindex>
    %880 = stablehlo.dynamic_broadcast_in_dim %cst_12, %879, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %881 = stablehlo.multiply %878, %880 : tensor<?x64xf32>
    %882 = stablehlo.dot %873, %arg162, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %883 = shape.shape_of %882 : tensor<?x32xf32> -> tensor<2xindex>
    %884 = stablehlo.dynamic_broadcast_in_dim %arg163, %883, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %885 = stablehlo.add %882, %884 : tensor<?x32xf32>
    %886 = stablehlo.logistic %885 : tensor<?x32xf32>
    %887 = shape.shape_of %886 : tensor<?x32xf32> -> tensor<2xindex>
    %888 = stablehlo.dynamic_broadcast_in_dim %cst_12, %887, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %889 = stablehlo.multiply %886, %888 : tensor<?x32xf32>
    %890 = shape.shape_of %889 : tensor<?x32xf32> -> tensor<2xindex>
    %891 = shape.broadcast %713, %890 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %892 = stablehlo.dynamic_broadcast_in_dim %collapsed_152, %891, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %893 = stablehlo.dynamic_broadcast_in_dim %889, %891, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %894 = stablehlo.multiply %892, %893 : tensor<?x32xf32>
    %895 = stablehlo.reduce(%819 init: %cst_23) applies stablehlo.maximum across dimensions = [2] : (tensor<?x1x60xf32>, tensor<f32>) -> tensor<?x1xf32>
    %dim_219 = tensor.dim %895, %c0 : tensor<?x1xf32>
    %from_elements_220 = tensor.from_elements %dim_219, %c1, %c1 : tensor<3xindex>
    %dim_221 = tensor.dim %895, %c0 : tensor<?x1xf32>
    %expanded_222 = tensor.expand_shape %895 [[0], [1, 2]] output_shape [%dim_221, 1, 1] : tensor<?x1xf32> into tensor<?x1x1xf32>
    %896 = shape.shape_of %819 : tensor<?x1x60xf32> -> tensor<3xindex>
    %897 = shape.broadcast %896, %from_elements_220 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %898 = stablehlo.dynamic_broadcast_in_dim %819, %897, dims = [0, 1, 2] : (tensor<?x1x60xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %899 = stablehlo.dynamic_broadcast_in_dim %expanded_222, %897, dims = [0, 1, 2] : (tensor<?x1x1xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %900 = stablehlo.subtract %898, %899 : tensor<?x1x60xf32>
    %901 = stablehlo.exponential %900 : tensor<?x1x60xf32>
    %902 = stablehlo.reduce(%901 init: %cst_21) applies stablehlo.add across dimensions = [2] : (tensor<?x1x60xf32>, tensor<f32>) -> tensor<?x1xf32>
    %dim_223 = tensor.dim %902, %c0 : tensor<?x1xf32>
    %from_elements_224 = tensor.from_elements %dim_223, %c1, %c1 : tensor<3xindex>
    %dim_225 = tensor.dim %902, %c0 : tensor<?x1xf32>
    %expanded_226 = tensor.expand_shape %902 [[0], [1, 2]] output_shape [%dim_225, 1, 1] : tensor<?x1xf32> into tensor<?x1x1xf32>
    %903 = shape.shape_of %901 : tensor<?x1x60xf32> -> tensor<3xindex>
    %904 = shape.broadcast %903, %from_elements_224 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %905 = stablehlo.dynamic_broadcast_in_dim %901, %904, dims = [0, 1, 2] : (tensor<?x1x60xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %906 = stablehlo.dynamic_broadcast_in_dim %expanded_226, %904, dims = [0, 1, 2] : (tensor<?x1x1xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %907 = stablehlo.divide %905, %906 : tensor<?x1x60xf32>
    %908 = shape.shape_of %907 : tensor<?x1x60xf32> -> tensor<3xindex>
    %909 = shape.shape_of %arg164 : tensor<?x60x64xf32> -> tensor<3xindex>
    %head_227, %tail_228 = "shape.split_at"(%908, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_229, %tail_230 = "shape.split_at"(%909, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %910 = shape.broadcast %head_227, %head_229 : !shape.shape, !shape.shape -> !shape.shape
    %911 = shape.concat %910, %tail_228 : !shape.shape, !shape.shape -> !shape.shape
    %912 = shape.to_extent_tensor %911 : !shape.shape -> tensor<3xindex>
    %913 = stablehlo.dynamic_broadcast_in_dim %907, %912, dims = [0, 1, 2] : (tensor<?x1x60xf32>, tensor<3xindex>) -> tensor<?x1x60xf32>
    %914 = shape.concat %910, %tail_230 : !shape.shape, !shape.shape -> !shape.shape
    %915 = shape.to_extent_tensor %914 : !shape.shape -> tensor<3xindex>
    %916 = stablehlo.dynamic_broadcast_in_dim %arg164, %915, dims = [0, 1, 2] : (tensor<?x60x64xf32>, tensor<3xindex>) -> tensor<?x60x64xf32>
    %917 = stablehlo.dot_general %913, %916, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<?x1x60xf32>, tensor<?x60x64xf32>) -> tensor<?x1x64xf32>
    %918 = shape.shape_of %917 : tensor<?x1x64xf32> -> tensor<3xindex>
    %919 = shape.num_elements %918 : tensor<3xindex> -> index
    %920 = shape.index_to_size %919
    %921 = shape.div %920, %c64 : !shape.size, !shape.size -> !shape.size
    %922 = shape.from_extents %921, %c64 : !shape.size, !shape.size
    %923 = shape.to_extent_tensor %922 : !shape.shape -> tensor<2xindex>
    %collapsed_231 = tensor.collapse_shape %917 [[0], [1, 2]] : tensor<?x1x64xf32> into tensor<?x64xf32>
    %924 = shape.shape_of %844 : tensor<?x64xf32> -> tensor<2xindex>
    %925 = shape.broadcast %923, %924 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %926 = stablehlo.dynamic_broadcast_in_dim %collapsed_231, %925, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %927 = stablehlo.dynamic_broadcast_in_dim %844, %925, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %928 = stablehlo.multiply %926, %927 : tensor<?x64xf32>
    %929 = shape.shape_of %881 : tensor<?x64xf32> -> tensor<2xindex>
    %930 = shape.broadcast %923, %929 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %931 = stablehlo.dynamic_broadcast_in_dim %collapsed_231, %930, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %932 = stablehlo.dynamic_broadcast_in_dim %881, %930, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %933 = stablehlo.multiply %931, %932 : tensor<?x64xf32>
    %dim_232 = tensor.dim %arg165, %c0 : tensor<?x60x24xf32>
    %expanded_233 = tensor.expand_shape %arg165 [[0, 1], [2], [3]] output_shape [1, %dim_232, 60, 24] : tensor<?x60x24xf32> into tensor<1x?x60x24xf32>
    %dim_234 = tensor.dim %arg166, %c0 : tensor<?x60x24xf32>
    %expanded_235 = tensor.expand_shape %arg166 [[0, 1], [2], [3]] output_shape [1, %dim_234, 60, 24] : tensor<?x60x24xf32> into tensor<1x?x60x24xf32>
    %934 = stablehlo.concatenate %expanded_233, %expanded_235, dim = 0 : (tensor<1x?x60x24xf32>, tensor<1x?x60x24xf32>) -> tensor<2x?x60x24xf32>
    %dim_236 = tensor.dim %arg167, %c0 : tensor<?x1x24xf32>
    %expanded_237 = tensor.expand_shape %arg167 [[0, 1], [2], [3]] output_shape [1, %dim_236, 1, 24] : tensor<?x1x24xf32> into tensor<1x?x1x24xf32>
    %dim_238 = tensor.dim %arg168, %c0 : tensor<?x1x24xf32>
    %expanded_239 = tensor.expand_shape %arg168 [[0, 1], [2], [3]] output_shape [1, %dim_238, 1, 24] : tensor<?x1x24xf32> into tensor<1x?x1x24xf32>
    %935 = stablehlo.concatenate %expanded_237, %expanded_239, dim = 0 : (tensor<1x?x1x24xf32>, tensor<1x?x1x24xf32>) -> tensor<2x?x1x24xf32>
    %936 = shape.shape_of %935 : tensor<2x?x1x24xf32> -> tensor<4xindex>
    %937 = shape.shape_of %934 : tensor<2x?x60x24xf32> -> tensor<4xindex>
    %head_240, %tail_241 = "shape.split_at"(%936, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_242, %tail_243 = "shape.split_at"(%937, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %938 = shape.broadcast %head_240, %head_242 : !shape.shape, !shape.shape -> !shape.shape
    %939 = shape.concat %938, %tail_241 : !shape.shape, !shape.shape -> !shape.shape
    %940 = shape.to_extent_tensor %939 : !shape.shape -> tensor<4xindex>
    %941 = stablehlo.dynamic_broadcast_in_dim %935, %940, dims = [0, 1, 2, 3] : (tensor<2x?x1x24xf32>, tensor<4xindex>) -> tensor<2x?x1x24xf32>
    %942 = shape.concat %938, %tail_243 : !shape.shape, !shape.shape -> !shape.shape
    %943 = shape.to_extent_tensor %942 : !shape.shape -> tensor<4xindex>
    %944 = stablehlo.dynamic_broadcast_in_dim %934, %943, dims = [0, 1, 2, 3] : (tensor<2x?x60x24xf32>, tensor<4xindex>) -> tensor<2x?x60x24xf32>
    %945 = stablehlo.dot_general %941, %944, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x24xf32>, tensor<2x?x60x24xf32>) -> tensor<2x?x1x60xf32>
    %946 = shape.shape_of %945 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %947 = stablehlo.dynamic_broadcast_in_dim %cst_5, %946, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %948 = stablehlo.multiply %945, %947 : tensor<2x?x1x60xf32>
    %949 = shape.shape_of %948 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %950 = shape.broadcast %814, %949 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %951 = stablehlo.dynamic_broadcast_in_dim %76, %950, dims = [1, 2, 3] : (tensor<?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %952 = stablehlo.dynamic_broadcast_in_dim %948, %950, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %953 = stablehlo.add %951, %952 : tensor<2x?x1x60xf32>
    %954 = stablehlo.reduce(%953 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_244 = tensor.dim %954, %c1 : tensor<2x?x1xf32>
    %from_elements_245 = tensor.from_elements %c2, %dim_244, %c1, %c1 : tensor<4xindex>
    %dim_246 = tensor.dim %954, %c1 : tensor<2x?x1xf32>
    %expanded_247 = tensor.expand_shape %954 [[0], [1], [2, 3]] output_shape [2, %dim_246, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %955 = shape.shape_of %953 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %956 = shape.broadcast %955, %from_elements_245 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %957 = stablehlo.dynamic_broadcast_in_dim %953, %956, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %958 = stablehlo.dynamic_broadcast_in_dim %expanded_247, %956, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %959 = stablehlo.subtract %957, %958 : tensor<2x?x1x60xf32>
    %960 = stablehlo.exponential %959 : tensor<2x?x1x60xf32>
    %961 = stablehlo.reduce(%960 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_248 = tensor.dim %961, %c1 : tensor<2x?x1xf32>
    %from_elements_249 = tensor.from_elements %c2, %dim_248, %c1, %c1 : tensor<4xindex>
    %dim_250 = tensor.dim %961, %c1 : tensor<2x?x1xf32>
    %expanded_251 = tensor.expand_shape %961 [[0], [1], [2, 3]] output_shape [2, %dim_250, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %962 = shape.shape_of %960 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %963 = shape.broadcast %962, %from_elements_249 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %964 = stablehlo.dynamic_broadcast_in_dim %960, %963, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %965 = stablehlo.dynamic_broadcast_in_dim %expanded_251, %963, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %966 = stablehlo.divide %964, %965 : tensor<2x?x1x60xf32>
    %dim_252 = tensor.dim %arg169, %c0 : tensor<?x60x24xf32>
    %expanded_253 = tensor.expand_shape %arg169 [[0, 1], [2], [3]] output_shape [1, %dim_252, 60, 24] : tensor<?x60x24xf32> into tensor<1x?x60x24xf32>
    %dim_254 = tensor.dim %arg170, %c0 : tensor<?x60x24xf32>
    %expanded_255 = tensor.expand_shape %arg170 [[0, 1], [2], [3]] output_shape [1, %dim_254, 60, 24] : tensor<?x60x24xf32> into tensor<1x?x60x24xf32>
    %967 = stablehlo.concatenate %expanded_253, %expanded_255, dim = 0 : (tensor<1x?x60x24xf32>, tensor<1x?x60x24xf32>) -> tensor<2x?x60x24xf32>
    %968 = shape.shape_of %966 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %969 = shape.shape_of %967 : tensor<2x?x60x24xf32> -> tensor<4xindex>
    %head_256, %tail_257 = "shape.split_at"(%968, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_258, %tail_259 = "shape.split_at"(%969, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %970 = shape.broadcast %head_256, %head_258 : !shape.shape, !shape.shape -> !shape.shape
    %971 = shape.concat %970, %tail_257 : !shape.shape, !shape.shape -> !shape.shape
    %972 = shape.to_extent_tensor %971 : !shape.shape -> tensor<4xindex>
    %973 = stablehlo.dynamic_broadcast_in_dim %966, %972, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %974 = shape.concat %970, %tail_259 : !shape.shape, !shape.shape -> !shape.shape
    %975 = shape.to_extent_tensor %974 : !shape.shape -> tensor<4xindex>
    %976 = stablehlo.dynamic_broadcast_in_dim %967, %975, dims = [0, 1, 2, 3] : (tensor<2x?x60x24xf32>, tensor<4xindex>) -> tensor<2x?x60x24xf32>
    %977 = stablehlo.dot_general %973, %976, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x60xf32>, tensor<2x?x60x24xf32>) -> tensor<2x?x1x24xf32>
    %978 = stablehlo.transpose %977, dims = [1, 2, 0, 3] : (tensor<2x?x1x24xf32>) -> tensor<?x1x2x24xf32>
    %collapsed_260 = tensor.collapse_shape %978 [[0], [1, 2, 3]] : tensor<?x1x2x24xf32> into tensor<?x48xf32>
    %dim_261 = tensor.dim %arg171, %c0 : tensor<?x60x12xf32>
    %expanded_262 = tensor.expand_shape %arg171 [[0, 1], [2], [3]] output_shape [1, %dim_261, 60, 12] : tensor<?x60x12xf32> into tensor<1x?x60x12xf32>
    %dim_263 = tensor.dim %arg172, %c0 : tensor<?x60x12xf32>
    %expanded_264 = tensor.expand_shape %arg172 [[0, 1], [2], [3]] output_shape [1, %dim_263, 60, 12] : tensor<?x60x12xf32> into tensor<1x?x60x12xf32>
    %979 = stablehlo.concatenate %expanded_262, %expanded_264, dim = 0 : (tensor<1x?x60x12xf32>, tensor<1x?x60x12xf32>) -> tensor<2x?x60x12xf32>
    %dim_265 = tensor.dim %arg173, %c0 : tensor<?x1x12xf32>
    %expanded_266 = tensor.expand_shape %arg173 [[0, 1], [2], [3]] output_shape [1, %dim_265, 1, 12] : tensor<?x1x12xf32> into tensor<1x?x1x12xf32>
    %dim_267 = tensor.dim %arg174, %c0 : tensor<?x1x12xf32>
    %expanded_268 = tensor.expand_shape %arg174 [[0, 1], [2], [3]] output_shape [1, %dim_267, 1, 12] : tensor<?x1x12xf32> into tensor<1x?x1x12xf32>
    %980 = stablehlo.concatenate %expanded_266, %expanded_268, dim = 0 : (tensor<1x?x1x12xf32>, tensor<1x?x1x12xf32>) -> tensor<2x?x1x12xf32>
    %981 = shape.shape_of %980 : tensor<2x?x1x12xf32> -> tensor<4xindex>
    %982 = shape.shape_of %979 : tensor<2x?x60x12xf32> -> tensor<4xindex>
    %head_269, %tail_270 = "shape.split_at"(%981, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_271, %tail_272 = "shape.split_at"(%982, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %983 = shape.broadcast %head_269, %head_271 : !shape.shape, !shape.shape -> !shape.shape
    %984 = shape.concat %983, %tail_270 : !shape.shape, !shape.shape -> !shape.shape
    %985 = shape.to_extent_tensor %984 : !shape.shape -> tensor<4xindex>
    %986 = stablehlo.dynamic_broadcast_in_dim %980, %985, dims = [0, 1, 2, 3] : (tensor<2x?x1x12xf32>, tensor<4xindex>) -> tensor<2x?x1x12xf32>
    %987 = shape.concat %983, %tail_272 : !shape.shape, !shape.shape -> !shape.shape
    %988 = shape.to_extent_tensor %987 : !shape.shape -> tensor<4xindex>
    %989 = stablehlo.dynamic_broadcast_in_dim %979, %988, dims = [0, 1, 2, 3] : (tensor<2x?x60x12xf32>, tensor<4xindex>) -> tensor<2x?x60x12xf32>
    %990 = stablehlo.dot_general %986, %989, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x12xf32>, tensor<2x?x60x12xf32>) -> tensor<2x?x1x60xf32>
    %991 = shape.shape_of %990 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %992 = stablehlo.dynamic_broadcast_in_dim %cst_3, %991, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %993 = stablehlo.multiply %990, %992 : tensor<2x?x1x60xf32>
    %994 = shape.shape_of %993 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %995 = shape.broadcast %814, %994 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %996 = stablehlo.dynamic_broadcast_in_dim %76, %995, dims = [1, 2, 3] : (tensor<?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %997 = stablehlo.dynamic_broadcast_in_dim %993, %995, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %998 = stablehlo.add %996, %997 : tensor<2x?x1x60xf32>
    %999 = stablehlo.reduce(%998 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_273 = tensor.dim %999, %c1 : tensor<2x?x1xf32>
    %from_elements_274 = tensor.from_elements %c2, %dim_273, %c1, %c1 : tensor<4xindex>
    %dim_275 = tensor.dim %999, %c1 : tensor<2x?x1xf32>
    %expanded_276 = tensor.expand_shape %999 [[0], [1], [2, 3]] output_shape [2, %dim_275, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1000 = shape.shape_of %998 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1001 = shape.broadcast %1000, %from_elements_274 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1002 = stablehlo.dynamic_broadcast_in_dim %998, %1001, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1003 = stablehlo.dynamic_broadcast_in_dim %expanded_276, %1001, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1004 = stablehlo.subtract %1002, %1003 : tensor<2x?x1x60xf32>
    %1005 = stablehlo.exponential %1004 : tensor<2x?x1x60xf32>
    %1006 = stablehlo.reduce(%1005 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_277 = tensor.dim %1006, %c1 : tensor<2x?x1xf32>
    %from_elements_278 = tensor.from_elements %c2, %dim_277, %c1, %c1 : tensor<4xindex>
    %dim_279 = tensor.dim %1006, %c1 : tensor<2x?x1xf32>
    %expanded_280 = tensor.expand_shape %1006 [[0], [1], [2, 3]] output_shape [2, %dim_279, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1007 = shape.shape_of %1005 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1008 = shape.broadcast %1007, %from_elements_278 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1009 = stablehlo.dynamic_broadcast_in_dim %1005, %1008, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1010 = stablehlo.dynamic_broadcast_in_dim %expanded_280, %1008, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1011 = stablehlo.divide %1009, %1010 : tensor<2x?x1x60xf32>
    %dim_281 = tensor.dim %arg175, %c0 : tensor<?x60x12xf32>
    %expanded_282 = tensor.expand_shape %arg175 [[0, 1], [2], [3]] output_shape [1, %dim_281, 60, 12] : tensor<?x60x12xf32> into tensor<1x?x60x12xf32>
    %dim_283 = tensor.dim %arg176, %c0 : tensor<?x60x12xf32>
    %expanded_284 = tensor.expand_shape %arg176 [[0, 1], [2], [3]] output_shape [1, %dim_283, 60, 12] : tensor<?x60x12xf32> into tensor<1x?x60x12xf32>
    %1012 = stablehlo.concatenate %expanded_282, %expanded_284, dim = 0 : (tensor<1x?x60x12xf32>, tensor<1x?x60x12xf32>) -> tensor<2x?x60x12xf32>
    %1013 = shape.shape_of %1011 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1014 = shape.shape_of %1012 : tensor<2x?x60x12xf32> -> tensor<4xindex>
    %head_285, %tail_286 = "shape.split_at"(%1013, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_287, %tail_288 = "shape.split_at"(%1014, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1015 = shape.broadcast %head_285, %head_287 : !shape.shape, !shape.shape -> !shape.shape
    %1016 = shape.concat %1015, %tail_286 : !shape.shape, !shape.shape -> !shape.shape
    %1017 = shape.to_extent_tensor %1016 : !shape.shape -> tensor<4xindex>
    %1018 = stablehlo.dynamic_broadcast_in_dim %1011, %1017, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1019 = shape.concat %1015, %tail_288 : !shape.shape, !shape.shape -> !shape.shape
    %1020 = shape.to_extent_tensor %1019 : !shape.shape -> tensor<4xindex>
    %1021 = stablehlo.dynamic_broadcast_in_dim %1012, %1020, dims = [0, 1, 2, 3] : (tensor<2x?x60x12xf32>, tensor<4xindex>) -> tensor<2x?x60x12xf32>
    %1022 = stablehlo.dot_general %1018, %1021, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x60xf32>, tensor<2x?x60x12xf32>) -> tensor<2x?x1x12xf32>
    %1023 = stablehlo.transpose %1022, dims = [1, 2, 0, 3] : (tensor<2x?x1x12xf32>) -> tensor<?x1x2x12xf32>
    %collapsed_289 = tensor.collapse_shape %1023 [[0], [1, 2, 3]] : tensor<?x1x2x12xf32> into tensor<?x24xf32>
    %dim_290 = tensor.dim %arg177, %c0 : tensor<?x60x6xf32>
    %expanded_291 = tensor.expand_shape %arg177 [[0, 1], [2], [3]] output_shape [1, %dim_290, 60, 6] : tensor<?x60x6xf32> into tensor<1x?x60x6xf32>
    %dim_292 = tensor.dim %arg178, %c0 : tensor<?x60x6xf32>
    %expanded_293 = tensor.expand_shape %arg178 [[0, 1], [2], [3]] output_shape [1, %dim_292, 60, 6] : tensor<?x60x6xf32> into tensor<1x?x60x6xf32>
    %1024 = stablehlo.concatenate %expanded_291, %expanded_293, dim = 0 : (tensor<1x?x60x6xf32>, tensor<1x?x60x6xf32>) -> tensor<2x?x60x6xf32>
    %dim_294 = tensor.dim %arg179, %c0 : tensor<?x1x6xf32>
    %expanded_295 = tensor.expand_shape %arg179 [[0, 1], [2], [3]] output_shape [1, %dim_294, 1, 6] : tensor<?x1x6xf32> into tensor<1x?x1x6xf32>
    %dim_296 = tensor.dim %arg180, %c0 : tensor<?x1x6xf32>
    %expanded_297 = tensor.expand_shape %arg180 [[0, 1], [2], [3]] output_shape [1, %dim_296, 1, 6] : tensor<?x1x6xf32> into tensor<1x?x1x6xf32>
    %1025 = stablehlo.concatenate %expanded_295, %expanded_297, dim = 0 : (tensor<1x?x1x6xf32>, tensor<1x?x1x6xf32>) -> tensor<2x?x1x6xf32>
    %1026 = shape.shape_of %1025 : tensor<2x?x1x6xf32> -> tensor<4xindex>
    %1027 = shape.shape_of %1024 : tensor<2x?x60x6xf32> -> tensor<4xindex>
    %head_298, %tail_299 = "shape.split_at"(%1026, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_300, %tail_301 = "shape.split_at"(%1027, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1028 = shape.broadcast %head_298, %head_300 : !shape.shape, !shape.shape -> !shape.shape
    %1029 = shape.concat %1028, %tail_299 : !shape.shape, !shape.shape -> !shape.shape
    %1030 = shape.to_extent_tensor %1029 : !shape.shape -> tensor<4xindex>
    %1031 = stablehlo.dynamic_broadcast_in_dim %1025, %1030, dims = [0, 1, 2, 3] : (tensor<2x?x1x6xf32>, tensor<4xindex>) -> tensor<2x?x1x6xf32>
    %1032 = shape.concat %1028, %tail_301 : !shape.shape, !shape.shape -> !shape.shape
    %1033 = shape.to_extent_tensor %1032 : !shape.shape -> tensor<4xindex>
    %1034 = stablehlo.dynamic_broadcast_in_dim %1024, %1033, dims = [0, 1, 2, 3] : (tensor<2x?x60x6xf32>, tensor<4xindex>) -> tensor<2x?x60x6xf32>
    %1035 = stablehlo.dot_general %1031, %1034, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x6xf32>, tensor<2x?x60x6xf32>) -> tensor<2x?x1x60xf32>
    %1036 = shape.shape_of %1035 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1037 = stablehlo.dynamic_broadcast_in_dim %cst_1, %1036, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1038 = stablehlo.multiply %1035, %1037 : tensor<2x?x1x60xf32>
    %1039 = shape.shape_of %1038 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1040 = shape.broadcast %814, %1039 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1041 = stablehlo.dynamic_broadcast_in_dim %76, %1040, dims = [1, 2, 3] : (tensor<?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1042 = stablehlo.dynamic_broadcast_in_dim %1038, %1040, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1043 = stablehlo.add %1041, %1042 : tensor<2x?x1x60xf32>
    %1044 = stablehlo.reduce(%1043 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_302 = tensor.dim %1044, %c1 : tensor<2x?x1xf32>
    %from_elements_303 = tensor.from_elements %c2, %dim_302, %c1, %c1 : tensor<4xindex>
    %dim_304 = tensor.dim %1044, %c1 : tensor<2x?x1xf32>
    %expanded_305 = tensor.expand_shape %1044 [[0], [1], [2, 3]] output_shape [2, %dim_304, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1045 = shape.shape_of %1043 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1046 = shape.broadcast %1045, %from_elements_303 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1047 = stablehlo.dynamic_broadcast_in_dim %1043, %1046, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1048 = stablehlo.dynamic_broadcast_in_dim %expanded_305, %1046, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1049 = stablehlo.subtract %1047, %1048 : tensor<2x?x1x60xf32>
    %1050 = stablehlo.exponential %1049 : tensor<2x?x1x60xf32>
    %1051 = stablehlo.reduce(%1050 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x60xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_306 = tensor.dim %1051, %c1 : tensor<2x?x1xf32>
    %from_elements_307 = tensor.from_elements %c2, %dim_306, %c1, %c1 : tensor<4xindex>
    %dim_308 = tensor.dim %1051, %c1 : tensor<2x?x1xf32>
    %expanded_309 = tensor.expand_shape %1051 [[0], [1], [2, 3]] output_shape [2, %dim_308, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1052 = shape.shape_of %1050 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1053 = shape.broadcast %1052, %from_elements_307 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1054 = stablehlo.dynamic_broadcast_in_dim %1050, %1053, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1055 = stablehlo.dynamic_broadcast_in_dim %expanded_309, %1053, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1056 = stablehlo.divide %1054, %1055 : tensor<2x?x1x60xf32>
    %dim_310 = tensor.dim %arg181, %c0 : tensor<?x60x6xf32>
    %expanded_311 = tensor.expand_shape %arg181 [[0, 1], [2], [3]] output_shape [1, %dim_310, 60, 6] : tensor<?x60x6xf32> into tensor<1x?x60x6xf32>
    %dim_312 = tensor.dim %arg182, %c0 : tensor<?x60x6xf32>
    %expanded_313 = tensor.expand_shape %arg182 [[0, 1], [2], [3]] output_shape [1, %dim_312, 60, 6] : tensor<?x60x6xf32> into tensor<1x?x60x6xf32>
    %1057 = stablehlo.concatenate %expanded_311, %expanded_313, dim = 0 : (tensor<1x?x60x6xf32>, tensor<1x?x60x6xf32>) -> tensor<2x?x60x6xf32>
    %1058 = shape.shape_of %1056 : tensor<2x?x1x60xf32> -> tensor<4xindex>
    %1059 = shape.shape_of %1057 : tensor<2x?x60x6xf32> -> tensor<4xindex>
    %head_314, %tail_315 = "shape.split_at"(%1058, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_316, %tail_317 = "shape.split_at"(%1059, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1060 = shape.broadcast %head_314, %head_316 : !shape.shape, !shape.shape -> !shape.shape
    %1061 = shape.concat %1060, %tail_315 : !shape.shape, !shape.shape -> !shape.shape
    %1062 = shape.to_extent_tensor %1061 : !shape.shape -> tensor<4xindex>
    %1063 = stablehlo.dynamic_broadcast_in_dim %1056, %1062, dims = [0, 1, 2, 3] : (tensor<2x?x1x60xf32>, tensor<4xindex>) -> tensor<2x?x1x60xf32>
    %1064 = shape.concat %1060, %tail_317 : !shape.shape, !shape.shape -> !shape.shape
    %1065 = shape.to_extent_tensor %1064 : !shape.shape -> tensor<4xindex>
    %1066 = stablehlo.dynamic_broadcast_in_dim %1057, %1065, dims = [0, 1, 2, 3] : (tensor<2x?x60x6xf32>, tensor<4xindex>) -> tensor<2x?x60x6xf32>
    %1067 = stablehlo.dot_general %1063, %1066, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x60xf32>, tensor<2x?x60x6xf32>) -> tensor<2x?x1x6xf32>
    %1068 = stablehlo.transpose %1067, dims = [1, 2, 0, 3] : (tensor<2x?x1x6xf32>) -> tensor<?x1x2x6xf32>
    %collapsed_318 = tensor.collapse_shape %1068 [[0], [1, 2, 3]] : tensor<?x1x2x6xf32> into tensor<?x12xf32>
    %1069 = stablehlo.concatenate %arg183, %arg184, dim = 2 : (tensor<?x1x512xf32>, tensor<?x1x512xf32>) -> tensor<?x1x1024xf32>
    %collapsed_319 = tensor.collapse_shape %1069 [[0], [1, 2]] : tensor<?x1x1024xf32> into tensor<?x1024xf32>
    %dim_320 = tensor.dim %arg185, %c0 : tensor<?x64x24xf32>
    %expanded_321 = tensor.expand_shape %arg185 [[0, 1], [2], [3]] output_shape [1, %dim_320, 64, 24] : tensor<?x64x24xf32> into tensor<1x?x64x24xf32>
    %dim_322 = tensor.dim %arg186, %c0 : tensor<?x64x24xf32>
    %expanded_323 = tensor.expand_shape %arg186 [[0, 1], [2], [3]] output_shape [1, %dim_322, 64, 24] : tensor<?x64x24xf32> into tensor<1x?x64x24xf32>
    %1070 = stablehlo.concatenate %expanded_321, %expanded_323, dim = 0 : (tensor<1x?x64x24xf32>, tensor<1x?x64x24xf32>) -> tensor<2x?x64x24xf32>
    %dim_324 = tensor.dim %arg187, %c0 : tensor<?x1x24xf32>
    %expanded_325 = tensor.expand_shape %arg187 [[0, 1], [2], [3]] output_shape [1, %dim_324, 1, 24] : tensor<?x1x24xf32> into tensor<1x?x1x24xf32>
    %dim_326 = tensor.dim %arg188, %c0 : tensor<?x1x24xf32>
    %expanded_327 = tensor.expand_shape %arg188 [[0, 1], [2], [3]] output_shape [1, %dim_326, 1, 24] : tensor<?x1x24xf32> into tensor<1x?x1x24xf32>
    %1071 = stablehlo.concatenate %expanded_325, %expanded_327, dim = 0 : (tensor<1x?x1x24xf32>, tensor<1x?x1x24xf32>) -> tensor<2x?x1x24xf32>
    %1072 = shape.shape_of %1071 : tensor<2x?x1x24xf32> -> tensor<4xindex>
    %1073 = shape.shape_of %1070 : tensor<2x?x64x24xf32> -> tensor<4xindex>
    %head_328, %tail_329 = "shape.split_at"(%1072, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_330, %tail_331 = "shape.split_at"(%1073, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1074 = shape.broadcast %head_328, %head_330 : !shape.shape, !shape.shape -> !shape.shape
    %1075 = shape.concat %1074, %tail_329 : !shape.shape, !shape.shape -> !shape.shape
    %1076 = shape.to_extent_tensor %1075 : !shape.shape -> tensor<4xindex>
    %1077 = stablehlo.dynamic_broadcast_in_dim %1071, %1076, dims = [0, 1, 2, 3] : (tensor<2x?x1x24xf32>, tensor<4xindex>) -> tensor<2x?x1x24xf32>
    %1078 = shape.concat %1074, %tail_331 : !shape.shape, !shape.shape -> !shape.shape
    %1079 = shape.to_extent_tensor %1078 : !shape.shape -> tensor<4xindex>
    %1080 = stablehlo.dynamic_broadcast_in_dim %1070, %1079, dims = [0, 1, 2, 3] : (tensor<2x?x64x24xf32>, tensor<4xindex>) -> tensor<2x?x64x24xf32>
    %1081 = stablehlo.dot_general %1077, %1080, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x24xf32>, tensor<2x?x64x24xf32>) -> tensor<2x?x1x64xf32>
    %1082 = shape.shape_of %1081 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1083 = stablehlo.dynamic_broadcast_in_dim %cst_5, %1082, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1084 = stablehlo.multiply %1081, %1083 : tensor<2x?x1x64xf32>
    %1085 = shape.shape_of %79 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1086 = shape.shape_of %1084 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1087 = shape.broadcast %1085, %1086 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1088 = stablehlo.dynamic_broadcast_in_dim %79, %1087, dims = [1, 2, 3] : (tensor<?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1089 = stablehlo.dynamic_broadcast_in_dim %1084, %1087, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1090 = stablehlo.add %1088, %1089 : tensor<2x?x1x64xf32>
    %1091 = stablehlo.reduce(%1090 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_332 = tensor.dim %1091, %c1 : tensor<2x?x1xf32>
    %from_elements_333 = tensor.from_elements %c2, %dim_332, %c1, %c1 : tensor<4xindex>
    %dim_334 = tensor.dim %1091, %c1 : tensor<2x?x1xf32>
    %expanded_335 = tensor.expand_shape %1091 [[0], [1], [2, 3]] output_shape [2, %dim_334, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1092 = shape.shape_of %1090 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1093 = shape.broadcast %1092, %from_elements_333 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1094 = stablehlo.dynamic_broadcast_in_dim %1090, %1093, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1095 = stablehlo.dynamic_broadcast_in_dim %expanded_335, %1093, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1096 = stablehlo.subtract %1094, %1095 : tensor<2x?x1x64xf32>
    %1097 = stablehlo.exponential %1096 : tensor<2x?x1x64xf32>
    %1098 = stablehlo.reduce(%1097 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_336 = tensor.dim %1098, %c1 : tensor<2x?x1xf32>
    %from_elements_337 = tensor.from_elements %c2, %dim_336, %c1, %c1 : tensor<4xindex>
    %dim_338 = tensor.dim %1098, %c1 : tensor<2x?x1xf32>
    %expanded_339 = tensor.expand_shape %1098 [[0], [1], [2, 3]] output_shape [2, %dim_338, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1099 = shape.shape_of %1097 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1100 = shape.broadcast %1099, %from_elements_337 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1101 = stablehlo.dynamic_broadcast_in_dim %1097, %1100, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1102 = stablehlo.dynamic_broadcast_in_dim %expanded_339, %1100, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1103 = stablehlo.divide %1101, %1102 : tensor<2x?x1x64xf32>
    %dim_340 = tensor.dim %arg189, %c0 : tensor<?x64x24xf32>
    %expanded_341 = tensor.expand_shape %arg189 [[0, 1], [2], [3]] output_shape [1, %dim_340, 64, 24] : tensor<?x64x24xf32> into tensor<1x?x64x24xf32>
    %dim_342 = tensor.dim %arg190, %c0 : tensor<?x64x24xf32>
    %expanded_343 = tensor.expand_shape %arg190 [[0, 1], [2], [3]] output_shape [1, %dim_342, 64, 24] : tensor<?x64x24xf32> into tensor<1x?x64x24xf32>
    %1104 = stablehlo.concatenate %expanded_341, %expanded_343, dim = 0 : (tensor<1x?x64x24xf32>, tensor<1x?x64x24xf32>) -> tensor<2x?x64x24xf32>
    %1105 = shape.shape_of %1103 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1106 = shape.shape_of %1104 : tensor<2x?x64x24xf32> -> tensor<4xindex>
    %head_344, %tail_345 = "shape.split_at"(%1105, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_346, %tail_347 = "shape.split_at"(%1106, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1107 = shape.broadcast %head_344, %head_346 : !shape.shape, !shape.shape -> !shape.shape
    %1108 = shape.concat %1107, %tail_345 : !shape.shape, !shape.shape -> !shape.shape
    %1109 = shape.to_extent_tensor %1108 : !shape.shape -> tensor<4xindex>
    %1110 = stablehlo.dynamic_broadcast_in_dim %1103, %1109, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1111 = shape.concat %1107, %tail_347 : !shape.shape, !shape.shape -> !shape.shape
    %1112 = shape.to_extent_tensor %1111 : !shape.shape -> tensor<4xindex>
    %1113 = stablehlo.dynamic_broadcast_in_dim %1104, %1112, dims = [0, 1, 2, 3] : (tensor<2x?x64x24xf32>, tensor<4xindex>) -> tensor<2x?x64x24xf32>
    %1114 = stablehlo.dot_general %1110, %1113, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x64xf32>, tensor<2x?x64x24xf32>) -> tensor<2x?x1x24xf32>
    %1115 = stablehlo.transpose %1114, dims = [1, 2, 0, 3] : (tensor<2x?x1x24xf32>) -> tensor<?x1x2x24xf32>
    %collapsed_348 = tensor.collapse_shape %1115 [[0], [1, 2, 3]] : tensor<?x1x2x24xf32> into tensor<?x48xf32>
    %dim_349 = tensor.dim %arg191, %c0 : tensor<?x64x12xf32>
    %expanded_350 = tensor.expand_shape %arg191 [[0, 1], [2], [3]] output_shape [1, %dim_349, 64, 12] : tensor<?x64x12xf32> into tensor<1x?x64x12xf32>
    %dim_351 = tensor.dim %arg192, %c0 : tensor<?x64x12xf32>
    %expanded_352 = tensor.expand_shape %arg192 [[0, 1], [2], [3]] output_shape [1, %dim_351, 64, 12] : tensor<?x64x12xf32> into tensor<1x?x64x12xf32>
    %1116 = stablehlo.concatenate %expanded_350, %expanded_352, dim = 0 : (tensor<1x?x64x12xf32>, tensor<1x?x64x12xf32>) -> tensor<2x?x64x12xf32>
    %dim_353 = tensor.dim %arg193, %c0 : tensor<?x1x12xf32>
    %expanded_354 = tensor.expand_shape %arg193 [[0, 1], [2], [3]] output_shape [1, %dim_353, 1, 12] : tensor<?x1x12xf32> into tensor<1x?x1x12xf32>
    %dim_355 = tensor.dim %arg194, %c0 : tensor<?x1x12xf32>
    %expanded_356 = tensor.expand_shape %arg194 [[0, 1], [2], [3]] output_shape [1, %dim_355, 1, 12] : tensor<?x1x12xf32> into tensor<1x?x1x12xf32>
    %1117 = stablehlo.concatenate %expanded_354, %expanded_356, dim = 0 : (tensor<1x?x1x12xf32>, tensor<1x?x1x12xf32>) -> tensor<2x?x1x12xf32>
    %1118 = shape.shape_of %1117 : tensor<2x?x1x12xf32> -> tensor<4xindex>
    %1119 = shape.shape_of %1116 : tensor<2x?x64x12xf32> -> tensor<4xindex>
    %head_357, %tail_358 = "shape.split_at"(%1118, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_359, %tail_360 = "shape.split_at"(%1119, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1120 = shape.broadcast %head_357, %head_359 : !shape.shape, !shape.shape -> !shape.shape
    %1121 = shape.concat %1120, %tail_358 : !shape.shape, !shape.shape -> !shape.shape
    %1122 = shape.to_extent_tensor %1121 : !shape.shape -> tensor<4xindex>
    %1123 = stablehlo.dynamic_broadcast_in_dim %1117, %1122, dims = [0, 1, 2, 3] : (tensor<2x?x1x12xf32>, tensor<4xindex>) -> tensor<2x?x1x12xf32>
    %1124 = shape.concat %1120, %tail_360 : !shape.shape, !shape.shape -> !shape.shape
    %1125 = shape.to_extent_tensor %1124 : !shape.shape -> tensor<4xindex>
    %1126 = stablehlo.dynamic_broadcast_in_dim %1116, %1125, dims = [0, 1, 2, 3] : (tensor<2x?x64x12xf32>, tensor<4xindex>) -> tensor<2x?x64x12xf32>
    %1127 = stablehlo.dot_general %1123, %1126, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x12xf32>, tensor<2x?x64x12xf32>) -> tensor<2x?x1x64xf32>
    %1128 = shape.shape_of %1127 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1129 = stablehlo.dynamic_broadcast_in_dim %cst_3, %1128, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1130 = stablehlo.multiply %1127, %1129 : tensor<2x?x1x64xf32>
    %1131 = shape.shape_of %1130 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1132 = shape.broadcast %1085, %1131 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1133 = stablehlo.dynamic_broadcast_in_dim %79, %1132, dims = [1, 2, 3] : (tensor<?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1134 = stablehlo.dynamic_broadcast_in_dim %1130, %1132, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1135 = stablehlo.add %1133, %1134 : tensor<2x?x1x64xf32>
    %1136 = stablehlo.reduce(%1135 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_361 = tensor.dim %1136, %c1 : tensor<2x?x1xf32>
    %from_elements_362 = tensor.from_elements %c2, %dim_361, %c1, %c1 : tensor<4xindex>
    %dim_363 = tensor.dim %1136, %c1 : tensor<2x?x1xf32>
    %expanded_364 = tensor.expand_shape %1136 [[0], [1], [2, 3]] output_shape [2, %dim_363, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1137 = shape.shape_of %1135 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1138 = shape.broadcast %1137, %from_elements_362 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1139 = stablehlo.dynamic_broadcast_in_dim %1135, %1138, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1140 = stablehlo.dynamic_broadcast_in_dim %expanded_364, %1138, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1141 = stablehlo.subtract %1139, %1140 : tensor<2x?x1x64xf32>
    %1142 = stablehlo.exponential %1141 : tensor<2x?x1x64xf32>
    %1143 = stablehlo.reduce(%1142 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_365 = tensor.dim %1143, %c1 : tensor<2x?x1xf32>
    %from_elements_366 = tensor.from_elements %c2, %dim_365, %c1, %c1 : tensor<4xindex>
    %dim_367 = tensor.dim %1143, %c1 : tensor<2x?x1xf32>
    %expanded_368 = tensor.expand_shape %1143 [[0], [1], [2, 3]] output_shape [2, %dim_367, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1144 = shape.shape_of %1142 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1145 = shape.broadcast %1144, %from_elements_366 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1146 = stablehlo.dynamic_broadcast_in_dim %1142, %1145, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1147 = stablehlo.dynamic_broadcast_in_dim %expanded_368, %1145, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1148 = stablehlo.divide %1146, %1147 : tensor<2x?x1x64xf32>
    %dim_369 = tensor.dim %arg195, %c0 : tensor<?x64x12xf32>
    %expanded_370 = tensor.expand_shape %arg195 [[0, 1], [2], [3]] output_shape [1, %dim_369, 64, 12] : tensor<?x64x12xf32> into tensor<1x?x64x12xf32>
    %dim_371 = tensor.dim %arg196, %c0 : tensor<?x64x12xf32>
    %expanded_372 = tensor.expand_shape %arg196 [[0, 1], [2], [3]] output_shape [1, %dim_371, 64, 12] : tensor<?x64x12xf32> into tensor<1x?x64x12xf32>
    %1149 = stablehlo.concatenate %expanded_370, %expanded_372, dim = 0 : (tensor<1x?x64x12xf32>, tensor<1x?x64x12xf32>) -> tensor<2x?x64x12xf32>
    %1150 = shape.shape_of %1148 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1151 = shape.shape_of %1149 : tensor<2x?x64x12xf32> -> tensor<4xindex>
    %head_373, %tail_374 = "shape.split_at"(%1150, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_375, %tail_376 = "shape.split_at"(%1151, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1152 = shape.broadcast %head_373, %head_375 : !shape.shape, !shape.shape -> !shape.shape
    %1153 = shape.concat %1152, %tail_374 : !shape.shape, !shape.shape -> !shape.shape
    %1154 = shape.to_extent_tensor %1153 : !shape.shape -> tensor<4xindex>
    %1155 = stablehlo.dynamic_broadcast_in_dim %1148, %1154, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1156 = shape.concat %1152, %tail_376 : !shape.shape, !shape.shape -> !shape.shape
    %1157 = shape.to_extent_tensor %1156 : !shape.shape -> tensor<4xindex>
    %1158 = stablehlo.dynamic_broadcast_in_dim %1149, %1157, dims = [0, 1, 2, 3] : (tensor<2x?x64x12xf32>, tensor<4xindex>) -> tensor<2x?x64x12xf32>
    %1159 = stablehlo.dot_general %1155, %1158, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x64xf32>, tensor<2x?x64x12xf32>) -> tensor<2x?x1x12xf32>
    %1160 = stablehlo.transpose %1159, dims = [1, 2, 0, 3] : (tensor<2x?x1x12xf32>) -> tensor<?x1x2x12xf32>
    %collapsed_377 = tensor.collapse_shape %1160 [[0], [1, 2, 3]] : tensor<?x1x2x12xf32> into tensor<?x24xf32>
    %dim_378 = tensor.dim %arg197, %c0 : tensor<?x64x6xf32>
    %expanded_379 = tensor.expand_shape %arg197 [[0, 1], [2], [3]] output_shape [1, %dim_378, 64, 6] : tensor<?x64x6xf32> into tensor<1x?x64x6xf32>
    %dim_380 = tensor.dim %arg198, %c0 : tensor<?x64x6xf32>
    %expanded_381 = tensor.expand_shape %arg198 [[0, 1], [2], [3]] output_shape [1, %dim_380, 64, 6] : tensor<?x64x6xf32> into tensor<1x?x64x6xf32>
    %1161 = stablehlo.concatenate %expanded_379, %expanded_381, dim = 0 : (tensor<1x?x64x6xf32>, tensor<1x?x64x6xf32>) -> tensor<2x?x64x6xf32>
    %dim_382 = tensor.dim %arg199, %c0 : tensor<?x1x6xf32>
    %expanded_383 = tensor.expand_shape %arg199 [[0, 1], [2], [3]] output_shape [1, %dim_382, 1, 6] : tensor<?x1x6xf32> into tensor<1x?x1x6xf32>
    %dim_384 = tensor.dim %arg200, %c0 : tensor<?x1x6xf32>
    %expanded_385 = tensor.expand_shape %arg200 [[0, 1], [2], [3]] output_shape [1, %dim_384, 1, 6] : tensor<?x1x6xf32> into tensor<1x?x1x6xf32>
    %1162 = stablehlo.concatenate %expanded_383, %expanded_385, dim = 0 : (tensor<1x?x1x6xf32>, tensor<1x?x1x6xf32>) -> tensor<2x?x1x6xf32>
    %1163 = shape.shape_of %1162 : tensor<2x?x1x6xf32> -> tensor<4xindex>
    %1164 = shape.shape_of %1161 : tensor<2x?x64x6xf32> -> tensor<4xindex>
    %head_386, %tail_387 = "shape.split_at"(%1163, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_388, %tail_389 = "shape.split_at"(%1164, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1165 = shape.broadcast %head_386, %head_388 : !shape.shape, !shape.shape -> !shape.shape
    %1166 = shape.concat %1165, %tail_387 : !shape.shape, !shape.shape -> !shape.shape
    %1167 = shape.to_extent_tensor %1166 : !shape.shape -> tensor<4xindex>
    %1168 = stablehlo.dynamic_broadcast_in_dim %1162, %1167, dims = [0, 1, 2, 3] : (tensor<2x?x1x6xf32>, tensor<4xindex>) -> tensor<2x?x1x6xf32>
    %1169 = shape.concat %1165, %tail_389 : !shape.shape, !shape.shape -> !shape.shape
    %1170 = shape.to_extent_tensor %1169 : !shape.shape -> tensor<4xindex>
    %1171 = stablehlo.dynamic_broadcast_in_dim %1161, %1170, dims = [0, 1, 2, 3] : (tensor<2x?x64x6xf32>, tensor<4xindex>) -> tensor<2x?x64x6xf32>
    %1172 = stablehlo.dot_general %1168, %1171, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x6xf32>, tensor<2x?x64x6xf32>) -> tensor<2x?x1x64xf32>
    %1173 = shape.shape_of %1172 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1174 = stablehlo.dynamic_broadcast_in_dim %cst_1, %1173, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1175 = stablehlo.multiply %1172, %1174 : tensor<2x?x1x64xf32>
    %1176 = shape.shape_of %1175 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1177 = shape.broadcast %1085, %1176 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1178 = stablehlo.dynamic_broadcast_in_dim %79, %1177, dims = [1, 2, 3] : (tensor<?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1179 = stablehlo.dynamic_broadcast_in_dim %1175, %1177, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1180 = stablehlo.add %1178, %1179 : tensor<2x?x1x64xf32>
    %1181 = stablehlo.reduce(%1180 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_390 = tensor.dim %1181, %c1 : tensor<2x?x1xf32>
    %from_elements_391 = tensor.from_elements %c2, %dim_390, %c1, %c1 : tensor<4xindex>
    %dim_392 = tensor.dim %1181, %c1 : tensor<2x?x1xf32>
    %expanded_393 = tensor.expand_shape %1181 [[0], [1], [2, 3]] output_shape [2, %dim_392, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1182 = shape.shape_of %1180 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1183 = shape.broadcast %1182, %from_elements_391 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1184 = stablehlo.dynamic_broadcast_in_dim %1180, %1183, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1185 = stablehlo.dynamic_broadcast_in_dim %expanded_393, %1183, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1186 = stablehlo.subtract %1184, %1185 : tensor<2x?x1x64xf32>
    %1187 = stablehlo.exponential %1186 : tensor<2x?x1x64xf32>
    %1188 = stablehlo.reduce(%1187 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_394 = tensor.dim %1188, %c1 : tensor<2x?x1xf32>
    %from_elements_395 = tensor.from_elements %c2, %dim_394, %c1, %c1 : tensor<4xindex>
    %dim_396 = tensor.dim %1188, %c1 : tensor<2x?x1xf32>
    %expanded_397 = tensor.expand_shape %1188 [[0], [1], [2, 3]] output_shape [2, %dim_396, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1189 = shape.shape_of %1187 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1190 = shape.broadcast %1189, %from_elements_395 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1191 = stablehlo.dynamic_broadcast_in_dim %1187, %1190, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1192 = stablehlo.dynamic_broadcast_in_dim %expanded_397, %1190, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1193 = stablehlo.divide %1191, %1192 : tensor<2x?x1x64xf32>
    %dim_398 = tensor.dim %arg201, %c0 : tensor<?x64x6xf32>
    %expanded_399 = tensor.expand_shape %arg201 [[0, 1], [2], [3]] output_shape [1, %dim_398, 64, 6] : tensor<?x64x6xf32> into tensor<1x?x64x6xf32>
    %dim_400 = tensor.dim %arg202, %c0 : tensor<?x64x6xf32>
    %expanded_401 = tensor.expand_shape %arg202 [[0, 1], [2], [3]] output_shape [1, %dim_400, 64, 6] : tensor<?x64x6xf32> into tensor<1x?x64x6xf32>
    %1194 = stablehlo.concatenate %expanded_399, %expanded_401, dim = 0 : (tensor<1x?x64x6xf32>, tensor<1x?x64x6xf32>) -> tensor<2x?x64x6xf32>
    %1195 = shape.shape_of %1193 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1196 = shape.shape_of %1194 : tensor<2x?x64x6xf32> -> tensor<4xindex>
    %head_402, %tail_403 = "shape.split_at"(%1195, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_404, %tail_405 = "shape.split_at"(%1196, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1197 = shape.broadcast %head_402, %head_404 : !shape.shape, !shape.shape -> !shape.shape
    %1198 = shape.concat %1197, %tail_403 : !shape.shape, !shape.shape -> !shape.shape
    %1199 = shape.to_extent_tensor %1198 : !shape.shape -> tensor<4xindex>
    %1200 = stablehlo.dynamic_broadcast_in_dim %1193, %1199, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1201 = shape.concat %1197, %tail_405 : !shape.shape, !shape.shape -> !shape.shape
    %1202 = shape.to_extent_tensor %1201 : !shape.shape -> tensor<4xindex>
    %1203 = stablehlo.dynamic_broadcast_in_dim %1194, %1202, dims = [0, 1, 2, 3] : (tensor<2x?x64x6xf32>, tensor<4xindex>) -> tensor<2x?x64x6xf32>
    %1204 = stablehlo.dot_general %1200, %1203, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x64xf32>, tensor<2x?x64x6xf32>) -> tensor<2x?x1x6xf32>
    %1205 = stablehlo.transpose %1204, dims = [1, 2, 0, 3] : (tensor<2x?x1x6xf32>) -> tensor<?x1x2x6xf32>
    %collapsed_406 = tensor.collapse_shape %1205 [[0], [1, 2, 3]] : tensor<?x1x2x6xf32> into tensor<?x12xf32>
    %1206 = shape.shape_of %arg203 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1207 = shape.shape_of %arg204 : tensor<?x64x64xf32> -> tensor<3xindex>
    %head_407, %tail_408 = "shape.split_at"(%1206, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_409, %tail_410 = "shape.split_at"(%1207, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %1208 = shape.broadcast %head_407, %head_409 : !shape.shape, !shape.shape -> !shape.shape
    %1209 = shape.concat %1208, %tail_408 : !shape.shape, !shape.shape -> !shape.shape
    %1210 = shape.to_extent_tensor %1209 : !shape.shape -> tensor<3xindex>
    %1211 = stablehlo.dynamic_broadcast_in_dim %arg203, %1210, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1212 = shape.concat %1208, %tail_410 : !shape.shape, !shape.shape -> !shape.shape
    %1213 = shape.to_extent_tensor %1212 : !shape.shape -> tensor<3xindex>
    %1214 = stablehlo.dynamic_broadcast_in_dim %arg204, %1213, dims = [0, 1, 2] : (tensor<?x64x64xf32>, tensor<3xindex>) -> tensor<?x64x64xf32>
    %1215 = stablehlo.dot_general %1211, %1214, batching_dims = [0] x [0], contracting_dims = [2] x [2], precision = [DEFAULT, DEFAULT] : (tensor<?x1x64xf32>, tensor<?x64x64xf32>) -> tensor<?x1x64xf32>
    %1216 = shape.shape_of %1215 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1217 = stablehlo.dynamic_broadcast_in_dim %cst_6, %1216, dims = [] : (tensor<f32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1218 = stablehlo.multiply %1215, %1217 : tensor<?x1x64xf32>
    %1219 = shape.shape_of %1218 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1220 = shape.broadcast %1085, %1219 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %1221 = stablehlo.dynamic_broadcast_in_dim %79, %1220, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1222 = stablehlo.dynamic_broadcast_in_dim %1218, %1220, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1223 = stablehlo.add %1221, %1222 : tensor<?x1x64xf32>
    %dim_411 = tensor.dim %1223, %c0 : tensor<?x1x64xf32>
    %expanded_412 = tensor.expand_shape %1223 [[0, 1], [2], [3]] output_shape [1, %dim_411, 1, 64] : tensor<?x1x64xf32> into tensor<1x?x1x64xf32>
    %1224 = stablehlo.transpose %expanded_412, dims = [1, 0, 2, 3] : (tensor<1x?x1x64xf32>) -> tensor<?x1x1x64xf32>
    %collapsed_413 = tensor.collapse_shape %1224 [[0], [1, 2, 3]] : tensor<?x1x1x64xf32> into tensor<?x64xf32>
    %1225 = stablehlo.concatenate %collapsed_413, %collapsed_173, dim = 1 : (tensor<?x64xf32>, tensor<?x50xf32>) -> tensor<?x114xf32>
    %1226 = stablehlo.dot %1225, %arg205, precision = [DEFAULT, DEFAULT] : (tensor<?x114xf32>, tensor<114x128xf32>) -> tensor<?x128xf32>
    %1227 = shape.shape_of %1226 : tensor<?x128xf32> -> tensor<2xindex>
    %1228 = stablehlo.dynamic_broadcast_in_dim %arg206, %1227, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1229 = stablehlo.add %1226, %1228 : tensor<?x128xf32>
    %1230 = stablehlo.logistic %1229 : tensor<?x128xf32>
    %1231 = shape.shape_of %1229 : tensor<?x128xf32> -> tensor<2xindex>
    %1232 = shape.shape_of %1230 : tensor<?x128xf32> -> tensor<2xindex>
    %1233 = shape.broadcast %1231, %1232 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1234 = stablehlo.dynamic_broadcast_in_dim %1229, %1233, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1235 = stablehlo.dynamic_broadcast_in_dim %1230, %1233, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1236 = stablehlo.multiply %1234, %1235 : tensor<?x128xf32>
    %1237 = stablehlo.dot %1236, %arg207, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %1238 = shape.shape_of %1237 : tensor<?x64xf32> -> tensor<2xindex>
    %1239 = stablehlo.dynamic_broadcast_in_dim %arg208, %1238, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1240 = stablehlo.add %1237, %1239 : tensor<?x64xf32>
    %1241 = stablehlo.dot %1240, %arg209, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %1242 = shape.shape_of %1241 : tensor<?x64xf32> -> tensor<2xindex>
    %1243 = stablehlo.dynamic_broadcast_in_dim %arg210, %1242, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1244 = stablehlo.add %1241, %1243 : tensor<?x64xf32>
    %1245 = stablehlo.logistic %1244 : tensor<?x64xf32>
    %1246 = shape.shape_of %1245 : tensor<?x64xf32> -> tensor<2xindex>
    %1247 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1246, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1248 = stablehlo.multiply %1245, %1247 : tensor<?x64xf32>
    %1249 = stablehlo.dot %1240, %arg211, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %1250 = shape.shape_of %1249 : tensor<?x32xf32> -> tensor<2xindex>
    %1251 = stablehlo.dynamic_broadcast_in_dim %arg212, %1250, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1252 = stablehlo.add %1249, %1251 : tensor<?x32xf32>
    %1253 = stablehlo.logistic %1252 : tensor<?x32xf32>
    %1254 = shape.shape_of %1253 : tensor<?x32xf32> -> tensor<2xindex>
    %1255 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1254, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1256 = stablehlo.multiply %1253, %1255 : tensor<?x32xf32>
    %1257 = shape.shape_of %1256 : tensor<?x32xf32> -> tensor<2xindex>
    %1258 = shape.broadcast %760, %1257 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1259 = stablehlo.dynamic_broadcast_in_dim %collapsed_182, %1258, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1260 = stablehlo.dynamic_broadcast_in_dim %1256, %1258, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1261 = stablehlo.multiply %1259, %1260 : tensor<?x32xf32>
    %1262 = stablehlo.concatenate %collapsed_413, %collapsed_143, dim = 1 : (tensor<?x64xf32>, tensor<?x30xf32>) -> tensor<?x94xf32>
    %1263 = stablehlo.dot %1262, %arg213, precision = [DEFAULT, DEFAULT] : (tensor<?x94xf32>, tensor<94x128xf32>) -> tensor<?x128xf32>
    %1264 = shape.shape_of %1263 : tensor<?x128xf32> -> tensor<2xindex>
    %1265 = stablehlo.dynamic_broadcast_in_dim %arg214, %1264, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1266 = stablehlo.add %1263, %1265 : tensor<?x128xf32>
    %1267 = stablehlo.logistic %1266 : tensor<?x128xf32>
    %1268 = shape.shape_of %1266 : tensor<?x128xf32> -> tensor<2xindex>
    %1269 = shape.shape_of %1267 : tensor<?x128xf32> -> tensor<2xindex>
    %1270 = shape.broadcast %1268, %1269 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1271 = stablehlo.dynamic_broadcast_in_dim %1266, %1270, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1272 = stablehlo.dynamic_broadcast_in_dim %1267, %1270, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1273 = stablehlo.multiply %1271, %1272 : tensor<?x128xf32>
    %1274 = stablehlo.dot %1273, %arg215, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %1275 = shape.shape_of %1274 : tensor<?x64xf32> -> tensor<2xindex>
    %1276 = stablehlo.dynamic_broadcast_in_dim %arg216, %1275, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1277 = stablehlo.add %1274, %1276 : tensor<?x64xf32>
    %1278 = stablehlo.dot %1277, %arg217, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %1279 = shape.shape_of %1278 : tensor<?x64xf32> -> tensor<2xindex>
    %1280 = stablehlo.dynamic_broadcast_in_dim %arg218, %1279, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1281 = stablehlo.add %1278, %1280 : tensor<?x64xf32>
    %1282 = stablehlo.logistic %1281 : tensor<?x64xf32>
    %1283 = shape.shape_of %1282 : tensor<?x64xf32> -> tensor<2xindex>
    %1284 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1283, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1285 = stablehlo.multiply %1282, %1284 : tensor<?x64xf32>
    %1286 = stablehlo.dot %1277, %arg219, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %1287 = shape.shape_of %1286 : tensor<?x32xf32> -> tensor<2xindex>
    %1288 = stablehlo.dynamic_broadcast_in_dim %arg220, %1287, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1289 = stablehlo.add %1286, %1288 : tensor<?x32xf32>
    %1290 = stablehlo.logistic %1289 : tensor<?x32xf32>
    %1291 = shape.shape_of %1290 : tensor<?x32xf32> -> tensor<2xindex>
    %1292 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1291, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1293 = stablehlo.multiply %1290, %1292 : tensor<?x32xf32>
    %1294 = shape.shape_of %1293 : tensor<?x32xf32> -> tensor<2xindex>
    %1295 = shape.broadcast %713, %1294 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1296 = stablehlo.dynamic_broadcast_in_dim %collapsed_152, %1295, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1297 = stablehlo.dynamic_broadcast_in_dim %1293, %1295, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1298 = stablehlo.multiply %1296, %1297 : tensor<?x32xf32>
    %1299 = stablehlo.reduce(%1223 init: %cst_23) applies stablehlo.maximum across dimensions = [2] : (tensor<?x1x64xf32>, tensor<f32>) -> tensor<?x1xf32>
    %dim_414 = tensor.dim %1299, %c0 : tensor<?x1xf32>
    %from_elements_415 = tensor.from_elements %dim_414, %c1, %c1 : tensor<3xindex>
    %dim_416 = tensor.dim %1299, %c0 : tensor<?x1xf32>
    %expanded_417 = tensor.expand_shape %1299 [[0], [1, 2]] output_shape [%dim_416, 1, 1] : tensor<?x1xf32> into tensor<?x1x1xf32>
    %1300 = shape.shape_of %1223 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1301 = shape.broadcast %1300, %from_elements_415 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %1302 = stablehlo.dynamic_broadcast_in_dim %1223, %1301, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1303 = stablehlo.dynamic_broadcast_in_dim %expanded_417, %1301, dims = [0, 1, 2] : (tensor<?x1x1xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1304 = stablehlo.subtract %1302, %1303 : tensor<?x1x64xf32>
    %1305 = stablehlo.exponential %1304 : tensor<?x1x64xf32>
    %1306 = stablehlo.reduce(%1305 init: %cst_21) applies stablehlo.add across dimensions = [2] : (tensor<?x1x64xf32>, tensor<f32>) -> tensor<?x1xf32>
    %dim_418 = tensor.dim %1306, %c0 : tensor<?x1xf32>
    %from_elements_419 = tensor.from_elements %dim_418, %c1, %c1 : tensor<3xindex>
    %dim_420 = tensor.dim %1306, %c0 : tensor<?x1xf32>
    %expanded_421 = tensor.expand_shape %1306 [[0], [1, 2]] output_shape [%dim_420, 1, 1] : tensor<?x1xf32> into tensor<?x1x1xf32>
    %1307 = shape.shape_of %1305 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1308 = shape.broadcast %1307, %from_elements_419 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %1309 = stablehlo.dynamic_broadcast_in_dim %1305, %1308, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1310 = stablehlo.dynamic_broadcast_in_dim %expanded_421, %1308, dims = [0, 1, 2] : (tensor<?x1x1xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1311 = stablehlo.divide %1309, %1310 : tensor<?x1x64xf32>
    %1312 = shape.shape_of %1311 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1313 = shape.shape_of %arg221 : tensor<?x64x64xf32> -> tensor<3xindex>
    %head_422, %tail_423 = "shape.split_at"(%1312, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_424, %tail_425 = "shape.split_at"(%1313, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %1314 = shape.broadcast %head_422, %head_424 : !shape.shape, !shape.shape -> !shape.shape
    %1315 = shape.concat %1314, %tail_423 : !shape.shape, !shape.shape -> !shape.shape
    %1316 = shape.to_extent_tensor %1315 : !shape.shape -> tensor<3xindex>
    %1317 = stablehlo.dynamic_broadcast_in_dim %1311, %1316, dims = [0, 1, 2] : (tensor<?x1x64xf32>, tensor<3xindex>) -> tensor<?x1x64xf32>
    %1318 = shape.concat %1314, %tail_425 : !shape.shape, !shape.shape -> !shape.shape
    %1319 = shape.to_extent_tensor %1318 : !shape.shape -> tensor<3xindex>
    %1320 = stablehlo.dynamic_broadcast_in_dim %arg221, %1319, dims = [0, 1, 2] : (tensor<?x64x64xf32>, tensor<3xindex>) -> tensor<?x64x64xf32>
    %1321 = stablehlo.dot_general %1317, %1320, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<?x1x64xf32>, tensor<?x64x64xf32>) -> tensor<?x1x64xf32>
    %1322 = shape.shape_of %1321 : tensor<?x1x64xf32> -> tensor<3xindex>
    %1323 = shape.num_elements %1322 : tensor<3xindex> -> index
    %1324 = shape.index_to_size %1323
    %1325 = shape.div %1324, %c64 : !shape.size, !shape.size -> !shape.size
    %1326 = shape.from_extents %1325, %c64 : !shape.size, !shape.size
    %1327 = shape.to_extent_tensor %1326 : !shape.shape -> tensor<2xindex>
    %collapsed_426 = tensor.collapse_shape %1321 [[0], [1, 2]] : tensor<?x1x64xf32> into tensor<?x64xf32>
    %1328 = shape.shape_of %1248 : tensor<?x64xf32> -> tensor<2xindex>
    %1329 = shape.broadcast %1327, %1328 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1330 = stablehlo.dynamic_broadcast_in_dim %collapsed_426, %1329, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1331 = stablehlo.dynamic_broadcast_in_dim %1248, %1329, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1332 = stablehlo.multiply %1330, %1331 : tensor<?x64xf32>
    %1333 = shape.shape_of %1285 : tensor<?x64xf32> -> tensor<2xindex>
    %1334 = shape.broadcast %1327, %1333 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1335 = stablehlo.dynamic_broadcast_in_dim %collapsed_426, %1334, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1336 = stablehlo.dynamic_broadcast_in_dim %1285, %1334, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1337 = stablehlo.multiply %1335, %1336 : tensor<?x64xf32>
    %dim_427 = tensor.dim %arg222, %c0 : tensor<?x64x32xf32>
    %expanded_428 = tensor.expand_shape %arg222 [[0, 1], [2], [3]] output_shape [1, %dim_427, 64, 32] : tensor<?x64x32xf32> into tensor<1x?x64x32xf32>
    %dim_429 = tensor.dim %arg223, %c0 : tensor<?x64x32xf32>
    %expanded_430 = tensor.expand_shape %arg223 [[0, 1], [2], [3]] output_shape [1, %dim_429, 64, 32] : tensor<?x64x32xf32> into tensor<1x?x64x32xf32>
    %1338 = stablehlo.concatenate %expanded_428, %expanded_430, dim = 0 : (tensor<1x?x64x32xf32>, tensor<1x?x64x32xf32>) -> tensor<2x?x64x32xf32>
    %dim_431 = tensor.dim %arg224, %c0 : tensor<?x1x32xf32>
    %expanded_432 = tensor.expand_shape %arg224 [[0, 1], [2], [3]] output_shape [1, %dim_431, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %dim_433 = tensor.dim %arg225, %c0 : tensor<?x1x32xf32>
    %expanded_434 = tensor.expand_shape %arg225 [[0, 1], [2], [3]] output_shape [1, %dim_433, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %1339 = stablehlo.concatenate %expanded_432, %expanded_434, dim = 0 : (tensor<1x?x1x32xf32>, tensor<1x?x1x32xf32>) -> tensor<2x?x1x32xf32>
    %1340 = shape.shape_of %1339 : tensor<2x?x1x32xf32> -> tensor<4xindex>
    %1341 = shape.shape_of %1338 : tensor<2x?x64x32xf32> -> tensor<4xindex>
    %head_435, %tail_436 = "shape.split_at"(%1340, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_437, %tail_438 = "shape.split_at"(%1341, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1342 = shape.broadcast %head_435, %head_437 : !shape.shape, !shape.shape -> !shape.shape
    %1343 = shape.concat %1342, %tail_436 : !shape.shape, !shape.shape -> !shape.shape
    %1344 = shape.to_extent_tensor %1343 : !shape.shape -> tensor<4xindex>
    %1345 = stablehlo.dynamic_broadcast_in_dim %1339, %1344, dims = [0, 1, 2, 3] : (tensor<2x?x1x32xf32>, tensor<4xindex>) -> tensor<2x?x1x32xf32>
    %1346 = shape.concat %1342, %tail_438 : !shape.shape, !shape.shape -> !shape.shape
    %1347 = shape.to_extent_tensor %1346 : !shape.shape -> tensor<4xindex>
    %1348 = stablehlo.dynamic_broadcast_in_dim %1338, %1347, dims = [0, 1, 2, 3] : (tensor<2x?x64x32xf32>, tensor<4xindex>) -> tensor<2x?x64x32xf32>
    %1349 = stablehlo.dot_general %1345, %1348, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x32xf32>, tensor<2x?x64x32xf32>) -> tensor<2x?x1x64xf32>
    %1350 = shape.shape_of %1349 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1351 = stablehlo.dynamic_broadcast_in_dim %cst, %1350, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1352 = stablehlo.multiply %1349, %1351 : tensor<2x?x1x64xf32>
    %1353 = shape.shape_of %1352 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1354 = shape.broadcast %1085, %1353 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1355 = stablehlo.dynamic_broadcast_in_dim %79, %1354, dims = [1, 2, 3] : (tensor<?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1356 = stablehlo.dynamic_broadcast_in_dim %1352, %1354, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1357 = stablehlo.add %1355, %1356 : tensor<2x?x1x64xf32>
    %1358 = stablehlo.reduce(%1357 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_439 = tensor.dim %1358, %c1 : tensor<2x?x1xf32>
    %from_elements_440 = tensor.from_elements %c2, %dim_439, %c1, %c1 : tensor<4xindex>
    %dim_441 = tensor.dim %1358, %c1 : tensor<2x?x1xf32>
    %expanded_442 = tensor.expand_shape %1358 [[0], [1], [2, 3]] output_shape [2, %dim_441, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1359 = shape.shape_of %1357 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1360 = shape.broadcast %1359, %from_elements_440 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1361 = stablehlo.dynamic_broadcast_in_dim %1357, %1360, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1362 = stablehlo.dynamic_broadcast_in_dim %expanded_442, %1360, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1363 = stablehlo.subtract %1361, %1362 : tensor<2x?x1x64xf32>
    %1364 = stablehlo.exponential %1363 : tensor<2x?x1x64xf32>
    %1365 = stablehlo.reduce(%1364 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<2x?x1x64xf32>, tensor<f32>) -> tensor<2x?x1xf32>
    %dim_443 = tensor.dim %1365, %c1 : tensor<2x?x1xf32>
    %from_elements_444 = tensor.from_elements %c2, %dim_443, %c1, %c1 : tensor<4xindex>
    %dim_445 = tensor.dim %1365, %c1 : tensor<2x?x1xf32>
    %expanded_446 = tensor.expand_shape %1365 [[0], [1], [2, 3]] output_shape [2, %dim_445, 1, 1] : tensor<2x?x1xf32> into tensor<2x?x1x1xf32>
    %1366 = shape.shape_of %1364 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1367 = shape.broadcast %1366, %from_elements_444 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1368 = stablehlo.dynamic_broadcast_in_dim %1364, %1367, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1369 = stablehlo.dynamic_broadcast_in_dim %expanded_446, %1367, dims = [0, 1, 2, 3] : (tensor<2x?x1x1xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1370 = stablehlo.divide %1368, %1369 : tensor<2x?x1x64xf32>
    %dim_447 = tensor.dim %arg226, %c0 : tensor<?x64x32xf32>
    %expanded_448 = tensor.expand_shape %arg226 [[0, 1], [2], [3]] output_shape [1, %dim_447, 64, 32] : tensor<?x64x32xf32> into tensor<1x?x64x32xf32>
    %dim_449 = tensor.dim %arg227, %c0 : tensor<?x64x32xf32>
    %expanded_450 = tensor.expand_shape %arg227 [[0, 1], [2], [3]] output_shape [1, %dim_449, 64, 32] : tensor<?x64x32xf32> into tensor<1x?x64x32xf32>
    %1371 = stablehlo.concatenate %expanded_448, %expanded_450, dim = 0 : (tensor<1x?x64x32xf32>, tensor<1x?x64x32xf32>) -> tensor<2x?x64x32xf32>
    %1372 = shape.shape_of %1370 : tensor<2x?x1x64xf32> -> tensor<4xindex>
    %1373 = shape.shape_of %1371 : tensor<2x?x64x32xf32> -> tensor<4xindex>
    %head_451, %tail_452 = "shape.split_at"(%1372, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_453, %tail_454 = "shape.split_at"(%1373, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1374 = shape.broadcast %head_451, %head_453 : !shape.shape, !shape.shape -> !shape.shape
    %1375 = shape.concat %1374, %tail_452 : !shape.shape, !shape.shape -> !shape.shape
    %1376 = shape.to_extent_tensor %1375 : !shape.shape -> tensor<4xindex>
    %1377 = stablehlo.dynamic_broadcast_in_dim %1370, %1376, dims = [0, 1, 2, 3] : (tensor<2x?x1x64xf32>, tensor<4xindex>) -> tensor<2x?x1x64xf32>
    %1378 = shape.concat %1374, %tail_454 : !shape.shape, !shape.shape -> !shape.shape
    %1379 = shape.to_extent_tensor %1378 : !shape.shape -> tensor<4xindex>
    %1380 = stablehlo.dynamic_broadcast_in_dim %1371, %1379, dims = [0, 1, 2, 3] : (tensor<2x?x64x32xf32>, tensor<4xindex>) -> tensor<2x?x64x32xf32>
    %1381 = stablehlo.dot_general %1377, %1380, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<2x?x1x64xf32>, tensor<2x?x64x32xf32>) -> tensor<2x?x1x32xf32>
    %1382 = stablehlo.transpose %1381, dims = [1, 2, 0, 3] : (tensor<2x?x1x32xf32>) -> tensor<?x1x2x32xf32>
    %collapsed_455 = tensor.collapse_shape %1382 [[0], [1, 2, 3]] : tensor<?x1x2x32xf32> into tensor<?x64xf32>
    %dim_456 = tensor.dim %arg228, %c0 : tensor<?x30x32xf32>
    %from_elements_457 = tensor.from_elements %c1, %dim_456, %c30, %c32_32 : tensor<4xindex>
    %dim_458 = tensor.dim %arg228, %c0 : tensor<?x30x32xf32>
    %expanded_459 = tensor.expand_shape %arg228 [[0, 1], [2], [3]] output_shape [1, %dim_458, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %dim_460 = tensor.dim %arg229, %c0 : tensor<?x1x32xf32>
    %from_elements_461 = tensor.from_elements %c1, %dim_460, %c1, %c32_32 : tensor<4xindex>
    %dim_462 = tensor.dim %arg229, %c0 : tensor<?x1x32xf32>
    %expanded_463 = tensor.expand_shape %arg229 [[0, 1], [2], [3]] output_shape [1, %dim_462, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_464, %tail_465 = "shape.split_at"(%from_elements_461, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_466, %tail_467 = "shape.split_at"(%from_elements_457, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1383 = shape.broadcast %head_464, %head_466 : !shape.shape, !shape.shape -> !shape.shape
    %1384 = shape.concat %1383, %tail_465 : !shape.shape, !shape.shape -> !shape.shape
    %1385 = shape.to_extent_tensor %1384 : !shape.shape -> tensor<4xindex>
    %1386 = stablehlo.dynamic_broadcast_in_dim %expanded_463, %1385, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %1387 = shape.concat %1383, %tail_467 : !shape.shape, !shape.shape -> !shape.shape
    %1388 = shape.to_extent_tensor %1387 : !shape.shape -> tensor<4xindex>
    %1389 = stablehlo.dynamic_broadcast_in_dim %expanded_459, %1388, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %1390 = stablehlo.dot_general %1386, %1389, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x30xf32>
    %1391 = shape.shape_of %1390 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1392 = stablehlo.dynamic_broadcast_in_dim %cst, %1391, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1393 = stablehlo.multiply %1390, %1392 : tensor<1x?x1x30xf32>
    %1394 = shape.shape_of %73 : tensor<?x1x30xf32> -> tensor<3xindex>
    %1395 = shape.shape_of %1393 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1396 = shape.broadcast %1394, %1395 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1397 = stablehlo.dynamic_broadcast_in_dim %73, %1396, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1398 = stablehlo.dynamic_broadcast_in_dim %1393, %1396, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1399 = stablehlo.add %1397, %1398 : tensor<1x?x1x30xf32>
    %1400 = stablehlo.reduce(%1399 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_468 = tensor.dim %1400, %c1 : tensor<1x?x1xf32>
    %from_elements_469 = tensor.from_elements %c1, %dim_468, %c1, %c1 : tensor<4xindex>
    %dim_470 = tensor.dim %1400, %c1 : tensor<1x?x1xf32>
    %expanded_471 = tensor.expand_shape %1400 [[0], [1], [2, 3]] output_shape [1, %dim_470, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1401 = shape.shape_of %1399 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1402 = shape.broadcast %1401, %from_elements_469 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1403 = stablehlo.dynamic_broadcast_in_dim %1399, %1402, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1404 = stablehlo.dynamic_broadcast_in_dim %expanded_471, %1402, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1405 = stablehlo.subtract %1403, %1404 : tensor<1x?x1x30xf32>
    %1406 = stablehlo.exponential %1405 : tensor<1x?x1x30xf32>
    %1407 = stablehlo.reduce(%1406 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_472 = tensor.dim %1407, %c1 : tensor<1x?x1xf32>
    %from_elements_473 = tensor.from_elements %c1, %dim_472, %c1, %c1 : tensor<4xindex>
    %dim_474 = tensor.dim %1407, %c1 : tensor<1x?x1xf32>
    %expanded_475 = tensor.expand_shape %1407 [[0], [1], [2, 3]] output_shape [1, %dim_474, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1408 = shape.shape_of %1406 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1409 = shape.broadcast %1408, %from_elements_473 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1410 = stablehlo.dynamic_broadcast_in_dim %1406, %1409, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1411 = stablehlo.dynamic_broadcast_in_dim %expanded_475, %1409, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1412 = stablehlo.divide %1410, %1411 : tensor<1x?x1x30xf32>
    %dim_476 = tensor.dim %arg230, %c0 : tensor<?x30x32xf32>
    %from_elements_477 = tensor.from_elements %c1, %dim_476, %c30, %c32_32 : tensor<4xindex>
    %dim_478 = tensor.dim %arg230, %c0 : tensor<?x30x32xf32>
    %expanded_479 = tensor.expand_shape %arg230 [[0, 1], [2], [3]] output_shape [1, %dim_478, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %1413 = shape.shape_of %1412 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_480, %tail_481 = "shape.split_at"(%1413, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_482, %tail_483 = "shape.split_at"(%from_elements_477, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1414 = shape.broadcast %head_480, %head_482 : !shape.shape, !shape.shape -> !shape.shape
    %1415 = shape.concat %1414, %tail_481 : !shape.shape, !shape.shape -> !shape.shape
    %1416 = shape.to_extent_tensor %1415 : !shape.shape -> tensor<4xindex>
    %1417 = stablehlo.dynamic_broadcast_in_dim %1412, %1416, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1418 = shape.concat %1414, %tail_483 : !shape.shape, !shape.shape -> !shape.shape
    %1419 = shape.to_extent_tensor %1418 : !shape.shape -> tensor<4xindex>
    %1420 = stablehlo.dynamic_broadcast_in_dim %expanded_479, %1419, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %1421 = stablehlo.dot_general %1417, %1420, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x32xf32>
    %1422 = stablehlo.transpose %1421, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_484 = tensor.collapse_shape %1422 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_485 = tensor.dim %arg231, %c0 : tensor<?x50x32xf32>
    %from_elements_486 = tensor.from_elements %c1, %dim_485, %c50, %c32_32 : tensor<4xindex>
    %dim_487 = tensor.dim %arg231, %c0 : tensor<?x50x32xf32>
    %expanded_488 = tensor.expand_shape %arg231 [[0, 1], [2], [3]] output_shape [1, %dim_487, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %dim_489 = tensor.dim %arg232, %c0 : tensor<?x1x32xf32>
    %from_elements_490 = tensor.from_elements %c1, %dim_489, %c1, %c32_32 : tensor<4xindex>
    %dim_491 = tensor.dim %arg232, %c0 : tensor<?x1x32xf32>
    %expanded_492 = tensor.expand_shape %arg232 [[0, 1], [2], [3]] output_shape [1, %dim_491, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_493, %tail_494 = "shape.split_at"(%from_elements_490, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_495, %tail_496 = "shape.split_at"(%from_elements_486, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1423 = shape.broadcast %head_493, %head_495 : !shape.shape, !shape.shape -> !shape.shape
    %1424 = shape.concat %1423, %tail_494 : !shape.shape, !shape.shape -> !shape.shape
    %1425 = shape.to_extent_tensor %1424 : !shape.shape -> tensor<4xindex>
    %1426 = stablehlo.dynamic_broadcast_in_dim %expanded_492, %1425, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %1427 = shape.concat %1423, %tail_496 : !shape.shape, !shape.shape -> !shape.shape
    %1428 = shape.to_extent_tensor %1427 : !shape.shape -> tensor<4xindex>
    %1429 = stablehlo.dynamic_broadcast_in_dim %expanded_488, %1428, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %1430 = stablehlo.dot_general %1426, %1429, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x50xf32>
    %1431 = shape.shape_of %1430 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1432 = stablehlo.dynamic_broadcast_in_dim %cst, %1431, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1433 = stablehlo.multiply %1430, %1432 : tensor<1x?x1x50xf32>
    %1434 = shape.shape_of %82 : tensor<?x1x50xf32> -> tensor<3xindex>
    %1435 = shape.shape_of %1433 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1436 = shape.broadcast %1434, %1435 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1437 = stablehlo.dynamic_broadcast_in_dim %82, %1436, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1438 = stablehlo.dynamic_broadcast_in_dim %1433, %1436, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1439 = stablehlo.add %1437, %1438 : tensor<1x?x1x50xf32>
    %1440 = stablehlo.reduce(%1439 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_497 = tensor.dim %1440, %c1 : tensor<1x?x1xf32>
    %from_elements_498 = tensor.from_elements %c1, %dim_497, %c1, %c1 : tensor<4xindex>
    %dim_499 = tensor.dim %1440, %c1 : tensor<1x?x1xf32>
    %expanded_500 = tensor.expand_shape %1440 [[0], [1], [2, 3]] output_shape [1, %dim_499, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1441 = shape.shape_of %1439 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1442 = shape.broadcast %1441, %from_elements_498 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1443 = stablehlo.dynamic_broadcast_in_dim %1439, %1442, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1444 = stablehlo.dynamic_broadcast_in_dim %expanded_500, %1442, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1445 = stablehlo.subtract %1443, %1444 : tensor<1x?x1x50xf32>
    %1446 = stablehlo.exponential %1445 : tensor<1x?x1x50xf32>
    %1447 = stablehlo.reduce(%1446 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_501 = tensor.dim %1447, %c1 : tensor<1x?x1xf32>
    %from_elements_502 = tensor.from_elements %c1, %dim_501, %c1, %c1 : tensor<4xindex>
    %dim_503 = tensor.dim %1447, %c1 : tensor<1x?x1xf32>
    %expanded_504 = tensor.expand_shape %1447 [[0], [1], [2, 3]] output_shape [1, %dim_503, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1448 = shape.shape_of %1446 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1449 = shape.broadcast %1448, %from_elements_502 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1450 = stablehlo.dynamic_broadcast_in_dim %1446, %1449, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1451 = stablehlo.dynamic_broadcast_in_dim %expanded_504, %1449, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1452 = stablehlo.divide %1450, %1451 : tensor<1x?x1x50xf32>
    %dim_505 = tensor.dim %arg233, %c0 : tensor<?x50x32xf32>
    %from_elements_506 = tensor.from_elements %c1, %dim_505, %c50, %c32_32 : tensor<4xindex>
    %dim_507 = tensor.dim %arg233, %c0 : tensor<?x50x32xf32>
    %expanded_508 = tensor.expand_shape %arg233 [[0, 1], [2], [3]] output_shape [1, %dim_507, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %1453 = shape.shape_of %1452 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_509, %tail_510 = "shape.split_at"(%1453, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_511, %tail_512 = "shape.split_at"(%from_elements_506, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1454 = shape.broadcast %head_509, %head_511 : !shape.shape, !shape.shape -> !shape.shape
    %1455 = shape.concat %1454, %tail_510 : !shape.shape, !shape.shape -> !shape.shape
    %1456 = shape.to_extent_tensor %1455 : !shape.shape -> tensor<4xindex>
    %1457 = stablehlo.dynamic_broadcast_in_dim %1452, %1456, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1458 = shape.concat %1454, %tail_512 : !shape.shape, !shape.shape -> !shape.shape
    %1459 = shape.to_extent_tensor %1458 : !shape.shape -> tensor<4xindex>
    %1460 = stablehlo.dynamic_broadcast_in_dim %expanded_508, %1459, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %1461 = stablehlo.dot_general %1457, %1460, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x32xf32>
    %1462 = stablehlo.transpose %1461, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_513 = tensor.collapse_shape %1462 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_514 = tensor.dim %arg234, %c0 : tensor<?x50x16xf32>
    %from_elements_515 = tensor.from_elements %c1, %dim_514, %c50, %c16 : tensor<4xindex>
    %dim_516 = tensor.dim %arg234, %c0 : tensor<?x50x16xf32>
    %expanded_517 = tensor.expand_shape %arg234 [[0, 1], [2], [3]] output_shape [1, %dim_516, 50, 16] : tensor<?x50x16xf32> into tensor<1x?x50x16xf32>
    %dim_518 = tensor.dim %arg235, %c0 : tensor<?x1x16xf32>
    %from_elements_519 = tensor.from_elements %c1, %dim_518, %c1, %c16 : tensor<4xindex>
    %dim_520 = tensor.dim %arg235, %c0 : tensor<?x1x16xf32>
    %expanded_521 = tensor.expand_shape %arg235 [[0, 1], [2], [3]] output_shape [1, %dim_520, 1, 16] : tensor<?x1x16xf32> into tensor<1x?x1x16xf32>
    %head_522, %tail_523 = "shape.split_at"(%from_elements_519, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_524, %tail_525 = "shape.split_at"(%from_elements_515, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1463 = shape.broadcast %head_522, %head_524 : !shape.shape, !shape.shape -> !shape.shape
    %1464 = shape.concat %1463, %tail_523 : !shape.shape, !shape.shape -> !shape.shape
    %1465 = shape.to_extent_tensor %1464 : !shape.shape -> tensor<4xindex>
    %1466 = stablehlo.dynamic_broadcast_in_dim %expanded_521, %1465, dims = [0, 1, 2, 3] : (tensor<1x?x1x16xf32>, tensor<4xindex>) -> tensor<1x?x1x16xf32>
    %1467 = shape.concat %1463, %tail_525 : !shape.shape, !shape.shape -> !shape.shape
    %1468 = shape.to_extent_tensor %1467 : !shape.shape -> tensor<4xindex>
    %1469 = stablehlo.dynamic_broadcast_in_dim %expanded_517, %1468, dims = [0, 1, 2, 3] : (tensor<1x?x50x16xf32>, tensor<4xindex>) -> tensor<1x?x50x16xf32>
    %1470 = stablehlo.dot_general %1466, %1469, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x16xf32>, tensor<1x?x50x16xf32>) -> tensor<1x?x1x50xf32>
    %1471 = shape.shape_of %1470 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1472 = stablehlo.dynamic_broadcast_in_dim %cst_4, %1471, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1473 = stablehlo.multiply %1470, %1472 : tensor<1x?x1x50xf32>
    %1474 = shape.shape_of %1473 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1475 = shape.broadcast %1434, %1474 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1476 = stablehlo.dynamic_broadcast_in_dim %82, %1475, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1477 = stablehlo.dynamic_broadcast_in_dim %1473, %1475, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1478 = stablehlo.add %1476, %1477 : tensor<1x?x1x50xf32>
    %1479 = stablehlo.reduce(%1478 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_526 = tensor.dim %1479, %c1 : tensor<1x?x1xf32>
    %from_elements_527 = tensor.from_elements %c1, %dim_526, %c1, %c1 : tensor<4xindex>
    %dim_528 = tensor.dim %1479, %c1 : tensor<1x?x1xf32>
    %expanded_529 = tensor.expand_shape %1479 [[0], [1], [2, 3]] output_shape [1, %dim_528, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1480 = shape.shape_of %1478 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1481 = shape.broadcast %1480, %from_elements_527 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1482 = stablehlo.dynamic_broadcast_in_dim %1478, %1481, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1483 = stablehlo.dynamic_broadcast_in_dim %expanded_529, %1481, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1484 = stablehlo.subtract %1482, %1483 : tensor<1x?x1x50xf32>
    %1485 = stablehlo.exponential %1484 : tensor<1x?x1x50xf32>
    %1486 = stablehlo.reduce(%1485 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_530 = tensor.dim %1486, %c1 : tensor<1x?x1xf32>
    %from_elements_531 = tensor.from_elements %c1, %dim_530, %c1, %c1 : tensor<4xindex>
    %dim_532 = tensor.dim %1486, %c1 : tensor<1x?x1xf32>
    %expanded_533 = tensor.expand_shape %1486 [[0], [1], [2, 3]] output_shape [1, %dim_532, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1487 = shape.shape_of %1485 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1488 = shape.broadcast %1487, %from_elements_531 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1489 = stablehlo.dynamic_broadcast_in_dim %1485, %1488, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1490 = stablehlo.dynamic_broadcast_in_dim %expanded_533, %1488, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1491 = stablehlo.divide %1489, %1490 : tensor<1x?x1x50xf32>
    %dim_534 = tensor.dim %arg236, %c0 : tensor<?x50x16xf32>
    %from_elements_535 = tensor.from_elements %c1, %dim_534, %c50, %c16 : tensor<4xindex>
    %dim_536 = tensor.dim %arg236, %c0 : tensor<?x50x16xf32>
    %expanded_537 = tensor.expand_shape %arg236 [[0, 1], [2], [3]] output_shape [1, %dim_536, 50, 16] : tensor<?x50x16xf32> into tensor<1x?x50x16xf32>
    %1492 = shape.shape_of %1491 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_538, %tail_539 = "shape.split_at"(%1492, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_540, %tail_541 = "shape.split_at"(%from_elements_535, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1493 = shape.broadcast %head_538, %head_540 : !shape.shape, !shape.shape -> !shape.shape
    %1494 = shape.concat %1493, %tail_539 : !shape.shape, !shape.shape -> !shape.shape
    %1495 = shape.to_extent_tensor %1494 : !shape.shape -> tensor<4xindex>
    %1496 = stablehlo.dynamic_broadcast_in_dim %1491, %1495, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1497 = shape.concat %1493, %tail_541 : !shape.shape, !shape.shape -> !shape.shape
    %1498 = shape.to_extent_tensor %1497 : !shape.shape -> tensor<4xindex>
    %1499 = stablehlo.dynamic_broadcast_in_dim %expanded_537, %1498, dims = [0, 1, 2, 3] : (tensor<1x?x50x16xf32>, tensor<4xindex>) -> tensor<1x?x50x16xf32>
    %1500 = stablehlo.dot_general %1496, %1499, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x16xf32>) -> tensor<1x?x1x16xf32>
    %1501 = stablehlo.transpose %1500, dims = [1, 2, 0, 3] : (tensor<1x?x1x16xf32>) -> tensor<?x1x1x16xf32>
    %collapsed_542 = tensor.collapse_shape %1501 [[0], [1, 2, 3]] : tensor<?x1x1x16xf32> into tensor<?x16xf32>
    %dim_543 = tensor.dim %arg237, %c0 : tensor<?x50x8xf32>
    %from_elements_544 = tensor.from_elements %c1, %dim_543, %c50, %c8 : tensor<4xindex>
    %dim_545 = tensor.dim %arg237, %c0 : tensor<?x50x8xf32>
    %expanded_546 = tensor.expand_shape %arg237 [[0, 1], [2], [3]] output_shape [1, %dim_545, 50, 8] : tensor<?x50x8xf32> into tensor<1x?x50x8xf32>
    %dim_547 = tensor.dim %arg238, %c0 : tensor<?x1x8xf32>
    %from_elements_548 = tensor.from_elements %c1, %dim_547, %c1, %c8 : tensor<4xindex>
    %dim_549 = tensor.dim %arg238, %c0 : tensor<?x1x8xf32>
    %expanded_550 = tensor.expand_shape %arg238 [[0, 1], [2], [3]] output_shape [1, %dim_549, 1, 8] : tensor<?x1x8xf32> into tensor<1x?x1x8xf32>
    %head_551, %tail_552 = "shape.split_at"(%from_elements_548, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_553, %tail_554 = "shape.split_at"(%from_elements_544, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1502 = shape.broadcast %head_551, %head_553 : !shape.shape, !shape.shape -> !shape.shape
    %1503 = shape.concat %1502, %tail_552 : !shape.shape, !shape.shape -> !shape.shape
    %1504 = shape.to_extent_tensor %1503 : !shape.shape -> tensor<4xindex>
    %1505 = stablehlo.dynamic_broadcast_in_dim %expanded_550, %1504, dims = [0, 1, 2, 3] : (tensor<1x?x1x8xf32>, tensor<4xindex>) -> tensor<1x?x1x8xf32>
    %1506 = shape.concat %1502, %tail_554 : !shape.shape, !shape.shape -> !shape.shape
    %1507 = shape.to_extent_tensor %1506 : !shape.shape -> tensor<4xindex>
    %1508 = stablehlo.dynamic_broadcast_in_dim %expanded_546, %1507, dims = [0, 1, 2, 3] : (tensor<1x?x50x8xf32>, tensor<4xindex>) -> tensor<1x?x50x8xf32>
    %1509 = stablehlo.dot_general %1505, %1508, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x8xf32>, tensor<1x?x50x8xf32>) -> tensor<1x?x1x50xf32>
    %1510 = shape.shape_of %1509 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1511 = stablehlo.dynamic_broadcast_in_dim %cst_2, %1510, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1512 = stablehlo.multiply %1509, %1511 : tensor<1x?x1x50xf32>
    %1513 = shape.shape_of %1512 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1514 = shape.broadcast %1434, %1513 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1515 = stablehlo.dynamic_broadcast_in_dim %82, %1514, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1516 = stablehlo.dynamic_broadcast_in_dim %1512, %1514, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1517 = stablehlo.add %1515, %1516 : tensor<1x?x1x50xf32>
    %1518 = stablehlo.reduce(%1517 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_555 = tensor.dim %1518, %c1 : tensor<1x?x1xf32>
    %from_elements_556 = tensor.from_elements %c1, %dim_555, %c1, %c1 : tensor<4xindex>
    %dim_557 = tensor.dim %1518, %c1 : tensor<1x?x1xf32>
    %expanded_558 = tensor.expand_shape %1518 [[0], [1], [2, 3]] output_shape [1, %dim_557, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1519 = shape.shape_of %1517 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1520 = shape.broadcast %1519, %from_elements_556 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1521 = stablehlo.dynamic_broadcast_in_dim %1517, %1520, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1522 = stablehlo.dynamic_broadcast_in_dim %expanded_558, %1520, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1523 = stablehlo.subtract %1521, %1522 : tensor<1x?x1x50xf32>
    %1524 = stablehlo.exponential %1523 : tensor<1x?x1x50xf32>
    %1525 = stablehlo.reduce(%1524 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_559 = tensor.dim %1525, %c1 : tensor<1x?x1xf32>
    %from_elements_560 = tensor.from_elements %c1, %dim_559, %c1, %c1 : tensor<4xindex>
    %dim_561 = tensor.dim %1525, %c1 : tensor<1x?x1xf32>
    %expanded_562 = tensor.expand_shape %1525 [[0], [1], [2, 3]] output_shape [1, %dim_561, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1526 = shape.shape_of %1524 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1527 = shape.broadcast %1526, %from_elements_560 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1528 = stablehlo.dynamic_broadcast_in_dim %1524, %1527, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1529 = stablehlo.dynamic_broadcast_in_dim %expanded_562, %1527, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1530 = stablehlo.divide %1528, %1529 : tensor<1x?x1x50xf32>
    %dim_563 = tensor.dim %arg239, %c0 : tensor<?x50x8xf32>
    %from_elements_564 = tensor.from_elements %c1, %dim_563, %c50, %c8 : tensor<4xindex>
    %dim_565 = tensor.dim %arg239, %c0 : tensor<?x50x8xf32>
    %expanded_566 = tensor.expand_shape %arg239 [[0, 1], [2], [3]] output_shape [1, %dim_565, 50, 8] : tensor<?x50x8xf32> into tensor<1x?x50x8xf32>
    %1531 = shape.shape_of %1530 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_567, %tail_568 = "shape.split_at"(%1531, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_569, %tail_570 = "shape.split_at"(%from_elements_564, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1532 = shape.broadcast %head_567, %head_569 : !shape.shape, !shape.shape -> !shape.shape
    %1533 = shape.concat %1532, %tail_568 : !shape.shape, !shape.shape -> !shape.shape
    %1534 = shape.to_extent_tensor %1533 : !shape.shape -> tensor<4xindex>
    %1535 = stablehlo.dynamic_broadcast_in_dim %1530, %1534, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1536 = shape.concat %1532, %tail_570 : !shape.shape, !shape.shape -> !shape.shape
    %1537 = shape.to_extent_tensor %1536 : !shape.shape -> tensor<4xindex>
    %1538 = stablehlo.dynamic_broadcast_in_dim %expanded_566, %1537, dims = [0, 1, 2, 3] : (tensor<1x?x50x8xf32>, tensor<4xindex>) -> tensor<1x?x50x8xf32>
    %1539 = stablehlo.dot_general %1535, %1538, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x8xf32>) -> tensor<1x?x1x8xf32>
    %1540 = stablehlo.transpose %1539, dims = [1, 2, 0, 3] : (tensor<1x?x1x8xf32>) -> tensor<?x1x1x8xf32>
    %collapsed_571 = tensor.collapse_shape %1540 [[0], [1, 2, 3]] : tensor<?x1x1x8xf32> into tensor<?x8xf32>
    %dim_572 = tensor.dim %arg240, %c0 : tensor<?x50x64xf32>
    %from_elements_573 = tensor.from_elements %c1, %dim_572, %c50, %c64_33 : tensor<4xindex>
    %dim_574 = tensor.dim %arg240, %c0 : tensor<?x50x64xf32>
    %expanded_575 = tensor.expand_shape %arg240 [[0, 1], [2], [3]] output_shape [1, %dim_574, 50, 64] : tensor<?x50x64xf32> into tensor<1x?x50x64xf32>
    %dim_576 = tensor.dim %arg241, %c0 : tensor<?x1x64xf32>
    %from_elements_577 = tensor.from_elements %c1, %dim_576, %c1, %c64_33 : tensor<4xindex>
    %dim_578 = tensor.dim %arg241, %c0 : tensor<?x1x64xf32>
    %expanded_579 = tensor.expand_shape %arg241 [[0, 1], [2], [3]] output_shape [1, %dim_578, 1, 64] : tensor<?x1x64xf32> into tensor<1x?x1x64xf32>
    %head_580, %tail_581 = "shape.split_at"(%from_elements_577, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_582, %tail_583 = "shape.split_at"(%from_elements_573, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1541 = shape.broadcast %head_580, %head_582 : !shape.shape, !shape.shape -> !shape.shape
    %1542 = shape.concat %1541, %tail_581 : !shape.shape, !shape.shape -> !shape.shape
    %1543 = shape.to_extent_tensor %1542 : !shape.shape -> tensor<4xindex>
    %1544 = stablehlo.dynamic_broadcast_in_dim %expanded_579, %1543, dims = [0, 1, 2, 3] : (tensor<1x?x1x64xf32>, tensor<4xindex>) -> tensor<1x?x1x64xf32>
    %1545 = shape.concat %1541, %tail_583 : !shape.shape, !shape.shape -> !shape.shape
    %1546 = shape.to_extent_tensor %1545 : !shape.shape -> tensor<4xindex>
    %1547 = stablehlo.dynamic_broadcast_in_dim %expanded_575, %1546, dims = [0, 1, 2, 3] : (tensor<1x?x50x64xf32>, tensor<4xindex>) -> tensor<1x?x50x64xf32>
    %1548 = stablehlo.dot_general %1544, %1547, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x64xf32>, tensor<1x?x50x64xf32>) -> tensor<1x?x1x50xf32>
    %1549 = shape.shape_of %1548 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1550 = stablehlo.dynamic_broadcast_in_dim %cst_6, %1549, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1551 = stablehlo.multiply %1548, %1550 : tensor<1x?x1x50xf32>
    %1552 = shape.shape_of %1551 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1553 = shape.broadcast %1434, %1552 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1554 = stablehlo.dynamic_broadcast_in_dim %82, %1553, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1555 = stablehlo.dynamic_broadcast_in_dim %1551, %1553, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1556 = stablehlo.add %1554, %1555 : tensor<1x?x1x50xf32>
    %1557 = stablehlo.reduce(%1556 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_584 = tensor.dim %1557, %c1 : tensor<1x?x1xf32>
    %from_elements_585 = tensor.from_elements %c1, %dim_584, %c1, %c1 : tensor<4xindex>
    %dim_586 = tensor.dim %1557, %c1 : tensor<1x?x1xf32>
    %expanded_587 = tensor.expand_shape %1557 [[0], [1], [2, 3]] output_shape [1, %dim_586, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1558 = shape.shape_of %1556 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1559 = shape.broadcast %1558, %from_elements_585 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1560 = stablehlo.dynamic_broadcast_in_dim %1556, %1559, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1561 = stablehlo.dynamic_broadcast_in_dim %expanded_587, %1559, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1562 = stablehlo.subtract %1560, %1561 : tensor<1x?x1x50xf32>
    %1563 = stablehlo.exponential %1562 : tensor<1x?x1x50xf32>
    %1564 = stablehlo.reduce(%1563 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_588 = tensor.dim %1564, %c1 : tensor<1x?x1xf32>
    %from_elements_589 = tensor.from_elements %c1, %dim_588, %c1, %c1 : tensor<4xindex>
    %dim_590 = tensor.dim %1564, %c1 : tensor<1x?x1xf32>
    %expanded_591 = tensor.expand_shape %1564 [[0], [1], [2, 3]] output_shape [1, %dim_590, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1565 = shape.shape_of %1563 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1566 = shape.broadcast %1565, %from_elements_589 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1567 = stablehlo.dynamic_broadcast_in_dim %1563, %1566, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1568 = stablehlo.dynamic_broadcast_in_dim %expanded_591, %1566, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1569 = stablehlo.divide %1567, %1568 : tensor<1x?x1x50xf32>
    %1570 = stablehlo.transpose %1556, dims = [1, 0, 2, 3] : (tensor<1x?x1x50xf32>) -> tensor<?x1x1x50xf32>
    %collapsed_592 = tensor.collapse_shape %1570 [[0], [1, 2, 3]] : tensor<?x1x1x50xf32> into tensor<?x50xf32>
    %1571 = stablehlo.concatenate %collapsed_592, %collapsed_173, dim = 1 : (tensor<?x50xf32>, tensor<?x50xf32>) -> tensor<?x100xf32>
    %1572 = stablehlo.dot %1571, %arg242, precision = [DEFAULT, DEFAULT] : (tensor<?x100xf32>, tensor<100x128xf32>) -> tensor<?x128xf32>
    %1573 = shape.shape_of %1572 : tensor<?x128xf32> -> tensor<2xindex>
    %1574 = stablehlo.dynamic_broadcast_in_dim %arg243, %1573, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1575 = stablehlo.add %1572, %1574 : tensor<?x128xf32>
    %1576 = stablehlo.logistic %1575 : tensor<?x128xf32>
    %1577 = shape.shape_of %1575 : tensor<?x128xf32> -> tensor<2xindex>
    %1578 = shape.shape_of %1576 : tensor<?x128xf32> -> tensor<2xindex>
    %1579 = shape.broadcast %1577, %1578 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1580 = stablehlo.dynamic_broadcast_in_dim %1575, %1579, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1581 = stablehlo.dynamic_broadcast_in_dim %1576, %1579, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1582 = stablehlo.multiply %1580, %1581 : tensor<?x128xf32>
    %1583 = stablehlo.dot %1582, %arg244, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %1584 = shape.shape_of %1583 : tensor<?x64xf32> -> tensor<2xindex>
    %1585 = stablehlo.dynamic_broadcast_in_dim %arg245, %1584, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1586 = stablehlo.add %1583, %1585 : tensor<?x64xf32>
    %1587 = stablehlo.dot %1586, %arg246, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %1588 = shape.shape_of %1587 : tensor<?x64xf32> -> tensor<2xindex>
    %1589 = stablehlo.dynamic_broadcast_in_dim %arg247, %1588, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1590 = stablehlo.add %1587, %1589 : tensor<?x64xf32>
    %1591 = stablehlo.logistic %1590 : tensor<?x64xf32>
    %1592 = shape.shape_of %1591 : tensor<?x64xf32> -> tensor<2xindex>
    %1593 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1592, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1594 = stablehlo.multiply %1591, %1593 : tensor<?x64xf32>
    %1595 = stablehlo.dot %1586, %arg248, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %1596 = shape.shape_of %1595 : tensor<?x32xf32> -> tensor<2xindex>
    %1597 = stablehlo.dynamic_broadcast_in_dim %arg249, %1596, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1598 = stablehlo.add %1595, %1597 : tensor<?x32xf32>
    %1599 = stablehlo.logistic %1598 : tensor<?x32xf32>
    %1600 = shape.shape_of %1599 : tensor<?x32xf32> -> tensor<2xindex>
    %1601 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1600, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1602 = stablehlo.multiply %1599, %1601 : tensor<?x32xf32>
    %1603 = shape.shape_of %1602 : tensor<?x32xf32> -> tensor<2xindex>
    %1604 = shape.broadcast %760, %1603 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1605 = stablehlo.dynamic_broadcast_in_dim %collapsed_182, %1604, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1606 = stablehlo.dynamic_broadcast_in_dim %1602, %1604, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1607 = stablehlo.multiply %1605, %1606 : tensor<?x32xf32>
    %1608 = stablehlo.concatenate %collapsed_592, %collapsed_143, dim = 1 : (tensor<?x50xf32>, tensor<?x30xf32>) -> tensor<?x80xf32>
    %1609 = stablehlo.dot %1608, %arg250, precision = [DEFAULT, DEFAULT] : (tensor<?x80xf32>, tensor<80x128xf32>) -> tensor<?x128xf32>
    %1610 = shape.shape_of %1609 : tensor<?x128xf32> -> tensor<2xindex>
    %1611 = stablehlo.dynamic_broadcast_in_dim %arg251, %1610, dims = [1] : (tensor<128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1612 = stablehlo.add %1609, %1611 : tensor<?x128xf32>
    %1613 = stablehlo.logistic %1612 : tensor<?x128xf32>
    %1614 = shape.shape_of %1612 : tensor<?x128xf32> -> tensor<2xindex>
    %1615 = shape.shape_of %1613 : tensor<?x128xf32> -> tensor<2xindex>
    %1616 = shape.broadcast %1614, %1615 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1617 = stablehlo.dynamic_broadcast_in_dim %1612, %1616, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1618 = stablehlo.dynamic_broadcast_in_dim %1613, %1616, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %1619 = stablehlo.multiply %1617, %1618 : tensor<?x128xf32>
    %1620 = stablehlo.dot %1619, %arg252, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x64xf32>) -> tensor<?x64xf32>
    %1621 = shape.shape_of %1620 : tensor<?x64xf32> -> tensor<2xindex>
    %1622 = stablehlo.dynamic_broadcast_in_dim %arg253, %1621, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1623 = stablehlo.add %1620, %1622 : tensor<?x64xf32>
    %1624 = stablehlo.dot %1623, %arg254, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %1625 = shape.shape_of %1624 : tensor<?x64xf32> -> tensor<2xindex>
    %1626 = stablehlo.dynamic_broadcast_in_dim %arg255, %1625, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1627 = stablehlo.add %1624, %1626 : tensor<?x64xf32>
    %1628 = stablehlo.logistic %1627 : tensor<?x64xf32>
    %1629 = shape.shape_of %1628 : tensor<?x64xf32> -> tensor<2xindex>
    %1630 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1629, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1631 = stablehlo.multiply %1628, %1630 : tensor<?x64xf32>
    %1632 = stablehlo.dot %1623, %arg256, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x32xf32>) -> tensor<?x32xf32>
    %1633 = shape.shape_of %1632 : tensor<?x32xf32> -> tensor<2xindex>
    %1634 = stablehlo.dynamic_broadcast_in_dim %arg257, %1633, dims = [1] : (tensor<32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1635 = stablehlo.add %1632, %1634 : tensor<?x32xf32>
    %1636 = stablehlo.logistic %1635 : tensor<?x32xf32>
    %1637 = shape.shape_of %1636 : tensor<?x32xf32> -> tensor<2xindex>
    %1638 = stablehlo.dynamic_broadcast_in_dim %cst_12, %1637, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1639 = stablehlo.multiply %1636, %1638 : tensor<?x32xf32>
    %1640 = shape.shape_of %1639 : tensor<?x32xf32> -> tensor<2xindex>
    %1641 = shape.broadcast %713, %1640 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1642 = stablehlo.dynamic_broadcast_in_dim %collapsed_152, %1641, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1643 = stablehlo.dynamic_broadcast_in_dim %1639, %1641, dims = [0, 1] : (tensor<?x32xf32>, tensor<2xindex>) -> tensor<?x32xf32>
    %1644 = stablehlo.multiply %1642, %1643 : tensor<?x32xf32>
    %dim_593 = tensor.dim %arg258, %c0 : tensor<?x50x64xf32>
    %from_elements_594 = tensor.from_elements %c1, %dim_593, %c50, %c64_33 : tensor<4xindex>
    %dim_595 = tensor.dim %arg258, %c0 : tensor<?x50x64xf32>
    %expanded_596 = tensor.expand_shape %arg258 [[0, 1], [2], [3]] output_shape [1, %dim_595, 50, 64] : tensor<?x50x64xf32> into tensor<1x?x50x64xf32>
    %1645 = shape.shape_of %1569 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_597, %tail_598 = "shape.split_at"(%1645, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_599, %tail_600 = "shape.split_at"(%from_elements_594, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1646 = shape.broadcast %head_597, %head_599 : !shape.shape, !shape.shape -> !shape.shape
    %1647 = shape.concat %1646, %tail_598 : !shape.shape, !shape.shape -> !shape.shape
    %1648 = shape.to_extent_tensor %1647 : !shape.shape -> tensor<4xindex>
    %1649 = stablehlo.dynamic_broadcast_in_dim %1569, %1648, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1650 = shape.concat %1646, %tail_600 : !shape.shape, !shape.shape -> !shape.shape
    %1651 = shape.to_extent_tensor %1650 : !shape.shape -> tensor<4xindex>
    %1652 = stablehlo.dynamic_broadcast_in_dim %expanded_596, %1651, dims = [0, 1, 2, 3] : (tensor<1x?x50x64xf32>, tensor<4xindex>) -> tensor<1x?x50x64xf32>
    %1653 = stablehlo.dot_general %1649, %1652, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x64xf32>) -> tensor<1x?x1x64xf32>
    %1654 = stablehlo.transpose %1653, dims = [1, 2, 0, 3] : (tensor<1x?x1x64xf32>) -> tensor<?x1x1x64xf32>
    %1655 = shape.shape_of %1654 : tensor<?x1x1x64xf32> -> tensor<4xindex>
    %1656 = shape.num_elements %1655 : tensor<4xindex> -> index
    %1657 = shape.index_to_size %1656
    %1658 = shape.div %1657, %c64 : !shape.size, !shape.size -> !shape.size
    %1659 = shape.from_extents %1658, %c64 : !shape.size, !shape.size
    %1660 = shape.to_extent_tensor %1659 : !shape.shape -> tensor<2xindex>
    %collapsed_601 = tensor.collapse_shape %1654 [[0], [1, 2, 3]] : tensor<?x1x1x64xf32> into tensor<?x64xf32>
    %1661 = shape.shape_of %1594 : tensor<?x64xf32> -> tensor<2xindex>
    %1662 = shape.broadcast %1660, %1661 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1663 = stablehlo.dynamic_broadcast_in_dim %collapsed_601, %1662, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1664 = stablehlo.dynamic_broadcast_in_dim %1594, %1662, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1665 = stablehlo.multiply %1663, %1664 : tensor<?x64xf32>
    %1666 = shape.shape_of %1631 : tensor<?x64xf32> -> tensor<2xindex>
    %1667 = shape.broadcast %1660, %1666 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %1668 = stablehlo.dynamic_broadcast_in_dim %collapsed_601, %1667, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1669 = stablehlo.dynamic_broadcast_in_dim %1631, %1667, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %1670 = stablehlo.multiply %1668, %1669 : tensor<?x64xf32>
    %dim_602 = tensor.dim %arg259, %c0 : tensor<?x30x32xf32>
    %from_elements_603 = tensor.from_elements %c1, %dim_602, %c30, %c32_32 : tensor<4xindex>
    %dim_604 = tensor.dim %arg259, %c0 : tensor<?x30x32xf32>
    %expanded_605 = tensor.expand_shape %arg259 [[0, 1], [2], [3]] output_shape [1, %dim_604, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %dim_606 = tensor.dim %arg260, %c0 : tensor<?x1x32xf32>
    %from_elements_607 = tensor.from_elements %c1, %dim_606, %c1, %c32_32 : tensor<4xindex>
    %dim_608 = tensor.dim %arg260, %c0 : tensor<?x1x32xf32>
    %expanded_609 = tensor.expand_shape %arg260 [[0, 1], [2], [3]] output_shape [1, %dim_608, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_610, %tail_611 = "shape.split_at"(%from_elements_607, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_612, %tail_613 = "shape.split_at"(%from_elements_603, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1671 = shape.broadcast %head_610, %head_612 : !shape.shape, !shape.shape -> !shape.shape
    %1672 = shape.concat %1671, %tail_611 : !shape.shape, !shape.shape -> !shape.shape
    %1673 = shape.to_extent_tensor %1672 : !shape.shape -> tensor<4xindex>
    %1674 = stablehlo.dynamic_broadcast_in_dim %expanded_609, %1673, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %1675 = shape.concat %1671, %tail_613 : !shape.shape, !shape.shape -> !shape.shape
    %1676 = shape.to_extent_tensor %1675 : !shape.shape -> tensor<4xindex>
    %1677 = stablehlo.dynamic_broadcast_in_dim %expanded_605, %1676, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %1678 = stablehlo.dot_general %1674, %1677, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x30xf32>
    %1679 = shape.shape_of %1678 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1680 = stablehlo.dynamic_broadcast_in_dim %cst, %1679, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1681 = stablehlo.multiply %1678, %1680 : tensor<1x?x1x30xf32>
    %1682 = shape.shape_of %88 : tensor<?x1x30xf32> -> tensor<3xindex>
    %1683 = shape.shape_of %1681 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1684 = shape.broadcast %1682, %1683 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1685 = stablehlo.dynamic_broadcast_in_dim %88, %1684, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1686 = stablehlo.dynamic_broadcast_in_dim %1681, %1684, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1687 = stablehlo.add %1685, %1686 : tensor<1x?x1x30xf32>
    %1688 = stablehlo.reduce(%1687 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_614 = tensor.dim %1688, %c1 : tensor<1x?x1xf32>
    %from_elements_615 = tensor.from_elements %c1, %dim_614, %c1, %c1 : tensor<4xindex>
    %dim_616 = tensor.dim %1688, %c1 : tensor<1x?x1xf32>
    %expanded_617 = tensor.expand_shape %1688 [[0], [1], [2, 3]] output_shape [1, %dim_616, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1689 = shape.shape_of %1687 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1690 = shape.broadcast %1689, %from_elements_615 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1691 = stablehlo.dynamic_broadcast_in_dim %1687, %1690, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1692 = stablehlo.dynamic_broadcast_in_dim %expanded_617, %1690, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1693 = stablehlo.subtract %1691, %1692 : tensor<1x?x1x30xf32>
    %1694 = stablehlo.exponential %1693 : tensor<1x?x1x30xf32>
    %1695 = stablehlo.reduce(%1694 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_618 = tensor.dim %1695, %c1 : tensor<1x?x1xf32>
    %from_elements_619 = tensor.from_elements %c1, %dim_618, %c1, %c1 : tensor<4xindex>
    %dim_620 = tensor.dim %1695, %c1 : tensor<1x?x1xf32>
    %expanded_621 = tensor.expand_shape %1695 [[0], [1], [2, 3]] output_shape [1, %dim_620, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1696 = shape.shape_of %1694 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1697 = shape.broadcast %1696, %from_elements_619 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1698 = stablehlo.dynamic_broadcast_in_dim %1694, %1697, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1699 = stablehlo.dynamic_broadcast_in_dim %expanded_621, %1697, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1700 = stablehlo.divide %1698, %1699 : tensor<1x?x1x30xf32>
    %dim_622 = tensor.dim %arg261, %c0 : tensor<?x30x32xf32>
    %from_elements_623 = tensor.from_elements %c1, %dim_622, %c30, %c32_32 : tensor<4xindex>
    %dim_624 = tensor.dim %arg261, %c0 : tensor<?x30x32xf32>
    %expanded_625 = tensor.expand_shape %arg261 [[0, 1], [2], [3]] output_shape [1, %dim_624, 30, 32] : tensor<?x30x32xf32> into tensor<1x?x30x32xf32>
    %1701 = shape.shape_of %1700 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_626, %tail_627 = "shape.split_at"(%1701, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_628, %tail_629 = "shape.split_at"(%from_elements_623, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1702 = shape.broadcast %head_626, %head_628 : !shape.shape, !shape.shape -> !shape.shape
    %1703 = shape.concat %1702, %tail_627 : !shape.shape, !shape.shape -> !shape.shape
    %1704 = shape.to_extent_tensor %1703 : !shape.shape -> tensor<4xindex>
    %1705 = stablehlo.dynamic_broadcast_in_dim %1700, %1704, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1706 = shape.concat %1702, %tail_629 : !shape.shape, !shape.shape -> !shape.shape
    %1707 = shape.to_extent_tensor %1706 : !shape.shape -> tensor<4xindex>
    %1708 = stablehlo.dynamic_broadcast_in_dim %expanded_625, %1707, dims = [0, 1, 2, 3] : (tensor<1x?x30x32xf32>, tensor<4xindex>) -> tensor<1x?x30x32xf32>
    %1709 = stablehlo.dot_general %1705, %1708, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x32xf32>) -> tensor<1x?x1x32xf32>
    %1710 = stablehlo.transpose %1709, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_630 = tensor.collapse_shape %1710 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_631 = tensor.dim %arg262, %c0 : tensor<?x30x16xf32>
    %from_elements_632 = tensor.from_elements %c1, %dim_631, %c30, %c16 : tensor<4xindex>
    %dim_633 = tensor.dim %arg262, %c0 : tensor<?x30x16xf32>
    %expanded_634 = tensor.expand_shape %arg262 [[0, 1], [2], [3]] output_shape [1, %dim_633, 30, 16] : tensor<?x30x16xf32> into tensor<1x?x30x16xf32>
    %dim_635 = tensor.dim %arg263, %c0 : tensor<?x1x16xf32>
    %from_elements_636 = tensor.from_elements %c1, %dim_635, %c1, %c16 : tensor<4xindex>
    %dim_637 = tensor.dim %arg263, %c0 : tensor<?x1x16xf32>
    %expanded_638 = tensor.expand_shape %arg263 [[0, 1], [2], [3]] output_shape [1, %dim_637, 1, 16] : tensor<?x1x16xf32> into tensor<1x?x1x16xf32>
    %head_639, %tail_640 = "shape.split_at"(%from_elements_636, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_641, %tail_642 = "shape.split_at"(%from_elements_632, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1711 = shape.broadcast %head_639, %head_641 : !shape.shape, !shape.shape -> !shape.shape
    %1712 = shape.concat %1711, %tail_640 : !shape.shape, !shape.shape -> !shape.shape
    %1713 = shape.to_extent_tensor %1712 : !shape.shape -> tensor<4xindex>
    %1714 = stablehlo.dynamic_broadcast_in_dim %expanded_638, %1713, dims = [0, 1, 2, 3] : (tensor<1x?x1x16xf32>, tensor<4xindex>) -> tensor<1x?x1x16xf32>
    %1715 = shape.concat %1711, %tail_642 : !shape.shape, !shape.shape -> !shape.shape
    %1716 = shape.to_extent_tensor %1715 : !shape.shape -> tensor<4xindex>
    %1717 = stablehlo.dynamic_broadcast_in_dim %expanded_634, %1716, dims = [0, 1, 2, 3] : (tensor<1x?x30x16xf32>, tensor<4xindex>) -> tensor<1x?x30x16xf32>
    %1718 = stablehlo.dot_general %1714, %1717, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x16xf32>, tensor<1x?x30x16xf32>) -> tensor<1x?x1x30xf32>
    %1719 = shape.shape_of %1718 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1720 = stablehlo.dynamic_broadcast_in_dim %cst_4, %1719, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1721 = stablehlo.multiply %1718, %1720 : tensor<1x?x1x30xf32>
    %1722 = shape.shape_of %1721 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1723 = shape.broadcast %1682, %1722 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1724 = stablehlo.dynamic_broadcast_in_dim %88, %1723, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1725 = stablehlo.dynamic_broadcast_in_dim %1721, %1723, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1726 = stablehlo.add %1724, %1725 : tensor<1x?x1x30xf32>
    %1727 = stablehlo.reduce(%1726 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_643 = tensor.dim %1727, %c1 : tensor<1x?x1xf32>
    %from_elements_644 = tensor.from_elements %c1, %dim_643, %c1, %c1 : tensor<4xindex>
    %dim_645 = tensor.dim %1727, %c1 : tensor<1x?x1xf32>
    %expanded_646 = tensor.expand_shape %1727 [[0], [1], [2, 3]] output_shape [1, %dim_645, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1728 = shape.shape_of %1726 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1729 = shape.broadcast %1728, %from_elements_644 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1730 = stablehlo.dynamic_broadcast_in_dim %1726, %1729, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1731 = stablehlo.dynamic_broadcast_in_dim %expanded_646, %1729, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1732 = stablehlo.subtract %1730, %1731 : tensor<1x?x1x30xf32>
    %1733 = stablehlo.exponential %1732 : tensor<1x?x1x30xf32>
    %1734 = stablehlo.reduce(%1733 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_647 = tensor.dim %1734, %c1 : tensor<1x?x1xf32>
    %from_elements_648 = tensor.from_elements %c1, %dim_647, %c1, %c1 : tensor<4xindex>
    %dim_649 = tensor.dim %1734, %c1 : tensor<1x?x1xf32>
    %expanded_650 = tensor.expand_shape %1734 [[0], [1], [2, 3]] output_shape [1, %dim_649, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1735 = shape.shape_of %1733 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1736 = shape.broadcast %1735, %from_elements_648 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1737 = stablehlo.dynamic_broadcast_in_dim %1733, %1736, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1738 = stablehlo.dynamic_broadcast_in_dim %expanded_650, %1736, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1739 = stablehlo.divide %1737, %1738 : tensor<1x?x1x30xf32>
    %dim_651 = tensor.dim %arg264, %c0 : tensor<?x30x16xf32>
    %from_elements_652 = tensor.from_elements %c1, %dim_651, %c30, %c16 : tensor<4xindex>
    %dim_653 = tensor.dim %arg264, %c0 : tensor<?x30x16xf32>
    %expanded_654 = tensor.expand_shape %arg264 [[0, 1], [2], [3]] output_shape [1, %dim_653, 30, 16] : tensor<?x30x16xf32> into tensor<1x?x30x16xf32>
    %1740 = shape.shape_of %1739 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_655, %tail_656 = "shape.split_at"(%1740, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_657, %tail_658 = "shape.split_at"(%from_elements_652, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1741 = shape.broadcast %head_655, %head_657 : !shape.shape, !shape.shape -> !shape.shape
    %1742 = shape.concat %1741, %tail_656 : !shape.shape, !shape.shape -> !shape.shape
    %1743 = shape.to_extent_tensor %1742 : !shape.shape -> tensor<4xindex>
    %1744 = stablehlo.dynamic_broadcast_in_dim %1739, %1743, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1745 = shape.concat %1741, %tail_658 : !shape.shape, !shape.shape -> !shape.shape
    %1746 = shape.to_extent_tensor %1745 : !shape.shape -> tensor<4xindex>
    %1747 = stablehlo.dynamic_broadcast_in_dim %expanded_654, %1746, dims = [0, 1, 2, 3] : (tensor<1x?x30x16xf32>, tensor<4xindex>) -> tensor<1x?x30x16xf32>
    %1748 = stablehlo.dot_general %1744, %1747, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x16xf32>) -> tensor<1x?x1x16xf32>
    %1749 = stablehlo.transpose %1748, dims = [1, 2, 0, 3] : (tensor<1x?x1x16xf32>) -> tensor<?x1x1x16xf32>
    %collapsed_659 = tensor.collapse_shape %1749 [[0], [1, 2, 3]] : tensor<?x1x1x16xf32> into tensor<?x16xf32>
    %dim_660 = tensor.dim %arg265, %c0 : tensor<?x30x8xf32>
    %from_elements_661 = tensor.from_elements %c1, %dim_660, %c30, %c8 : tensor<4xindex>
    %dim_662 = tensor.dim %arg265, %c0 : tensor<?x30x8xf32>
    %expanded_663 = tensor.expand_shape %arg265 [[0, 1], [2], [3]] output_shape [1, %dim_662, 30, 8] : tensor<?x30x8xf32> into tensor<1x?x30x8xf32>
    %dim_664 = tensor.dim %arg266, %c0 : tensor<?x1x8xf32>
    %from_elements_665 = tensor.from_elements %c1, %dim_664, %c1, %c8 : tensor<4xindex>
    %dim_666 = tensor.dim %arg266, %c0 : tensor<?x1x8xf32>
    %expanded_667 = tensor.expand_shape %arg266 [[0, 1], [2], [3]] output_shape [1, %dim_666, 1, 8] : tensor<?x1x8xf32> into tensor<1x?x1x8xf32>
    %head_668, %tail_669 = "shape.split_at"(%from_elements_665, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_670, %tail_671 = "shape.split_at"(%from_elements_661, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1750 = shape.broadcast %head_668, %head_670 : !shape.shape, !shape.shape -> !shape.shape
    %1751 = shape.concat %1750, %tail_669 : !shape.shape, !shape.shape -> !shape.shape
    %1752 = shape.to_extent_tensor %1751 : !shape.shape -> tensor<4xindex>
    %1753 = stablehlo.dynamic_broadcast_in_dim %expanded_667, %1752, dims = [0, 1, 2, 3] : (tensor<1x?x1x8xf32>, tensor<4xindex>) -> tensor<1x?x1x8xf32>
    %1754 = shape.concat %1750, %tail_671 : !shape.shape, !shape.shape -> !shape.shape
    %1755 = shape.to_extent_tensor %1754 : !shape.shape -> tensor<4xindex>
    %1756 = stablehlo.dynamic_broadcast_in_dim %expanded_663, %1755, dims = [0, 1, 2, 3] : (tensor<1x?x30x8xf32>, tensor<4xindex>) -> tensor<1x?x30x8xf32>
    %1757 = stablehlo.dot_general %1753, %1756, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x8xf32>, tensor<1x?x30x8xf32>) -> tensor<1x?x1x30xf32>
    %1758 = shape.shape_of %1757 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1759 = stablehlo.dynamic_broadcast_in_dim %cst_2, %1758, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1760 = stablehlo.multiply %1757, %1759 : tensor<1x?x1x30xf32>
    %1761 = shape.shape_of %1760 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1762 = shape.broadcast %1682, %1761 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1763 = stablehlo.dynamic_broadcast_in_dim %88, %1762, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1764 = stablehlo.dynamic_broadcast_in_dim %1760, %1762, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1765 = stablehlo.add %1763, %1764 : tensor<1x?x1x30xf32>
    %1766 = stablehlo.reduce(%1765 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_672 = tensor.dim %1766, %c1 : tensor<1x?x1xf32>
    %from_elements_673 = tensor.from_elements %c1, %dim_672, %c1, %c1 : tensor<4xindex>
    %dim_674 = tensor.dim %1766, %c1 : tensor<1x?x1xf32>
    %expanded_675 = tensor.expand_shape %1766 [[0], [1], [2, 3]] output_shape [1, %dim_674, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1767 = shape.shape_of %1765 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1768 = shape.broadcast %1767, %from_elements_673 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1769 = stablehlo.dynamic_broadcast_in_dim %1765, %1768, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1770 = stablehlo.dynamic_broadcast_in_dim %expanded_675, %1768, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1771 = stablehlo.subtract %1769, %1770 : tensor<1x?x1x30xf32>
    %1772 = stablehlo.exponential %1771 : tensor<1x?x1x30xf32>
    %1773 = stablehlo.reduce(%1772 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_676 = tensor.dim %1773, %c1 : tensor<1x?x1xf32>
    %from_elements_677 = tensor.from_elements %c1, %dim_676, %c1, %c1 : tensor<4xindex>
    %dim_678 = tensor.dim %1773, %c1 : tensor<1x?x1xf32>
    %expanded_679 = tensor.expand_shape %1773 [[0], [1], [2, 3]] output_shape [1, %dim_678, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1774 = shape.shape_of %1772 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1775 = shape.broadcast %1774, %from_elements_677 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1776 = stablehlo.dynamic_broadcast_in_dim %1772, %1775, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1777 = stablehlo.dynamic_broadcast_in_dim %expanded_679, %1775, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1778 = stablehlo.divide %1776, %1777 : tensor<1x?x1x30xf32>
    %dim_680 = tensor.dim %arg267, %c0 : tensor<?x30x8xf32>
    %from_elements_681 = tensor.from_elements %c1, %dim_680, %c30, %c8 : tensor<4xindex>
    %dim_682 = tensor.dim %arg267, %c0 : tensor<?x30x8xf32>
    %expanded_683 = tensor.expand_shape %arg267 [[0, 1], [2], [3]] output_shape [1, %dim_682, 30, 8] : tensor<?x30x8xf32> into tensor<1x?x30x8xf32>
    %1779 = shape.shape_of %1778 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_684, %tail_685 = "shape.split_at"(%1779, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_686, %tail_687 = "shape.split_at"(%from_elements_681, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1780 = shape.broadcast %head_684, %head_686 : !shape.shape, !shape.shape -> !shape.shape
    %1781 = shape.concat %1780, %tail_685 : !shape.shape, !shape.shape -> !shape.shape
    %1782 = shape.to_extent_tensor %1781 : !shape.shape -> tensor<4xindex>
    %1783 = stablehlo.dynamic_broadcast_in_dim %1778, %1782, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1784 = shape.concat %1780, %tail_687 : !shape.shape, !shape.shape -> !shape.shape
    %1785 = shape.to_extent_tensor %1784 : !shape.shape -> tensor<4xindex>
    %1786 = stablehlo.dynamic_broadcast_in_dim %expanded_683, %1785, dims = [0, 1, 2, 3] : (tensor<1x?x30x8xf32>, tensor<4xindex>) -> tensor<1x?x30x8xf32>
    %1787 = stablehlo.dot_general %1783, %1786, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x8xf32>) -> tensor<1x?x1x8xf32>
    %1788 = stablehlo.transpose %1787, dims = [1, 2, 0, 3] : (tensor<1x?x1x8xf32>) -> tensor<?x1x1x8xf32>
    %collapsed_688 = tensor.collapse_shape %1788 [[0], [1, 2, 3]] : tensor<?x1x1x8xf32> into tensor<?x8xf32>
    %dim_689 = tensor.dim %arg268, %c0 : tensor<?x30x64xf32>
    %from_elements_690 = tensor.from_elements %c1, %dim_689, %c30, %c64_33 : tensor<4xindex>
    %dim_691 = tensor.dim %arg268, %c0 : tensor<?x30x64xf32>
    %expanded_692 = tensor.expand_shape %arg268 [[0, 1], [2], [3]] output_shape [1, %dim_691, 30, 64] : tensor<?x30x64xf32> into tensor<1x?x30x64xf32>
    %dim_693 = tensor.dim %arg269, %c0 : tensor<?x1x64xf32>
    %from_elements_694 = tensor.from_elements %c1, %dim_693, %c1, %c64_33 : tensor<4xindex>
    %dim_695 = tensor.dim %arg269, %c0 : tensor<?x1x64xf32>
    %expanded_696 = tensor.expand_shape %arg269 [[0, 1], [2], [3]] output_shape [1, %dim_695, 1, 64] : tensor<?x1x64xf32> into tensor<1x?x1x64xf32>
    %head_697, %tail_698 = "shape.split_at"(%from_elements_694, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_699, %tail_700 = "shape.split_at"(%from_elements_690, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1789 = shape.broadcast %head_697, %head_699 : !shape.shape, !shape.shape -> !shape.shape
    %1790 = shape.concat %1789, %tail_698 : !shape.shape, !shape.shape -> !shape.shape
    %1791 = shape.to_extent_tensor %1790 : !shape.shape -> tensor<4xindex>
    %1792 = stablehlo.dynamic_broadcast_in_dim %expanded_696, %1791, dims = [0, 1, 2, 3] : (tensor<1x?x1x64xf32>, tensor<4xindex>) -> tensor<1x?x1x64xf32>
    %1793 = shape.concat %1789, %tail_700 : !shape.shape, !shape.shape -> !shape.shape
    %1794 = shape.to_extent_tensor %1793 : !shape.shape -> tensor<4xindex>
    %1795 = stablehlo.dynamic_broadcast_in_dim %expanded_692, %1794, dims = [0, 1, 2, 3] : (tensor<1x?x30x64xf32>, tensor<4xindex>) -> tensor<1x?x30x64xf32>
    %1796 = stablehlo.dot_general %1792, %1795, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x64xf32>, tensor<1x?x30x64xf32>) -> tensor<1x?x1x30xf32>
    %1797 = shape.shape_of %1796 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1798 = stablehlo.dynamic_broadcast_in_dim %cst_6, %1797, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1799 = stablehlo.multiply %1796, %1798 : tensor<1x?x1x30xf32>
    %1800 = shape.shape_of %1799 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1801 = shape.broadcast %1682, %1800 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1802 = stablehlo.dynamic_broadcast_in_dim %88, %1801, dims = [1, 2, 3] : (tensor<?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1803 = stablehlo.dynamic_broadcast_in_dim %1799, %1801, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1804 = stablehlo.add %1802, %1803 : tensor<1x?x1x30xf32>
    %1805 = stablehlo.reduce(%1804 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_701 = tensor.dim %1805, %c1 : tensor<1x?x1xf32>
    %from_elements_702 = tensor.from_elements %c1, %dim_701, %c1, %c1 : tensor<4xindex>
    %dim_703 = tensor.dim %1805, %c1 : tensor<1x?x1xf32>
    %expanded_704 = tensor.expand_shape %1805 [[0], [1], [2, 3]] output_shape [1, %dim_703, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1806 = shape.shape_of %1804 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1807 = shape.broadcast %1806, %from_elements_702 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1808 = stablehlo.dynamic_broadcast_in_dim %1804, %1807, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1809 = stablehlo.dynamic_broadcast_in_dim %expanded_704, %1807, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1810 = stablehlo.subtract %1808, %1809 : tensor<1x?x1x30xf32>
    %1811 = stablehlo.exponential %1810 : tensor<1x?x1x30xf32>
    %1812 = stablehlo.reduce(%1811 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x30xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_705 = tensor.dim %1812, %c1 : tensor<1x?x1xf32>
    %from_elements_706 = tensor.from_elements %c1, %dim_705, %c1, %c1 : tensor<4xindex>
    %dim_707 = tensor.dim %1812, %c1 : tensor<1x?x1xf32>
    %expanded_708 = tensor.expand_shape %1812 [[0], [1], [2, 3]] output_shape [1, %dim_707, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1813 = shape.shape_of %1811 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %1814 = shape.broadcast %1813, %from_elements_706 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1815 = stablehlo.dynamic_broadcast_in_dim %1811, %1814, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1816 = stablehlo.dynamic_broadcast_in_dim %expanded_708, %1814, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1817 = stablehlo.divide %1815, %1816 : tensor<1x?x1x30xf32>
    %dim_709 = tensor.dim %arg270, %c0 : tensor<?x30x64xf32>
    %from_elements_710 = tensor.from_elements %c1, %dim_709, %c30, %c64_33 : tensor<4xindex>
    %dim_711 = tensor.dim %arg270, %c0 : tensor<?x30x64xf32>
    %expanded_712 = tensor.expand_shape %arg270 [[0, 1], [2], [3]] output_shape [1, %dim_711, 30, 64] : tensor<?x30x64xf32> into tensor<1x?x30x64xf32>
    %1818 = shape.shape_of %1817 : tensor<1x?x1x30xf32> -> tensor<4xindex>
    %head_713, %tail_714 = "shape.split_at"(%1818, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_715, %tail_716 = "shape.split_at"(%from_elements_710, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1819 = shape.broadcast %head_713, %head_715 : !shape.shape, !shape.shape -> !shape.shape
    %1820 = shape.concat %1819, %tail_714 : !shape.shape, !shape.shape -> !shape.shape
    %1821 = shape.to_extent_tensor %1820 : !shape.shape -> tensor<4xindex>
    %1822 = stablehlo.dynamic_broadcast_in_dim %1817, %1821, dims = [0, 1, 2, 3] : (tensor<1x?x1x30xf32>, tensor<4xindex>) -> tensor<1x?x1x30xf32>
    %1823 = shape.concat %1819, %tail_716 : !shape.shape, !shape.shape -> !shape.shape
    %1824 = shape.to_extent_tensor %1823 : !shape.shape -> tensor<4xindex>
    %1825 = stablehlo.dynamic_broadcast_in_dim %expanded_712, %1824, dims = [0, 1, 2, 3] : (tensor<1x?x30x64xf32>, tensor<4xindex>) -> tensor<1x?x30x64xf32>
    %1826 = stablehlo.dot_general %1822, %1825, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x30xf32>, tensor<1x?x30x64xf32>) -> tensor<1x?x1x64xf32>
    %1827 = stablehlo.transpose %1826, dims = [1, 2, 0, 3] : (tensor<1x?x1x64xf32>) -> tensor<?x1x1x64xf32>
    %collapsed_717 = tensor.collapse_shape %1827 [[0], [1, 2, 3]] : tensor<?x1x1x64xf32> into tensor<?x64xf32>
    %dim_718 = tensor.dim %arg271, %c0 : tensor<?x50x32xf32>
    %from_elements_719 = tensor.from_elements %c1, %dim_718, %c50, %c32_32 : tensor<4xindex>
    %dim_720 = tensor.dim %arg271, %c0 : tensor<?x50x32xf32>
    %expanded_721 = tensor.expand_shape %arg271 [[0, 1], [2], [3]] output_shape [1, %dim_720, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %dim_722 = tensor.dim %arg272, %c0 : tensor<?x1x32xf32>
    %from_elements_723 = tensor.from_elements %c1, %dim_722, %c1, %c32_32 : tensor<4xindex>
    %dim_724 = tensor.dim %arg272, %c0 : tensor<?x1x32xf32>
    %expanded_725 = tensor.expand_shape %arg272 [[0, 1], [2], [3]] output_shape [1, %dim_724, 1, 32] : tensor<?x1x32xf32> into tensor<1x?x1x32xf32>
    %head_726, %tail_727 = "shape.split_at"(%from_elements_723, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_728, %tail_729 = "shape.split_at"(%from_elements_719, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1828 = shape.broadcast %head_726, %head_728 : !shape.shape, !shape.shape -> !shape.shape
    %1829 = shape.concat %1828, %tail_727 : !shape.shape, !shape.shape -> !shape.shape
    %1830 = shape.to_extent_tensor %1829 : !shape.shape -> tensor<4xindex>
    %1831 = stablehlo.dynamic_broadcast_in_dim %expanded_725, %1830, dims = [0, 1, 2, 3] : (tensor<1x?x1x32xf32>, tensor<4xindex>) -> tensor<1x?x1x32xf32>
    %1832 = shape.concat %1828, %tail_729 : !shape.shape, !shape.shape -> !shape.shape
    %1833 = shape.to_extent_tensor %1832 : !shape.shape -> tensor<4xindex>
    %1834 = stablehlo.dynamic_broadcast_in_dim %expanded_721, %1833, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %1835 = stablehlo.dot_general %1831, %1834, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x32xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x50xf32>
    %1836 = shape.shape_of %1835 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1837 = stablehlo.dynamic_broadcast_in_dim %cst, %1836, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1838 = stablehlo.multiply %1835, %1837 : tensor<1x?x1x50xf32>
    %1839 = shape.shape_of %85 : tensor<?x1x50xf32> -> tensor<3xindex>
    %1840 = shape.shape_of %1838 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1841 = shape.broadcast %1839, %1840 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1842 = stablehlo.dynamic_broadcast_in_dim %85, %1841, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1843 = stablehlo.dynamic_broadcast_in_dim %1838, %1841, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1844 = stablehlo.add %1842, %1843 : tensor<1x?x1x50xf32>
    %1845 = stablehlo.reduce(%1844 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_730 = tensor.dim %1845, %c1 : tensor<1x?x1xf32>
    %from_elements_731 = tensor.from_elements %c1, %dim_730, %c1, %c1 : tensor<4xindex>
    %dim_732 = tensor.dim %1845, %c1 : tensor<1x?x1xf32>
    %expanded_733 = tensor.expand_shape %1845 [[0], [1], [2, 3]] output_shape [1, %dim_732, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1846 = shape.shape_of %1844 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1847 = shape.broadcast %1846, %from_elements_731 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1848 = stablehlo.dynamic_broadcast_in_dim %1844, %1847, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1849 = stablehlo.dynamic_broadcast_in_dim %expanded_733, %1847, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1850 = stablehlo.subtract %1848, %1849 : tensor<1x?x1x50xf32>
    %1851 = stablehlo.exponential %1850 : tensor<1x?x1x50xf32>
    %1852 = stablehlo.reduce(%1851 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_734 = tensor.dim %1852, %c1 : tensor<1x?x1xf32>
    %from_elements_735 = tensor.from_elements %c1, %dim_734, %c1, %c1 : tensor<4xindex>
    %dim_736 = tensor.dim %1852, %c1 : tensor<1x?x1xf32>
    %expanded_737 = tensor.expand_shape %1852 [[0], [1], [2, 3]] output_shape [1, %dim_736, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1853 = shape.shape_of %1851 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1854 = shape.broadcast %1853, %from_elements_735 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1855 = stablehlo.dynamic_broadcast_in_dim %1851, %1854, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1856 = stablehlo.dynamic_broadcast_in_dim %expanded_737, %1854, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1857 = stablehlo.divide %1855, %1856 : tensor<1x?x1x50xf32>
    %dim_738 = tensor.dim %arg273, %c0 : tensor<?x50x32xf32>
    %from_elements_739 = tensor.from_elements %c1, %dim_738, %c50, %c32_32 : tensor<4xindex>
    %dim_740 = tensor.dim %arg273, %c0 : tensor<?x50x32xf32>
    %expanded_741 = tensor.expand_shape %arg273 [[0, 1], [2], [3]] output_shape [1, %dim_740, 50, 32] : tensor<?x50x32xf32> into tensor<1x?x50x32xf32>
    %1858 = shape.shape_of %1857 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_742, %tail_743 = "shape.split_at"(%1858, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_744, %tail_745 = "shape.split_at"(%from_elements_739, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1859 = shape.broadcast %head_742, %head_744 : !shape.shape, !shape.shape -> !shape.shape
    %1860 = shape.concat %1859, %tail_743 : !shape.shape, !shape.shape -> !shape.shape
    %1861 = shape.to_extent_tensor %1860 : !shape.shape -> tensor<4xindex>
    %1862 = stablehlo.dynamic_broadcast_in_dim %1857, %1861, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1863 = shape.concat %1859, %tail_745 : !shape.shape, !shape.shape -> !shape.shape
    %1864 = shape.to_extent_tensor %1863 : !shape.shape -> tensor<4xindex>
    %1865 = stablehlo.dynamic_broadcast_in_dim %expanded_741, %1864, dims = [0, 1, 2, 3] : (tensor<1x?x50x32xf32>, tensor<4xindex>) -> tensor<1x?x50x32xf32>
    %1866 = stablehlo.dot_general %1862, %1865, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x32xf32>) -> tensor<1x?x1x32xf32>
    %1867 = stablehlo.transpose %1866, dims = [1, 2, 0, 3] : (tensor<1x?x1x32xf32>) -> tensor<?x1x1x32xf32>
    %collapsed_746 = tensor.collapse_shape %1867 [[0], [1, 2, 3]] : tensor<?x1x1x32xf32> into tensor<?x32xf32>
    %dim_747 = tensor.dim %arg274, %c0 : tensor<?x50x16xf32>
    %from_elements_748 = tensor.from_elements %c1, %dim_747, %c50, %c16 : tensor<4xindex>
    %dim_749 = tensor.dim %arg274, %c0 : tensor<?x50x16xf32>
    %expanded_750 = tensor.expand_shape %arg274 [[0, 1], [2], [3]] output_shape [1, %dim_749, 50, 16] : tensor<?x50x16xf32> into tensor<1x?x50x16xf32>
    %dim_751 = tensor.dim %arg275, %c0 : tensor<?x1x16xf32>
    %from_elements_752 = tensor.from_elements %c1, %dim_751, %c1, %c16 : tensor<4xindex>
    %dim_753 = tensor.dim %arg275, %c0 : tensor<?x1x16xf32>
    %expanded_754 = tensor.expand_shape %arg275 [[0, 1], [2], [3]] output_shape [1, %dim_753, 1, 16] : tensor<?x1x16xf32> into tensor<1x?x1x16xf32>
    %head_755, %tail_756 = "shape.split_at"(%from_elements_752, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_757, %tail_758 = "shape.split_at"(%from_elements_748, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1868 = shape.broadcast %head_755, %head_757 : !shape.shape, !shape.shape -> !shape.shape
    %1869 = shape.concat %1868, %tail_756 : !shape.shape, !shape.shape -> !shape.shape
    %1870 = shape.to_extent_tensor %1869 : !shape.shape -> tensor<4xindex>
    %1871 = stablehlo.dynamic_broadcast_in_dim %expanded_754, %1870, dims = [0, 1, 2, 3] : (tensor<1x?x1x16xf32>, tensor<4xindex>) -> tensor<1x?x1x16xf32>
    %1872 = shape.concat %1868, %tail_758 : !shape.shape, !shape.shape -> !shape.shape
    %1873 = shape.to_extent_tensor %1872 : !shape.shape -> tensor<4xindex>
    %1874 = stablehlo.dynamic_broadcast_in_dim %expanded_750, %1873, dims = [0, 1, 2, 3] : (tensor<1x?x50x16xf32>, tensor<4xindex>) -> tensor<1x?x50x16xf32>
    %1875 = stablehlo.dot_general %1871, %1874, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x16xf32>, tensor<1x?x50x16xf32>) -> tensor<1x?x1x50xf32>
    %1876 = shape.shape_of %1875 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1877 = stablehlo.dynamic_broadcast_in_dim %cst_4, %1876, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1878 = stablehlo.multiply %1875, %1877 : tensor<1x?x1x50xf32>
    %1879 = shape.shape_of %1878 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1880 = shape.broadcast %1839, %1879 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1881 = stablehlo.dynamic_broadcast_in_dim %85, %1880, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1882 = stablehlo.dynamic_broadcast_in_dim %1878, %1880, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1883 = stablehlo.add %1881, %1882 : tensor<1x?x1x50xf32>
    %1884 = stablehlo.reduce(%1883 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_759 = tensor.dim %1884, %c1 : tensor<1x?x1xf32>
    %from_elements_760 = tensor.from_elements %c1, %dim_759, %c1, %c1 : tensor<4xindex>
    %dim_761 = tensor.dim %1884, %c1 : tensor<1x?x1xf32>
    %expanded_762 = tensor.expand_shape %1884 [[0], [1], [2, 3]] output_shape [1, %dim_761, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1885 = shape.shape_of %1883 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1886 = shape.broadcast %1885, %from_elements_760 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1887 = stablehlo.dynamic_broadcast_in_dim %1883, %1886, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1888 = stablehlo.dynamic_broadcast_in_dim %expanded_762, %1886, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1889 = stablehlo.subtract %1887, %1888 : tensor<1x?x1x50xf32>
    %1890 = stablehlo.exponential %1889 : tensor<1x?x1x50xf32>
    %1891 = stablehlo.reduce(%1890 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_763 = tensor.dim %1891, %c1 : tensor<1x?x1xf32>
    %from_elements_764 = tensor.from_elements %c1, %dim_763, %c1, %c1 : tensor<4xindex>
    %dim_765 = tensor.dim %1891, %c1 : tensor<1x?x1xf32>
    %expanded_766 = tensor.expand_shape %1891 [[0], [1], [2, 3]] output_shape [1, %dim_765, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1892 = shape.shape_of %1890 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1893 = shape.broadcast %1892, %from_elements_764 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1894 = stablehlo.dynamic_broadcast_in_dim %1890, %1893, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1895 = stablehlo.dynamic_broadcast_in_dim %expanded_766, %1893, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1896 = stablehlo.divide %1894, %1895 : tensor<1x?x1x50xf32>
    %dim_767 = tensor.dim %arg276, %c0 : tensor<?x50x16xf32>
    %from_elements_768 = tensor.from_elements %c1, %dim_767, %c50, %c16 : tensor<4xindex>
    %dim_769 = tensor.dim %arg276, %c0 : tensor<?x50x16xf32>
    %expanded_770 = tensor.expand_shape %arg276 [[0, 1], [2], [3]] output_shape [1, %dim_769, 50, 16] : tensor<?x50x16xf32> into tensor<1x?x50x16xf32>
    %1897 = shape.shape_of %1896 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_771, %tail_772 = "shape.split_at"(%1897, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_773, %tail_774 = "shape.split_at"(%from_elements_768, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1898 = shape.broadcast %head_771, %head_773 : !shape.shape, !shape.shape -> !shape.shape
    %1899 = shape.concat %1898, %tail_772 : !shape.shape, !shape.shape -> !shape.shape
    %1900 = shape.to_extent_tensor %1899 : !shape.shape -> tensor<4xindex>
    %1901 = stablehlo.dynamic_broadcast_in_dim %1896, %1900, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1902 = shape.concat %1898, %tail_774 : !shape.shape, !shape.shape -> !shape.shape
    %1903 = shape.to_extent_tensor %1902 : !shape.shape -> tensor<4xindex>
    %1904 = stablehlo.dynamic_broadcast_in_dim %expanded_770, %1903, dims = [0, 1, 2, 3] : (tensor<1x?x50x16xf32>, tensor<4xindex>) -> tensor<1x?x50x16xf32>
    %1905 = stablehlo.dot_general %1901, %1904, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x16xf32>) -> tensor<1x?x1x16xf32>
    %1906 = stablehlo.transpose %1905, dims = [1, 2, 0, 3] : (tensor<1x?x1x16xf32>) -> tensor<?x1x1x16xf32>
    %collapsed_775 = tensor.collapse_shape %1906 [[0], [1, 2, 3]] : tensor<?x1x1x16xf32> into tensor<?x16xf32>
    %dim_776 = tensor.dim %arg277, %c0 : tensor<?x50x8xf32>
    %from_elements_777 = tensor.from_elements %c1, %dim_776, %c50, %c8 : tensor<4xindex>
    %dim_778 = tensor.dim %arg277, %c0 : tensor<?x50x8xf32>
    %expanded_779 = tensor.expand_shape %arg277 [[0, 1], [2], [3]] output_shape [1, %dim_778, 50, 8] : tensor<?x50x8xf32> into tensor<1x?x50x8xf32>
    %dim_780 = tensor.dim %arg278, %c0 : tensor<?x1x8xf32>
    %from_elements_781 = tensor.from_elements %c1, %dim_780, %c1, %c8 : tensor<4xindex>
    %dim_782 = tensor.dim %arg278, %c0 : tensor<?x1x8xf32>
    %expanded_783 = tensor.expand_shape %arg278 [[0, 1], [2], [3]] output_shape [1, %dim_782, 1, 8] : tensor<?x1x8xf32> into tensor<1x?x1x8xf32>
    %head_784, %tail_785 = "shape.split_at"(%from_elements_781, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_786, %tail_787 = "shape.split_at"(%from_elements_777, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1907 = shape.broadcast %head_784, %head_786 : !shape.shape, !shape.shape -> !shape.shape
    %1908 = shape.concat %1907, %tail_785 : !shape.shape, !shape.shape -> !shape.shape
    %1909 = shape.to_extent_tensor %1908 : !shape.shape -> tensor<4xindex>
    %1910 = stablehlo.dynamic_broadcast_in_dim %expanded_783, %1909, dims = [0, 1, 2, 3] : (tensor<1x?x1x8xf32>, tensor<4xindex>) -> tensor<1x?x1x8xf32>
    %1911 = shape.concat %1907, %tail_787 : !shape.shape, !shape.shape -> !shape.shape
    %1912 = shape.to_extent_tensor %1911 : !shape.shape -> tensor<4xindex>
    %1913 = stablehlo.dynamic_broadcast_in_dim %expanded_779, %1912, dims = [0, 1, 2, 3] : (tensor<1x?x50x8xf32>, tensor<4xindex>) -> tensor<1x?x50x8xf32>
    %1914 = stablehlo.dot_general %1910, %1913, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x8xf32>, tensor<1x?x50x8xf32>) -> tensor<1x?x1x50xf32>
    %1915 = shape.shape_of %1914 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1916 = stablehlo.dynamic_broadcast_in_dim %cst_2, %1915, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1917 = stablehlo.multiply %1914, %1916 : tensor<1x?x1x50xf32>
    %1918 = shape.shape_of %1917 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1919 = shape.broadcast %1839, %1918 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1920 = stablehlo.dynamic_broadcast_in_dim %85, %1919, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1921 = stablehlo.dynamic_broadcast_in_dim %1917, %1919, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1922 = stablehlo.add %1920, %1921 : tensor<1x?x1x50xf32>
    %1923 = stablehlo.reduce(%1922 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_788 = tensor.dim %1923, %c1 : tensor<1x?x1xf32>
    %from_elements_789 = tensor.from_elements %c1, %dim_788, %c1, %c1 : tensor<4xindex>
    %dim_790 = tensor.dim %1923, %c1 : tensor<1x?x1xf32>
    %expanded_791 = tensor.expand_shape %1923 [[0], [1], [2, 3]] output_shape [1, %dim_790, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1924 = shape.shape_of %1922 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1925 = shape.broadcast %1924, %from_elements_789 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1926 = stablehlo.dynamic_broadcast_in_dim %1922, %1925, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1927 = stablehlo.dynamic_broadcast_in_dim %expanded_791, %1925, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1928 = stablehlo.subtract %1926, %1927 : tensor<1x?x1x50xf32>
    %1929 = stablehlo.exponential %1928 : tensor<1x?x1x50xf32>
    %1930 = stablehlo.reduce(%1929 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_792 = tensor.dim %1930, %c1 : tensor<1x?x1xf32>
    %from_elements_793 = tensor.from_elements %c1, %dim_792, %c1, %c1 : tensor<4xindex>
    %dim_794 = tensor.dim %1930, %c1 : tensor<1x?x1xf32>
    %expanded_795 = tensor.expand_shape %1930 [[0], [1], [2, 3]] output_shape [1, %dim_794, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1931 = shape.shape_of %1929 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1932 = shape.broadcast %1931, %from_elements_793 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1933 = stablehlo.dynamic_broadcast_in_dim %1929, %1932, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1934 = stablehlo.dynamic_broadcast_in_dim %expanded_795, %1932, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1935 = stablehlo.divide %1933, %1934 : tensor<1x?x1x50xf32>
    %dim_796 = tensor.dim %arg279, %c0 : tensor<?x50x8xf32>
    %from_elements_797 = tensor.from_elements %c1, %dim_796, %c50, %c8 : tensor<4xindex>
    %dim_798 = tensor.dim %arg279, %c0 : tensor<?x50x8xf32>
    %expanded_799 = tensor.expand_shape %arg279 [[0, 1], [2], [3]] output_shape [1, %dim_798, 50, 8] : tensor<?x50x8xf32> into tensor<1x?x50x8xf32>
    %1936 = shape.shape_of %1935 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_800, %tail_801 = "shape.split_at"(%1936, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_802, %tail_803 = "shape.split_at"(%from_elements_797, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1937 = shape.broadcast %head_800, %head_802 : !shape.shape, !shape.shape -> !shape.shape
    %1938 = shape.concat %1937, %tail_801 : !shape.shape, !shape.shape -> !shape.shape
    %1939 = shape.to_extent_tensor %1938 : !shape.shape -> tensor<4xindex>
    %1940 = stablehlo.dynamic_broadcast_in_dim %1935, %1939, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1941 = shape.concat %1937, %tail_803 : !shape.shape, !shape.shape -> !shape.shape
    %1942 = shape.to_extent_tensor %1941 : !shape.shape -> tensor<4xindex>
    %1943 = stablehlo.dynamic_broadcast_in_dim %expanded_799, %1942, dims = [0, 1, 2, 3] : (tensor<1x?x50x8xf32>, tensor<4xindex>) -> tensor<1x?x50x8xf32>
    %1944 = stablehlo.dot_general %1940, %1943, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x8xf32>) -> tensor<1x?x1x8xf32>
    %1945 = stablehlo.transpose %1944, dims = [1, 2, 0, 3] : (tensor<1x?x1x8xf32>) -> tensor<?x1x1x8xf32>
    %collapsed_804 = tensor.collapse_shape %1945 [[0], [1, 2, 3]] : tensor<?x1x1x8xf32> into tensor<?x8xf32>
    %dim_805 = tensor.dim %arg280, %c0 : tensor<?x50x64xf32>
    %from_elements_806 = tensor.from_elements %c1, %dim_805, %c50, %c64_33 : tensor<4xindex>
    %dim_807 = tensor.dim %arg280, %c0 : tensor<?x50x64xf32>
    %expanded_808 = tensor.expand_shape %arg280 [[0, 1], [2], [3]] output_shape [1, %dim_807, 50, 64] : tensor<?x50x64xf32> into tensor<1x?x50x64xf32>
    %dim_809 = tensor.dim %arg281, %c0 : tensor<?x1x64xf32>
    %from_elements_810 = tensor.from_elements %c1, %dim_809, %c1, %c64_33 : tensor<4xindex>
    %dim_811 = tensor.dim %arg281, %c0 : tensor<?x1x64xf32>
    %expanded_812 = tensor.expand_shape %arg281 [[0, 1], [2], [3]] output_shape [1, %dim_811, 1, 64] : tensor<?x1x64xf32> into tensor<1x?x1x64xf32>
    %head_813, %tail_814 = "shape.split_at"(%from_elements_810, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_815, %tail_816 = "shape.split_at"(%from_elements_806, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1946 = shape.broadcast %head_813, %head_815 : !shape.shape, !shape.shape -> !shape.shape
    %1947 = shape.concat %1946, %tail_814 : !shape.shape, !shape.shape -> !shape.shape
    %1948 = shape.to_extent_tensor %1947 : !shape.shape -> tensor<4xindex>
    %1949 = stablehlo.dynamic_broadcast_in_dim %expanded_812, %1948, dims = [0, 1, 2, 3] : (tensor<1x?x1x64xf32>, tensor<4xindex>) -> tensor<1x?x1x64xf32>
    %1950 = shape.concat %1946, %tail_816 : !shape.shape, !shape.shape -> !shape.shape
    %1951 = shape.to_extent_tensor %1950 : !shape.shape -> tensor<4xindex>
    %1952 = stablehlo.dynamic_broadcast_in_dim %expanded_808, %1951, dims = [0, 1, 2, 3] : (tensor<1x?x50x64xf32>, tensor<4xindex>) -> tensor<1x?x50x64xf32>
    %1953 = stablehlo.dot_general %1949, %1952, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [3], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x64xf32>, tensor<1x?x50x64xf32>) -> tensor<1x?x1x50xf32>
    %1954 = shape.shape_of %1953 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1955 = stablehlo.dynamic_broadcast_in_dim %cst_6, %1954, dims = [] : (tensor<f32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1956 = stablehlo.multiply %1953, %1955 : tensor<1x?x1x50xf32>
    %1957 = shape.shape_of %1956 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1958 = shape.broadcast %1839, %1957 : tensor<3xindex>, tensor<4xindex> -> tensor<4xindex>
    %1959 = stablehlo.dynamic_broadcast_in_dim %85, %1958, dims = [1, 2, 3] : (tensor<?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1960 = stablehlo.dynamic_broadcast_in_dim %1956, %1958, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1961 = stablehlo.add %1959, %1960 : tensor<1x?x1x50xf32>
    %1962 = stablehlo.reduce(%1961 init: %cst_23) applies stablehlo.maximum across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_817 = tensor.dim %1962, %c1 : tensor<1x?x1xf32>
    %from_elements_818 = tensor.from_elements %c1, %dim_817, %c1, %c1 : tensor<4xindex>
    %dim_819 = tensor.dim %1962, %c1 : tensor<1x?x1xf32>
    %expanded_820 = tensor.expand_shape %1962 [[0], [1], [2, 3]] output_shape [1, %dim_819, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1963 = shape.shape_of %1961 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1964 = shape.broadcast %1963, %from_elements_818 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1965 = stablehlo.dynamic_broadcast_in_dim %1961, %1964, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1966 = stablehlo.dynamic_broadcast_in_dim %expanded_820, %1964, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1967 = stablehlo.subtract %1965, %1966 : tensor<1x?x1x50xf32>
    %1968 = stablehlo.exponential %1967 : tensor<1x?x1x50xf32>
    %1969 = stablehlo.reduce(%1968 init: %cst_21) applies stablehlo.add across dimensions = [3] : (tensor<1x?x1x50xf32>, tensor<f32>) -> tensor<1x?x1xf32>
    %dim_821 = tensor.dim %1969, %c1 : tensor<1x?x1xf32>
    %from_elements_822 = tensor.from_elements %c1, %dim_821, %c1, %c1 : tensor<4xindex>
    %dim_823 = tensor.dim %1969, %c1 : tensor<1x?x1xf32>
    %expanded_824 = tensor.expand_shape %1969 [[0], [1], [2, 3]] output_shape [1, %dim_823, 1, 1] : tensor<1x?x1xf32> into tensor<1x?x1x1xf32>
    %1970 = shape.shape_of %1968 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %1971 = shape.broadcast %1970, %from_elements_822 : tensor<4xindex>, tensor<4xindex> -> tensor<4xindex>
    %1972 = stablehlo.dynamic_broadcast_in_dim %1968, %1971, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1973 = stablehlo.dynamic_broadcast_in_dim %expanded_824, %1971, dims = [0, 1, 2, 3] : (tensor<1x?x1x1xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1974 = stablehlo.divide %1972, %1973 : tensor<1x?x1x50xf32>
    %dim_825 = tensor.dim %arg282, %c0 : tensor<?x50x64xf32>
    %from_elements_826 = tensor.from_elements %c1, %dim_825, %c50, %c64_33 : tensor<4xindex>
    %dim_827 = tensor.dim %arg282, %c0 : tensor<?x50x64xf32>
    %expanded_828 = tensor.expand_shape %arg282 [[0, 1], [2], [3]] output_shape [1, %dim_827, 50, 64] : tensor<?x50x64xf32> into tensor<1x?x50x64xf32>
    %1975 = shape.shape_of %1974 : tensor<1x?x1x50xf32> -> tensor<4xindex>
    %head_829, %tail_830 = "shape.split_at"(%1975, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %head_831, %tail_832 = "shape.split_at"(%from_elements_826, %c-2) : (tensor<4xindex>, index) -> (!shape.shape, !shape.shape)
    %1976 = shape.broadcast %head_829, %head_831 : !shape.shape, !shape.shape -> !shape.shape
    %1977 = shape.concat %1976, %tail_830 : !shape.shape, !shape.shape -> !shape.shape
    %1978 = shape.to_extent_tensor %1977 : !shape.shape -> tensor<4xindex>
    %1979 = stablehlo.dynamic_broadcast_in_dim %1974, %1978, dims = [0, 1, 2, 3] : (tensor<1x?x1x50xf32>, tensor<4xindex>) -> tensor<1x?x1x50xf32>
    %1980 = shape.concat %1976, %tail_832 : !shape.shape, !shape.shape -> !shape.shape
    %1981 = shape.to_extent_tensor %1980 : !shape.shape -> tensor<4xindex>
    %1982 = stablehlo.dynamic_broadcast_in_dim %expanded_828, %1981, dims = [0, 1, 2, 3] : (tensor<1x?x50x64xf32>, tensor<4xindex>) -> tensor<1x?x50x64xf32>
    %1983 = stablehlo.dot_general %1979, %1982, batching_dims = [0, 1] x [0, 1], contracting_dims = [3] x [2], precision = [DEFAULT, DEFAULT] : (tensor<1x?x1x50xf32>, tensor<1x?x50x64xf32>) -> tensor<1x?x1x64xf32>
    %1984 = stablehlo.transpose %1983, dims = [1, 2, 0, 3] : (tensor<1x?x1x64xf32>) -> tensor<?x1x1x64xf32>
    %collapsed_833 = tensor.collapse_shape %1984 [[0], [1, 2, 3]] : tensor<?x1x1x64xf32> into tensor<?x64xf32>
    %1985 = stablehlo.concatenate %arg283, %arg284, dim = 1 : (tensor<?x11x16xf32>, tensor<?x10x16xf32>) -> tensor<?x21x16xf32>
    %1986 = stablehlo.concatenate %arg285, %arg286, dim = 1 : (tensor<?x11x16xf32>, tensor<?x10x16xf32>) -> tensor<?x21x16xf32>
    %1987 = stablehlo.concatenate %arg287, %arg288, dim = 1 : (tensor<?x13x16xf32>, tensor<?x12x16xf32>) -> tensor<?x25x16xf32>
    %1988 = shape.shape_of %1985 : tensor<?x21x16xf32> -> tensor<3xindex>
    %1989 = shape.shape_of %arg289 : tensor<?x16x5xf32> -> tensor<3xindex>
    %head_834, %tail_835 = "shape.split_at"(%1988, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_836, %tail_837 = "shape.split_at"(%1989, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %1990 = shape.broadcast %head_834, %head_836 : !shape.shape, !shape.shape -> !shape.shape
    %1991 = shape.concat %1990, %tail_835 : !shape.shape, !shape.shape -> !shape.shape
    %1992 = shape.to_extent_tensor %1991 : !shape.shape -> tensor<3xindex>
    %1993 = stablehlo.dynamic_broadcast_in_dim %1985, %1992, dims = [0, 1, 2] : (tensor<?x21x16xf32>, tensor<3xindex>) -> tensor<?x21x16xf32>
    %1994 = shape.concat %1990, %tail_837 : !shape.shape, !shape.shape -> !shape.shape
    %1995 = shape.to_extent_tensor %1994 : !shape.shape -> tensor<3xindex>
    %1996 = stablehlo.dynamic_broadcast_in_dim %arg289, %1995, dims = [0, 1, 2] : (tensor<?x16x5xf32>, tensor<3xindex>) -> tensor<?x16x5xf32>
    %1997 = stablehlo.dot_general %1993, %1996, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<?x21x16xf32>, tensor<?x16x5xf32>) -> tensor<?x21x5xf32>
    %collapsed_838 = tensor.collapse_shape %1997 [[0], [1, 2]] : tensor<?x21x5xf32> into tensor<?x105xf32>
    %1998 = shape.shape_of %1986 : tensor<?x21x16xf32> -> tensor<3xindex>
    %1999 = shape.shape_of %arg290 : tensor<?x16x4xf32> -> tensor<3xindex>
    %head_839, %tail_840 = "shape.split_at"(%1998, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_841, %tail_842 = "shape.split_at"(%1999, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %2000 = shape.broadcast %head_839, %head_841 : !shape.shape, !shape.shape -> !shape.shape
    %2001 = shape.concat %2000, %tail_840 : !shape.shape, !shape.shape -> !shape.shape
    %2002 = shape.to_extent_tensor %2001 : !shape.shape -> tensor<3xindex>
    %2003 = stablehlo.dynamic_broadcast_in_dim %1986, %2002, dims = [0, 1, 2] : (tensor<?x21x16xf32>, tensor<3xindex>) -> tensor<?x21x16xf32>
    %2004 = shape.concat %2000, %tail_842 : !shape.shape, !shape.shape -> !shape.shape
    %2005 = shape.to_extent_tensor %2004 : !shape.shape -> tensor<3xindex>
    %2006 = stablehlo.dynamic_broadcast_in_dim %arg290, %2005, dims = [0, 1, 2] : (tensor<?x16x4xf32>, tensor<3xindex>) -> tensor<?x16x4xf32>
    %2007 = stablehlo.dot_general %2003, %2006, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<?x21x16xf32>, tensor<?x16x4xf32>) -> tensor<?x21x4xf32>
    %collapsed_843 = tensor.collapse_shape %2007 [[0], [1, 2]] : tensor<?x21x4xf32> into tensor<?x84xf32>
    %2008 = shape.shape_of %1987 : tensor<?x25x16xf32> -> tensor<3xindex>
    %2009 = shape.shape_of %arg291 : tensor<?x16x4xf32> -> tensor<3xindex>
    %head_844, %tail_845 = "shape.split_at"(%2008, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %head_846, %tail_847 = "shape.split_at"(%2009, %c-2) : (tensor<3xindex>, index) -> (!shape.shape, !shape.shape)
    %2010 = shape.broadcast %head_844, %head_846 : !shape.shape, !shape.shape -> !shape.shape
    %2011 = shape.concat %2010, %tail_845 : !shape.shape, !shape.shape -> !shape.shape
    %2012 = shape.to_extent_tensor %2011 : !shape.shape -> tensor<3xindex>
    %2013 = stablehlo.dynamic_broadcast_in_dim %1987, %2012, dims = [0, 1, 2] : (tensor<?x25x16xf32>, tensor<3xindex>) -> tensor<?x25x16xf32>
    %2014 = shape.concat %2010, %tail_847 : !shape.shape, !shape.shape -> !shape.shape
    %2015 = shape.to_extent_tensor %2014 : !shape.shape -> tensor<3xindex>
    %2016 = stablehlo.dynamic_broadcast_in_dim %arg291, %2015, dims = [0, 1, 2] : (tensor<?x16x4xf32>, tensor<3xindex>) -> tensor<?x16x4xf32>
    %2017 = stablehlo.dot_general %2013, %2016, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<?x25x16xf32>, tensor<?x16x4xf32>) -> tensor<?x25x4xf32>
    %collapsed_848 = tensor.collapse_shape %2017 [[0], [1, 2]] : tensor<?x25x4xf32> into tensor<?x100xf32>
    %2018 = stablehlo.concatenate %arg292, %arg293, %arg294, %arg295, %arg296, %arg297, %arg298, %arg299, %arg300, %collapsed_838, %collapsed_843, %collapsed_848, %arg301, %arg302, %arg303, %arg304, %arg305, %arg306, %arg307, %arg308, %arg309, %arg310, %arg311, %arg312, %arg313, %arg314, %arg315, %arg316, %arg317, %arg318, %arg319, %arg320, %arg321, %arg322, %arg323, %arg324, %arg325, %arg326, %arg327, %arg328, %arg329, %arg330, %arg331, %arg332, %arg333, %arg334, %arg335, %arg336, %arg337, %arg338, %arg339, %arg340, %arg341, %arg342, %arg343, %arg344, %arg345, %arg346, %arg347, %arg348, %arg349, %arg350, %arg351, %arg352, %arg353, %arg354, %arg355, %arg356, %arg357, %arg358, %arg359, %arg360, %arg361, %arg362, %arg363, %arg364, %arg365, %arg366, %arg367, %arg368, %arg369, %arg370, %arg371, %arg372, %arg373, %arg374, %arg375, %arg376, %arg377, %arg378, %arg379, %arg380, %arg381, %arg382, %arg383, %arg384, %arg385, %arg386, %arg387, %arg388, %arg389, %arg390, %arg391, %arg392, %arg393, %arg394, %arg395, %arg396, %arg397, %arg398, %arg399, %arg400, %arg401, %arg402, %arg403, %arg404, %arg405, %arg406, %arg407, %arg408, %arg409, %arg410, %arg411, %arg412, %arg413, %arg414, %arg415, %arg416, %collapsed_211, %arg417, %arg418, %arg419, %arg420, %arg421, %arg422, %arg423, %arg424, %arg425, %arg426, %arg427, %arg428, %arg429, %arg430, %arg431, %arg432, %arg433, %arg434, %arg435, %arg436, %arg437, %arg438, %arg439, %arg440, %arg441, %arg442, %arg443, %arg444, %collapsed_93, %321, %collapsed_484, %322, %collapsed_231, %478, %collapsed_426, %collapsed_455, %collapsed_601, %collapsed_833, %collapsed_717, %320, %532, %376, %426, %477, %586, %103, %104, %106, %collapsed_122, %arg445, %99, %101, %arg446, %collapsed_182, %427, %collapsed_152, %arg447, %1332, %1261, %1337, %1298, %928, %857, %933, %894, %1665, %1607, %1670, %1644, %300, %302, %304, %arg448, %arg449, %arg450, %arg451, %arg452, %arg453, %arg454, %arg455, %arg456, %arg457, %arg458, %arg459, %arg460, %arg461, %arg462, %arg463, %arg464, %arg465, %arg466, %arg467, %arg468, %arg469, %arg470, %arg471, %arg472, %arg473, %arg474, %arg475, %arg476, %arg477, %arg478, %arg479, %arg480, %arg481, %arg482, %arg483, %arg484, %arg485, %arg486, %arg487, %arg488, %arg489, %arg490, %arg491, %arg492, %arg493, %arg494, %arg495, %arg496, %arg497, %arg498, %arg499, %arg500, %arg501, %arg502, %arg503, %arg504, %arg505, %arg506, %arg507, %arg508, %arg509, %arg510, %collapsed_513, %collapsed_746, %collapsed_630, %collapsed_260, %collapsed_348, %collapsed_542, %collapsed_775, %collapsed_659, %collapsed_289, %collapsed_377, %collapsed_571, %collapsed_804, %collapsed_688, %collapsed_318, %collapsed_406, %collapsed_319, %arg511, dim = 1 : (tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x105xf32>, tensor<?x84xf32>, tensor<?x100xf32>, tensor<?x180xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x16xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x76xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x16xf32>, tensor<?x48xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x32xf32>, tensor<?x68xf32>, tensor<?x32xf32>, tensor<?x104xf32>, tensor<?x64xf32>, tensor<?x88xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x1184xf32>, tensor<?x80xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x80xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x32xf32>, tensor<?x108xf32>, tensor<?x32xf32>, tensor<?x92xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x64xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x16xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x8xf32>, tensor<?x96xf32>, tensor<?x96xf32>, tensor<?x96xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x48xf32>, tensor<?x48xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x24xf32>, tensor<?x24xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x12xf32>, tensor<?x12xf32>, tensor<?x1024xf32>, tensor<?x120xf32>) -> tensor<?x8821xf32>
    %2019 = shape.shape_of %2018 : tensor<?x8821xf32> -> tensor<2xindex>
    %2020 = shape.shape_of %207 : tensor<?x8821xf32> -> tensor<2xindex>
    %2021 = shape.broadcast %2019, %2020 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2022 = stablehlo.dynamic_broadcast_in_dim %2018, %2021, dims = [0, 1] : (tensor<?x8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %2023 = stablehlo.dynamic_broadcast_in_dim %207, %2021, dims = [0, 1] : (tensor<?x8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %2024 = stablehlo.multiply %2022, %2023 : tensor<?x8821xf32>
    %2025 = shape.shape_of %2024 : tensor<?x8821xf32> -> tensor<2xindex>
    %head_849, %tail_850 = "shape.split_at"(%2025, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2026 = shape.broadcast %head_849, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2027 = shape.concat %2026, %tail_850 : !shape.shape, !shape.shape -> !shape.shape
    %2028 = shape.to_extent_tensor %2027 : !shape.shape -> tensor<3xindex>
    %2029 = stablehlo.dynamic_broadcast_in_dim %2024, %2028, dims = [1, 2] : (tensor<?x8821xf32>, tensor<3xindex>) -> tensor<5x?x8821xf32>
    %2030 = stablehlo.dot_general %2029, %arg512, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x8821xf32>, tensor<5x8821x348xf32>) -> tensor<5x?x348xf32>
    %2031 = shape.shape_of %2030 : tensor<5x?x348xf32> -> tensor<3xindex>
    %2032 = shape.broadcast %2031, %11 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2033 = stablehlo.dynamic_broadcast_in_dim %2030, %2032, dims = [0, 1, 2] : (tensor<5x?x348xf32>, tensor<3xindex>) -> tensor<5x?x348xf32>
    %2034 = stablehlo.dynamic_broadcast_in_dim %arg513, %2032, dims = [0, 1, 2] : (tensor<5x1x348xf32>, tensor<3xindex>) -> tensor<5x?x348xf32>
    %2035 = stablehlo.add %2033, %2034 : tensor<5x?x348xf32>
    %dim_851 = tensor.dim %2035, %c1 : tensor<5x?x348xf32>
    %2036 = arith.index_cast %dim_851 : index to i32
    %from_elements_852 = tensor.from_elements %c1_i32, %2036, %c348_i32 : tensor<3xi32>
    %2037 = stablehlo.real_dynamic_slice %2035, %cst_28, %from_elements_852, %cst_27 : (tensor<5x?x348xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x348xf32>
    %collapsed_853 = tensor.collapse_shape %2037 [[0, 1], [2]] : tensor<1x?x348xf32> into tensor<?x348xf32>
    %from_elements_854 = tensor.from_elements %c2_i32, %2036, %c348_i32 : tensor<3xi32>
    %2038 = stablehlo.real_dynamic_slice %2035, %cst_29, %from_elements_854, %cst_27 : (tensor<5x?x348xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x348xf32>
    %collapsed_855 = tensor.collapse_shape %2038 [[0, 1], [2]] : tensor<1x?x348xf32> into tensor<?x348xf32>
    %from_elements_856 = tensor.from_elements %c3_i32, %2036, %c348_i32 : tensor<3xi32>
    %2039 = stablehlo.real_dynamic_slice %2035, %cst_30, %from_elements_856, %cst_27 : (tensor<5x?x348xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x348xf32>
    %collapsed_857 = tensor.collapse_shape %2039 [[0, 1], [2]] : tensor<1x?x348xf32> into tensor<?x348xf32>
    %from_elements_858 = tensor.from_elements %c4_i32, %2036, %c348_i32 : tensor<3xi32>
    %2040 = stablehlo.real_dynamic_slice %2035, %cst_34, %from_elements_858, %cst_27 : (tensor<5x?x348xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x348xf32>
    %collapsed_859 = tensor.collapse_shape %2040 [[0, 1], [2]] : tensor<1x?x348xf32> into tensor<?x348xf32>
    %from_elements_860 = tensor.from_elements %c5_i32, %2036, %c348_i32 : tensor<3xi32>
    %2041 = stablehlo.real_dynamic_slice %2035, %cst_35, %from_elements_860, %cst_27 : (tensor<5x?x348xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x348xf32>
    %collapsed_861 = tensor.collapse_shape %2041 [[0, 1], [2]] : tensor<1x?x348xf32> into tensor<?x348xf32>
    %2042 = stablehlo.dot %collapsed_861, %arg514, precision = [DEFAULT, DEFAULT] : (tensor<?x348xf32>, tensor<348x348xf32>) -> tensor<?x348xf32>
    %2043 = shape.shape_of %2042 : tensor<?x348xf32> -> tensor<2xindex>
    %2044 = shape.broadcast %2043, %12 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2045 = stablehlo.dynamic_broadcast_in_dim %2042, %2044, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2046 = stablehlo.dynamic_broadcast_in_dim %arg515, %2044, dims = [0, 1] : (tensor<1x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2047 = stablehlo.add %2045, %2046 : tensor<?x348xf32>
    %2048 = shape.shape_of %2047 : tensor<?x348xf32> -> tensor<2xindex>
    %2049 = shape.shape_of %collapsed_861 : tensor<?x348xf32> -> tensor<2xindex>
    %2050 = shape.broadcast %2048, %2049 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2051 = stablehlo.dynamic_broadcast_in_dim %2047, %2050, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2052 = stablehlo.dynamic_broadcast_in_dim %collapsed_861, %2050, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2053 = stablehlo.multiply %2051, %2052 : tensor<?x348xf32>
    %2054 = shape.shape_of %2053 : tensor<?x348xf32> -> tensor<2xindex>
    %2055 = shape.broadcast %2054, %2049 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2056 = stablehlo.dynamic_broadcast_in_dim %2053, %2055, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2057 = stablehlo.dynamic_broadcast_in_dim %collapsed_861, %2055, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2058 = stablehlo.add %2056, %2057 : tensor<?x348xf32>
    %2059 = shape.shape_of %2058 : tensor<?x348xf32> -> tensor<2xindex>
    %2060 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2059, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2061 = stablehlo.multiply %2058, %2060 : tensor<?x348xf32>
    %2062 = stablehlo.tanh %2061 : tensor<?x348xf32>
    %2063 = shape.shape_of %2062 : tensor<?x348xf32> -> tensor<2xindex>
    %2064 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2063, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2065 = stablehlo.multiply %2062, %2064 : tensor<?x348xf32>
    %2066 = stablehlo.reduce(%2065 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x348xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_862 = tensor.dim %2066, %c0 : tensor<?xf32>
    %from_elements_863 = tensor.from_elements %dim_862, %c1 : tensor<2xindex>
    %dim_864 = tensor.dim %2066, %c0 : tensor<?xf32>
    %expanded_865 = tensor.expand_shape %2066 [[0, 1]] output_shape [%dim_864, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2067 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_863, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2068 = stablehlo.multiply %expanded_865, %2067 : tensor<?x1xf32>
    %2069 = stablehlo.tanh %2068 : tensor<?x1xf32>
    %2070 = shape.shape_of %2069 : tensor<?x1xf32> -> tensor<2xindex>
    %2071 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2070, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2072 = stablehlo.multiply %2069, %2071 : tensor<?x1xf32>
    %2073 = shape.shape_of %collapsed_855 : tensor<?x348xf32> -> tensor<2xindex>
    %2074 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2073, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2075 = stablehlo.multiply %collapsed_855, %2074 : tensor<?x348xf32>
    %2076 = shape.shape_of %collapsed_859 : tensor<?x348xf32> -> tensor<2xindex>
    %2077 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2076, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2078 = stablehlo.multiply %collapsed_859, %2077 : tensor<?x348xf32>
    %2079 = shape.shape_of %collapsed_853 : tensor<?x348xf32> -> tensor<2xindex>
    %2080 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2079, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2081 = stablehlo.maximum %collapsed_853, %2080 : tensor<?x348xf32>
    %2082 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2073, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2083 = stablehlo.maximum %collapsed_855, %2082 : tensor<?x348xf32>
    %2084 = shape.shape_of %collapsed_857 : tensor<?x348xf32> -> tensor<2xindex>
    %2085 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2084, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2086 = stablehlo.maximum %collapsed_857, %2085 : tensor<?x348xf32>
    %2087 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2049, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2088 = stablehlo.maximum %collapsed_861, %2087 : tensor<?x348xf32>
    %2089 = shape.shape_of %2075 : tensor<?x348xf32> -> tensor<2xindex>
    %2090 = shape.broadcast %2079, %2089 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2091 = stablehlo.dynamic_broadcast_in_dim %collapsed_853, %2090, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2092 = stablehlo.dynamic_broadcast_in_dim %2075, %2090, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2093 = stablehlo.multiply %2091, %2092 : tensor<?x348xf32>
    %2094 = stablehlo.tanh %2093 : tensor<?x348xf32>
    %2095 = shape.shape_of %2094 : tensor<?x348xf32> -> tensor<2xindex>
    %2096 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2095, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2097 = stablehlo.multiply %2094, %2096 : tensor<?x348xf32>
    %2098 = stablehlo.reduce(%2097 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x348xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_866 = tensor.dim %2098, %c0 : tensor<?xf32>
    %from_elements_867 = tensor.from_elements %dim_866, %c1 : tensor<2xindex>
    %dim_868 = tensor.dim %2098, %c0 : tensor<?xf32>
    %expanded_869 = tensor.expand_shape %2098 [[0, 1]] output_shape [%dim_868, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2099 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_867, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2100 = stablehlo.multiply %expanded_869, %2099 : tensor<?x1xf32>
    %2101 = stablehlo.tanh %2100 : tensor<?x1xf32>
    %2102 = shape.shape_of %2101 : tensor<?x1xf32> -> tensor<2xindex>
    %2103 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2102, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2104 = stablehlo.multiply %2101, %2103 : tensor<?x1xf32>
    %2105 = shape.shape_of %2078 : tensor<?x348xf32> -> tensor<2xindex>
    %2106 = shape.broadcast %2084, %2105 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2107 = stablehlo.dynamic_broadcast_in_dim %collapsed_857, %2106, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2108 = stablehlo.dynamic_broadcast_in_dim %2078, %2106, dims = [0, 1] : (tensor<?x348xf32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2109 = stablehlo.multiply %2107, %2108 : tensor<?x348xf32>
    %2110 = stablehlo.tanh %2109 : tensor<?x348xf32>
    %2111 = shape.shape_of %2110 : tensor<?x348xf32> -> tensor<2xindex>
    %2112 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2111, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x348xf32>
    %2113 = stablehlo.multiply %2110, %2112 : tensor<?x348xf32>
    %2114 = stablehlo.reduce(%2113 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x348xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_870 = tensor.dim %2114, %c0 : tensor<?xf32>
    %from_elements_871 = tensor.from_elements %dim_870, %c1 : tensor<2xindex>
    %dim_872 = tensor.dim %2114, %c0 : tensor<?xf32>
    %expanded_873 = tensor.expand_shape %2114 [[0, 1]] output_shape [%dim_872, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2115 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_871, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2116 = stablehlo.multiply %expanded_873, %2115 : tensor<?x1xf32>
    %2117 = stablehlo.tanh %2116 : tensor<?x1xf32>
    %2118 = shape.shape_of %2117 : tensor<?x1xf32> -> tensor<2xindex>
    %2119 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2118, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2120 = stablehlo.multiply %2117, %2119 : tensor<?x1xf32>
    %2121 = stablehlo.concatenate %2081, %2083, %2086, %2088, %2097, %2113, %2065, %2104, %2120, %2072, dim = 1 : (tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x348xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x2439xf32>
    %2122 = shape.shape_of %2121 : tensor<?x2439xf32> -> tensor<2xindex>
    %2123 = shape.shape_of %215 : tensor<?x2439xf32> -> tensor<2xindex>
    %2124 = shape.broadcast %2122, %2123 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2125 = stablehlo.dynamic_broadcast_in_dim %2121, %2124, dims = [0, 1] : (tensor<?x2439xf32>, tensor<2xindex>) -> tensor<?x2439xf32>
    %2126 = stablehlo.dynamic_broadcast_in_dim %215, %2124, dims = [0, 1] : (tensor<?x2439xf32>, tensor<2xindex>) -> tensor<?x2439xf32>
    %2127 = stablehlo.multiply %2125, %2126 : tensor<?x2439xf32>
    %2128 = shape.shape_of %2127 : tensor<?x2439xf32> -> tensor<2xindex>
    %head_874, %tail_875 = "shape.split_at"(%2128, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2129 = shape.broadcast %head_874, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2130 = shape.concat %2129, %tail_875 : !shape.shape, !shape.shape -> !shape.shape
    %2131 = shape.to_extent_tensor %2130 : !shape.shape -> tensor<3xindex>
    %2132 = stablehlo.dynamic_broadcast_in_dim %2127, %2131, dims = [1, 2] : (tensor<?x2439xf32>, tensor<3xindex>) -> tensor<5x?x2439xf32>
    %2133 = stablehlo.dot_general %2132, %arg516, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x2439xf32>, tensor<5x2439x238xf32>) -> tensor<5x?x238xf32>
    %2134 = shape.shape_of %2133 : tensor<5x?x238xf32> -> tensor<3xindex>
    %2135 = shape.broadcast %2134, %13 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2136 = stablehlo.dynamic_broadcast_in_dim %2133, %2135, dims = [0, 1, 2] : (tensor<5x?x238xf32>, tensor<3xindex>) -> tensor<5x?x238xf32>
    %2137 = stablehlo.dynamic_broadcast_in_dim %arg517, %2135, dims = [0, 1, 2] : (tensor<5x1x238xf32>, tensor<3xindex>) -> tensor<5x?x238xf32>
    %2138 = stablehlo.add %2136, %2137 : tensor<5x?x238xf32>
    %dim_876 = tensor.dim %2138, %c1 : tensor<5x?x238xf32>
    %2139 = arith.index_cast %dim_876 : index to i32
    %from_elements_877 = tensor.from_elements %c1_i32, %2139, %c238_i32 : tensor<3xi32>
    %2140 = stablehlo.real_dynamic_slice %2138, %cst_28, %from_elements_877, %cst_27 : (tensor<5x?x238xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x238xf32>
    %collapsed_878 = tensor.collapse_shape %2140 [[0, 1], [2]] : tensor<1x?x238xf32> into tensor<?x238xf32>
    %from_elements_879 = tensor.from_elements %c2_i32, %2139, %c238_i32 : tensor<3xi32>
    %2141 = stablehlo.real_dynamic_slice %2138, %cst_29, %from_elements_879, %cst_27 : (tensor<5x?x238xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x238xf32>
    %collapsed_880 = tensor.collapse_shape %2141 [[0, 1], [2]] : tensor<1x?x238xf32> into tensor<?x238xf32>
    %from_elements_881 = tensor.from_elements %c3_i32, %2139, %c238_i32 : tensor<3xi32>
    %2142 = stablehlo.real_dynamic_slice %2138, %cst_30, %from_elements_881, %cst_27 : (tensor<5x?x238xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x238xf32>
    %collapsed_882 = tensor.collapse_shape %2142 [[0, 1], [2]] : tensor<1x?x238xf32> into tensor<?x238xf32>
    %from_elements_883 = tensor.from_elements %c4_i32, %2139, %c238_i32 : tensor<3xi32>
    %2143 = stablehlo.real_dynamic_slice %2138, %cst_34, %from_elements_883, %cst_27 : (tensor<5x?x238xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x238xf32>
    %collapsed_884 = tensor.collapse_shape %2143 [[0, 1], [2]] : tensor<1x?x238xf32> into tensor<?x238xf32>
    %from_elements_885 = tensor.from_elements %c5_i32, %2139, %c238_i32 : tensor<3xi32>
    %2144 = stablehlo.real_dynamic_slice %2138, %cst_35, %from_elements_885, %cst_27 : (tensor<5x?x238xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x238xf32>
    %collapsed_886 = tensor.collapse_shape %2144 [[0, 1], [2]] : tensor<1x?x238xf32> into tensor<?x238xf32>
    %2145 = stablehlo.dot %collapsed_886, %arg518, precision = [DEFAULT, DEFAULT] : (tensor<?x238xf32>, tensor<238x238xf32>) -> tensor<?x238xf32>
    %2146 = shape.shape_of %2145 : tensor<?x238xf32> -> tensor<2xindex>
    %2147 = shape.broadcast %2146, %14 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2148 = stablehlo.dynamic_broadcast_in_dim %2145, %2147, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2149 = stablehlo.dynamic_broadcast_in_dim %arg519, %2147, dims = [0, 1] : (tensor<1x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2150 = stablehlo.add %2148, %2149 : tensor<?x238xf32>
    %2151 = shape.shape_of %2150 : tensor<?x238xf32> -> tensor<2xindex>
    %2152 = shape.shape_of %collapsed_886 : tensor<?x238xf32> -> tensor<2xindex>
    %2153 = shape.broadcast %2151, %2152 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2154 = stablehlo.dynamic_broadcast_in_dim %2150, %2153, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2155 = stablehlo.dynamic_broadcast_in_dim %collapsed_886, %2153, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2156 = stablehlo.multiply %2154, %2155 : tensor<?x238xf32>
    %2157 = shape.shape_of %2156 : tensor<?x238xf32> -> tensor<2xindex>
    %2158 = shape.broadcast %2157, %2152 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2159 = stablehlo.dynamic_broadcast_in_dim %2156, %2158, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2160 = stablehlo.dynamic_broadcast_in_dim %collapsed_886, %2158, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2161 = stablehlo.add %2159, %2160 : tensor<?x238xf32>
    %2162 = shape.shape_of %2161 : tensor<?x238xf32> -> tensor<2xindex>
    %2163 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2162, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2164 = stablehlo.multiply %2161, %2163 : tensor<?x238xf32>
    %2165 = stablehlo.tanh %2164 : tensor<?x238xf32>
    %2166 = shape.shape_of %2165 : tensor<?x238xf32> -> tensor<2xindex>
    %2167 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2166, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2168 = stablehlo.multiply %2165, %2167 : tensor<?x238xf32>
    %2169 = stablehlo.reduce(%2168 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x238xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_887 = tensor.dim %2169, %c0 : tensor<?xf32>
    %from_elements_888 = tensor.from_elements %dim_887, %c1 : tensor<2xindex>
    %dim_889 = tensor.dim %2169, %c0 : tensor<?xf32>
    %expanded_890 = tensor.expand_shape %2169 [[0, 1]] output_shape [%dim_889, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2170 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_888, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2171 = stablehlo.multiply %expanded_890, %2170 : tensor<?x1xf32>
    %2172 = stablehlo.tanh %2171 : tensor<?x1xf32>
    %2173 = shape.shape_of %2172 : tensor<?x1xf32> -> tensor<2xindex>
    %2174 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2173, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2175 = stablehlo.multiply %2172, %2174 : tensor<?x1xf32>
    %2176 = shape.shape_of %collapsed_880 : tensor<?x238xf32> -> tensor<2xindex>
    %2177 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2176, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2178 = stablehlo.multiply %collapsed_880, %2177 : tensor<?x238xf32>
    %2179 = shape.shape_of %collapsed_884 : tensor<?x238xf32> -> tensor<2xindex>
    %2180 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2179, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2181 = stablehlo.multiply %collapsed_884, %2180 : tensor<?x238xf32>
    %2182 = shape.shape_of %collapsed_878 : tensor<?x238xf32> -> tensor<2xindex>
    %2183 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2182, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2184 = stablehlo.maximum %collapsed_878, %2183 : tensor<?x238xf32>
    %2185 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2176, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2186 = stablehlo.maximum %collapsed_880, %2185 : tensor<?x238xf32>
    %2187 = shape.shape_of %collapsed_882 : tensor<?x238xf32> -> tensor<2xindex>
    %2188 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2187, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2189 = stablehlo.maximum %collapsed_882, %2188 : tensor<?x238xf32>
    %2190 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2152, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2191 = stablehlo.maximum %collapsed_886, %2190 : tensor<?x238xf32>
    %2192 = shape.shape_of %2178 : tensor<?x238xf32> -> tensor<2xindex>
    %2193 = shape.broadcast %2182, %2192 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2194 = stablehlo.dynamic_broadcast_in_dim %collapsed_878, %2193, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2195 = stablehlo.dynamic_broadcast_in_dim %2178, %2193, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2196 = stablehlo.multiply %2194, %2195 : tensor<?x238xf32>
    %2197 = stablehlo.tanh %2196 : tensor<?x238xf32>
    %2198 = shape.shape_of %2197 : tensor<?x238xf32> -> tensor<2xindex>
    %2199 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2198, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2200 = stablehlo.multiply %2197, %2199 : tensor<?x238xf32>
    %2201 = stablehlo.reduce(%2200 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x238xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_891 = tensor.dim %2201, %c0 : tensor<?xf32>
    %from_elements_892 = tensor.from_elements %dim_891, %c1 : tensor<2xindex>
    %dim_893 = tensor.dim %2201, %c0 : tensor<?xf32>
    %expanded_894 = tensor.expand_shape %2201 [[0, 1]] output_shape [%dim_893, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2202 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_892, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2203 = stablehlo.multiply %expanded_894, %2202 : tensor<?x1xf32>
    %2204 = stablehlo.tanh %2203 : tensor<?x1xf32>
    %2205 = shape.shape_of %2204 : tensor<?x1xf32> -> tensor<2xindex>
    %2206 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2205, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2207 = stablehlo.multiply %2204, %2206 : tensor<?x1xf32>
    %2208 = shape.shape_of %2181 : tensor<?x238xf32> -> tensor<2xindex>
    %2209 = shape.broadcast %2187, %2208 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2210 = stablehlo.dynamic_broadcast_in_dim %collapsed_882, %2209, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2211 = stablehlo.dynamic_broadcast_in_dim %2181, %2209, dims = [0, 1] : (tensor<?x238xf32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2212 = stablehlo.multiply %2210, %2211 : tensor<?x238xf32>
    %2213 = stablehlo.tanh %2212 : tensor<?x238xf32>
    %2214 = shape.shape_of %2213 : tensor<?x238xf32> -> tensor<2xindex>
    %2215 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2214, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x238xf32>
    %2216 = stablehlo.multiply %2213, %2215 : tensor<?x238xf32>
    %2217 = stablehlo.reduce(%2216 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x238xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_895 = tensor.dim %2217, %c0 : tensor<?xf32>
    %from_elements_896 = tensor.from_elements %dim_895, %c1 : tensor<2xindex>
    %dim_897 = tensor.dim %2217, %c0 : tensor<?xf32>
    %expanded_898 = tensor.expand_shape %2217 [[0, 1]] output_shape [%dim_897, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2218 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_896, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2219 = stablehlo.multiply %expanded_898, %2218 : tensor<?x1xf32>
    %2220 = stablehlo.tanh %2219 : tensor<?x1xf32>
    %2221 = shape.shape_of %2220 : tensor<?x1xf32> -> tensor<2xindex>
    %2222 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2221, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2223 = stablehlo.multiply %2220, %2222 : tensor<?x1xf32>
    %2224 = stablehlo.concatenate %2184, %2186, %2189, %2191, %2200, %2216, %2168, %2207, %2223, %2175, dim = 1 : (tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x238xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x1669xf32>
    %2225 = shape.shape_of %2224 : tensor<?x1669xf32> -> tensor<2xindex>
    %2226 = shape.shape_of %238 : tensor<?x1669xf32> -> tensor<2xindex>
    %2227 = shape.broadcast %2225, %2226 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2228 = stablehlo.dynamic_broadcast_in_dim %2224, %2227, dims = [0, 1] : (tensor<?x1669xf32>, tensor<2xindex>) -> tensor<?x1669xf32>
    %2229 = stablehlo.dynamic_broadcast_in_dim %238, %2227, dims = [0, 1] : (tensor<?x1669xf32>, tensor<2xindex>) -> tensor<?x1669xf32>
    %2230 = stablehlo.multiply %2228, %2229 : tensor<?x1669xf32>
    %2231 = shape.shape_of %2230 : tensor<?x1669xf32> -> tensor<2xindex>
    %head_899, %tail_900 = "shape.split_at"(%2231, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2232 = shape.broadcast %head_899, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2233 = shape.concat %2232, %tail_900 : !shape.shape, !shape.shape -> !shape.shape
    %2234 = shape.to_extent_tensor %2233 : !shape.shape -> tensor<3xindex>
    %2235 = stablehlo.dynamic_broadcast_in_dim %2230, %2234, dims = [1, 2] : (tensor<?x1669xf32>, tensor<3xindex>) -> tensor<5x?x1669xf32>
    %2236 = stablehlo.dot_general %2235, %arg520, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x1669xf32>, tensor<5x1669x113xf32>) -> tensor<5x?x113xf32>
    %2237 = shape.shape_of %2236 : tensor<5x?x113xf32> -> tensor<3xindex>
    %2238 = shape.broadcast %2237, %15 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2239 = stablehlo.dynamic_broadcast_in_dim %2236, %2238, dims = [0, 1, 2] : (tensor<5x?x113xf32>, tensor<3xindex>) -> tensor<5x?x113xf32>
    %2240 = stablehlo.dynamic_broadcast_in_dim %arg521, %2238, dims = [0, 1, 2] : (tensor<5x1x113xf32>, tensor<3xindex>) -> tensor<5x?x113xf32>
    %2241 = stablehlo.add %2239, %2240 : tensor<5x?x113xf32>
    %dim_901 = tensor.dim %2241, %c1 : tensor<5x?x113xf32>
    %2242 = arith.index_cast %dim_901 : index to i32
    %from_elements_902 = tensor.from_elements %c1_i32, %2242, %c113_i32 : tensor<3xi32>
    %2243 = stablehlo.real_dynamic_slice %2241, %cst_28, %from_elements_902, %cst_27 : (tensor<5x?x113xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x113xf32>
    %collapsed_903 = tensor.collapse_shape %2243 [[0, 1], [2]] : tensor<1x?x113xf32> into tensor<?x113xf32>
    %from_elements_904 = tensor.from_elements %c2_i32, %2242, %c113_i32 : tensor<3xi32>
    %2244 = stablehlo.real_dynamic_slice %2241, %cst_29, %from_elements_904, %cst_27 : (tensor<5x?x113xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x113xf32>
    %collapsed_905 = tensor.collapse_shape %2244 [[0, 1], [2]] : tensor<1x?x113xf32> into tensor<?x113xf32>
    %from_elements_906 = tensor.from_elements %c3_i32, %2242, %c113_i32 : tensor<3xi32>
    %2245 = stablehlo.real_dynamic_slice %2241, %cst_30, %from_elements_906, %cst_27 : (tensor<5x?x113xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x113xf32>
    %collapsed_907 = tensor.collapse_shape %2245 [[0, 1], [2]] : tensor<1x?x113xf32> into tensor<?x113xf32>
    %from_elements_908 = tensor.from_elements %c4_i32, %2242, %c113_i32 : tensor<3xi32>
    %2246 = stablehlo.real_dynamic_slice %2241, %cst_34, %from_elements_908, %cst_27 : (tensor<5x?x113xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x113xf32>
    %collapsed_909 = tensor.collapse_shape %2246 [[0, 1], [2]] : tensor<1x?x113xf32> into tensor<?x113xf32>
    %from_elements_910 = tensor.from_elements %c5_i32, %2242, %c113_i32 : tensor<3xi32>
    %2247 = stablehlo.real_dynamic_slice %2241, %cst_35, %from_elements_910, %cst_27 : (tensor<5x?x113xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x113xf32>
    %collapsed_911 = tensor.collapse_shape %2247 [[0, 1], [2]] : tensor<1x?x113xf32> into tensor<?x113xf32>
    %2248 = stablehlo.dot %collapsed_911, %arg522, precision = [DEFAULT, DEFAULT] : (tensor<?x113xf32>, tensor<113x113xf32>) -> tensor<?x113xf32>
    %2249 = shape.shape_of %2248 : tensor<?x113xf32> -> tensor<2xindex>
    %2250 = shape.broadcast %2249, %16 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2251 = stablehlo.dynamic_broadcast_in_dim %2248, %2250, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2252 = stablehlo.dynamic_broadcast_in_dim %arg523, %2250, dims = [0, 1] : (tensor<1x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2253 = stablehlo.add %2251, %2252 : tensor<?x113xf32>
    %2254 = shape.shape_of %2253 : tensor<?x113xf32> -> tensor<2xindex>
    %2255 = shape.shape_of %collapsed_911 : tensor<?x113xf32> -> tensor<2xindex>
    %2256 = shape.broadcast %2254, %2255 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2257 = stablehlo.dynamic_broadcast_in_dim %2253, %2256, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2258 = stablehlo.dynamic_broadcast_in_dim %collapsed_911, %2256, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2259 = stablehlo.multiply %2257, %2258 : tensor<?x113xf32>
    %2260 = shape.shape_of %2259 : tensor<?x113xf32> -> tensor<2xindex>
    %2261 = shape.broadcast %2260, %2255 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2262 = stablehlo.dynamic_broadcast_in_dim %2259, %2261, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2263 = stablehlo.dynamic_broadcast_in_dim %collapsed_911, %2261, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2264 = stablehlo.add %2262, %2263 : tensor<?x113xf32>
    %2265 = shape.shape_of %2264 : tensor<?x113xf32> -> tensor<2xindex>
    %2266 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2265, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2267 = stablehlo.multiply %2264, %2266 : tensor<?x113xf32>
    %2268 = stablehlo.tanh %2267 : tensor<?x113xf32>
    %2269 = shape.shape_of %2268 : tensor<?x113xf32> -> tensor<2xindex>
    %2270 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2269, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2271 = stablehlo.multiply %2268, %2270 : tensor<?x113xf32>
    %2272 = stablehlo.reduce(%2271 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x113xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_912 = tensor.dim %2272, %c0 : tensor<?xf32>
    %from_elements_913 = tensor.from_elements %dim_912, %c1 : tensor<2xindex>
    %dim_914 = tensor.dim %2272, %c0 : tensor<?xf32>
    %expanded_915 = tensor.expand_shape %2272 [[0, 1]] output_shape [%dim_914, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2273 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_913, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2274 = stablehlo.multiply %expanded_915, %2273 : tensor<?x1xf32>
    %2275 = stablehlo.tanh %2274 : tensor<?x1xf32>
    %2276 = shape.shape_of %2275 : tensor<?x1xf32> -> tensor<2xindex>
    %2277 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2276, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2278 = stablehlo.multiply %2275, %2277 : tensor<?x1xf32>
    %2279 = shape.shape_of %collapsed_905 : tensor<?x113xf32> -> tensor<2xindex>
    %2280 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2279, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2281 = stablehlo.multiply %collapsed_905, %2280 : tensor<?x113xf32>
    %2282 = shape.shape_of %collapsed_909 : tensor<?x113xf32> -> tensor<2xindex>
    %2283 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2282, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2284 = stablehlo.multiply %collapsed_909, %2283 : tensor<?x113xf32>
    %2285 = shape.shape_of %collapsed_903 : tensor<?x113xf32> -> tensor<2xindex>
    %2286 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2285, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2287 = stablehlo.maximum %collapsed_903, %2286 : tensor<?x113xf32>
    %2288 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2279, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2289 = stablehlo.maximum %collapsed_905, %2288 : tensor<?x113xf32>
    %2290 = shape.shape_of %collapsed_907 : tensor<?x113xf32> -> tensor<2xindex>
    %2291 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2290, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2292 = stablehlo.maximum %collapsed_907, %2291 : tensor<?x113xf32>
    %2293 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2255, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2294 = stablehlo.maximum %collapsed_911, %2293 : tensor<?x113xf32>
    %2295 = shape.shape_of %2281 : tensor<?x113xf32> -> tensor<2xindex>
    %2296 = shape.broadcast %2285, %2295 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2297 = stablehlo.dynamic_broadcast_in_dim %collapsed_903, %2296, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2298 = stablehlo.dynamic_broadcast_in_dim %2281, %2296, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2299 = stablehlo.multiply %2297, %2298 : tensor<?x113xf32>
    %2300 = stablehlo.tanh %2299 : tensor<?x113xf32>
    %2301 = shape.shape_of %2300 : tensor<?x113xf32> -> tensor<2xindex>
    %2302 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2301, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2303 = stablehlo.multiply %2300, %2302 : tensor<?x113xf32>
    %2304 = stablehlo.reduce(%2303 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x113xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_916 = tensor.dim %2304, %c0 : tensor<?xf32>
    %from_elements_917 = tensor.from_elements %dim_916, %c1 : tensor<2xindex>
    %dim_918 = tensor.dim %2304, %c0 : tensor<?xf32>
    %expanded_919 = tensor.expand_shape %2304 [[0, 1]] output_shape [%dim_918, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2305 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_917, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2306 = stablehlo.multiply %expanded_919, %2305 : tensor<?x1xf32>
    %2307 = stablehlo.tanh %2306 : tensor<?x1xf32>
    %2308 = shape.shape_of %2307 : tensor<?x1xf32> -> tensor<2xindex>
    %2309 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2308, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2310 = stablehlo.multiply %2307, %2309 : tensor<?x1xf32>
    %2311 = shape.shape_of %2284 : tensor<?x113xf32> -> tensor<2xindex>
    %2312 = shape.broadcast %2290, %2311 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2313 = stablehlo.dynamic_broadcast_in_dim %collapsed_907, %2312, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2314 = stablehlo.dynamic_broadcast_in_dim %2284, %2312, dims = [0, 1] : (tensor<?x113xf32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2315 = stablehlo.multiply %2313, %2314 : tensor<?x113xf32>
    %2316 = stablehlo.tanh %2315 : tensor<?x113xf32>
    %2317 = shape.shape_of %2316 : tensor<?x113xf32> -> tensor<2xindex>
    %2318 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2317, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x113xf32>
    %2319 = stablehlo.multiply %2316, %2318 : tensor<?x113xf32>
    %2320 = stablehlo.reduce(%2319 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x113xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_920 = tensor.dim %2320, %c0 : tensor<?xf32>
    %from_elements_921 = tensor.from_elements %dim_920, %c1 : tensor<2xindex>
    %dim_922 = tensor.dim %2320, %c0 : tensor<?xf32>
    %expanded_923 = tensor.expand_shape %2320 [[0, 1]] output_shape [%dim_922, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2321 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_921, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2322 = stablehlo.multiply %expanded_923, %2321 : tensor<?x1xf32>
    %2323 = stablehlo.tanh %2322 : tensor<?x1xf32>
    %2324 = shape.shape_of %2323 : tensor<?x1xf32> -> tensor<2xindex>
    %2325 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2324, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2326 = stablehlo.multiply %2323, %2325 : tensor<?x1xf32>
    %2327 = stablehlo.concatenate %2287, %2289, %2292, %2294, %2303, %2319, %2271, %2310, %2326, %2278, dim = 1 : (tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x113xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x794xf32>
    %2328 = shape.shape_of %2327 : tensor<?x794xf32> -> tensor<2xindex>
    %2329 = shape.shape_of %253 : tensor<?x794xf32> -> tensor<2xindex>
    %2330 = shape.broadcast %2328, %2329 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2331 = stablehlo.dynamic_broadcast_in_dim %2327, %2330, dims = [0, 1] : (tensor<?x794xf32>, tensor<2xindex>) -> tensor<?x794xf32>
    %2332 = stablehlo.dynamic_broadcast_in_dim %253, %2330, dims = [0, 1] : (tensor<?x794xf32>, tensor<2xindex>) -> tensor<?x794xf32>
    %2333 = stablehlo.multiply %2331, %2332 : tensor<?x794xf32>
    %2334 = stablehlo.dot %2333, %arg524, precision = [DEFAULT, DEFAULT] : (tensor<?x794xf32>, tensor<794x452xf32>) -> tensor<?x452xf32>
    %2335 = shape.shape_of %2334 : tensor<?x452xf32> -> tensor<2xindex>
    %2336 = stablehlo.dynamic_broadcast_in_dim %arg525, %2335, dims = [1] : (tensor<452xf32>, tensor<2xindex>) -> tensor<?x452xf32>
    %2337 = stablehlo.add %2334, %2336 : tensor<?x452xf32>
    %2338 = shape.shape_of %2337 : tensor<?x452xf32> -> tensor<2xindex>
    %2339 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2338, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x452xf32>
    %2340 = stablehlo.maximum %2337, %2339 : tensor<?x452xf32>
    %2341 = shape.shape_of %223 : tensor<?x8821xf32> -> tensor<2xindex>
    %2342 = shape.broadcast %2019, %2341 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2343 = stablehlo.dynamic_broadcast_in_dim %2018, %2342, dims = [0, 1] : (tensor<?x8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %2344 = stablehlo.dynamic_broadcast_in_dim %223, %2342, dims = [0, 1] : (tensor<?x8821xf32>, tensor<2xindex>) -> tensor<?x8821xf32>
    %2345 = stablehlo.multiply %2343, %2344 : tensor<?x8821xf32>
    %2346 = shape.shape_of %2345 : tensor<?x8821xf32> -> tensor<2xindex>
    %head_924, %tail_925 = "shape.split_at"(%2346, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2347 = shape.broadcast %head_924, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2348 = shape.concat %2347, %tail_925 : !shape.shape, !shape.shape -> !shape.shape
    %2349 = shape.to_extent_tensor %2348 : !shape.shape -> tensor<3xindex>
    %2350 = stablehlo.dynamic_broadcast_in_dim %2345, %2349, dims = [1, 2] : (tensor<?x8821xf32>, tensor<3xindex>) -> tensor<5x?x8821xf32>
    %2351 = stablehlo.dot_general %2350, %arg526, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x8821xf32>, tensor<5x8821x128xf32>) -> tensor<5x?x128xf32>
    %2352 = shape.shape_of %2351 : tensor<5x?x128xf32> -> tensor<3xindex>
    %2353 = shape.broadcast %2352, %17 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2354 = stablehlo.dynamic_broadcast_in_dim %2351, %2353, dims = [0, 1, 2] : (tensor<5x?x128xf32>, tensor<3xindex>) -> tensor<5x?x128xf32>
    %2355 = stablehlo.dynamic_broadcast_in_dim %arg527, %2353, dims = [0, 1, 2] : (tensor<5x1x128xf32>, tensor<3xindex>) -> tensor<5x?x128xf32>
    %2356 = stablehlo.add %2354, %2355 : tensor<5x?x128xf32>
    %dim_926 = tensor.dim %2356, %c1 : tensor<5x?x128xf32>
    %2357 = arith.index_cast %dim_926 : index to i32
    %from_elements_927 = tensor.from_elements %c1_i32, %2357, %c128_i32 : tensor<3xi32>
    %2358 = stablehlo.real_dynamic_slice %2356, %cst_28, %from_elements_927, %cst_27 : (tensor<5x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_928 = tensor.collapse_shape %2358 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_929 = tensor.from_elements %c2_i32, %2357, %c128_i32 : tensor<3xi32>
    %2359 = stablehlo.real_dynamic_slice %2356, %cst_29, %from_elements_929, %cst_27 : (tensor<5x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_930 = tensor.collapse_shape %2359 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_931 = tensor.from_elements %c3_i32, %2357, %c128_i32 : tensor<3xi32>
    %2360 = stablehlo.real_dynamic_slice %2356, %cst_30, %from_elements_931, %cst_27 : (tensor<5x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_932 = tensor.collapse_shape %2360 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_933 = tensor.from_elements %c4_i32, %2357, %c128_i32 : tensor<3xi32>
    %2361 = stablehlo.real_dynamic_slice %2356, %cst_34, %from_elements_933, %cst_27 : (tensor<5x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_934 = tensor.collapse_shape %2361 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %from_elements_935 = tensor.from_elements %c5_i32, %2357, %c128_i32 : tensor<3xi32>
    %2362 = stablehlo.real_dynamic_slice %2356, %cst_35, %from_elements_935, %cst_27 : (tensor<5x?x128xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x128xf32>
    %collapsed_936 = tensor.collapse_shape %2362 [[0, 1], [2]] : tensor<1x?x128xf32> into tensor<?x128xf32>
    %2363 = stablehlo.dot %collapsed_936, %arg528, precision = [DEFAULT, DEFAULT] : (tensor<?x128xf32>, tensor<128x128xf32>) -> tensor<?x128xf32>
    %2364 = shape.shape_of %2363 : tensor<?x128xf32> -> tensor<2xindex>
    %2365 = shape.broadcast %2364, %18 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2366 = stablehlo.dynamic_broadcast_in_dim %2363, %2365, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2367 = stablehlo.dynamic_broadcast_in_dim %arg529, %2365, dims = [0, 1] : (tensor<1x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2368 = stablehlo.add %2366, %2367 : tensor<?x128xf32>
    %2369 = shape.shape_of %2368 : tensor<?x128xf32> -> tensor<2xindex>
    %2370 = shape.shape_of %collapsed_936 : tensor<?x128xf32> -> tensor<2xindex>
    %2371 = shape.broadcast %2369, %2370 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2372 = stablehlo.dynamic_broadcast_in_dim %2368, %2371, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2373 = stablehlo.dynamic_broadcast_in_dim %collapsed_936, %2371, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2374 = stablehlo.multiply %2372, %2373 : tensor<?x128xf32>
    %2375 = shape.shape_of %2374 : tensor<?x128xf32> -> tensor<2xindex>
    %2376 = shape.broadcast %2375, %2370 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2377 = stablehlo.dynamic_broadcast_in_dim %2374, %2376, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2378 = stablehlo.dynamic_broadcast_in_dim %collapsed_936, %2376, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2379 = stablehlo.add %2377, %2378 : tensor<?x128xf32>
    %2380 = shape.shape_of %2379 : tensor<?x128xf32> -> tensor<2xindex>
    %2381 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2380, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2382 = stablehlo.multiply %2379, %2381 : tensor<?x128xf32>
    %2383 = stablehlo.tanh %2382 : tensor<?x128xf32>
    %2384 = shape.shape_of %2383 : tensor<?x128xf32> -> tensor<2xindex>
    %2385 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2384, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2386 = stablehlo.multiply %2383, %2385 : tensor<?x128xf32>
    %2387 = stablehlo.reduce(%2386 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x128xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_937 = tensor.dim %2387, %c0 : tensor<?xf32>
    %from_elements_938 = tensor.from_elements %dim_937, %c1 : tensor<2xindex>
    %dim_939 = tensor.dim %2387, %c0 : tensor<?xf32>
    %expanded_940 = tensor.expand_shape %2387 [[0, 1]] output_shape [%dim_939, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2388 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_938, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2389 = stablehlo.multiply %expanded_940, %2388 : tensor<?x1xf32>
    %2390 = stablehlo.tanh %2389 : tensor<?x1xf32>
    %2391 = shape.shape_of %2390 : tensor<?x1xf32> -> tensor<2xindex>
    %2392 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2391, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2393 = stablehlo.multiply %2390, %2392 : tensor<?x1xf32>
    %2394 = shape.shape_of %collapsed_930 : tensor<?x128xf32> -> tensor<2xindex>
    %2395 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2394, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2396 = stablehlo.multiply %collapsed_930, %2395 : tensor<?x128xf32>
    %2397 = shape.shape_of %collapsed_934 : tensor<?x128xf32> -> tensor<2xindex>
    %2398 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2397, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2399 = stablehlo.multiply %collapsed_934, %2398 : tensor<?x128xf32>
    %2400 = shape.shape_of %collapsed_928 : tensor<?x128xf32> -> tensor<2xindex>
    %2401 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2400, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2402 = stablehlo.maximum %collapsed_928, %2401 : tensor<?x128xf32>
    %2403 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2394, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2404 = stablehlo.maximum %collapsed_930, %2403 : tensor<?x128xf32>
    %2405 = shape.shape_of %collapsed_932 : tensor<?x128xf32> -> tensor<2xindex>
    %2406 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2405, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2407 = stablehlo.maximum %collapsed_932, %2406 : tensor<?x128xf32>
    %2408 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2370, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2409 = stablehlo.maximum %collapsed_936, %2408 : tensor<?x128xf32>
    %2410 = shape.shape_of %2396 : tensor<?x128xf32> -> tensor<2xindex>
    %2411 = shape.broadcast %2400, %2410 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2412 = stablehlo.dynamic_broadcast_in_dim %collapsed_928, %2411, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2413 = stablehlo.dynamic_broadcast_in_dim %2396, %2411, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2414 = stablehlo.multiply %2412, %2413 : tensor<?x128xf32>
    %2415 = stablehlo.tanh %2414 : tensor<?x128xf32>
    %2416 = shape.shape_of %2415 : tensor<?x128xf32> -> tensor<2xindex>
    %2417 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2416, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2418 = stablehlo.multiply %2415, %2417 : tensor<?x128xf32>
    %2419 = stablehlo.reduce(%2418 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x128xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_941 = tensor.dim %2419, %c0 : tensor<?xf32>
    %from_elements_942 = tensor.from_elements %dim_941, %c1 : tensor<2xindex>
    %dim_943 = tensor.dim %2419, %c0 : tensor<?xf32>
    %expanded_944 = tensor.expand_shape %2419 [[0, 1]] output_shape [%dim_943, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2420 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_942, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2421 = stablehlo.multiply %expanded_944, %2420 : tensor<?x1xf32>
    %2422 = stablehlo.tanh %2421 : tensor<?x1xf32>
    %2423 = shape.shape_of %2422 : tensor<?x1xf32> -> tensor<2xindex>
    %2424 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2423, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2425 = stablehlo.multiply %2422, %2424 : tensor<?x1xf32>
    %2426 = shape.shape_of %2399 : tensor<?x128xf32> -> tensor<2xindex>
    %2427 = shape.broadcast %2405, %2426 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2428 = stablehlo.dynamic_broadcast_in_dim %collapsed_932, %2427, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2429 = stablehlo.dynamic_broadcast_in_dim %2399, %2427, dims = [0, 1] : (tensor<?x128xf32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2430 = stablehlo.multiply %2428, %2429 : tensor<?x128xf32>
    %2431 = stablehlo.tanh %2430 : tensor<?x128xf32>
    %2432 = shape.shape_of %2431 : tensor<?x128xf32> -> tensor<2xindex>
    %2433 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2432, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x128xf32>
    %2434 = stablehlo.multiply %2431, %2433 : tensor<?x128xf32>
    %2435 = stablehlo.reduce(%2434 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x128xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_945 = tensor.dim %2435, %c0 : tensor<?xf32>
    %from_elements_946 = tensor.from_elements %dim_945, %c1 : tensor<2xindex>
    %dim_947 = tensor.dim %2435, %c0 : tensor<?xf32>
    %expanded_948 = tensor.expand_shape %2435 [[0, 1]] output_shape [%dim_947, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2436 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_946, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2437 = stablehlo.multiply %expanded_948, %2436 : tensor<?x1xf32>
    %2438 = stablehlo.tanh %2437 : tensor<?x1xf32>
    %2439 = shape.shape_of %2438 : tensor<?x1xf32> -> tensor<2xindex>
    %2440 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2439, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2441 = stablehlo.multiply %2438, %2440 : tensor<?x1xf32>
    %2442 = stablehlo.concatenate %2402, %2404, %2407, %2409, %2418, %2434, %2386, %2425, %2441, %2393, dim = 1 : (tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x128xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x899xf32>
    %2443 = shape.shape_of %2442 : tensor<?x899xf32> -> tensor<2xindex>
    %2444 = shape.shape_of %268 : tensor<?x899xf32> -> tensor<2xindex>
    %2445 = shape.broadcast %2443, %2444 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2446 = stablehlo.dynamic_broadcast_in_dim %2442, %2445, dims = [0, 1] : (tensor<?x899xf32>, tensor<2xindex>) -> tensor<?x899xf32>
    %2447 = stablehlo.dynamic_broadcast_in_dim %268, %2445, dims = [0, 1] : (tensor<?x899xf32>, tensor<2xindex>) -> tensor<?x899xf32>
    %2448 = stablehlo.multiply %2446, %2447 : tensor<?x899xf32>
    %2449 = shape.shape_of %2448 : tensor<?x899xf32> -> tensor<2xindex>
    %head_949, %tail_950 = "shape.split_at"(%2449, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2450 = shape.broadcast %head_949, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2451 = shape.concat %2450, %tail_950 : !shape.shape, !shape.shape -> !shape.shape
    %2452 = shape.to_extent_tensor %2451 : !shape.shape -> tensor<3xindex>
    %2453 = stablehlo.dynamic_broadcast_in_dim %2448, %2452, dims = [1, 2] : (tensor<?x899xf32>, tensor<3xindex>) -> tensor<5x?x899xf32>
    %2454 = stablehlo.dot_general %2453, %arg530, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x899xf32>, tensor<5x899x64xf32>) -> tensor<5x?x64xf32>
    %2455 = shape.shape_of %2454 : tensor<5x?x64xf32> -> tensor<3xindex>
    %2456 = shape.broadcast %2455, %19 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2457 = stablehlo.dynamic_broadcast_in_dim %2454, %2456, dims = [0, 1, 2] : (tensor<5x?x64xf32>, tensor<3xindex>) -> tensor<5x?x64xf32>
    %2458 = stablehlo.dynamic_broadcast_in_dim %arg531, %2456, dims = [0, 1, 2] : (tensor<5x1x64xf32>, tensor<3xindex>) -> tensor<5x?x64xf32>
    %2459 = stablehlo.add %2457, %2458 : tensor<5x?x64xf32>
    %dim_951 = tensor.dim %2459, %c1 : tensor<5x?x64xf32>
    %2460 = arith.index_cast %dim_951 : index to i32
    %from_elements_952 = tensor.from_elements %c1_i32, %2460, %c64_i32 : tensor<3xi32>
    %2461 = stablehlo.real_dynamic_slice %2459, %cst_28, %from_elements_952, %cst_27 : (tensor<5x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_953 = tensor.collapse_shape %2461 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_954 = tensor.from_elements %c2_i32, %2460, %c64_i32 : tensor<3xi32>
    %2462 = stablehlo.real_dynamic_slice %2459, %cst_29, %from_elements_954, %cst_27 : (tensor<5x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_955 = tensor.collapse_shape %2462 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_956 = tensor.from_elements %c3_i32, %2460, %c64_i32 : tensor<3xi32>
    %2463 = stablehlo.real_dynamic_slice %2459, %cst_30, %from_elements_956, %cst_27 : (tensor<5x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_957 = tensor.collapse_shape %2463 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_958 = tensor.from_elements %c4_i32, %2460, %c64_i32 : tensor<3xi32>
    %2464 = stablehlo.real_dynamic_slice %2459, %cst_34, %from_elements_958, %cst_27 : (tensor<5x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_959 = tensor.collapse_shape %2464 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_960 = tensor.from_elements %c5_i32, %2460, %c64_i32 : tensor<3xi32>
    %2465 = stablehlo.real_dynamic_slice %2459, %cst_35, %from_elements_960, %cst_27 : (tensor<5x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_961 = tensor.collapse_shape %2465 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %2466 = stablehlo.dot %collapsed_961, %arg532, precision = [DEFAULT, DEFAULT] : (tensor<?x64xf32>, tensor<64x64xf32>) -> tensor<?x64xf32>
    %2467 = shape.shape_of %2466 : tensor<?x64xf32> -> tensor<2xindex>
    %2468 = shape.broadcast %2467, %20 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2469 = stablehlo.dynamic_broadcast_in_dim %2466, %2468, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2470 = stablehlo.dynamic_broadcast_in_dim %arg533, %2468, dims = [0, 1] : (tensor<1x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2471 = stablehlo.add %2469, %2470 : tensor<?x64xf32>
    %2472 = shape.shape_of %2471 : tensor<?x64xf32> -> tensor<2xindex>
    %2473 = shape.shape_of %collapsed_961 : tensor<?x64xf32> -> tensor<2xindex>
    %2474 = shape.broadcast %2472, %2473 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2475 = stablehlo.dynamic_broadcast_in_dim %2471, %2474, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2476 = stablehlo.dynamic_broadcast_in_dim %collapsed_961, %2474, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2477 = stablehlo.multiply %2475, %2476 : tensor<?x64xf32>
    %2478 = shape.shape_of %2477 : tensor<?x64xf32> -> tensor<2xindex>
    %2479 = shape.broadcast %2478, %2473 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2480 = stablehlo.dynamic_broadcast_in_dim %2477, %2479, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2481 = stablehlo.dynamic_broadcast_in_dim %collapsed_961, %2479, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2482 = stablehlo.add %2480, %2481 : tensor<?x64xf32>
    %2483 = shape.shape_of %2482 : tensor<?x64xf32> -> tensor<2xindex>
    %2484 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2483, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2485 = stablehlo.multiply %2482, %2484 : tensor<?x64xf32>
    %2486 = stablehlo.tanh %2485 : tensor<?x64xf32>
    %2487 = shape.shape_of %2486 : tensor<?x64xf32> -> tensor<2xindex>
    %2488 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2487, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2489 = stablehlo.multiply %2486, %2488 : tensor<?x64xf32>
    %2490 = stablehlo.reduce(%2489 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x64xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_962 = tensor.dim %2490, %c0 : tensor<?xf32>
    %from_elements_963 = tensor.from_elements %dim_962, %c1 : tensor<2xindex>
    %dim_964 = tensor.dim %2490, %c0 : tensor<?xf32>
    %expanded_965 = tensor.expand_shape %2490 [[0, 1]] output_shape [%dim_964, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2491 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_963, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2492 = stablehlo.multiply %expanded_965, %2491 : tensor<?x1xf32>
    %2493 = stablehlo.tanh %2492 : tensor<?x1xf32>
    %2494 = shape.shape_of %2493 : tensor<?x1xf32> -> tensor<2xindex>
    %2495 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2494, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2496 = stablehlo.multiply %2493, %2495 : tensor<?x1xf32>
    %2497 = shape.shape_of %collapsed_955 : tensor<?x64xf32> -> tensor<2xindex>
    %2498 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2497, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2499 = stablehlo.multiply %collapsed_955, %2498 : tensor<?x64xf32>
    %2500 = shape.shape_of %collapsed_959 : tensor<?x64xf32> -> tensor<2xindex>
    %2501 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2500, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2502 = stablehlo.multiply %collapsed_959, %2501 : tensor<?x64xf32>
    %2503 = shape.shape_of %collapsed_953 : tensor<?x64xf32> -> tensor<2xindex>
    %2504 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2503, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2505 = stablehlo.maximum %collapsed_953, %2504 : tensor<?x64xf32>
    %2506 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2497, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2507 = stablehlo.maximum %collapsed_955, %2506 : tensor<?x64xf32>
    %2508 = shape.shape_of %collapsed_957 : tensor<?x64xf32> -> tensor<2xindex>
    %2509 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2508, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2510 = stablehlo.maximum %collapsed_957, %2509 : tensor<?x64xf32>
    %2511 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2473, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2512 = stablehlo.maximum %collapsed_961, %2511 : tensor<?x64xf32>
    %2513 = shape.shape_of %2499 : tensor<?x64xf32> -> tensor<2xindex>
    %2514 = shape.broadcast %2503, %2513 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2515 = stablehlo.dynamic_broadcast_in_dim %collapsed_953, %2514, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2516 = stablehlo.dynamic_broadcast_in_dim %2499, %2514, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2517 = stablehlo.multiply %2515, %2516 : tensor<?x64xf32>
    %2518 = stablehlo.tanh %2517 : tensor<?x64xf32>
    %2519 = shape.shape_of %2518 : tensor<?x64xf32> -> tensor<2xindex>
    %2520 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2519, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2521 = stablehlo.multiply %2518, %2520 : tensor<?x64xf32>
    %2522 = stablehlo.reduce(%2521 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x64xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_966 = tensor.dim %2522, %c0 : tensor<?xf32>
    %from_elements_967 = tensor.from_elements %dim_966, %c1 : tensor<2xindex>
    %dim_968 = tensor.dim %2522, %c0 : tensor<?xf32>
    %expanded_969 = tensor.expand_shape %2522 [[0, 1]] output_shape [%dim_968, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2523 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_967, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2524 = stablehlo.multiply %expanded_969, %2523 : tensor<?x1xf32>
    %2525 = stablehlo.tanh %2524 : tensor<?x1xf32>
    %2526 = shape.shape_of %2525 : tensor<?x1xf32> -> tensor<2xindex>
    %2527 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2526, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2528 = stablehlo.multiply %2525, %2527 : tensor<?x1xf32>
    %2529 = shape.shape_of %2502 : tensor<?x64xf32> -> tensor<2xindex>
    %2530 = shape.broadcast %2508, %2529 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2531 = stablehlo.dynamic_broadcast_in_dim %collapsed_957, %2530, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2532 = stablehlo.dynamic_broadcast_in_dim %2502, %2530, dims = [0, 1] : (tensor<?x64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2533 = stablehlo.multiply %2531, %2532 : tensor<?x64xf32>
    %2534 = stablehlo.tanh %2533 : tensor<?x64xf32>
    %2535 = shape.shape_of %2534 : tensor<?x64xf32> -> tensor<2xindex>
    %2536 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2535, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2537 = stablehlo.multiply %2534, %2536 : tensor<?x64xf32>
    %2538 = stablehlo.reduce(%2537 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x64xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_970 = tensor.dim %2538, %c0 : tensor<?xf32>
    %from_elements_971 = tensor.from_elements %dim_970, %c1 : tensor<2xindex>
    %dim_972 = tensor.dim %2538, %c0 : tensor<?xf32>
    %expanded_973 = tensor.expand_shape %2538 [[0, 1]] output_shape [%dim_972, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2539 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_971, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2540 = stablehlo.multiply %expanded_973, %2539 : tensor<?x1xf32>
    %2541 = stablehlo.tanh %2540 : tensor<?x1xf32>
    %2542 = shape.shape_of %2541 : tensor<?x1xf32> -> tensor<2xindex>
    %2543 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2542, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2544 = stablehlo.multiply %2541, %2543 : tensor<?x1xf32>
    %2545 = stablehlo.concatenate %2505, %2507, %2510, %2512, %2521, %2537, %2489, %2528, %2544, %2496, dim = 1 : (tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x451xf32>
    %2546 = shape.shape_of %2545 : tensor<?x451xf32> -> tensor<2xindex>
    %2547 = shape.shape_of %283 : tensor<?x451xf32> -> tensor<2xindex>
    %2548 = shape.broadcast %2546, %2547 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2549 = stablehlo.dynamic_broadcast_in_dim %2545, %2548, dims = [0, 1] : (tensor<?x451xf32>, tensor<2xindex>) -> tensor<?x451xf32>
    %2550 = stablehlo.dynamic_broadcast_in_dim %283, %2548, dims = [0, 1] : (tensor<?x451xf32>, tensor<2xindex>) -> tensor<?x451xf32>
    %2551 = stablehlo.multiply %2549, %2550 : tensor<?x451xf32>
    %2552 = shape.shape_of %2551 : tensor<?x451xf32> -> tensor<2xindex>
    %head_974, %tail_975 = "shape.split_at"(%2552, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2553 = shape.broadcast %head_974, %10 : !shape.shape, !shape.shape -> !shape.shape
    %2554 = shape.concat %2553, %tail_975 : !shape.shape, !shape.shape -> !shape.shape
    %2555 = shape.to_extent_tensor %2554 : !shape.shape -> tensor<3xindex>
    %2556 = stablehlo.dynamic_broadcast_in_dim %2551, %2555, dims = [1, 2] : (tensor<?x451xf32>, tensor<3xindex>) -> tensor<5x?x451xf32>
    %2557 = stablehlo.dot_general %2556, %arg534, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<5x?x451xf32>, tensor<5x451x16xf32>) -> tensor<5x?x16xf32>
    %2558 = shape.shape_of %2557 : tensor<5x?x16xf32> -> tensor<3xindex>
    %2559 = shape.broadcast %2558, %21 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2560 = stablehlo.dynamic_broadcast_in_dim %2557, %2559, dims = [0, 1, 2] : (tensor<5x?x16xf32>, tensor<3xindex>) -> tensor<5x?x16xf32>
    %2561 = stablehlo.dynamic_broadcast_in_dim %arg535, %2559, dims = [0, 1, 2] : (tensor<5x1x16xf32>, tensor<3xindex>) -> tensor<5x?x16xf32>
    %2562 = stablehlo.add %2560, %2561 : tensor<5x?x16xf32>
    %dim_976 = tensor.dim %2562, %c1 : tensor<5x?x16xf32>
    %2563 = arith.index_cast %dim_976 : index to i32
    %from_elements_977 = tensor.from_elements %c1_i32, %2563, %c16_i32 : tensor<3xi32>
    %2564 = stablehlo.real_dynamic_slice %2562, %cst_28, %from_elements_977, %cst_27 : (tensor<5x?x16xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x16xf32>
    %collapsed_978 = tensor.collapse_shape %2564 [[0, 1], [2]] : tensor<1x?x16xf32> into tensor<?x16xf32>
    %from_elements_979 = tensor.from_elements %c2_i32, %2563, %c16_i32 : tensor<3xi32>
    %2565 = stablehlo.real_dynamic_slice %2562, %cst_29, %from_elements_979, %cst_27 : (tensor<5x?x16xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x16xf32>
    %collapsed_980 = tensor.collapse_shape %2565 [[0, 1], [2]] : tensor<1x?x16xf32> into tensor<?x16xf32>
    %from_elements_981 = tensor.from_elements %c3_i32, %2563, %c16_i32 : tensor<3xi32>
    %2566 = stablehlo.real_dynamic_slice %2562, %cst_30, %from_elements_981, %cst_27 : (tensor<5x?x16xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x16xf32>
    %collapsed_982 = tensor.collapse_shape %2566 [[0, 1], [2]] : tensor<1x?x16xf32> into tensor<?x16xf32>
    %from_elements_983 = tensor.from_elements %c4_i32, %2563, %c16_i32 : tensor<3xi32>
    %2567 = stablehlo.real_dynamic_slice %2562, %cst_34, %from_elements_983, %cst_27 : (tensor<5x?x16xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x16xf32>
    %collapsed_984 = tensor.collapse_shape %2567 [[0, 1], [2]] : tensor<1x?x16xf32> into tensor<?x16xf32>
    %from_elements_985 = tensor.from_elements %c5_i32, %2563, %c16_i32 : tensor<3xi32>
    %2568 = stablehlo.real_dynamic_slice %2562, %cst_35, %from_elements_985, %cst_27 : (tensor<5x?x16xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x16xf32>
    %collapsed_986 = tensor.collapse_shape %2568 [[0, 1], [2]] : tensor<1x?x16xf32> into tensor<?x16xf32>
    %2569 = stablehlo.dot %collapsed_986, %arg536, precision = [DEFAULT, DEFAULT] : (tensor<?x16xf32>, tensor<16x16xf32>) -> tensor<?x16xf32>
    %2570 = shape.shape_of %2569 : tensor<?x16xf32> -> tensor<2xindex>
    %2571 = shape.broadcast %2570, %22 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2572 = stablehlo.dynamic_broadcast_in_dim %2569, %2571, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2573 = stablehlo.dynamic_broadcast_in_dim %arg537, %2571, dims = [0, 1] : (tensor<1x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2574 = stablehlo.add %2572, %2573 : tensor<?x16xf32>
    %2575 = shape.shape_of %2574 : tensor<?x16xf32> -> tensor<2xindex>
    %2576 = shape.shape_of %collapsed_986 : tensor<?x16xf32> -> tensor<2xindex>
    %2577 = shape.broadcast %2575, %2576 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2578 = stablehlo.dynamic_broadcast_in_dim %2574, %2577, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2579 = stablehlo.dynamic_broadcast_in_dim %collapsed_986, %2577, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2580 = stablehlo.multiply %2578, %2579 : tensor<?x16xf32>
    %2581 = shape.shape_of %2580 : tensor<?x16xf32> -> tensor<2xindex>
    %2582 = shape.broadcast %2581, %2576 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2583 = stablehlo.dynamic_broadcast_in_dim %2580, %2582, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2584 = stablehlo.dynamic_broadcast_in_dim %collapsed_986, %2582, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2585 = stablehlo.add %2583, %2584 : tensor<?x16xf32>
    %2586 = shape.shape_of %2585 : tensor<?x16xf32> -> tensor<2xindex>
    %2587 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2586, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2588 = stablehlo.multiply %2585, %2587 : tensor<?x16xf32>
    %2589 = stablehlo.tanh %2588 : tensor<?x16xf32>
    %2590 = shape.shape_of %2589 : tensor<?x16xf32> -> tensor<2xindex>
    %2591 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2590, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2592 = stablehlo.multiply %2589, %2591 : tensor<?x16xf32>
    %2593 = stablehlo.reduce(%2592 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x16xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_987 = tensor.dim %2593, %c0 : tensor<?xf32>
    %from_elements_988 = tensor.from_elements %dim_987, %c1 : tensor<2xindex>
    %dim_989 = tensor.dim %2593, %c0 : tensor<?xf32>
    %expanded_990 = tensor.expand_shape %2593 [[0, 1]] output_shape [%dim_989, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2594 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_988, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2595 = stablehlo.multiply %expanded_990, %2594 : tensor<?x1xf32>
    %2596 = stablehlo.tanh %2595 : tensor<?x1xf32>
    %2597 = shape.shape_of %2596 : tensor<?x1xf32> -> tensor<2xindex>
    %2598 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2597, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2599 = stablehlo.multiply %2596, %2598 : tensor<?x1xf32>
    %2600 = shape.shape_of %collapsed_980 : tensor<?x16xf32> -> tensor<2xindex>
    %2601 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2600, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2602 = stablehlo.multiply %collapsed_980, %2601 : tensor<?x16xf32>
    %2603 = shape.shape_of %collapsed_984 : tensor<?x16xf32> -> tensor<2xindex>
    %2604 = stablehlo.dynamic_broadcast_in_dim %cst_0, %2603, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2605 = stablehlo.multiply %collapsed_984, %2604 : tensor<?x16xf32>
    %2606 = shape.shape_of %collapsed_978 : tensor<?x16xf32> -> tensor<2xindex>
    %2607 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2606, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2608 = stablehlo.maximum %collapsed_978, %2607 : tensor<?x16xf32>
    %2609 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2600, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2610 = stablehlo.maximum %collapsed_980, %2609 : tensor<?x16xf32>
    %2611 = shape.shape_of %collapsed_982 : tensor<?x16xf32> -> tensor<2xindex>
    %2612 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2611, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2613 = stablehlo.maximum %collapsed_982, %2612 : tensor<?x16xf32>
    %2614 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2576, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2615 = stablehlo.maximum %collapsed_986, %2614 : tensor<?x16xf32>
    %2616 = shape.shape_of %2602 : tensor<?x16xf32> -> tensor<2xindex>
    %2617 = shape.broadcast %2606, %2616 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2618 = stablehlo.dynamic_broadcast_in_dim %collapsed_978, %2617, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2619 = stablehlo.dynamic_broadcast_in_dim %2602, %2617, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2620 = stablehlo.multiply %2618, %2619 : tensor<?x16xf32>
    %2621 = stablehlo.tanh %2620 : tensor<?x16xf32>
    %2622 = shape.shape_of %2621 : tensor<?x16xf32> -> tensor<2xindex>
    %2623 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2622, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2624 = stablehlo.multiply %2621, %2623 : tensor<?x16xf32>
    %2625 = stablehlo.reduce(%2624 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x16xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_991 = tensor.dim %2625, %c0 : tensor<?xf32>
    %from_elements_992 = tensor.from_elements %dim_991, %c1 : tensor<2xindex>
    %dim_993 = tensor.dim %2625, %c0 : tensor<?xf32>
    %expanded_994 = tensor.expand_shape %2625 [[0, 1]] output_shape [%dim_993, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2626 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_992, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2627 = stablehlo.multiply %expanded_994, %2626 : tensor<?x1xf32>
    %2628 = stablehlo.tanh %2627 : tensor<?x1xf32>
    %2629 = shape.shape_of %2628 : tensor<?x1xf32> -> tensor<2xindex>
    %2630 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2629, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2631 = stablehlo.multiply %2628, %2630 : tensor<?x1xf32>
    %2632 = shape.shape_of %2605 : tensor<?x16xf32> -> tensor<2xindex>
    %2633 = shape.broadcast %2611, %2632 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2634 = stablehlo.dynamic_broadcast_in_dim %collapsed_982, %2633, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2635 = stablehlo.dynamic_broadcast_in_dim %2605, %2633, dims = [0, 1] : (tensor<?x16xf32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2636 = stablehlo.multiply %2634, %2635 : tensor<?x16xf32>
    %2637 = stablehlo.tanh %2636 : tensor<?x16xf32>
    %2638 = shape.shape_of %2637 : tensor<?x16xf32> -> tensor<2xindex>
    %2639 = stablehlo.dynamic_broadcast_in_dim %cst_13, %2638, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x16xf32>
    %2640 = stablehlo.multiply %2637, %2639 : tensor<?x16xf32>
    %2641 = stablehlo.reduce(%2640 init: %cst_21) applies stablehlo.add across dimensions = [1] : (tensor<?x16xf32>, tensor<f32>) -> tensor<?xf32>
    %dim_995 = tensor.dim %2641, %c0 : tensor<?xf32>
    %from_elements_996 = tensor.from_elements %dim_995, %c1 : tensor<2xindex>
    %dim_997 = tensor.dim %2641, %c0 : tensor<?xf32>
    %expanded_998 = tensor.expand_shape %2641 [[0, 1]] output_shape [%dim_997, 1] : tensor<?xf32> into tensor<?x1xf32>
    %2642 = stablehlo.dynamic_broadcast_in_dim %cst_14, %from_elements_996, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2643 = stablehlo.multiply %expanded_998, %2642 : tensor<?x1xf32>
    %2644 = stablehlo.tanh %2643 : tensor<?x1xf32>
    %2645 = shape.shape_of %2644 : tensor<?x1xf32> -> tensor<2xindex>
    %2646 = stablehlo.dynamic_broadcast_in_dim %cst_15, %2645, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x1xf32>
    %2647 = stablehlo.multiply %2644, %2646 : tensor<?x1xf32>
    %2648 = stablehlo.concatenate %2608, %2610, %2613, %2615, %2624, %2640, %2592, %2631, %2647, %2599, dim = 1 : (tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x1xf32>, tensor<?x1xf32>, tensor<?x1xf32>) -> tensor<?x115xf32>
    %2649 = shape.shape_of %2648 : tensor<?x115xf32> -> tensor<2xindex>
    %2650 = shape.shape_of %298 : tensor<?x115xf32> -> tensor<2xindex>
    %2651 = shape.broadcast %2649, %2650 : tensor<2xindex>, tensor<2xindex> -> tensor<2xindex>
    %2652 = stablehlo.dynamic_broadcast_in_dim %2648, %2651, dims = [0, 1] : (tensor<?x115xf32>, tensor<2xindex>) -> tensor<?x115xf32>
    %2653 = stablehlo.dynamic_broadcast_in_dim %298, %2651, dims = [0, 1] : (tensor<?x115xf32>, tensor<2xindex>) -> tensor<?x115xf32>
    %2654 = stablehlo.multiply %2652, %2653 : tensor<?x115xf32>
    %2655 = stablehlo.dot %2654, %arg538, precision = [DEFAULT, DEFAULT] : (tensor<?x115xf32>, tensor<115x64xf32>) -> tensor<?x64xf32>
    %2656 = shape.shape_of %2655 : tensor<?x64xf32> -> tensor<2xindex>
    %2657 = stablehlo.dynamic_broadcast_in_dim %arg539, %2656, dims = [1] : (tensor<64xf32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2658 = stablehlo.add %2655, %2657 : tensor<?x64xf32>
    %2659 = shape.shape_of %2658 : tensor<?x64xf32> -> tensor<2xindex>
    %2660 = stablehlo.dynamic_broadcast_in_dim %cst_22, %2659, dims = [] : (tensor<f32>, tensor<2xindex>) -> tensor<?x64xf32>
    %2661 = stablehlo.maximum %2658, %2660 : tensor<?x64xf32>
    %2662 = stablehlo.concatenate %181, %2661, %arg540, dim = 1 : (tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x1xf32>) -> tensor<?x129xf32>
    %2663 = shape.shape_of %2662 : tensor<?x129xf32> -> tensor<2xindex>
    %head_999, %tail_1000 = "shape.split_at"(%2663, %c-2) : (tensor<2xindex>, index) -> (!shape.shape, !shape.shape)
    %2664 = shape.broadcast %head_999, %23 : !shape.shape, !shape.shape -> !shape.shape
    %2665 = shape.concat %2664, %tail_1000 : !shape.shape, !shape.shape -> !shape.shape
    %2666 = shape.to_extent_tensor %2665 : !shape.shape -> tensor<3xindex>
    %2667 = stablehlo.dynamic_broadcast_in_dim %2662, %2666, dims = [1, 2] : (tensor<?x129xf32>, tensor<3xindex>) -> tensor<14x?x129xf32>
    %2668 = stablehlo.dot_general %2667, %arg541, batching_dims = [0] x [0], contracting_dims = [2] x [1], precision = [DEFAULT, DEFAULT] : (tensor<14x?x129xf32>, tensor<14x129x64xf32>) -> tensor<14x?x64xf32>
    %2669 = shape.shape_of %2668 : tensor<14x?x64xf32> -> tensor<3xindex>
    %2670 = shape.broadcast %2669, %24 : tensor<3xindex>, tensor<3xindex> -> tensor<3xindex>
    %2671 = stablehlo.dynamic_broadcast_in_dim %2668, %2670, dims = [0, 1, 2] : (tensor<14x?x64xf32>, tensor<3xindex>) -> tensor<14x?x64xf32>
    %2672 = stablehlo.dynamic_broadcast_in_dim %arg542, %2670, dims = [0, 1, 2] : (tensor<14x1x64xf32>, tensor<3xindex>) -> tensor<14x?x64xf32>
    %2673 = stablehlo.add %2671, %2672 : tensor<14x?x64xf32>
    %dim_1001 = tensor.dim %2673, %c1 : tensor<14x?x64xf32>
    %2674 = arith.index_cast %dim_1001 : index to i32
    %from_elements_1002 = tensor.from_elements %c1_i32, %2674, %c64_i32 : tensor<3xi32>
    %2675 = stablehlo.real_dynamic_slice %2673, %cst_28, %from_elements_1002, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1003 = tensor.collapse_shape %2675 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1004 = tensor.from_elements %c2_i32, %2674, %c64_i32 : tensor<3xi32>
    %2676 = stablehlo.real_dynamic_slice %2673, %cst_29, %from_elements_1004, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1005 = tensor.collapse_shape %2676 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1006 = tensor.from_elements %c3_i32, %2674, %c64_i32 : tensor<3xi32>
    %2677 = stablehlo.real_dynamic_slice %2673, %cst_30, %from_elements_1006, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1007 = tensor.collapse_shape %2677 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1008 = tensor.from_elements %c4_i32, %2674, %c64_i32 : tensor<3xi32>
    %2678 = stablehlo.real_dynamic_slice %2673, %cst_34, %from_elements_1008, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1009 = tensor.collapse_shape %2678 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1010 = tensor.from_elements %c5_i32, %2674, %c64_i32 : tensor<3xi32>
    %2679 = stablehlo.real_dynamic_slice %2673, %cst_35, %from_elements_1010, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1011 = tensor.collapse_shape %2679 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1012 = tensor.from_elements %c6_i32, %2674, %c64_i32 : tensor<3xi32>
    %2680 = stablehlo.real_dynamic_slice %2673, %cst_36, %from_elements_1012, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1013 = tensor.collapse_shape %2680 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1014 = tensor.from_elements %c7_i32, %2674, %c64_i32 : tensor<3xi32>
    %2681 = stablehlo.real_dynamic_slice %2673, %cst_37, %from_elements_1014, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1015 = tensor.collapse_shape %2681 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1016 = tensor.from_elements %c8_i32, %2674, %c64_i32 : tensor<3xi32>
    %2682 = stablehlo.real_dynamic_slice %2673, %cst_38, %from_elements_1016, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1017 = tensor.collapse_shape %2682 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1018 = tensor.from_elements %c9_i32, %2674, %c64_i32 : tensor<3xi32>
    %2683 = stablehlo.real_dynamic_slice %2673, %cst_39, %from_elements_1018, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1019 = tensor.collapse_shape %2683 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1020 = tensor.from_elements %c10_i32, %2674, %c64_i32 : tensor<3xi32>
    %2684 = stablehlo.real_dynamic_slice %2673, %cst_40, %from_elements_1020, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1021 = tensor.collapse_shape %2684 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1022 = tensor.from_elements %c11_i32, %2674, %c64_i32 : tensor<3xi32>
    %2685 = stablehlo.real_dynamic_slice %2673, %cst_41, %from_elements_1022, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1023 = tensor.collapse_shape %2685 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1024 = tensor.from_elements %c12_i32, %2674, %c64_i32 : tensor<3xi32>
    %2686 = stablehlo.real_dynamic_slice %2673, %cst_42, %from_elements_1024, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1025 = tensor.collapse_shape %2686 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1026 = tensor.from_elements %c13_i32, %2674, %c64_i32 : tensor<3xi32>
    %2687 = stablehlo.real_dynamic_slice %2673, %cst_43, %from_elements_1026, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1027 = tensor.collapse_shape %2687 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %from_elements_1028 = tensor.from_elements %c14_i32, %2674, %c64_i32 : tensor<3xi32>
    %2688 = stablehlo.real_dynamic_slice %2673, %cst_44, %from_elements_1028, %cst_27 : (tensor<14x?x64xf32>, tensor<3xi32>, tensor<3xi32>, tensor<3xi32>) -> tensor<1x?x64xf32>
    %collapsed_1029 = tensor.collapse_shape %2688 [[0, 1], [2]] : tensor<1x?x64xf32> into tensor<?x64xf32>
    %2689 = stablehlo.dot %2018, %arg543, precision = [DEFAULT, DEFAULT] : (tensor<?x8821xf32>, tensor<8821x2592xf32>) -> tensor<?x2592xf32>
    %2690 = shape.shape_of %2689 : tensor<?x2592xf32> -> tensor<2xindex>
    %2691 = stablehlo.dynamic_broadcast_in_dim %arg544, %2690, dims = [1] : (tensor<2592xf32>, tensor<2xindex>) -> tensor<?x2592xf32>
    %2692 = stablehlo.add %2689, %2691 : tensor<?x2592xf32>
    %2693 = stablehlo.concatenate %arg292, %arg293, %arg294, %arg295, %arg296, %arg297, %arg298, %arg299, %arg300, %collapsed_838, %collapsed_843, %collapsed_848, %arg301, %arg302, %arg303, %arg304, %arg305, %arg306, %arg307, %arg308, %arg309, %arg310, %arg311, %arg312, %arg313, %arg314, %arg315, %arg316, %arg317, %arg318, %arg319, %arg320, %arg321, %arg322, %arg323, %arg324, %arg325, %arg326, %arg327, %arg328, %arg329, %arg330, %arg331, %arg332, %arg333, %arg334, %arg335, %arg336, %arg337, %arg338, %arg339, %arg340, %arg341, %arg342, %arg343, %arg344, %arg345, %arg346, %arg347, %arg348, %arg349, %arg350, %arg351, %arg352, %arg353, %arg354, %arg355, %arg356, %arg357, %arg358, %arg359, %arg360, %arg361, %arg362, %arg363, %arg364, %arg365, %arg366, %arg367, %arg368, %arg369, %arg370, %arg371, %arg372, %arg373, %arg374, %arg375, %arg376, %arg377, %arg378, %arg379, %arg380, %arg381, %arg382, %arg383, %arg384, %arg385, %arg386, %arg387, %arg388, %arg389, %arg390, %arg391, %arg392, %arg393, %arg394, %arg395, %arg396, %arg397, %arg398, %arg399, %arg400, %arg401, %arg402, %arg403, %arg404, %arg405, %arg406, %arg407, %arg408, %arg409, %arg410, %arg411, %arg412, %arg413, %arg414, %arg415, %arg416, %collapsed_211, %arg417, %arg418, %arg419, %arg420, %arg421, %arg422, %arg423, %arg424, %arg425, %arg426, %arg427, %arg428, %arg429, %arg430, %arg431, %arg432, %arg433, %arg434, %arg435, %arg436, %arg437, %arg438, %arg439, %arg440, %arg441, %arg442, %arg443, %arg444, %collapsed_93, %321, %collapsed_484, %322, %collapsed_231, %478, %collapsed_426, %collapsed_455, %collapsed_601, %collapsed_833, %collapsed_717, %2340, dim = 1 : (tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x105xf32>, tensor<?x84xf32>, tensor<?x100xf32>, tensor<?x180xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x16xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x76xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x4xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x16xf32>, tensor<?x48xf32>, tensor<?x16xf32>, tensor<?x16xf32>, tensor<?x32xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x8xf32>, tensor<?x32xf32>, tensor<?x68xf32>, tensor<?x32xf32>, tensor<?x104xf32>, tensor<?x64xf32>, tensor<?x88xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x452xf32>) -> tensor<?x3393xf32>
    %2694 = stablehlo.transpose %c, dims = [1, 0] : (tensor<2x2xi32>) -> tensor<2x2xi32>
    %2695 = stablehlo.reshape %2694 : (tensor<2x2xi32>) -> tensor<4xi32>
    %2696 = stablehlo.slice %2695 [0:2] : (tensor<4xi32>) -> tensor<2xi32>
    %2697 = stablehlo.slice %2695 [2:4] : (tensor<4xi32>) -> tensor<2xi32>
    %2698 = stablehlo.dynamic_pad %2693, %cst_22, %2696, %2697, %c_45 : (tensor<?x3393xf32>, tensor<f32>, tensor<2xi32>, tensor<2xi32>, tensor<2xi32>) -> tensor<?x3408xf32>
    return %181, %collapsed_152, %collapsed_182, %collapsed_231, %collapsed_426, %collapsed_1003, %collapsed_1005, %collapsed_1007, %collapsed_1009, %collapsed_1011, %collapsed_1013, %collapsed_1015, %collapsed_1017, %collapsed_1019, %collapsed_1021, %collapsed_1023, %collapsed_1025, %collapsed_1027, %collapsed_1029, %2692, %2698 : tensor<?x64xf32>, tensor<?x32xf32>, tensor<?x32xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x64xf32>, tensor<?x2592xf32>, tensor<?x3408xf32>
  }
}

