
/tmp/lark-awq-compiler-preflight-v1-20261112/m17_k32_n64.gfx950.elf:	file format elf64-amdgpu

Disassembly of section .text:

0000000000001700 <awq_fp16_gemm>:
	v_lshrrev_b32_e32 v3, 5, v0                                // 000000001700: 20060085
	s_load_dwordx4 s[4:7], s[0:1], 0x0                         // 000000001704: C00A0100 00000000
	s_load_dwordx2 s[8:9], s[0:1], 0x10                        // 00000000170C: C0060200 00000010
	s_lshl_b32 s2, s2, 4                                       // 000000001714: 8E028402
	v_lshlrev_b32_e32 v1, 3, v3                                // 000000001718: 24020683
	v_add_u32_e32 v2, s2, v1                                   // 00000000171C: 68040202
	v_bfe_u32 v5, v0, 2, 3                                     // 000000001720: D1C80005 020D0500
	v_lshlrev_b32_e32 v4, 3, v0                                // 000000001728: 24080083
	v_or_b32_e32 v8, v2, v5                                    // 00000000172C: 28100B02
	v_and_b32_e32 v9, 24, v4                                   // 000000001730: 26120898
	v_or_b32_e32 v2, v1, v5                                    // 000000001734: 28040B01
	v_lshrrev_b32_e32 v5, 2, v0                                // 000000001738: 200A0082
	v_mul_u32_u24_e32 v2, 0x50, v2                             // 00000000173C: 100404FF 00000050
	v_lshlrev_b32_e32 v6, 1, v9                                // 000000001744: 240C1281
	s_movk_i32 s0, 0x1200                                      // 000000001748: B0001200
	v_and_b32_e32 v1, 0xfc, v5                                 // 00000000174C: 26020AFF 000000FC
	v_cmp_lt_i32_e32 vcc, 16, v8                               // 000000001754: 7D821090
	v_add3_u32 v2, v2, v6, s0                                  // 000000001758: D1FF0002 00020D02
	v_and_b32_e32 v20, 15, v0                                  // 000000001760: 2628008F
	v_or_b32_e32 v6, 3, v5                                     // 000000001764: 280C0A83
	s_waitcnt lgkmcnt(0)                                       // 000000001768: BF8CC07F
	s_barrier                                                  // 00000000176C: BF8A0000
	s_and_saveexec_b64 s[0:1], vcc                             // 000000001770: BE80206A
	s_xor_b64 s[0:1], exec, s[0:1]                             // 000000001774: 8880007E
	s_cbranch_execz 7                                          // 000000001778: BF880007 <awq_fp16_gemm+0x98>
	v_mov_b32_e32 v8, 0                                        // 00000000177C: 7E100280
	v_mov_b32_e32 v9, v8                                       // 000000001780: 7E120308
	v_mov_b32_e32 v10, v8                                      // 000000001784: 7E140308
	ds_write_b96 v2, v[8:10]                                   // 000000001788: D9BC0000 00000802
	ds_write_b16 v2, v8 offset:12                              // 000000001790: D83E000C 00000802
	s_or_saveexec_b64 s[0:1], s[0:1]                           // 000000001798: BE802100
	v_and_b32_e32 v10, 31, v0                                  // 00000000179C: 2614009F
	v_mul_u32_u24_e32 v0, 40, v20                              // 0000000017A0: 100028A8
	v_mul_u32_u24_e32 v5, 0x90, v1                             // 0000000017A4: 100A02FF 00000090
	v_mul_u32_u24_e32 v6, 0x90, v6                             // 0000000017AC: 100C0CFF 00000090
	v_mov_b32_e32 v7, 0                                        // 0000000017B4: 7E0E0280
	s_xor_b64 exec, exec, s[0:1]                               // 0000000017B8: 88FE007E
	s_cbranch_execz 15                                         // 0000000017BC: BF88000F <awq_fp16_gemm+0xfc>
	v_lshl_or_b32 v8, v8, 5, v9                                // 0000000017C0: D2000008 04250B08
	v_mov_b32_e32 v12, s4                                      // 0000000017C8: 7E180204
	v_mov_b32_e32 v13, s5                                      // 0000000017CC: 7E1A0205
	v_ashrrev_i32_e32 v9, 31, v8                               // 0000000017D0: 2212109F
	v_lshl_add_u64 v[8:9], v[8:9], 1, v[12:13]                 // 0000000017D4: D2080008 04310308
	global_load_dwordx4 v[12:15], v[8:9], off                  // 0000000017DC: DC5C8000 0C7F0008
	s_waitcnt vmcnt(0)                                         // 0000000017E4: BF8C0F70
	ds_write_b96 v2, v[12:14]                                  // 0000000017E8: D9BC0000 00000C02
	ds_write_b16 v2, v15 offset:12                             // 0000000017F0: D83E000C 00000F02
	v_lshrrev_b32_e32 v7, 16, v15                              // 0000000017F8: 200E1E90
	s_or_b64 exec, exec, s[0:1]                                // 0000000017FC: 87FE007E
	v_lshrrev_b32_e32 v8, 3, v10                               // 000000001800: 20101483
	v_lshl_or_b32 v3, v3, 2, v8                                // 000000001804: D2000003 04210503
	v_and_b32_e32 v4, 56, v4                                   // 00000000180C: 260808B8
	v_lshl_or_b32 v8, v3, 6, v4                                // 000000001810: D2000008 04110D03
	v_lshlrev_b32_e32 v16, 1, v8                               // 000000001818: 24201081
	v_add_u32_e32 v17, 0x400, v16                              // 00000000181C: 682220FF 00000400
	v_add_u32_e32 v21, 0x800, v16                              // 000000001824: 682A20FF 00000800
	global_load_dwordx4 v[8:11], v16, s[6:7]                   // 00000000182C: DC5C8000 08060010
	global_load_dwordx4 v[12:15], v17, s[6:7]                  // 000000001834: DC5C8000 0C060011
	v_add_u32_e32 v26, 0xc00, v16                              // 00000000183C: 683420FF 00000C00
	global_load_dwordx4 v[16:19], v21, s[6:7]                  // 000000001844: DC5C8000 10060015
	global_load_dwordx4 v[22:25], v26, s[6:7]                  // 00000000184C: DC5C8000 1606001A
	v_lshlrev_b32_e32 v21, 1, v1                               // 000000001854: 242A0281
	v_lshl_add_u32 v0, v0, 1, v21                              // 000000001858: D1FD0000 04550300
	v_mul_u32_u24_e32 v3, 0x90, v3                             // 000000001860: 100606FF 00000090
	v_lshlrev_b32_e32 v26, 1, v20                              // 000000001868: 24342881
	v_add_u32_e32 v0, 0x1000, v0                               // 00000000186C: 680000FF 00001000
	v_lshl_add_u32 v3, v4, 1, v3                               // 000000001874: D1FD0003 040D0304
	ds_write_b16 v2, v7 offset:14                              // 00000000187C: D83E000E 00000702
	v_add_u32_e32 v30, v5, v26                                 // 000000001884: 683C3505
	v_add_u32_e32 v2, v6, v26                                  // 000000001888: 68043506
	s_mov_b32 s0, 0x5040100                                    // 00000000188C: BE8000FF 05040100
	s_waitcnt vmcnt(3)                                         // 000000001894: BF8C0F73
	ds_write_b128 v3, v[8:11]                                  // 000000001898: D9BE0000 00000803
	s_waitcnt vmcnt(2)                                         // 0000000018A0: BF8C0F72
	ds_write_b128 v3, v[12:15] offset:1152                     // 0000000018A4: D9BE0480 00000C03
	s_waitcnt vmcnt(1)                                         // 0000000018AC: BF8C0F71
	ds_write_b128 v3, v[16:19] offset:2304                     // 0000000018B0: D9BE0900 00001003
	s_waitcnt vmcnt(0)                                         // 0000000018B8: BF8C0F70
	ds_write_b128 v3, v[22:25] offset:3456                     // 0000000018BC: D9BE0D80 00001603
	s_waitcnt lgkmcnt(0)                                       // 0000000018C4: BF8CC07F
	s_barrier                                                  // 0000000018C8: BF8A0000
	ds_read2_b64 v[14:17], v0 offset0:64 offset1:68            // 0000000018CC: D8EE4440 0E000000
	ds_read_u16 v0, v30 offset:144                             // 0000000018D4: D8780090 0000001E
	ds_read_u16 v4, v30                                        // 0000000018DC: D8780000 0400001E
	ds_read_u16 v6, v30 offset:32                              // 0000000018E4: D8780020 0600001E
	ds_read_u16 v8, v30 offset:176                             // 0000000018EC: D87800B0 0800001E
	ds_read_u16 v10, v30 offset:64                             // 0000000018F4: D8780040 0A00001E
	ds_read_u16 v12, v30 offset:208                            // 0000000018FC: D87800D0 0C00001E
	ds_read_u16 v13, v30 offset:240                            // 000000001904: D87800F0 0D00001E
	ds_read_u16 v18, v30 offset:96                             // 00000000190C: D8780060 1200001E
	ds_read_u16 v3, v30 offset:288                             // 000000001914: D8780120 0300001E
	ds_read_u16 v7, v30 offset:320                             // 00000000191C: D8780140 0700001E
	ds_read_u16 v11, v30 offset:352                            // 000000001924: D8780160 0B00001E
	ds_read_u16 v19, v30 offset:384                            // 00000000192C: D8780180 1300001E
	ds_read_u16 v21, v30 offset:2304                           // 000000001934: D8780900 1500001E
	ds_read_u16 v31, v30 offset:2336                           // 00000000193C: D8780920 1F00001E
	ds_read_u16 v32, v30 offset:2368                           // 000000001944: D8780940 2000001E
	ds_read_u16 v33, v30 offset:2400                           // 00000000194C: D8780960 2100001E
	ds_read_u16 v5, v2                                         // 000000001954: D8780000 05000002
	ds_read_u16 v9, v2 offset:32                               // 00000000195C: D8780020 09000002
	ds_read_u16 v22, v2 offset:64                              // 000000001964: D8780040 16000002
	ds_read_u16 v26, v2 offset:96                              // 00000000196C: D8780060 1A000002
	ds_read_u16 v34, v30 offset:2832                           // 000000001974: D8780B10 2200001E
	s_waitcnt lgkmcnt(14)                                      // 00000000197C: BF8CCE7F
	v_perm_b32 v10, v12, v10, s0                               // 000000001980: D1ED000A 0002150C
	s_waitcnt lgkmcnt(4)                                       // 000000001988: BF8CC47F
	v_perm_b32 v3, v5, v3, s0                                  // 00000000198C: D1ED0003 00020705
	s_waitcnt lgkmcnt(2)                                       // 000000001994: BF8CC27F
	v_perm_b32 v11, v22, v11, s0                               // 000000001998: D1ED000B 00021716
	v_perm_b32 v2, v0, v4, s0                                  // 0000000019A0: D1ED0002 00020900
	v_perm_b32 v7, v9, v7, s0                                  // 0000000019A8: D1ED0007 00020F09
	v_mfma_f32_16x16x16_f16 v[22:25], v[14:15], v[10:11], 0    // 0000000019B0: D3CD0016 0202150E
	s_waitcnt lgkmcnt(1)                                       // 0000000019B8: BF8CC17F
	v_perm_b32 v11, v26, v19, s0                               // 0000000019BC: D1ED000B 0002271A
	v_perm_b32 v10, v13, v18, s0                               // 0000000019C4: D1ED000A 0002250D
	v_perm_b32 v6, v8, v6, s0                                  // 0000000019CC: D1ED0006 00020D08
	v_mfma_f32_16x16x16_f16 v[2:5], v[14:15], v[2:3], 0        // 0000000019D4: D3CD0002 0202050E
	ds_read_u16 v0, v30 offset:2736                            // 0000000019DC: D8780AB0 0000001E
	ds_read_u16 v35, v30 offset:2768                           // 0000000019E4: D8780AD0 2300001E
	ds_read_u16 v36, v30 offset:2800                           // 0000000019EC: D8780AF0 2400001E
	v_mfma_f32_16x16x16_f16 v[26:29], v[14:15], v[10:11], 0    // 0000000019F4: D3CD001A 0202150E
	ds_read_u16 v10, v30 offset:2448                           // 0000000019FC: D8780990 0A00001E
	ds_read_u16 v11, v30 offset:2592                           // 000000001A04: D8780A20 0B00001E
	ds_read_u16 v18, v30 offset:2480                           // 000000001A0C: D87809B0 1200001E
	ds_read_u16 v19, v30 offset:2624                           // 000000001A14: D8780A40 1300001E
	ds_read_u16 v37, v30 offset:2512                           // 000000001A1C: D87809D0 2500001E
	ds_read_u16 v38, v30 offset:2656                           // 000000001A24: D8780A60 2600001E
	ds_read_u16 v39, v30 offset:2688                           // 000000001A2C: D8780A80 2700001E
	ds_read_u16 v30, v30 offset:2544                           // 000000001A34: D87809F0 1E00001E
	s_waitcnt lgkmcnt(6)                                       // 000000001A3C: BF8CC67F
	v_perm_b32 v11, v0, v11, s0                                // 000000001A40: D1ED000B 00021700
	v_perm_b32 v10, v10, v21, s0                               // 000000001A48: D1ED000A 00022B0A
	v_mfma_f32_16x16x16_f16 v[6:9], v[14:15], v[6:7], 0        // 000000001A50: D3CD0006 02020D0E
	v_add_u32_e32 v21, s2, v1                                  // 000000001A58: 682A0202
	s_waitcnt lgkmcnt(1)                                       // 000000001A5C: BF8CC17F
	v_perm_b32 v1, v34, v39, s0                                // 000000001A60: D1ED0001 00024F22
	s_waitcnt lgkmcnt(0)                                       // 000000001A68: BF8CC07F
	v_perm_b32 v0, v30, v33, s0                                // 000000001A6C: D1ED0000 0002431E
	v_mfma_f32_16x16x16_f16 v[12:15], v[16:17], v[10:11], v[2:5]// 000000001A74: D3CD000C 040A1510
	v_cmp_gt_i32_e32 vcc, 17, v21                              // 000000001A7C: 7D882A91
	s_nop 1                                                    // 000000001A80: BF800001
	v_perm_b32 v3, v35, v19, s0                                // 000000001A84: D1ED0003 00022723
	v_perm_b32 v2, v18, v31, s0                                // 000000001A8C: D1ED0002 00023F12
	s_nop 1                                                    // 000000001A94: BF800001
	v_mfma_f32_16x16x16_f16 v[8:11], v[16:17], v[2:3], v[6:9]  // 000000001A98: D3CD0008 041A0510
	v_perm_b32 v3, v36, v38, s0                                // 000000001AA0: D1ED0003 00024D24
	v_perm_b32 v2, v37, v32, s0                                // 000000001AA8: D1ED0002 00024125
	s_nop 1                                                    // 000000001AB0: BF800001
	v_mfma_f32_16x16x16_f16 v[4:7], v[16:17], v[2:3], v[22:25] // 000000001AB4: D3CD0004 045A0510
	v_mfma_f32_16x16x16_f16 v[0:3], v[16:17], v[0:1], v[26:29] // 000000001ABC: D3CD0000 046A0110
	v_lshl_or_b32 v16, v21, 6, v20                             // 000000001AC4: D2000010 04510D15
	s_and_saveexec_b64 s[0:1], vcc                             // 000000001ACC: BE80206A
	s_cbranch_execz 6                                          // 000000001AD0: BF880006 <awq_fp16_gemm+0x3ec>
	v_cvt_f16_f32_e32 v12, v12                                 // 000000001AD4: 7E18150C
	v_ashrrev_i32_e32 v17, 31, v16                             // 000000001AD8: 2222209F
	v_lshl_add_u64 v[18:19], v[16:17], 1, s[8:9]               // 000000001ADC: D2080012 00210310
	global_store_short v[18:19], v12, off                      // 000000001AE4: DC688000 007F0C12
	s_or_b64 exec, exec, s[0:1]                                // 000000001AEC: 87FE007E
	v_or_b32_e32 v12, 1, v21                                   // 000000001AF0: 28182A81
	v_cmp_gt_i32_e64 s[0:1], 17, v12                           // 000000001AF4: D0C40000 00021891
	v_lshl_or_b32 v12, v12, 6, v20                             // 000000001AFC: D200000C 04510D0C
	s_and_saveexec_b64 s[2:3], s[0:1]                          // 000000001B04: BE822000
	s_cbranch_execz 6                                          // 000000001B08: BF880006 <awq_fp16_gemm+0x424>
	v_cvt_f16_f32_e32 v17, v13                                 // 000000001B0C: 7E22150D
	v_ashrrev_i32_e32 v13, 31, v12                             // 000000001B10: 221A189F
	v_lshl_add_u64 v[18:19], v[12:13], 1, s[8:9]               // 000000001B14: D2080012 0021030C
	global_store_short v[18:19], v17, off                      // 000000001B1C: DC688000 007F1112
	s_or_b64 exec, exec, s[2:3]                                // 000000001B24: 87FE027E
	v_or_b32_e32 v13, 2, v21                                   // 000000001B28: 281A2A82
	v_cmp_gt_i32_e64 s[2:3], 17, v13                           // 000000001B2C: D0C40002 00021A91
	v_lshl_or_b32 v18, v13, 6, v20                             // 000000001B34: D2000012 04510D0D
	s_and_saveexec_b64 s[4:5], s[2:3]                          // 000000001B3C: BE842002
	s_cbranch_execz 6                                          // 000000001B40: BF880006 <awq_fp16_gemm+0x45c>
	v_cvt_f16_f32_e32 v13, v14                                 // 000000001B44: 7E1A150E
	v_ashrrev_i32_e32 v19, 31, v18                             // 000000001B48: 2226249F
	v_lshl_add_u64 v[22:23], v[18:19], 1, s[8:9]               // 000000001B4C: D2080016 00210312
	global_store_short v[22:23], v13, off                      // 000000001B54: DC688000 007F0D16
	s_or_b64 exec, exec, s[4:5]                                // 000000001B5C: 87FE047E
	v_or_b32_e32 v13, 3, v21                                   // 000000001B60: 281A2A83
	v_cmp_gt_i32_e64 s[4:5], 17, v13                           // 000000001B64: D0C40004 00021A91
	v_lshl_or_b32 v14, v13, 6, v20                             // 000000001B6C: D200000E 04510D0D
	s_and_saveexec_b64 s[6:7], s[4:5]                          // 000000001B74: BE862004
	s_cbranch_execz 6                                          // 000000001B78: BF880006 <awq_fp16_gemm+0x494>
	v_cvt_f16_f32_e32 v13, v15                                 // 000000001B7C: 7E1A150F
	v_ashrrev_i32_e32 v15, 31, v14                             // 000000001B80: 221E1C9F
	v_lshl_add_u64 v[20:21], v[14:15], 1, s[8:9]               // 000000001B84: D2080014 0021030E
	global_store_short v[20:21], v13, off                      // 000000001B8C: DC688000 007F0D14
	s_or_b64 exec, exec, s[6:7]                                // 000000001B94: 87FE067E
	s_and_saveexec_b64 s[6:7], vcc                             // 000000001B98: BE86206A
	s_cbranch_execz 6                                          // 000000001B9C: BF880006 <awq_fp16_gemm+0x4b8>
	v_cvt_f16_f32_e32 v8, v8                                   // 000000001BA0: 7E101508
	v_ashrrev_i32_e32 v17, 31, v16                             // 000000001BA4: 2222209F
	v_lshl_add_u64 v[20:21], v[16:17], 1, s[8:9]               // 000000001BA8: D2080014 00210310
	global_store_short v[20:21], v8, off offset:32             // 000000001BB0: DC688020 007F0814
	s_or_b64 exec, exec, s[6:7]                                // 000000001BB8: 87FE067E
	s_and_saveexec_b64 s[6:7], s[0:1]                          // 000000001BBC: BE862000
	s_cbranch_execz 6                                          // 000000001BC0: BF880006 <awq_fp16_gemm+0x4dc>
	v_cvt_f16_f32_e32 v15, v9                                  // 000000001BC4: 7E1E1509
	v_ashrrev_i32_e32 v13, 31, v12                             // 000000001BC8: 221A189F
	v_lshl_add_u64 v[8:9], v[12:13], 1, s[8:9]                 // 000000001BCC: D2080008 0021030C
	global_store_short v[8:9], v15, off offset:32              // 000000001BD4: DC688020 007F0F08
	s_or_b64 exec, exec, s[6:7]                                // 000000001BDC: 87FE067E
	s_and_saveexec_b64 s[6:7], s[2:3]                          // 000000001BE0: BE862002
	s_cbranch_execz 6                                          // 000000001BE4: BF880006 <awq_fp16_gemm+0x500>
	v_cvt_f16_f32_e32 v10, v10                                 // 000000001BE8: 7E14150A
	v_ashrrev_i32_e32 v19, 31, v18                             // 000000001BEC: 2226249F
	v_lshl_add_u64 v[8:9], v[18:19], 1, s[8:9]                 // 000000001BF0: D2080008 00210312
	global_store_short v[8:9], v10, off offset:32              // 000000001BF8: DC688020 007F0A08
	s_or_b64 exec, exec, s[6:7]                                // 000000001C00: 87FE067E
	s_and_saveexec_b64 s[6:7], s[4:5]                          // 000000001C04: BE862004
	s_cbranch_execz 6                                          // 000000001C08: BF880006 <awq_fp16_gemm+0x524>
	v_cvt_f16_f32_e32 v10, v11                                 // 000000001C0C: 7E14150B
	v_ashrrev_i32_e32 v15, 31, v14                             // 000000001C10: 221E1C9F
	v_lshl_add_u64 v[8:9], v[14:15], 1, s[8:9]                 // 000000001C14: D2080008 0021030E
	global_store_short v[8:9], v10, off offset:32              // 000000001C1C: DC688020 007F0A08
	s_or_b64 exec, exec, s[6:7]                                // 000000001C24: 87FE067E
	s_and_saveexec_b64 s[6:7], vcc                             // 000000001C28: BE86206A
	s_cbranch_execz 6                                          // 000000001C2C: BF880006 <awq_fp16_gemm+0x548>
	v_cvt_f16_f32_e32 v4, v4                                   // 000000001C30: 7E081504
	v_ashrrev_i32_e32 v17, 31, v16                             // 000000001C34: 2222209F
	v_lshl_add_u64 v[8:9], v[16:17], 1, s[8:9]                 // 000000001C38: D2080008 00210310
	global_store_short v[8:9], v4, off offset:64               // 000000001C40: DC688040 007F0408
	s_or_b64 exec, exec, s[6:7]                                // 000000001C48: 87FE067E
	s_and_saveexec_b64 s[6:7], s[0:1]                          // 000000001C4C: BE862000
	s_cbranch_execz 6                                          // 000000001C50: BF880006 <awq_fp16_gemm+0x56c>
	v_cvt_f16_f32_e32 v8, v5                                   // 000000001C54: 7E101505
	v_ashrrev_i32_e32 v13, 31, v12                             // 000000001C58: 221A189F
	v_lshl_add_u64 v[4:5], v[12:13], 1, s[8:9]                 // 000000001C5C: D2080004 0021030C
	global_store_short v[4:5], v8, off offset:64               // 000000001C64: DC688040 007F0804
	s_or_b64 exec, exec, s[6:7]                                // 000000001C6C: 87FE067E
	s_and_saveexec_b64 s[6:7], s[2:3]                          // 000000001C70: BE862002
	s_cbranch_execz 6                                          // 000000001C74: BF880006 <awq_fp16_gemm+0x590>
	v_cvt_f16_f32_e32 v6, v6                                   // 000000001C78: 7E0C1506
	v_ashrrev_i32_e32 v19, 31, v18                             // 000000001C7C: 2226249F
	v_lshl_add_u64 v[4:5], v[18:19], 1, s[8:9]                 // 000000001C80: D2080004 00210312
	global_store_short v[4:5], v6, off offset:64               // 000000001C88: DC688040 007F0604
	s_or_b64 exec, exec, s[6:7]                                // 000000001C90: 87FE067E
	s_and_saveexec_b64 s[6:7], s[4:5]                          // 000000001C94: BE862004
	s_cbranch_execz 6                                          // 000000001C98: BF880006 <awq_fp16_gemm+0x5b4>
	v_cvt_f16_f32_e32 v6, v7                                   // 000000001C9C: 7E0C1507
	v_ashrrev_i32_e32 v15, 31, v14                             // 000000001CA0: 221E1C9F
	v_lshl_add_u64 v[4:5], v[14:15], 1, s[8:9]                 // 000000001CA4: D2080004 0021030E
	global_store_short v[4:5], v6, off offset:64               // 000000001CAC: DC688040 007F0604
	s_or_b64 exec, exec, s[6:7]                                // 000000001CB4: 87FE067E
	s_and_saveexec_b64 s[6:7], vcc                             // 000000001CB8: BE86206A
	s_cbranch_execz 6                                          // 000000001CBC: BF880006 <awq_fp16_gemm+0x5d8>
	v_cvt_f16_f32_e32 v0, v0                                   // 000000001CC0: 7E001500
	v_ashrrev_i32_e32 v17, 31, v16                             // 000000001CC4: 2222209F
	v_lshl_add_u64 v[4:5], v[16:17], 1, s[8:9]                 // 000000001CC8: D2080004 00210310
	global_store_short v[4:5], v0, off offset:96               // 000000001CD0: DC688060 007F0004
	s_or_b64 exec, exec, s[6:7]                                // 000000001CD8: 87FE067E
	s_and_saveexec_b64 s[6:7], s[0:1]                          // 000000001CDC: BE862000
	s_cbranch_execz 6                                          // 000000001CE0: BF880006 <awq_fp16_gemm+0x5fc>
	v_cvt_f16_f32_e32 v4, v1                                   // 000000001CE4: 7E081501
	v_ashrrev_i32_e32 v13, 31, v12                             // 000000001CE8: 221A189F
	v_lshl_add_u64 v[0:1], v[12:13], 1, s[8:9]                 // 000000001CEC: D2080000 0021030C
	global_store_short v[0:1], v4, off offset:96               // 000000001CF4: DC688060 007F0400
	s_or_b64 exec, exec, s[6:7]                                // 000000001CFC: 87FE067E
	s_and_saveexec_b64 s[0:1], s[2:3]                          // 000000001D00: BE802002
	s_cbranch_execz 6                                          // 000000001D04: BF880006 <awq_fp16_gemm+0x620>
	v_cvt_f16_f32_e32 v2, v2                                   // 000000001D08: 7E041502
	v_ashrrev_i32_e32 v19, 31, v18                             // 000000001D0C: 2226249F
	v_lshl_add_u64 v[0:1], v[18:19], 1, s[8:9]                 // 000000001D10: D2080000 00210312
	global_store_short v[0:1], v2, off offset:96               // 000000001D18: DC688060 007F0200
	s_or_b64 exec, exec, s[0:1]                                // 000000001D20: 87FE007E
	s_and_saveexec_b64 s[0:1], s[4:5]                          // 000000001D24: BE802004
	s_cbranch_execz 6                                          // 000000001D28: BF880006 <awq_fp16_gemm+0x644>
	v_cvt_f16_f32_e32 v2, v3                                   // 000000001D2C: 7E041503
	v_ashrrev_i32_e32 v15, 31, v14                             // 000000001D30: 221E1C9F
	v_lshl_add_u64 v[0:1], v[14:15], 1, s[8:9]                 // 000000001D34: D2080000 0021030E
	global_store_short v[0:1], v2, off offset:96               // 000000001D3C: DC688060 007F0200
	s_endpgm                                                   // 000000001D44: BF810000
	s_nop 0                                                    // 000000001D48: BF800000
	s_nop 0                                                    // 000000001D4C: BF800000
	s_nop 0                                                    // 000000001D50: BF800000
	s_nop 0                                                    // 000000001D54: BF800000
	s_nop 0                                                    // 000000001D58: BF800000
	s_nop 0                                                    // 000000001D5C: BF800000
	s_nop 0                                                    // 000000001D60: BF800000
	s_nop 0                                                    // 000000001D64: BF800000
	s_nop 0                                                    // 000000001D68: BF800000
	s_nop 0                                                    // 000000001D6C: BF800000
	s_nop 0                                                    // 000000001D70: BF800000
	s_nop 0                                                    // 000000001D74: BF800000
	s_nop 0                                                    // 000000001D78: BF800000
	s_nop 0                                                    // 000000001D7C: BF800000
	s_nop 0                                                    // 000000001D80: BF800000
	s_nop 0                                                    // 000000001D84: BF800000
	s_nop 0                                                    // 000000001D88: BF800000
	s_nop 0                                                    // 000000001D8C: BF800000
	s_nop 0                                                    // 000000001D90: BF800000
	s_nop 0                                                    // 000000001D94: BF800000
	s_nop 0                                                    // 000000001D98: BF800000
	s_nop 0                                                    // 000000001D9C: BF800000
	s_nop 0                                                    // 000000001DA0: BF800000
	s_nop 0                                                    // 000000001DA4: BF800000
	s_nop 0                                                    // 000000001DA8: BF800000
	s_nop 0                                                    // 000000001DAC: BF800000
	s_nop 0                                                    // 000000001DB0: BF800000
	s_nop 0                                                    // 000000001DB4: BF800000
	s_nop 0                                                    // 000000001DB8: BF800000
	s_nop 0                                                    // 000000001DBC: BF800000
	s_nop 0                                                    // 000000001DC0: BF800000
	s_nop 0                                                    // 000000001DC4: BF800000
	s_nop 0                                                    // 000000001DC8: BF800000
	s_nop 0                                                    // 000000001DCC: BF800000
	s_nop 0                                                    // 000000001DD0: BF800000
	s_nop 0                                                    // 000000001DD4: BF800000
	s_nop 0                                                    // 000000001DD8: BF800000
	s_nop 0                                                    // 000000001DDC: BF800000
	s_nop 0                                                    // 000000001DE0: BF800000
	s_nop 0                                                    // 000000001DE4: BF800000
	s_nop 0                                                    // 000000001DE8: BF800000
	s_nop 0                                                    // 000000001DEC: BF800000
	s_nop 0                                                    // 000000001DF0: BF800000
	s_nop 0                                                    // 000000001DF4: BF800000
	s_nop 0                                                    // 000000001DF8: BF800000
	s_nop 0                                                    // 000000001DFC: BF800000
	s_nop 0                                                    // 000000001E00: BF800000
	s_nop 0                                                    // 000000001E04: BF800000
	s_nop 0                                                    // 000000001E08: BF800000
	s_nop 0                                                    // 000000001E0C: BF800000
	s_nop 0                                                    // 000000001E10: BF800000
	s_nop 0                                                    // 000000001E14: BF800000
	s_nop 0                                                    // 000000001E18: BF800000
	s_nop 0                                                    // 000000001E1C: BF800000
	s_nop 0                                                    // 000000001E20: BF800000
	s_nop 0                                                    // 000000001E24: BF800000
	s_nop 0                                                    // 000000001E28: BF800000
	s_nop 0                                                    // 000000001E2C: BF800000
	s_nop 0                                                    // 000000001E30: BF800000
	s_nop 0                                                    // 000000001E34: BF800000
	s_nop 0                                                    // 000000001E38: BF800000
	s_nop 0                                                    // 000000001E3C: BF800000
	s_nop 0                                                    // 000000001E40: BF800000
	s_nop 0                                                    // 000000001E44: BF800000
	s_nop 0                                                    // 000000001E48: BF800000
	s_nop 0                                                    // 000000001E4C: BF800000
	s_nop 0                                                    // 000000001E50: BF800000
	s_nop 0                                                    // 000000001E54: BF800000
	s_nop 0                                                    // 000000001E58: BF800000
	s_nop 0                                                    // 000000001E5C: BF800000
	s_nop 0                                                    // 000000001E60: BF800000
	s_nop 0                                                    // 000000001E64: BF800000
	s_nop 0                                                    // 000000001E68: BF800000
	s_nop 0                                                    // 000000001E6C: BF800000
	s_nop 0                                                    // 000000001E70: BF800000
	s_nop 0                                                    // 000000001E74: BF800000
	s_nop 0                                                    // 000000001E78: BF800000
	s_nop 0                                                    // 000000001E7C: BF800000
	s_nop 0                                                    // 000000001E80: BF800000
	s_nop 0                                                    // 000000001E84: BF800000
	s_nop 0                                                    // 000000001E88: BF800000
	s_nop 0                                                    // 000000001E8C: BF800000
	s_nop 0                                                    // 000000001E90: BF800000
	s_nop 0                                                    // 000000001E94: BF800000
	s_nop 0                                                    // 000000001E98: BF800000
	s_nop 0                                                    // 000000001E9C: BF800000
	s_nop 0                                                    // 000000001EA0: BF800000
	s_nop 0                                                    // 000000001EA4: BF800000
	s_nop 0                                                    // 000000001EA8: BF800000
	s_nop 0                                                    // 000000001EAC: BF800000
	s_nop 0                                                    // 000000001EB0: BF800000
	s_nop 0                                                    // 000000001EB4: BF800000
	s_nop 0                                                    // 000000001EB8: BF800000
	s_nop 0                                                    // 000000001EBC: BF800000
	s_nop 0                                                    // 000000001EC0: BF800000
	s_nop 0                                                    // 000000001EC4: BF800000
	s_nop 0                                                    // 000000001EC8: BF800000
	s_nop 0                                                    // 000000001ECC: BF800000
	s_nop 0                                                    // 000000001ED0: BF800000
	s_nop 0                                                    // 000000001ED4: BF800000
	s_nop 0                                                    // 000000001ED8: BF800000
	s_nop 0                                                    // 000000001EDC: BF800000
	s_nop 0                                                    // 000000001EE0: BF800000
	s_nop 0                                                    // 000000001EE4: BF800000
	s_nop 0                                                    // 000000001EE8: BF800000
	s_nop 0                                                    // 000000001EEC: BF800000
	s_nop 0                                                    // 000000001EF0: BF800000
	s_nop 0                                                    // 000000001EF4: BF800000
	s_nop 0                                                    // 000000001EF8: BF800000
	s_nop 0                                                    // 000000001EFC: BF800000
	s_nop 0                                                    // 000000001F00: BF800000
	s_nop 0                                                    // 000000001F04: BF800000
	s_nop 0                                                    // 000000001F08: BF800000
	s_nop 0                                                    // 000000001F0C: BF800000
	s_nop 0                                                    // 000000001F10: BF800000
	s_nop 0                                                    // 000000001F14: BF800000
	s_nop 0                                                    // 000000001F18: BF800000
	s_nop 0                                                    // 000000001F1C: BF800000
	s_nop 0                                                    // 000000001F20: BF800000
	s_nop 0                                                    // 000000001F24: BF800000
	s_nop 0                                                    // 000000001F28: BF800000
	s_nop 0                                                    // 000000001F2C: BF800000
	s_nop 0                                                    // 000000001F30: BF800000
	s_nop 0                                                    // 000000001F34: BF800000
	s_nop 0                                                    // 000000001F38: BF800000
	s_nop 0                                                    // 000000001F3C: BF800000
	s_nop 0                                                    // 000000001F40: BF800000
	s_nop 0                                                    // 000000001F44: BF800000
	s_nop 0                                                    // 000000001F48: BF800000
	s_nop 0                                                    // 000000001F4C: BF800000
	s_nop 0                                                    // 000000001F50: BF800000
	s_nop 0                                                    // 000000001F54: BF800000
	s_nop 0                                                    // 000000001F58: BF800000
	s_nop 0                                                    // 000000001F5C: BF800000
	s_nop 0                                                    // 000000001F60: BF800000
	s_nop 0                                                    // 000000001F64: BF800000
	s_nop 0                                                    // 000000001F68: BF800000
	s_nop 0                                                    // 000000001F6C: BF800000
	s_nop 0                                                    // 000000001F70: BF800000
	s_nop 0                                                    // 000000001F74: BF800000
	s_nop 0                                                    // 000000001F78: BF800000
	s_nop 0                                                    // 000000001F7C: BF800000
	s_nop 0                                                    // 000000001F80: BF800000
	s_nop 0                                                    // 000000001F84: BF800000
	s_nop 0                                                    // 000000001F88: BF800000
	s_nop 0                                                    // 000000001F8C: BF800000
	s_nop 0                                                    // 000000001F90: BF800000
	s_nop 0                                                    // 000000001F94: BF800000
	s_nop 0                                                    // 000000001F98: BF800000
	s_nop 0                                                    // 000000001F9C: BF800000
	s_nop 0                                                    // 000000001FA0: BF800000
	s_nop 0                                                    // 000000001FA4: BF800000
	s_nop 0                                                    // 000000001FA8: BF800000
	s_nop 0                                                    // 000000001FAC: BF800000
	s_nop 0                                                    // 000000001FB0: BF800000
	s_nop 0                                                    // 000000001FB4: BF800000
	s_nop 0                                                    // 000000001FB8: BF800000
	s_nop 0                                                    // 000000001FBC: BF800000
	s_nop 0                                                    // 000000001FC0: BF800000
	s_nop 0                                                    // 000000001FC4: BF800000
	s_nop 0                                                    // 000000001FC8: BF800000
	s_nop 0                                                    // 000000001FCC: BF800000
	s_nop 0                                                    // 000000001FD0: BF800000
	s_nop 0                                                    // 000000001FD4: BF800000
	s_nop 0                                                    // 000000001FD8: BF800000
	s_nop 0                                                    // 000000001FDC: BF800000
	s_nop 0                                                    // 000000001FE0: BF800000
	s_nop 0                                                    // 000000001FE4: BF800000
	s_nop 0                                                    // 000000001FE8: BF800000
	s_nop 0                                                    // 000000001FEC: BF800000
	s_nop 0                                                    // 000000001FF0: BF800000
	s_nop 0                                                    // 000000001FF4: BF800000
	s_nop 0                                                    // 000000001FF8: BF800000
	s_nop 0                                                    // 000000001FFC: BF800000
	s_nop 0                                                    // 000000002000: BF800000
	s_nop 0                                                    // 000000002004: BF800000
	s_nop 0                                                    // 000000002008: BF800000
	s_nop 0                                                    // 00000000200C: BF800000
	s_nop 0                                                    // 000000002010: BF800000
	s_nop 0                                                    // 000000002014: BF800000
	s_nop 0                                                    // 000000002018: BF800000
	s_nop 0                                                    // 00000000201C: BF800000
	s_nop 0                                                    // 000000002020: BF800000
	s_nop 0                                                    // 000000002024: BF800000
	s_nop 0                                                    // 000000002028: BF800000
	s_nop 0                                                    // 00000000202C: BF800000
	s_nop 0                                                    // 000000002030: BF800000
	s_nop 0                                                    // 000000002034: BF800000
	s_nop 0                                                    // 000000002038: BF800000
	s_nop 0                                                    // 00000000203C: BF800000
	s_nop 0                                                    // 000000002040: BF800000
	s_nop 0                                                    // 000000002044: BF800000
	s_nop 0                                                    // 000000002048: BF800000
	s_nop 0                                                    // 00000000204C: BF800000
	s_nop 0                                                    // 000000002050: BF800000
	s_nop 0                                                    // 000000002054: BF800000
	s_nop 0                                                    // 000000002058: BF800000
	s_nop 0                                                    // 00000000205C: BF800000
	s_nop 0                                                    // 000000002060: BF800000
	s_nop 0                                                    // 000000002064: BF800000
	s_nop 0                                                    // 000000002068: BF800000
	s_nop 0                                                    // 00000000206C: BF800000
	s_nop 0                                                    // 000000002070: BF800000
	s_nop 0                                                    // 000000002074: BF800000
	s_nop 0                                                    // 000000002078: BF800000
	s_nop 0                                                    // 00000000207C: BF800000
	s_nop 0                                                    // 000000002080: BF800000
	s_nop 0                                                    // 000000002084: BF800000
	s_nop 0                                                    // 000000002088: BF800000
	s_nop 0                                                    // 00000000208C: BF800000
	s_nop 0                                                    // 000000002090: BF800000
	s_nop 0                                                    // 000000002094: BF800000
	s_nop 0                                                    // 000000002098: BF800000
	s_nop 0                                                    // 00000000209C: BF800000
	s_nop 0                                                    // 0000000020A0: BF800000
	s_nop 0                                                    // 0000000020A4: BF800000
	s_nop 0                                                    // 0000000020A8: BF800000
	s_nop 0                                                    // 0000000020AC: BF800000
	s_nop 0                                                    // 0000000020B0: BF800000
	s_nop 0                                                    // 0000000020B4: BF800000
	s_nop 0                                                    // 0000000020B8: BF800000
	s_nop 0                                                    // 0000000020BC: BF800000
	s_nop 0                                                    // 0000000020C0: BF800000
	s_nop 0                                                    // 0000000020C4: BF800000
	s_nop 0                                                    // 0000000020C8: BF800000
	s_nop 0                                                    // 0000000020CC: BF800000
	s_nop 0                                                    // 0000000020D0: BF800000
	s_nop 0                                                    // 0000000020D4: BF800000
	s_nop 0                                                    // 0000000020D8: BF800000
	s_nop 0                                                    // 0000000020DC: BF800000
	s_nop 0                                                    // 0000000020E0: BF800000
	s_nop 0                                                    // 0000000020E4: BF800000
	s_nop 0                                                    // 0000000020E8: BF800000
	s_nop 0                                                    // 0000000020EC: BF800000
	s_nop 0                                                    // 0000000020F0: BF800000
	s_nop 0                                                    // 0000000020F4: BF800000
	s_nop 0                                                    // 0000000020F8: BF800000
	s_nop 0                                                    // 0000000020FC: BF800000
	s_nop 0                                                    // 000000002100: BF800000
	s_nop 0                                                    // 000000002104: BF800000
	s_nop 0                                                    // 000000002108: BF800000
	s_nop 0                                                    // 00000000210C: BF800000
	s_nop 0                                                    // 000000002110: BF800000
	s_nop 0                                                    // 000000002114: BF800000
	s_nop 0                                                    // 000000002118: BF800000
	s_nop 0                                                    // 00000000211C: BF800000
	s_nop 0                                                    // 000000002120: BF800000
	s_nop 0                                                    // 000000002124: BF800000
	s_nop 0                                                    // 000000002128: BF800000
	s_nop 0                                                    // 00000000212C: BF800000
	s_nop 0                                                    // 000000002130: BF800000
	s_nop 0                                                    // 000000002134: BF800000
	s_nop 0                                                    // 000000002138: BF800000
	s_nop 0                                                    // 00000000213C: BF800000
	s_nop 0                                                    // 000000002140: BF800000
	s_nop 0                                                    // 000000002144: BF800000
	s_nop 0                                                    // 000000002148: BF800000
	s_nop 0                                                    // 00000000214C: BF800000
	s_nop 0                                                    // 000000002150: BF800000
	s_nop 0                                                    // 000000002154: BF800000
	s_nop 0                                                    // 000000002158: BF800000
	s_nop 0                                                    // 00000000215C: BF800000
	s_nop 0                                                    // 000000002160: BF800000
	s_nop 0                                                    // 000000002164: BF800000
	s_nop 0                                                    // 000000002168: BF800000
	s_nop 0                                                    // 00000000216C: BF800000
	s_nop 0                                                    // 000000002170: BF800000
	s_nop 0                                                    // 000000002174: BF800000
	s_nop 0                                                    // 000000002178: BF800000
	s_nop 0                                                    // 00000000217C: BF800000
