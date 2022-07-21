#ifndef NULL
#define NULL 0
#endif
#ifndef bool
#define bool _Bool
#endif
#define FIELD_DECLS() __CPROVER_field_decl_global("dr_noatomic", (_Bool)0); __CPROVER_field_decl_global("dr", (_Bool)0); __CPROVER_field_decl_local("dr_noatomic", (_Bool)0); __CPROVER_field_decl_local("dr", (_Bool)0);


#define EXPR_0() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag1, "dr", 1), __CPROVER_set_field(&flag1, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag1, "dr")), flag1 = 1)

#define EXPR_1() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&turn, "dr", 1), __CPROVER_set_field(&turn, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&turn, "dr")), turn = 1)

#define EXPR_2() (__CPROVER_assume((__cs_cond_1 = (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag2, "dr")), flag2 == 1)) && (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&turn, "dr")), turn == 1)), __cs_cond_0 = !__cs_cond_1, __cs_cond_0)))

#define EXPR_3() (__CPROVER_assume((!((flag2 == 1) && (turn == 1)))))

#define EXPR_4() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&x, "dr", 1), __CPROVER_set_field(&x, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&x, "dr")), x = 0)

#define EXPR_5() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&__dr_nondet_thr1___cs_tmp_if_cond_0, "dr", 1), __CPROVER_set_field(&__dr_nondet_thr1___cs_tmp_if_cond_0, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_thr1___cs_tmp_if_cond_0, "dr")), ((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&x, "dr")), __cs_cond_2 = !(x <= 0)), __dr_nondet_thr1___cs_tmp_if_cond_0 = __cs_cond_2)

#define EXPR_6() (__dr_nondet_thr1___cs_tmp_if_cond_0 = !(x <= 0))

#define EXPR_7() (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_thr1___cs_tmp_if_cond_0, "dr")), __dr_nondet_thr1___cs_tmp_if_cond_0))

#define EXPR_8() (0)

#define EXPR_9() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag1, "dr", 1), __CPROVER_set_field(&flag1, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag1, "dr")), flag1 = 0)

#define EXPR_10() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag2, "dr", 1), __CPROVER_set_field(&flag2, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag2, "dr")), flag2 = 1)

#define EXPR_11() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&turn, "dr", 1), __CPROVER_set_field(&turn, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&turn, "dr")), turn = 0)

#define EXPR_12() (__CPROVER_assume((__cs_cond_4 = (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag1, "dr")), flag1 == 1)) && (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&turn, "dr")), turn == 0)), __cs_cond_3 = !__cs_cond_4, __cs_cond_3)))

#define EXPR_13() (__CPROVER_assume((!((flag1 == 1) && (turn == 0)))))

#define EXPR_14() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&x, "dr", 1), __CPROVER_set_field(&x, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&x, "dr")), x = 1)

#define EXPR_15() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&__dr_nondet_thr2___cs_tmp_if_cond_1, "dr", 1), __CPROVER_set_field(&__dr_nondet_thr2___cs_tmp_if_cond_1, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_thr2___cs_tmp_if_cond_1, "dr")), ((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&x, "dr")), __cs_cond_5 = !(x >= 1)), __dr_nondet_thr2___cs_tmp_if_cond_1 = __cs_cond_5)

#define EXPR_16() (__dr_nondet_thr2___cs_tmp_if_cond_1 = !(x >= 1))

#define EXPR_17() (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_thr2___cs_tmp_if_cond_1, "dr")), __dr_nondet_thr2___cs_tmp_if_cond_1))

#define EXPR_18() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag1, "dr", 1), __CPROVER_set_field(&flag1, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag1, "dr")), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag1, "dr")), flag1 = flag1)

#define EXPR_19() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag2, "dr", 1), __CPROVER_set_field(&flag2, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag2, "dr")), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag2, "dr")), flag2 = flag2)

#define EXPR_20() (((__cs_dataraceDetectionStarted && (!__cs_dataraceSecondThread)) && __cs_dataraceActiveVP1) && ((__CPROVER_set_field(&flag2, "dr", 1), __CPROVER_set_field(&flag2, "dr_noatomic", 1), __cs_wkm = 1)), (__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&flag2, "dr")), flag2 = 0)

#define EXPR_21() (&__dr_nondet_main_t1)

#define EXPR_22() (&__dr_nondet_main_t1)

#define EXPR_23() ((&__dr_nondet_main_t1))

#define EXPR_24() ((0))

#define EXPR_25() (&__dr_nondet_main_t2)

#define EXPR_26() (&__dr_nondet_main_t2)

#define EXPR_27() ((&__dr_nondet_main_t2))

#define EXPR_28() (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_main_t1, "dr")), __dr_nondet_main_t1))

#define EXPR_29() ((__dr_nondet_main_t1))

#define EXPR_30() (((__cs_dataraceSecondThread && __cs_dataraceActiveVP2) && (__cs_dr = (__cs_dr || __cs_wam) || __CPROVER_get_field(&__dr_nondet_main_t2, "dr")), __dr_nondet_main_t2))

#define EXPR_31() ((__dr_nondet_main_t2))