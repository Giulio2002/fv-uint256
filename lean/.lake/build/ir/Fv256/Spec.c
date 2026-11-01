// Lean compiler output
// Module: Fv256.Spec
// Imports: public import Init public meta import Init public import Janus
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t lp_fv256_Fv256_Spec_W___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_fv256_Fv256_Spec_W___closed__0;
LEAN_EXPORT lean_object* lp_fv256_Fv256_Spec_W;
LEAN_EXPORT uint8_t lp_fv256_Fv256_Spec_isZero(lean_object*);
LEAN_EXPORT lean_object* lp_fv256_Fv256_Spec_isZero___boxed(lean_object*);
static lean_object* _init_lp_fv256_Fv256_Spec_W___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_unsigned_to_nat(256u);
v___x_2_ = lean_unsigned_to_nat(2u);
v___x_3_ = lean_nat_pow(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_fv256_Fv256_Spec_W(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&lp_fv256_Fv256_Spec_W___closed__0, &lp_fv256_Fv256_Spec_W___closed__0_once, _init_lp_fv256_Fv256_Spec_W___closed__0);
return v___x_4_;
}
}
LEAN_EXPORT uint8_t lp_fv256_Fv256_Spec_isZero(lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_nat_dec_eq(v_x_5_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_fv256_Fv256_Spec_isZero___boxed(lean_object* v_x_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = lp_fv256_Fv256_Spec_isZero(v_x_8_);
lean_dec(v_x_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_janus_Janus(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_fv256_Fv256_Spec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_janus_Janus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_fv256_Fv256_Spec_W = _init_lp_fv256_Fv256_Spec_W();
lean_mark_persistent(lp_fv256_Fv256_Spec_W);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
