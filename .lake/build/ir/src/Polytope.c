// Lean compiler output
// Module: src.Polytope
// Imports: Init src.Polar
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
LEAN_EXPORT lean_object* l_Cyclic3_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Cyclic3_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instMulCyclic3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Cyclic3_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_instMulCyclic3(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Cyclic3_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Cyclic3_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Cyclic3_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Cyclic3_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Cyclic3_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Cyclic3_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Cyclic3_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Cyclic3_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Cyclic3_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Cyclic3_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instMulCyclic3(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
return x_2;
}
case 1:
{
switch (x_2) {
case 0:
{
return x_1;
}
case 1:
{
uint8_t x_3; 
x_3 = 2;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
default: 
{
switch (x_2) {
case 0:
{
return x_1;
}
case 1:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_instMulCyclic3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instMulCyclic3(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_src_Polar(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_src_Polytope(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_src_Polar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Cyclic3_noConfusion___rarg___closed__1 = _init_l_Cyclic3_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Cyclic3_noConfusion___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
