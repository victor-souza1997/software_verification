

/*
We have p1, p2, p3, p4
g2
a1, a2, a3, a4, i0

# Constants
1, 2, 0

# position
&a[0]

p1 = store(p0, 0, &a[0]);
p2 = store(p1, 1, 0)

g2 = x == 0;

a1 = store(a0, i0, 0);
a2 = a0;
a3 = store(a2, i0+1,1);

a4 = ite(g1, a1, a3);

p4 = store(p2, 1, select(p2, 1)+2);

*/


// First, declare the context and solver. 
// We will use them through our solution. 
#include <stdio.h>
#include <stdlib.h>
#include <z3.h>
#define Z3_type_ast            Z3_sort
#define Z3_get_type            Z3_get_sort
#define Z3_get_type_kind       Z3_get_sort_kind
#define Z3_const_decl_ast      Z3_func_decl
#define Z3_get_tuple_type_num_fields Z3_get_tuple_sort_num_fields
#define Z3_TUPLE_TYPE          Z3_DATATYPE_SORT
#define Z3_get_tuple_type_field_decl Z3_get_tuple_sort_field_decl
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}
void unreachable()
{
    exitf("unreachable code was reached");
}
Z3_ast mk_int(Z3_context ctx, int v)
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}
Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x)
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}


Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

Z3_ast mk_bool_var(Z3_context ctx, const char * name)
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}
Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

Z3_solver mk_solver(Z3_context ctx)
{
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  return s;
}


void display_symbol(Z3_context c, FILE * out, Z3_symbol s)
{
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
        fprintf(out, "#%d", Z3_get_symbol_int(c, s));
        break;
    case Z3_STRING_SYMBOL:
        fprintf(out, "%s", Z3_get_symbol_string(c, s));
        break;
    default:
        unreachable();
    }
}

Z3_ast Z3_mk_add_two_terms(Z3_context ctx, Z3_ast t1, Z3_ast t2) {
  Z3_ast temp[2] = {t1, t2};
  return Z3_mk_add(ctx, 2, temp);
}

Z3_ast Z3_mk_and_two_terms(Z3_context ctx, Z3_ast t1, Z3_ast t2) {
  Z3_ast temp[2] = {t1, t2};
  return Z3_mk_and(ctx, 2, temp);
}

void del_solver(Z3_context ctx, Z3_solver s)
{
  Z3_solver_dec_ref(ctx, s);
}
void display_sort(Z3_context c, FILE * out, Z3_sort ty)
{
    switch (Z3_get_sort_kind(c, ty)) {
    case Z3_UNINTERPRETED_SORT:
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        break;
    case Z3_BOOL_SORT:
        fprintf(out, "bool");
        break;
    case Z3_INT_SORT:
        fprintf(out, "int");
        break;
    case Z3_REAL_SORT:
        fprintf(out, "real");
        break;
    case Z3_BV_SORT:
        fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
        break;
    case Z3_ARRAY_SORT:
        fprintf(out, "[");
        display_sort(c, out, Z3_get_array_sort_domain(c, ty));
        fprintf(out, "->");
        display_sort(c, out, Z3_get_array_sort_range(c, ty));
        fprintf(out, "]");
        break;
    case Z3_DATATYPE_SORT:
        if (Z3_get_datatype_sort_num_constructors(c, ty) != 1)
        {
            fprintf(out, "%s", Z3_sort_to_string(c,ty));
            break;
        }
        {
            unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
            unsigned i;
            fprintf(out, "(");
            for (i = 0; i < num_fields; i++) {
                Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
                if (i > 0) {
                    fprintf(out, ", ");
                }
                display_sort(c, out, Z3_get_range(c, field));
            }
            fprintf(out, ")");
            break;
        }
    default:
        fprintf(out, "unknown[");
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        fprintf(out, "]");
        break;
    }
}
void display_ast(Z3_context c, FILE * out, Z3_ast v)
{
    switch (Z3_get_ast_kind(c, v)) {
    case Z3_NUMERAL_AST: {
        Z3_sort t;
        fprintf(out, "%s", Z3_get_numeral_string(c, v));
        t = Z3_get_sort(c, v);
        fprintf(out, ":");
        display_sort(c, out, t);
        break;
    }
    case Z3_APP_AST: {
        unsigned i;
        Z3_app app = Z3_to_app(c, v);
        unsigned num_fields = Z3_get_app_num_args(c, app);
        Z3_func_decl d = Z3_get_app_decl(c, app);
        fprintf(out, "%s", Z3_func_decl_to_string(c, d));
        if (num_fields > 0) {
            fprintf(out, "[");
            for (i = 0; i < num_fields; i++) {
                if (i > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_get_app_arg(c, app, i));
            }
            fprintf(out, "]");
        }
        break;
    }
    case Z3_QUANTIFIER_AST: {
        fprintf(out, "quantifier");
        ;
    }
    default:
        fprintf(out, "#unknown");
    }
}

void display_function_interpretations(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_functions, i;

    fprintf(out, "function interpretations:\n");

    num_functions = Z3_model_get_num_funcs(c, m);
    for (i = 0; i < num_functions; i++) {
        Z3_func_decl fdecl;
        Z3_symbol name;
        Z3_ast func_else;
        unsigned num_entries = 0, j;
        Z3_func_interp_opt finterp;

        fdecl = Z3_model_get_func_decl(c, m, i);
        finterp = Z3_model_get_func_interp(c, m, fdecl);
        Z3_func_interp_inc_ref(c, finterp);
        name = Z3_get_decl_name(c, fdecl);
        display_symbol(c, out, name);
        fprintf(out, " = {");
        if (finterp)
          num_entries = Z3_func_interp_get_num_entries(c, finterp);
        for (j = 0; j < num_entries; j++) {
            unsigned num_args, k;
            Z3_func_entry fentry = Z3_func_interp_get_entry(c, finterp, j);
            Z3_func_entry_inc_ref(c, fentry);
            if (j > 0) {
                fprintf(out, ", ");
            }
            num_args = Z3_func_entry_get_num_args(c, fentry);
            fprintf(out, "(");
            for (k = 0; k < num_args; k++) {
                if (k > 0) {
                    fprintf(out, ", ");
                }
                display_ast(c, out, Z3_func_entry_get_arg(c, fentry, k));
            }
            fprintf(out, "|->");
            display_ast(c, out, Z3_func_entry_get_value(c, fentry));
            fprintf(out, ")");
            Z3_func_entry_dec_ref(c, fentry);
        }
        if (num_entries > 0) {
            fprintf(out, ", ");
        }
        fprintf(out, "(else|->");
        func_else = Z3_func_interp_get_else(c, finterp);
        display_ast(c, out, func_else);
        fprintf(out, ")}\n");
        Z3_func_interp_dec_ref(c, finterp);
    }
}
Z3_ast mk_tuple_select(Z3_context c, Z3_ast t, unsigned i)
{
    Z3_type_ast         ty;
    unsigned            num_fields;

    ty = Z3_get_type(c, t);

    if (Z3_get_type_kind(c, ty) != Z3_TUPLE_TYPE) {
        exitf("argument must be a tuple");
    }

    num_fields = Z3_get_tuple_type_num_fields(c, ty);

    if (i >= num_fields) {
        exitf("invalid tuple select, index is too big");
    }

    Z3_const_decl_ast proj_decl = Z3_get_tuple_type_field_decl(c, ty, i);
    return mk_unary_app(c, proj_decl, t);
}
Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val)
{
    Z3_sort         ty;
    Z3_func_decl   mk_tuple_decl;
    unsigned            num_fields, j;
    Z3_ast *            new_fields;
    Z3_ast              result;

    ty = Z3_get_sort(c, t);

    if (Z3_get_sort_kind(c, ty) != Z3_DATATYPE_SORT) {
        exitf("argument must be a tuple");
    }

    num_fields = Z3_get_tuple_sort_num_fields(c, ty);

    if (i >= num_fields) {
        exitf("invalid tuple update, index is too big");
    }

    new_fields = (Z3_ast*) malloc(sizeof(Z3_ast) * num_fields);
    for (j = 0; j < num_fields; j++) {
        if (i == j) {
            /* use new_val at position i */
            new_fields[j] = new_val;
        }
        else {
            /* use field j of t */
            Z3_func_decl proj_decl = Z3_get_tuple_sort_field_decl(c, ty, j);
            new_fields[j] = mk_unary_app(c, proj_decl, t);
        }
    }
    mk_tuple_decl = Z3_get_tuple_sort_mk_decl(c, ty);
    result = Z3_mk_app(c, mk_tuple_decl, num_fields, new_fields);
    free(new_fields);
    return result;
}

Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y)
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}
void display_model(Z3_context c, FILE * out, Z3_model m)
{
    unsigned num_constants;
    unsigned i;

    if (!m) return;

    num_constants = Z3_model_get_num_consts(c, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_func_decl cnst = Z3_model_get_const_decl(c, m, i);
        Z3_ast a, v;
        bool ok;
        name = Z3_get_decl_name(c, cnst);
        display_symbol(c, out, name);
        fprintf(out, " = ");
        a = Z3_mk_app(c, cnst, 0, 0);
        v = a;
        ok = Z3_model_eval(c, m, a, 1, &v);
        (void)ok;
        display_ast(c, out, v);
        fprintf(out, "\n");
    }
    display_function_interpretations(c, out, m);
}
void prove(Z3_context ctx, Z3_solver s, Z3_ast f, bool is_valid)
{
    Z3_model m = 0;
    Z3_ast   not_f;

    /* save the current state of the context */
    Z3_solver_push(ctx, s);

    not_f = Z3_mk_not(ctx, f);
    Z3_solver_assert(ctx, s, not_f);

    switch (Z3_solver_check(ctx, s)) {
    case Z3_L_FALSE:
        /* proved */
        printf("valid\n");
        if (!is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_UNDEF:
        /* Z3 failed to prove/disprove f. */
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m != 0) {
            Z3_model_inc_ref(ctx, m);
            /* m should be viewed as a potential counterexample. */
            printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_TRUE:
        /* disproved */
        printf("invalid\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) {
            Z3_model_inc_ref(ctx, m);
            /* the model returned by Z3 is a counterexample */
            printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    }
    if (m) Z3_model_dec_ref(ctx, m);

    /* restore scope */
    Z3_solver_pop(ctx, s, 1);
}

void check(Z3_context ctx, Z3_solver s, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
    if (m) Z3_model_dec_ref(ctx, m);
}


void check2(Z3_context ctx, Z3_solver s, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        display_model(ctx, stdout, m);
        break;
    case Z3_L_TRUE:
        printf("sat\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        display_model(ctx, stdout, m);
        break;
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
    if (m) Z3_model_dec_ref(ctx, m);

}

void buffer_overflow(){
Z3_context ctx = mk_context();
Z3_solver s = mk_solver(ctx);

//Second, declare the variable sort names:
Z3_sort array_sort, bool_sort, pointer_sort,bv1_sort,bv32_sort,bv64_sort;

// And assign each variable sort name a sort. 
//In our case, bitvector of 32 bits as int and 
// bool to be used for the guard.
bv1_sort = Z3_mk_bv_sort(ctx,1);
bv32_sort = Z3_mk_bv_sort(ctx,32);
bv64_sort = Z3_mk_bv_sort(ctx,64);
array_sort = Z3_mk_array_sort(ctx, bv1_sort, bv32_sort);
bool_sort = Z3_mk_bool_sort(ctx);

// It's important to declare and define constants
Z3_ast zero, one, two;
zero = Z3_mk_numeral(ctx, "0", bv32_sort);
one = Z3_mk_numeral(ctx, "1", bv32_sort);
two = Z3_mk_numeral(ctx, "2", bv32_sort);

// Now, we will define our variables 
// and assign each variable 
// its corresponding sort.
Z3_ast p1, p2, p3, p4;
Z3_ast g2;
Z3_ast i0, a0, a1, a2, a3, a4;
Z3_ast x0;
Z3_ast addr_a_start, mem_zero,mem_8;
Z3_ast addr_a;
Z3_ast guard_exec;

i0 = mk_var(ctx, "i0", bv32_sort);
x0 = mk_var(ctx, "x0", bv32_sort);
a0 = mk_var(ctx, "a0", array_sort);
a1 = mk_var(ctx, "a1", array_sort);
a2 = mk_var(ctx, "a2", array_sort);
a3 = mk_var(ctx, "a3", array_sort);
a4 = mk_var(ctx, "a4", array_sort);

//pointer_sort as tuple
printf("\n making pointer type\n");
Z3_symbol mk_tuple_name;
Z3_func_decl mk_pointer_sort_decl;
Z3_symbol proj_names[2];
Z3_sort proj_sorts[2];
Z3_func_decl proj_decls[2];
Z3_func_decl get_object, get_offset;
/* Create pair (tuple) type */
mk_tuple_name = Z3_mk_string_symbol(ctx, "struct_pointer_type_struct");
proj_names[0] = Z3_mk_string_symbol(ctx, "pointer_object");
proj_names[1] = Z3_mk_string_symbol(ctx, "pointer_offset");
proj_sorts[0] = bv64_sort;
proj_sorts[1] = bv64_sort;

pointer_sort = Z3_mk_tuple_sort(ctx, mk_tuple_name, 2, proj_names, proj_sorts,
&mk_pointer_sort_decl, proj_decls);
get_object = proj_decls[0]; /* function that extracts the first element of a tuple. object*/
get_offset = proj_decls[1]; /* function that extracts the second element of a tuple. offset */

display_sort(ctx, stdout, pointer_sort);
addr_a_start = Z3_mk_numeral(ctx,"2",bv64_sort);
mem_zero = Z3_mk_numeral(ctx,"0",bv64_sort);
mem_8 = Z3_mk_numeral(ctx,"8",bv64_sort);

Z3_ast TRUE;
TRUE=Z3_mk_true(ctx);
guard_exec = mk_var(ctx,"guard_exec",bool_sort);


p1 = mk_var(ctx, "p1", pointer_sort);
p2 = mk_var(ctx, "p2", pointer_sort);
p3 = mk_var(ctx, "p2", pointer_sort);

g2 = mk_var(ctx, "i0", bool_sort);

addr_a_start = Z3_mk_numeral(ctx,"2",bv64_sort);
mem_zero = Z3_mk_numeral(ctx,"0",bv64_sort);
mem_8 = Z3_mk_numeral(ctx,"8",bv64_sort);
// These variables are going to help us construct C and P as

addr_a = mk_binary_app(ctx, mk_pointer_sort_decl, addr_a_start ,mem_zero);
Z3_ast c[7], p[7], C, notP, P;

// Construct C
c[0] = Z3_mk_eq(ctx, g2, Z3_mk_eq(ctx, x0,  zero));
c[1] = Z3_mk_eq(ctx, a1, Z3_mk_store(ctx, a0, Z3_mk_extract(ctx,0,0,i0), zero));
c[2] = Z3_mk_eq(ctx, a2, a0);
c[3] = Z3_mk_eq(ctx, a3, Z3_mk_store(ctx, a2, Z3_mk_extract(ctx,0,0,
    Z3_mk_bvadd(ctx, i0, one)), one));
c[4] = Z3_mk_eq(ctx, a4, Z3_mk_ite(ctx, g2, a1, a3));
c[5] = Z3_mk_eq(ctx, p2, addr_a);
c[6] = Z3_mk_eq(ctx, p3, mk_binary_app(ctx, mk_pointer_sort_decl,
mk_unary_app(ctx, get_object, addr_a) ,mem_8));

// creating  matrix C by puting everything into and
C = Z3_mk_and(ctx, 7, c);

for(int i=0;i<6;i++)
{
Z3_solver_assert(ctx,s,c[i]);
}

// Defining P
p[0] = Z3_mk_bvuge(ctx, i0, zero);
p[1] = Z3_mk_bvult(ctx, i0, two);
p[2] = Z3_mk_bvuge(ctx, Z3_mk_bvadd(ctx, i0, one), zero);
p[3] = Z3_mk_bvult(ctx, Z3_mk_bvadd(ctx, i0, one), two);
p[4] = Z3_mk_eq(ctx, mk_unary_app(ctx, get_object, p3) , mk_unary_app(ctx, get_object, addr_a));
p[5] = Z3_mk_eq(ctx,Z3_mk_select(ctx,a3,Z3_mk_extract(ctx,0,0,Z3_mk_bvadd(ctx, i0, two))), one);

for(int i=0;i<6;i++)
{
p[i] = Z3_mk_not(ctx, Z3_mk_implies(ctx,/*Z3_mk_eq(ctx,one,one)*/TRUE,Z3_mk_implies(ctx,guard_exec,p[i])));
}

P = Z3_mk_or(ctx, 6, p);

Z3_solver_assert(ctx, s, P);

printf("P := [%s]\n", Z3_ast_to_string(ctx, P));
Z3_ast cp[] = {C,P};
printf("solver := [%s]\n", Z3_solver_to_string(ctx, s));
check(ctx, s, Z3_L_TRUE);

printf("\nEND\n");
del_solver(ctx, s);
Z3_del_context(ctx);

}

int main(){

    buffer_overflow();
}