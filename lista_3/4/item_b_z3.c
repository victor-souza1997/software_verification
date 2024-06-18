

void memory_leak(void){

    /*primeiro declaramos o contexto
    e definimos o objeto solver como s*/ 

    Z3_context ctx = mk_context();
    Z3_solver s = mk_solver(ctx);

    /*declaramos os tipos*/
    Z3_sort array_sort, bool_sort, pointer_sort, bv32_sort, bv64_sort;
    bool_sort = Z3_mk_bool_sort(ctx);
    bv32_sort = Z3_mk_bv_sort(ctx, 32);
    bv64_sort = Z3_mk_bv_sort(ctx, 64);
    array_sort = Z3_mk_array_sort(ctx, bv64_sort, bool_sort);

    /*agora criamos o tipo pointeiro*/
    Z3_symbol mk_tuple_name;
    Z3_func_decl mk_pointer_sort_decl;
    Z3_symbol proj_names[2];
    Z3_sort proj_sorts[2];
    Z3_func_decl proj_decls[2];
    Z3_func_decl get_object, get_offset;

    /*definimos o tipo do ponteiro
    pointer_sort: eh a declaracao da tuple
    get_object and get_offset sao funcoes para extrair elementos da tuple */
    mk_tuple_name = Z3_mk_string_symbol(ctx, "struct_pointer_type_struct");
    proj_names[0] = Z3_mk_string_symbol(ctx, "pointer_object");
    proj_names[1] = Z3_mk_string_symbol(ctx, "pointer_offset");
    proj_sorts[0] = bv64_sort;
    proj_sorts[1] = bv64_sort;
    pointer_sort = Z3_mk_tuple_sort(ctx, mk_tuple_name, 2, proj_names, proj_sorts, &mk_pointer_sort_decl, proj_decls);
    get_object = proj_decls[0];
    get_offset = proj_decls[1];
    /*criamos as constantess
    cada mem_i representa uma posicao na memoria para alocar ponteiro*/
    mem_null = Z3_mk_numeral(ctx, "0", bv64_sort);
    mem_2 = Z3_mk_numeral(ctx, "2", bv64_sort);
    mem_3 = Z3_mk_numeral(ctx, "3", bv64_sort);
    mem_4 = Z3_mk_numeral(ctx, "4", bv64_sort);
    size5 = Z3_mk_numeral(ctx, "5", bv64_sort);
    TRUE = Z3_mk_true(ctx);
    FALSE = Z3_mk_false(ctx);
    zero = Z3_mk_numeral(ctx, "0", bv64_sort);
    one = Z3_mk_numeral(ctx, "1", bv64_sort);
    two = Z3_mk_numeral(ctx, "2", bv64_sort);
    three = Z3_mk_numeral(ctx, "3", bv64_sort);
    /*vms definir vars de memoria. Como sao 3 ponteiros e cada um possui 2 elementos, vms precisar de 6*/
    alloc0 = mk_var(ctx, "alloc0", array_sort);
    alloc1 = mk_var(ctx, "alloc1", array_sort);
    alloc2 = mk_var(ctx, "alloc2", array_sort);
    alloc3 = mk_var(ctx, "alloc3", array_sort);
    alloc4 = mk_var(ctx, "alloc4", array_sort);
    alloc5 = mk_var(ctx, "alloc5", array_sort);
    alloc6 = mk_var(ctx, "alloc6", array_sort);
    /*existem 3 vo1.p, vo2.p = 2, vo3.p = 3*/
    id0 = mk_var(ctx,"id0",bv64_sort);
    id1 = mk_var(ctx,"id1",bv64_sort);
    id2 = mk_var(ctx,"id2",bv64_sort);
    /*p_i vai representar se a memoria na p_i esta usada. Sao 3*/
    p0 = mk_var(ctx, "p0", pointer_sort);
    p1 = mk_var(ctx, "p1", pointer_sort);
    p2 = mk_var(ctx, "p2", pointer_sort);
    /*s_i representa o tamanho do ponteiro*/
    s0 = mk_var(ctx,"s0",bv64_sort);
    s1 = mk_var(ctx,"s1",bv64_sort);
    s2 = mk_var(ctx,"s2",bv64_sort);
    /*malloc rho vai representar */
    malloc_r0 = mk_var(ctx, "malloc_r0", pointer_sort);
    malloc_r1 = mk_var(ctx, "malloc_r1", pointer_sort);
    malloc_r2 = mk_var(ctx, "malloc_r2", pointer_sort);
    /*q0 representa ponteiro que vai receber*/

    /*constructing C*/
    /*recebeu id 1*/
    c[0] = Z3_mk_eq(ctx, id0, one);
    c[1] = Z3_mk_eq(ctx, loc0, mem_2);
    c[2] = Z3_mk_eq(ctx, s0, size5);
    c[3] = Z3_mk_eq(ctx, alloc1, Z3_mk_store(ctx, alloc0, loc0, TRUE));
    c[4] = Z3_mk_eq(ctx, dealloc1, Z3_mk_store(ctx, dealloc0, loc0, FALSE));


    c[5] = Z3_mk_eq(ctx, malloc_r0, mk_binary_app(ctx, mk_pointer_sort_decl, loc0 ,zero));
    c[6] = Z3_mk_eq(ctx,p0,mk_binary_app(ctx, mk_pointer_sort_decl, mk_unary_app(ctx, get_object, malloc_r0) ,zero));
















};