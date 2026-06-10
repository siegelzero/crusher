import crusher
import std/[sets]
import flatzinc/[parser, translator]

proc rep(label, src: string) =
  var tr = translate(parseFzn(src))
  echo "==== ", label, " ===="
  echo "  defs=", tr.conditionalSourceDefs.len
  echo "  t/post1 in channels: ",
    ("t" in tr.channelVarNames) or ("post1" in tr.channelVarNames)

# (A) My 3-value full-coverage control (FAILED in the suite)
rep("A: 3-value, 3 implications, common array", """
var 0..2: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: c :: output_var;
var 0..9: t :: output_var;
array [1..3] of var int: src_arr ::var_is_introduced = [a, b, c];
var bool: b_cond0 ::var_is_introduced ::is_defined_var;
var bool: b_cond1 ::var_is_introduced ::is_defined_var;
var bool: b_cond2 ::var_is_introduced ::is_defined_var;
var bool: b_a ::var_is_introduced ::is_defined_var;
var bool: b_b ::var_is_introduced ::is_defined_var;
var bool: b_c ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 0, b_cond0) :: defines_var(b_cond0);
constraint int_eq_reif(cond, 1, b_cond1) :: defines_var(b_cond1);
constraint int_eq_reif(cond, 2, b_cond2) :: defines_var(b_cond2);
constraint int_eq_reif(t, a, b_a) :: defines_var(b_a);
constraint int_eq_reif(t, b, b_b) :: defines_var(b_b);
constraint int_eq_reif(t, c, b_c) :: defines_var(b_c);
constraint bool_clause([b_a], [b_cond0]);
constraint bool_clause([b_b], [b_cond1]);
constraint bool_clause([b_c], [b_cond2]);
solve satisfy;
""")

# (B) Same but condition domain 1..3 (avoid 0)
rep("B: 3-value 1..3, 3 implications, common array", """
var 1..3: cond :: output_var;
var 0..9: a :: output_var;
var 0..9: b :: output_var;
var 0..9: c :: output_var;
var 0..9: t :: output_var;
array [1..3] of var int: src_arr ::var_is_introduced = [a, b, c];
var bool: b_cond0 ::var_is_introduced ::is_defined_var;
var bool: b_cond1 ::var_is_introduced ::is_defined_var;
var bool: b_cond2 ::var_is_introduced ::is_defined_var;
var bool: b_a ::var_is_introduced ::is_defined_var;
var bool: b_b ::var_is_introduced ::is_defined_var;
var bool: b_c ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(cond, 1, b_cond0) :: defines_var(b_cond0);
constraint int_eq_reif(cond, 2, b_cond1) :: defines_var(b_cond1);
constraint int_eq_reif(cond, 3, b_cond2) :: defines_var(b_cond2);
constraint int_eq_reif(t, a, b_a) :: defines_var(b_a);
constraint int_eq_reif(t, b, b_b) :: defines_var(b_b);
constraint int_eq_reif(t, c, b_c) :: defines_var(b_c);
constraint bool_clause([b_a], [b_cond0]);
constraint bool_clause([b_b], [b_cond1]);
constraint bool_clause([b_c], [b_cond2]);
solve satisfy;
""")

# (C) EVM-style 2-value full coverage, single target (KNOWN good shape)
rep("C: 2-value, 2 implications, single target", """
var 1..2: op :: output_var;
var 1..5: pre1 :: output_var;
var 1..5: pre2 :: output_var;
var 1..5: post1 :: output_var;
array [1..2] of var int: pre_arr ::var_is_introduced = [pre1, pre2];
var bool: b_nop1 ::var_is_introduced ::is_defined_var;
var bool: b_swap1 ::var_is_introduced ::is_defined_var;
var bool: d_nop ::var_is_introduced ::is_defined_var;
var bool: d_swap ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(op, 1, d_nop) :: defines_var(d_nop);
constraint int_eq_reif(op, 2, d_swap) :: defines_var(d_swap);
constraint int_eq_reif(post1, pre1, b_nop1) :: defines_var(b_nop1);
constraint int_eq_reif(post1, pre2, b_swap1) :: defines_var(b_swap1);
constraint bool_clause([b_nop1], [d_nop]);
constraint bool_clause([b_swap1], [d_swap]);
solve satisfy;
""")

# (D) EVM-style 3-value full coverage, single target
rep("D: 3-value op, 3 implications, single target", """
var 1..3: op :: output_var;
var 1..5: pre1 :: output_var;
var 1..5: pre2 :: output_var;
var 1..5: pre3 :: output_var;
var 1..5: post1 :: output_var;
array [1..3] of var int: pre_arr ::var_is_introduced = [pre1, pre2, pre3];
var bool: b_1 ::var_is_introduced ::is_defined_var;
var bool: b_2 ::var_is_introduced ::is_defined_var;
var bool: b_3 ::var_is_introduced ::is_defined_var;
var bool: d_1 ::var_is_introduced ::is_defined_var;
var bool: d_2 ::var_is_introduced ::is_defined_var;
var bool: d_3 ::var_is_introduced ::is_defined_var;
constraint int_eq_reif(op, 1, d_1) :: defines_var(d_1);
constraint int_eq_reif(op, 2, d_2) :: defines_var(d_2);
constraint int_eq_reif(op, 3, d_3) :: defines_var(d_3);
constraint int_eq_reif(post1, pre1, b_1) :: defines_var(b_1);
constraint int_eq_reif(post1, pre2, b_2) :: defines_var(b_2);
constraint int_eq_reif(post1, pre3, b_3) :: defines_var(b_3);
constraint bool_clause([b_1], [d_1]);
constraint bool_clause([b_2], [d_2]);
constraint bool_clause([b_3], [d_3]);
solve satisfy;
""")
