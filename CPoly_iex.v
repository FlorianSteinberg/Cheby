Require Import Psatz.
Require Import Coquelicot.Coquelicot.
From mathcomp Require Import all_ssreflect.
Require Import CPoly_I.
From Bignums Require Import BigZ.
Import Rtrigo_def Rdefinitions Rpower R_sqrt Ratan.

Coercion fromZ := SFBI2.fromZ.

Module V := CPoly_interval SFBI2.

Export V.

Open Scope fexpr_scope.

Declare Scope sollya.
Notation " x * 2^ y " := 
  (Interval_specific_ops.Float x%bigZ y%bigZ) (at level 0) : sollya.
Notation " [ x ; y ] " :=  (Interval_interval_float.Ibnd x y) : sollya.
Notation "[| x1 , x2 , .. , xn |]" := (x1 :: x2 :: .. [:: xn] ..) : sollya.

Open Scope sollya.

Section Examples.

Let prec := 165%bigZ.

Ltac l_tac := 
  let u := fresh "u" in 
  (set u := I.lower _; vm_compute in u; rewrite {}/u;
   rewrite /I.T.toR /SFBI2.toX;
   set u := SFBI2.toF _; vm_compute in u; rewrite {}/u;
  rewrite /Interval_definitions.FtoX;
  rewrite /Interval_definitions.FtoR;
  set u := Z.pow_pos _; vm_compute in u; rewrite {}/u;
  set u := Z.pow_pos _; vm_compute in u; rewrite {}/u;
  rewrite /Interval_xreal.proj_val;
  lra).

Ltac r_tac :=
  let u := fresh "u" in 
  (set u := I.upper _; vm_compute in u; rewrite {}/u;
   rewrite /I.T.toR /SFBI2.toX;
   set u := SFBI2.toF _; vm_compute in u; rewrite {}/u;
   rewrite /Interval_definitions.FtoX;
   rewrite /Interval_definitions.FtoR;
   set u := Z.pow_pos _; vm_compute in u; rewrite {}/u;
   set u := Z.pow_pos _; vm_compute in u; rewrite {}/u;
   rewrite /Interval_xreal.proj_val;
   lra).

Notation " 'RInt[' a , b '](' e ')' " :=
    (iintz a b e)
  : iexpr_scope.

Definition ex1 := (RInt[0,1]('x))%iexpr.

Print ex1.
  
Eval vm_compute in mk_iexpr_ieval prec 10 ex1.

Eval lazy iota delta
  [iexpr_eval fexpr_eval ex1 iintz] beta in iexpr_eval ex1.


Lemma empty_interval a b : (a <= b <= a) -> b = a.
Proof. lra. Qed.

Lemma ex1_correct : RInt (fun x : R => x) 0 1 = 0.5%R.
Proof.
apply: empty_interval.
have ->: RInt (fun x : R => x) 0 1 = iexpr_eval ex1 by [].
apply: (@mk_iexpr_ieval_correct_r prec 10) => //.
- refine (fun x y _ _ => _).
  apply: ex_RInt_continuous => z _.
  by apply: continuous_id.
- l_tac.
r_tac.
Qed.

Definition fI := 
  ('x * 'x * 'x * 'x * 'x * (1 - 'x) * (1 - 'x) * (1 - 'x) *
                            (1 - 'x) * (1 - 'x) * (1 - 'x) *
      (c(197) + c(462) * 'x * 'x))
     / (c(530) * (1 + 'x * 'x))%fexpr.

Definition ex2 := (RInt[0,1](fI) + c(333,106))%iexpr.

Print ex2.
  
Eval vm_compute in mk_iexpr_ieval prec 20 ex2.

Definition eval_ex2 :=
  Eval vm_compute in mk_iexpr_ieval prec 10 ex2.

Eval lazy iota delta
  [fconstq fconstz iexpr_eval fexpr_eval fI ex2 iintz 
   iconstz iconstq] beta in iexpr_eval ex2.

Definition fR := (fun x : R =>
   (x * x * x * x * x * (1 - x) * (1 - x) * (1 - x) * (1 - x) * (1 - x) *
    (1 - x) * (197 + 462 * x * x) / (530 * (1 + x * x))))%R.

Lemma ex_RInt_ex a b : ex_RInt fR a b.
Proof.
apply: ex_RInt_continuous => z _.
repeat (apply: continuous_mult || apply: continuous_plus ||
          apply: continuous_id || apply: continuous_minus ||
          apply: continuous_const || apply: continuous_opp
          || apply: coquelicot_compl.continuous_Rinv_comp).
by nra.
Qed.

Lemma add_iexpr_wf a b : 
 iexpr_wf prec (a)%iexpr -> iexpr_wf prec (b)%iexpr -> 
 iexpr_wf prec (a + b)%iexpr.
Proof.
move=> aH bH.
by apply/mk_wf_correct.
Qed.

Lemma fI_iexpr_wf a b c d : 
 I.bounded (I.div prec (I.fromZ a) (I.fromZ b)) &&
 I.bounded (I.div prec (I.fromZ c) (I.fromZ d)) ->
 SFBI2.cmp
    (SFBI2.min (I.lower (I.div prec (I.fromZ a) (I.fromZ b)))
       (I.lower (I.div prec (I.fromZ c) (I.fromZ d))))
    (SFBI2.max (I.upper (I.div prec (I.fromZ a) (I.fromZ b)))
       (I.upper (I.div prec (I.fromZ c) (I.fromZ d)))) = Interval_xreal.Xlt ->
 iexpr_wf prec (RInt[a,b,c,d](fI))%iexpr. 
Proof.
move=> H H1.
rewrite /iintq /iexpr_wf H H1 => x y _ _.
set u := fexpr_eval _; vm_compute in u; rewrite {}/u.
by apply: ex_RInt_ex.
Qed.

Lemma ex2_correct : 
 3.1415%R <= (RInt fR 0 1 + 333 / 106)%R <= 3.1416%R.
Proof.
have := (@mk_iexpr_ieval_correct_r prec 10 _ _ ex2).
set u := mk_iexpr_ieval _ _ _.
have -> : u = eval_ex2 by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex2.
- apply: add_iexpr_wf; last by [].
  refine (fun x1 y1 _ _ => _).
  by apply: ex_RInt_ex.
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.

Definition ex3 := (RInt[0, 1, 1, 2](fI) +
                   RInt[1, 2, 1, 1](fI) + c(333,106))%iexpr.

Print ex3.
  
Eval vm_compute in mk_iexpr_ieval prec 20 ex3.

Definition eval_ex3 :=
  Eval vm_compute in mk_iexpr_ieval prec 20 ex3.

Print eval_ex3.

Eval lazy iota delta
  [fconstq fconstz iexpr_eval fexpr_eval ex3 fI iintq 
   iconstz iconstq] beta in iexpr_eval ex3.

Lemma ex3_correct : 
 3.1415926535897932384 <= (RInt fR 0 1 + 333 / 106)%R <= 
 3.1415926535897932385.
Proof.
have-> : RInt fR 0 1 = (RInt fR (0/1) (1/2) + RInt fR (1/2) (1/1))%R.
  rewrite [(_ + _)%R] (@RInt_Chasles _ fR).
  - by congr RInt; lra.
  - by apply: ex_RInt_ex.
  by apply: ex_RInt_ex.
have := (@mk_iexpr_ieval_correct_r prec 20 _ _ ex3).
set u := mk_iexpr_ieval _ _ _;
have -> : u = eval_ex3 by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex3.
- apply: add_iexpr_wf.
    apply: add_iexpr_wf.
    vm_cast_no_check (fI_iexpr_wf 0 1 1 2 (refl_equal true) 
      (refl_equal Interval_xreal.Xlt)).
    vm_cast_no_check (fI_iexpr_wf 1 2 1 1 (refl_equal true) 
      (refl_equal Interval_xreal.Xlt)).
    by [].
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.


End Examples.