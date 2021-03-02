Require Import Psatz.
Require Import Coquelicot.Coquelicot.
From mathcomp Require Import all_ssreflect.
Require Import CPoly_I.
From Bignums Require Import BigZ.
Import Rtrigo_def Rdefinitions Rpower Rpow_def R_sqrt Ratan.

Notation "x ^ y" := (pow x y) : R_scope.

Coercion fromZ := SFBI2.fromZ.

Module V := CPoly_interval SFBI2.

Export V.

Import V.

Open Scope fexpr_scope.

Declare Scope sollya.
Notation " x * 2^ y " := 
  (Specific_ops.Float x%bigZ y%bigZ) (at level 0) : sollya.
Notation " [ x ; y ] " :=  (Float.Ibnd x y) : sollya.
Notation "[| x1 , x2 , .. , xn |]" := (x1 :: x2 :: .. [:: xn] ..) : sollya.

Open Scope sollya.

Section Examples.

Let prec := 165%bigZ.

Ltac l_tac := 
  let u := fresh "u" in 
  (set u := I.lower _; vm_compute in u; rewrite {}/u;
   rewrite /I.T.toR /SFBI2.toX;
   set u := SFBI2.toF _; vm_compute in u; rewrite {}/u;
  rewrite /Basic.FtoX /Basic.FtoR;
  repeat (set u := Z.pow_pos _; vm_compute in u; rewrite {}/u);
  rewrite /Xreal.proj_val;
  lra).

Ltac r_tac :=
  let u := fresh "u" in 
  (set u := I.upper _; vm_compute in u; rewrite {}/u;
   rewrite /I.T.toR /SFBI2.toX;
   set u := SFBI2.toF _; vm_compute in u; rewrite {}/u;
   rewrite /Basic.FtoX /Basic.FtoR;
   repeat (set u := Z.pow_pos _; vm_compute in u; rewrite {}/u);
   rewrite /Xreal.proj_val;
   lra).

Definition ex1 := (RInt[c(0),c(1)]('x))%iexpr.

Eval vm_compute in mk_iexpr_ieval prec 10 0 ex1.

Eval lazy iota delta
  [iexpr_eval fexpr_eval ex1] beta in iexpr_eval ex1.

Lemma empty_interval a b : (a <= b <= a) -> b = a.
Proof. lra. Qed.

Lemma ex1_correct : RInt (fun x : R => x) 0 1 = 0.5%R.
Proof.
apply: empty_interval.
have ->: RInt (fun x : R => x) 0 1 = iexpr_eval ex1 by [].
apply: (@mk_iexpr_ieval_correct_r prec 10 0) => //.
- apply: ex_RInt_continuous => z _.
  by apply: continuous_id.
- l_tac.
r_tac.
Qed.

Definition fI := 
  ('x ^ 5  * (1 - 'x) ^6 * (c(197) + c(462) * 'x ^ 2))
     / (c(530) * (1 + 'x ^ 2))%fexpr.

Definition ex2 := (RInt[c(0),c(1)](fI) + c(333,106))%iexpr.

Print ex2.
  
Eval vm_compute in mk_iexpr_ieval prec 20 0 ex2.

Definition eval_ex2 :=
  Eval vm_compute in mk_iexpr_ieval prec 10 0 ex2.

Eval lazy iota delta
  [fconstz iexpr_eval fexpr_eval fI ex2 Pos.to_nat
     Pos.iter_op Init.Nat.add] beta in iexpr_eval ex2.

Definition fR := (fun x : R =>
   (x ^ 5 * (1 - x) ^ 6 * (197 + 462 * x ^ 2) / (530 * (1 + x ^ 2))))%R.

Lemma ex_RInt_ex a b : ex_RInt fR a b.
Proof.
apply: ex_RInt_continuous => z _.
repeat (apply: continuous_mult || apply: continuous_plus ||
          apply: continuous_id || apply: continuous_minus ||
          apply: continuous_const || apply: continuous_opp
          || apply: Coquelicot.continuous_Rinv_comp).
by nra.
Qed.

Lemma add_iexpr_wf n k a b : 
 mk_iexpr_wf prec n k (a)%iexpr -> mk_iexpr_wf prec n k (b)%iexpr -> 
 mk_iexpr_wf prec n k (a + b)%iexpr.
Proof.
move=> aH bH.
by apply/mk_wf_correct.
Qed.

Lemma fI_iexpr_wf n k a b :
   mk_iexpr_wf prec n k a -> mk_iexpr_wf prec n k b ->  
   mk_iexpr_wf prec n k (RInt[a, b](fI))%iexpr. 
Proof.
move=> H1 H2.
rewrite /mk_iexpr_wf /iexpr_wf.
case: (_ && _) => //; case: (SFBI2.cmp _ _) => //.
apply/mk2_wf_correct; repeat (split => //).
set u := fexpr_eval _; vm_compute in u; rewrite {}/u.
by apply: ex_RInt_ex.
Qed.

Lemma ex2_correct : 
 3.1415%R <= (RInt fR 0 1 + 333 / 106)%R <= 3.1416%R.
Proof.
have := (@mk_iexpr_ieval_correct_r prec 10 0 _ _ ex2).
set u := mk_iexpr_ieval _ _ _ _.
have -> : u = eval_ex2 by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex2.
- apply: add_iexpr_wf; last by [].
  by apply: fI_iexpr_wf.
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.

Definition ex3 := (RInt[c(0), c(1,2)](fI) +
                   RInt[c(1,2), c(1)](fI) + c(333,106))%iexpr.


Eval vm_compute in mk_iexpr_ieval prec 20 0 ex3.

Definition eval_ex3 :=
  Eval vm_compute in mk_iexpr_ieval prec 20 0 ex3.

Eval lazy iota delta
  [fconstz iexpr_eval fexpr_eval fI ex2 Pos.to_nat
     Pos.iter_op Init.Nat.add ex3] beta in iexpr_eval ex3.

Lemma ex3_correct : 
 3.1415926535897932384 <= (RInt fR 0 1 + 333 / 106)%R <= 
 3.1415926535897932385.
Proof.
have-> : RInt fR 0 1 = (RInt fR 0 (1/2) + RInt fR (1/2) 1)%R.
  rewrite [(_ + _)%R] (@RInt_Chasles _ fR).
  - by congr RInt; lra.
  - by apply: ex_RInt_ex.
  by apply: ex_RInt_ex.
have := (@mk_iexpr_ieval_correct_r prec 20 0 _ _ ex3).
set u := mk_iexpr_ieval _ _ _ _;
have -> : u = eval_ex3.
 by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex3.
- apply: add_iexpr_wf.
    by apply: add_iexpr_wf; apply fI_iexpr_wf.
    by [].
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.

(* depth of the dichotomy *)
Definition depth := 5%nat.
(* degree of the polynomial *)
Definition degree := 11%nat.

Definition eval_ex4 :=
  Eval vm_compute in mk_iexpr_ieval prec degree depth ex2.

Lemma ex4_correct : 
 3.1415926535897932384626433 <= (RInt fR 0 1 + 333 / 106)%R <= 
 3.1415926535897932384626434.
Proof.
have := (@mk_iexpr_ieval_correct_r prec degree depth _ _ ex2).
set u := mk_iexpr_ieval _ _ _ _.
have -> : u = eval_ex4 by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex2.
- apply: add_iexpr_wf; last by [].
  by apply: fI_iexpr_wf.
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.

Definition gI := (c(4) / (1 + 'x ^ 2))%fexpr.

Definition gR x := (4 / (1 + x ^ 2))%R.

Lemma gI_iexpr_eval_RInt a b : 
  iexpr_eval (iint c(a)%iexpr c(b)%iexpr gI) = RInt gR (IZR a) (IZR b).
Proof. by rewrite /iexpr_eval. Qed.

Lemma ex_RInt_gex a b : ex_RInt gR a b.
Proof.
apply: ex_RInt_continuous => z _.
repeat (apply: continuous_mult || apply: continuous_plus ||
          apply: continuous_id || apply: continuous_minus ||
          apply: continuous_const || apply: continuous_opp
          || apply: Coquelicot.continuous_Rinv_comp).
by nra.
Qed.

Lemma gI_iexpr_wf n k a b : mk_iexpr_wf prec n k (RInt[c(a), c(b)](gI))%iexpr. 
Proof.
rewrite /mk_iexpr_wf /=.
case: (SFBI2.cmp _ _) => //.
by rewrite /mk2_wf; do 2 case: iexpr_icheck; repeat split => //;
   apply: ex_RInt_gex.
Qed.

Definition degree1 := 10%nat.
Definition depth1 := 4%nat.

Definition gexpr := (RInt[ c(0), 1]( gI)%iexpr).

Lemma gI_iexpr_wf_iint n k a b : 
  (mk_iexpr_wf prec n k (RInt[ c(a), c(b)]( gI)%iexpr)).
Proof.
rewrite /mk_iexpr_wf /=.
case: (SFBI2.cmp _ _) => //.
by rewrite /mk2_wf; do 2 case: iexpr_icheck; repeat split => //;
   apply: ex_RInt_gex.
Qed.

Definition eval_gexpr :=
  Eval vm_compute in mk_iexpr_ieval prec degree depth gexpr.

Lemma exgr_correct : 
  3.141592653589793238459 <= (RInt gR 0 1)%R <= 
  3.141592653589793238466.
Proof.
rewrite -gI_iexpr_eval_RInt  -/gexpr.
have := (@mk_iexpr_ieval_correct_r prec degree depth _ _ gexpr).
set u := mk_iexpr_ieval _ _ _ _.
have -> : u = eval_gexpr by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/gexpr.
- by apply: gI_iexpr_wf_iint.
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.


Definition hI := (sin(sin(x)))%fexpr.

Definition hR x := (sin (sin x))%R.

Lemma hI_iexpr_eval_RInt a b : 
  iexpr_eval (iint c(a)%iexpr c(b)%iexpr hI) = RInt hR (IZR a) (IZR b).
Proof. by rewrite /iexpr_eval. Qed.

Lemma ex_RInt_hex a b : ex_RInt hR a b.
Proof.
apply: ex_RInt_continuous => z _.
apply: continuous_comp.
apply: continuous_sin.
apply: continuous_sin.
Qed.

Lemma hI_iexpr_wf_iint n k a b : 
   mk_iexpr_wf prec n k (iint c(a)%iexpr c(b)%iexpr hI).
Proof.
rewrite /mk_iexpr_wf /=.
case: (SFBI2.cmp _ _) => //.
by rewrite /mk2_wf; do 2 case: iexpr_icheck; repeat split => //;
   apply: ex_RInt_hex.
Qed.

Definition hexpr := (RInt[ c(0), 1 ]( hI))%iexpr.

Definition eval_hexpr :=
  Eval vm_compute in mk_iexpr_ieval prec degree1 depth1 hexpr.

Lemma exhr_correct : 
  0.430606103120690604912376 <= (RInt hR 0 1)%R <= 
  0.430606103120690604912378.
Proof.
rewrite -hI_iexpr_eval_RInt.
have := (@mk_iexpr_ieval_correct_r prec degree1 depth1 _ _ hexpr).
set u := (mk_iexpr_ieval _ _ _ _).
have -> : u = eval_hexpr by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex.
- apply: hI_iexpr_wf_iint.
- by [].
- by l_tac.
by r_tac.
Time Qed.

(* 
(* florent *)
Let rx0 := (9/10)%R.
Let ex0 := c(9,10).
Let rr := (0.895)%R.
Let er := c(895,1000).
Let rxp := (sqrt (rx0 + rr * sqrt 2))%R.
*)

End Examples.