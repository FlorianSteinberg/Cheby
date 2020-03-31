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
- apply: ex_RInt_continuous => z _.
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
   iexpr_wf prec (RInt[a,b,c,d](fI))%iexpr. 
Proof.
rewrite /iintq /iexpr_wf.
case: (_ && _) => //; case: (SFBI2.cmp _ _) => //.
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
    vm_cast_no_check (fI_iexpr_wf 0 1 1 2).
    vm_cast_no_check (fI_iexpr_wf 1 2 1 1).
    by [].
- vm_cast_no_check (refl_equal true).
- by l_tac.
by r_tac.
Qed.

(* Implementation naive dichotomy *)

(* Integration is limited to the Float type for the moment *)
Fixpoint split_r k (a b : SFBI2.type) f := 
 (if k is k1.+1 then
  let c := I.midpoint (I.bnd a b) in
    if (SFBI2.cmp a c) is Interval_xreal.Xlt then
    if (SFBI2.cmp c b) is Interval_xreal.Xlt then
           (split_r k1 a c f + split_r k1 c b f)%iexpr
    else (iint (fun=> FtoI_correct a)
               (fun=> FtoI_correct b) f)
    else (iint (fun=> FtoI_correct a)
               (fun=> FtoI_correct b) f)
  else (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) f)).

Lemma split_r0 a b f : split_r 0 a b f =
 (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) f).
Proof. by []. Qed.

Lemma split_rS k a b f (c := I.midpoint (I.bnd a b)): 
  split_r k.+1 a b f = 
    if (SFBI2.cmp a c) is Interval_xreal.Xlt then
    if (SFBI2.cmp c b) is Interval_xreal.Xlt then
           (split_r k a c f + split_r k c b f)%iexpr
    else (iint (fun=> FtoI_correct a)
               (fun=> FtoI_correct b) f)
    else (iint (fun=> FtoI_correct a)
               (fun=> FtoI_correct b) f).
Proof. by []. Qed.

Lemma RInt_split_r k a b f :
 SFBI2.cmp a b = Interval_xreal.Xlt ->
  (iexpr_wf prec (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) f)) ->
  iexpr_wf prec (split_r k a b f).
Proof.
move=> aLb pH.
suff iH : forall c d,
   SFBI2.cmp c d = Interval_xreal.Xlt ->
   I.subset (I.bnd c d) (I.bnd a b) ->
   iexpr_wf prec (split_r k c d f).
  by apply: iH (isubset_refl _).
elim: k => //.
  move=> c d; rewrite split_r0.
  move: aLb pH.
  rewrite /iexpr_wf /= /I.T.toR !SFBI2.real_correct
                       !SFBI2.cmp_correct
                       !SFBI2.min_correct
                       !SFBI2.max_correct.
  case Ec : (SFBI2.toX c) => [ |cr] //=.
  case Ed : (SFBI2.toX d) => [ |dr] //=.
  case: Raux.Rcompare_spec => //=.
  case Ea : (SFBI2.toX a) => [ |ar] //=.
  case Eb : (SFBI2.toX b) => [ |br] //=.
  case: Raux.Rcompare_spec => //.
  rewrite /Rbasic_fun.Rmin /Rbasic_fun.Rmax.
  case: RIneq.Rle_dec; try lra.
  case: Raux.Rcompare_spec => //=; try lra.
  by case: Raux.Rcompare_spec => //=; try lra;
     case: Raux.Rcompare_spec => //=; try lra;
     case: RIneq.Rle_dec; try lra;
     case: Raux.Rcompare_spec => //= *; try lra;
     apply: (@ex_RInt_Chasles_1 _ _ _ _ br); try lra;
     apply: (@ex_RInt_Chasles_2 _ _ ar); try lra.
move=> k IH c d cdH iH.
have EF : iexpr_wf prec (iint (fun=> FtoI_correct c) (fun=> FtoI_correct d) f).
  move: aLb pH cdH iH.
  rewrite /iexpr_wf /= /I.T.toR !SFBI2.real_correct
                       !SFBI2.cmp_correct
                       !SFBI2.min_correct
                       !SFBI2.max_correct.
  case Ec : (SFBI2.toX c) => [ |cr] //=;
  case Ed : (SFBI2.toX d) => [ |dr] //=;
  case Ea : (SFBI2.toX a) => [ |ar] //=;
  case Eb : (SFBI2.toX b) => [ |br] //=.
  rewrite /Rbasic_fun.Rmin /Rbasic_fun.Rmax.
  by (repeat ((case: RIneq.Rle_dec; try lra) ||
          (case: Raux.Rcompare_spec => //; try lra))) => *;
     apply: (@ex_RInt_Chasles_1 _ _ _ _ br); try lra;
     apply: (@ex_RInt_Chasles_2 _ _ ar); try lra.
rewrite split_rS.
case Ecp : SFBI2.cmp => //.
case Epd : SFBI2.cmp => //.
by apply/mk_wf_correct; split;
   apply: IH => //;
   move: cdH aLb iH Ecp Epd;
   move: (I.midpoint _) => u;
   rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct;
   repeat ((case: Raux.Rcompare_spec => //; try lra) ||
           (case : (SFBI2.toX _) => [ |?] //=)).
Qed.

Lemma eval_split_r k a b f :
  SFBI2.cmp a b = Interval_xreal.Xlt ->
  (iexpr_wf prec (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) f)) ->
  iexpr_eval (split_r k a b f) =
  iexpr_eval (iint (fun=> FtoI_correct a) (fun=> FtoI_correct b) f).
Proof.
move=> aLb pH.
have abE : ex_RInt (fexpr_eval f) (I.T.toR a) (I.T.toR b).
  move: aLb pH; rewrite /iexpr_wf.
  rewrite /I.T.toR /=
             !SFBI2.real_correct !SFBI2.cmp_correct
             !SFBI2.min_correct !SFBI2.max_correct /=
             /Rbasic_fun.Rmin /Rbasic_fun.Rmax.
  do 2 (case : (SFBI2.toX _) => [ |?] //=; try lra).
  by do 2 ((case: RIneq.Rle_dec => //; try lra) ||
          (case: Raux.Rcompare_spec; try lra)). 
suff iH : forall c d,
   SFBI2.cmp c d = Interval_xreal.Xlt ->
   I.subset (I.bnd c d) (I.bnd a b) ->
   iexpr_eval (split_r k c d f) =
   iexpr_eval (iint (fun=> FtoI_correct c) (fun=> FtoI_correct d) f).
  by apply: iH (isubset_refl _).
elim: k => // k IH c d cdH iH.
rewrite split_rS.
case Ecp : SFBI2.cmp => //.
case Epd : SFBI2.cmp => //.
apply: etrans (_ : (iexpr_eval _ + iexpr_eval _)%R = _); first by [].
rewrite !IH //; last 2 first.
- by move: cdH aLb iH Ecp Epd;
     move: (I.midpoint _) => u;
     rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct;
     repeat ((case: Raux.Rcompare_spec => //; try lra) ||
             (case : (SFBI2.toX _) => [ |?] //=)).
- by move: cdH aLb iH Ecp Epd;
     move: (I.midpoint _) => u;
     rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct;
     repeat ((case: Raux.Rcompare_spec => //; try lra) ||
             (case : (SFBI2.toX _) => [ |?] //=)).
apply: RInt_Chasles.
  apply: ex_RInt_Chasles_1; last first.
    apply: ex_RInt_Chasles_2; last by exact: abE.
    move: aLb cdH iH.
    rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct.
    do 4 (case : (SFBI2.toX _) => [ |?] //=).
    by repeat (case: Raux.Rcompare_spec=> //=; try lra).
  move: (I.midpoint _) aLb cdH iH Ecp Epd => u.
  rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct.
  do 5 (case : (SFBI2.toX _) => [ |?] //=).
  by repeat (case: Raux.Rcompare_spec=> //=; try lra).
apply: ex_RInt_Chasles_1; last first.
  apply: ex_RInt_Chasles_2; last by exact: abE.
  move: (I.midpoint _) aLb cdH iH Ecp Epd => u.
  rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct.
  do 5 (case : (SFBI2.toX _) => [ |?] //=).
  by repeat (case: Raux.Rcompare_spec=> //=; try lra).
move: (I.midpoint _) aLb cdH iH Ecp Epd => u.
rewrite /= /I.T.toR !SFBI2.real_correct !SFBI2.cmp_correct.
do 5 (case : (SFBI2.toX _) => [ |?] //=).
by repeat (case: Raux.Rcompare_spec=> //=; try lra).
Qed.

Lemma fI_iexpr_wf_iint a b : 
  (iexpr_wf prec (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) fI)).
Proof.
rewrite /iexpr_wf.
case: (_ && _) => //.
case: (SFBI2.cmp _ _) => //.
by apply: ex_RInt_ex.
Qed.

Lemma fI_iexpr_eval_RInt a b : 
  (iexpr_eval (iint (fun=> FtoI_correct a)
             (fun=> FtoI_correct b) fI)) =
  (RInt fR (I.T.toR a) (I.T.toR b)).
Proof.
by rewrite /iexpr_eval.
Qed.

(* depth of the dichotomy *)
Definition depth := 5%nat.
(* degree of the polynomial *)
Definition degree := 11%nat.

Definition eval_expr :=
  Eval vm_compute in 
   mk_iexpr_ieval prec degree
     (split_r depth (SFBI2.fromZ 0) (SFBI2.fromZ 1) fI).

Print eval_expr.

Lemma minus_R a b c d : a - d <= c <= b - d ->  a <= c + d <= b.
Proof. by lra. Qed.

Lemma exr_correct : 
 3.1415926535897932384626433 <= (RInt fR 0 1 + 333 / 106)%R <= 
 3.1415926535897932384626434.
Proof.
apply: minus_R.
have <- : I.T.toR (SFBI2.fromZ 0) = 0 by [].
have <- : I.T.toR (SFBI2.fromZ 1) = 1%R by [].
rewrite -fI_iexpr_eval_RInt.
rewrite -(@eval_split_r depth); last 2 first.
- by [].
- by apply: fI_iexpr_wf_iint.
set ex := split_r _ _ _ _.
have := (@mk_iexpr_ieval_correct_r prec degree _ _ ex).
set u := (mk_iexpr_ieval prec degree ex).
have -> : u = eval_expr by vm_cast_no_check (refl_equal u).
apply; rewrite {u}/ex.
by exact: RInt_split_r depth  (SFBI2.fromZ 0) (SFBI2.fromZ 1) fI
         (refl_equal _) (fI_iexpr_wf_iint (SFBI2.fromZ 0) (SFBI2.fromZ 1)).
- by [].
- by l_tac.
by r_tac.
Qed.

End Examples.