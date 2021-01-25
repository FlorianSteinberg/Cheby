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
  ('x ^ 5  * (1 - 'x) ^6 * (c(197) + c(462) * 'x ^ 2))
     / (c(530) * (1 + 'x ^ 2))%fexpr.

Definition ex2 := (RInt[0,1](fI) + c(333,106))%iexpr.

Print ex2.
  
Eval vm_compute in mk_iexpr_ieval prec 20 ex2.

Definition eval_ex2 :=
  Eval vm_compute in mk_iexpr_ieval prec 10 ex2.

Eval lazy iota delta
  [fconstq fconstz iexpr_eval fexpr_eval fI ex2 iintz 
   iconstz iconstq] beta in iexpr_eval ex2.

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

Definition toI (a : SFBI2.type) := 
  if SFBI2.real a then (FtoI a) else I.bnd I.nan I.nan.

Lemma toI_correct a : 
	Interval.contains (I.convert (toI a)) (Xreal.Xreal (SFBI2.toR a)).
Proof.
rewrite /toI.
have := @FtoI_correct a.
by case: SFBI2.real => //=; apply.
Qed.

(* Implementation naive dichotomy *)

(* Integration is limited to the Float type for the moment *)
Fixpoint split_r k (a b : SFBI2.type) f := 
 (if k is k1.+1 then
  let c := I.midpoint (I.bnd a b) in
    if (SFBI2.cmp a c) is Xreal.Xlt then
    if (SFBI2.cmp c b) is Xreal.Xlt then
    if [&& SFBI2.real a, SFBI2.real c & SFBI2.real b] then 
           (split_r k1 a c f + split_r k1 c b f)%iexpr
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f)
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f)
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f)
  else (iint (fun => toI_correct a)
             (fun=> toI_correct b) f)).

Lemma split_r0 a b f : split_r 0 a b f =
 (iint (fun=> toI_correct a) (fun=> toI_correct b) f).
Proof. by []. Qed.

Lemma split_rS k a b f (c := I.midpoint (I.bnd a b)): 
  split_r k.+1 a b f = 
    if (SFBI2.cmp a c) is Xreal.Xlt then
    if (SFBI2.cmp c b) is Xreal.Xlt then
    if [&& SFBI2.real a, SFBI2.real c & SFBI2.real b] then 
           (split_r k a c f + split_r k c b f)%iexpr
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f)
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f)
    else (iint (fun=> toI_correct a)
               (fun=> toI_correct b) f).
Proof. by []. Qed.

Lemma RInt_split_r k a b f :
 SFBI2.cmp a b = Xreal.Xlt -> SFBI2.real a -> SFBI2.real b ->
  (iexpr_wf prec (iint (fun=> toI_correct a)
             (fun=> toI_correct b) f)) ->
  iexpr_wf prec (split_r k a b f).
Proof.
move=> aLb aF bF pH.
suff iH : forall c d,
   SFBI2.cmp c d = Xreal.Xlt -> SFBI2.real c -> SFBI2.real d ->
   I.subset (I.bnd c d) (I.bnd a b) ->
   iexpr_wf prec (split_r k c d f).
  by apply: iH (isubset_refl _).
elim: k => //.
  move=> c d cLd cF dF; move: aLb cLd pH.
  rewrite split_r0 /iexpr_wf /toI /=.
  rewrite  !SFBI2.cmp_correct.
  rewrite [SFBI2.classify a]I.F'.classify_real //.
  rewrite [SFBI2.classify b]I.F'.classify_real //.
  rewrite [SFBI2.classify c]I.F'.classify_real //.
  rewrite [SFBI2.classify d]I.F'.classify_real //.
  move: (aF) (bF) (cF) (dF); rewrite 4!SFBI2.real_correct.
  case axE : SFBI2.toX => [ | ax] // _.
  case bxE : SFBI2.toX => [ | bx] // _.
  case cxE : SFBI2.toX => [ | cx] // _.
  case dxE : SFBI2.toX => [ | dx] //= _.
  (do 2 case: Raux.Rcompare_spec => //)  => axLbx cxLdx _ _.
  rewrite aF bF cF dF //=.
  have aE : SFBI2.toR a = ax.
    suff : Xreal.Xreal (SFBI2.toR a) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct.
  have bE : SFBI2.toR b = bx.
    suff : Xreal.Xreal (SFBI2.toR b) = Xreal.Xreal bx by case.
    by rewrite -I.F'.real_correct.
  have cE : SFBI2.toR c = cx.
    suff : Xreal.Xreal (SFBI2.toR c) = Xreal.Xreal cx by case.
    by rewrite -I.F'.real_correct.
  have dE : SFBI2.toR d = dx.
    suff : Xreal.Xreal (SFBI2.toR d) = Xreal.Xreal dx by case.
    by rewrite -I.F'.real_correct.
  have minHab : SFBI2.toX (SFBI2.min a b) = Xreal.Xreal ax.
    have := SFBI2.min_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmin; case: RIneq.Rle_dec => //; lra.
  have maxHab : SFBI2.toX (SFBI2.max a b) = Xreal.Xreal bx.
    have := SFBI2.max_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmax; case: RIneq.Rle_dec => //; lra.
  have minHcd: SFBI2.toX (SFBI2.min c d) =  Xreal.Xreal cx.
    have := SFBI2.min_correct c d.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX c]I.F'.real_correct // dxE cE.
    rewrite /Rbasic_fun.Rmin; case: RIneq.Rle_dec => //; lra.
  have maxHcd: SFBI2.toX (SFBI2.max c d) = Xreal.Xreal dx.
    have := SFBI2.max_correct c d.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX c]I.F'.real_correct // dxE cE.
    rewrite /Rbasic_fun.Rmax; case: RIneq.Rle_dec => //; lra.
  have minHabE : SFBI2.toR (SFBI2.min a b) = ax.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.min a b)) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct minHab.
  have maxHabE : SFBI2.toR (SFBI2.max a b) = bx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.max a b)) = Xreal.Xreal bx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct maxHab.
  have minHcdE : SFBI2.toR (SFBI2.min c d) = cx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.min c d)) = Xreal.Xreal cx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct minHcd.
  have maxHcdE : SFBI2.toR (SFBI2.max c d) = dx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.max c d)) = Xreal.Xreal dx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct maxHcd.
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct minHab. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct maxHab. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct minHcd. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct maxHcd. 
  rewrite minHab maxHab /= minHcd maxHcd /=.
  by do 4 case: Raux.Rcompare_spec => //=; try lra;
    rewrite minHabE maxHabE minHcdE maxHcdE => *;
    apply: (@ex_RInt_Chasles_2 _ _ ax) => //; try lra;
    apply: (@ex_RInt_Chasles_1 _ _ _ _ bx) => //; try lra.
move=> k IH c d cLd cF dF iH.
have EF : iexpr_wf prec (iint (fun=> toI_correct c) (fun=> toI_correct d) f).
  move: aLb cLd pH iH => /=.
  rewrite /iexpr_wf /toI /=.
  rewrite  !SFBI2.cmp_correct.
  rewrite [SFBI2.classify a]I.F'.classify_real //.
  rewrite [SFBI2.classify b]I.F'.classify_real //.
  rewrite [SFBI2.classify c]I.F'.classify_real //.
  rewrite [SFBI2.classify d]I.F'.classify_real //.
  move: (aF) (bF) (cF) (dF); rewrite 4!SFBI2.real_correct.
  case axE : SFBI2.toX => [ | ax] // _.
  case bxE : SFBI2.toX => [ | bx] // _.
  case cxE : SFBI2.toX => [ | cx] // _.
  case dxE : SFBI2.toX => [ | dx] //= _.
  (do 2 case: Raux.Rcompare_spec => //)  => axLbx cxLdx _ _.
  rewrite aF bF cF dF //=.
  have aE : SFBI2.toR a = ax.
    suff : Xreal.Xreal (SFBI2.toR a) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct.
  have bE : SFBI2.toR b = bx.
    suff : Xreal.Xreal (SFBI2.toR b) = Xreal.Xreal bx by case.
    by rewrite -I.F'.real_correct.
  have cE : SFBI2.toR c = cx.
    suff : Xreal.Xreal (SFBI2.toR c) = Xreal.Xreal cx by case.
    by rewrite -I.F'.real_correct.
  have dE : SFBI2.toR d = dx.
    suff : Xreal.Xreal (SFBI2.toR d) = Xreal.Xreal dx by case.
    by rewrite -I.F'.real_correct.
  have minHab : SFBI2.toX (SFBI2.min a b) = Xreal.Xreal ax.
    have := SFBI2.min_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmin; case: RIneq.Rle_dec => //; lra.
  have maxHab : SFBI2.toX (SFBI2.max a b) = Xreal.Xreal bx.
    have := SFBI2.max_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmax; case: RIneq.Rle_dec => //; lra.
  have minHcd: SFBI2.toX (SFBI2.min c d) =  Xreal.Xreal cx.
    have := SFBI2.min_correct c d.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX c]I.F'.real_correct // dxE cE.
    rewrite /Rbasic_fun.Rmin; case: RIneq.Rle_dec => //; lra.
  have maxHcd: SFBI2.toX (SFBI2.max c d) = Xreal.Xreal dx.
    have := SFBI2.max_correct c d.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX c]I.F'.real_correct // dxE cE.
    rewrite /Rbasic_fun.Rmax; case: RIneq.Rle_dec => //; lra.
  have minHabE : SFBI2.toR (SFBI2.min a b) = ax.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.min a b)) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct minHab.
  have maxHabE : SFBI2.toR (SFBI2.max a b) = bx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.max a b)) = Xreal.Xreal bx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct maxHab.
  have minHcdE : SFBI2.toR (SFBI2.min c d) = cx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.min c d)) = Xreal.Xreal cx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct minHcd.
  have maxHcdE : SFBI2.toR (SFBI2.max c d) = dx.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.max c d)) = Xreal.Xreal dx by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct maxHcd.
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct minHab. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct maxHab. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct minHcd. 
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct maxHcd. 
  rewrite minHab maxHab /= minHcd maxHcd /=.
  do 4 case: Raux.Rcompare_spec => //=; try lra;
    rewrite minHabE maxHabE minHcdE maxHcdE => *;
    apply: (@ex_RInt_Chasles_2 _ _ ax) => //; try lra;
    apply: (@ex_RInt_Chasles_1 _ _ _ _ bx) => //; try lra.
rewrite split_rS.
case Ecp : SFBI2.cmp => //.
case Epd : SFBI2.cmp => //.
case: (boolP [&& _, _ & _]) => //.
case/and3P=> c1F m1F d1F.
by apply/mk_wf_correct; split; apply: IH => //;
   move: cLd aLb iH Ecp Epd;
   move: (I.midpoint _) m1F => u uF;
   rewrite !SFBI2.cmp_correct !I.F'.classify_real //=;
   rewrite !SFBI2.cmp_correct !I.F'.classify_real //=;
   rewrite !I.F'.real_correct //=;
   do 7 case: Raux.Rcompare_spec => //=; lra.
Qed.

Lemma eval_split_r k a b f :
  SFBI2.cmp a b = Xreal.Xlt -> SFBI2.real a -> SFBI2.real b ->
  (iexpr_wf prec (iint (fun=> toI_correct a)
             (fun=> toI_correct b) f)) ->
  iexpr_eval (split_r k a b f) =
  iexpr_eval (iint (fun=> toI_correct a) (fun=> toI_correct b) f).
Proof.
move=> aLb aF bF pH.
have abE : ex_RInt (fexpr_eval f) (I.T.toR a) (I.T.toR b).
  move: aLb pH; rewrite /iexpr_wf.
  rewrite /toI /FtoI /= aF bF /= aF bF /=.
  rewrite !SFBI2.cmp_correct [SFBI2.classify a]I.F'.classify_real //.
  rewrite [SFBI2.classify b]I.F'.classify_real //.  
  move: (aF) (bF); rewrite 2!SFBI2.real_correct.
  case axE : SFBI2.toX => [ | ax] // _.
  case bxE : SFBI2.toX => [ | bx] // _.
  have aE : SFBI2.toR a = ax.
    suff : Xreal.Xreal (SFBI2.toR a) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct.
  have bE : SFBI2.toR b = bx.
    suff : Xreal.Xreal (SFBI2.toR b) = Xreal.Xreal bx by case.
    by rewrite -I.F'.real_correct.
  rewrite aE bE /=; case: Raux.Rcompare_spec => // axLbx _.
  have minHab : SFBI2.toX (SFBI2.min a b) = Xreal.Xreal ax.
    have := SFBI2.min_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmin; case: RIneq.Rle_dec => //; lra.
  have maxHab : SFBI2.toX (SFBI2.max a b) = Xreal.Xreal bx.
    have := SFBI2.max_correct a b.
    rewrite !I.F'.classify_real / Xreal.Xbind2  //=.
    rewrite [SFBI2.toX a]I.F'.real_correct // bxE aE.
    rewrite /Rbasic_fun.Rmax; case: RIneq.Rle_dec => //; lra.
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct minHab.
  rewrite I.F'.classify_real; last by rewrite SFBI2.real_correct maxHab.
  rewrite minHab maxHab /=; case: Raux.Rcompare_spec => //; try lra.
  have -> : SFBI2.toR (SFBI2.min a b) = ax.
    suff : Xreal.Xreal (SFBI2.toR (SFBI2.min a b)) = Xreal.Xreal ax by case.
    by rewrite -I.F'.real_correct // SFBI2.real_correct minHab.
  suff -> : SFBI2.toR (SFBI2.max a b) = bx by [].
  suff : Xreal.Xreal (SFBI2.toR (SFBI2.max a b)) = Xreal.Xreal bx by case.
  by rewrite -I.F'.real_correct // SFBI2.real_correct maxHab.
suff iH : forall c d,
   SFBI2.cmp c d = Xreal.Xlt -> SFBI2.real c -> SFBI2.real d ->
   I.subset (I.bnd c d) (I.bnd a b) ->
   iexpr_eval (split_r k c d f) =
   iexpr_eval (iint (fun=> toI_correct c) (fun=> toI_correct d) f).
  by apply: iH (isubset_refl _).
elim: k => // k IH c d cdH cF dF iH.
rewrite split_rS.
case Ecp : SFBI2.cmp => //.
case Epd : SFBI2.cmp => //.
rewrite cF dF andbT andTb.
have [mF|//] := boolP (SFBI2.real (I.midpoint (I.bnd c d))).
rewrite /= cF dF in mF.
apply: etrans (_ : (iexpr_eval _ + iexpr_eval _)%R = _); first by [].
rewrite !IH //; last 4 first.
- by rewrite /= cF dF.
- move: Ecp Epd cdH aLb iH.
  rewrite /= cF dF /= !I.F'.classify_real // !SFBI2.cmp_correct //=.
  rewrite !I.F'.classify_real //.
  rewrite !I.F'.real_correct //=.
  (repeat case: Raux.Rcompare_spec => //=) => //=; try lra.
- by rewrite /= cF dF.
- move: Ecp Epd cdH aLb iH.
  rewrite /= cF dF /= !I.F'.classify_real // !SFBI2.cmp_correct //=.
  rewrite !I.F'.classify_real //.
  rewrite !I.F'.real_correct //=.
  (repeat case: Raux.Rcompare_spec => //=) => //=; try lra.
apply: RInt_Chasles.
  apply: ex_RInt_Chasles_1; last first.
    apply: ex_RInt_Chasles_2; last by exact: abE.
    move: aLb cdH iH.
    rewrite !SFBI2.cmp_correct /= !I.F'.classify_real //= !SFBI2.cmp_correct.
    rewrite !I.F'.classify_real //=  !I.F'.real_correct //=.
    by repeat (case: Raux.Rcompare_spec=> //=; try lra).
  move: aLb cdH iH Ecp Epd => /=.
  rewrite cF dF !I.F'.classify_real //=.
  rewrite !SFBI2.cmp_correct /= !I.F'.classify_real //= .
  rewrite  !I.F'.real_correct //=.
  by repeat (case: Raux.Rcompare_spec=> //=; try lra).
apply: ex_RInt_Chasles_1; last first.
  apply: ex_RInt_Chasles_2; last by exact: abE.
  move: aLb cdH iH Ecp Epd => /=.
  rewrite cF dF !I.F'.classify_real //=.
  rewrite !SFBI2.cmp_correct /= !I.F'.classify_real //= .
  rewrite  !I.F'.real_correct //=.
  by repeat (case: Raux.Rcompare_spec=> //=; try lra).
move: aLb cdH iH Ecp Epd => /=.
rewrite cF dF !I.F'.classify_real //=.
rewrite !SFBI2.cmp_correct /= !I.F'.classify_real //= .
rewrite  !I.F'.real_correct //=.
by repeat (case: Raux.Rcompare_spec=> //=; try lra).
Qed.

Lemma fI_iexpr_wf_iint a b : 
  (iexpr_wf prec (iint (fun=> toI_correct a) (fun=> toI_correct b) fI)).
Proof.
rewrite /iexpr_wf.
case: (_ && _) => //.
case: (SFBI2.cmp _ _) => //.
by apply: ex_RInt_ex.
Qed.

Lemma fI_iexpr_eval_RInt a b : 
  (iexpr_eval (iint (fun=> toI_correct a) (fun=> toI_correct b) fI)) =
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
- set ex := split_r _ _ _ _.
  have := (@mk_iexpr_ieval_correct_r prec degree _ _ ex).
  set u := (mk_iexpr_ieval prec degree ex).
  have -> : u = eval_expr by vm_cast_no_check (refl_equal u).
  apply; rewrite {u}/ex.
  - by exact: RInt_split_r depth  (SFBI2.fromZ 0) (SFBI2.fromZ 1) fI
           (refl_equal _)  (refl_equal _)  (refl_equal _)
           (fI_iexpr_wf_iint (SFBI2.fromZ 0) (SFBI2.fromZ 1)).
  - by [].
  - by l_tac.
  by r_tac.
- by [].
by [].
Time Qed.

Definition gI := (c(4) / (1 + 'x ^ 2))%fexpr.

Definition gR x := (4 / (1 + x ^ 2))%R.

Lemma gI_iexpr_eval_RInt a b : 
  (iexpr_eval (iint (fun=> toI_correct a) (fun=> toI_correct b) gI)) =
  (RInt gR (I.T.toR a) (I.T.toR b)).
Proof.
by rewrite /iexpr_eval.
Qed.

Lemma ex_RInt_gex a b : ex_RInt gR a b.
Proof.
apply: ex_RInt_continuous => z _.
repeat (apply: continuous_mult || apply: continuous_plus ||
          apply: continuous_id || apply: continuous_minus ||
          apply: continuous_const || apply: continuous_opp
          || apply: Coquelicot.continuous_Rinv_comp).
by nra.
Qed.

Lemma gI_iexpr_wf a b c d : 
   iexpr_wf prec (RInt[a,b,c,d](gI))%iexpr. 
Proof.
rewrite /iintq /iexpr_wf.
case: (_ && _) => //; case: (SFBI2.cmp _ _) => //.
set u := fexpr_eval _; vm_compute in u; rewrite {}/u.
by apply: ex_RInt_gex.
Qed.


Definition degree1 := 10%nat.
Definition depth1 := 4%nat.

Lemma gI_iexpr_wf_iint a b : 
  (iexpr_wf prec (iint (fun=> toI_correct a) (fun=> toI_correct b) gI)).
Proof.
rewrite /iexpr_wf.
case: (_ && _) => //.
case: (SFBI2.cmp _ _) => //.
by apply: ex_RInt_gex.
Qed.

Definition eval_gexpr :=
  Eval vm_compute in 
   mk_iexpr_ieval prec degree1
     (split_r depth1 (SFBI2.fromZ 0) (SFBI2.fromZ 1) gI).

Print eval_gexpr.

Lemma exgr_correct : 
  3.141592653589793238459 <= (RInt gR 0 1)%R <= 
  3.141592653589793238466.
Proof.
have <- : I.T.toR (SFBI2.fromZ 0) = 0 by [].
have <- : I.T.toR (SFBI2.fromZ 1) = 1%R by [].
rewrite -gI_iexpr_eval_RInt.
rewrite -(@eval_split_r depth1); last 2 first.
- by [].
- by apply: gI_iexpr_wf_iint.
- set ex := split_r _ _ _ _.
  have := (@mk_iexpr_ieval_correct_r prec degree1 _ _ ex).
  set u := (mk_iexpr_ieval prec degree1 ex).
  have -> : u = eval_gexpr by vm_cast_no_check (refl_equal u).
  apply; rewrite {u}/ex.
  - by exact: RInt_split_r depth1  (SFBI2.fromZ 0) (SFBI2.fromZ 1) gI
           (refl_equal _)  (refl_equal _)  (refl_equal _)
           (gI_iexpr_wf_iint (SFBI2.fromZ 0) (SFBI2.fromZ 1)).
  - by [].
  - by l_tac.
  by r_tac.
- by [].
by [].
Time Qed.

Definition hI := (sin(sin(x)))%fexpr.

Definition hR x := (sin (sin x))%R.

Lemma hI_iexpr_eval_RInt a b : 
  (iexpr_eval (iint (fun=> toI_correct a) (fun=> toI_correct b) hI)) =
  (RInt hR (I.T.toR a) (I.T.toR b)).
Proof.
by rewrite /iexpr_eval.
Qed.


Lemma ex_RInt_hex a b : ex_RInt hR a b.
Proof.
apply: ex_RInt_continuous => z _.
apply: continuous_comp.
apply: continuous_sin.
apply: continuous_sin.
Qed.

Lemma hI_iexpr_wf_iint a b : 
  (iexpr_wf prec (iint (fun=> toI_correct a) (fun=> toI_correct b) hI)).
Proof.
rewrite /iexpr_wf.
case: (_ && _) => //.
case: (SFBI2.cmp _ _) => //.
by apply: ex_RInt_hex.
Qed.

Definition eval_hexpr :=
  Eval vm_compute in 
   mk_iexpr_ieval prec degree1
     (split_r depth1 (SFBI2.fromZ 0) (SFBI2.fromZ 1) hI).

Lemma exhr_correct : 
  0.430606103120690604912376 <= (RInt hR 0 1)%R <= 
  0.430606103120690604912378.
Proof.
have <- : I.T.toR (SFBI2.fromZ 0) = 0 by [].
have <- : I.T.toR (SFBI2.fromZ 1) = 1%R by [].
rewrite -hI_iexpr_eval_RInt.
rewrite -(@eval_split_r depth1); last 2 first.
- by [].
- by apply: hI_iexpr_wf_iint.
- set ex := split_r _ _ _ _.
  have := (@mk_iexpr_ieval_correct_r prec degree1 _ _ ex).
  set u := (mk_iexpr_ieval prec degree1 ex).
  have -> : u = eval_hexpr by vm_cast_no_check (refl_equal u).
  apply; rewrite {u}/ex.
  - by exact: RInt_split_r depth1  (SFBI2.fromZ 0) (SFBI2.fromZ 1) hI
           (refl_equal _)  (refl_equal _)  (refl_equal _)
           (hI_iexpr_wf_iint (SFBI2.fromZ 0) (SFBI2.fromZ 1)).
  - by [].
  - by l_tac.
  by r_tac.
- by [].
by [].
Time Qed.

End Examples.