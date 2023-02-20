From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_trigo atan_asin_acos.
Import Rtrigo_def.
Import Rtrigo1.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(* The interpotation with the Chebyshev flavor                                *)
(*                     prodl l == compute the polynomial of lowest degree     *)
(*                                whose roots are exactly those in l          *)
(*           interpolation f l == compute the polynomial of lowest degree     *)
(*                                that evaluates in (f i) for all i in l      *)
(*           has_zeros f n a b == f has n zeros between a and b included      *)
(*           ierror f l x      == compute the error on x of the interpolation *)
(*                                the difference between                      *)
(*                                f x and (interpolation f l).[x]             *)
(*           cheby_nodes n     == list of the Chebyshev nodes of rank n       *)
(*          scheby_nodes a b n == list of the Chebyshev nodes of rank n for   *)
(*                                the interval [a, b]                         *)
(*           sum_cheby n x     == sum of the cos (i * x + x/2) for i <= n     *)
(*          dsprod_cheby n p q == discrete scalar product between polynomials *)
(*                                p and q at Chebyshev nodes of rank n        *)
(*     sdsprod_cheby a b n p q == discrete scalar product between polynomials *)
(*                                p and q at Chebyshev nodes of rank n for    *)
(*                                the interval [a, b]                         *)
(******************************************************************************)

Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0, expr0).

Definition rm1 := (mulr1, mul1r, mulr1n, expr1).

Section Interpolation.

Variable R : fieldType.
Variable f : R -> R.

Definition prodl (l : seq R) : {poly R} :=
  \prod_(i <- undup l) ('X - i%:P).

Local Notation "'W[ l ]" := (prodl l) (format "''W[' l ]").

Lemma prodl_memE i l :
 uniq l -> i \in l ->
 prodl l = 
 ('X - i%:P) * \prod_(j <- l | j != i) ('X - j%:P).
Proof.
move=> Hu; rewrite /prodl undup_id //.
elim: l Hu => //= a l IH /andP[aNIl /IH IH1].
rewrite inE; case: eqP => /= [Ha _| /eqP aDi /IH1 IH2].
  rewrite Ha !big_cons eqxx /=.
  congr (_ * _); rewrite [RHS]big_seq_cond 
                         [RHS](eq_bigl (fun i => (i \in l) && true)).
    by rewrite -big_seq_cond.
  by move=> j; case: eqP => // ->; rewrite (negPf aNIl).
by rewrite !big_cons eq_sym (negPf aDi) /= IH2 mulrCA.
Qed.

Lemma monic_prodl l : prodl l \is monic.
Proof.
apply: monic_prod => i _.
apply: monicXsubC.
Qed.

Lemma root_prodl l : root (prodl l) =i l.
Proof.
elim: l => [i|a l IH i]; rewrite /prodl /=.
  by rewrite big_nil rootE hornerE oner_eq0.
have [aIl|aNIl] := boolP (a \in l).
  by rewrite IH inE; case: eqP => [->|].
by rewrite big_cons [LHS]rootM root_XsubC inE -IH.
Qed.

Lemma size_prodl l : (size (prodl l) <= (size l).+1)%nat.
Proof.
elim: l => /= [|a l IH].
 by rewrite /prodl big_nil size_polyC; case: eqP.
rewrite /prodl /=; case: (boolP (_ \in _)) => H.
  by apply: leq_trans IH _.
rewrite big_cons.
apply: leq_trans (size_mul_leq _ _) _.
by rewrite size_XsubC.
Qed.

Lemma prodl_undup l :  prodl l = prodl (undup l).
Proof.
elim: l => //= a l IH.
rewrite /prodl /=; case: (boolP (_ \in _)) => H //=.
by rewrite mem_undup (negPf H) !big_cons [X in _ * X = _]IH.
Qed.

Lemma size_prodl_undup l :  size (prodl l) = (size (undup l)).+1.
Proof.
elim: l => //= [|a l IH].
  by rewrite /prodl big_nil size_polyC oner_neq0.
rewrite /prodl /=; case: (boolP (_ \in _)) => H //.
rewrite big_cons size_Mmonic ?IH ?size_XsubC ?monic_prodl //.
have : size ('X - a%:P) != 0%N by rewrite size_XsubC.
by apply: contra => /eqP->; rewrite size_poly0.
Qed.

Lemma size_prodl_uniq l : uniq l -> size (prodl l) = (size l).+1.
Proof.  by move=> H; rewrite -{2}(undup_id H) size_prodl_undup. Qed.

Lemma derivn_size (Q : ringType) (p : {poly Q}) :
  p ^`((size p).-1) = (lead_coef p *+ (size p).-1 `!)%:P.
Proof.
apply/polyP => [] [|i]; rewrite coef_derivn coefC /=.
  by rewrite addn0 ffactnn.
have/leq_sizeP->// : (size p <= (size p).-1 + i.+1)%nat.
  by case: size => // k; rewrite addnS ltnS leq_addr.
by rewrite mul0rn.
Qed.

Lemma monic_prodl_diff (i : R) l : \prod_(j <- l | j != i) ('X - j%:P) \is monic.
Proof.  by apply: monic_prod => *; exact: monicXsubC. Qed.

Lemma size_prodl_diff (i : R) l : uniq l -> 
  size (\prod_(j <- l | j != i) ('X - j%:P)) = (size l - (i \in l)).+1%nat.
Proof.
elim: l => [|a l IH] /=.
  by rewrite big_nil size_poly1.
rewrite big_cons inE [i == a]eq_sym.
case: eqP => /= [->|iDa] /andP[H1 Ul].
  rewrite subn1 big_seq_cond (eq_bigl (fun i => (i \in l) && true)) /= => [|j].
    by rewrite -big_seq_cond -{1}(undup_id Ul) size_prodl_uniq.
  by case: (boolP (j \in l)) => //; case: eqP => //-> /(negP H1).
rewrite size_monicM ?IH ?size_XsubC ?monicXsubC //; last first.
  by apply/monic_neq0/monic_prodl_diff.
case: (l) => //= b l1.
by rewrite [in RHS]subSn //; case: (_ \in _).
Qed.

Lemma prodl_deriv_fact l (n := size l) :
  uniq l -> (prodl l)^`(n) = (n `!)%:R%:P.
Proof.
move=> Ul.
rewrite {1}(pred_Sn n) -(size_prodl_uniq Ul) derivn_size.
have := monic_prodl l.
rewrite monicE => /eqP->.
by rewrite size_prodl_uniq.
Qed.

Fixpoint interpolation (l : seq R) : {poly R} :=
  if l is a :: l1 then
      let r := interpolation l1 in
      if a \in l1 then r else
        let q := prodl l1 in
        r + (f a - r.[a]) / q.[a] *: q
  else 0.

Local Notation "`P[ l ]" := (interpolation l) (format "`P[ l ]").

Lemma interpolation_nil : interpolation [::] = 0.
Proof. by []. Qed.

Lemma interpolationC a : interpolation [:: a] = (f a)%:P.
Proof. 
by rewrite /= [prodl _]big_nil !hornerC !rm0 divr1 alg_polyC.
Qed.

Lemma interpolation_cons a l :
  a \notin l -> 
  interpolation (a :: l) =
     interpolation l + 
     (f a - (interpolation l).[a])/(prodl l).[a] *: prodl l.
Proof. by move=> /= /negPf->. Qed.

Lemma horner_interpolation l i : 
   i \in l ->  (interpolation l).[i] = f i.
Proof.
suff: all (fun i => (interpolation l).[i] == f i) l.
  by move=> H Hi; apply/eqP/(allP H).
elim: l => //= a l IH.
have [aIl|aNIl] := boolP (_ \in _).
  by rewrite IH (allP IH).
rewrite !hornerE divfK; last first.
  by rewrite -mem_root root_prodl.
rewrite addrC subrK eqxx /=.
apply/allP=> b bIl.
rewrite !hornerE (eqP (allP IH _ bIl)).
rewrite (_ : _.[b] = 0) ?rm0 //.
by apply/eqP; rewrite -mem_root root_prodl.
Qed.

Lemma interpolation_size l : (size (interpolation l) <= size l)%nat.
Proof.
elim: l => /= [|a l IH].
  by rewrite size_poly0.
have [aIl|aNIl] := boolP (_ \in _).
  by apply: leq_trans IH _.
apply: leq_trans (size_add _ _) _.
rewrite geq_max (leq_trans IH _) // 
                (leq_trans (size_scale_leq _ _)) //.
by exact: size_prodl.
Qed.

Lemma interpolation_derivn_eq0 l (n := size l) : (interpolation l)^`(n) = 0.
Proof.
apply/polyP => [] i.
rewrite coef_derivn coefC /=.
have/leq_sizeP->// : (size (interpolation l) <= n + i)%nat.
  by apply: leq_trans (interpolation_size _) (leq_addr _ _).
by rewrite if_same mul0rn.
Qed.

End Interpolation.

Require Import Reals Coquelicot.Coquelicot Interval.Missing.Coquelicot Psatz.
Require Import Rstruct.

Lemma is_derive_horner p x :
  is_derive (horner p : R -> R) x (p^`()).[x].
Proof.
elim/poly_ind: p => [|p c IH].
  rewrite deriv0 hornerE.
  have F (y : R_AbsRing) : (fun x => 0) y = 0.[y] by rewrite hornerE.
  by apply: is_derive_ext F (is_derive_const _ _).
rewrite derivMXaddC !hornerE.
apply: (is_derive_ext (fun x => p.[x] * x + c)) => [t|].
  by rewrite !hornerE.
auto_derive; first by exists (p^`().[x]).
rewrite Rmult_1_r Rmult_1_l Rplus_comm.
congr (_ + _ * _).
by apply: is_derive_unique.
Qed.

Lemma Derive_horner p x : Derive (horner p) x = (p^`()).[x].
Proof. by apply: is_derive_unique; exact: is_derive_horner. Qed.

Lemma ex_derive_horner (p : {poly R}) x : ex_derive (horner p) x.
Proof. by exists ((p^`()).[x]); exact: is_derive_horner. Qed.

Lemma is_derive_n_horner p x n :
  is_derive_n (horner p : R -> R) n x (p^`(n)).[x].
Proof.
elim: n x => [|n IH] x //=.
have F y :  (p^`(n)).[y] = Derive_n (horner p) n y.
  by apply/sym_equal/is_derive_n_unique.
apply: (@is_derive_ext _ _
                (horner (p^`(n)))
                (Derive_n (horner p) n)) => //.
apply: is_derive_horner.
Qed.

Lemma Derive_n_horner p n x : Derive_n (horner p) n x = (p^`(n)).[x].
Proof. by apply: is_derive_n_unique; exact: is_derive_n_horner. Qed.

Lemma ex_derive_n_horner (p : {poly R}) (x : R) n : ex_derive_n (horner p) n x.
Proof.
case: n => //= n.
exists (p^`(n.+1)).[x] => /=.
apply: (@is_derive_ext _ _
                (horner (p^`(n)))
                (Derive_n (horner p) n)) => [t|].
  by rewrite Derive_n_horner.
by apply: is_derive_horner.
Qed.

Lemma continuous_horner (p : {poly R}) x : continuous (horner p) x.
Proof.
elim/poly_ind: p => /= [|p c IH].
  apply: continuous_ext => [y|]; first by rewrite !hornerE.
  by apply: continuous_const.
apply: continuous_ext => [y|]; first by rewrite !hornerE.
apply: continuous_plus; last by exact: continuous_const.
by apply: continuous_mult => //; exact: continuous_id.
Qed.

Lemma integrable_horner (p : {poly R}) x1 x2 : ex_RInt (horner p) x1 x2.
Proof.
apply: ex_RInt_continuous => x _.
by exact: continuous_horner.
Qed.

Lemma RInt_Derive_horner (p : {poly R}) a b : 
  RInt (horner (p^`())) a b = (p.[b] - p.[a])%R.
Proof.
rewrite -RInt_Derive //.
- by apply: RInt_ext => x; rewrite Derive_horner.
- by move=> x _; apply: ex_derive_horner.
move=> x _.
apply: continuous_ext; first by move=> y; rewrite Derive_horner.
apply: continuous_horner.
Qed.

Definition has_zeros f n a b := 
  exists l : seq R,
   [/\  uniq l,
        forall x,  x \in l ->  a <= x <= b /\ f x = 0 &
        size l = n].

Lemma has_zerosEs f n a b :
  has_zeros f n a b <->
  exists l : seq R,
   [/\  path.sorted Rltb l,
        forall x,  x \in l ->  a <= x <= b /\ f x = 0 &
        size l = n].
Proof.
split=> [] [l [H1 H2 H3]].
  exists (path.sort Rleb l); split => [|x|].
  - rewrite Rltb_sorted_uniq_leb sort_uniq H1 sort_sorted //.
    exact: Rleb_total.
  - by rewrite mem_sort; exact: H2.
  apply/eqP; rewrite -H3 -uniq_size_uniq ?sort_uniq //.
  by move=> a1; rewrite mem_sort.
exists l; split => //.
by move: H1; rewrite Rltb_sorted_uniq_leb => /andP[].
Qed.

Lemma has_zerosW f n a b c d :
  a <= c -> d <= b -> 
  has_zeros f n c d -> has_zeros f n a b.
Proof.
move=> H1 H2 [l [Hl1 Hl2 Hl3]]; exists l; split => // x xIl.
by case: (Hl2 _ xIl); lra.
Qed.

Lemma has_zeros_S_le f n a b : 
  has_zeros f n.+1 a b -> a <= b.
Proof.
case; case; first by case.
move=> c l [_ /(_ c) []//]; try lra.
by rewrite inE eqxx.
Qed.

Lemma has_zeros_0 f a b : has_zeros f 0 a b.
Proof. by exists [::]; split. Qed.

Lemma has_zeros_1 f a b : 
  has_zeros f 1 a b <-> (exists x, a <= x <= b /\ f x = 0).
Proof.
split=> [[[|x [|y l]] //=] |]; case=> //.
  move=> _ /(_ x) []; rewrite ?inE // => H1 H2 _.
  by exists x.
move=> x [H1 H2]; exists [::x]; split=> // y.
by rewrite inE => /eqP->.
Qed.

Lemma has_zeros_add f m n a b c d:
   b < c -> a <= b -> c <= d ->
   has_zeros f m a b -> has_zeros f n c d -> has_zeros f (m + n) a d.
Proof.
move=> H1 H2 H3 [l1 [H1l1 H2l1 H3l1]] [l2 [H1l2 H2l2 H3l2]].
exists (l1 ++ l2); split.
- rewrite cat_uniq H1l1 H1l2 andbT /=.
  apply/hasPn => x /H2l2 [HH1 _].
  apply/negP=> /H2l1 [HH2 _].
  by lra.
- by move=> x; rewrite mem_cat => /orP[/H2l1[]|/H2l2[]]; lra.
by rewrite size_cat H3l1 H3l2.
Qed.

Lemma has_zeros_split f n a b :
  has_zeros f n.+1 a b -> exists c d,
             [/\ a <= c <= b, c < d, has_zeros f 1 a c & has_zeros f n d b].
Proof.
move=> HH.
have aLb := has_zeros_S_le HH.
move: HH.
rewrite {1}has_zerosEs => [] [] [|x [|y k]]; case => // H1 H2 H3.
  exists b; exists (b + 1); split; try lra.
    by exists [::x]; split.
  by case: H3 => <-; apply: has_zeros_0.
case: (H2 x); rewrite ?inE ?eqxx => // Hx Hfx.
case: (H2 y); rewrite ?inE ?eqxx ?orbT => // Hy Hfy.
have Hxy : x < y.
  by apply/RltbP; case/andP: H1.
exists x; exists y; split; try lra.
  exists [::x]; split => // z.
  by rewrite inE => /eqP ->; lra.
apply/has_zerosEs.
exists [::y & k]; split => [|z Hz|] //=; first 2 last.
- by move: H3 => /= [->].
- by case/andP: H1.
case: (H2 z) => [|H4 H5].
  by rewrite inE Hz orbT.
split => //.
suff: y <= z by lra.
move: Hz; rewrite inE => /orP[/eqP->|Hz]; first by lra.
have/allP/(_ z Hz)/RltbP: all (Rltb y) k.
  apply: order_path_min; first by apply: Rltb_trans.
  by case/andP: H1.
by lra.
Qed.

Lemma has_zeros_deriv f n a b :
 (forall x, a < x < b -> ex_derive f x) ->
 (forall x, a <= x <= b -> continuous f x) ->
  has_zeros f n.+1 a b -> 
  has_zeros (Derive f) n a b.
Proof.
elim: n a b => [a b _ _ _|n IH a b Hd Hc]; first by exact: has_zeros_0.
case/has_zeros_split => c [d [H1c H2c /has_zeros_1 [a1 [Ha1 Ra1]]]].
case/has_zeros_split => c1 [d1 [H1d H2d /has_zeros_1 [a2 [Ha2 Ra2]]]] H1.
have F1 x : a1 < x < a2 -> derivable_pt f x.
  move=> HH; apply: ex_derive_Reals_0.
  by apply: Hd; lra.
have F2 x : a1 <= x <= a2 -> continuity_pt f x.
  by move=> HH; apply/continuous_continuity_pt/Hc; lra.
have [||x [P HP]] := Rolle f a1 a2 F1 F2; try lra.
have F3 : has_zeros (Derive f) 1 a x.
  apply/has_zeros_1; exists x; split => //; try lra.
  by rewrite Derive_Reals in HP.
have F4 : has_zeros f 1 a2 c1.
  apply/has_zeros_1; exists a2; split => //; try lra.
have F5 : has_zeros (Derive f) n a2 b.
  apply: IH => [y Hy|y Hy|].
  - by apply: Hd; lra.
  - by apply: Hc; lra.
  - case: (n) H1 => [|n1] H1.
      by apply: has_zerosW F4; lra.
    have F5 : d1 <= b by apply: has_zeros_S_le H1.
    by apply: has_zeros_add F4 H1; lra.
by apply: has_zeros_add F3 F5 => //; lra.
Qed.

Lemma has_zeros_deriv_n f m n a b :
 (forall x k, (k <= m)%nat -> a < x < b -> ex_derive_n f k x) ->
 (forall x k, (k <= m)%nat -> a <= x <= b -> continuous (Derive_n f k) x) ->
  has_zeros f n a b -> 
  has_zeros (Derive_n f m) (n - m) a b.
Proof.
case: (leqP n m).
  rewrite -subn_eq0 => /eqP-> *.
  by apply: has_zeros_0.
elim: m f n a b => [|m IH] f n a b mLn Hd Hc Hz //=.
  by rewrite subn0.
apply: has_zeros_deriv => [x aLxLb|x aLxLb|] //.
- by apply: (Hd x m.+1) => //; lra.
- by apply: Hc.
rewrite -subSn ?(leq_trans _ mLn) // subSS.
apply: IH => //; first by apply: leq_trans mLn.
  move=> x k kLm aLxLb.
  apply: Hd => //.
  by apply: leq_trans kLm _.
move=> x k kLm Hx.
apply: Hc => //.
by apply: leq_trans kLm _.
Qed.

Section bound.

Variable f : R -> R.
Variable n : nat.
Variable l : list R.
Hypothesis size_n : n = size l.
Hypothesis Ul : uniq l.
Variables a b c1 c2 : R.
Hypothesis c1La : c1 < a.
Hypothesis bLc2 : b < c2.
Hypothesis range : forall x : R, x \in l -> a <= x <= b.
Hypothesis deriv_f : 
  forall x k, c1 < x < c2 -> (k <= n)%nat -> ex_derive_n f k x.
Hypothesis cont_f :
 forall x k, (k <= n)%nat -> a <= x <= b ->
   continuous (Derive_n f k) x.

Definition ierror x := f x - (interpolation f l).[x].

Lemma ierror_val x :
  a <= x <= b -> ierror x != 0 -> 
  exists z, 
    a <= z <= b /\
    ierror x = (1 / (n `! %:R)) * (Derive_n f n z) * (prodl l).[x].
Proof.
move=> Hl Hi.
have NZWx : (prodl l).[x] != 0.
  apply: contra Hi => H.
  apply/eqP; rewrite /ierror.
  have/horner_interpolation-> : x \in l by rewrite -root_prodl; exact: H.
  lra.
pose c := ierror x / (prodl l).[x].
pose g y := ierror y - c * (prodl l).[y].
have F0 x1 k : (k <= n)%nat -> a < x1 < b -> ex_derive_n g k x1.
  apply:  ex_derive_n_minus_inter => [|y k1 k1Ln aLyLb].
    apply:  ex_derive_n_minus_inter=> [x2 k1 k1Ln aLx2Lb|*].
      by apply: deriv_f; try lra.
    by apply: ex_derive_n_horner.
  apply: ex_derive_n_scal_l.
  by apply: ex_derive_n_horner.
have F1 y k : (k <= n)%nat -> c1 < y < c2 ->
          Derive_n f k y - Derive_n (horner (interpolation f l)) k y
                         - Derive_n (fun y => c * (prodl l).[y]) k y = 
          Derive_n g k y.
  move=> kLn c1LyLc2.
  pose e := Rmin (y - c1) (c2 - y).
  have He : 0 < e.
     by rewrite /e /Rmin; case: Rle_dec; lra.
  pose pe := mkposreal _ He.
  rewrite /g /ierror !Derive_n_minus //.
  - exists (pos_div_2 pe) => y2 Hy2 k1 k1Ln.
    apply: deriv_f => //.
      move/ball_to_lra: Hy2; rewrite /= /e /Rmin.
      by case: Rle_dec; lra.
    by apply: leq_trans kLn; apply/leP.
  - by exists pe => *; apply: ex_derive_n_horner.
  - exists (pos_div_2 (pos_div_2 pe)) => y2 Hy2 k1 k1Ln.
    apply: ex_derive_n_minus.
      exists (pos_div_2 (pos_div_2 pe)) => y3 Hy3 k2 k2Ln.
      apply: deriv_f => //.
      move/ball_to_lra: Hy2.
      move/ball_to_lra: Hy3; rewrite /= /e /Rmin.
      by case: Rle_dec; lra.
      apply: leq_trans kLn.
      by apply: leq_trans (_ : k1 <= _)%nat; apply/leP.
    by exists pe => *; apply: ex_derive_n_horner.
  exists pe => *; apply: ex_derive_n_scal_l.
  by apply: ex_derive_n_horner.
have F2 y k : (k <= n)%nat -> a <= y <= b ->
              continuous (Derive_n g k) y.
  move=> kLn aLyLb.
  pose e := Rmin (y - c1) (c2 - y).
  have He : 0 < e.
     by rewrite /e /Rmin; case: Rle_dec; lra.
  pose pe := mkposreal _ He.
  apply: continuous_ext_loc.
    exists (pos_div_2 pe) => z /ball_to_lra /= Hz.
    apply: F1 => //.
    by move: Hz; rewrite /e /Rmin; case: Rle_dec; lra.
  repeat apply: continuous_minus.
  - by apply: cont_f.
  - apply: ex_derive_continuous.
      by apply: (ex_derive_n_horner _ _ k.+1).
  apply: ex_derive_continuous.
  apply: (@ex_derive_n_scal_l _ k.+1).
  by apply: ex_derive_n_horner.
have F3 : has_zeros g n.+1 a b.
  exists (x :: l); split => [|y|] //=.
  - by rewrite Ul andbT -root_prodl.
  - rewrite inE => /orP[/eqP->|Hy].
      split; rewrite // /g /c.
      by field; apply/eqP.
    split; first by apply: range.
    rewrite /g /ierror horner_interpolation //.
    have := Hy; rewrite -root_prodl => /eqP->.
    by toR; ring.
  have [[|z [|z1 l1]]] : has_zeros (Derive_n g n) 1 a b; rewrite -?size_n //.
  rewrite -(subSnn n).
  apply: has_zeros_deriv_n=>  //.
  exists (x :: l); split => [|x1|] /=.
  - by rewrite -root_prodl Ul andbT.
  - rewrite !inE => /orP[/eqP->|x1Il].
      split => //.
      rewrite /g /c /ierror /=; field.
      by apply/eqP.
    split; first by apply: range.
    rewrite /g /ierror.
    rewrite horner_interpolation //.
    rewrite (_ : _.[x1] = 0); try ring.
    apply/eqP.
    by rewrite [_ == _]root_prodl.
  by rewrite size_n.
have F4 : has_zeros (Derive_n g n) (n.+1 - n) a b.
  by apply: has_zeros_deriv_n.
rewrite subSnn in F4.
have /has_zeros_1[z [Hz]] := F4.
rewrite -(F1 _ _ (leqnn n)); last by lra.
rewrite Derive_n_horner.
rewrite {2}size_n.
rewrite interpolation_derivn_eq0 !hornerE.
rewrite Derive_n_scal_l.
rewrite Derive_n_horner.
rewrite {2}size_n.
rewrite prodl_deriv_fact // -size_n /c !hornerE => HH.
exists z; split=> //.
have HH1 : Derive_n f n z = ierror x / (prodl l).[x] * n`!%:R.
  move: HH; toR.
  set xx := Derive_n _ _ _; set yy := _ * _.
  lra.
rewrite HH1; toR.
field; split; first by apply/eqP.
move=> /(INR_eq _ 0) H.
by have := fact_gt0 n; rewrite H.
Qed.

End bound.

Definition cheby_nodes (n : nat) := [seq cos (i.*2.+1%:R * PI / n.*2%:R) | i <- seq.iota 0%nat n].

Lemma size_cheby_nodes n : size (cheby_nodes n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma cheby_nodes_bound n x :
  x \in cheby_nodes n -> -1 < x < 1.
Proof. 
move=> /mapP[i Hi ->].
set u := _ / _.
have Le : -1 <= cos u <= 1 by apply: COS_bound.
suff: cos u <> -1 /\ cos u <> 1 by lra.
have DD : INR n.*2 <> 0.
  case: (n) Hi => // m _; rewrite doubleS !S_INR.
  suff: (0 <= INR m.*2) by lra.
  by apply: pos_INR.
suff : sin u <> 0 => [|/sin_eq_0_0[k Hk]].
  move=> H; split; have := sin2_cos2 u; rewrite /Rsqr; nra.
have H1 : i.*2.+1%:R / n.*2%:R = IZR k.
  have: 0 < PI by have := Rgt_2PI_0; lra.
  rewrite /u in Hk; nra.
have : i.*2.+1%:R  = IZR k * n.*2%:R by rewrite -H1; toR; field.
rewrite !natr_INR !INR_IZR_INZ -mult_IZR => /eq_IZR.
rewrite Z_of_nat_S !Z_of_nat_double; lia.
Qed.

Lemma cheby_nodes_boundW n x :
  x \in cheby_nodes n -> -1 <= x <= 1.
Proof. by move/cheby_nodes_bound; lra. Qed.

Lemma root_cheby_nodes n : all (root 'T_n) (cheby_nodes n).
Proof.
apply/allP => x /mapP [i H1i ->]; apply/eqP.
rewrite -pT_Cheby; last by apply: COS_bound.
rewrite mem_iota /= add0n in H1i.
rewrite /=  [_.+1%:R](natrD _ 1) -!mul2n !natrM.
rewrite !natr_INR /=; toR.
have P_b := PI2_3_2.
have P_i : 0 <= INR i by apply: pos_INR.
have P_n : INR i + 1 <= INR n.
  rewrite -(plus_INR _ 1).
  by apply: le_INR; have /ltP := H1i; lia.
rewrite Cheby_cos; last first.
  split; first by apply: Rdiv_le_0_compat; nra.
  apply: Float.Generic_proof.Rdiv_ge_mult_pos; nra.
apply: cos_eq_0_1; exists (Z.of_nat i).
rewrite -INR_IZR_INZ.
field; lra.
Qed.

Lemma uniq_cheby_nodes n : uniq (cheby_nodes n).
Proof.
apply/(uniqP 0) => x y /=.
rewrite !inE size_cheby_nodes => Hx Hy.
rewrite !(nth_map 0%nat) ?size_iota // !nth_iota //.
rewrite !add0n.
rewrite /=  ![_.*2.+1%:R](natrD _ 1) -!mul2n !natrM.
rewrite !natr_INR -[INR 1]/1 -[INR 2]/2 => H.
apply: INR_eq.
have P_x : 0 <= INR x by apply: pos_INR.
have P_y : 0 <= INR y by apply: pos_INR.
have P_xn : INR x + 1 <= INR n.
  rewrite -(plus_INR _ 1).
  by apply: le_INR; have /ltP := Hx; lia.
have P_yn : INR y + 1 <= INR n.
  rewrite -(plus_INR _ 1).
  by apply: le_INR; have /ltP := Hy; lia.
have P_b := PI2_3_2.
have F : ((1 + 2 * INR x)%R * PI /
       (2 * INR n)%R) =
      ((1 + 2 * INR y)%R * PI /
       (2 * INR n)%R).
  apply: cos_inj => //.
    split.
      by apply: Rdiv_le_0_compat; nra.
    by apply: Float.Generic_proof.Rdiv_ge_mult_pos; nra.
  split.
    by apply: Rdiv_le_0_compat; nra.
  by apply: Float.Generic_proof.Rdiv_ge_mult_pos; nra.
suff : (1 + 2 * INR x) * PI = (1 + 2 * INR y) * PI.
  by nra.
have F1 x1 : x1 / (2 * INR n) * (2 * INR n) = x1.
  field; lra.
by rewrite -[_ * PI]F1 F F1.
Qed.

Lemma cheby_prod n : 
   'T_ n = (expn 2 n.-1)%nat%:R *:  \prod_(z <- cheby_nodes n) ('X - z%:P).
Proof.
set p := 'T_n.
have F1 : size p = n.+1.
  apply: size_pT.
  move=> x y; rewrite -[_%:R]/2; toR; lra. 
rewrite -coef_pTn {2}[n]pred_Sn -F1.
apply: all_roots_prod_XsubC.
- by rewrite F1 size_cheby_nodes.
- by apply: root_cheby_nodes.
rewrite uniq_rootsE.
apply: uniq_cheby_nodes.
Qed.

Lemma cheby_prodl n : 
   'T_ n = (expn 2 n.-1)%nat%:R *:  prodl (cheby_nodes n).
Proof.
by rewrite /prodl undup_id ?cheby_prod // uniq_cheby_nodes.
Qed.

Section ChebyBound.

Variable f : R -> R.
Variable c1 c2 : R.
Hypothesis c1LN1 : c1 < -1.
Hypothesis c2G1 : 1 < c2.

Variable n : nat.
Hypothesis deriv_f : 
  forall x k, c1 < x < c2 -> (k <= n)%nat -> ex_derive_n f k x.

Hypothesis cont_f :
 forall x k, (k <= n)%nat -> -1 <= x <= 1 -> continuous (Derive_n f k) x.

Lemma ierror_cheby x z :
  -1 <= x <= 1 ->
  (forall y,   -1 <= y <= 1 -> Rabs (Derive_n f n y) <= z) ->
  Rabs (ierror f (cheby_nodes n) x) <= (1 / ((expn 2 n.-1 * n `!) %:R)) * z.
Proof.
move=> Hx Hy.
have Hz : 0 <= z.
  suff: Rabs (Derive_n f n 0) <= z by split_Rabs; lra.
  by apply: Hy; lra.
have F1 : 0 < n`!%:R.
  rewrite natr_INR.
  by apply/lt_0_INR/ltP/fact_gt0.
have F2 : 0 < (expn 2 n.-1)%:R.
  rewrite natr_INR.
  by apply/lt_0_INR/ltP/expn_gt0.
have F3 : 0 < / (expn 2 n.-1)%:R.
  by apply: Rinv_0_lt_compat; lra.
have F4 : 0 < / n`!%:R.
  by apply: Rinv_0_lt_compat; lra.
have [/eqP-> | Hc] := boolP (ierror f (cheby_nodes n) x == 0).
  rewrite Rabs_R0.
  apply: Rmult_le_pos => //.
  apply: Stdlib.Rdiv_pos_compat; try lra.
  rewrite natr_INR.
  apply/lt_0_INR/leP/neq0_lt0n/eqP/eqP.
  by rewrite muln_eq0 negb_or -!lt0n expn_gt0 fact_gt0.
have [z1 [H1z1 ->]] := ierror_val (sym_equal (size_cheby_nodes n))
         (uniq_cheby_nodes n) c1LN1 c2G1 (@cheby_nodes_boundW n)
         deriv_f cont_f Hx Hc.
rewrite !Rabs_mult Rabs_R1 Rabs_inv; try lra.
rewrite Rabs_pos_eq; try lra.
rewrite natrM.
rewrite Rmult_comm/Rdiv Rinv_mult; try lra.
rewrite -!Rmult_assoc.
apply: Rmult_le_compat; last by apply: Hy; lra.
- apply: Stdlib.Rmult_le_pos_pos => //.
    rewrite Rmult_1_r.
    by apply: Rabs_pos.
- by lra.
- by apply: Rabs_pos.
- apply: Rmult_le_compat_r; try lra.
rewrite Rmult_1_r Rmult_1_l.
have -> : (prodl (cheby_nodes n)).[x] = / (expn 2 n.-1)%:R * ((pT _ n).[x]).
  rewrite cheby_prodl /prodl undup_id ?uniq_cheby_nodes //.
  rewrite hornerE.
  set xx : R := _.[x]; set yy : R :=  _%:R.
  by toR; field; rewrite /yy; lra.
rewrite Rabs_mult Rabs_pos_eq; try lra.
rewrite -[X in _ <= X]Rmult_1_r.
apply: Rmult_le_compat_l; try lra.
rewrite -pT_Cheby // /Cheby.
have := COS_bound (INR n * acos x).
by split_Rabs; lra.
Qed.

End ChebyBound.

Section ScaleBound.

Variable a b : R.
Hypothesis aLb : a < b.

Definition scheby_nodes (n : nat) :=
  [seq ((b - a) * i + a + b) / 2 | i <- cheby_nodes n].

Lemma size_scheby_nodes n : size (scheby_nodes n) = n.
Proof. by rewrite size_map size_cheby_nodes. Qed.

Lemma scheby_nodes_bound n x :
  x \in scheby_nodes n -> a < x < b.
Proof.
move=> /mapP[i /cheby_nodes_bound] [H1 H2] ->.
nra.
Qed.

Lemma scheby_nodes_boundW n x :
  x \in scheby_nodes n -> a <= x <= b.
Proof. move/scheby_nodes_bound; lra. Qed.

Lemma root_scheby_nodes n : all (root ('T^(a,b)_n)) (scheby_nodes n).
Proof.
apply/allP => /= x /mapP[y /(allP (root_cheby_nodes n))] H ->.
rewrite root_comp !hornerE /=.
have D :  b + - a != 0 by apply/eqP; lra.
toR; rewrite /Rinvx D; set z := (_ + _).
rewrite (_ : z = y) // /z.
by field; apply/eqP.
Qed.

Lemma uniq_scheby_nodes n : uniq (scheby_nodes n).
Proof.
rewrite map_inj_uniq; first by exact: uniq_cheby_nodes.
move=> i j; nra.
Qed.

Lemma scheby_prodl n : 
   'T^(a,b)_n = ((expn 2 (n.*2.-1))%:R / (b - a)^+n) *:  
                \prod_(z <- scheby_nodes n) ('X - z%:P).
Proof.
set p := 'T^(a,b)_n.
have D :  b + - a != 0 by apply/eqP; lra.
have E : GRing.lreg ((1 + 1) / (b - a)).
  move=> /= x y; toR; rewrite /Rinvx D => H.
  have H1 :  / (b + - a) * x = / (b + - a) * y by lra.
  rewrite (_ : x = (b + - a) * / (b + - a) * x); last first.
    by field; apply/eqP.
  by rewrite Rmult_assoc H1; field; apply/eqP.
have F1 : size p = n.+1.
  rewrite size_comp_poly2 ?size_pT //. 
    by move=> /= x /= y; rewrite -[2%:R]/2; toR; lra.
  rewrite /Tab size_addl lreg_size ?size_polyX //.
  by rewrite size_polyC; case: (_ == _).
rewrite -coef_pTab; last first.
  apply/eqP; rewrite -[_%:R]/2; toR; lra.
rewrite {2}[n]pred_Sn -F1.
apply: all_roots_prod_XsubC.
- by rewrite F1 size_scheby_nodes.
- by apply: root_scheby_nodes.
rewrite uniq_rootsE.
apply: uniq_scheby_nodes.
Qed.

End ScaleBound.

Section SChebyBound.

Variable a b : R.
Hypothesis aLb : a < b.
Variable c1 c2 : R.
Hypothesis c1La : c1 < a.
Hypothesis bLc2 : b < c2.
Variable f : R -> R.
Variable n : nat.
Hypothesis deriv_f : 
  forall x k, c1 < x < c2 -> (k <= n)%nat -> ex_derive_n f k x.

Hypothesis cont_f :
 forall x k, (k <= n)%nat -> a <= x <= b -> continuous (Derive_n f k) x.

Lemma Tab_bound x : a <= x <= b -> -1 <= (Tab a b).[x] <= 1.
Proof.
move=> [H1 H2].
have D' :  b != a by apply/eqP; lra.
have D :  b + -a != 0 by apply/eqP; lra.
have ->: -1 = (-1)%RR by toR.
have ->: 1 = 1%RR by toR.
rewrite -(@Taba _ a b) // -(@Tabb _ a b) //.
have F : 0 <= ((1 + 1) / (b - a))%R.
  by apply: Rdiv_le_0_compat; lra.
rewrite /Tab !hornerE; split; apply: Rplus_le_compat_r.
- by apply: Rmult_le_compat_l; toR; rewrite /Rinvx D.
- by apply: Rmult_le_compat_l; toR; rewrite /Rinvx D.
Qed.

Lemma ierror_scheby x z :
  a <= x <= b ->
  (forall y,   a <= y <= b -> Rabs (Derive_n f n y) <= z) ->
  Rabs (ierror f (scheby_nodes a b n) x) <= 
  ((b - a)^+n / ((expn 2 n.*2.-1 * n `!) %:R)) * z.
Proof.
move=> Hx Hy.
have Hz : 0 <= z.
  suff: Rabs (Derive_n f n a) <= z by split_Rabs; lra.
  by apply: Hy; lra.
have F1 : 0 < n`!%:R.
  rewrite natr_INR.
  by apply/lt_0_INR/ltP/fact_gt0.
have F2 : 0 < (expn 2 n.*2.-1)%:R.
  rewrite natr_INR.
  by apply/lt_0_INR/ltP/expn_gt0.
have F3 : 0 < / (expn 2 n.*2.-1)%:R.
  by apply: Rinv_0_lt_compat; lra.
have F4 : 0 < / n`!%:R.
  by apply: Rinv_0_lt_compat; lra.
have F5 : 0 < (b - a) ^+ n.
  elim: n => [|n1 IH].
    by rewrite expr0; toR; lra.
  rewrite exprS; apply: Rmult_lt_0_compat => //.
  by toR; lra.
have [/eqP-> | Hc] := boolP (ierror f (scheby_nodes a b n) x == 0).
  rewrite Rabs_R0.
  apply: Rmult_le_pos => //.
  apply: Stdlib.Rdiv_pos_compat; try lra.
  rewrite natr_INR.
  apply/lt_0_INR/leP/neq0_lt0n/eqP/eqP.
  by rewrite muln_eq0 negb_or -!lt0n expn_gt0 fact_gt0.
have [z1 [H1z1 ->]] := ierror_val (sym_equal (size_scheby_nodes a b n))
    (@uniq_scheby_nodes a b aLb n) c1La bLc2 (@scheby_nodes_boundW a b aLb n)
    deriv_f cont_f Hx Hc.
rewrite !Rabs_mult Rabs_R1 Rabs_inv; try lra.
rewrite Rabs_pos_eq; try lra.
rewrite natrM.
rewrite Rmult_comm/Rdiv Rinv_mult; try lra.
rewrite -!Rmult_assoc.
apply: Rmult_le_compat; last by apply: Hy; lra.
- apply: Stdlib.Rmult_le_pos_pos => //.
    rewrite Rmult_1_r.
    by apply: Rabs_pos.
  by lra.
- by apply: Rabs_pos.
apply: Rmult_le_compat_r; try lra.
rewrite Rmult_1_r.
have F : (b - a) ^+ n != 0.
  elim: n => [|n1 IH1].
    by rewrite expr0; apply/eqP; toR; lra.
  rewrite exprS mulf_eq0 negb_or IH1 andbT.
  by apply/eqP; toR; lra.
have -> : (prodl (scheby_nodes a b n)).[x] = 
           (b - a)^+n / (expn 2 n.*2.-1)%:R * ((pTab a b n).[x]).
  rewrite scheby_prodl // /prodl undup_id ?uniq_scheby_nodes //.
  rewrite hornerE.
  set xx : R := _.[x]; set yy : R :=  _%:R.
  toR; rewrite /Rinvx F; field; split.
    by apply/eqP.
  by rewrite /yy; lra.
rewrite Rabs_mult Rabs_pos_eq; try lra.
  rewrite -[X in _ <= X]Rmult_1_r.
  apply: Rmult_le_compat_l; try lra.
    by apply: Rmult_le_pos; apply: Rlt_le.
  rewrite /pTab horner_comp -pT_Cheby.
    rewrite /Cheby.
    have := COS_bound (INR n * acos (Tab a b).[x]).
    set xx := cos _.
    split_Rabs; lra.
  by have := Tab_bound Hx; split_Rabs.
by apply: Rmult_le_pos; apply: Rlt_le.
Qed.

End SChebyBound.

Section ChebyCoef.

Definition sum_cheby n x : R :=
   \sum_(i < n.+1) cos (INR (i.*2.+1) * x / 2).

Lemma sum_cheby_0r n : sum_cheby n 0 = INR n.+1.
Proof.
rewrite [LHS](eq_bigr (fun i : 'I_n.+1 => 1)) => [|i _]; last first.
  by rewrite -cos_0; congr cos; toR; lra.
rewrite big_const cardT size_enum_ord.
elim: n.+1 => //= k ->; case: k => [|k]; first by rewrite /=; toR; lra.
by toR; lra.
Qed.

Lemma sum_cheby_2PIr n : sum_cheby n (2 * PI) = - INR n.+1.
Proof.
rewrite [LHS](eq_bigr (fun i : 'I_n.+1 => -1)) => [|i _]; last first.
  rewrite (_ : _ /2 =  PI + 2 * INR i * PI).
    by rewrite cos_period cos_PI.
  by rewrite S_INR -addnn plus_INR; toR; lra.
rewrite big_const cardT size_enum_ord.
elim: n.+1 => [|k /= ->]; first by rewrite /=; toR; lra.
case: k => [|k]; first by rewrite /=; toR; lra.
by toR; lra.
Qed.

Lemma close_sum_cheby n x :
  sin (x / 2) != 0 -> 
  sum_cheby n x = sin (INR (n.*2.+1) * x / 2 + x / 2) / (2 * sin (x /2)).
Proof.
move=> sinNz.
pose u := x / 2.
pose v i := INR i.*2.+1 * x / 2.
suff <-: 2 * sin u * sum_cheby n x = sin (v n  + u).
  by rewrite /u; field; apply/eqP.
rewrite Rmult_assoc [sin _ * _](@mulr_sumr [ringType of R]).
rewrite [_ * _](@mulr_sumr [ringType of R]).
pose f (i : 'I_n.+1) := sin (v i + u) - sin (v i - u).
rewrite (eq_bigr f)=> [|i _]; last first.
  by rewrite /f -[_/2]/(v i) sin_minus sin_plus; toR; ring.
rewrite sumrB big_ord_recr /=.
set s1 := \sum_(_ < _) _.
rewrite big_ord_recl /=.
set s2 := \sum_(_ < _) _.
rewrite (_ : s1 = s2); last first.
  apply: eq_bigr => i _; congr sin.
  rewrite /bump /= /v /u -!addnn !S_INR !plus_INR.
  by toR; lra.
rewrite (_ : _ - u = 0); last first.
  by rewrite /v /u /=; toR; lra.
rewrite sin_0; toR; lra.
Qed.

Lemma sum_cheby_Pin n r :
  (0 < r < n.+1.*2)%nat -> sum_cheby n (INR r * PI / INR (n.+1)) = 0.
Proof.
move=> /andP[rP rL].
have F : INR (n.+1) * 2 = INR (n.+1.*2) :> R.
  by rewrite -addnn plus_INR; lra.
have F1 (k : R) : k / INR (n.+1) / 2 = k / INR (n.+1.*2).
  by rewrite /Rdiv Rmult_assoc -Rinv_mult ?F.
have F2 : 0 < INR (n.+1).*2 by apply: (lt_INR 0) => //; apply/leP.
have F3 : 0 < PI by have := PI2_3_2; lra.
have F4 : sin (INR r * PI / INR (n.+1) / 2) != 0.
  rewrite F1.
  apply/eqP.
  suff : 0 < sin (INR r * PI / INR (n.+1).*2) by lra.
  apply: sin_gt_0.
    suff H : 0 < INR r.
      repeat apply: Rmult_lt_0_compat => //.
      by apply: Rinv_0_lt_compat.
    by apply: (lt_INR 0) => //; apply/leP.
  apply/Rlt_div_l; try lra.
  rewrite Rmult_comm.
  apply: Rmult_lt_compat_l => //.
  by apply/lt_INR/leP.
rewrite close_sum_cheby //.
rewrite [_ / 2]Rmult_assoc.
rewrite F1 [_ * / 2]F1 -{2}[_ / INR _]Rmult_1_l.
rewrite -Rmult_plus_distr_r -S_INR.
rewrite -[_.+2]/(n.+1).*2.
have -> : INR n.+1.*2 * (INR r * PI / INR (n.+1).*2) =
          INR r * PI.
  by field; lra.
suff ->: sin (INR r * PI) = 0 by lra.
elim: (r) => [|k HK].
  by rewrite Rmult_0_l sin_0.
rewrite S_INR Rmult_plus_distr_r Rmult_1_l neg_sin.
by lra.
Qed.

Definition dsprod_cheby n (f g : {poly R}) : R := 
   \sum_(i <- cheby_nodes n) f.[i] * g.[i].

Notation "'<< f , g >>_ n" := (dsprod_cheby n f g) 
  (at level 10, format "''<<' f ,   g >>_ n").

Lemma dsprod_chebyC n f g : '<<f, g>>_n = '<<g, f >>_n.
Proof. by apply: eq_bigr => i _; rewrite mulrC. Qed.

Lemma dsprod_chebyZ n k f g : '<<k *: f, g>>_n = k * '<<f, g>>_ n.
Proof.
rewrite [_ * _](@mulr_sumr [ringType of R]).
by apply: eq_bigr => i _; rewrite hornerE mulrA.
Qed.

Lemma dsprod_cheby0 n g : '<<0, g>>_n = 0.
Proof.
rewrite -(@scale0r _ [lmodType R of {poly R}] 0) dsprod_chebyZ.
by rewrite [0 * _](@mul0r [ringType of R]).
Qed.

Lemma dsprod_chebyN n f g : '<<-f, g>>_n = - '<<f, g >>_ n.
Proof.
rewrite -scaleN1r dsprod_chebyZ /=; exact: mulN1r.
Qed.

Lemma dsprod_chebyD n f1 f2 g : 
  '<<f1 + f2, g>>_n = '<<f1, g>>_n + '<<f2, g>>_n.
Proof.
rewrite -[_ + _](@big_split [ringType of R]) /=.
by apply: eq_bigr => i _; rewrite !hornerE mulrDl.
Qed.

Lemma dsprod_chebyB n f1 f2 g : 
  '<<f1 - f2, g>>_n = '<<f1, g>>_n - '<<f2, g>>_n.
Proof. by rewrite dsprod_chebyD dsprod_chebyN. Qed.

Lemma dsprod_cheby_sum n I r P (F : I -> _) g :
  '<<(\sum_(i <- r | P i) F i), g>>_n = 
   \sum_(i <- r | P i) '<<F i, g>>_n.
Proof.
elim: r => /= [|a r IH]; first by rewrite !big_nil dsprod_cheby0.
rewrite !big_cons; case: (P a) => //.
by rewrite dsprod_chebyD IH.
Qed.

Lemma dsprod_sum_cheby n i j :
   (j <= i <= n)%nat ->
  '<<'T_i, 'T_j>>_n.+1 = /2 * (sum_cheby n (INR (i + j) * PI / INR n.+1) +
                               sum_cheby n (INR (i - j) * PI / INR n.+1)).
Proof.
move=> /andP[jLi iLn].
have F : INR (n.+1) * 2 = INR (n.+1.*2) :> R.
  by rewrite -addnn plus_INR; lra.
have F1 (k : R) : k / INR (n.+1) / 2 = k / INR (n.+1.*2).
  by rewrite /Rdiv Rmult_assoc -Rinv_mult ?F.
have PIpos : 0 < PI by have := PI2_3_2; lra.
rewrite /dsprod_cheby big_map.
pose g i1 := (i1.*2.+1%:R * PI / n.+1.*2%:R).
rewrite -val_enum_ord big_map [LHS]/=.
rewrite (eq_bigr (fun k : 'I_n.+1 => cos (INR i * g k) * cos (INR j * g k)))
    => [|k _]; last first.
  rewrite -!pT_Cheby; try by apply: COS_bound.
  rewrite /Cheby acos_cos //.
  have F2 : 0 < n.+1.*2%:R.
   rewrite natr_INR; apply/(lt_INR 0)/leP.
   apply: leq_ltn_trans (_ : i.*2 < _)%nat => //.
   by rewrite ltn_double.
  split.
    apply: Rmult_le_pos; last first.
      by apply/Rlt_le/Rinv_0_lt_compat.
    apply: Rmult_le_pos; last by lra.
    by rewrite natr_INR; apply/(le_INR 0)/leP.
  apply/Rle_div_l; try lra.
  rewrite Rmult_comm.
  apply: Rmult_le_compat_l; try lra.
  rewrite !natr_INR; apply/le_INR/leP.
  by rewrite ltn_double.
rewrite (eq_bigr (fun k : 'I_n.+1 => 
   / 2 * (cos (INR (i + j) * g k) + cos (INR (i - j) * g k))))
    => [|k _]; last first.
  rewrite /g plus_INR minus_INR; try by apply/leP.
  rewrite Rmult_minus_distr_r Rmult_plus_distr_r.
  set x := INR _ * _; set y := INR _ * _.
  by rewrite cos_minus cos_plus; lra.
rewrite -mulr_sumr /sum_cheby.
have <- : index_enum (ordinal_finType n.+1) = enum 'I_n.+1.
  by apply/sym_equal/all_filterP/allP.
by rewrite big_split; congr (_ * (_ + _)); 
   apply: eq_bigr => k _; congr cos;
   rewrite /g !natr_INR -!Rmult_assoc F1; lra.
Qed.

Lemma dsprod_cheby_ortho n i j :
   (j <= n)%nat -> (i <= n)%nat ->
  '<<'T_i, 'T_j>>_n.+1 = if i == j then
                           if i == 0%nat then INR n.+1 
                           else (INR n.+1)/2
                         else 0.
Proof.
wlog : i j / (j <= i)%nat => [H|jLi jLn iLn].
  case: (leqP j i) => [] H1 H2 H3; first by apply: H.
  rewrite dsprod_chebyC H //; last by apply: ltnW.
  by rewrite eq_sym; case: eqP => // ->.
rewrite dsprod_sum_cheby ?jLi //.
case: eqP => [<-|/eqP iDj].
  case: eqP => [->|/eqP iNZ].
  rewrite Rmult_0_l [_ / _]Rmult_0_l sum_cheby_0r; lra.
  rewrite subnn Rmult_0_l [0 / _]Rmult_0_l sum_cheby_0r.
  rewrite sum_cheby_Pin; try lra.
  by rewrite addn_gt0 lt0n iNZ /= addnn ltn_double ltnS.
rewrite !sum_cheby_Pin; try lra.
- rewrite subn_gt0 ltn_neqAle eq_sym iDj jLi /=.
  apply: leq_ltn_trans (leq_subr _ _) _.
  apply: leq_trans (_ : n.+1 <= _)%nat; first by rewrite ltnS.
  by rewrite -addnn leq_addr.
apply/andP; split; first by  case: (i) iDj => //; case: (j).
rewrite -addnn -addSn leq_add ?ltnS //.
apply: leq_trans jLi _.
by apply: leq_trans iLn _.
Qed.

Definition dsprod_coef p n i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
  '<<p, 'T_i>>_n.+1.

Lemma dsprod_coefD p q n i :
  dsprod_coef p n i + dsprod_coef q n i = dsprod_coef (p + q) n i.
Proof.
by rewrite /dsprod_coef -Rmult_plus_distr_l dsprod_chebyD.
Qed.

Lemma dsprod_cheby_eq n (p : {poly R}) :
   (size p <= n.+1)%nat ->
   p = \sum_(i < n.+1) (dsprod_coef p n i) *: 'T_i.
Proof.
have [k pLs] := ubnPleq (size p).
elim: k p pLs  => [p|k IH p pLk kLn].
  rewrite size_poly_leq0 => /eqP-> _.
  apply: sym_equal; apply: big1 => i _.
  by rewrite /dsprod_coef dsprod_cheby0 Rmult_0_r scale0r.
pose p1 := (GRing.add p (-((p`_k / lead_coef 'T_k) *: 'T_k))).
have Hreg : GRing.lreg (2%:R : R).
  by apply /GRing.lregP/eqP; rewrite natr_INR /=; toR; lra.
have p1Lk : (size p1 <= k)%nat.
  apply/leq_sizeP => j.
  rewrite leq_eqVlt => /orP[/eqP<-|H].
    rewrite coefB coefZ /lead_coef size_pT //.
    rewrite divfK ?subrr //=.
    rewrite {2}[k]pred_Sn -[k.+1](@size_pT [unitRingType of R]) //.
    by rewrite lead_coef_eq0 pT_neq0.
  rewrite coefB coefZ.
  have /leq_sizeP->// := pLk.
  have  /(leq_trans)/(_ H)/leq_sizeP-> // := size_pT_leq [ringType of R] k.
  by rewrite !rm0.
rewrite -{1}[p](subrK ((p`_k / lead_coef 'T_k) *: 'T_k)).
rewrite -/p1 (IH _ p1Lk); last by apply: leq_trans kLn.
set u := _ *: _.
suff -> : u = \sum_(i < n.+1) (dsprod_coef u n i) *: 'T_i.
  rewrite -big_split /=.
  apply: eq_bigr => i _.
  by rewrite -scalerDl [(GRing.add _ _)%R]dsprod_coefD subrK.
have kLn1 : (k < n.+1)%nat by apply: leq_trans kLn.
rewrite (bigD1 (Ordinal kLn1)) // big1 /= => [|i /eqP/val_eqP/= Hi]; last first.
  rewrite /u /dsprod_coef dsprod_chebyZ.
  rewrite dsprod_cheby_ortho //.
    by rewrite [k == _]eq_sym (negPf Hi) !Rmult_0_r rm0.
  by rewrite -ltnS.
rewrite addr0 /u /dsprod_coef dsprod_chebyZ dsprod_cheby_ortho //.
congr (_ *: _).
set x : R := (GRing.mul _ _); set y : R := INR _.
rewrite eqxx.
by case: eqP => _ /=; field; apply: (not_INR _ 0).
Qed.

Lemma dsprod_coef_interpolation f n i :
  dsprod_coef (interpolation f (cheby_nodes n.+1)) n i 
  =
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j <- cheby_nodes n.+1) f j * ('T_i).[j].
Proof.
congr (_ * _).
rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr => k /andP[Hk _].
by rewrite horner_interpolation.
Qed.

Definition sdsprod_cheby a b n (f g : {poly R}) : R := 
   \sum_(i <- scheby_nodes a b n) f.[i] * g.[i].

Notation "'<< f , g >>[ a , b ]_ n" := (sdsprod_cheby a b n f g) 
  (at level 10, format "''<<' f ,   g >>[ a ,  b ]_ n").

Lemma sdsprod_chebyC a b n f g : '<<f, g>>[a, b]_n = '<<g, f >>[a, b]_n.
Proof. by apply: eq_bigr => i _; rewrite mulrC. Qed.

Lemma sdsprod_chebyZ a b n k f g : 
  '<<k *: f, g>>[a, b]_n = k * '<<f, g>>[a, b]_ n.
Proof.
rewrite [_ * _](@mulr_sumr [ringType of R]).
by apply: eq_bigr => i _; rewrite hornerE mulrA.
Qed.

Lemma sdsprod_cheby0 a b n g : '<<0, g>>[a, b]_n = 0.
Proof.
rewrite -(@scale0r _ [lmodType R of {poly R}] 0) sdsprod_chebyZ.
by rewrite [0 * _](@mul0r [ringType of R]).
Qed.

Lemma sdsprod_chebyN a b n f g : '<<-f, g>>[a, b]_n = - '<<f, g >>[a, b]_ n.
Proof. by rewrite -scaleN1r sdsprod_chebyZ /=; exact: mulN1r. Qed.

Lemma sdsprod_chebyD a b n f1 f2 g : 
  '<<f1 + f2, g>>[a, b]_n = '<<f1, g>>[a, b]_n + '<<f2, g>>[a, b]_n.
Proof.
rewrite -[_ + _](@big_split [ringType of R]) /=.
by apply: eq_bigr => i _; rewrite !hornerE mulrDl.
Qed.

Lemma sdsprod_chebyB a b n f1 f2 g : 
  '<<f1 - f2, g>>[a, b]_n = '<<f1, g>>[a, b]_n - '<<f2, g>>[a, b]_n.
Proof. by rewrite sdsprod_chebyD sdsprod_chebyN. Qed.

Lemma sdsprod_cheby_sum a b n I r P (F : I -> _) g :
  '<<(\sum_(i <- r | P i) F i), g>>[a, b]_n = 
   \sum_(i <- r | P i) '<<F i, g>>[a, b]_n.
Proof.
elim: r => /= [|c r IH]; first by rewrite !big_nil sdsprod_cheby0.
rewrite !big_cons; case: (P c) => //.
by rewrite sdsprod_chebyD IH.
Qed.

Lemma sdsprod_cheby_ortho a b n i j :
  a != b -> (j <= n)%nat -> (i <= n)%nat ->
  '<< 'T^(a, b)_i, 'T^(a, b)_j>>[a, b]_n.+1 = 
                         if i == j then
                           if i == 0%nat then INR n.+1 
                           else (INR n.+1)/2
                         else 0.
Proof.
move=> aDb jLn iLn.
have F : b + - a != 0  by apply/eqP; move/eqP: aDb;lra.
rewrite [LHS]big_map -dsprod_cheby_ortho //.
apply: eq_bigr => k _.
rewrite !horner_comp !hornerE /=.
by congr (_.[_] * _.[_]); toR; rewrite /Rinvx F; field; apply/eqP.
Qed.

Definition sdsprod_coef a b p n i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
  '<<p, 'T^(a, b)_i>>[a, b]_n.+1.

Lemma sdsprod_coefD a b p q n i :
  sdsprod_coef a b p n i + sdsprod_coef a b q n i = 
  sdsprod_coef a b (p + q) n i.
Proof.
by rewrite /sdsprod_coef -Rmult_plus_distr_l sdsprod_chebyD.
Qed.

Lemma sdsprod_cheby_eq a b n (p : {poly R}) :
   a != b -> (size p <= n.+1)%nat ->
   p = \sum_(i < n.+1) (sdsprod_coef a b p n i) *: 'T^(a, b)_i.
Proof.
move=> aDb.
have [k pLs] := ubnPleq (size p).
elim: k p pLs  => [p|k IH p pLk kLn].
  rewrite size_poly_leq0 => /eqP-> _.
  apply: sym_equal; apply: big1 => i _.
  by rewrite /sdsprod_coef sdsprod_cheby0 Rmult_0_r scale0r.
pose p1 := (GRing.add p (-((p`_k / lead_coef 'T^(a, b)_k) *: 'T^(a, b)_k))).
have t2Z : 2%:R != 0 :> R.
  by apply /eqP; rewrite natr_INR /=; toR; lra.
have Hreg : GRing.lreg (2%:R : R) by apply /GRing.lregP.
have p1Lk : (size p1 <= k)%nat.
  apply/leq_sizeP => j.
  rewrite leq_eqVlt => /orP[/eqP<-|H].
    rewrite coefB coefZ /lead_coef size_pTab //.
    rewrite divfK ?subrr //=.
    rewrite {2}[k]pred_Sn -[k.+1](size_pTab _ t2Z aDb).
    by rewrite lead_coef_eq0 -size_poly_eq0 size_pTab.
  rewrite coefB coefZ.
  have /leq_sizeP->// := pLk.
  have /leq_sizeP-> // : (size ('T^(a,b)_k) <= j)%nat by rewrite size_pTab.
  by rewrite !rm0.
rewrite -{1}[p](subrK ((p`_k / lead_coef 'T^(a, b)_k) *: 'T^(a, b)_k)).
rewrite -/p1 (IH _ p1Lk); last by apply: leq_trans kLn.
set u := _ *: _.
suff -> : u = \sum_(i < n.+1) (sdsprod_coef a b u n i) *: 'T^(a, b)_i.
  rewrite -big_split /=.
  apply: eq_bigr => i _.
  by rewrite -scalerDl [(GRing.add _ _)%R]sdsprod_coefD subrK.
have kLn1 : (k < n.+1)%nat by apply: leq_trans kLn.
rewrite (bigD1 (Ordinal kLn1)) // big1 /= => [|i /eqP/val_eqP/= Hi]; last first.
  rewrite /u /sdsprod_coef sdsprod_chebyZ.
  rewrite sdsprod_cheby_ortho //.
    by rewrite [k == _]eq_sym (negPf Hi) !Rmult_0_r rm0.
  by rewrite -ltnS.
rewrite addr0 /u /sdsprod_coef sdsprod_chebyZ sdsprod_cheby_ortho //.
congr (_ *: _).
set x : R := (GRing.mul _ _); set y : R := INR _.
rewrite eqxx.
by case: eqP => _ /=; field; apply: (not_INR _ 0).
Qed.

Lemma sdsprod_coef_interpolation f a b n i :
  sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n i 
  =
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j <- scheby_nodes a b n.+1) f j * ('T^(a, b)_i).[j].
Proof.
congr (_ * _).
rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
apply: eq_bigr => k /andP[Hk _].
by rewrite horner_interpolation.
Qed.

Lemma sdsprod_coef_interpolation_pT f a b n i 
      (cn := cheby_nodes n.+1) :
  a != b ->
  sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n i 
  =
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) f (((b - a) * (cn`_j) + a + b) / 2)%R * ('T_i).[cn`_j].
Proof.
move=> aDb.
have aDb1 : b + - a != 0.
  by apply: contra aDb => /eqP H; apply/eqP; lra.
rewrite sdsprod_coef_interpolation. 
congr (_ * _).
rewrite -[in RHS](size_scheby_nodes a b n.+1) big_tnth.
apply: eq_bigr => k _; rewrite (tnth_nth 0) /= !(nth_map 0); last first.
  by rewrite size_cheby_nodes -{2}(size_scheby_nodes a b n.+1).
congr (_ * _).
rewrite horner_comp !hornerE /=.
congr (_.[_]); set x := _ `_ _.
by toR; rewrite /Rinvx aDb1; field; apply/eqP.
Qed.

End ChebyCoef.

Section Newton.

Variable R : fieldType.

Variable f : R -> R.

Definition ddiff (l : seq R) := 
  \sum_(i <- l) (f i / (\prod_(j <- l | j != i) (i - j))).

Lemma ddiffE a b l : 
  uniq [::a, b  & l] ->
  ddiff (a :: l) = (ddiff (b :: l) + (a - b) * ddiff [::a, b & l])%RR.
Proof.
rewrite /= inE negb_or => /and3P[/andP[aDb aNIl] bNIl Ul].
rewrite /ddiff !big_cons !eqxx [b == _]eq_sym (negPf aDb) /=.
have F x : x \notin l -> \prod_(j <- l | j != x) (x - j) = 
                         \prod_(j <- l) (x - j).
  move=> xNIl.
  rewrite big_seq_cond [RHS]big_seq_cond.
  apply: eq_bigl => i.
  by case: eqP => // ->; rewrite (negPf xNIl).
rewrite !F //.
set Pa := \prod_(_ <- _ | _) _.
set Pb := \prod_(_ <- _ | _) _.
set Sa := \sum_(j <- l) _.
set Sb := \sum_(j <- l) _.
set Sab := \sum_(j <- l) _.
rewrite !mulrDr mulrCA invfM.
rewrite [((a - b) * (_ / _))%RR]mulrA divff ?div1r; last first.
  by rewrite GRing.subr_eq0.
rewrite mulrCA invfM -opprB mulNr.
rewrite [((b - a) * (_ / _))%RR]mulrA divff ?div1r; last first.
  by rewrite GRing.subr_eq0 eq_sym.
rewrite mulrN [RHS]addrCA -!addrA; congr (_ + _)%RR.
rewrite !addrA [(_ + Sb)%RR]addrC addrK opprB.
rewrite mulr_sumr -big_split /=.
rewrite [LHS]big_seq_cond [RHS]big_seq_cond; apply: eq_big=> i //.
rewrite andbT => iIl.
rewrite !big_cons (_ : a != i) 1?(_ : b != i) /=; last 2 first.
- by apply: contra bNIl => /eqP->.
- by apply: contra aNIl => /eqP->.
set P := \prod_(_ <- _ | _) _.
rewrite (_ : a - b = (i - b) - (i - a))%RR; last first.
  by rewrite opprB [in RHS]addrC addrA subrK.
rewrite [(((i - b) - _)* _)%RR]mulrBl.
set x := (_ / _)%RR.
set y := (_ / _)%RR.
rewrite {1}[(_ * P)%RR]mulrC [(_ * (P * _))%RR]mulrA.
rewrite invfM [(f i * _)%RR]mulrA [((i - b) * _)%RR]mulrC -/x divfK; last first.
  by rewrite subr_eq0; apply: contra bNIl => /eqP<-.
rewrite [((i - a) * (_ * P))%RR]mulrC invfM  [(f i * _)%RR]mulrA -/y.
rewrite mulrC divfK; last first.
  by rewrite subr_eq0; apply: contra aNIl => /eqP<-.
by rewrite addrC subrK.
Qed.

Lemma ddiff_nil : ddiff [::] = 0%RR.
Proof. by rewrite [LHS]big_nil. Qed.

Lemma ddiff_singleton a : ddiff [:: a] = f a.
Proof. 
 rewrite [LHS]big_cons big_cons !big_nil eqxx /=.
by rewrite addr0 divr1.
Qed.

Lemma ddiff_perm_eq l1 l2 :  perm_eq l1 l2 -> ddiff l1 = ddiff l2.
Proof.
move=> H.
rewrite /ddiff.
apply: etrans (_ : \sum_(i <- l1)
   f i / (\prod_(j <- l2 | j != i) (i - j))= _).
  apply:eq_bigr => i _.
  congr (_ / _)%RR.
  by apply: perm_big.
by apply: perm_big.
Qed.

Definition lagrange (l : seq R) i := 
      ((\prod_(j <- l | j != i) (i - j)) ^-1)
         *:  \prod_(j <- l | j != i) ('X - j %:P).

Lemma horner_lagrange l i j :
  j \in i :: l -> (lagrange l i).[j] = (i == j)%:R.
Proof.
move=> H.
rewrite /lagrange !hornerE horner_prod.
rewrite [X in (_ * X = _)%RR](eq_bigr (fun x : R => (j - x)%RR)) => [|k]; 
     last by rewrite !hornerE.
rewrite mulrC.
have H1 : (\prod_(j0 <- l | j0 != i) (i - j0)) != 0%RR.
  rewrite prodf_seq_eq0.
  by apply/hasPn=> x; rewrite subr_eq0 eq_sym; case: eqP.
case: (i =P j)=> [<-|/eqP iDj].
  by rewrite divff.
suff->: \prod_(i0 <- l | i0 != i) (j - i0) = 0%RR.
  by rewrite mul0r.
move: H; rewrite inE eq_sym (negPf iDj) /=.
elim: {H1}l => //= a l IH.
  rewrite !big_cons !inE.
case: (a =P i) => /= [->|/eqP jDa].
  by rewrite eq_sym (negPf iDj).
case: (j =P a) => [->|_ /IH ->].
  by rewrite subrr mul0r.
by rewrite mulr0.
Qed.

Lemma size_lagrange l i :
  i \in l -> (size (lagrange l i) <= size l)%nat.
Proof.
move=> iIl.
rewrite size_scale; last first.
  rewrite invr_eq0.
  rewrite prodf_seq_eq0.
  by apply/hasPn=> x; rewrite subr_eq0 eq_sym; case: eqP.
rewrite (big_nth 0%RR) big_mkord size_prod; last first.
  by move=> k _; apply/monic_neq0/monicXsubC.
rewrite (eq_bigr (fun i => 2%nat)); last first.
  by move=> j; rewrite size_XsubC.
rewrite sum_nat_const muln2 -addnn -addSn addnK.
have I : (index i l < size l)%nat by rewrite index_mem.
pose o := Ordinal I.
rewrite -[X in (_ < X)%nat]card_ord [X in (_ < X)%nat](cardD1 o) inE /= ltnS.
apply/subset_leq_card/subsetP => k; rewrite !inE unfold_in andbT.
apply: contra => /eqP->.
by rewrite nth_index.
Qed.

Lemma interpolationE l :
  uniq l -> interpolation f l = \sum_(i <- l) f i *: lagrange l i.
Proof.
move=> Hs.
apply/eqP; rewrite -subr_eq0.
set p := (_ - _)%RR.
case: eqP => // /eqP pNZ.
have: (size p <= size l)%nat.
  apply: leq_trans (size_add _ _) _.
  rewrite size_opp geq_max interpolation_size //.
  apply: leq_trans (size_sum _ _ _) _.
  rewrite (big_nth 0%RR) big_mkord.
  apply/bigmax_leqP=> i _.
  apply: leq_trans (size_scale_leq _ _) _.
  apply:  size_lagrange.
  by rewrite mem_nth.
rewrite leqNgt; case/negP.
apply: max_poly_roots => //.
apply/allP => x xIl.
apply/rootP; rewrite !hornerE horner_interpolation //.
have I : (index x l < size l)%nat by rewrite index_mem.
pose o := Ordinal I.
rewrite (big_nth 0%RR) big_mkord (bigD1 o) //=.
rewrite nth_index // !(horner_lagrange, hornerE, inE, eqxx) //.
rewrite horner_sum big1 ?hornerE ?addn0 ?subrr //.
move=> k.
rewrite !(horner_lagrange, hornerE, inE, eqxx) //; last first.
  by rewrite xIl orbT.
case: (_ =P x) => /= [H /eqP[]|_]; last by rewrite mulr0.
apply/val_eqP.
by rewrite /= -(nth_uniq 0%RR (ltn_ord _)) // H nth_index.
Qed.

Lemma interpolation_ddiff l :
  uniq l -> (interpolation f l)`_(size l).-1 = ddiff l.
Proof.
move=> Ul; rewrite interpolationE // coef_sum.
rewrite [LHS]big_seq_cond [RHS]big_seq_cond; apply: eq_bigr => i.
rewrite andbT => iIl.
rewrite coefZ /lagrange coefZ (_ : _ `_ _ = 1%RR) ?mulr1 //.
rewrite (_ : _.-1 = (size l - (i \in l)).+1.-1); last by rewrite iIl subn1.
rewrite -size_prodl_diff //.
by apply/eqP/monic_prodl_diff.
Qed.

Lemma error_ddiff l a :
  uniq (a :: l) -> (f a - (interpolation f l).[a] = ddiff (a :: l) * (prodl l).[a])%RR.
Proof.
move=> /= /andP[aNIl Ul].
rewrite -interpolation_ddiff /= ?aNIl ?(negPf aNIl) //.
rewrite coefD coefZ nth_default ?interpolation_size ?add0r //.
rewrite [size _]pred_Sn -size_prodl_uniq // -lead_coefE (eqP (monic_prodl _)) mulr1.
rewrite divfK //.
have := root_prodl l a.
by rewrite (negPf aNIl)=> /eqP/eqP.
Qed.

End Newton.

Lemma ddiffN (R: fieldType) (f : R -> R) (l : seq R) :
   (ddiff (fun z => - (f z)) l = - (ddiff f l))%RR.
Proof.
rewrite /ddiff -sumrN.
by apply: eq_bigr => i _; rewrite -mulNr.
Qed.

Section DiffMore.

Variable RR : fieldType.

Lemma ddiff1 (l : seq RR) n :
  (1 < size l <= n)%nat -> uniq l -> ddiff (fun _ => 1)%RR l = 0%RR.
Proof.
elim: n l => [l|n IH [|a [|b [|c l]]] // /andP[_ H] Ul].
- by case: size => // n; rewrite andbF.
- have := ddiffE (fun _ => 1%RR) Ul.
  rewrite !ddiff_singleton.
  rewrite -{1}[1%RR]addr0 => /addrI/eqP.
  rewrite eq_sym mulf_eq0 (negPf (_ : a - b != 0)%RR); first by move/eqP.
  by move: Ul; rewrite subr_eq0 /= inE; case: eqP.
have: ddiff (fun _ : RR => 1%RR) [:: a, c & l] = 0%RR.
    apply: IH => //.
    by move: Ul; rewrite (@uniq_catCA _ [::a] [::b]) cat_uniq => /and3P[].
rewrite (ddiffE _ Ul) IH; last 2 first.
- by move: H; rewrite /= ltnS.
- by case/andP: Ul.
rewrite add0r => /eqP.
rewrite mulf_eq0 (negPf (_ : a - b != 0)%RR) //; first by move/eqP.
by move: Ul; rewrite subr_eq0 /= inE; case: eqP.
Qed.

Lemma sum_prod_uniq (l : seq RR) : (1 < size l)%nat -> uniq l ->
  (\sum_(i <- l) (1/(\prod_(j <- l | j != i) (i - j))) = 0)%RR.
Proof.
move=> Hs Ul.
by have /ddiff1/(_ Ul){2}<-: (1 < size l <= size l)%nat by rewrite Hs leqnn.
Qed.

End DiffMore.

(* Version of ddiff with integral *)
Fixpoint iddiff_rec l f prev var acc :=
  if l is a :: l1 then
    RInt (fun z => 
             iddiff_rec l1 (Derive f) a z ((a - prev) * z + acc)) 0 var
  else f acc.

Definition iddiff f l  :=
  if l is a :: l1 then
    iddiff_rec l1 f a 1 a
   else 0.


Lemma iddiff_rec_sum b1 b2 c1 c2 f k prev var acc l :
  c1 < b1 -> b2 < c2 ->
  uniq (prev :: l) ->
  (forall i, i \in prev :: l -> b1 <= i <= b2) ->
  (forall i, i \in prev :: l -> b1 <= (i - k) * var + acc <= b2) ->
  (0 <= var) ->
  (forall m x, (m <= (size l))%nat -> b1 <= x <= b2 -> continuous (Derive_n f m) x) ->
  (forall m x, (m <= (size l))%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  iddiff_rec l f prev var ((prev - k) * var + acc) = 
    \sum_(i <- (prev :: l)) (f ((i - k) * var + acc)) / (\prod_(j <- prev :: l | j != i) (i - j)).
Proof.
pose RC := R_CompleteNormedModule.
move=> c1Lb1 b2Lc2.
elim: l f k prev var acc => [f k prev var acc Ul Hb Hc Hv Df De | 
                             a l IH f k prev var acc Ul Hb Hc Hv Df De] /=.
  by rewrite !(big_cons, big_nil) eqxx divr1 addr0.
have F i :
  i \in a :: l ->
  ex_RInt
    (fun y : R =>
     Derive f ((i - prev) * y + ((prev - k) * var + acc)%R)%RR) 0 var.
  move=> Hi.
  apply: ex_RInt_ext => [x Hx /=|].
    apply: etrans; last first.
      set D := Derive _ _.
      rewrite -[D]mul1r -(@divff _ (i - prev)).
        by rewrite [(_/_)%RR]mulrC -mulrA.
      rewrite subr_eq0.
      move: Ul; rewrite /= => /and3P[H1 _ _].
      by apply: contra H1 => /eqP<-.
    by [].
  apply: ex_RInt_scal.
  apply: ex_RInt_comp_lin.
  apply: ex_RInt_continuous => z [Hz1 Hz2].
  apply: Df (isT : (1 <= size (a :: l))%nat) _.
  have F1 : b1 <= (prev - k) * var + acc <= b2.
    by apply: Hc; rewrite inE eqxx.
  have F2 : b1 <= (i - k) * var + acc <= b2.
    by apply: Hc; rewrite inE Hi orbT.
  split.
    apply: Rle_trans Hz1.
    by apply: Rmin_glb; toR; nra.
  apply: Rle_trans Hz2 _.
  by apply: Rmax_lub; toR; nra.
apply: etrans.
  apply: RInt_ext => x Hx.
  apply: IH => [|u Hu|i Hi||m y Hm Hy|[|m] y Hm Hy] //; first by case/andP: Ul.
  - by apply: Hb; rewrite inE Hu orbT.
  - rewrite Rmin_left // Rmax_right // in Hx.
    have F1 : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    have F2 : b1 <= (i - k) * var + acc <= b2.
      by apply: Hc; rewrite inE Hi orbT.
    by nra.
  - by rewrite Rmin_left in Hx; lra.
  - apply: continuous_ext=> [z|].
      by rewrite -Derive_nS.
    by apply: Df.
  - apply: ex_derive_ext => [z|].
      by rewrite -Derive_nS.
    by apply: De (_ : (m.+2 <= size (a :: l))%nat) _.
apply: etrans.
  apply: RInt_sum => i Hi _.
  apply: ex_RInt_ext => [x Hx|].
    by rewrite mulrC.
  apply: ex_RInt_scal.
  by apply: F.
apply: etrans.
  apply: eq_bigr => i _.
  apply: RInt_ext => x Hx.
  apply: Rmult_comm.
apply: etrans.
  rewrite big_seq_cond.
  apply: eq_bigr => i; rewrite andbT => Hi.
  apply: RInt_scal.
  by apply: F.
apply: etrans.
  apply: eq_bigr => i;  rewrite andbT => Hi.
  apply: f_equal.
  apply: (RInt_deriv_lin _ _ c1Lb1 b2Lc2) => //.
  - have /= /andP[V _] := Ul.
    by rewrite subr_eq0; apply: contra V => /eqP<-.
  - have F1 : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    by lra.
  - have F2 : b1 <= (i - k) * var + acc <= b2.
      by apply: Hc; rewrite inE Hi orbT.
    by toR; lra.
  - move=> x Hx.
    by apply: De (_ : (1 <= size (a :: l))%nat) _ => //; lra.
  - move=> x Hx.
    by apply: Df (_ : (1 <= size (a :: l))%nat) _ => //; lra.
apply: etrans.
  apply: eq_bigr => i; rewrite andbT => Hi.
  apply: etrans.
    apply: mulrA.
  apply: f_equal2; last by [].
  apply: etrans (_ : (\prod_(j <- prev :: a :: l | j != i) (i - j))^-1 = _).
    rewrite [in RHS]big_cons ifT; last first.
      case/andP: Ul => U _.
      by apply: contra U => /eqP->.
    rewrite invfM mulrC; toR.
    rewrite {2}/Rinvx ifT //.
    rewrite subr_eq0 eq_sym.
    case/andP: Ul => U _.
    by apply: contra U => /eqP->.
  by [].
apply: etrans.
  apply: eq_bigr => i _.
  apply: mulrBr.
rewrite sumrB.
apply: etrans.
  apply: f_equal2.
    apply: eq_bigr => i _.
    apply: f_equal2; first by [].
    apply: etrans (_ : f ((i - k) * var + acc) = _); last by [].
    by congr f; toR; lra.
  apply: f_equal.
  apply: eq_bigr => i _.
    apply: f_equal2; first by [].
    apply: etrans (_ : f ((prev - k) * var + acc) = _); last by [].
    by congr f; toR; lra.
rewrite -!big_seq_cond.
rewrite /= [RHS]big_cons /=.
rewrite [LHS]addrC.
congr (_ + _); last first.
  apply: eq_bigr => i _.
  by rewrite mulrC.
rewrite -mulr_suml mulrC -mulrN.
congr (_ * _).
  have H := (fun x => sum_prod_uniq x Ul) isT.
  rewrite big_cons mul1r in H.
move/eqP: H; rewrite addr_eq0 => /eqP->.
congr (- _).
apply: eq_bigr => i _.
by rewrite div1r.
Qed.

Lemma iddiff_diff b1 b2 c1 c2 f l :
  c1 < b1 -> b2 < c2 ->
  uniq l ->
  (forall i, i \in l -> b1 <= i <= b2) ->
  (forall m x, (m <= (size l).-1)%nat -> b1 <= x <= b2 -> continuous (Derive_n f m) x) ->
  (forall m x, (m <= (size l).-1)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  iddiff f l = ddiff f l.
Proof.
move=> c1Lb1 b2Lc2.
case: l => /= a l; first by rewrite ddiff_nil.
move=> Ul Hb Df De.
rewrite {2}(_ : a = (a - a) * 1 + a); try lra.
rewrite (@iddiff_rec_sum b1 b2 c1 c2) => // [|i Hi|]; try lra.
  by apply: eq_bigr => i _; rewrite mulr1 subrK.
by have := Hb _ Hi; lra.
Qed.

Lemma iddiff_rec_le b1 b2 c1 c2 f k x y prev var acc l :
  c1 < b1 -> b2 < c2 ->
  (x <= y) ->
  uniq (prev :: x :: y :: l) ->
  (forall i, i \in prev :: x :: y :: l -> b1 <= i <= b2) ->
  (forall i, i \in prev :: x :: y :: l -> b1 <= (i - k) * var + acc <= b2) ->
  (0 <= var) ->
  (forall m x, (m <= (size l).+2)%nat -> b1 <= x <= b2 -> continuous (Derive_n f m) x) ->
  (forall x,  b1 <= x <= b2 ->  0 <= Derive_n f (size l).+2 x) ->
  (forall m x, (m <= (size l).+2)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  iddiff_rec (rcons l x) f prev var ((prev - k) * var + acc) <=
  iddiff_rec (rcons l y)  f prev var ((prev - k) * var + acc).
Proof.
pose RC := R_CompleteNormedModule.
move=> c1Lb1 b2Lc2 xLy.
elim: l f k prev var acc => [f k prev var acc Ul Hb Hc Hv Df Dp De | 
                             a l IH f k prev var acc Ul Hb Hc Hv Df Dp De] /=.
  have Fp : b1 <= (prev - k) * var + acc <= b2.
    by apply: Hc; rewrite inE eqxx.
  have Fx : b1 <= (x - k) * var + acc <= b2.
    by apply: Hc; rewrite !inE eqxx ?orbT.
  have Fy : b1 <= (y - k) * var + acc <= b2.
    by apply: Hc; rewrite !inE eqxx ?orbT.
  apply: RInt_le => //.
  - apply: ex_RInt_comp_lin1.
    apply: ex_RInt_continuous => x1 Hx1.
    apply:  (Df 1%nat) => //.
    by move: Hx1; rewrite /Rmin /Rmax; case: Rle_dec; nra.
  - apply: ex_RInt_comp_lin1.
    apply: ex_RInt_continuous => x1 Hx1.
    apply:  (Df 1%nat) => //.
    by move: Hx1; rewrite /Rmin /Rmax; case: Rle_dec; nra.
  move=> z Hz.
  apply: MVT_le => [t Ht|t Ht|t Ht|].
  - by apply/Derive_correct/(De 2%nat) => //; nra.
  - by apply: Dp => //; nra.
  - by apply/continuous_continuity_pt/(Df 1%nat) => //; nra.
  by nra.
apply: RInt_le => //.
- apply: ex_RInt_ext => [z Hz|].
  rewrite Rmin_left ?Rmax_right in Hz; last 2 first.
  - by [].
  - by [].    
  rewrite [RHS](@iddiff_rec_sum b1 b2 c1 c2) //.
  - have := Ul; rewrite /= rcons_uniq !(inE, in_cons, mem_rcons).
    rewrite !negb_or [a == x]eq_sym; case: (x == a); first by rewrite !andbF.
    case: (a \in l); first by rewrite !andbF.
    case: (x \in l); first by rewrite !andbF.
    by case: (uniq l) => //; rewrite !andbF.
  - move=> i Hi; apply: Hb.
    have := Hi; rewrite !(inE, in_cons, mem_rcons).
    case: (i == a); rewrite ?orbT //.
    case: (i == x); rewrite ?orbT //.
    by case: (i \in l); rewrite ?orbT.
  - move=> i Hi.
    have Fp : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    have Fi : b1 <= (i - k) * var + acc <= b2.
      apply: Hc; move: Hi; rewrite !(inE, in_cons, mem_rcons).
      case: (i == a); rewrite ?orbT //.
      case: (i == x); rewrite ?orbT //.
      by case: (i \in l); rewrite ?orbT.
    nra.
  - by lra.
  - rewrite size_rcons => m t Hm tB.
    rewrite -Derive_nS.
    apply: Df => //.
    by apply: leq_trans Hm _.
  - rewrite size_rcons => [] [|m] t Hm tB // .
    rewrite -ex_derive_nSS.
    apply: De => //.
    by rewrite !ltnS ltnW.
  - apply: ex_RInt_sum => i Hi _.
    apply: ex_RInt_ext => [z Hz|].
      by rewrite mulrC.
    apply: ex_RInt_scal.
    apply: ex_RInt_continuous => z.
    rewrite Rmin_left // Rmax_right // => Hz.
    apply: continuous_comp.
       by repeat apply: continuous_plus || apply: continuous_id || 
                  apply: continuous_const || apply: continuous_mult.
    apply: (@Df 1%nat) => //.
    have Fp : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    have Fi : b1 <= (i - k) * var + acc <= b2.
      apply: Hc; move: Hi; rewrite !(inE, in_cons, mem_rcons).
      case: (i == a); rewrite ?orbT //.
      case: (i == x); rewrite ?orbT //.
      by case: (i \in l); rewrite ?orbT.
     toR.
     case: (Req_dec 0 z) => [<-|]; first by lra.
     case: (Req_dec var z) => [<-|]; first by lra.
     nra.
- apply: ex_RInt_ext => [z Hz|].
  rewrite Rmin_left ?Rmax_right in Hz; last 2 first.
  - by [].
  - by [].    
  rewrite [RHS](@iddiff_rec_sum b1 b2 c1 c2) //.
  - have := Ul; rewrite /= rcons_uniq !(inE, in_cons, mem_rcons).
    rewrite !negb_or [a == y]eq_sym; case: (y == a); first by rewrite !andbF.
    case: (a \in l); first by rewrite !andbF.
    case: (y \in l); first by rewrite !andbF.
    by case: (uniq l) => //; rewrite !andbF.
  - move=> i Hi; apply: Hb.
    have := Hi; rewrite !(inE, in_cons, mem_rcons).
    case: (i == a); rewrite ?orbT //.
    case: (i == y); rewrite ?orbT //.
    by case: (i \in l); rewrite ?orbT.
  - move=> i Hi.
    have Fp : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    have Fi : b1 <= (i - k) * var + acc <= b2.
      apply: Hc; move: Hi; rewrite !(inE, in_cons, mem_rcons).
      case: (i == a); rewrite ?orbT //.
      case: (i == y); rewrite ?orbT //.
      by case: (i \in l); rewrite ?orbT.
    nra.
  - by lra.
  - rewrite size_rcons => m t Hm tB.
    rewrite -Derive_nS.
    apply: Df => //.
    by apply: leq_trans Hm _.
  - rewrite size_rcons => [] [|m] t Hm tB // .
    rewrite -ex_derive_nSS.
    apply: De => //.
    by rewrite !ltnS ltnW.
  - apply: ex_RInt_sum => i Hi _.
    apply: ex_RInt_ext => [z Hz|].
      by rewrite mulrC.
    apply: ex_RInt_scal.
    apply: ex_RInt_continuous => z.
    rewrite Rmin_left // Rmax_right // => Hz.
    apply: continuous_comp.
       by repeat apply: continuous_plus || apply: continuous_id || 
                  apply: continuous_const || apply: continuous_mult.
    apply: (@Df 1%nat) => //.
    have Fp : b1 <= (prev - k) * var + acc <= b2.
      by apply: Hc; rewrite inE eqxx.
    have Fi : b1 <= (i - k) * var + acc <= b2.
      apply: Hc; move: Hi; rewrite !(inE, in_cons, mem_rcons).
      case: (i == a); rewrite ?orbT //.
      case: (i == y); rewrite ?orbT //.
      by case: (i \in l); rewrite ?orbT.
     toR.
     case: (Req_dec 0 z) => [<-|]; first by lra.
     case: (Req_dec var z) => [<-|]; first by lra.
     nra.
move=> t Ht.
have Pi : perm_eq [:: a, x, y & l] [:: x, y, a & l].
  rewrite (@perm_cat2r _ l [::a; x; y] [::x; y; a]).
  by rewrite (perm_catC [::a] [::x; y]).
apply: IH => //.
- have /perm_uniq-> := Pi.
  by case/andP: Ul.
- move=> i Hi.
  apply: Hb.
  by rewrite inE -(perm_mem Pi) Hi orbT.
- move=> i Hi.
  have Fp : b1 <= (prev - k) * var + acc <= b2.
   by apply: Hc; rewrite inE eqxx.
  have Fi : b1 <= (i - k) * var + acc <= b2.
    apply: Hc.
    by rewrite inE -(perm_mem Pi) Hi orbT.
  by nra.
- by lra.
- move=> m Hm mB.
  rewrite -Derive_nS.
  by apply: Df.
- move=> z zB.
  rewrite -Derive_nS.
  by apply: Dp.
case=> // [] [|m] z Hm tB //.
  by apply: (@De 2%nat).
rewrite -ex_derive_nSS.
by apply: De.
Qed.

Lemma ddiff_le b1 b2 c1 c2 f x y l :
  c1 < b1 -> b2 < c2 ->
  (x <= y) ->
  uniq (x :: y :: l) ->
  (forall i, i \in x :: y :: l -> b1 <= i <= b2) ->
  (forall m x, (m <= (size l).+1)%nat -> b1 <= x <= b2 -> continuous (Derive_n f m) x) ->
  (forall x,  b1 <= x <= b2 ->  0 <= Derive_n f (size l).+1 x) ->
  (forall m x, (m <= (size l).+1)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  ddiff f (rcons l x) <= ddiff f (rcons l y).
Proof.
move=> c1Lb1 b2Lc2.
case: l.
  rewrite /= !ddiff_singleton; move=> xLy Ul Pb Pc Pd Pe.
  have Px : b1 <= x <= b2 by apply: Pb; rewrite !inE eqxx ?orbT.
  have Py : b1 <= y <= b2 by apply: Pb; rewrite !inE eqxx ?orbT.
  apply: MVT_le => //.
  - move=> z Hz; apply: Derive_correct.
    by apply: (Pe 1%nat) => //; lra.
  - by move=> m Hm; apply: Pd; lra.
  - move=> z Hz; apply: continuous_continuity_pt.
    by apply: (@Pc 0%nat) => //; lra.
move=> a l xLy Ul Pb Pc Pd Pe.
rewrite -!(@iddiff_diff b1 b2 c1 c2) //; first last.
- move=> m z Hm Bz; apply: Pe => //.
  by apply: leq_trans Hm _; rewrite size_rcons.
- move=> m z Hm Bz; apply: Pc => //.
  by apply: leq_trans Hm _; rewrite size_rcons.
- move=> i Hi; apply: Pb => //.
  move: Hi; rewrite !(inE, mem_rcons). 
  by do 3 (case: (_ \in _) || case: (_ == _); rewrite ?orbT //=).
- suff: uniq (y :: rcons (a :: l) x) by case/andP.
  suff /perm_uniq<- : perm_eq [:: x, y, a & l] (y :: rcons (a :: l) x) by [].
  by rewrite perm_sym (@perm_rcons _ _ (y :: a :: l)).
- move=> m z Hm Bz; apply: Pe => //.
  by apply: leq_trans Hm _; rewrite size_rcons.
- move=> m z Hm Bz; apply: Pc => //.
  by apply: leq_trans Hm _; rewrite size_rcons.
- move=> i Hi; apply: Pb => //.
  move: Hi; rewrite !(inE, mem_rcons). 
  by do 3 (case: (_ \in _) || case: (_ == _); rewrite ?orbT //=).
- suff: uniq (x :: rcons (a :: l) y) by case/andP.
  suff /perm_uniq<- : perm_eq [:: x, y, a & l] (x :: rcons (a :: l) y) by [].
  by rewrite perm_cons -perm_rcons.
rewrite /= {2 4}(_ : a = (a - 1) * 1 + 1); try lra.
have Pi : perm_eq [:: x, y, a & l] [:: a, x, y & l].
  rewrite (perm_cat2r _ [:: x; y; a] [:: a; x; y]) .
  by rewrite (perm_rcons a [:: x; y]).
apply: (@iddiff_rec_le b1 b2 c1 c2) => //; try lra.
- by rewrite -(perm_uniq Pi).
- by move=> i Hi; apply: Pb; rewrite (perm_mem Pi).
move=> i Hi.
suff: b1 <= i <= b2 by lra.
by apply: Pb; rewrite (perm_mem Pi).
Qed.

Lemma ddiff_ge b1 b2 c1 c2 f x y l :
  c1 < b1 -> b2 < c2 ->
  (x <= y) ->
  uniq (x :: y :: l) ->
  (forall i, i \in x :: y :: l -> b1 <= i <= b2) ->
  (forall m x, (m <= (size l).+1)%nat -> b1 <= x <= b2 -> 
    continuous (Derive_n f m) x) ->
  (forall x,  b1 <= x <= b2 ->  Derive_n f (size l).+1 x <= 0) ->
  (forall m x, (m <= (size l).+1)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  ddiff f (rcons l y) <= ddiff f (rcons l x).
Proof.
move=> c1Lb1 b2Lc2 xLy Ul Pb Pc Pd Pe.
suff: ddiff (fun z => - (f z)) (rcons l x) <= ddiff (fun z => -(f z)) (rcons l y).
  by rewrite !ddiffN; toR; lra.
apply: ddiff_le c1Lb1 b2Lc2 xLy Ul Pb _ _ _ => //.
- move=> m z Hm Bz.
  apply: continuous_ext=> [t|].
    by rewrite Derive_n_opp.
  apply: continuous_opp.
  by apply: Pc.
- move=> z Bz.
  rewrite Derive_n_opp; toR.
  have /= := Pd _ Bz; lra.
move=> m z Hm Bz.
apply: ex_derive_n_opp.
by apply: Pe.
Qed.

Lemma ierror_cheby_diff n f x :
 x \notin (cheby_nodes n) ->
 ierror f (cheby_nodes n) x = /INR (2 ^ n.-1) * 
 ddiff f (rcons (cheby_nodes n) x) * ('T_n).[x].
Proof.
pose RC := [comRingType of R].
move=> xNIc.
rewrite /ierror [_ - _](@error_ddiff [fieldType of R]); last first.
  by rewrite cons_uniq xNIc uniq_cheby_nodes.
rewrite cheby_prodl hornerE /=; toR.
rewrite -[RHS](@mulrA RC) [RHS](@mulrC RC) -![RHS](@mulrA RC); toR.
congr (_ * _).
  by apply/ddiff_perm_eq; rewrite perm_sym perm_rcons.
rewrite pow_expn; toR.
set u : R := _.[_]; field.
by apply/not_0_INR/eqP; rewrite expn_eq0.
Qed.

Lemma interpolation_cheby_ge n c1 c2 f x :
  c1 < -1 -> 1 < c2 -> -1 <= x <= 1 ->
  (forall m x, (m <= n.+1)%nat -> -1 <= x <= 1 -> continuous (Derive_n f m) x) ->
  (   (forall x,  -1 <= x <= 1-> Derive_n f n.+1 x <= 0) 
    \/
      (forall x,  -1 <= x <= 1-> Derive_n f n.+1 x >= 0)) ->
  (forall m x, (m <= n.+1)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  Rabs (ierror f (cheby_nodes n) x) <=
    Rmax (Rabs (ierror f (cheby_nodes n) (-1))) 
         (Rabs (ierror f (cheby_nodes n) 1)).
Proof.
move=> c1L1 c2G1 xB Pc Pd Pe.
have [xIc|xNIc] := boolP (x \in cheby_nodes n).
  rewrite {1}/ierror horner_interpolation // Rminus_eq_0 Rabs_R0.
  by rewrite /Rmax; case: Rle_dec => H; split_Rabs; lra.
have Ul : uniq [::-1, 1 & cheby_nodes n].
  rewrite 2!cons_uniq uniq_cheby_nodes andbT.
  rewrite inE (_: _ == _ = false); last by apply/eqP; lra.
  by apply/andP; split; apply/negP=>/cheby_nodes_bound; lra.
rewrite !ierror_cheby_diff //; last 2 first.
- by apply/negP=> /cheby_nodes_bound; lra.
- by apply/negP=> /cheby_nodes_bound; lra.
rewrite horner1_pT hornerN1_pT !Rabs_mult Rabs_R1 Rabs_exprN1 !Rmult_1_r.
rewrite -Rmult_max_distr_l; last by apply: Rabs_pos.
rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first by apply: Rabs_pos.
rewrite -[X in _ <= X]Rmult_1_r.
apply: Rmult_le_compat; try apply: Rabs_pos; last first.
  suff : -1 <= ('T_n).[x] <= 1 by split_Rabs; lra.
  rewrite -pT_Cheby //.
  by apply: COS_bound.
have [->|/eqP xD1] := (x =P 1); first by apply: Rmax_r.
have [->|/eqP xDN1] := (x =P -1); first by apply: Rmax_l.
set dx := ddiff _ _; set dN1 := ddiff _ _; set d1 := ddiff _ _.
have Ux : uniq [:: x, 1 & cheby_nodes n].
  rewrite 2!cons_uniq inE negb_or -andbA.
  apply/and4P; split => //; try lra.
    by apply/negP=> /cheby_nodes_bound; lra.
  by apply: uniq_cheby_nodes.
have Bx i :
    i \in [:: x, 1 & cheby_nodes n] -> -1 <= i <= 1.
  rewrite 2!inE => /or3P[/eqP->|/eqP->|H]; try lra.
  by apply: cheby_nodes_boundW H.
have UNx : uniq [:: -1, x & cheby_nodes n].
  rewrite 2!cons_uniq inE negb_or -andbA.
  apply/and4P; split => //; try lra.
  - by rewrite eq_sym.
  - by apply/negP=> /cheby_nodes_bound; lra.
  by apply: uniq_cheby_nodes.
have BxN i :
    i \in [:: -1, x & cheby_nodes n] -> -1 <= i <= 1.
  rewrite 2!inE => /or3P[/eqP->|/eqP->|H]; try lra.
  by apply: cheby_nodes_boundW H.
case: Pd => Pd.
  suff: d1 <= dx <= dN1.
    by rewrite /Rmax; case: Rle_dec; split_Rabs; lra.
  split; apply: (ddiff_ge c1L1 c2G1); rewrite ?size_cheby_nodes //; try lra.
suff: dN1 <= dx <= d1.
  by rewrite /Rmax; case: Rle_dec; split_Rabs; lra.
split; apply: (ddiff_le c1L1 c2G1); rewrite ?size_cheby_nodes //; try lra.
  by move=> y /Pd; lra.
by move=> y /Pd; lra.
Qed.

Lemma ierror_scheby_diff n a b f x :
  a < b -> x \notin (scheby_nodes a b n) ->
 ierror f (scheby_nodes a b n) x = (b - a) ^+ n/INR (2 ^ n.*2.-1) * 
 ddiff f (rcons (scheby_nodes a b n) x) * ('T^(a,b)_n).[x].
Proof.
pose RC := [comRingType of R].
move=> aLb xNIc.
rewrite /ierror [_ - _](@error_ddiff [fieldType of R]); last first.
  by rewrite cons_uniq xNIc uniq_scheby_nodes.
rewrite scheby_prodl // hornerE /=.
rewrite /prodl undup_id ?uniq_scheby_nodes //.
set p : R := _.[_].
rewrite -[RHS](@mulrA RC) [RHS](@mulrC RC) -![RHS](@mulrA RC); toR.
congr (_ * _).
  by apply/ddiff_perm_eq; rewrite perm_sym perm_rcons.
rewrite pow_expn; toR. 
set u : R := INR _; set v : R := _ ^+ _.
have vNZ : v <> 0.
  by apply/eqP; rewrite expf_neq0 //; apply/eqP; toR; lra.
have uNZ : u <> 0. 
  by apply/not_0_INR/eqP; rewrite expn_eq0.
rewrite /Rinvx (negPf (_ : v != 0)) /=; last by apply/eqP.
by field.
Qed.

Lemma interpolation_scheby_ge n a b c1 c2 f x :
  a < b -> c1 < a -> b < c2 -> a <= x <= b ->
  (forall m x, (m <= n.+1)%nat -> a <= x <= b -> continuous (Derive_n f m) x) ->
  (   (forall x,  a <= x <= b -> Derive_n f n.+1 x <= 0) 
    \/
      (forall x,  a <= x <= b -> Derive_n f n.+1 x >= 0)) ->
  (forall m x, (m <= n.+1)%nat -> c1 < x < c2 -> ex_derive_n f m x) ->
  Rabs (ierror f (scheby_nodes a b n) x) <=
    Rmax (Rabs (ierror f (scheby_nodes a b n) a)) 
         (Rabs (ierror f (scheby_nodes a b n) b)).
Proof.
move=> aLb c1La bLc2 xB Pc Pd Pe.
have [xIc|xNIc] := boolP (x \in scheby_nodes a b n).
  rewrite {1}/ierror horner_interpolation // Rminus_eq_0 Rabs_R0.
  by rewrite /Rmax; case: Rle_dec => H; split_Rabs; lra.
have Ul : uniq [::a, b & scheby_nodes a b n].
  rewrite 2!cons_uniq uniq_scheby_nodes // andbT.
  rewrite inE (_: _ == _ = false); last by apply/eqP; lra.
  by apply/andP; split; apply/negP=>/scheby_nodes_bound; lra.
rewrite !ierror_scheby_diff //; last 2 first.
- by apply/negP=> /scheby_nodes_bound; lra.
- by apply/negP=> /scheby_nodes_bound; lra.
rewrite horner_pTab_a; last by apply/eqP; lra.
rewrite horner_pTab_b; last by apply/eqP; lra.
rewrite horner1_pT hornerN1_pT !Rabs_mult Rabs_R1 Rabs_exprN1 !Rmult_1_r.
rewrite -Rmult_max_distr_l; last by apply:Rmult_le_pos; apply: Rabs_pos.
rewrite !Rmult_assoc; apply: Rmult_le_compat_l; first by apply: Rabs_pos.
apply: Rmult_le_compat_l; first by apply: Rabs_pos.
rewrite -[X in _ <= X]Rmult_1_r.
apply: Rmult_le_compat; try apply: Rabs_pos; last first.
  suff : -1 <= ('T^(a,b)_n).[x] <= 1 by split_Rabs; lra.
  rewrite horner_pTab -pT_Cheby //.
    by apply: COS_bound.
  toR; rewrite /Rinvx ifT; last by apply/eqP; lra.
  split.
    apply: Float.Generic_proof.Rdiv_le_mult_pos; try lra.
    by rewrite mulr2n; toR; lra.
  apply: Float.Generic_proof.Rdiv_ge_mult_pos; try lra.
  by rewrite mulr2n; toR; lra.
have [->|/eqP xDb] := (x =P b); first by apply: Rmax_r.
have [->|/eqP xDa] := (x =P a); first by apply: Rmax_l.
set dx := ddiff _ _; set da := ddiff _ _; set db := ddiff _ _.
have Ux : uniq [:: x, b & scheby_nodes a b n].
  rewrite 2!cons_uniq inE negb_or -andbA.
  apply/and4P; split => //; try lra.
    by apply/negP=> /scheby_nodes_bound; lra.
  by apply: uniq_scheby_nodes.
have Bx i :
    i \in [:: x, b & scheby_nodes a b n] -> a <= i <= b.
  rewrite 2!inE => /or3P[/eqP->|/eqP->|H]; try lra.
  by apply: scheby_nodes_boundW H.
have UNx : uniq [:: a, x & scheby_nodes a b n].
  rewrite 2!cons_uniq inE negb_or -andbA.
  apply/and4P; split => //; try lra.
  - by rewrite eq_sym.
  - by apply/negP=> /scheby_nodes_bound; lra.
  by apply: uniq_scheby_nodes.
have BxN i :
    i \in [:: a, x & scheby_nodes a b n] -> a <= i <= b.
  rewrite 2!inE => /or3P[/eqP->|/eqP->|H]; try lra.
  by apply: scheby_nodes_boundW H.
case: Pd => Pd.
  suff: db <= dx <= da.
    by rewrite /Rmax; case: Rle_dec; split_Rabs; lra.
  split; apply: (ddiff_ge c1La bLc2); rewrite ?size_scheby_nodes //; try lra.
suff: da <= dx <= db.
  by rewrite /Rmax; case: Rle_dec; split_Rabs; lra.
split; apply: (ddiff_le c1La bLc2); rewrite ?size_scheby_nodes //; try lra.
  by move=> y /Pd; lra.
by move=> y /Pd; lra.
Qed.
