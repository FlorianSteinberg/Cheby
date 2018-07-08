From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import Rstruct CPoly CPoly_trigo.
Import Rtrigo_def.
Import Rtrigo1.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.

(******************************************************************************)
(* The interpotation with the Chebyshev flavor                                *)
(*                      prod l == compute the polynomial of lowest degree     *)
(*                                whose roots are exactly those of l          *)
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
(******************************************************************************)

Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0).

Definition rm1 := (mulr1, mul1r, mulr1n).

Section Interpolation.

Variable R : fieldType.
Variable f : R -> R.

Definition prodl (l : seq R) : {poly R} :=
  \prod_(i <- undup l) ('X - i%:P).

Local Notation "'W[ l ]" := (prodl l) (format "''W[' l ]").

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

Lemma size_prodl_ulist l : uniq l -> size (prodl l) = (size l).+1.
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

Lemma prodl_deriv_fact l (n := size l) :
  uniq l -> (prodl l)^`(n) = (n `!)%:R%:P.
Proof.
move=> Ul.
rewrite {1}(pred_Sn n) -(size_prodl_ulist Ul) derivn_size.
have := monic_prodl l.
rewrite monicE => /eqP->.
by rewrite size_prodl_ulist.
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

Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.
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

Definition has_zeros f n a b := 
  exists l : seq R,
   [/\  uniq l,
        forall x,  x \in l ->  a <= x <= b /\ f x = 0 &
        size l = n].

Import path.

Lemma eqR_leb a b : (a == b) = (Rleb a b && Rleb b a).
Proof.
apply/eqP/andP=> [->|[/RlebP H /RlebP]]; try lra.
by split; apply/RlebP; lra.
Qed.

Lemma Rleb_total : total Rleb.
Proof.
move=> a b; have [/RlebP->//|/RlebP->//] : a <= b \/ b <= a by lra.
by rewrite orbT.
Qed.

Lemma Rleb_trans : transitive Rleb.
Proof. by move=> a b c /RlebP H /RlebP H1;apply/RlebP; lra. Qed.

Lemma Rltb_trans : transitive Rltb.
Proof. by move=> a b c /RltbP H /RltbP H1;apply/RltbP; lra. Qed.

Lemma Rltb_sorted_uniq_leb s : sorted Rltb s = uniq s && sorted Rleb s.
Proof.
case: s => //= n s; elim: s n => //= m s IHs n.
rewrite inE Rltb_def negb_or IHs -!andbA eq_sym.
case sn: (n \in s); last do !bool_congr.
rewrite andbF; apply/and5P=> [[ne_nm lenm _ _ le_ms]]; case/negP: ne_nm.
by rewrite eqR_leb lenm; apply: (allP (order_path_min Rleb_trans le_ms)).
Qed.

Lemma has_zerosEs f n a b :
  has_zeros f n a b <->
  exists l : seq R,
   [/\  sorted Rltb l,
        forall x,  x \in l ->  a <= x <= b /\ f x = 0 &
        size l = n].
Proof.
split=> [] [l [H1 H2 H3]].
  exists (sort Rleb l); split => [|x|].
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
 (forall x, a <= x <= b -> continuity_pt f x) ->
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
  by move=> HH; apply: Hc; lra.
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
 (forall x k, (k <= m)%nat -> a <= x <= b -> continuity_pt (Derive_n f k) x) ->
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

Lemma ex_derive_n_minus_inter f g n a b (h := fun z => f z - g z) :
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n f k x) ->
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n g k x) ->
      (forall x k,
        (k <= n)%nat -> a < x < b -> ex_derive_n h k x).
Proof.
move=> Hf Hg x k kLn aLxLb.
pose d := (Rmin (x - a) (b - x)) / 2.
have Pd : 0 < d.
  by rewrite /d /Rmin; case: Rle_dec; lra.
have Hd : a < x - d < x /\ x < x + d < b.
  by rewrite /d /Rmin; case: Rle_dec; lra.
apply: ex_derive_n_minus.
  exists (mkposreal _ Pd) => /= y Hy k1 Hk1.
  apply: Hf; first apply : leq_trans kLn.
    by apply/leP.
  rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in Hy.
  split_Rabs; lra.
exists (mkposreal _ Pd) => /= y Hy k1 Hk1.
apply: Hg; first apply : leq_trans kLn.
  by apply/leP.
rewrite /ball /= /AbsRing_ball /= /abs /= /minus /plus /opp /= in Hy.
split_Rabs; lra.
Qed.

Variable f : R -> R.
Variable n : nat.
Variable l : list R.
Hypothesis size_n : n = size l.
Hypothesis Ul : uniq l.
Variables a b : R.
Hypothesis range : forall x : R, x \in l -> a <= x <= b.
Hypothesis deriv_f : 
  forall x, a <= x <= b ->
   locally x (fun y : R => forall k : nat, (k <= n)%nat -> ex_derive_n f k y).

Hypothesis cont_f :
 forall x k, (k <= n)%nat -> a <= x <= b ->
   continuity_pt (Derive_n f k) x.

Definition ierror x := f x - (interpolation f l).[x].

Lemma ierror_val x :
  a <= x <= b ->
  ierror x != 0 -> exists z, 
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
      have /deriv_f[e] : a <= x2 <= b by lra. 
      by apply => //; apply: ball_center.
    by apply: ex_derive_n_horner.
  apply: ex_derive_n_scal_l.
  by apply: ex_derive_n_horner.
have F1 y k : (k <= n)%nat -> a <= y <= b ->
  locally y 
        (fun y => 
          Derive_n f k y - Derive_n (horner (interpolation f l)) k y
                         - Derive_n (fun y => c * (prodl l).[y]) k y = 
          Derive_n g k y).
  move=> kLn aLyLb.
  have [e He] := deriv_f aLyLb.
  exists (pos_div_2 e) => y1 Hy1.
  rewrite /g /ierror !Derive_n_minus //.
  - exists (pos_div_2 e) => y2 Hy2 k1 k1Ln.
    apply: He => //.
      rewrite (_ : e = (pos_div_2 e) + (pos_div_2 e) :> R) /=; try lra.
      by apply: ball_triangle Hy2.
    by apply: leq_trans kLn; apply/leP.
  - by exists e => *; apply: ex_derive_n_horner.
  - exists (pos_div_2 (pos_div_2 e)) => y2 Hy2 k1 k1Ln.
    apply: ex_derive_n_minus.
      exists (pos_div_2 (pos_div_2 e)) => y3 Hy3 k2 k2Ln.
      apply: He => //.
        rewrite (_ : e = (pos_div_2 e) + (pos_div_2 (pos_div_2 e))
                                       + (pos_div_2 (pos_div_2 e)):> R) /=; try lra.
        apply: ball_triangle Hy3.
        by apply: ball_triangle Hy2.
      apply: leq_trans kLn.
      by apply: leq_trans (_ : k1 <= _)%nat; apply/leP.
    by exists e => *; apply: ex_derive_n_horner.
  exists e => *; apply: ex_derive_n_scal_l.
  by apply: ex_derive_n_horner.
have F2 y k : (k <= n)%nat -> a <= y <= b ->
              continuity_pt (Derive_n g k) y.
  move=> kLn aLyLb.
  apply: continuity_pt_ext_loc (F1 _ _ kLn aLyLb) _.
  apply: continuity_pt_minus.
    apply: continuity_pt_minus.
      by apply: cont_f.
    apply: derivable_continuous_pt.
    apply: ex_derive_Reals_0.
    by apply: (@ex_derive_n_horner _ _ k.+1).
  apply: derivable_continuous_pt.
  apply: ex_derive_Reals_0.
  apply: (@ex_derive_n_scal_l _ k.+1).
  by apply: ex_derive_n_horner.
have F3 : has_zeros g n.+1 a b.
  exists (x :: l); split => [|y] //=.
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
have [e /(_ z (ball_center _ _))<-] := F1 _ _ (leqnn n) Hz.
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
apply/eqP.
rewrite -[_ != _]/(n`!%:R != 0%:R :> R).
rewrite Num.Theory.eqr_nat.
apply: lt0n_neq0.
apply: fact_gt0.
Qed.

End bound.

Definition cheby_nodes (n : nat) := [seq cos (i.*2.+1%:R * PI / n.*2%:R) | i <- seq.iota 0%nat n].

Lemma size_cheby_nodes n : size (cheby_nodes n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma cheby_nodes_bound n x :
  x \in cheby_nodes n -> -1 <= x <= 1.
Proof. by move=> /mapP[i _ ->]; apply: COS_bound. Qed.

Lemma natr_INR n : n%:R = INR n.
Proof.
elim: n => // n IH.
rewrite  S_INR [_.+1%:R](natrD _ 1) IH -[1%:R]/1.
toR; lra.
Qed.

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
  apply: Interval_generic_proof.Rdiv_ge_mult_pos; nra.
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
  apply: cos_is_inj => //.
    split.
      by apply: Rdiv_le_0_compat; nra.
    by apply: Interval_generic_proof.Rdiv_ge_mult_pos; nra.
  split.
    by apply: Rdiv_le_0_compat; nra.
  by apply: Interval_generic_proof.Rdiv_ge_mult_pos; nra.
suff : (1 + 2 * INR x) * PI = (1 + 2 * INR y) * PI.
  by nra.
have F1 x1 : x1 / (2 * INR n) * (2 * INR n) = x1.
  field; lra.
by rewrite -[_ * PI]F1 F F1.
Qed.

Lemma cheby_prodl n : 
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

Section ChebyBound.

Variable f : R -> R.
Variable n : nat.
Hypothesis deriv_f : 
  forall x, -1 <= x <= 1 ->
   locally x (fun y : R => forall k : nat, (k <= n)%nat -> ex_derive_n f k y).

Hypothesis cont_f :
 forall x k, (k <= n)%nat -> -1 <= x <= 1 ->
   continuity_pt (Derive_n f k) x.

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
  apply: Interval_missing.Rdiv_pos_compat; try lra.
  rewrite natr_INR.
  apply/lt_0_INR/leP/neq0_lt0n/eqP/eqP.
  by rewrite muln_eq0 negb_or -!lt0n expn_gt0 fact_gt0.
have [z1 [H1z1 ->]] := ierror_val (sym_equal (size_cheby_nodes n))
         (uniq_cheby_nodes n) (@cheby_nodes_bound n)
         deriv_f cont_f Hx Hc.
rewrite !Rabs_mult Rabs_R1 Rabs_Rinv; try lra.
rewrite Rabs_pos_eq; try lra.
rewrite natrM.
rewrite Rmult_comm/Rdiv Rinv_mult_distr; try lra.
rewrite -!Rmult_assoc.
apply: Rmult_le_compat; last by apply: Hy; lra.
- apply: Interval_missing.Rmult_le_pos_pos => //.
    rewrite Rmult_1_r.
    by apply: Rabs_pos.
- by lra.
- by apply: Rabs_pos.
- apply: Rmult_le_compat_r; try lra.
rewrite Rmult_1_r Rmult_1_l.
have -> : (prodl (cheby_nodes n)).[x] = / (expn 2 n.-1)%:R * ((pT _ n).[x]).  rewrite cheby_prodl /prodl undup_id ?uniq_cheby_nodes //.
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

Definition scheby_nodes (n : nat) := [seq ((b - a) * i + a + b) / 2 | i <- cheby_nodes n].

Lemma size_scheby_nodes n : size (scheby_nodes n) = n.
Proof. by rewrite size_map size_cheby_nodes. Qed.

Lemma scheby_nodes_bound n x :
  x \in scheby_nodes n -> a <= x <= b.
Proof.
move=> /mapP[i /cheby_nodes_bound] [H1 H2] ->.
nra.
Qed.

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
   'T^(a,b)_n = ((expn 2 (n.*2.-1))%:R / (b - a)^+n) *:  \prod_(z <- scheby_nodes n) ('X - z%:P).
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
Variable f : R -> R.
Variable n : nat.
Hypothesis deriv_f : 
  forall x, a <= x <= b ->
   locally x (fun y : R => forall k : nat, (k <= n)%nat -> ex_derive_n f k y).

Hypothesis cont_f :
 forall x k, (k <= n)%nat -> a <= x <= b ->
   continuity_pt (Derive_n f k) x.

Lemma Tab_bound x : a <= x <= b -> -1 <= (Tab a b).[x] <= 1.
Proof.
move=> [H1 H2].
have D :  b + - a != 0 by apply/eqP; lra.
have <-: (Tab a b).[a] = -1.
  rewrite /Tab !hornerE /=; toR; rewrite /Rinvx D.
  by field; apply/eqP.
have <-: (Tab a b).[b] = 1.
  rewrite /Tab !hornerE /=; toR; rewrite /Rinvx D.
  by field; apply/eqP.
have F : 0 <= ((1 + 1) / (b - a))%R.
  by apply: Rdiv_le_0_compat; lra.
rewrite /Tab !hornerE; split; apply: Rplus_le_compat_r.
- by apply: Rmult_le_compat_l; toR; rewrite /Rinvx D.
- by apply: Rmult_le_compat_l; toR; rewrite /Rinvx D.
Qed.

Lemma ierror_scheby x z :
  a <= x <= b ->
  (forall y,   a <= y <= b -> Rabs (Derive_n f n y) <= z) ->
  Rabs (ierror f (scheby_nodes a b n) x) <= ((b - a)^+n / ((expn 2 n.*2.-1 * n `!) %:R)) * z.
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
  apply: Interval_missing.Rdiv_pos_compat; try lra.
  rewrite natr_INR.
  apply/lt_0_INR/leP/neq0_lt0n/eqP/eqP.
  by rewrite muln_eq0 negb_or -!lt0n expn_gt0 fact_gt0.
have [z1 [H1z1 ->]] := ierror_val (sym_equal (size_scheby_nodes a b n))
         (@uniq_scheby_nodes a b aLb n) (@scheby_nodes_bound a b aLb n)
         deriv_f cont_f Hx Hc.
rewrite !Rabs_mult Rabs_R1 Rabs_Rinv; try lra.
rewrite Rabs_pos_eq; try lra.
rewrite natrM.
rewrite Rmult_comm/Rdiv Rinv_mult_distr; try lra.
rewrite -!Rmult_assoc.
apply: Rmult_le_compat; last by apply: Hy; lra.
- apply: Interval_missing.Rmult_le_pos_pos => //.
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
  rewrite /Rdiv Rmult_assoc -Rinv_mult_distr ?F //.
  by apply/(not_INR _ 0)/eqP.
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
  apply Rlt_div_l; try lra.
  rewrite Rmult_comm.
  apply : Rmult_lt_compat_l => //.
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
  rewrite /Rdiv Rmult_assoc -Rinv_mult_distr ?F //.
  by apply/(not_INR _ 0)/eqP.
have PIpos : 0 < PI by have := PI2_3_2; lra.
rewrite /dsprod_cheby big_map.
pose g i1 := (i1.*2.+1%:R * PI / n.+1.*2%:R).
rewrite -val_enum_ord big_map [LHS]/=.
rewrite (eq_bigr (fun k : 'I_n.+1 => cos (INR i * g k) * cos (INR j * g k)))
    => [|k _]; last first.
  rewrite -!pT_Cheby; try by apply: COS_bound.
  rewrite /Cheby acos_left_inv //.
  have F2 : 0 < n.+1.*2%:R.
   rewrite natr_INR; apply/(lt_INR 0)/leP.
   apply: leq_ltn_trans (_ : i.*2 < _)%nat => //.
   by rewrite ltn_double.
  split.
    apply: Rmult_le_pos; last first.
      by apply/Rlt_le/Rinv_0_lt_compat.
    apply: Rmult_le_pos; last by lra.
    by rewrite natr_INR; apply/(le_INR 0)/leP.
  apply Rle_div_l; try lra.
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

End ChebyCoef.
