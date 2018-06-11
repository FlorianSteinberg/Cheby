From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Scope ring_scope.


Definition rm0 :=
 (mulr0, mul0r, subr0, sub0r, add0r, addr0, mul0rn, mulr0n, oppr0,
  scale0r, scaler0).

Definition rm1 := (mulr1, mul1r, mulr1n).

Section Interp.

Variable R : fieldType.
Variable f : R -> R.

Definition prodl (l : seq R) : {poly R} :=
  \prod_(i <- undup l) ('X - i%:P).

Local Notation "'W[ l ]" := (prodl l) (format "''W[' l ]").

Lemma prodl_root l : root (prodl l) =i l.
Proof.
elim: l => [i|a l IH i]; rewrite /prodl /=.
  by rewrite big_nil rootE hornerE oner_eq0.
have [aIl|aNIl] := boolP (a \in l).
  by rewrite IH inE; case: eqP => [->|].
by rewrite big_cons [LHS]rootM root_XsubC inE -IH.
Qed.

Lemma prodl_size l : (size (prodl l) <= (size l).+1)%N.
Proof.
elim: l => /= [|a l IH].
 by rewrite /prodl big_nil size_polyC; case: eqP.
rewrite /prodl /=; case: (boolP (_ \in _)) => H.
  by apply: leq_trans IH _.
rewrite big_cons.
apply: leq_trans (size_mul_leq _ _) _.
by rewrite size_XsubC.
Qed.

Fixpoint interp (l : seq R) : {poly R} :=
  if l is a :: l1 then
      let r := interp l1 in
      if a \in l1 then r else
        let q := prodl l1 in
        r + (f a - r.[a]) / q.[a] *: q
  else 0.

Lemma interp_nil : interp [::] = 0.
Proof. by []. Qed.

Lemma interpC a : interp [:: a] = (f a)%:P.
Proof. 
by rewrite /= [prodl _]big_nil !hornerC !rm0 divr1 alg_polyC.
Qed.

Lemma interp_cons a l :
  a \notin l -> 
  interp (a :: l) =
     interp l + (f a - (interp l).[a])/(prodl l).[a] *: prodl l.
Proof. by move=> /= /negPf->. Qed.

Lemma horner_interp l : all (fun i => (interp l).[i] == f i) l.
Proof.
elim: l => //= a l IH.
have [aIl|aNIl] := boolP (_ \in _).
  by rewrite IH (allP IH).
rewrite !hornerE divfK; last first.
  by rewrite -mem_root prodl_root.
rewrite addrC subrK eqxx /=.
apply/allP=> b bIl.
rewrite !hornerE (eqP (allP IH _ bIl)).
rewrite (_ : _.[b] = 0) ?rm0 //.
by apply/eqP; rewrite -mem_root prodl_root.
Qed.

Lemma interp_size l : (size (interp l) <= size l)%N.
Proof.
elim: l => /= [|a l IH].
  by rewrite size_poly0.
have [aIl|aNIl] := boolP (_ \in _).
  by apply: leq_trans IH _.
Search _ (size _) (_ + _) in poly.
apply: leq_trans (size_add _ _) _.
rewrite geq_max (leq_trans IH _) // 
                (leq_trans (size_scale_leq _ _)) //.
by exact: prodl_size.
Qed.

End Interp.

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

Definition has_zeros f n a b := 
  exists l : seq R,
   [/\  uniq l,
        forall x,  x \in l ->  a < x < b /\ f x = 0 &
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
        forall x,  x \in l ->  a < x < b /\ f x = 0 &
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

Lemma has_zeros_S_lt f n a b : 
  has_zeros f n.+1 a b -> a < b.
Proof.
case; case; first by case.
move=> c l [_ /(_ c) []//]; try lra.
by rewrite inE eqxx.
Qed.

Lemma has_zeros_0 f a b : has_zeros f 0 a b.
Proof. by exists [::]; split. Qed.

Lemma has_zeros_1 f a b : 
  has_zeros f 1 a b <-> (exists x, a < x < b /\ f x = 0).
Proof.
split=> [[[|x [|y l]] //=] |]; case=> //.
  move=> _ /(_ x) []; rewrite ?inE // => H1 H2 _.
  by exists x.
move=> x [H1 H2]; exists [::x]; split=> // y.
by rewrite inE => /eqP->.
Qed.

Lemma has_zeros_add f m n a b c :
   a <= b <= c ->
   has_zeros f m a b -> has_zeros f n b c -> has_zeros f (m + n) a c.
Proof.
move=> H1 [l1 [H1l1 H2l1 H3l1]] [l2 [H1l2 H2l2 H3l2]].
exists (l1 ++ l2); split.
- rewrite cat_uniq H1l1 H1l2 andbT /=.
  apply/hasPn => x /H2l2 [HH1 _].
  apply/negP=> /H2l1 [HH2 _].
  lra.
- by move=> x; rewrite mem_cat => /orP[/H2l1[]|/H2l2[]]; lra.
by rewrite size_cat H3l1 H3l2.
Qed.

Lemma has_zeros_split f n a b :
  has_zeros f n.+1 a b -> exists c,
             [/\ a < c <= b, has_zeros f 1 a c & has_zeros f n c b].
Proof.
move=> HH.
have aLb := has_zeros_S_lt HH.
move: HH.
rewrite {1}has_zerosEs => [] [] [|x [|y k]]; case => // H1 H2 H3.
  exists b; split; try lra.
    exists [::x]; split=> //.
  by case: H3 => <-; apply: has_zeros_0.
case: (H2 x); rewrite ?inE ?eqxx => // Hx Hfx.
case: (H2 y); rewrite ?inE ?eqxx ?orbT => // Hy Hfy.
have Hxy : x < y.
  by apply/RltbP; case/andP: H1.
exists ((x + y) / 2); split; try lra.
  exists [::x]; split => // z.
  by rewrite inE => /eqP ->; lra.
apply/has_zerosEs.
exists [::y & k]; split => [|z Hz|] //=; first 2 last.
- by move: H3 => /= [].
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
case/has_zeros_split => c [H1c /has_zeros_1 [a1 [Ha1 Ra1]]].
case/has_zeros_split => d [H1d /has_zeros_1 [a2 [Ha2 Ra2]]] H1.
have F1 x : a1 < x < a2 -> derivable_pt f x.
  move=> HH; apply: ex_derive_Reals_0.
  by apply: Hd; lra.
have F2 x : a1 <= x <= a2 -> continuity_pt f x.
  by move=> HH; apply: Hc; lra.
have [||x [P HP]] := Rolle f a1 a2 F1 F2; try lra.
pose u := (x + a2) / 2.
have F3 : has_zeros (Derive f) 1 a u.
  rewrite /u.
  apply/has_zeros_1; exists x; split => //; try lra.
  by rewrite Derive_Reals in HP.
have F4 : has_zeros f 1 u d.
  rewrite /u.
  apply/has_zeros_1; exists a2; split => //; try lra.
have F5 : has_zeros (Derive f) n u b.
  rewrite /u.
  apply: IH => [y Hy|y Hy|].
  - by apply: Hd; lra.
  - by apply: Hc; lra.
  apply: (has_zeros_add _ F4 _) => //.
  by rewrite /u; lra.
rewrite -[n.+1]/(1 + n)%nat.
apply: has_zeros_add F5 => //.
by rewrite /u; lra.
Qed.
