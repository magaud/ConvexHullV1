(* ======================= *)
(* ===== CH03_init.v ===== *)
(* ======================= *)

Require Export CH02_def.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Fixpoint linkless (m:fmap) {struct m} : Prop :=
  match m with
    V => True
  | I m0 _ _ _ => linkless m0
  | L _ _ _ _ => False
  end.

Definition inv_poly (m:fmap) : Prop :=
  forall (d:dart), exd m d ->
  black_dart m d \/ blue_dart m d \/ red_dart m d.

Definition well_emb (m:fmap) : Prop :=
  forall (da:dart), exd m da ->
  (succ m zero da -> (fpoint m da) <> (fpoint m (A m zero da))) /\
  (pred m zero da -> (fpoint m da) <> (fpoint m (A_1 m zero da))) /\
  (succ m one da -> (fpoint m da) = (fpoint m (A m one da))) /\
  (pred m one da -> (fpoint m da) = (fpoint m (A_1 m one da))) /\
  (forall db:dart, exd m db -> db <> da -> db <> (A m one da) ->
   db <> (A_1 m one da) -> (fpoint m da) <> (fpoint m db)).

Definition noalign (m:fmap) : Prop :=
  forall (d1:dart)(d2:dart)(d3:dart),
  exd m d1 -> exd m d2 -> exd m d3 ->
  (fpoint m d1) <> (fpoint m d2) ->
  (fpoint m d1) <> (fpoint m d3) ->
  (fpoint m d2) <> (fpoint m d3) ->
  ~ align (fpoint m d1) (fpoint m d2) (fpoint m d3).

Definition convex (m:fmap) : Prop :=
  forall (x:dart), exd m x -> blue_dart m x ->
  forall (y:dart), exd m y -> 
  (fpoint m y) <> (fpoint m x) -> (fpoint m y) <> (fpoint m (A m zero x)) ->
  ccw (fpoint m x) (fpoint m (A m zero x)) (fpoint m y).

Definition prec_CH (m:fmap) : Prop :=
  inv_hmap m /\ linkless m /\ well_emb m /\ noalign m.

(* ========================= *)

Definition inv_noalign_point (m:fmap)(p:point) : Prop :=
  forall (d1:dart)(d2:dart),
  exd m d1 -> exd m d2 -> (fpoint m d1) <> (fpoint m d2) ->
  ~ align (fpoint m d1) (fpoint m d2) p.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma not_or_and_not : forall A B : Prop,
  ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
tauto.
Qed.

Ltac rewritenotorandnot H H1 H2 :=
let Hf := fresh in assert (Hf := not_or_and_not _  _ H); clear H; destruct Hf as [H1 H2].

Lemma or_not_not_and : forall A B : Prop,
  ~ A \/ ~ B -> ~ (A /\ B).
Proof.
simple induction 1; red in |- *; simple induction 2; auto.
Qed.

Lemma and_not_not_or : forall A B : Prop,
  ~ A /\ ~ B -> ~ (A \/ B).
Proof.
tauto.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma neq_sym : forall (x:dart)(y:dart),
  (x <> y) -> (y <> x).
Proof.
intros x y.
auto with arith.
Qed.

Lemma not_neq_eq : forall (x:dart)(y:dart),
  ~ (x <> y) -> x = y.
Proof.
intros x y.
elim (eq_dart_dec x y).
 trivial.
 tauto.
Qed.

Lemma eq_not_neq : forall (x:dart)(y:dart),
  x = y -> ~ (x <> y).
Proof.
intros x y H.
subst x; tauto.
Qed.

Lemma neq_not_not_neq : forall (x:dart)(y:dart),
  x <> y -> ~ ~ (x <> y).
Proof.
intros x y H.
tauto.
Qed.

Lemma neq_le_trans : forall (x:dart)(y:dart),
  x <> nil -> x <= y -> y <> nil.
Proof.
intros x y H1 H2.
unfold nil in *.
apply (neq_sym 0 y).
apply (lt_O_neq y).
generalize (lt_le_trans 0 x y).
generalize (neq_O_lt x).
generalize (neq_sym x 0).
tauto.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Ltac elimeqdartdec := repeat
  let H := fresh in
  match goal with
  | [ |- context [(if (eq_dart_dec ?d ?d) then ?A else ?B)]] =>
    elim (eq_dart_dec d d); [intro H; clear H | tauto]
  | [_:?d1<>?d2 |- context [(if (eq_dart_dec ?d1 ?d2) then ?A else ?B)]] =>
    elim (eq_dart_dec d1 d2); [contradiction | intro H; clear H]
  | [H0:?d1<>?d2 |- context [(if (eq_dart_dec ?d2 ?d1) then ?A else ?B)]] =>
    elim (eq_dart_dec d2 d1); [intro H; apply neq_sym in H0; contradiction | intro H; clear H]
  end.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma exd_not_exd_neq :
  forall (m:fmap)(x:dart)(y:dart),
  exd m x -> ~ exd m y -> x <> y.
Proof.
induction m.
 (* Cas 1 : m = V *)
 simpl; tauto.
 (* Cas 2 : m = I *)
 intros x y H1 H2.
 simpl in *.
 elim H1; clear H1.
  intro H1; subst x.
  unfold not in *; tauto.
  intro H1; apply IHm; [exact H1 | tauto].
 (* Cas 3 : m = L *)
 intros x y H1 H2.
 simpl in *.
 apply IHm; [exact H1 | exact H2].
Qed.

(* ========================== *)

Lemma exd_le_max_dart :
  forall (m:fmap)(x:dart),
  exd m x -> x <= max_dart m.
Proof.
induction m.
 (* Cas 1 : m = V *)
 simpl; tauto.
 (* Cas 2 : m = I *)
 intros x Hexd.
 simpl in *.
 elim (le_lt_dec d (max_dart m)).
  elim Hexd; clear Hexd.
   intros; subst x; tauto.
   intros; apply IHm; assumption.
  elim Hexd; clear Hexd.
   intros; subst x; lia.
   intros Hexd Hmax.
   assert (x <= max_dart m);
   [apply IHm; assumption | lia].
 (* Cas 3 : m = L *)
 intros x Hexd.
 simpl in *.
 apply IHm; assumption.
Qed.

Lemma gt_max_dart_not_exd :
  forall (m:fmap)(x:dart),
  max_dart m < x -> ~ exd m x.
Proof.
induction m.
 (* Cas 1 : m = V *)
 simpl; tauto.
 (* Cas 2 : m = I *)
 intro x; simpl in *.
 elim (le_lt_dec d (max_dart m)).
  intros H1 H2.
  unfold not; intro Hfs.
  elim Hfs; clear Hfs.
  intro H; subst x; intuition.
  intro H; generalize (IHm x H2);
  clear IHm; contradiction.
  intros H1 H2.
  unfold not; intro Hfs.
  elim Hfs; clear Hfs.
  intro H; subst x; intuition.
  intro H; generalize (IHm x);
  clear IHm; intuition.
 (* Cas 3 : m = L *)
 intros x; simpl in *.
 apply IHm; assumption.
Qed.

(* ========================== *)

Lemma not_exd_black :
  forall (m:fmap)(x:dart),
  inv_hmap m -> ~ exd m x -> black_dart m x.
Proof.
intros m x Hinv Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl in *.
 unfold black_dart, succ, pred; simpl; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 unfold black_dart, succ, pred in *; simpl.
 apply IHm; tauto.
 (* Cas 3 : m = L *)
 induction d; simpl in *.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 generalize (IHm Hinv Hexd); clear IHm; intro IHm.
 unfold black_dart, succ, pred in *; simpl.
 elim (eq_dart_dec d0 x).
  intro H0; subst d0; contradiction.
 elim (eq_dart_dec d1 x).
  intro H0; subst d1; contradiction.
 intros H6 H7; assumption.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 generalize (IHm Hinv Hexd); clear IHm; intro IHm.
 unfold black_dart, succ, pred in *; simpl.
 elim (eq_dart_dec d0 x).
  intro H0; subst d0; contradiction.
 elim (eq_dart_dec d1 x).
  intro H0; subst d1; contradiction.
 intros H6 H7; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma A_A_1 :
  forall (m:fmap)(k:dim)(d:dart),
  inv_hmap m -> exd m d -> exd m (A_1 m k d) ->
  d = A m k (A_1 m k d).
Proof.
intros m k d Hinv Hexd1 Hexd2.
rewrite (Jordan1.A_A_1 m k d); trivial.
unfold pred; simpl.
apply exd_not_nil with m; assumption.
Qed.

Lemma A_1_A :
  forall (m:fmap)(k:dim)(d:dart),
  inv_hmap m -> exd m d -> exd m (A m k d) ->
  d = A_1 m k (A m k d).
Proof.
intros m k d Hinv Hexd1 Hexd2.
rewrite (Jordan1.A_1_A m k d); trivial.
unfold succ; simpl.
apply exd_not_nil with m; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma fixpoint_cA : forall (m:fmap)(k:dim)(d:dart),
  inv_hmap m -> exd m d -> ~ succ m k d -> ~ pred m k d -> cA m k d = d.
Proof.
intros m k d Hmap Hexd Hsucc Hpred.
generalize (fixpt_cA_cA_1 m k d Hmap Hexd Hsucc Hpred); intuition.
Qed.

Lemma fixpoint_cA_1 : forall (m:fmap)(k:dim)(d:dart),
  inv_hmap m -> exd m d -> ~ succ m k d -> ~ pred m k d -> cA_1 m k d = d.
Proof.
intros m k d Hmap Hexd Hsucc Hpred.
generalize (fixpt_cA_cA_1 m k d Hmap Hexd Hsucc Hpred); intuition.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma linkless_A_nil :
  forall (m:fmap)(k:dim)(d:dart),
  linkless m -> A m k d = nil.
Proof.
intros m k d; induction m; simpl; tauto.
Qed.

Lemma linkless_A_1_nil :
  forall (m:fmap)(k:dim)(d:dart),
  linkless m -> A_1 m k d = nil.
Proof.
intros m k d; induction m; simpl; tauto.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma black_not_blue :
  forall (m:fmap)(d:dart),
  black_dart m d -> ~ blue_dart m d.
Proof.
intros m d; unfold black_dart, blue_dart; tauto.
Qed.

Lemma black_not_red :
  forall (m:fmap)(d:dart),
  black_dart m d -> ~ red_dart m d.
Proof.
intros m d; unfold black_dart, red_dart; tauto.
Qed.

Lemma blue_not_black :
  forall (m:fmap)(d:dart),
  blue_dart m d -> ~ black_dart m d.
Proof.
intros m d.
unfold blue_dart, black_dart; tauto.
Qed.

Lemma blue_not_red :
  forall (m:fmap)(d:dart),
  blue_dart m d -> ~ red_dart m d.
Proof.
intros m d.
unfold blue_dart, red_dart; tauto.
Qed.

Lemma red_not_black :
  forall (m:fmap)(d:dart),
  red_dart m d -> ~ black_dart m d.
Proof.
intros m d; unfold red_dart, black_dart; tauto.
Qed.

Lemma red_not_blue :
  forall (m:fmap)(d:dart),
  red_dart m d -> ~ blue_dart m d.
Proof.
intros m d; unfold red_dart, blue_dart; tauto.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Lemma succ_zero_blue_dart :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  succ m zero d -> blue_dart m d.
Proof.
intros m d Hmap Hpoly Hsucc.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
assert (H1 : exd m d).
apply (succ_exd m zero d); tauto.
generalize (Hpoly d H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 repeat split; assumption.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
Qed.

Lemma pred_one_blue_dart :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  pred m one d -> blue_dart m d.
Proof.
intros m d Hmap Hpoly Hsucc.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
assert (H1 : exd m d).
apply (pred_exd m one d); tauto.
generalize (Hpoly d H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 repeat split; assumption.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
Qed.

Lemma succ_one_red_dart :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  succ m one d -> red_dart m d.
Proof.
intros m d Hmap Hpoly Hsucc.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
assert (H1 : exd m d).
apply (succ_exd m one d); tauto.
generalize (Hpoly d H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 repeat split; assumption.
Qed.

Lemma pred_zero_red_dart :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  pred m zero d -> red_dart m d.
Proof.
intros m d Hmap Hpoly Hsucc.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
assert (H1 : exd m d).
apply (pred_exd m zero d); tauto.
generalize (Hpoly d H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
elim H2; clear H2; intro H2.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 contradiction.
 destruct H2 as [H2a [H2b [H2c H2d]]].
 repeat split; assumption.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma blue_A_red :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  blue_dart m d -> red_dart m (A m zero d).
Proof.
intros m d Hqh Hpoly Hblue.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
destruct Hblue as [Hb1 [Hb2 [Hb3 Hb4]]].
assert (H1 : exd m (A m zero d)).
apply succ_exd_A; tauto.
generalize (Hpoly (A m zero d) H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A_1 m zero (A m zero d))).
 apply (A_1_A m zero d); try (assumption||trivial).
 apply (succ_exd m zero d); assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (succ_exd m zero d); try assumption.
 tauto.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A_1 m zero (A m zero d))).
 apply (A_1_A m zero d); try (assumption||trivial).
 apply (succ_exd m zero d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (succ_exd m zero d); try assumption.
 tauto.
assumption.
Qed.

Lemma blue_A_1_red :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  blue_dart m d -> red_dart m (A_1 m one d).
Proof.
intros m d Hqh Hpoly Hblue.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
destruct Hblue as [Hb1 [Hb2 [Hb3 Hb4]]].
assert (H1 : exd m (A_1 m one d)).
apply pred_exd_A_1; tauto.
generalize (Hpoly (A_1 m one d) H1); intro H2; clear Hpoly.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A m one (A_1 m one d))).
 apply (A_A_1 m one d); try (assumption||trivial).
 apply (pred_exd m one d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (pred_exd m one d); try assumption.
 tauto.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A m one (A_1 m one d))).
 apply (A_A_1 m one d); try (assumption||trivial).
 apply (pred_exd m one d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (pred_exd m one d); try assumption.
 tauto.
assumption.
Qed.

Lemma red_A_blue :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  red_dart m d -> blue_dart m (A m one d).
Proof.
intros m d Hqh Hpoly Hred.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
destruct Hred as [Hr1 [Hr2 [Hr3 Hr4]]].
assert (H1 : exd m (A m one d)).
apply succ_exd_A; tauto.
generalize (Hpoly (A m one d) H1); clear Hpoly; intro H2.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A_1 m one (A m one d))).
 apply (A_1_A m one d); try (assumption||trivial).
 apply (succ_exd m one d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (succ_exd m one d); try assumption.
 tauto.
elim H2; clear H2; intro H2.
 assumption.
 assert (H3 : d = (A_1 m one (A m one d))).
 apply (A_1_A m one d); try (assumption||trivial).
 apply (succ_exd m one d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (succ_exd m one d); try assumption.
 tauto.
Qed.

Lemma red_A_1_blue :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_poly m ->
  red_dart m d -> blue_dart m (A_1 m zero d).
Proof.
intros m d Hqh Hpoly Hred.
unfold inv_poly in *.
unfold black_dart, blue_dart, red_dart in *.
unfold succ, pred in *; simpl in *.
destruct Hred as [Hr1 [Hr2 [Hr3 Hr4]]].
assert (H1 : exd m (A_1 m zero d)).
apply pred_exd_A_1; tauto.
generalize (Hpoly (A_1 m zero d) H1); clear Hpoly; intro H2.
elim H2; clear H2; intro H2.
 assert (H3 : d = (A m zero (A_1 m zero d))).
 apply (A_A_1 m zero d); try (assumption||trivial).
 apply (pred_exd m zero d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (pred_exd m zero d); try assumption.
 tauto.
elim H2; clear H2; intro H2.
 assumption.
 assert (H3 : d = (A m zero (A_1 m zero d))).
 apply (A_A_1 m zero d); try (assumption||trivial).
 apply (pred_exd m zero d); try assumption.
 rewrite <- H3 in H2.
 assert (H4 : d <> nil).
 apply (exd_not_nil m d); try assumption.
 apply (pred_exd m zero d); try assumption.
 tauto.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Lemma invisible_A_invisible : 
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> invisible m d p ->
  invisible m (A m zero d) p.
Proof.
intros m d p Hmap Hpoly Hexd Hblue.
unfold invisible.
elim blue_dart_dec; intros Hb1 Hccw1.
 elim blue_dart_dec; intros Hb2.
  apply blue_A_red in Hblue; try assumption.
  apply red_not_blue in Hblue; intuition.
  rewrite <- A_1_A; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in Hblue; tauto.
 contradiction.
Qed.

Lemma invisible_A_1_invisible : 
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> invisible m d p ->
  invisible m (A_1 m zero d) p.
Proof.
intros m d p Hmap Hpoly Hexd Hred.
unfold invisible.
elim blue_dart_dec; intros Hb1 Hccw1.
 apply red_not_blue in Hred; intuition.
 elim blue_dart_dec; intros Hb2.
  rewrite <- A_A_1; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold red_dart in Hred; tauto.
  apply red_A_1_blue in Hred; intuition.
Qed.

Lemma visible_A_visible : 
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> visible m d p ->
  visible m (A m zero d) p.
Proof.
intros m d p Hmap Hpoly Hexd Hblue.
unfold visible.
elim blue_dart_dec; intros Hb1 Hccw1.
 elim blue_dart_dec; intros Hb2.
  apply blue_A_red in Hblue; try assumption.
  apply red_not_blue in Hblue; intuition.
  rewrite <- A_1_A; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in Hblue; tauto.
 contradiction.
Qed.

Lemma visible_A_1_visible : 
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> visible m d p ->
  visible m (A_1 m zero d) p.
Proof.
intros m d p Hmap Hpoly Hexd Hred.
unfold visible.
elim blue_dart_dec; intros Hb1 Hccw1.
 apply red_not_blue in Hred; intuition.
 elim blue_dart_dec; intros Hb2.
  rewrite <- A_A_1; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold red_dart in Hred; tauto.
  apply red_A_1_blue in Hred; intuition.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Lemma inv_poly_not_fixpoint :
  forall (m:fmap)(k:dim)(d:dart),
  inv_hmap m -> inv_poly m -> exd m d ->
  (d <> A m k d) /\ (d <> A_1 m k d).
Proof.
intros m k d Hqh Hpoly Hexd.
generalize Hpoly; intro H0.
unfold inv_poly in H0.
generalize (H0 d Hexd); clear H0; intro H0.
elim H0; clear H0; intro H0.
 unfold black_dart, succ, pred in *.
 destruct H0 as [H1 [H2 [H3 H4]]].
 induction k.
 apply not_neq_eq in H1; rewrite H1.
 apply not_neq_eq in H3; rewrite H3.
 apply (exd_not_nil m d Hqh) in Hexd.
 split; assumption.
 apply not_neq_eq in H2; rewrite H2.
 apply not_neq_eq in H4; rewrite H4.
 apply (exd_not_nil m d Hqh) in Hexd.
 split; assumption.
elim H0; clear H0; intro H0.
 generalize (blue_A_red m d Hqh Hpoly H0); intro HA.
 generalize (blue_A_1_red m d Hqh Hpoly H0); intro HA1.
 unfold blue_dart, red_dart, succ, pred in *.
 destruct H0 as [H1 [H2 [H3 H4]]].
 induction k; split.
 elim (eq_dart_dec d (A m zero d)); [idtac|trivial].
  intro Heq; rewrite <- Heq in *; tauto.
 apply not_neq_eq in H3; rewrite H3.
 apply (exd_not_nil m d); try assumption.
 apply not_neq_eq in H2; rewrite H2.
 apply (exd_not_nil m d); try assumption.
 elim (eq_dart_dec d (A_1 m one d)); [idtac|trivial].
  intro Heq; rewrite <- Heq in *; tauto.
 generalize (red_A_blue m d Hqh Hpoly H0); intro HA.
 generalize (red_A_1_blue m d Hqh Hpoly H0); intro HA1.
 unfold blue_dart, red_dart, succ, pred in *.
 destruct H0 as [H1 [H2 [H3 H4]]].
 induction k; split.
 apply not_neq_eq in H1; rewrite H1.
 apply (exd_not_nil m d); try assumption.
 elim (eq_dart_dec d (A_1 m zero d)); [idtac|trivial].
  intro Heq; rewrite <- Heq in *; tauto.
 elim (eq_dart_dec d (A m one d)); [idtac|trivial].
  intro Heq; rewrite <- Heq in *; tauto.
 apply not_neq_eq in H4; rewrite H4.
 apply (exd_not_nil m d); try assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma eq_point_eq :
  forall (p:point)(q:point),
  (eq_point p q) <-> (p = q).
Proof.
intros p q.
unfold eq_point; split.
induction p; induction q.
simpl; intros [H1 H2].
subst a b; trivial.
intro H1; subst p.
tauto.
Qed.

Lemma eq_point_dec_2 :
  forall (p:point)(q:point),
  {p = q} + {p <> q}.
Proof.
intros p q.
generalize (eq_point_eq p q).
intro H; destruct H as [H1 H2].
elim (eq_point_dec p q).
intro H; left; tauto.
intro H; right; tauto.
Qed.

Lemma neq_sym_point :
  forall (p:point)(q:point),
  (p <> q) -> (q <> p).
Proof.
intros p q.
auto with arith.
Qed.

(*
Lemma not_exd_fpoint_zero :
  forall (m:fmap)(d:dart),
  ~ exd m d -> fpoint m d = (0%R, 0%R).
Proof.
induction m.
 simpl; tauto.
 intros x Hexd.
 simpl in *.
 rewritenotorandnot Hexd Hexd1 Hexd2.
 elim (eq_dart_dec d x); intro Heq.
  subst d; tauto.
  apply IHm; assumption.
 intros x Hexd.
 simpl in *.
 apply IHm; tauto.
Qed.
*)

(* ========================= *)

Lemma ccw_neq_point :
  forall (A:point)(B:point)(C:point),
  ccw A B C -> A <> B.
Proof.
intros A B C H.
elim (eq_point_dec_2 A B).
 intro Heq; subst B; unfold ccw in H.
 cut (det A A C = 0%R).
 intro H0; rewrite H0 in H.
 apply Rgt_not_eq in H; intuition.
 unfold det; ring.
 trivial.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

(*
Lemma inv_hmap_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> inv_hmap m.
Proof.
intros m d t p.
simpl; tauto.
Qed.

Lemma inv_hmap_L :
  forall (m:fmap)(k:dim)(da:dart)(db:dart),
  inv_hmap (L m k da db) -> inv_hmap m.
Proof.
intros m d t p.
simpl; tauto.
Qed.
*)

Lemma well_emb_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> well_emb (I m d t p) -> well_emb m.
Proof.
intros m d t p Hqh.
unfold well_emb; simpl in *;
destruct Hqh as [Hqh [Hqh1 Hqh2]].
intros Hemb da Hda; repeat split.
intro Hsucc.
assert (H0 : d = da \/ exd m da); [tauto|idtac].
generalize (Hemb da H0); clear H0.
intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]].
assert (H0 : succ (I m d t p) zero da); [tauto|idtac].
generalize (Hw1 H0); clear H0 Hw1 Hw2 Hw3 Hw4 Hw5.
elim (eq_dart_dec d da).
 intro Heq; subst da; contradiction.
 elim (eq_dart_dec d (A m zero da)); trivial.
  apply succ_exd_A in Hsucc; try assumption.
  intro Heq; subst d; contradiction.
intro Hpred.
assert (H0 : d = da \/ exd m da); [tauto|idtac].
generalize (Hemb da H0); clear H0.
intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]].
assert (H0 : pred (I m d t p) zero da); [tauto|idtac].
generalize (Hw2 H0); clear H0 Hw1 Hw2 Hw3 Hw4 Hw5.
elim (eq_dart_dec d da).
 intro Heq; subst da; contradiction.
 elim (eq_dart_dec d (A_1 m zero da)); trivial.
  apply pred_exd_A_1 in Hpred; try assumption.
  intro Heq; subst d; contradiction.
intro Hsucc.
assert (H0 : d = da \/ exd m da); [tauto|idtac].
generalize (Hemb da H0); clear H0.
intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]].
assert (H0 : succ (I m d t p) one da); [tauto|idtac].
generalize (Hw3 H0); clear H0 Hw1 Hw2 Hw3 Hw4 Hw5.
elim (eq_dart_dec d da).
 intro Heq; subst da; contradiction.
 elim (eq_dart_dec d (A m one da)); trivial.
  apply succ_exd_A in Hsucc; try assumption.
  intro Heq; subst d; contradiction.
intro Hpred.
assert (H0 : d = da \/ exd m da); [tauto|idtac].
generalize (Hemb da H0); clear H0.
intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]].
assert (H0 : pred (I m d t p) one da); [tauto|idtac].
generalize (Hw4 H0); clear H0 Hw1 Hw2 Hw3 Hw4 Hw5.
elim (eq_dart_dec d da).
 intro Heq; subst da; contradiction.
 elim (eq_dart_dec d (A_1 m one da)); trivial.
  apply pred_exd_A_1 in Hpred; try assumption.
  intro Heq; subst d; contradiction.
intros db Hdb Hp1 Hp2 Hp3.
assert (H0 : d = da \/ exd m da); [tauto|idtac].
generalize (Hemb da H0); clear H0.
intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]].
assert (H0 : d = db \/ exd m db); [tauto|idtac].
generalize (Hw5 db H0 Hp1 Hp2 Hp3); clear H0 Hw1 Hw2 Hw3 Hw4 Hw5.
elim (eq_dart_dec d da).
 intro Heq; subst da; contradiction.
 elim (eq_dart_dec d db); trivial.
  intro Heq; subst db; contradiction.
Qed.

Lemma convex_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> convex (I m d t p) -> convex m.
Proof.
intros m d t p Hqh Hconv.
simpl in Hqh; destruct Hqh as [Hqh [Hqh1 Hqh2]].
unfold convex in *.
intros da Ha1 Ha2 db Hb1 Hb2 Hb3.
simpl in *.
assert (H1 : d = da \/ exd m da).
right; assumption.
assert (H2 : blue_dart (I m d t p) da).
unfold blue_dart, succ, pred in *; simpl in *; assumption.
assert (H3 : d = db \/ exd m db).
right; assumption.
generalize (Hconv da H1 H2 db H3); clear Hconv H1 H2 H3.
elim (eq_dart_dec d da).
intro H; subst d; contradiction.
elim (eq_dart_dec d db).
intro H; subst d; contradiction.
elim (eq_dart_dec d (A m zero da)).
intro H; subst d.
unfold not in Hqh2; elim Hqh2.
apply (succ_exd_A m zero da); unfold succ; assumption.
tauto.
Qed.

Lemma noalign_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> noalign (I m d t p) -> noalign m.
Proof.
intros m d t p Hqh.
unfold noalign; simpl in *;
destruct Hqh as [Hqh [Hqh1 Hqh2]].
intros H d1 d2 d3 H1 H2 H3.
generalize (H d1 d2 d3); clear H.
elim (eq_dart_dec d d1).
intro Heq; subst d; contradiction.
elim (eq_dart_dec d d2).
intro Heq; subst d; contradiction.
elim (eq_dart_dec d d3).
intro Heq; subst d; contradiction.
intuition.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma well_emb_A_zero :
  forall (m:fmap)(d:dart),
  inv_hmap m -> well_emb m -> exd m d -> succ m zero d ->
  fpoint m d <> fpoint m (A m zero d).
Proof.
intros m da Hqh Hemb Hexd1 Hsucc.
generalize (Hemb da Hexd1); intuition.
Qed.

Lemma well_emb_A_one :
  forall (m:fmap)(d:dart),
  inv_hmap m -> well_emb m -> exd m d -> succ m one d ->
  fpoint m d = fpoint m (A m one d).
Proof.
intros m da Hqh Hemb Hexd1 Hsucc.
generalize (Hemb da Hexd1); intuition.
Qed.

Lemma well_emb_A_1_zero :
  forall (m:fmap)(d:dart),
  inv_hmap m -> well_emb m -> exd m d -> pred m zero d ->
  fpoint m d <> fpoint m (A_1 m zero d).
Proof.
intros m da Hqh Hemb Hexd1 Hpred.
generalize (Hemb da Hexd1); intuition.
Qed.

Lemma well_emb_A_1_one :
  forall (m:fmap)(d:dart),
  inv_hmap m -> well_emb m -> exd m d -> pred m one d ->
  fpoint m d = fpoint m (A_1 m one d).
Proof.
intros m da Hqh Hemb Hexd1 Hpred.
generalize (Hemb da Hexd1); intuition.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma max_dart_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  x < max -> max_dart m < max -> max_dart (CHID m mr x tx px max) <= max.
Proof.
intros m mr x tx px max Hmax1 Hmax2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *.
 elim (le_lt_dec x 0).
  intro H; lia.
  intro H; lia.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
    intros H_left H_ccw H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
     intros H_right H_ccw H_red H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
   intros H_red H_blue.
simpl; generalize Hmax2; clear Hmax2.
repeat elim le_lt_dec; intuition.
 (* Cas 3 : m = L *)
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm; assumption.
   intros H_ccw.
simpl in *; apply IHm; assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm; assumption.
   elim invisible_dec.
    intros Hccw1 Hccw2.
simpl in *; apply IHm; assumption.
    intros Hccw1 Hccw2.
simpl in *; apply IHm; assumption.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma not_exd_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  ~ exd m d -> d <> x -> d <> max -> ~ exd (CHID m mr x tx px max) d.
Proof.
induction m.
 (* Cas 1 : m = V *)
 intros mr x tx px max y Hexd Hneq1 Hneq2.
 simpl in *.
 unfold not; intro Hfs.
 elim Hfs; clear Hfs.
 intro H; apply sym_eq in H; contradiction.
 intro H; trivial.
 (* Cas 2 : m = I *)
 intros mr x tx px max y Hexd Hneq1 Hneq2.
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros Hccw Hblue.
   simpl in *.
   unfold not; intro Hfs.
   elim Hfs; clear Hfs.
   intro H; subst y; intuition.
   intro H; generalize (IHm mr x tx px max y);
   clear IHm; intuition.
   elim left_dart_dec.
    intros Hleft Hccw Hblue.
    simpl in *.
    unfold not; intro Hfs.
    elim Hfs; clear Hfs.
    intro H; apply sym_eq in H; contradiction.
    intro Hfs; elim Hfs; clear Hfs.
    intro H; subst y; intuition.
    intro H; generalize (IHm mr x tx px max y);
    clear IHm; intuition.
    intros Hleft Hccw Hblue.
    simpl in *.
    unfold not; intro Hfs.
    elim Hfs; clear Hfs.
    intro H; subst y; intuition.
    intro H; generalize (IHm mr x tx px max y);
    clear IHm; intuition.
  elim red_dart_dec.
   elim invisible_dec.
    intros Hccw Hred Hblue.
    simpl in *.
    unfold not; intro Hfs.
    elim Hfs; clear Hfs.
    intro H; subst y; intuition.
    intro H; generalize (IHm mr x tx px max y);
    clear IHm; intuition.
    elim right_dart_dec.
     intros Hright Hccw Hred Hblue.
     simpl in *.
     unfold not; intro Hfs.
     elim Hfs; clear Hfs.
     intro H; subst y; intuition.
     intro H; generalize (IHm mr x tx px max y);
     clear IHm; intuition.
     intros Hright Hccw Hred Hblue.
     apply IHm; tauto.
   intros Hred Hblue.
   simpl in *.
   unfold not; intro Hfs.
   elim Hfs; clear Hfs.
   intro H; subst y; intuition.
   intro H; generalize (IHm mr x tx px max y);
   clear IHm; intuition.
 (* Cas 3 : m = L *)
 intros mr x tx px max y Hexd Hneq1 Hneq2.
 case d; simpl in *.
  elim ccw_dec.
   intros Hccw; simpl; apply IHm; assumption.
   intros Hccw; simpl; apply IHm; assumption.
  elim invisible_dec.
   intros Hccw; simpl; apply IHm; assumption.
   elim invisible_dec.
    intros Hccw1 Hccw2; simpl; apply IHm; assumption.
    intros Hccw1 Hccw2; simpl; apply IHm; assumption.
Qed.

Lemma exd_CHID_exd_m_or_x_or_max :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  exd (CHID m mr x tx px max) d -> exd m d \/ d = x \/ d = max.
Proof.
intros m mr x tx px max d.
induction m.
 (* Cas 1 : m = V *)
 simpl in *.
 intro H; elim H; clear H; intro H.
  apply sym_eq in H; right; left; assumption.
  left; assumption.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [apply sym_eq in Hexd; tauto | idtac].
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
    intros H_left H_ccw H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
     intros H_right H_ccw H_red H_blue.
simpl in *; intro Hexd.
generalize (IHm Hexd); intro H.
elim H; clear H; intro H; [tauto|idtac].
elim H; clear H; intro H; [tauto|tauto].
   intros H_red H_blue.
simpl in *; intro Hexd.
elim Hexd; clear Hexd; intro Hexd; [tauto|idtac].
 generalize (IHm Hexd); intro H.
 elim H; clear H; intro H; [tauto|idtac].
 elim H; clear H; intro H; [tauto|tauto].
 (* Cas 3 : m = L *)
 induction d0; simpl in *.
  elim ccw_dec.
   intros H_ccw.
simpl; apply IHm; assumption.
   intros H_ccw.
simpl; apply IHm; assumption.
  elim invisible_dec.
   intros H_ccw.
simpl; apply IHm; assumption.
   elim invisible_dec.
    intros Hccw1 Hccw2.
simpl; apply IHm; assumption.
    intros Hccw1 Hccw2.
simpl; apply IHm; assumption.
Qed.

Lemma exd_CHID_neq_x_neq_max_exd_m :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  exd (CHID m mr x tx px max) d -> d <> x -> d <> max -> exd m d.
Proof.
intros m mr x tx px max y H1 H2 H3.
apply exd_CHID_exd_m_or_x_or_max in H1.
elim H1; clear H1; intro H1; try assumption.
elim H1; clear H1; intro H1; contradiction.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma not_exd_m1_not_exd_m2_lt_max_not_exd_CHI :
  forall (m1:fmap)(m2:fmap)(max:dart)(x:dart),
  ~ exd m1 x -> ~ exd m2 x -> x < max -> ~ exd (CHI m1 m2 max) x.
Proof.
intro m; induction m;
intros m2 max x Hexd1 Hexd2 Hneq.
 (* Cas 1 : m = V *)
 simpl in *; assumption.
 (* Cas 2 : m = I *)
 simpl in *.
 apply (IHm (CHID m2 m2 d t p max) (max+1) x). tauto.
 apply not_exd_CHID. assumption. apply neq_sym; tauto. lia. lia.
 (* Cas 3 : m = L *)
 simpl in *; tauto.
Qed.

Lemma exd_CHI_not_exd_m2_lt_max_exd_m1 :
  forall (m1:fmap)(m2:fmap)(max:dart)(x:dart),
  exd (CHI m1 m2 max) x -> ~ exd m2 x -> x < max -> exd m1 x.
Proof.
intro m; induction m;
intros m2 max x Hexd1 Hexd2 Hmax.
 (* Cas 1 : m = V *)
 simpl in *; contradiction.
 (* Cas 2 : m = I *)
 simpl in *.
 elim (eq_dart_dec x d).
 intro H1; left; apply sym_eq; assumption.
 intro H1; right.
 assert (H2 : ~ exd (CHID m2 m2 d t p max) x).
 apply not_exd_CHID; [assumption|assumption|lia].
 assert (H3 : x < max+1). lia.
 apply (IHm (CHID m2 m2 d t p max) (max+1) x Hexd1 H2 H3).
 (* Cas 3 : m = L *)
 simpl in *; tauto.
Qed.

Lemma exd_CHI_not_exd_m1_lt_max_exd_m2 :
  forall (m1:fmap)(m2:fmap)(max:dart)(x:dart),
  exd (CHI m1 m2 max) x -> ~ exd m1 x -> x < max -> exd m2 x.
Proof.
intro m; induction m;
intros m2 max x Hexd1 Hexd2 Hmax.
 (* Cas 1 : m = V *)
 simpl in *; assumption.
 (* Cas 2 : m = I *)
 simpl in *.
 rewritenotorandnot Hexd2 Hneq Hexd2.
 assert (H : x < max+1). lia.
 generalize (IHm (CHID m2 m2 d t p max) (max+1) x Hexd1 Hexd2 H);
 clear H; intro H.
 apply (exd_CHID_neq_x_neq_max_exd_m m2 m2 d t p max x H (neq_sym d x Hneq)); lia.
 (* Cas 3 : m = L *)
 simpl in *; tauto.
Qed.

Lemma exd_CHI_not_exd_m1_not_exd_m2_ge_max :
  forall (m1:fmap)(m2:fmap)(max:dart)(x:dart),
  exd (CHI m1 m2 max) x -> ~ exd m1 x -> ~ exd m2 x -> max <= x.
Proof.
intro m; induction m;
intros m2 max x Hexd1 Hexd2 Hneq.
 (* Cas 1 : m = V *)
 simpl in *; contradiction.
 (* Cas 2 : m = I *)
 simpl in *.
 elim (eq_dart_dec max x); intro H1.
  subst max; lia.
  cut (max+1 <= x).
  intro H2; lia.
  apply (IHm (CHID m2 m2 d t p max) (max+1) x).
  assumption.
  tauto.
  apply not_exd_CHID. assumption. apply neq_sym; tauto. lia.
 (* Cas 3 : m = L *)
 simpl in *; tauto.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Ltac firstif_aux x :=
 match x with
  | context firstif_aux [ (if (eq_dim_dec ?k ?d) then ?A else ?B) ] => elim (eq_dim_dec k d)
  | context firstif_aux [ (if (eq_dart_dec ?x ?y) then ?A else ?B) ] => elim (eq_dart_dec x y)
  | context firstif_aux [ (if (invisible_dec ?a ?b ?c) then ?A else ?B) ] => elim (invisible_dec a b c)
  | context firstif_aux [ (if (black_dart_dec ?m ?d) then ?A else ?B) ] => elim (black_dart_dec m d)
  | context firstif_aux [ (if (blue_dart_dec ?m ?d) then ?A else ?B) ] => elim (blue_dart_dec m d)
  | context firstif_aux [ (if (red_dart_dec ?m ?d) then ?A else ?B) ] => elim (red_dart_dec m d)
  | context firstif_aux [ (if (left_dart_dec ?m ?p ?d) then ?A else ?B) ] => elim (left_dart_dec m p d)
  | context firstif_aux [ (if (right_dart_dec ?m ?p ?d) then ?A else ?B) ] => elim (right_dart_dec m p d)
 end.

Ltac firstif := match goal with |- ?x => firstif_aux x end.

Ltac elimdec := repeat firstif.

Ltac absumption :=
 match goal with
  | [_:?A,_:~?A |- ?C] => solve [ absurd A; assumption ]
  | [_:~(?x=?_) |- ?C] => solve [absurd (x=x); trivial ]
  | [_:~succ ?m ?k ?v|- (A ?m ?k ?v = nil) ] => solve [apply not_neq_eq; assumption]
  | [_:~pred ?m ?k ?v|- (A_1 ?m ?k ?v = nil) ] => solve [apply not_neq_eq; assumption]
 end.

Ltac easy := intros; subst; solve [ absumption | intuition ].

Ltac destructif := repeat (simpl; progress firstif; try easy).
