(* ============================ *)
(* ===== CH06_induction.v ===== *)
(* ============================ *)

Require Export CH05_left_dart_right_dart.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma black_dart_exd :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  black_dart mr d -> exd m d -> exd (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hblack Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl in Hexd; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; right; left; trivial.
 intro H; simpl; right; right; apply IHm; assumption.
    intros H_left H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
     intros H_right H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl.
 apply red_not_black in H_red; contradiction.
 intro H; simpl; apply IHm; assumption.
   intros H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
 (* Cas 3 : m = L *)
 induction d; simpl in *.
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

Lemma black_dart_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> black_dart mr d ->
  black_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hblack.
induction m.
 (* Cas 1 : m = V *)
 unfold black_dart, pred, succ in *.
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold black_dart, pred, succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 clear Hsub3 Hsub4.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold black_dart, blue_dart, pred, succ in *; simpl in *.
elim (eq_dart_dec d y).
intro H1; subst y; tauto.
elim (eq_dart_dec max y).
apply neq_sym in Hneq2; contradiction.
elim (eq_dart_dec x y).
apply neq_sym in Hneq1; contradiction.
intros H1 H2 H3; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold black_dart, red_dart, pred, succ in *; simpl in *.
elim (eq_dart_dec d y).
intro Heq; subst y; tauto.
elim (eq_dart_dec x y).
apply neq_sym in Hneq1; contradiction.
intros H1 H2; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold black_dart, pred, succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d0 y).
 intro H1; move H1 after Hsub; subst d0.
 elim (eq_dart_dec d1 y).
  intro H2; move H2 after Hsub; subst d1.
  rewrite Hsub2 in Hblack; tauto.
  intro H2; rewrite Hsub2 in Hblack; tauto.
 elim (eq_dart_dec d1 y).
  intros H1 H2; move H1 after Hsub; subst d1.
  rewrite Hsub3 in Hblack; tauto.
  intros H1 H2; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 y).
 intro H1; move H1 after Hsub; subst d0.
 elim (eq_dart_dec d1 y).
  intro H2; move H2 after Hsub; subst d1.
  rewrite Hsub2 in Hblack; tauto.
  intro H2; rewrite Hsub2 in Hblack; tauto.
 elim (eq_dart_dec d1 y).
  intros H1 H2; move H1 after Hsub; subst d1.
  rewrite Hsub3 in Hblack; tauto.
  intros H1 H2; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 y).
 intro H1; move H1 after Hsub; subst d0.
 elim (eq_dart_dec d1 y).
  intro H2; move H2 after Hsub; subst d1.
  rewrite Hsub2 in Hblack; tauto.
  intro H2; rewrite Hsub2 in Hblack; tauto.
 elim (eq_dart_dec d1 y).
  intros H1 H2; move H1 after Hsub; subst d1.
  rewrite Hsub3 in Hblack; tauto.
  intros H1 H2; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma blue_dart_CHID_1 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  blue_dart mr d -> exd m d -> exd (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hblue Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl in Hexd; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; right; left; trivial.
 intro H; simpl; right; right; apply IHm; assumption.
    intros H_left H_ccw H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
     intros H_right H_ccw H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl.
 apply red_not_black in H_red; contradiction.
 intro H; simpl; apply IHm; assumption.
   intros H_red H_blue.
elim Hexd; clear Hexd.
 intro H; subst y; simpl; left; trivial.
 intro H; simpl; right; apply IHm; assumption.
 (* Cas 3 : m = L *)
 induction d; simpl in *.
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

Lemma blue_dart_CHID_2 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> blue_dart mr d ->
  ~ succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ; simpl in *.
elim (eq_dart_dec max y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 y).
intro H; move H after Hsub; subst d0.
unfold blue_dart, succ, pred in Hblue.
rewrite Hsub2 in Hblue; tauto.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 y).
intro H; move H after Hsub; subst d0.
unfold blue_dart, succ, pred in Hblue.
rewrite Hsub2 in Hblue; tauto.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_3 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> blue_dart mr d ->
  ~ pred (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold pred; simpl in *.
elim (eq_dart_dec max y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d y).
intro H; subst y; contradiction.
intro H; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 y).
intro H; move H after Hsub; subst d1.
unfold blue_dart, succ, pred in Hblue.
rewrite Hsub3 in Hblue; tauto.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

(* ========================== *)

Lemma blue_dart_CHID_4 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  ccw (fpoint mr d) (fpoint mr (A mr zero d)) px ->
  A m zero d = A (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec d y).
intro H; subst d.
generalize H_ccw; clear H_ccw; unfold invisible.
elim (blue_dart_dec); intros H1 H2; [idtac|contradiction].
rewritenotorandnot H2 H2 H3; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec x y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; trivial.
intro H; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; move H after Hsub; subst d0.
rewrite <- Hsub2 in H_ccw; contradiction.
intro H; apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_5 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  ccw (fpoint mr d) (fpoint mr (A mr zero d)) px ->
  ~ succ m zero d -> ~ succ (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw Hsucc.
unfold succ in *; apply eq_not_neq; apply not_neq_eq in Hsucc.
apply sym_eq; rewrite <- Hsucc; clear Hsucc.
apply blue_dart_CHID_4; assumption.
Qed.

Lemma blue_dart_CHID_6 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  ccw (fpoint mr d) (fpoint mr (A mr zero d)) px ->
  succ m zero d -> succ (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw Hsucc.
unfold succ in *; rewrite <- blue_dart_CHID_4; assumption.
Qed.

Lemma blue_dart_CHID_7 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> blue_dart mr d -> invisible mr d px ->
  A_1 m one d = A_1 (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hblue Hccw.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec x y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; trivial.
intro H; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; trivial.
intro H; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; subst y; contradiction.
intro H; apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_8 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> blue_dart mr d -> invisible mr d px ->
  ~ pred m one d -> ~ pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hblue Hccw Hpred.
unfold pred in *; apply eq_not_neq; apply not_neq_eq in Hpred.
apply sym_eq; rewrite <- Hpred; clear Hpred.
apply blue_dart_CHID_7; assumption.
Qed.

Lemma blue_dart_CHID_9 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> blue_dart mr d -> invisible mr d px ->
  pred m one d -> pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hblue Hccw Hpred.
unfold pred in *; rewrite <- blue_dart_CHID_7; assumption.
Qed.

Lemma blue_dart_CHID_10 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> blue_dart mr d ->
  ccw (fpoint mr d) (fpoint mr (A mr zero d)) px ->
  blue_dart m d -> blue_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hblue Hccw H.
unfold blue_dart; repeat split.
apply blue_dart_CHID_6; try assumption.
unfold blue_dart in H; intuition.
apply blue_dart_CHID_2; try assumption.
apply blue_dart_CHID_3; try assumption.
apply blue_dart_CHID_9; try assumption.
unfold invisible.
elim blue_dart_dec; intro H0.
 left; assumption.
 contradiction.
unfold blue_dart in H; intuition.
Qed.

(* ========================== *)

Lemma blue_dart_CHID_11 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> exd m d -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  A (CHID m mr x tx px max) zero d = max.
Proof.
intros m mr x tx px max da Hsub Hneq Hexd Hblue Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 apply invisible_not_visible in H_ccw.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec d da); intro Heq.
 trivial.
 elim Hexd; clear Hexd; intro Hexd.
  contradiction.
  apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 elim H_left; subst da.
 unfold left_dart; split;
 [assumption | split; assumption].
 apply IHm; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec x da); intro Heq.
 apply sym_eq in Heq; contradiction.
 elim Hexd; clear Hexd; intro Hexd.
  subst da; contradiction.
  apply IHm; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d0 da); intro Heq.
 rewrite <- Hsub1 in H_ccw.
 generalize Hccw1; clear Hccw1.
 unfold visible; elim blue_dart_dec.
 intros H1 H2; subst da.
 apply axiom_orientation_4 in H2; contradiction.
 intros H1 H2; contradiction.
 apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_12 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> max <> nil -> exd m d -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  succ (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max da Hsub Hneq1 Hneq2 Hexd Hblue Hccw1 Hccw2.
unfold succ; rewrite blue_dart_CHID_11; assumption.
Qed.

Lemma blue_dart_CHID_13 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  A_1 m one d = A_1 (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec x y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; trivial.
intro H; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; trivial.
intro H; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; subst y.
rewrite Hsub2 in Hccw2; contradiction.
intro H; apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_14 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  ~ pred m one d -> ~ pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw1 Hccw2 Hpred.
unfold pred in *; apply eq_not_neq; apply not_neq_eq in Hpred.
apply sym_eq; rewrite <- Hpred; clear Hpred.
apply blue_dart_CHID_13; assumption.
Qed.

Lemma blue_dart_CHID_15 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  pred m one d -> pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw1 Hccw2 Hpred.
unfold pred in *; rewrite <- blue_dart_CHID_13; assumption.
Qed.

Lemma blue_dart_CHID_16 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> max <> nil ->
  exd m d -> blue_dart mr d ->
  visible mr d px -> invisible mr (A_1 mr one d) px ->
  blue_dart m d -> blue_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hneq3 Hexd Hblue Hccw1 Hccw2 H.
unfold blue_dart; repeat split.
apply blue_dart_CHID_12; try assumption.
apply blue_dart_CHID_2; try assumption.
apply blue_dart_CHID_3; try assumption.
apply blue_dart_CHID_15; try assumption.
unfold blue_dart in H; intuition.
Qed.

(* ========================== *)

Lemma blue_dart_CHID_17 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  visible mr d px -> visible mr (A_1 mr one d) px ->
  ~ succ (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max da Hsub Hneq Hblue Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec d da); intro Heq.
 unfold left_dart in H_left.
 destruct H_left as [H1 [H2 H3]].
 apply invisible_not_visible in H2.
 subst d; contradiction.
 apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec x da); intro Heq.
 apply sym_eq in Heq; contradiction.
 assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d0 da); intro Heq.
 rewrite <- Hsub1 in H_ccw.
 generalize Hccw1; clear Hccw1.
 unfold visible; elim blue_dart_dec.
 intros H1 H2; subst da.
 apply axiom_orientation_4 in H2; contradiction.
 intros H1 H2; contradiction.
 apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_18 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  visible mr d px -> visible mr (A_1 mr one d) px ->
  ~ pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max da Hsub Hneq Hblue Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold pred in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec x da); intro Heq.
 apply sym_eq in Heq; contradiction.
 apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold pred in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d1 da); intro Heq.
 subst da; rewrite Hsub2 in Hccw2.
 apply visible_not_invisible in Hccw2; contradiction.
apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d1 da); intro Heq.
 apply visible_not_invisible in Hccw1;
 subst da; contradiction.
apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_CHID_19 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> blue_dart mr d ->
  visible mr d px -> visible mr (A_1 mr one d) px ->
  black_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hblue Hccw1 Hccw2.
unfold black_dart; repeat split.
apply blue_dart_CHID_17; try assumption.
apply blue_dart_CHID_2; try assumption.
apply blue_dart_CHID_3; try assumption.
apply blue_dart_CHID_18; try assumption.
Qed.

(* ========================== *)

Lemma blue_dart_CHID_20 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap m -> d <> x -> blue_dart mr d ->
  ~ pred m one d -> ~ pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max d1 Hmap Hneq Hblue Hpred.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold pred in *; simpl in *.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 simpl.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl; apply IHm; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl; elim (eq_dart_dec x d1).
 intro H; apply sym_eq in H; contradiction.
 intro H; apply IHm; assumption.
    intros H_left H_ccw H_blue.
simpl; apply IHm; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl; apply IHm; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl; apply IHm; assumption.
     intros H_right H_ccw H_red H_blue.
apply IHm; assumption.
   intros H_red H_blue.
simpl; apply IHm; assumption.
 (* Cas 3 : m = L *)
 induction d; simpl in *;
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
  elim ccw_dec.
   intros H_ccw.
apply IHm; assumption.
   intros H_ccw.
apply IHm; assumption.
  elim invisible_dec.
   intros H_ccw.
unfold pred in *; simpl in *.
generalize Hpred; clear Hpred.
elim (eq_dart_dec d2 d1).
 intros H1 H2; trivial.
 intros H1 H2; apply IHm; assumption.
   elim invisible_dec.
    intros Hccw1 Hccw2.
unfold pred in *; simpl in *.
generalize Hpred; clear Hpred.
elim (eq_dart_dec d2 d1).
 intros H1 H2; trivial.
 intros H1 H2; apply IHm; assumption.
    intros Hccw1 Hccw2.
unfold pred in *; simpl in *.
generalize Hpred; clear Hpred.
elim (eq_dart_dec d2 d1).
 intros H1 H2; subst d2.
 apply exd_not_nil in Hmap1; tauto.
 intros H1 H2; apply IHm; assumption.
Qed.

(* ========================== *)

Lemma blue_dart_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> inv_hmap mr -> well_emb mr -> inv_noalign_point mr px ->
  d <> x -> d <> max -> max <> nil -> exd m d ->
  blue_dart m d -> blue_dart mr d ->
  black_dart (CHID m mr x tx px max) d \/ blue_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max d.
intros Hsub Hmr1 Hmr2 Hmr3 Hneq1 Hneq2 Hneq3 Hexd Hb1 Hb2.
assert (Hd1 : succ mr zero d). unfold blue_dart in Hb2; intuition.
assert (Hd2 : exd mr d). apply succ_exd with zero; try assumption.
elim (ccw_dec (fpoint mr d) (fpoint mr (A mr zero d)) px); intro H1; [right|idtac].
 apply blue_dart_CHID_10; try assumption.
elim (invisible_dec mr (A_1 mr one d) px); intro H2; [right|left].
 apply blue_dart_CHID_16; try assumption.
 unfold visible; elim blue_dart_dec; intro Hblue; [clear Hblue | contradiction].
 apply axiom_orientation_7 in H1; elim H1; clear H1; [trivial|idtac].
 assert (H0 : ~ align (fpoint mr d) (fpoint mr (A mr zero d)) px); [idtac|contradiction].
  unfold inv_noalign_point in Hmr3; apply Hmr3; try assumption.
  apply succ_exd_A; try assumption.
  apply well_emb_A_zero; try assumption.
 apply blue_dart_CHID_19; try assumption.
 unfold visible; elim blue_dart_dec; intro Hblue; [clear Hblue | contradiction].
 apply axiom_orientation_7 in H1; elim H1; clear H1; [trivial|idtac].
 assert (H0 : ~ align (fpoint mr d) (fpoint mr (A mr zero d)) px); [idtac|contradiction].
  unfold inv_noalign_point in Hmr3; apply Hmr3; try assumption.
  apply succ_exd_A; try assumption.
  apply well_emb_A_zero; try assumption.
 apply not_invisible_visible; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma red_dart_CHID_1 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> red_dart mr d ->
  ~ succ (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d y).
intro H; apply blue_not_red in H_blue;
subst y; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold succ; simpl in *.
elim (eq_dart_dec x y).
 intro Heq; apply sym_eq in Heq; contradiction.
 intro Heq; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 y).
intro H; move H after Hsub; subst d0.
unfold red_dart, succ, pred in Hred.
rewrite Hsub2 in Hred; intuition.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_2 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> red_dart mr d ->
  ~ pred (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold pred; simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec x y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold pred; simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; move H after Hsub; subst d1.
unfold red_dart, succ, pred in Hred.
rewrite Hsub3 in Hred; tauto.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; move H after Hsub; subst d1.
unfold red_dart, succ, pred in Hred.
rewrite Hsub3 in Hred; tauto.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

(* ========================== *)

Lemma red_dart_CHID_3 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  red_dart mr d -> invisible mr d px ->
  exd m d -> exd (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hred Hccw Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; right; left; assumption.
 intro H; right; right; apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; subst d; contradiction.
 intro H; apply IHm; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_4 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> max -> red_dart mr d -> invisible mr d px ->
  A m one d = A (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hred Hccw.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; trivial.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; trivial.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; subst d0; contradiction.
intro H; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_5 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> max -> red_dart mr d -> invisible mr d px ->
  ~ succ m one d -> ~ succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hred Hccw Hsucc.
unfold succ in *; apply eq_not_neq; apply not_neq_eq in Hsucc.
apply sym_eq; rewrite <- Hsucc; clear Hsucc.
apply red_dart_CHID_4; assumption.
Qed.

Lemma red_dart_CHID_6 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> max -> red_dart mr d -> invisible mr d px ->
  succ m one d -> succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hneq Hred Hccw Hsucc.
unfold succ in *; rewrite <- red_dart_CHID_4; assumption.
Qed.

Lemma red_dart_CHID_7 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px ->
  A_1 m zero d = A_1 (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d y).
intro H; move H after Hsub; subst d.
generalize H_ccw; clear H_ccw.
unfold invisible; elim blue_dart_dec.
 intros H1 H2; contradiction.
 intros H1 H2; rewritenotorandnot H2 H2 H3; contradiction.
intro H; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; trivial.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl in *.
elim (eq_dart_dec d1 y).
intro H; move H after Hsub; subst d1.
rewrite <- Hsub3 in H_ccw; contradiction.
intro H; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_8 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px ->
  ~ pred m zero d -> ~ pred (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw Hpred.
unfold pred in *; apply eq_not_neq; apply not_neq_eq in Hpred.
apply sym_eq; rewrite <- Hpred; clear Hpred.
apply red_dart_CHID_7; assumption.
Qed.

Lemma red_dart_CHID_9 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px ->
  pred m zero d -> pred (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw Hpred.
unfold pred in *; rewrite <- red_dart_CHID_7; assumption.
Qed.

Lemma red_dart_CHID_10 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> red_dart mr d ->
  ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px ->
  red_dart m d -> red_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hred Hccw H.
unfold red_dart; repeat split.
apply red_dart_CHID_1; try assumption.
apply red_dart_CHID_6; try assumption.
unfold invisible.
elim blue_dart_dec; intro H0.
 apply red_not_blue in Hred; contradiction.
 left; assumption.
unfold red_dart in H; intuition.
apply red_dart_CHID_9; try assumption.
unfold red_dart in H; intuition.
apply red_dart_CHID_2; try assumption.
Qed.

(* ========================== *)

Lemma red_dart_CHID_11 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  red_dart mr d -> visible mr d px -> invisible mr (A mr one d) px ->
  exd m d -> exd (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hred Hccw1 Hccw2 Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; right; left; assumption.
 intro H; right; right; apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; subst d.
 elim H_right; unfold right_dart; intuition.
 intro H; apply IHm; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hexd; clear Hexd.
 intro H; left; assumption.
 intro H; right; apply IHm; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_12 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d -> visible mr d px -> invisible mr (A mr one d) px ->
  A m one d = A (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 [Hsub3 Hsub4]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max y).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; trivial.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; trivial.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *.
elim (eq_dart_dec d0 y).
intro H; subst y.
rewrite Hsub2 in Hccw2; contradiction.
intro H; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_13 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  visible mr d px -> invisible mr (A mr one d) px ->
  ~ succ m one d -> ~ succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw1 Hccw2 Hsucc.
unfold succ in *; apply eq_not_neq; apply not_neq_eq in Hsucc.
apply sym_eq; rewrite <- Hsucc; clear Hsucc.
apply red_dart_CHID_12; assumption.
Qed.

Lemma red_dart_CHID_14 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  visible mr d px -> invisible mr (A mr one d) px ->
  succ m one d -> succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hred Hccw1 Hccw2 Hsucc.
unfold succ in *; rewrite <- red_dart_CHID_12; assumption.
Qed.

Lemma red_dart_CHID_15 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> exd m d -> red_dart mr d ->
  visible mr d px -> invisible mr (A mr one d) px ->
  A_1 (CHID m mr x tx px max) zero d = x.
Proof.
intros m mr x tx px max da Hsub Hneq Hexd Hred Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 apply red_not_blue in Hred.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max da); intro Heq.
 apply sym_eq in Heq; contradiction.
 elim Hexd; clear Hexd; intro Hexd.
 apply red_not_blue in Hred.
 subst da; contradiction.
  apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 apply red_not_blue in Hred.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 apply visible_not_invisible in Hccw1;
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d da); intro Heq; [trivial|idtac].
elim Hexd; clear Hexd.
 intro Hexd; contradiction.
 intro Hexd; apply IHm; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 elim H_right; unfold right_dart; subst da; intuition. 
 apply IHm; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hexd; clear Hexd; intro Hexd.
 subst da; contradiction.
 apply IHm; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d1 da); intro Heq.
 rewrite <- Hsub2 in H_ccw.
 generalize Hccw1; clear Hccw1.
 unfold visible; elim blue_dart_dec.
 intros H1 H2; apply red_not_blue in Hred; contradiction.
 intros H1 H2; subst da.
 apply axiom_orientation_4 in H2; contradiction.
 apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_16 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> x <> nil -> exd m d -> red_dart mr d ->
  visible mr d px -> invisible mr (A mr one d) px ->
  pred (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max da Hsub Hneq1 Hneq2 Hexd Hred Hccw1 Hccw2.
unfold pred; rewrite red_dart_CHID_15; assumption.
Qed.

Lemma red_dart_CHID_17 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> d <> max -> x <> nil ->
  red_dart mr d -> visible mr d px -> invisible mr (A mr one d) px ->
  exd m d -> red_dart m d -> red_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hsub Hneq1 Hneq2 Hneq3 Hred Hccw1 Hccw2 Hexd H.
unfold red_dart; repeat split.
apply red_dart_CHID_1; try assumption.
apply red_dart_CHID_14; try assumption.
unfold red_dart in H; intuition.
apply red_dart_CHID_16; try assumption.
apply red_dart_CHID_2; try assumption.
Qed.

(* ========================== *)

Lemma red_dart_CHID_18 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> d <> max -> red_dart mr d ->
  visible mr d px -> visible mr (A mr one d) px ->
  ~ exd (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max da Hneq1 Hneq2 Hred Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; intuition.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da; apply red_not_blue in Hred; contradiction.
 intro H; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *; apply and_not_not_or; split.
apply neq_sym; assumption.
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da; apply red_not_blue in Hred; contradiction.
 intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da; apply red_not_blue in Hred; contradiction.
 intro H; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da; apply visible_not_invisible in Hccw1; contradiction.
 intro H; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da.
 unfold right_dart in H_right.
 apply visible_not_invisible in Hccw2; intuition.
 intro H; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; apply and_not_not_or; split; [idtac|assumption].
elim (eq_dart_dec d da).
 intro H; subst da; contradiction.
 intro H; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_19 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  visible mr d px -> visible mr (A mr one d) px ->
  ~ succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max da Hsub Hneq Hred Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max da); intro Heq.
 apply sym_eq in Heq; contradiction.
 apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold succ in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 da); intro Heq.
 apply visible_not_invisible in Hccw1.
 subst da; contradiction.
 apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 da); intro Heq.
 rewrite <- Hsub1 in H_ccw1.
 apply visible_not_invisible in Hccw2.
 subst da; contradiction.
 apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

Lemma red_dart_CHID_20 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> max -> red_dart mr d ->
  visible mr d px -> visible mr (A mr one d) px ->
  ~ pred (CHID m mr x tx px max) zero d.
Proof.
intros m mr x tx px max da Hsub Hneq Hred Hccw1 Hccw2.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold pred in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 generalize (IHm Hsub); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max da); intro Heq.
 apply sym_eq in Heq; contradiction.
 apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d da); intro Heq.
 subst da; unfold right_dart in H_right.
 apply visible_not_invisible in Hccw2; intuition.
 apply IHm; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold pred in *; simpl in *.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d1 da); intro Heq.
 subst da; rewrite <- Hsub2 in H_ccw.
 generalize Hccw1; clear Hccw1.
 unfold visible; elim blue_dart_dec.
 intros H1 H2; apply red_not_blue in Hred; contradiction.
 intros H1 H2; apply axiom_orientation_4 in H2; contradiction.
 apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; assumption.
(* ======== *)
Qed.

(* ========================== *)

Lemma red_dart_CHID_21 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap m -> d <> max -> red_dart mr d ->
  ~ succ m one d -> ~ succ (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hmap Hneq Hred Hsucc.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold succ in *; simpl in *.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 simpl.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl; apply IHm; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl; elim (eq_dart_dec max y).
 intro H; apply sym_eq in H; contradiction.
 intro H; apply IHm; assumption.
    intros H_left H_ccw H_blue.
simpl; apply IHm; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl; apply IHm; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl; apply IHm; assumption.
     intros H_right H_ccw H_red H_blue.
apply IHm; assumption.
   intros H_red H_blue.
simpl; apply IHm; assumption.
 (* Cas 3 : m = L *)
 induction d; simpl in *;
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
  elim ccw_dec.
   intros H_ccw.
apply IHm; assumption.
   intros H_ccw.
apply IHm; assumption.
  elim invisible_dec.
   intros H_ccw.
unfold succ in *; simpl in *.
generalize Hsucc; clear Hsucc.
elim (eq_dart_dec d0 y).
 intros H1 H2; trivial.
 intros H1 H2; apply IHm; assumption.
   elim invisible_dec.
    intros Hccw1 Hccw2.
unfold succ in *; simpl in *.
generalize Hsucc; clear Hsucc.
elim (eq_dart_dec d0 y).
 intros H1 H2; trivial.
 intros H1 H2; apply IHm; assumption.
    intros Hccw1 Hccw2.
unfold succ in *; simpl in *.
generalize Hsucc; clear Hsucc.
elim (eq_dart_dec d0 y).
 intros H1 H2; subst y.
 apply exd_not_nil in Hmap2; tauto.
 intros H1 H2; apply IHm; assumption.
Qed.

(* ========================== *)

Lemma red_dart_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> inv_hmap mr -> well_emb mr -> inv_noalign_point mr px ->
  d <> x -> d <> max -> x <> nil -> exd m d ->
  red_dart m d -> red_dart mr d ->
  ~ exd (CHID m mr x tx px max) d \/ red_dart (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max d.
intros Hsub Hmr1 Hmr2 Hmr3 Hneq1 Hneq2 Hneq3 Hexd Hb1 Hb2.
assert (Hd1 : pred mr zero d). unfold red_dart in Hb2; intuition.
assert (Hd2 : exd mr d). apply pred_exd with zero; try assumption.
elim (ccw_dec (fpoint mr (A_1 mr zero d)) (fpoint mr d) px); intro H1; [right|idtac].
 apply red_dart_CHID_10; try assumption.
elim (invisible_dec mr (A mr one d) px); intro H2; [right|left].
 apply red_dart_CHID_17; try assumption.
 unfold visible; elim blue_dart_dec; intro Hblue.
 apply red_not_blue in Hb2; contradiction.
 apply axiom_orientation_7 in H1; elim H1; clear H1; [trivial|idtac].
 assert (H0 : ~ align (fpoint mr (A_1 mr zero d)) (fpoint mr d) px); [idtac|contradiction].
  unfold inv_noalign_point in Hmr3; apply Hmr3; try assumption.
  apply pred_exd_A_1; try assumption.
  apply neq_sym_point; apply well_emb_A_1_zero; try assumption.
 apply red_dart_CHID_18; try assumption.
 unfold visible; elim blue_dart_dec; intro Hblue.
 apply red_not_blue in Hb2; contradiction.
 apply axiom_orientation_7 in H1; elim H1; clear H1; [trivial|idtac].
 assert (H0 : ~ align (fpoint mr (A_1 mr zero d)) (fpoint mr d) px); [idtac|contradiction].
  unfold inv_noalign_point in Hmr3; apply Hmr3; try assumption.
  apply pred_exd_A_1; try assumption.
  apply neq_sym_point; apply well_emb_A_1_zero; try assumption.
 apply not_invisible_visible; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma x_CHID_1 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  exd (CHID m mr x tx px max) x.
Proof.
induction m.
 (* Cas 1 : m = V *)
 intros mr x tx px max.
 simpl; tauto.
 (* Cas 2 : m = I *)
 intros mr x tx px max.
 simpl.
 elim blue_dart_dec.
  elim invisible_dec.
   intros Hccw Hblue.
   simpl; right; apply IHm.
   elim left_dart_dec.
    intros Hleft Hccw Hblue.
    simpl; right; right; apply IHm.
    intros Hleft Hccw Hblue.
    simpl; right; apply IHm.
  elim red_dart_dec.
   elim invisible_dec.
    intros Hccw Hred Hblue.
    simpl; right; apply IHm.
    elim right_dart_dec.
     intros Hright Hccw Hred Hblue.
     simpl; right; apply IHm.
     intros Hright Hccw Hred Hblue.
     simpl; apply IHm.
   intros Hred Hblue.
   simpl; right; apply IHm.
 (* Cas 3 : m = L *)
 intros mr x tx px max.
 case d; simpl.
  elim ccw_dec.
   intros Hccw; simpl; apply IHm.
   intros Hccw; simpl; apply IHm.
  elim invisible_dec.
   intros Hccw; simpl; apply IHm.
   elim invisible_dec.
    intros Hccw1 Hccw2; simpl; apply IHm.
    intros Hccw1 Hccw2; simpl; apply IHm.
Qed.

Lemma x_CHID_2 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m x ->
  ~ succ (CHID m mr x tx px max) one x.
Proof.
intros m mr x tx px max Hinv Hneq Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold succ; simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max x).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold succ; simpl in *.
 unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *.
elim (eq_dart_dec d0 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======== *)
Qed.

Lemma x_CHID_3 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m x ->
  ~ pred (CHID m mr x tx px max) zero x.
Proof.
intros m mr x tx px max Hinv Hneq Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold pred; simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max x).
intro H; apply sym_eq in H; contradiction.
intro H; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d x).
intro H; contradiction.
intro H; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 unfold pred; simpl in *.
 unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d1 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; apply IHm; assumption.
(* ======== *)
Qed.

Lemma x_CHID_4 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x ->
  (forall (d:dart), exd m d -> ~ right_dart mr px d) ->
  ~ succ (CHID m mr x tx px max) zero x.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold succ in *; simpl in *.
 unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl; elim (eq_dart_dec d x).
 apply not_or_and_not in Hexd; intuition.
intro Heq; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; elimeqdartdec.
generalize (H d); intuition.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   intros H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
 (* Cas 3 : m = L *)
 unfold succ in *; simpl in *.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl; elim (eq_dart_dec d0 x).
 intro Heq; subst x; contradiction.
 intro Heq; apply IHm; try assumption.
   intros H_ccw.
simpl; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl in *; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
simpl in *; apply IHm; try assumption.
Qed.

Lemma x_CHID_5 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d) ->
  ~ pred (CHID m mr x tx px max) one x.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold pred in *; simpl in *.
 unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; elimeqdartdec.
generalize (H d); intuition.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   intros H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
 (* Cas 3 : m = L *)
 unfold pred in *; simpl in *.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; elim (eq_dart_dec d1 x).
 intro Heq; subst x; contradiction.
 intro Heq; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl; elim (eq_dart_dec d1 x).
 intro Heq; subst x; contradiction.
 intro Heq; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
apply IHm; try assumption.
Qed.

Lemma x_CHID_6 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m x ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d /\ ~ right_dart mr px d) ->
  black_dart (CHID m mr x tx px max) x.
Proof.
intros m mr x tx px max Hinv Hneq Hexd H.
unfold black_dart; repeat split.
apply x_CHID_4; try assumption.
intros d H0; generalize (H d H0); intuition.
apply x_CHID_2; try assumption.
apply x_CHID_3; try assumption.
apply x_CHID_5; try assumption.
intros d H0; generalize (H d H0); intuition.
Qed.

Lemma x_CHID_7 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  inv_hmap m -> ~ exd m x -> exd m d -> right_dart mr px d ->
  A (CHID m mr x tx px max) zero x = d.
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hinv Hexd Hd1 Hd2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold right_dart in Hd2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec d x).
intro H; contradiction.
elim Hd1; clear Hd1.
 unfold right_dart in Hd2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 intros H1 H2; apply IHm; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold right_dart in Hd2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold right_dart in Hd2.
 apply invisible_not_visible in H_ccw.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elimeqdartdec.
apply one_right with mr px; try assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro H; subst d; contradiction.
 assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold right_dart in Hd2.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd Hd1); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d0 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma x_CHID_8 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> (exists d:dart, exd m d /\ right_dart mr px d) ->
  succ (CHID m mr x tx px max) zero x.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *.
 elim H; intuition.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
unfold succ; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold right_dart in Hda2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d x).
intro Heq; contradiction.
intro Heq; elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold right_dart in Hda2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold succ; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold right_dart in Hda2.
 apply blue_not_red in H_blue.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold succ; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 intro H; subst da; unfold right_dart in Hda2.
 apply invisible_not_visible in H_ccw; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold succ; simpl in *.
elimeqdartdec; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
unfold succ; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 intro H; subst da; contradiction.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold succ; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 intro H; subst da; unfold right_dart in Hda2; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 [Hinv5 Hinv6]]]]].
 generalize (IHm Hinv1 Hexd H); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 x).
intro Heq; subst x; contradiction.
intro Heq; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma x_CHID_9 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> (exists d:dart, exd m d /\ left_dart mr px d) ->
  A_1 (CHID m mr x tx px max) one x = max.
Proof.
intros m mr x tx px max Hinv Hexd H.
elim H; clear H; intros da [Hd1 Hd2].
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold left_dart in Hd2.
 apply invisible_not_visible in H_ccw.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elimeqdartdec; trivial.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro H; subst da; contradiction.
 assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold left_dart in Hd2.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold left_dart in Hd2.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold left_dart in Hd2.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hd1; clear Hd1.
 unfold left_dart in Hd2.
 intro H; subst da; intuition.
 assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd Hd1); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d1 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d1 x).
intro H; subst x; contradiction.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma x_CHID_10 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> max <> nil ->
  (exists d:dart, exd m d /\ left_dart mr px d) ->
  pred (CHID m mr x tx px max) one x.
Proof.
intros m mr x tx px max Hinv Hexd Hneq H.
unfold pred; rewrite (x_CHID_9 m mr x tx px max); try assumption.
Qed.

Lemma x_CHID_11 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m x -> max <> nil ->
  (exists da:dart, exd m da /\ left_dart mr px da) ->
  (exists db:dart, exd m db /\ right_dart mr px db) ->
  blue_dart (CHID m mr x tx px max) x.
Proof.
intros m mr x tx px max Hinv Hneq1 Hexd Hneq2 H1 H2.
unfold blue_dart; repeat split.
apply x_CHID_8; try assumption.
apply x_CHID_2; try assumption.
apply x_CHID_3; try assumption.
apply x_CHID_10; try assumption.
Qed.

Lemma x_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m x -> max <> nil ->
  (exists da:dart, exd m da /\ left_dart mr px da) /\
  (exists db:dart, exd m db /\ right_dart mr px db) \/
  (forall d:dart, exd m d -> ~ left_dart mr px d /\ ~ right_dart mr px d)->
  black_dart (CHID m mr x tx px max) x \/ blue_dart (CHID m mr x tx px max) x.
Proof.
intros m mr x tx px max Hinv Hneq Hexd Hmax H.
elim H; clear H.
intros [H1 H2]; right; apply x_CHID_11; assumption.
intro H; left; apply x_CHID_6; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma max_CHID_1 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m max ->
  ~ succ (CHID m mr x tx px max) zero max.
Proof.
intros m mr x tx px max Hmap Hneq Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold succ; simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hmap Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *.
elim (eq_dart_dec d max).
 intro H; contradiction.
 intro H; apply IHm.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *.
elim (eq_dart_dec x max).
 intro H; contradiction.
 intro H; apply IHm.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm.
   intros H_red H_blue.
simpl in *; apply IHm.
 (* Cas 3 : m = L *)
 induction d; simpl in *; unfold succ, prec_L in *;
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 Hmap4]]]];
 generalize (IHm Hmap Hexd); clear IHm; intro IHm.
  elim ccw_dec.
   intros H_ccw.
simpl in *.
elim (eq_dart_dec d0 max).
 intro H; subst max; contradiction.
 intro H; apply IHm.
   intros H_ccw.
simpl in *; apply IHm.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm.
   elim invisible_dec.
    intros Hccw1 Hccw2.
simpl in *; apply IHm.
    intros Hccw1 Hccw2.
simpl in *; apply IHm.
Qed.

Lemma max_CHID_2 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m max ->
  ~ pred (CHID m mr x tx px max) one max.
Proof.
intros m mr x tx px max Hmap Hneq Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 unfold pred; simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hmap Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *.
elim (eq_dart_dec x max).
 intro H; contradiction.
 intro H; apply IHm.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm.
   intros H_red H_blue.
simpl in *; apply IHm.
 (* Cas 3 : m = L *)
 induction d; simpl in *; unfold pred, prec_L in *;
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 Hmap4]]]];
 generalize (IHm Hmap Hexd); clear IHm; intro IHm.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm.
   intros H_ccw.
simpl in *; apply IHm.
  elim invisible_dec.
   intros H_ccw.
simpl in *.
elim (eq_dart_dec d1 max).
 intro H; subst max; contradiction.
 intro H; apply IHm.
   elim invisible_dec.
    intros Hccw1 Hccw2.
simpl in *.
elim (eq_dart_dec d1 max).
 intro H; subst max; contradiction.
 intro H; apply IHm.
    intros Hccw1 Hccw2.
simpl in *; apply IHm.
Qed.

Lemma max_CHID_3 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> max -> ~ exd m max ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d) ->
  ~ exd (CHID m mr x tx px max) max.
Proof.
intros m mr x tx px max Hinv Hneq Hexd H.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *; unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply and_not_not_or; split.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; generalize (H d); intuition.
    intros H_left H_ccw H_blue.
simpl in *; apply and_not_not_or; split.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply and_not_not_or; split.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply and_not_not_or; split.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   intros H_red H_blue.
simpl in *; apply and_not_not_or; split.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl in *; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
apply IHm; try assumption.
Qed.

Lemma max_CHID_4 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d) ->
  ~ succ (CHID m mr x tx px max) one max.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold succ in *; simpl in *.
 unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; generalize (H d); intuition.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   intros H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
 (* Cas 3 : m = L *)
 unfold succ in *; simpl in *.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; elim (eq_dart_dec d0 max).
 intro Heq; subst max; contradiction.
 intro Heq; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl; elim (eq_dart_dec d0 max).
 intro Heq; subst max; contradiction.
 intro Heq; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
apply IHm; try assumption.
Qed.

Lemma max_CHID_5 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d) ->
  ~ pred (CHID m mr x tx px max) zero max.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl; tauto.
 (* Cas 2 : m = I *)
 unfold pred in *; simpl in *.
 unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; generalize (H d); intuition.
    intros H_left H_ccw H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; elim (eq_dart_dec d max); intro Heq.
apply not_or_and_not in Hexd; intuition.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
     intros H_right H_ccw H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
   intros H_red H_blue.
simpl in *; apply IHm; try assumption.
apply not_or_and_not in Hexd; intuition.
intros d0 Hd0; clear IHm.
apply H; right; assumption.
 (* Cas 3 : m = L *)
 unfold pred in *; simpl in *.
 unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; elim (eq_dart_dec d1 max).
 intro Heq; subst max; contradiction.
 intro Heq; apply IHm; try assumption.
   intros H_ccw.
simpl in *; elim (eq_dart_dec d1 max).
 intro Heq; subst max; contradiction.
 intro Heq; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl in *; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
apply IHm; try assumption.
Qed.

Lemma max_CHID_6 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max ->
  (exists d:dart, exd m d /\ left_dart mr px d) ->
  exd (CHID m mr x tx px max) max.
Proof.
intros m mr x tx px max Hinv Hexd H.
elim H; clear H; intros da [Hd1 Hd2].
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *; unfold prec_I in Hinv.
 destruct Hinv as [Hinv [Hneq1 Hexd1]].
 rewritenotorandnot Hexd Hexd2 Hexd3.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
simpl in *; right.
elim Hd1; clear Hd1.
intro Hd1; subst da; clear IHm.
apply invisible_not_visible in H_ccw.
unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
simpl in *; left; trivial.
    intros H_left H_ccw H_blue.
simpl in *; right.
elim Hd1; clear Hd1.
intro Hd1; subst da; contradiction.
intro Hd1; apply IHm; try assumption.
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
simpl in *; right.
elim Hd1; clear Hd1.
intro Hd1; subst da; clear IHm.
unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
simpl in *; right.
elim Hd1; clear Hd1.
intro Hd1; subst da; clear IHm.
unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
     intros H_right H_ccw H_red H_blue.
elim Hd1; clear Hd1.
intro Hd1; subst da; clear IHm.
unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
   intros H_red H_blue.
simpl in *; right.
elim Hd1; clear Hd1.
intro Hd1; subst da; clear IHm.
unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in Hinv.
 destruct Hinv as [Hinv [H1 [H2 [H3 [H4 H5]]]]].
 induction d; simpl.
  elim ccw_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
  elim invisible_dec.
   intros H_ccw.
simpl in *; apply IHm; try assumption.
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
simpl in *; apply IHm; try assumption.
    intros H_ccw1 H_ccw2.
apply IHm; try assumption.
Qed.

Lemma max_CHID_7 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max ->
  (exists d:dart, exd m d /\ left_dart mr px d) ->
  A (CHID m mr x tx px max) one max = x.
Proof.
intros m mr x tx px max Hinv Hexd H.
elim H; clear H; intros da [Hd1 Hd2].
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 apply invisible_not_visible in H_ccw.
 unfold left_dart in Hd2; intuition.
intro Hd1; apply IHm; try assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *; elimeqdartdec; trivial.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; contradiction.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd Hd1); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *.
elim (eq_dart_dec d0 max).
intro H; subst max; contradiction.
intro H; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *.
elim (eq_dart_dec d0 max).
intro H; subst max; contradiction.
intro H; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma max_CHID_8 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> nil -> ~ exd m max ->
  (exists d:dart, exd m d /\ left_dart mr px d) ->
  succ (CHID m mr x tx px max) one max.
Proof.
intros m mr x tx px max Hinv Hneq Hexd H; unfold succ.
rewrite (max_CHID_7 m mr x tx px max); try assumption.
Qed.

Lemma max_CHID_9 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  inv_hmap m -> ~ exd m max -> exd m d -> left_dart mr px d ->
  A_1 (CHID m mr x tx px max) zero max = d.
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hinv Hexd Hd1 Hd2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 apply invisible_not_visible in H_ccw.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *; elimeqdartdec.
apply one_left with mr px; try assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; contradiction.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d max).
 intro Heq; contradiction.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intros H1 H2; apply IHm; try assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *.
elim Hd1; clear Hd1.
 intro Hd1; subst da; clear IHm.
 unfold left_dart in Hd2; intuition.
 intro Hd1; apply IHm; try assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in *;
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 Hinv5]]]].
 generalize (IHm Hinv1 Hexd Hd1); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *.
elim (eq_dart_dec d1 max).
intro H; subst max; contradiction.
intro H; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma max_CHID_10 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max -> (exists d:dart, exd m d /\ left_dart mr px d) ->
  pred (CHID m mr x tx px max) zero max.
Proof.
intros m mr x tx px max Hinv Hexd H.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *.
 elim H; intuition.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 Hinv3]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hinv1 Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
unfold pred; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold left_dart in Hda2.
 apply invisible_not_visible in H_ccw.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold pred; simpl in *.
elimeqdartdec; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold pred; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 intro H; subst da; contradiction.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold pred; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold left_dart in Hda2.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d max).
 intro Heq; contradiction.
 intro Heq; elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold left_dart in Hda2.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
unfold pred; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold left_dart in Hda2.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold pred; simpl in *.
elim H; clear H.
intros da [Hda1 Hda2].
elim Hda1; clear Hda1.
 unfold left_dart in Hda2.
 intro H; subst da; intuition.
 intro H; apply IHm; try assumption.
 exists da; split; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hinv as [Hinv1 [Hinv2 [Hinv3 [Hinv4 [Hinv5 Hinv6]]]]].
 generalize (IHm Hinv1 Hexd H); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 max).
intro Heq; subst max; contradiction.
intro Heq; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
simpl; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl; assumption.
(* ======== *)
Qed.

Lemma max_CHID_11 :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max -> x <> nil -> x <> max ->
  (exists d:dart, exd m d /\ left_dart mr px d) ->
  red_dart (CHID m mr x tx px max) max.
Proof.
intros m mr x tx px max Hinv Hexd Hneq1 Hneq2 H.
unfold red_dart; repeat split.
apply max_CHID_1; try assumption.
apply max_CHID_8; try assumption.
apply max_CHID_10; try assumption.
apply max_CHID_2; try assumption.
Qed.

Lemma max_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> x <> nil -> x <> max -> ~ exd m max ->
  (exists d:dart, exd m d /\ left_dart mr px d) \/
  (forall d:dart, exd m d -> ~ left_dart mr px d)->
  ~ exd (CHID m mr x tx px max) max \/ red_dart (CHID m mr x tx px max) max.
Proof.
intros m mr x tx px max Hinv Hneq1 Hneq2 Hexd H.
elim H; clear H; intro H.
 right; apply max_CHID_11; assumption.
 left; apply max_CHID_3; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma pred_one_x_exd_left_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> pred (CHID m mr x tx px max) one x ->
  (exists d:dart, exd m d /\ left_dart mr px d).
Proof.
intros m mr x tx px max Hqh Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold pred; simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hqh as [Hqh [Hqh1 Hqh2]].
 rewritenotorandnot Hexd Hneq Hexd.
 generalize (IHm Hqh Hexd); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *; intro H.
exists d; split; [left; trivial | assumption].
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; repeat (split; try assumption).
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hqh as [Hqh [Hqh1 [Hqh2 [Hqh3 Hqh4]]]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 x); intro Heq.
 subst x; contradiction.
apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 x); intro Heq.
 subst x; contradiction.
apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma succ_zero_x_exd_right_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> succ (CHID m mr x tx px max) zero x ->
  (exists d:dart, exd m d /\ right_dart mr px d).
Proof.
intros m mr x tx px max Hqh Hexd.
induction m.
 (* Cas 1 : m = V *)
 unfold succ; simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hqh as [Hqh [Hqh1 Hqh2]].
 rewritenotorandnot Hexd Hneq Hexd.
 generalize (IHm Hqh Hexd); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d x).
 intro Heq; contradiction.
intros Heq H; generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold succ; simpl in *.
elim (eq_dart_dec x x); [idtac|tauto].
 intros Heq Hneq0.
 exists d; split; [left; trivial | assumption].
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; repeat (split; try assumption).
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros db [Hdb1 [Hdb2 Hdb3]].
apply (@or_intror (d = db)) in Hdb1.
exists db; do 2 (split; try assumption).
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hqh as [Hqh [Hqh1 [Hqh2 [Hqh3 Hqh4]]]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 x); intro Heq.
 subst x; contradiction.
apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma blue_dart_x_exd_left_dart_exd_right_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> blue_dart (CHID m mr x tx px max) x ->
  (exists da:dart, exd m da /\ left_dart mr px da) /\
  (exists db:dart, exd m db /\ right_dart mr px db).
Proof.
intros m mr x tx px max Hqh Hexd.
intros [H1 [H2 [H3 H4]]]; split.
apply (pred_one_x_exd_left_dart m mr x tx px max); assumption.
apply (succ_zero_x_exd_right_dart m mr x tx px max); assumption.
Qed.

(* ========================== *)

Lemma not_pred_one_x_not_exd_left_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> max <> nil ->
  ~ pred (CHID m mr x tx px max) one x ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d).
Proof.
intros m mr x tx px max Hmap Hexd Hneq Hpred.
generalize (x_CHID_10 m mr x tx px max Hmap Hexd Hneq); intro H.
assert (H0 : forall (A B : Prop), (A -> B) -> (~ B -> ~ A)).
 intros A B H0 H1 H2; apply H1; apply H0; apply H2.
assert (H1 : ~ pred (CHID m mr x tx px max) one x ->
 ~ (exists d:dart, exd m d /\ left_dart mr px d)).
 apply H0; exact H.
generalize (H1 Hpred); clear H H0 H1 Hmap Hexd Hneq Hpred.
intros H d H1 H2; apply H; exists d; intuition.
Qed.

Lemma not_succ_zero_x_not_exd_right_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x -> ~ succ (CHID m mr x tx px max) zero x ->
  (forall (d:dart), exd m d -> ~ right_dart mr px d).
Proof.
intros m mr x tx px max Hmap Hexd Hsucc.
generalize (x_CHID_8 m mr x tx px max Hmap Hexd); intro H.
assert (H0 : forall (A B : Prop), (A -> B) -> (~ B -> ~ A)).
 intros A B H0 H1 H2; apply H1; apply H0; apply H2.
assert (H1 : ~ succ (CHID m mr x tx px max) zero x ->
 ~ (exists d:dart, exd m d /\ right_dart mr px d)).
 apply H0; exact H.
generalize (H1 Hsucc); clear H H0 H1 Hmap Hexd Hsucc.
intros H d H1 H2; apply H; exists d; intuition.
Qed.

Lemma black_dart_CHID_not_exd_left_dart_not_exd_right_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m x ->  max <> nil ->
  black_dart (CHID m mr x tx px max) x ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d /\ ~ right_dart mr px d).
Proof.
intros m mr x tx px max Hqh Hexd Hneq [H1 [H2 [H3 H4]]].
intros d Hd; split.
apply (not_pred_one_x_not_exd_left_dart m mr x tx px max); try assumption.
apply (not_succ_zero_x_not_exd_right_dart m mr x tx px max); try assumption.
Qed.

(* ========================== *)

Lemma exd_max_exd_left_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max -> x <> max -> exd (CHID m mr x tx px max) max ->
  (exists d:dart, exd m d /\ left_dart mr px d).
Proof.
intros m mr x tx px max Hmap Hexd Hneq.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; intuition.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 generalize (IHm Hmap Hexd2); clear IHm; intro IHm.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *; intro H.
elim H; clear H.
 intro H; contradiction.
 intro H; generalize (IHm H); clear IHm.
 intro IHm; elim IHm; clear IHm.
 intros da [Hda1 Hda2].
 apply (@or_intror (d = da)) in Hda1.
 exists da; do 2 (split; try assumption).
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *; intro H.
exists d; split; [left; trivial | assumption].
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *; intro H.
elim H; clear H.
 intro H; contradiction.
 intro H; generalize (IHm H); clear IHm.
 intro IHm; elim IHm; clear IHm.
 intros da [Hda1 Hda2].
 apply (@or_intror (d = da)) in Hda1.
 exists da; do 2 (split; try assumption).
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *; intro H.
elim H; clear H.
 intro H; contradiction.
 intro H; generalize (IHm H); clear IHm.
 intro IHm; elim IHm; clear IHm.
 intros da [Hda1 Hda2].
 apply (@or_intror (d = da)) in Hda1.
 exists da; do 2 (split; try assumption).
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *; intro H.
elim H; clear H.
 intro H; contradiction.
 intro H; generalize (IHm H); clear IHm.
 intro IHm; elim IHm; clear IHm.
 intros da [Hda1 Hda2].
 apply (@or_intror (d = da)) in Hda1.
 exists da; do 2 (split; try assumption).
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; intro H.
generalize (IHm H); clear IHm.
intro IHm; elim IHm; clear IHm.
intros da [Hda1 Hda2].
apply (@or_intror (d = da)) in Hda1.
exists da; do 2 (split; try assumption).
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
simpl in *; intro H.
elim H; clear H.
 intro H; contradiction.
 intro H; generalize (IHm H); clear IHm.
 intro IHm; elim IHm; clear IHm.
 intros da [Hda1 Hda2].
 apply (@or_intror (d = da)) in Hda1.
 exists da; do 2 (split; try assumption).
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 Hmap4]]]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; intro H.
apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma not_exd_max_not_exd_left_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> ~ exd m max ->
  ~ exd (CHID m mr x tx px max) max ->
  (forall (d:dart), exd m d -> ~ left_dart mr px d).
Proof.
intros m mr x tx px max Hmap Hexd Hmax.
generalize (max_CHID_6 m mr x tx px max Hmap Hexd); intro H.
assert (H0 : forall (A B : Prop), (A -> B) -> (~ B -> ~ A)).
 intros A B H0 H1 H2; apply H1; apply H0; apply H2.
assert (H1 : ~ exd (CHID m mr x tx px max) max ->
 ~ (exists d:dart, exd m d /\ left_dart mr px d)).
 apply H0; exact H.
generalize (H1 Hmax); clear H H0 H1 Hmap Hexd Hmax.
intros H d H1 H2; apply H; exists d; intuition.
Qed.
