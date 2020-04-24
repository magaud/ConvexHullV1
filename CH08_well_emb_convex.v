(* ================================== *)
(* ===== CH08_well_emb_convex.v ===== *)
(* ================================== *)

Require Export CH07_inv_hmap_inv_poly.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma fpoint_x :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  ~ exd m x -> fpoint (CHID m mr x tx px max) x = px.
Proof.
intros m mr x tx px max Hexd.
induction m.
 (* Cas 1 : m = V *)
 simpl; elim (eq_dart_dec x x).
  intro H; trivial.
  intro H; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim (eq_dart_dec d x).
 intro H; subst x; tauto.
 intro H; apply IHm; tauto.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max x).
 intro H1; trivial.
 elim (eq_dart_dec d x).
 intro H2; subst x; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim (eq_dart_dec d x).
 intro H; subst x; tauto.
 intro H; apply IHm; tauto.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim (eq_dart_dec d x).
 intro H; subst x; tauto.
 intro H; apply IHm; tauto.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d x).
 intro H; subst x; tauto.
 intro H; apply IHm; tauto.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; apply IHm; tauto.
(* ======= *)
   intros Hred Hblue.
(* == 7 == *)
simpl in *.
elim (eq_dart_dec d x).
 intro H; subst x; tauto.
 intro H; apply IHm; tauto.
(* ======= *)
 (* Cas 3 : m = L *)
induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; apply IHm; tauto.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
Qed.

Lemma fpoint_max :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  ~ exd m max -> exd (CHID m mr x tx px max) max -> fpoint (CHID m mr x tx px max) max = px.
Proof.
intros m mr x tx px max.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; elim (eq_dart_dec x max).
  intro H; trivial.
  intros H H1 H2; elim H2; clear H2.
   intro H2; subst max; tauto.
   intro H2; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl in *.
elim (eq_dart_dec d max).
 intros H H1 H2; subst max; tauto.
 intros H H1 H2; apply IHm; tauto.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max max).
 intros H H1 H2; trivial.
 intros H H1 H2; tauto.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim (eq_dart_dec d max).
 intros H H1 H2; subst max; tauto.
 intros H H1 H2; apply IHm; tauto.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim (eq_dart_dec d max).
 intros H H1 H2; subst max; tauto.
 intros H H1 H2; apply IHm; tauto.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d max).
 intros H H1 H2; subst max; tauto.
 intros H H1 H2; apply IHm; tauto.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *; intros H1 H2; apply IHm; tauto.
(* ======= *)
   intros Hred Hblue.
(* == 7 == *)
simpl in *.
elim (eq_dart_dec d max).
 intros H H1 H2; subst max; tauto.
 intros H H1 H2; apply IHm; tauto.
(* ======= *)
 (* Cas 3 : m = L *)
induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl in *; apply IHm; tauto.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
apply IHm; assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
simpl in *; apply IHm; tauto.
(* ======== *)
Qed.

(* ========================== *)

Lemma inv_fpoint_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  d <> x -> d <> max -> exd m d -> exd (CHID m mr x tx px max) d ->
  fpoint m d = fpoint (CHID m mr x tx px max) d.
Proof.
intros m mr x tx px max y Hneq1 Hneq2.
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
elim (eq_dart_dec d y).
 intros H H1 H2; trivial.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl in *.
elim (eq_dart_dec max y).
 intro Hmax; subst y; tauto.
elim (eq_dart_dec d y).
 intros H Hmax H1 H2; trivial.
 intros H Hmax H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
  intro H2; elim H2; clear H2.
  intro H2; subst d; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl in *.
elim (eq_dart_dec d y).
 intros H H1 H2; trivial.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl in *.
elim (eq_dart_dec d y).
 intros H H1 H2; trivial.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl in *.
elim (eq_dart_dec d y).
 intros H H1 H2; trivial.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
 intros H1 H2; apply IHm; tauto.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
simpl in *.
elim (eq_dart_dec d y).
 intros H H1 H2; subst y.
 assert (H : ~ exd (CHID m mr x tx px max) d).
  apply red_dart_CHID_18; try assumption.
   apply not_invisible_visible in H_ccw; assumption.
   unfold right_dart in H_right.
apply not_invisible_visible.
apply not_invisible_visible in H_ccw.
intuition.
 contradiction.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 intro H1; apply IHm; tauto.
(* ======= *)
   intros Hred Hblue.
(* == 7 == *)
simpl in *.
elim (eq_dart_dec d y).
 intros H H1 H2; trivial.
 intros H H1 H2.
 elim H1; clear H1.
  intro H1; subst y; tauto.
 elim H2; clear H2.
  intro H2; subst y; tauto.
 intros H1 H2; apply IHm; tauto.
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
simpl in *; apply IHm; assumption.
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
(* ======= ########## ======= *)
(* ========================== *)

Lemma succ_zero_x_or_blue_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> submap m mr -> 
  succ (CHID m mr x tx px max) zero d ->
  (d = x) \/ ((blue_dart mr d) /\ (ccw (fpoint mr d) (fpoint mr (A mr zero d)) px)) \/ (left_dart mr px d).
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hsub.
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
unfold succ in *; simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ in *; simpl in *.
elim (eq_dart_dec d da).
 intros Heq Hmax; subst d.
 right; right; assumption.
 intro Heq; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold succ in *; simpl in *.
elim (eq_dart_dec x da).
 intros Heq Hneq; subst x; left; trivial.
 intro Heq; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 da).
 intros Heq Hneq; subst da; right; left; split.
  apply succ_zero_blue_dart; try assumption.
  unfold succ; rewrite Hsub2; assumption.
  rewrite Hsub2; assumption.
 intro Heq; apply IHm; assumption.
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

Lemma pred_zero_max_or_red_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> submap m mr -> 
  pred (CHID m mr x tx px max) zero d ->
  (d = max) \/ ((red_dart mr d) /\ (ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px)) \/ (right_dart mr px d).
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hsub.
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
unfold pred in *; simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold pred in *; simpl in *.
elim (eq_dart_dec max da).
 intros Heq Hneq; subst max; left; trivial.
 intro Heq; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold pred in *; simpl in *.
elim (eq_dart_dec d da).
 intros Heq Hmax; subst d.
 right; right; assumption.
 intro Heq; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 da).
 intros Heq Hneq; subst da; right; left; split.
  apply pred_zero_red_dart; try assumption.
  unfold pred; rewrite Hsub3; assumption.
  rewrite Hsub3; assumption.
 intro Heq; apply IHm; assumption.
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

Lemma succ_one_max_or_red_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> submap m mr -> 
  succ (CHID m mr x tx px max) one d ->
  (d = max) \/ ((red_dart mr d) /\ (invisible mr d px)) \/ (right_dart mr px d).
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hsub.
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
unfold succ in *; simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold succ in *; simpl in *.
elim (eq_dart_dec max da).
 intros Heq Hneq; subst max; left; trivial.
 intro Heq; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold succ in *; simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
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
unfold succ; simpl in *.
elim (eq_dart_dec d0 da).
 intros Heq Hneq; subst da; right; left; split.
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub2; assumption.
  assumption.
 intro Heq; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
unfold succ; simpl in *.
elim (eq_dart_dec d0 da).
 intros Heq Hneq; subst da; right; right.
 unfold right_dart; split; [idtac|split].
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub2; assumption.
  apply not_invisible_visible; assumption.
  rewrite Hsub2; assumption.
 intro Heq; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

Lemma pred_one_x_or_blue_dart :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  inv_hmap mr -> inv_poly mr -> submap m mr -> 
  pred (CHID m mr x tx px max) one d ->
  (d = x) \/ ((blue_dart mr d) /\ ((invisible mr d px) \/ (invisible mr (A_1 mr one d) px))).
Proof.
intros m mr x tx px max da Hmr1 Hmr2 Hsub.
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
unfold pred in *; simpl in *; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
unfold pred in *; simpl in *.
elim (eq_dart_dec x da).
 intros Heq Hneq; subst x; left; trivial.
 intro Heq; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
unfold pred in *; simpl in *; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in *.
 destruct Hsub as [Hsub [Hsub2 Hsub3]].
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
elim (eq_dart_dec d1 da).
 intros Heq Hneq; subst da; right; split.
  apply pred_one_blue_dart; try assumption.
  unfold pred; rewrite Hsub3; assumption.
  right; rewrite Hsub3; assumption.
 intro Heq; apply IHm; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
unfold pred; simpl in *.
elim (eq_dart_dec d1 da).
 intros Heq Hneq; subst da; right; split.
  apply pred_one_blue_dart; try assumption.
  unfold pred; rewrite Hsub3; assumption.
  left; assumption.
 intro Heq; apply IHm; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
apply IHm; assumption.
(* ======== *)
Qed.

(* ========================== *)

Lemma blue_dart_CHID_13_bis :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart)(d:dart),
  submap m mr -> d <> x -> blue_dart mr d ->
  invisible mr (A_1 mr one d) px ->
  A_1 m one d = A_1 (CHID m mr x tx px max) one d.
Proof.
intros m mr x tx px max y Hsub Hneq Hblue Hccw.
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
rewrite Hsub2 in Hccw; contradiction.
intro H; apply IHm; assumption.
(* ======== *)
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem well_emb_CHID :
  forall (mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  x <> nil -> max <> nil -> x <> max -> ~ exd mr x ->  ~ exd mr max ->
  (forall d:dart, exd mr d -> (fpoint mr d) <> px) ->
  well_emb (CHID mr mr x tx px max).
Proof.
intros mr x tx px max Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hneq1 Hneq2 Hneq3 Hexd1 Hexd2 Hpx.
unfold well_emb; intros da Hda; repeat split.
 (* succ CHID zero da *)
 intro Hsucc.
 assert (Hsub : submap mr mr).
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
 generalize (succ_zero_x_or_blue_dart mr mr x tx px max da Hmr1 Hmr2 Hsub Hsucc).
 intro H; elim H; clear H; intro H; try subst da.
  (* da = x *)
  generalize (succ_zero_x_exd_right_dart mr mr x tx px max Hmr1 Hexd1 Hsucc).
  intro H; elim H; clear H; intros d [Hd1 Hd2].
  assert (H0 : A (CHID mr mr x tx px max) zero x = d).
   apply x_CHID_7; try assumption.
  rewrite H0.
  rewrite fpoint_x; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  apply neq_sym_point; apply Hpx; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H0.
  apply succ_exd_A; try assumption.
  apply inv_hmap_CHID; try assumption.
 elim H; clear H; intro H.
  (* blue_dart mr da /\ (ccw (fpoint mr d) (fpoint mr (A mr zero d)) px) *)
  destruct H as [H1 H2].
  assert (H0 : exd mr da).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H1; intuition.
  assert (H : A mr zero da = A (CHID mr mr x tx px max) zero da).
   apply blue_dart_CHID_4; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb1; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in H1; intuition.
  apply succ_exd_A; try assumption.
  unfold blue_dart in H1; intuition.
  rewrite H.
  apply succ_exd_A; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  (* left_dart mr px da *)
  destruct H as [H1 [H2 H3]].
  assert (H0 : exd mr da).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H1; intuition.
  assert (H : A (CHID mr mr x tx px max) zero da = max).
   apply blue_dart_CHID_11; try assumption.
   apply (exd_not_exd_neq mr); try assumption.
  rewrite H.
  rewrite fpoint_max; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  apply Hpx; try assumption.
  apply (exd_not_exd_neq mr); assumption.
  apply (exd_not_exd_neq mr); assumption.
  apply max_CHID_6; try assumption.
  exists da; split; unfold left_dart; intuition.
 (* pred CHID zero da *)
 intro Hpred.
 assert (Hsub : submap mr mr).
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
 generalize (pred_zero_max_or_red_dart mr mr x tx px max da Hmr1 Hmr2 Hsub Hpred).
 intro H; elim H; clear H; intro H; try subst da.
  (* da = max *)
  generalize (exd_max_exd_left_dart mr mr x tx px max Hmr1 Hexd2 Hneq3 Hda).
  intro H; elim H; clear H; intros d [Hd1 Hd2].
  assert (H0 : A_1 (CHID mr mr x tx px max) zero max = d).
   apply max_CHID_9; try assumption.
  rewrite H0.
  rewrite fpoint_max; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  apply neq_sym_point; apply Hpx; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H0.
  apply pred_exd_A_1; try assumption.
  apply inv_hmap_CHID; try assumption.
 elim H; clear H; intro H.
  (* red_dart mr da /\ (ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) px) *)
  destruct H as [H1 H2].
  assert (H0 : exd mr da).
   apply succ_exd with one; try assumption.
   unfold red_dart in H1; intuition.
  assert (H : A_1 mr zero da = A_1 (CHID mr mr x tx px max) zero da).
   apply red_dart_CHID_7; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb2; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold red_dart in H1; intuition.
  apply pred_exd_A_1; try assumption.
  unfold red_dart in H1; intuition.
  rewrite H.
  apply pred_exd_A_1; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  (* right_dart mr px da *)
  destruct H as [H1 [H2 H3]].
  assert (H0 : exd mr da).
   apply succ_exd with one; try assumption.
   unfold red_dart in H1; intuition.
  assert (H : A_1 (CHID mr mr x tx px max) zero da = x).
   apply red_dart_CHID_15; try assumption.
   apply (exd_not_exd_neq mr); try assumption.
  rewrite H.
  rewrite fpoint_x; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  apply Hpx; try assumption.
  apply (exd_not_exd_neq mr); assumption.
  apply (exd_not_exd_neq mr); assumption.
 (* succ CHID one da *)
 intro Hsucc.
 assert (Hsub : submap mr mr).
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
 generalize (succ_one_max_or_red_dart mr mr x tx px max da Hmr1 Hmr2 Hsub Hsucc).
 intro H; elim H; clear H; intro H; try subst da.
  (* da = max *)
  generalize (exd_max_exd_left_dart mr mr x tx px max Hmr1 Hexd2 Hneq3 Hda).
  intro H; elim H; clear H; intros d [Hd1 Hd2].
  assert (H0 : A (CHID mr mr x tx px max) one max = x).
   apply max_CHID_7; try assumption.
   exists d; split; assumption.
  rewrite H0.
  rewrite fpoint_max; try assumption.
  rewrite fpoint_x; try assumption; trivial.
 elim H; clear H; intro H.
  (* red_dart mr da /\ invisible mr da px *)
  destruct H as [H1 H2].
  assert (H0 : exd mr da).
  apply succ_exd with one; try assumption.
  unfold red_dart in H1; intuition.
  assert (H : A mr one da = A (CHID mr mr x tx px max) one da).
   apply red_dart_CHID_4; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb3; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  rewrite H.
  apply succ_exd_A; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  (* right_dart mr px da *)
  destruct H as [H1 [H2 H3]].
  assert (H0 : exd mr da).
  apply succ_exd with one; try assumption.
  unfold red_dart in H1; intuition.
  assert (H : A mr one da = A (CHID mr mr x tx px max) one da).
   apply red_dart_CHID_12; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb3; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  apply succ_exd_A; try assumption.
  unfold red_dart in H1; intuition.
  rewrite H.
  apply succ_exd_A; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
 (* pred CHID one da *)
 intro Hpred.
 assert (Hsub : submap mr mr).
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
 generalize (pred_one_x_or_blue_dart mr mr x tx px max da Hmr1 Hmr2 Hsub Hpred).
 intro H; elim H; clear H; intro H; try subst da.
  (* da = x *)
  generalize (pred_one_x_exd_left_dart mr mr x tx px max Hmr1 Hexd1 Hpred).
  intro H; elim H; clear H; intros d [Hd1 Hd2].
  assert (H0 : A_1 (CHID mr mr x tx px max) one x = max).
   apply x_CHID_9; try assumption.
   exists d; split; assumption.
  rewrite H0.
  rewrite fpoint_x; try assumption.
  rewrite fpoint_max; try assumption; trivial.
  apply max_CHID_6; try assumption.
   exists d; split; assumption.
 destruct H as [H1 H2].
 elim H2; clear H2; intro H2.
  (* blue_dart mr da /\ invisible mr da px) *)
  assert (H0 : exd mr da).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H1; intuition.
  assert (H : A_1 mr one da = A_1 (CHID mr mr x tx px max) one da).
   apply blue_dart_CHID_7; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb4; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  rewrite H.
  apply pred_exd_A_1; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  (* blue_dart mr da /\ invisible mr (A_1 mr one da) px) *)
  assert (H0 : exd mr da).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H1; intuition.
  assert (H : A_1 mr one da = A_1 (CHID mr mr x tx px max) one da).
   apply blue_dart_CHID_13_bis; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite <- H.
  rewrite <- inv_fpoint_CHID; try assumption.
  rewrite <- inv_fpoint_CHID; try assumption.
  generalize (Hmr3 da H0).
  intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
  apply Hemb4; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H1; intuition.
  rewrite H.
  apply pred_exd_A_1; try assumption.
  apply inv_hmap_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
 (* forall db:dart *)
 intros db Hdb H1 H2 H3.
 generalize Hda; intro Hda2.
 apply exd_CHID_exd_m_or_x_or_max in Hda2.
 generalize Hdb; intro Hdb2.
 apply exd_CHID_exd_m_or_x_or_max in Hdb2.
 elim Hda2; clear Hda2; intro Hda2.
  (* exd mr da *)
  elim Hdb2; clear Hdb2; intro Hdb2.
   (* exd mr db *)
   rewrite <- inv_fpoint_CHID; try assumption.
   rewrite <- inv_fpoint_CHID; try assumption.
   generalize (Hmr3 da Hda2).
   intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
   apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
(* db <> A mr one da *)
generalize (Hmr2 da Hda2); intro Hda3.
elim Hda3; clear Hda3; intro Hda3.
 unfold black_dart, succ in Hda3.
 destruct Hda3 as [Ha [Hb [Hc Hd]]].
 apply not_neq_eq in Hb; rewrite Hb.
 apply exd_not_nil with mr; try assumption.
elim Hda3; clear Hda3; intro Hda3.
 unfold blue_dart, succ in Hda3.
 destruct Hda3 as [Ha [Hb [Hc Hd]]].
 apply not_neq_eq in Hb; rewrite Hb.
 apply exd_not_nil with mr; try assumption.
 elim (invisible_dec mr da px); intro Hda4.
  assert (H : A mr one da = A (CHID mr mr x tx px max) one da).
   apply red_dart_CHID_4; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite H; assumption.
 elim (invisible_dec mr (A mr one da) px); intro Hda5.
  assert (H : A mr one da = A (CHID mr mr x tx px max) one da).
   apply red_dart_CHID_12; try assumption.
   apply submap_2_submap; try assumption.
   apply submap_2_refl.
   apply exd_not_exd_neq with mr; try assumption.
   apply not_invisible_visible; assumption.
  rewrite H; assumption.
  assert (H : ~ exd (CHID mr mr x tx px max) da).
   apply red_dart_CHID_18; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply not_invisible_visible; assumption.
   apply not_invisible_visible; assumption.
  contradiction.
(* db <> A_1 mr one da *)
generalize (Hmr2 da Hda2); intro Hda3.
elim Hda3; clear Hda3; intro Hda3.
 unfold black_dart, pred in Hda3.
 destruct Hda3 as [Ha [Hb [Hc Hd]]].
 apply not_neq_eq in Hd; rewrite Hd.
 apply exd_not_nil with mr; try assumption.
elim Hda3; clear Hda3; intro Hda3.
 elim (invisible_dec mr da px); intro Hda4.
  assert (H : A_1 mr one da = A_1 (CHID mr mr x tx px max) one da).
   apply blue_dart_CHID_7; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  rewrite H; assumption.
 elim (invisible_dec mr (A_1 mr one da) px); intro Hda5.
  assert (H : A_1 mr one da = A_1 (CHID mr mr x tx px max) one da).
   apply blue_dart_CHID_13; try assumption.
   apply submap_2_submap; try assumption.
   apply submap_2_refl.
   apply exd_not_exd_neq with mr; try assumption.
   apply not_invisible_visible; assumption.
  rewrite H; assumption.
  elim (eq_dart_dec db (A_1 mr one da));
  intro Heq; [idtac|assumption].
  assert (H0 : da = (A mr one db)).
   rewrite Heq; apply A_A_1; try assumption.
   apply pred_exd_A_1; try assumption.
   unfold blue_dart in Hda3; intuition.
  assert (H : ~ exd (CHID mr mr x tx px max) db).
   apply red_dart_CHID_18; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   rewrite Heq; apply blue_A_1_red in Hda3; try assumption.
   apply not_invisible_visible; rewrite Heq; assumption.
   apply not_invisible_visible; rewrite <- H0; assumption.
  contradiction.
 unfold red_dart, pred in Hda3.
 destruct Hda3 as [Ha [Hb [Hc Hd]]].
 apply not_neq_eq in Hd; rewrite Hd.
 apply exd_not_nil with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
  elim Hdb2; clear Hdb2; intro Hdb2; subst db.
   (* db = x *)
   rewrite fpoint_x; try assumption.
   rewrite <- inv_fpoint_CHID; try assumption.
   apply Hpx; try assumption.
   apply (exd_not_exd_neq mr); assumption.
   apply (exd_not_exd_neq mr); assumption.
   (* db = max *)
   rewrite fpoint_max; try assumption.
   rewrite <- inv_fpoint_CHID; try assumption.
   apply Hpx; try assumption.
   apply (exd_not_exd_neq mr); assumption.
   apply (exd_not_exd_neq mr); assumption.
 elim Hda2; clear Hda2; intro Hda2; subst da.
  (* da = x *)
  elim Hdb2; clear Hdb2; intro Hdb2.
   (* exd mr db *)
   rewrite fpoint_x; try assumption.
   rewrite <- inv_fpoint_CHID; try assumption.
   apply neq_sym_point; apply Hpx; try assumption.
   apply (exd_not_exd_neq mr); assumption.
  elim Hdb2; clear Hdb2; intro Hdb2; subst db.
   (* db = x *)
   intuition.
   (* db = max *)
   generalize (exd_max_exd_left_dart mr mr x tx px max Hmr1 Hexd2 Hneq3 Hdb).
   intro H; elim H; clear H; intros d [Hd1 Hd2].
   assert (H0 : A_1 (CHID mr mr x tx px max) one x = max).
    apply x_CHID_9; try assumption.
    exists d; split; assumption.
   rewrite H0 in H3; intuition.
  (* da = max *)
  elim Hdb2; clear Hdb2; intro Hdb2.
   (* exd mr db *)
   rewrite fpoint_max; try assumption.
   rewrite <- inv_fpoint_CHID; try assumption.
   apply neq_sym_point; apply Hpx; try assumption.
   apply (exd_not_exd_neq mr); assumption.
  elim Hdb2; clear Hdb2; intro Hdb2; subst db.
   (* db = x *)
   generalize (exd_max_exd_left_dart mr mr x tx px max Hmr1 Hexd2 Hneq3 Hda).
   intro H; elim H; clear H; intros d [Hd1 Hd2].
   assert (H0 : A (CHID mr mr x tx px max) one max = x).
    apply max_CHID_7; try assumption.
    exists d; split; assumption.
   rewrite H0 in H2; intuition.
   (* db = max *)
   intuition.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem inv_convex_CHID :
  forall (mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  x <> nil -> max <> nil -> x <> max -> ~ exd mr x ->  ~ exd mr max ->
  convex (CHID mr mr x tx px max).
Proof.
intros mr x tx px max Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hneq1 Hneq2 Hneq0 Hexd1 Hexd2.
unfold convex.
intros da Hda1 Hda2 db Hdb1 Hp1 Hp2.
(**)
generalize Hda2; intros [Hda3 [H2 [H3 H4]]]; clear H2 H3 H4.
apply succ_zero_x_or_blue_dart in Hda3; try assumption.
2:apply submap_2_submap; solve [assumption | apply submap_2_refl].
elim Hda3; clear Hda3; intro Hda3; try subst da.
 (* da = x *)
 rewrite fpoint_x in *; try assumption.
 generalize Hda2; intros [Hda3 [H2 [H3 H4]]]; clear H2 H3 H4.
 apply succ_zero_x_exd_right_dart in Hda3; try assumption.
 elim Hda3; clear Hda3; intros d [Hd1 [Hd2 [Hd3 Hd4]]].
 assert (Hda3 : A (CHID mr mr x tx px max) zero x = d).
  apply x_CHID_7; try assumption.
  unfold right_dart; intuition.
 rewrite Hda3 in *.
 assert (Hd5 : fpoint mr d = fpoint (CHID mr mr x tx px max) d).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply red_dart_CHID_11; try assumption.
 rewrite <- Hd5 in *.
(**)
generalize Hd3; clear Hd3.
unfold visible; elim blue_dart_dec; intro Hblue.
 apply red_not_blue in Hd2; try assumption; contradiction.
 intro Hd3; clear Hblue.
generalize Hd4; clear Hd4.
unfold invisible; elim blue_dart_dec; intro Hblue.
 2:apply red_A_blue in Hd2; try assumption; contradiction.
 intro Hccw; elim Hccw; clear Hccw.
 2:intro Hccw;
 assert (H1 : exd mr (A mr one d))
   by (apply succ_exd_A; solve [assumption | unfold red_dart in Hd2; intuition]);
  assert (H2 : exd mr (A mr zero (A mr one d)))
   by (apply succ_exd_A; solve [assumption | unfold blue_dart in Hblue; intuition]);
  assert (H3 : fpoint mr (A mr one d) <> fpoint mr (A mr zero (A mr one d))) by (apply well_emb_A_zero; solve [assumption | unfold blue_dart in Hblue; intuition]);
  generalize (Hmr4 (A mr one d) (A mr zero (A mr one d)) H1 H2 H3); intro H0; contradiction.
  
  intro Hd4; clear Hblue.
(**)
generalize Hdb1; intro Hdb2.
apply exd_CHID_exd_m_or_x_or_max in Hdb2.
elim Hdb2; clear Hdb2; intro Hdb2.
 (* exd mr db *)
 assert (Hdb3 : fpoint mr db = fpoint (CHID mr mr x tx px max) db).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
 rewrite <- Hdb3 in *.
(**)
elim (eq_point_dec_2 (fpoint mr db) (fpoint mr (A mr zero (A mr one d)))); intro Hp3.
 assert (H1 : (fpoint mr d) = (fpoint mr (A mr one d))).
  apply (well_emb_A_one mr d); try assumption.
  unfold red_dart in Hd2; intuition.
 apply ccw_axiom_1; apply ccw_axiom_1.
 rewrite Hp3; rewrite H1; assumption. 
(**)
elim (eq_point_dec_2 (fpoint mr db) (fpoint mr (A_1 mr zero d))); intro Hp4.
 apply ccw_axiom_1; rewrite Hp4; assumption. 
(**)
elim (eq_point_dec_2 (fpoint mr (A_1 mr zero d)) (fpoint mr (A mr zero (A mr one d)))); intro Hp5.
 assert False; [idtac|intuition].
 assert (Hccw1 : ccw (fpoint mr (A_1 mr zero d)) (fpoint mr d) (fpoint mr db)).
  assert (H1 : d = (A mr zero (A_1 mr zero d))).
   apply A_A_1; try assumption.
   apply pred_exd_A_1; try assumption.
   unfold red_dart in Hd2; intuition.
  pattern d at 2; rewrite H1.
  assert (H2 : exd mr (A_1 mr zero d)).
   apply pred_exd_A_1; try assumption.
   unfold red_dart in Hd2; intuition.
  assert (H3 : blue_dart mr (A_1 mr zero d)).
   apply red_A_1_blue; try assumption.
  apply (Hmr5 (A_1 mr zero d) H2 H3 db Hdb2); try assumption.
  rewrite <- H1; assumption.
 assert (Hccw2 : ccw (fpoint mr d) (fpoint mr (A mr zero (A mr one d))) (fpoint mr db)).
  assert (H1 : (fpoint mr d) = (fpoint mr (A mr one d))).
   apply (well_emb_A_one mr d); try assumption.
   unfold red_dart in Hd2; intuition.
  assert (H2 : exd mr (A mr one d)).
   apply succ_exd_A; try assumption.
   unfold red_dart in Hd2; intuition.
  assert (H3 : blue_dart mr (A mr one d)).
   apply red_A_blue; try assumption.
  rewrite H1; apply Hmr5; try assumption.
  rewrite <- H1; assumption.
 apply axiom_orientation_1 in Hccw2; rewrite Hp5 in Hccw1.
 apply axiom_orientation_4 in Hccw2; contradiction.
(**)
apply ccw_axiom_1; apply ccw_axiom_1.
apply ccw_axiom_5 with (fpoint mr (A_1 mr zero d)) (fpoint mr (A mr zero (A mr one d))).
(**)
assert (H1 : (fpoint mr d) = (fpoint mr (A mr one d))).
 apply (well_emb_A_one mr d); try assumption.
 unfold red_dart in Hd2; intuition.
assert (H2 : exd mr (A mr one d)).
 apply succ_exd_A; try assumption.
 unfold red_dart in Hd2; intuition.
assert (H3 : blue_dart mr (A mr one d)).
 apply red_A_blue; try assumption.
rewrite H1; apply Hmr5; try assumption.
rewrite <- H1; assumption.
(**)
assert (H1 : (fpoint mr d) = (fpoint mr (A mr one d))).
 apply (well_emb_A_one mr d); try assumption.
 unfold right_dart, red_dart in Hd2; intuition.
assert (H2 : exd mr (A mr one d)).
 apply succ_exd_A; try assumption.
 unfold red_dart in Hd2; intuition.
assert (H3 : blue_dart mr (A mr one d)).
 apply red_A_blue; try assumption.
assert (H4 : exd mr (A_1 mr zero d)).
 apply pred_exd_A_1; try assumption.
 unfold red_dart in Hd2; intuition.
rewrite H1; apply Hmr5; try assumption.
rewrite <- H1; apply neq_sym_point.
apply well_emb_A_1_zero; try assumption.
unfold red_dart in Hd2; intuition.
(**)
assert (H1 : (fpoint mr d) = (fpoint mr (A mr one d))).
 apply (well_emb_A_one mr d); try assumption.
 unfold right_dart, red_dart in Hd2; intuition.
rewrite H1; assumption.
(**)
apply ccw_axiom_1.
assert (H1 : d = (A mr zero (A_1 mr zero d))).
 apply A_A_1; try assumption.
 apply pred_exd_A_1; try assumption.
 unfold red_dart in Hd2; intuition.
pattern d at 2; rewrite H1.
assert (H2 : exd mr (A_1 mr zero d)).
 apply pred_exd_A_1; try assumption.
 unfold red_dart in Hd2; intuition.
assert (H3 : blue_dart mr (A_1 mr zero d)).
 apply red_A_1_blue; try assumption.
apply Hmr5; try assumption.
rewrite <- H1; assumption.
(**)
apply ccw_axiom_1; apply ccw_axiom_1; assumption.
 (* db = x \/ db = max *)
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x in *; intuition.
  rewrite fpoint_max in *; intuition.
(**)
elim Hda3; clear Hda3; intro Hda3.
 (* blue_dart mr da /\ ccw (fpoint mr da) (fpoint mr (A mr zero da)) px *)
 destruct Hda3 as [Hda3 Hda4].
 assert (Hda5 : fpoint mr da = fpoint (CHID mr mr x tx px max) da).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
 rewrite <- Hda5 in *.
 assert (Hda6 : A mr zero da = A (CHID mr mr x tx px max) zero da).
  apply blue_dart_CHID_4; try assumption.
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
 rewrite <- Hda6 in *.
 assert (Hda7 : fpoint mr (A mr zero da) = fpoint (CHID mr mr x tx px max) (A mr zero da)).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd_A; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply succ_exd_A; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply red_dart_CHID_3; try assumption.
  apply blue_A_red; assumption.
  unfold invisible; elim blue_dart_dec.
   intro Hblue.
   apply blue_A_red in Hda3; try assumption.
   apply red_not_blue in Hda3; contradiction.
   intro Hblue; left.
   rewrite <- A_1_A; try assumption.
   apply succ_exd with zero; try assumption.
   unfold blue_dart in Hda3; intuition.
   apply succ_exd_A; try assumption.
   unfold blue_dart in Hda3; intuition.
   apply succ_exd_A; try assumption.
   unfold blue_dart in Hda3; intuition.
 rewrite <- Hda7 in *.
(**)
generalize Hdb1; intro Hdb2.
apply exd_CHID_exd_m_or_x_or_max in Hdb2.
elim Hdb2; clear Hdb2; intro Hdb2.
 (* exd mr db *)
 assert (Hdb3 : fpoint mr db = fpoint (CHID mr mr x tx px max) db).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
 rewrite <- Hdb3 in *.
(**)
assert (H1 : exd mr da).
 apply succ_exd with zero; try assumption.
 unfold blue_dart in Hda3; intuition.
apply Hmr5; try assumption.
 (* db = x \/ db = max *)
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x in *; intuition.
  rewrite fpoint_max in *; intuition.
 (* left_dart mr da *)
 destruct Hda3 as [Hda3 [Hda4 Hda5]].
 assert (Hda6 : fpoint mr da = fpoint (CHID mr mr x tx px max) da).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
 rewrite <- Hda6 in *.
 assert (Hda7 : A (CHID mr mr x tx px max) zero da = max).
  apply blue_dart_CHID_11; try assumption.
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
  apply exd_not_exd_neq with mr; try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
 rewrite Hda7 in *.
 assert (H0 : exd (CHID mr mr x tx px max) max).
  apply max_CHID_6; try assumption.
  exists da; split.
   apply succ_exd with zero; try assumption.
   unfold blue_dart in Hda3; intuition.
  unfold left_dart; intuition.
 rewrite fpoint_max in *; try assumption.
(**)
generalize Hda5; clear Hda5.
unfold visible; elim blue_dart_dec; intro Hblue.
 2:contradiction. 
 intro Hda5; clear Hblue.
generalize Hda4; clear Hda4.
unfold invisible; elim blue_dart_dec; intro Hblue.
 apply blue_A_1_red in Hda3; try assumption.
 apply red_not_blue in Hda3; contradiction.
 intro Hccw; elim Hccw; clear Hccw.
  intro Hda4; clear Hblue.
(**)
generalize Hdb1; intro Hdb2.
apply exd_CHID_exd_m_or_x_or_max in Hdb2.
elim Hdb2; clear Hdb2; intro Hdb2.
 (* exd mr db *)
 assert (Hdb3 : fpoint mr db = fpoint (CHID mr mr x tx px max) db).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
  apply exd_not_exd_neq with mr; try assumption.
 rewrite <- Hdb3 in *.
(**)
elim (eq_point_dec_2 (fpoint mr db) (fpoint mr (A_1 mr zero (A_1 mr one da)))); intro Hp3.
 assert (H1 : (fpoint mr da) = (fpoint mr (A_1 mr one da))).
  apply (well_emb_A_1_one mr da); try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  unfold blue_dart in Hda3; intuition.
 apply ccw_axiom_1; rewrite Hp3; rewrite H1; assumption.
(**)
elim (eq_point_dec_2 (fpoint mr db) (fpoint mr (A mr zero da))); intro Hp4.
 rewrite Hp4; assumption. 
(**)
elim (eq_point_dec_2 (fpoint mr (A mr zero da)) (fpoint mr (A_1 mr zero (A_1 mr one da)))); intro Hp5.
 assert False; [idtac|intuition].
 assert (Hccw1 : ccw (fpoint mr da) (fpoint mr (A mr zero da)) (fpoint mr db)).
  assert (H1 : exd mr da).
   apply succ_exd with zero; try assumption.
   unfold blue_dart in Hda3; intuition.
 apply Hmr5; try assumption.
 assert (Hccw2 : ccw (fpoint mr (A_1 mr zero (A_1 mr one da))) (fpoint mr da) (fpoint mr db)).
  assert (H1 : fpoint mr da = fpoint mr (A_1 mr one da)).
   apply (well_emb_A_1_one mr da); try assumption.
   apply succ_exd with zero; try assumption.
   unfold blue_dart in Hda3; intuition.
   unfold blue_dart in Hda3; intuition.
  rewrite H1.
  assert (H2 : (A_1 mr one da) = (A mr zero (A_1 mr zero (A_1 mr one da)))).
   apply A_A_1; try assumption.
   apply pred_exd_A_1; try assumption.
   unfold blue_dart in Hda3; intuition.
   apply pred_exd_A_1; try assumption.
   apply blue_A_1_red in Hda3; try assumption.
   unfold red_dart in Hda3; intuition.
  pattern (A_1 mr one da) at 2; rewrite H2.
  assert (H3 : exd mr (A_1 mr zero (A_1 mr one da))).
   apply pred_exd_A_1; try assumption.
   apply blue_A_1_red in Hda3; try assumption.
   unfold red_dart in Hda3; intuition.
  assert (H4 : blue_dart mr (A_1 mr zero (A_1 mr one da))).
   apply red_A_1_blue; try assumption.
   apply blue_A_1_red; try assumption.
  assert (H5 : exd mr (A mr zero (A_1 mr zero (A_1 mr one da)))).
   rewrite <- H2; apply pred_exd_A_1; try assumption.
   unfold blue_dart in Hda3; intuition.
  apply Hmr5; try assumption.
  rewrite <- H2; rewrite <- H1; assumption.
 apply axiom_orientation_1 in Hccw2; rewrite Hp5 in Hccw1.
 apply axiom_orientation_4 in Hccw2; contradiction.
(**)
apply ccw_axiom_5_bis with (fpoint mr (A mr zero da)) (fpoint mr (A_1 mr zero (A_1 mr one da))).
(**)
assert (H1 : (fpoint mr da) = (fpoint mr (A_1 mr one da))).
 apply (well_emb_A_1_one mr da); try assumption.
  apply succ_exd with zero; try assumption.
  unfold blue_dart in Hda3; intuition.
  unfold blue_dart in Hda3; intuition.
rewrite H1; assumption.
(**)
apply ccw_axiom_1; apply ccw_axiom_1.
assert (H1 : exd mr da).
 apply succ_exd with zero; try assumption.
 unfold blue_dart in Hda3; intuition.
assert (H2 : exd mr (A_1 mr zero (A_1 mr one da))).
 apply pred_exd_A_1; try assumption.
 apply blue_A_1_red in Hda3; try assumption.
 unfold red_dart in Hda3; intuition.
apply Hmr5; try assumption.
assert (H3 : (fpoint mr da) = (fpoint mr (A_1 mr one da))).
 apply (well_emb_A_1_one mr da); try assumption.
 unfold blue_dart in Hda3; intuition.
rewrite H3; apply neq_sym_point.
apply well_emb_A_1_zero; try assumption.
apply pred_exd_A_1; try assumption.
unfold blue_dart in Hda3; intuition.
apply blue_A_1_red in Hda3; try assumption.
unfold red_dart in Hda3; intuition.
apply neq_sym_point; assumption.
(**)
assert (H1 : fpoint mr da = fpoint mr (A_1 mr one da)).
 apply (well_emb_A_1_one mr da); try assumption.
 apply succ_exd with zero; try assumption.
 unfold blue_dart in Hda3; intuition.
 unfold blue_dart in Hda3; intuition.
rewrite H1.
assert (H2 : (A_1 mr one da) = (A mr zero (A_1 mr zero (A_1 mr one da)))).
 apply A_A_1; try assumption.
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hda3; intuition.
 apply pred_exd_A_1; try assumption.
 apply blue_A_1_red in Hda3; try assumption.
 unfold red_dart in Hda3; intuition.
pattern (A_1 mr one da) at 2; rewrite H2.
assert (H3 : exd mr (A_1 mr zero (A_1 mr one da))).
 apply pred_exd_A_1; try assumption.
 apply blue_A_1_red in Hda3; try assumption.
 unfold red_dart in Hda3; intuition.
assert (H4 : blue_dart mr (A_1 mr zero (A_1 mr one da))).
 apply red_A_1_blue; try assumption.
 apply blue_A_1_red; try assumption.
assert (H5 : exd mr (A mr zero (A_1 mr zero (A_1 mr one da)))).
 rewrite <- H2; apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hda3; intuition.
apply Hmr5; try assumption.
rewrite <- H2; rewrite <- H1; assumption.
(**)
assumption.
(**)
assert (H1 : exd mr da).
 apply succ_exd with zero; try assumption.
 unfold blue_dart in Hda3; intuition.
assert (H2 : exd mr (A mr zero da)).
 apply succ_exd_A; try assumption.
 unfold blue_dart in Hda3; intuition.
apply Hmr5; try assumption.
 (* db = x \/ db = max *)
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x in *; intuition.
  rewrite fpoint_max in *; intuition.

intro Hccw.
 assert (H1 : exd mr (A_1 mr zero (A_1 mr one da))).
   apply pred_exd_A_1; try assumption.
   apply blue_A_1_red in Hda3; try assumption.
   unfold red_dart in Hda3; intuition.
  assert (H2 : exd mr (A_1 mr one da)).
   apply pred_exd_A_1; try assumption.
   unfold blue_dart in Hda3; intuition.
  assert (H3 : fpoint mr (A_1 mr zero (A_1 mr one da)) <> fpoint mr (A_1 mr one da)).
   apply neq_sym_point.
   apply well_emb_A_1_zero; try assumption.
   apply blue_A_1_red in Hda3; try assumption.
   unfold red_dart in Hda3; intuition.
   
  generalize (Hmr4 (A_1 mr zero (A_1 mr one da)) (A_1 mr one da) H1 H2 H3).
  intro H; contradiction.
  
Qed.
