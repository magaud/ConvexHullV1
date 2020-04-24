(* ==================================== *)
(* ===== CH07_inv_hmap_inv_poly.v ===== *)
(* ==================================== *)

Require Export CH06_induction.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma map_left_dart_less :
  forall (m:fmap)(mr:fmap)(p:point)(da:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr ->
  inv_noalign_point mr p -> convex mr ->
  inv_hmap m -> ~ exd m da -> left_dart mr p da ->
  forall (d:dart), exd m d -> ~ left_dart mr p d.
Proof.
intros m mr p da H_1 H_2 H_3 H_4 H_5 Hmap Hexd Hleft db Hdb.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 elim Hdb; clear Hdb; intro Hdb; [subst db | idtac].
  elim (left_dart_dec mr p d); [intro H1 | trivial].
   generalize (one_left mr p da d H_1 H_2 H_3 H_4 H_5 Hleft H1).
   intro H3; apply neq_sym in Hexd1; contradiction.
  apply (IHm Hmap Hexd2 Hdb).
 (* Cas 3 : m = L *)
 simpl in *; apply IHm; intuition.
Qed.

Lemma map_right_dart_less :
  forall (m:fmap)(mr:fmap)(p:point)(da:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr ->
  inv_noalign_point mr p -> convex mr ->
  inv_hmap m -> ~ exd m da -> right_dart mr p da ->
  forall (d:dart), exd m d -> ~ right_dart mr p d.
Proof.
intros m mr p da H_1 H_2 H_3 H_4 H_5 Hmap Hexd Hright db Hdb.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 rewritenotorandnot Hexd Hexd1 Hexd2.
 elim Hdb; clear Hdb; intro Hdb; [subst db | idtac].
  elim (right_dart_dec mr p d); [intro H1 | trivial].
   generalize (one_right mr p da d H_1 H_2 H_3 H_4 H_5 Hright H1).
   intro H3; apply neq_sym in Hexd1; contradiction.
  apply (IHm Hmap Hexd2 Hdb).
 (* Cas 3 : m = L *)
 simpl in *; apply IHm; tauto.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem inv_hmap_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  submap m mr -> inv_hmap m ->
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  x <> nil -> max <> nil -> x <> max -> ~ exd mr x ->  ~ exd mr max ->
  inv_hmap (CHID m mr x tx px max).
Proof.
intros m mr x tx px max Hsub Hinv1 Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hneq1 Hneq2 Hneq0 Hexd1 Hexd2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; unfold prec_I; simpl; tauto.
 (* Cas 2 : m = I *)
simpl in Hsub, Hinv1.
unfold prec_I in Hinv1.
destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
destruct Hinv1 as [Hinv1 [Hneq3 Hexd3]].
generalize (IHm Hsub Hinv1); clear IHm; intro IHm.
 simpl in *.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
simpl; unfold prec_I; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
simpl; unfold prec_I, prec_L.
simpl; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
apply and_not_not_or; split.
 apply (exd_not_exd_neq mr d max); assumption.
 apply (max_CHID_3 m mr x tx px max); try assumption.
  apply (submap_not_exd m mr max); try assumption.
  apply (map_left_dart_less m mr px d); try assumption.
left; trivial.
right; right; apply (x_CHID_1 m mr x tx px max); try assumption.
unfold succ; simpl; apply (max_CHID_4 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply (map_left_dart_less m mr px d); try assumption.
unfold pred; simpl; apply (x_CHID_5 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply (map_left_dart_less m mr px d); try assumption.
elimeqdartdec; apply neq_sym; assumption.
right; left; trivial.
left; trivial.
unfold succ; simpl; apply eq_not_neq; apply not_exd_A_nil; try assumption.
 apply (not_exd_CHID m mr x tx px max d); try assumption.
  apply (exd_not_exd_neq mr d x); assumption.
  apply (exd_not_exd_neq mr d max); assumption.
unfold pred; simpl; apply (max_CHID_5 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply (map_left_dart_less m mr px d); try assumption.
elim (eq_dart_dec max d).
 intro Heq; subst d; contradiction.
 elimeqdartdec; intuition.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
simpl; unfold prec_I; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
simpl; unfold prec_I; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
(* ======= *)
    elim right_dart_dec.
    intros H_right H_ccw H_red H_blue.
(* == 5 == *)
simpl; unfold prec_I, prec_L.
simpl; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
right; apply (x_CHID_1 m mr x tx px max); try assumption.
left; trivial.
unfold succ; simpl; apply (x_CHID_4 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply (map_right_dart_less m mr px d); try assumption.
unfold pred; simpl; apply eq_not_neq; apply not_exd_A_1_nil; try assumption.
 apply (not_exd_CHID m mr x tx px max d); try assumption.
  apply (exd_not_exd_neq mr d x); assumption.
  apply (exd_not_exd_neq mr d max); assumption.
elim (eq_dart_dec d x); intro Heq.
 subst d; contradiction.
 assert (H0 : cA (CHID m mr x tx px max) zero x = x).
  apply fixpoint_cA; try assumption.
  apply (x_CHID_1 m mr x tx px max); try assumption.
  apply (x_CHID_4 m mr x tx px max); try assumption.
   apply (submap_not_exd m mr x); try assumption.
   apply (map_right_dart_less m mr px d); try assumption.
  apply (x_CHID_3 m mr x tx px max); try assumption.
   apply (submap_not_exd m mr x); try assumption.
 rewrite H0; apply neq_sym; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros Hred Hblue.
(* == 7 == *)
simpl; unfold prec_I; repeat split; try assumption.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
(* ======= *)
 (* Cas 3 : m = L *)
simpl in Hsub, Hinv1.
unfold prec_L in Hinv1.
destruct Hsub as [Hsub [Hsub1 Hsub2]].
destruct Hinv1 as [Hinv1 [H1 [H2 [H3 [H4 H5]]]]].
generalize (IHm Hsub Hinv1); clear IHm; intro IHm.
induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
simpl; unfold prec_L; repeat split; try assumption.
apply (blue_dart_CHID_1 m mr x tx px max d0); try assumption.
 apply succ_zero_blue_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
apply (red_dart_CHID_3 m mr x tx px max d1); try assumption.
 apply pred_zero_red_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
 unfold invisible; elim blue_dart_dec; intro Hblue.
  cut (~ blue_dart mr d1); [contradiction|idtac].
  apply red_not_blue; try assumption.
  apply pred_zero_red_dart; try assumption.
  unfold pred; rewrite Hsub2; try assumption.
  apply (exd_not_nil m d0); try assumption.
  left; rewrite Hsub2; assumption.
apply (blue_dart_CHID_5 m mr x tx px max d0); try assumption.
 apply (exd_not_exd_neq m d0 x); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply succ_zero_blue_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
 rewrite Hsub1; assumption.
apply (red_dart_CHID_8 m mr x tx px max d1); try assumption.
 apply (exd_not_exd_neq m d1 max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply pred_zero_red_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
 rewrite Hsub2; assumption.
assert (H0 : cA (CHID m mr x tx px max) zero d0 = d0).
 apply fixpoint_cA; try assumption.
 apply (blue_dart_CHID_1 m mr x tx px max d0); try assumption.
  apply succ_zero_blue_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 apply (blue_dart_CHID_5 m mr x tx px max d0); try assumption.
  apply (exd_not_exd_neq m d0 x); try assumption.
  apply (submap_not_exd m mr x); try assumption.
  apply succ_zero_blue_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
  rewrite Hsub1; assumption.
 apply (blue_dart_CHID_3 m mr x tx px max d0); try assumption.
  apply (exd_not_exd_neq m d0 max); try assumption.
  apply (submap_not_exd m mr max); try assumption.
  apply succ_zero_blue_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 rewrite H0; elim (eq_dart_dec d0 d1); [idtac|trivial].
  intro Heq; move Heq after Hsub; subst d0.
  assert (Hblue : blue_dart mr d1).
   apply succ_zero_blue_dart; try assumption.
   unfold succ; rewrite Hsub1; try assumption.
   apply (exd_not_nil m d1); try assumption.
  assert (Hred : red_dart mr d1).
   apply pred_zero_red_dart; try assumption.
   unfold pred; rewrite Hsub2; try assumption.
   apply (exd_not_nil m d1); try assumption.
  apply blue_not_red in Hblue; contradiction.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
simpl; unfold prec_L; repeat split; try assumption.
apply (red_dart_CHID_3 m mr x tx px max d0); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
apply (blue_dart_CHID_1 m mr x tx px max d1); try assumption.
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
apply (red_dart_CHID_5 m mr x tx px max d0); try assumption.
 apply (exd_not_exd_neq m d0 max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
apply (blue_dart_CHID_20 m mr x tx px max d1); try assumption.
 apply (exd_not_exd_neq m d1 x); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
assert (H0 : cA (CHID m mr x tx px max) one d0 = d0).
 apply fixpoint_cA; try assumption.
 apply (red_dart_CHID_3 m mr x tx px max d0); try assumption.
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 apply (red_dart_CHID_5 m mr x tx px max d0); try assumption.
  apply (exd_not_exd_neq m d0 max); try assumption.
  apply (submap_not_exd m mr max); try assumption.
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 apply (red_dart_CHID_2 m mr x tx px max d0); try assumption.
  apply (exd_not_exd_neq m d0 x); try assumption.
  apply (submap_not_exd m mr x); try assumption.
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 rewrite H0; elim (eq_dart_dec d0 d1); [idtac|trivial].
  intro Heq; move Heq after Hsub; subst d0.
  assert (Hblue : blue_dart mr d1).
   apply pred_one_blue_dart; try assumption.
   unfold pred; rewrite Hsub2; try assumption.
   apply (exd_not_nil m d1); try assumption.
  assert (Hred : red_dart mr d1).
   apply succ_one_red_dart; try assumption.
   unfold succ; rewrite Hsub1; try assumption.
   apply (exd_not_nil m d1); try assumption.
  apply blue_not_red in Hblue; contradiction.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
simpl; unfold prec_L; repeat split; try assumption.
apply (red_dart_CHID_11 m mr x tx px max d0); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
 apply not_invisible_visible in H_ccw2; assumption.
 rewrite Hsub1; assumption.
apply (blue_dart_CHID_1 m mr x tx px max d1); try assumption.
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
apply (red_dart_CHID_13 m mr x tx px max d0); try assumption.
 apply (exd_not_exd_neq m d0 max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
 apply not_invisible_visible in H_ccw2; assumption.
 rewrite Hsub1; assumption.
apply (blue_dart_CHID_20 m mr x tx px max d1); try assumption.
 apply (exd_not_exd_neq m d1 x); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2; try assumption.
 apply (exd_not_nil m d0); try assumption.
assert (H0 : cA (CHID m mr x tx px max) one d0 = d0).
 apply fixpoint_cA; try assumption.
apply (red_dart_CHID_11 m mr x tx px max d0); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
 apply not_invisible_visible in H_ccw2; assumption.
 rewrite Hsub1; assumption.
apply (red_dart_CHID_13 m mr x tx px max d0); try assumption.
 apply (exd_not_exd_neq m d0 max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1; try assumption.
 apply (exd_not_nil m d1); try assumption.
 apply not_invisible_visible in H_ccw2; assumption.
 rewrite Hsub1; assumption.
 apply (red_dart_CHID_2 m mr x tx px max d0); try assumption.
  apply (exd_not_exd_neq m d0 x); try assumption.
  apply (submap_not_exd m mr x); try assumption.
  apply succ_one_red_dart; try assumption.
  unfold succ; rewrite Hsub1; try assumption.
  apply (exd_not_nil m d1); try assumption.
 rewrite H0; elim (eq_dart_dec d0 d1); [idtac|trivial].
  intro Heq; move Heq after Hsub; subst d0.
  assert (Hblue : blue_dart mr d1).
   apply pred_one_blue_dart; try assumption.
   unfold pred; rewrite Hsub2; try assumption.
   apply (exd_not_nil m d1); try assumption.
  assert (Hred : red_dart mr d1).
   apply succ_one_red_dart; try assumption.
   unfold succ; rewrite Hsub1; try assumption.
   apply (exd_not_nil m d1); try assumption.
  apply blue_not_red in Hblue; contradiction.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem inv_poly_CHID :
  forall (m:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  inv_hmap m -> inv_poly m -> well_emb m -> inv_noalign_point m px -> convex m ->
  x <> nil -> max <> nil -> x <> max -> ~ exd m x ->  ~ exd m max ->
  inv_poly (CHID m m x tx px max).
Proof.
intros m x tx px max H1 H2 H3 H4 H5 Hneq1 Hneq2 Hneq0 Hexd1 Hexd2.
unfold inv_poly; intros d Hexd0.
assert (Hsub : submap m m).
 apply submap_2_submap; try assumption.
 apply submap_2_refl.
generalize (exd_CHID_exd_m_or_x_or_max m m x tx px max d Hexd0); intro H.
elim H; clear H; intro H.
 generalize (H2 d H); clear H2; intro H2.
 elim H2; clear H2; intro H2.
  left; apply black_dart_CHID; try assumption.
  apply (exd_not_exd_neq m d x); try assumption.
  apply (exd_not_exd_neq m d max); try assumption.
 elim H2; clear H2; intro H2.
  cut (black_dart (CHID m m x tx px max) d \/ blue_dart (CHID m m x tx px max) d).
  intro H0; elim H0; clear H0; intro H0.
  left; assumption.
  right; left; assumption.
  apply blue_dart_CHID; try assumption.
  apply (exd_not_exd_neq m d x); try assumption.
  apply (exd_not_exd_neq m d max); try assumption.
  cut (~ exd (CHID m m x tx px max) d \/ red_dart (CHID m m x tx px max) d).
  intro H0; elim H0; clear H0; intro H0.
  contradiction.
  right; right; assumption.
  apply red_dart_CHID; try assumption.
  apply (exd_not_exd_neq m d x); try assumption.
  apply (exd_not_exd_neq m d max); try assumption.
elim H; clear H; intro H; subst d.
 elim (pred_dec (CHID m m x tx px max) one x); intro Hpred.
  apply (pred_one_x_exd_left_dart) in Hpred; try assumption.
  generalize (exd_left_dart_exd_right_dart m px H1 H2 Hpred); intro Hsucc.
  cut (blue_dart (CHID m m x tx px max) x).
  right; left; assumption.
  apply x_CHID_11; try assumption.
  cut (forall (d:dart), exd m d -> ~ left_dart m px d). intro Hleft.
  cut (forall (d:dart), exd m d -> ~ right_dart m px d). intro Hright.
  cut (black_dart (CHID m m x tx px max) x).
  left; assumption.
  apply x_CHID_6; try assumption.
  intros d Hexd; split.
  apply Hleft; try assumption.
  apply Hright; try assumption.
  apply not_exd_left_dart_not_exd_right_dart; try assumption.
  intros d Hexd.
  apply (not_pred_one_x_not_exd_left_dart m m x tx px max); try assumption.
  cut (~ exd (CHID m m x tx px max) max \/ red_dart (CHID m m x tx px max) max).
  intro H0; elim H0; clear H0; intro H0.
  contradiction.
  right; right; assumption.
  apply max_CHID; try assumption.
  left; apply exd_max_exd_left_dart with x tx max; try assumption.
Qed.
