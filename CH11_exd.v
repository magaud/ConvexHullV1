(* ====================== *)
(* ===== CH11_exd.v ===== *)
(* ====================== *)

Require Export CH10_CHI_CH.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma exd_m2_CHI :
  forall (m1:fmap)(m2:fmap)(max:dart)(d:dart),
  inv_hmap m1 -> linkless m1 -> well_emb m1 -> noalign m1 ->
  inv_hmap m2 -> inv_poly m2 -> well_emb m2 -> convex m2 ->
  (forall (d:dart), max <= d -> d <> nil) ->
  (forall (d:dart), exd m1 d -> ~ exd m2 d) ->
  (forall (d:dart), max <= d -> ~ exd m1 d /\ ~ exd m2 d) ->
  (forall (d1:dart)(d2:dart), exd m1 d1 -> exd m2 d2 -> (fpoint m1 d1) <> (fpoint m2 d2)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m1 d2 -> exd m2 d3 ->
   (fpoint m1 d1) <> (fpoint m1 d2) -> ~ align (fpoint m1 d1) (fpoint m1 d2) (fpoint m2 d3)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m2 d2 -> exd m2 d3 ->
   (fpoint m2 d2) <> (fpoint m2 d3) -> ~ align (fpoint m1 d1) (fpoint m2 d2) (fpoint m2 d3)) ->
  exd m2 d -> (black_dart m2 d) \/ (blue_dart m2 d) ->
  exd (CHI m1 m2 max) d /\ fpoint m2 d = fpoint (CHI m1 m2 max) d.
Proof.
induction m1.
 (* Case 1 : m = V *)
 intros m2 max x Hm11 Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd Hbb.
 simpl in *; intuition.
 (* Case 2 : m = I *)
 intros m2 max x Hmap Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd Hbb.
 simpl in *; unfold prec_I in *.
 destruct Hmap as [Hmap [Hmap1 Hamp2]].
(**)
assert (Hw2 : forall (d0:dart), d = d0 \/ exd m1 d0 -> d0 < max).
 intros d0 Hd0.
 elim Hd0; clear Hd0; intro Hd0; try subst d.
  elim (le_lt_dec max d0); intro H.
   generalize (Hw5 d0 H); intuition.
   assumption.
  elim (le_lt_dec max d0); intro H.
   generalize (Hw5 d0 H); intuition.
   assumption.
assert (Hw3 : forall (d0:dart), exd m2 d0 -> ~ exd m1 d0).
 intros d0 Hd0; elim (exd_dec m1 d0).
  intro H; generalize (Hw1 d0); intuition.
  intro H; assumption.
assert (Hw4 : forall (d0:dart), exd m2 d0 -> d0 < max).
 intros d0 Hd0; elim (le_lt_dec max d0).
  intro H; generalize (Hw5 d0 H); intuition.
  intro H; assumption.
move Hw1 after Hp3; move Hw0 after Hp3; move Hw5 after Hw4.
(**)
assert (Hp4 : forall (da:dart), exd m1 da -> fpoint m1 da <> p).
 intros da Hda.
 assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hm13 d H0); unfold well_emb; simpl.
 intros [H1 [H2 [H3 [H4 H5]]]]; clear H0 H1 H2 H3 H4.
 assert (H0 : exd (I m1 d t p) da); [simpl;tauto|idtac].
 generalize (H5 da H0); elimeqdartdec; clear H0 H5.
 elim (eq_dart_dec d da); intro Heq; [subst d; contradiction | idtac].
 intro H0; apply neq_sym_point; apply H0; try assumption.
 apply neq_sym; assumption.
 rewrite not_exd_A_nil; try assumption.
 apply exd_not_nil with m1; try assumption.
 rewrite not_exd_A_1_nil; try assumption.
 apply exd_not_nil with m1; try assumption.
(**)
elim (eq_dart_dec x d); intro Heq1; try subst x.
generalize (Hw1 d); intuition.
elim (eq_dart_dec x max); intro Heq2; try subst x.
generalize (Hw5 max (le_refl max)); intuition.
rewrite (inv_fpoint_CHID m2 m2 d t p max x); try assumption.
 apply IHm1; clear IHm1; try assumption.
 (* well_emb m1 /\ noalign m1 *)
 apply well_emb_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 apply noalign_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 (* inv_hmap CHID *)
 apply inv_hmap_CHID; try assumption.
 apply submap_2_submap; try assumption.
 apply submap_2_refl.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* inv_poly CHID *)
 apply inv_poly_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* well_emb CHID *)
 apply well_emb_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 intros da Hda; apply neq_sym_point.
 assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp1 d da H0 Hda); clear H0.
 elimeqdartdec; trivial.
 (* convex CHID *)
 apply inv_convex_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* Hw0 *)
 intros d0 Hd0; apply Hw0; omega.
 (* Hw1 *)
 intros d0 Hd0; apply not_exd_CHID.
  apply Hw1; right; assumption.
  apply exd_not_exd_neq with m1; assumption.
  generalize (Hw2 d0); intuition.
 (* Hw5 *)
 intros d0 Hd0; split.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  apply not_exd_CHID; try omega.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
 (* Hp1 *)
 intros da db Hda Hdb.
 generalize Hdb; intro Hdb2.
 apply exd_CHID_exd_m_or_x_or_max in Hdb2.
 elim Hdb2; clear Hdb2; intro Hdb2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H0 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  generalize (Hp1 da db H0 Hdb2); clear H0.
  elim (eq_dart_dec d da); trivial.
   intro Heq; subst d; contradiction.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 db Hdb2); intuition.
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x; try assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp2 *)
 intros da db dc Hda Hdb Hdc Hp0.
 generalize Hdc; intro Hdc2.
 apply exd_CHID_exd_m_or_x_or_max in Hdc2.
 elim Hdc2; clear Hdc2; intro Hdc2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  generalize (Hp2 da db dc H01 H02 Hdc2); clear H01 H02.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 dc Hdc2); intuition.
 elim Hdc2; clear Hdc2; intro Hdc2; subst dc.
  rewrite fpoint_x; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp3 *)
 intros d1 d2 d3 Hd1 Hd2 Hd3 Hp0.
 generalize Hd2; intro Hd20.
 apply exd_CHID_exd_m_or_x_or_max in Hd20.
 elim Hd20; clear Hd20; intro Hd20.
 assert (H1 : fpoint m2 d2 = fpoint (CHID m2 m2 d t p max) d2).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d2 Hd20); intuition.
 rewrite <- H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 generalize (Hp3 d1 d2 d3 H3 Hd20 Hd30 Hp0); clear H3.
 elim (eq_dart_dec d d1); trivial.
  intro Heq; subst d; contradiction.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd20; clear Hd20; intro Hd20; subst d2.
 assert (H1 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 assert (H1 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
   generalize (Hw5 max (le_refl max)); intuition.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 (* Hexd *)
 elim Hbb; clear Hbb; intro Hbb.
  apply black_dart_exd; assumption.
  apply blue_dart_CHID_1; assumption.
 elim Hbb; clear Hbb; intro Hbb.
  left; apply black_dart_CHID; try assumption.
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
  apply blue_dart_CHID; try assumption.
  apply submap_2_submap; try assumption.
  apply submap_2_refl.
  unfold inv_noalign_point.
   intros da db Hda Hdb Hp0.
   assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
   generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
   elimeqdartdec; intro H0; auto with myorientation.
  apply (Hw0 max (le_refl max)).
 (* Hexd *)
 elim Hbb; clear Hbb; intro Hbb.
  apply black_dart_exd; assumption.
  apply blue_dart_CHID_1; assumption.
 (* Case 3 : m = L *)
 intros m2 max x Hmap Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd Hbb.
 simpl in *; intuition.
Qed.

Lemma exd_m1_CHI :
  forall (m1:fmap)(m2:fmap)(max:dart)(d:dart),
  inv_hmap m1 -> linkless m1 -> well_emb m1 -> noalign m1 ->
  inv_hmap m2 -> inv_poly m2 -> well_emb m2 -> convex m2 ->
  (forall (d:dart), max <= d -> d <> nil) ->
  (forall (d:dart), exd m1 d -> ~ exd m2 d) ->
  (forall (d:dart), max <= d -> ~ exd m1 d /\ ~ exd m2 d) ->
  (forall (d1:dart)(d2:dart), exd m1 d1 -> exd m2 d2 -> (fpoint m1 d1) <> (fpoint m2 d2)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m1 d2 -> exd m2 d3 ->
   (fpoint m1 d1) <> (fpoint m1 d2) -> ~ align (fpoint m1 d1) (fpoint m1 d2) (fpoint m2 d3)) ->
  (forall (d1:dart)(d2:dart)(d3:dart), exd m1 d1 -> exd m2 d2 -> exd m2 d3 ->
   (fpoint m2 d2) <> (fpoint m2 d3) -> ~ align (fpoint m1 d1) (fpoint m2 d2) (fpoint m2 d3)) ->
  exd m1 d -> exd (CHI m1 m2 max) d /\ fpoint m1 d = fpoint (CHI m1 m2 max) d.
Proof.
induction m1.
 (* Case 1 : m = V *)
 intros m2 max x Hmap Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd.
 simpl in *; intuition.
 (* Case 2 : m = I *)
 intros m2 max x Hmap Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd.
 simpl in *; unfold prec_I in *.
 destruct Hmap as [Hmap [Hmap1 Hamp2]].
(**)
assert (Hw2 : forall (d0:dart), d = d0 \/ exd m1 d0 -> d0 < max).
 intros d0 Hd0.
 elim Hd0; clear Hd0; intro Hd0; try subst d.
  elim (le_lt_dec max d0); intro H.
   generalize (Hw5 d0 H); intuition.
   assumption.
  elim (le_lt_dec max d0); intro H.
   generalize (Hw5 d0 H); intuition.
   assumption.
assert (Hw3 : forall (d0:dart), exd m2 d0 -> ~ exd m1 d0).
 intros d0 Hd0; elim (exd_dec m1 d0).
  intro H; generalize (Hw1 d0); intuition.
  intro H; assumption.
assert (Hw4 : forall (d0:dart), exd m2 d0 -> d0 < max).
 intros d0 Hd0; elim (le_lt_dec max d0).
  intro H; generalize (Hw5 d0 H); intuition.
  intro H; assumption.
move Hw1 after Hp3; move Hw0 after Hp3; move Hw5 after Hw4.
(**)
assert (Hp4 : forall (da:dart), exd m1 da -> fpoint m1 da <> p).
 intros da Hda.
 assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hm13 d H0); unfold well_emb; simpl.
 intros [H1 [H2 [H3 [H4 H5]]]]; clear H0 H1 H2 H3 H4.
 assert (H0 : exd (I m1 d t p) da); [simpl;tauto|idtac].
 generalize (H5 da H0); elimeqdartdec; clear H0 H5.
 elim (eq_dart_dec d da); intro Heq; [subst d; contradiction | idtac].
 intro H0; apply neq_sym_point; apply H0; try assumption.
 apply neq_sym; assumption.
 rewrite not_exd_A_nil; try assumption.
 apply exd_not_nil with m1; try assumption.
 rewrite not_exd_A_1_nil; try assumption.
 apply exd_not_nil with m1; try assumption.
(**)
elim Hexd; clear Hexd; intro Hexd; try subst x.
 elimeqdartdec; pattern p at 2.
 rewrite <- fpoint_x with m2 m2 d t p max.
 apply exd_m2_CHI; try assumption.
 (* well_emb m1 /\ noalign m1 *)
 apply well_emb_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 apply noalign_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 (* inv_hmap CHID *)
 apply inv_hmap_CHID; try assumption.
 apply submap_2_submap; try assumption.
 apply submap_2_refl.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* inv_poly CHID *)
 apply inv_poly_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* well_emb CHID *)
 apply well_emb_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 intros da Hda; apply neq_sym_point.
 assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp1 d da H0 Hda); clear H0.
 elimeqdartdec; trivial.
 (* convex CHID *)
 apply inv_convex_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* Hw0 *)
 intros d0 Hd0; apply Hw0; omega.
 (* Hw1 *)
 intros d0 Hd0; apply not_exd_CHID.
  apply Hw1; right; assumption.
  apply exd_not_exd_neq with m1; assumption.
  generalize (Hw2 d0); intuition.
 (* Hw5 *)
 intros d0 Hd0; split.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  apply not_exd_CHID; try omega.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
 (* Hp1 *)
 intros da db Hda Hdb.
 generalize Hdb; intro Hdb2.
 apply exd_CHID_exd_m_or_x_or_max in Hdb2.
 elim Hdb2; clear Hdb2; intro Hdb2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H0 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  generalize (Hp1 da db H0 Hdb2); clear H0.
  elim (eq_dart_dec d da); trivial.
   intro Heq; subst d; contradiction.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 db Hdb2); intuition.
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x; try assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp2 *)
 intros da db dc Hda Hdb Hdc Hp0.
 generalize Hdc; intro Hdc2.
 apply exd_CHID_exd_m_or_x_or_max in Hdc2.
 elim Hdc2; clear Hdc2; intro Hdc2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  generalize (Hp2 da db dc H01 H02 Hdc2); clear H01 H02.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 dc Hdc2); intuition.
 elim Hdc2; clear Hdc2; intro Hdc2; subst dc.
  rewrite fpoint_x; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp3 *)
 intros d1 d2 d3 Hd1 Hd2 Hd3 Hp0.
 generalize Hd2; intro Hd20.
 apply exd_CHID_exd_m_or_x_or_max in Hd20.
 elim Hd20; clear Hd20; intro Hd20.
 assert (H1 : fpoint m2 d2 = fpoint (CHID m2 m2 d t p max) d2).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d2 Hd20); intuition.
 rewrite <- H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 generalize (Hp3 d1 d2 d3 H3 Hd20 Hd30 Hp0); clear H3.
 elim (eq_dart_dec d d1); trivial.
  intro Heq; subst d; contradiction.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd20; clear Hd20; intro Hd20; subst d2.
 assert (H1 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 assert (H1 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
   generalize (Hw5 max (le_refl max)); intuition.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 (* Hexd *)
 apply x_CHID_1; try assumption.
 (* Hbb *)
 apply x_CHID; try assumption.
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 apply Hw0; omega.
 elim (pred_dec (CHID m2 m2 d t p max) one d); intro H1.
  apply (pred_one_x_exd_left_dart) in H1; try assumption.
  generalize (exd_left_dart_exd_right_dart m2 p Hm21 Hm22 H1); intro H2.
  left; split; assumption.
  apply Hw1; left; trivial.
  cut (forall (d:dart), exd m2 d -> ~ left_dart m2 p d). intro Hleft.
  cut (forall (d:dart), exd m2 d -> ~ right_dart m2 p d). intro Hright.
  right; intros da Hda; split.
   apply Hleft; assumption.
   apply Hright; assumption.
  apply not_exd_left_dart_not_exd_right_dart; try assumption.
  intros da Hda.
  apply (not_pred_one_x_not_exd_left_dart m2 m2 d t p max); try assumption.
  apply Hw1; left; trivial.
  apply Hw0; omega.
  apply Hw1; left; trivial.
(**)
 elim (eq_dart_dec d x); intro Heq0; [subst d; contradiction | idtac].
 apply IHm1; clear IHm1; try assumption.
 (* well_emb m1 /\ noalign m1 *)
 apply well_emb_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 apply noalign_I with d t p; try assumption.
 simpl; unfold prec_I; repeat split; assumption.
 (* inv_hmap CHID *)
 apply inv_hmap_CHID; try assumption.
 apply submap_2_submap; try assumption.
 apply submap_2_refl.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* inv_poly CHID *)
 apply inv_poly_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* well_emb CHID *)
 apply well_emb_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 intros da Hda; apply neq_sym_point.
 assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp1 d da H0 Hda); clear H0.
 elimeqdartdec; trivial.
 (* convex CHID *)
 apply inv_convex_CHID; try assumption.
 unfold inv_noalign_point.
  intros da db Hda Hdb Hp0.
  assert (H0 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hp3 d da db H0 Hda Hdb Hp0); clear H0.
  elimeqdartdec; intro H0; auto with myorientation.
 apply (Hw0 max (le_refl max)).
 generalize (Hw2 d); intuition.
 apply Hw1; left; trivial.
 generalize (Hw5 max (le_refl max)); intuition.
 (* Hw0 *)
 intros d0 Hd0; apply Hw0; omega.
 (* Hw1 *)
 intros d0 Hd0; apply not_exd_CHID.
  apply Hw1; right; assumption.
  apply exd_not_exd_neq with m1; assumption.
  generalize (Hw2 d0); intuition.
 (* Hw5 *)
 intros d0 Hd0; split.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  apply not_exd_CHID; try omega.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
  assert (H : max <= d0); [omega|idtac].
  generalize (Hw5 d0 H); intuition.
 (* Hp1 *)
 intros da db Hda Hdb.
 generalize Hdb; intro Hdb2.
 apply exd_CHID_exd_m_or_x_or_max in Hdb2.
 elim Hdb2; clear Hdb2; intro Hdb2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H0 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  generalize (Hp1 da db H0 Hdb2); clear H0.
  elim (eq_dart_dec d da); trivial.
   intro Heq; subst d; contradiction.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 db Hdb2); intuition.
 elim Hdb2; clear Hdb2; intro Hdb2; subst db.
  rewrite fpoint_x; try assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp2 *)
 intros da db dc Hda Hdb Hdc Hp0.
 generalize Hdc; intro Hdc2.
 apply exd_CHID_exd_m_or_x_or_max in Hdc2.
 elim Hdc2; clear Hdc2; intro Hdc2.
  rewrite <- inv_fpoint_CHID; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  generalize (Hp2 da db dc H01 H02 Hdc2); clear H01 H02.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 dc Hdc2); intuition.
 elim Hdc2; clear Hdc2; intro Hdc2; subst dc.
  rewrite fpoint_x; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  apply Hw1; left; trivial.
  rewrite fpoint_max; try assumption.
  assert (H01 : exd (I m1 d t p) da); [simpl;tauto|idtac].
  assert (H02 : exd (I m1 d t p) db); [simpl;tauto|idtac].
  assert (H03 : exd (I m1 d t p) d); [simpl;tauto|idtac].
  generalize (Hm14 da db d H01 H02 H03); clear H01 H02 H03.
  simpl; elimeqdartdec.
  elim (eq_dart_dec d da).
   intro Heq; subst d; contradiction.
  elim (eq_dart_dec d db).
   intro Heq; subst d; contradiction.
  intros H1 H2 H0; apply H0; try assumption.
  apply Hp4; assumption.
  apply Hp4; assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 (* Hp3 *)
 intros d1 d2 d3 Hd1 Hd2 Hd3 Hp0.
 generalize Hd2; intro Hd20.
 apply exd_CHID_exd_m_or_x_or_max in Hd20.
 elim Hd20; clear Hd20; intro Hd20.
 assert (H1 : fpoint m2 d2 = fpoint (CHID m2 m2 d t p max) d2).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d2 Hd20); intuition.
 rewrite <- H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 generalize (Hp3 d1 d2 d3 H3 Hd20 Hd30 Hp0); clear H3.
 elim (eq_dart_dec d d1); trivial.
  intro Heq; subst d; contradiction.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d2 H3 H4 Hd20); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd20; clear Hd20; intro Hd20; subst d2.
 assert (H1 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 assert (H1 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
   generalize (Hw5 max (le_refl max)); intuition.
 rewrite H1 in *.
 generalize Hd3; intro Hd30.
 apply exd_CHID_exd_m_or_x_or_max in Hd30.
 elim Hd30; clear Hd30; intro Hd30.
 assert (H2 : fpoint m2 d3 = fpoint (CHID m2 m2 d t p max) d3).
  apply inv_fpoint_CHID; try assumption.
  apply exd_not_exd_neq with m2; try assumption.
  apply Hw1; left; trivial.
  generalize (Hw4 d3 Hd30); intuition.
 rewrite <- H2 in *.
 assert (H3 : exd (I m1 d t p) d1); [simpl;tauto|idtac].
 assert (H4 : exd (I m1 d t p) d); [simpl;tauto|idtac].
 generalize (Hp2 d1 d d3 H3 H4 Hd30); clear H3 H4.
 simpl; elimeqdartdec.
 elim (eq_dart_dec d d1).
  intro Heq; subst d; contradiction.
  generalize (Hp4 d1 Hd1); intros H Heq H0.
  generalize (H0 H); auto with myorientation.
 elim Hd30; clear Hd30; intro Hd30; subst d3.
 assert (H2 : fpoint (CHID m2 m2 d t p max) d = p).
  apply fpoint_x; try assumption.
  apply Hw1; left; trivial.
 rewrite H2 in *; tauto.
 assert (H2 : fpoint (CHID m2 m2 d t p max) max = p).
  apply fpoint_max; try assumption.
  generalize (Hw5 max (le_refl max)); intuition.
 rewrite H2 in *; tauto.
 (* Case 3 : m = L *)
 intros m2 max x Hmap Hm12 Hm13 Hm14 Hm21 Hm22 Hm23 Hm24 Hw0 Hw1 Hw5 Hp1 Hp2 Hp3 Hexd.
 simpl in *; intuition.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Theorem exd_CH : forall (m:fmap)(d:dart),
  prec_CH m -> exd m d -> exd (CH m) d /\ fpoint m d = fpoint (CH m) d.
Proof.
induction m.
 (* Case 1 : m = V *)
 simpl; tauto.
 clear IHm.
 (* Case 2 : m = I *)
 induction m.
  (* Case 2.1 : m = I V *)
  simpl; tauto.
  clear IHm.
  (* Case 2.2 : m = I I *)
  intros x [Hmap [Hless [Hemb Halign]]] Hexd.
  simpl in *; unfold prec_I in *; simpl in *.
  destruct Hmap as [[Hmap [H1 H2]] [H3 H4]].
  rewritenotorandnot H4 H4 H5.
(**)
assert (Hp1 : p <> p0).
 assert (H0 : exd (I (I m d0 t0 p0) d t p) d); [simpl;tauto|idtac].
 generalize (Hemb d H0); unfold well_emb; simpl.
 intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]; clear H0 Hw1 Hw2 Hw3 Hw4.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) d0); [simpl;tauto|idtac].
 generalize (Hw5 d0 H0); elimeqdartdec; clear H0 Hw5.
 intro H0; apply H0; try assumption.
 rewrite not_exd_A_nil; try assumption.
 rewrite not_exd_A_1_nil; try assumption.
assert (Hp2 : forall (d:dart), exd m d -> p <> fpoint m d).
 intros da Hda.
 assert (Hneq1 : da <> d). apply exd_not_exd_neq with m ; try assumption.
 assert (Hneq2 : da <> d0). apply exd_not_exd_neq with m ; try assumption.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) d); [simpl;tauto|idtac].
 generalize (Hemb d H0); unfold well_emb; simpl.
 intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]; clear H0 Hw1 Hw2 Hw3 Hw4.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) da); [simpl;tauto|idtac].
 generalize (Hw5 da H0); elimeqdartdec; clear H0 Hw5.
 intro H0; apply H0; try assumption.
 rewrite not_exd_A_nil; try assumption.
 apply exd_not_nil with m; try assumption.
 rewrite not_exd_A_1_nil; try assumption.
 apply exd_not_nil with m; try assumption.
assert (Hp3 : forall (d:dart), exd m d -> p0 <> fpoint m d).
 intros da Hda.
 assert (Hneq1 : da <> d). apply exd_not_exd_neq with m ; try assumption.
 assert (Hneq2 : da <> d0). apply exd_not_exd_neq with m ; try assumption.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) d0); [simpl;tauto|idtac].
 generalize (Hemb d0 H0); unfold well_emb; simpl.
 intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]; clear H0 Hw1 Hw2 Hw3 Hw4.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) da); [simpl;tauto|idtac].
 generalize (Hw5 da H0); elimeqdartdec; clear H0 Hw5.
 intro H0; apply H0; try assumption.
 rewrite not_exd_A_nil; try assumption.
 apply exd_not_nil with m; try assumption.
 rewrite not_exd_A_1_nil; try assumption.
 apply exd_not_nil with m; try assumption.
assert (Hp4 : forall (da:dart)(db:dart), exd m da -> exd m db -> da <> db -> fpoint m da <> fpoint m db).
 intros da db Hda Hdb Hneq.
 assert (Hneq1 : da <> d). apply exd_not_exd_neq with m ; try assumption.
 assert (Hneq2 : da <> d0). apply exd_not_exd_neq with m ; try assumption.
 assert (Hneq3 : db <> d). apply exd_not_exd_neq with m ; try assumption.
 assert (Hneq4 : db <> d0). apply exd_not_exd_neq with m ; try assumption.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) da); [simpl;tauto|idtac].
 generalize (Hemb da H0); unfold well_emb; simpl.
 intros [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]; clear H0 Hw1 Hw2 Hw3 Hw4.
 assert (H0 : exd (I (I m d0 t0 p0) d t p) db); [simpl;tauto|idtac].
 generalize (Hw5 db H0); elimeqdartdec; clear H0 Hw5.
 intro H0; apply H0; try assumption.
 apply neq_sym; assumption.
 rewrite linkless_A_nil; try assumption.
 apply exd_not_nil with m; try assumption.
 rewrite linkless_A_1_nil; try assumption.
 apply exd_not_nil with m; try assumption.
(**)
elim Hexd; clear Hexd; intro Hexd; try subst x.
(* H1 : x = d *)
elim (le_lt_dec d0 (max_dart m)).
 elim (le_lt_dec d (max_dart m)).
  (* 1 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p (max_dart m)) d = p).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption.
  apply inv_poly_CH2; try assumption.
  apply well_emb_CH2; try assumption.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
  (* 2 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d) d = p).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
 elim (le_lt_dec d d0).
  (* 3 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d0) d = p).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
  (* 4 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d) d = p).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
(**)
elim Hexd; clear Hexd; intro Hexd; try subst x.
    (* H2 : x = d0 *)
elim (le_lt_dec d0 (max_dart m)).
 elim (le_lt_dec d (max_dart m)).
  (* 1 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p (max_dart m)) d0 = p0).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p0 at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption.
  apply inv_poly_CH2; try assumption.
  apply well_emb_CH2; try assumption.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
  (* 2 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d) d0 = p0).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p0 at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
 elim (le_lt_dec d d0).
  (* 3 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d0) d0 = p0).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p0 at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
  (* 4 / 4 *)
  intros Hmax1 Hmax2; elimeqdartdec.
  assert (Hp : fpoint (CH2 d0 t0 p0 d t p d) d0 = p0).
   simpl; elimeqdartdec.
   elim eq_dart_dec; intro Heq1; [assert False; [omega|tauto] | idtac].
   elim eq_dart_dec; intro Heq2; [assert False; [omega|tauto] | trivial].
   pattern p0 at 2; rewrite <- Hp.
  apply exd_m2_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
(* Hexd *)
simpl; intuition.
(* Hbb *)
right; unfold blue_dart, succ, pred; simpl.
elimeqdartdec; repeat split.
apply neq_le_trans with d; [assumption|omega].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|tauto].
apply neq_le_trans with d; [assumption|omega].
    (* H3 : exd m x *)
elim (le_lt_dec d0 (max_dart m)).
 elim (le_lt_dec d (max_dart m)).
  (* 1 / 4 *)
  intros Hmax1 Hmax2.
  elim (eq_dart_dec d x); intro Hneq1; [subst x; contradiction | idtac].
  elim (eq_dart_dec d0 x); intro Hneq2; [subst x; contradiction | idtac].
  apply exd_m1_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption.
  apply inv_poly_CH2; try assumption.
  apply well_emb_CH2; try assumption.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
  (* 2 / 4 *)
  intros Hmax1 Hmax2.
  elim (eq_dart_dec d x); intro Hneq1; [subst x; contradiction | idtac].
  elim (eq_dart_dec d0 x); intro Hneq2; [subst x; contradiction | idtac].
  apply exd_m1_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
 elim (le_lt_dec d d0).
  (* 3 / 4 *)
  intros Hmax1 Hmax2.
  elim (eq_dart_dec d x); intro Hneq1; [subst x; contradiction | idtac].
  elim (eq_dart_dec d0 x); intro Hneq2; [subst x; contradiction | idtac].
  apply exd_m1_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
  (* 4 / 4 *)
  intros Hmax1 Hmax2.
  elim (eq_dart_dec d x); intro Hneq1; [subst x; contradiction | idtac].
  elim (eq_dart_dec d0 x); intro Hneq2; [subst x; contradiction | idtac].
  apply exd_m1_CHI; try assumption.
apply well_emb_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply well_emb_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
apply noalign_I with d0 t0 p0; try assumption.
simpl; unfold prec_I; simpl; repeat split; assumption.
apply noalign_I with d t p; try assumption.
simpl; unfold prec_I; simpl; repeat split; try assumption.
apply and_not_not_or; split; assumption.
  apply inv_hmap_CH2; try assumption || omega.
  apply inv_poly_CH2; try assumption || omega.
  apply well_emb_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
  apply convex_CH2; try assumption || omega.
   apply neq_sym_point; assumption.
(* Hw0 *)
intros da Hda;
apply neq_le_trans with d; [assumption|omega].
(* Hw1 *)
intros da Hda; simpl.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply exd_le_max_dart in Hda; omega.
apply and_not_not_or; split.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
apply and_not_not_or; split; try tauto.
apply neq_sym; apply exd_not_exd_neq with m; assumption.
(* Hw5 *)
intros da Hda; split; simpl.
apply gt_max_dart_not_exd; omega.
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|idtac].
apply and_not_not_or; split; [omega|tauto].
(* Hp1 *)
intros da db Hda Hdb; simpl in *.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp2; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim eq_dart_dec; intro Heq1; [omega|idtac].
elim eq_dart_dec; intro Heq2; [omega|idtac].
elim eq_dart_dec; intro Heq3; [intuition|idtac].
elimeqdartdec; apply neq_sym_point; apply Hp3; assumption.
(* Hp2 *)
intros da db dc Hda Hdb Hdc Hp0; simpl in *.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
generalize (Halign da db d H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp2; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) db); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da db d0 H01 H02 H03); simpl; elimeqdartdec.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d db).
 intro Heq2; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq3; subst d0; contradiction.
elim (eq_dart_dec d0 db).
 intro Heq4; subst d0; contradiction.
intros Heq1 Heq2 Heq3 Heq4.
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp3; assumption.
apply neq_sym_point; apply Hp3; assumption.
(* Hp3 *)
intros da db dc Hda Hdb Hdc; simpl in *.
elim (eq_dart_dec d da).
 intro Heq1; subst d; contradiction.
elim (eq_dart_dec d0 da).
 intro Heq2; subst d0; contradiction.
intros Heq1 Heq2.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec; tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
intro H; apply H; try assumption.
apply neq_sym_point; apply Hp2; assumption.
apply neq_sym_point; apply Hp3; assumption.
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdb; clear Hdb; intro Hdb; try subst db.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdb; clear Hdb; intro Hdb; try subst db; try tauto.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|tauto].
elim Hdc; clear Hdc; intro Hdc; try subst dc.
elimeqdartdec.
elim eq_dart_dec; intro Heq3; [omega|idtac].
elim eq_dart_dec; intro Heq4; [omega|idtac].
elim eq_dart_dec; intro Heq5; [omega|idtac].
elim eq_dart_dec; intro Heq6; [omega|idtac].
assert (H01 : exd (I (I m d0 t0 p0) d t p) da); [simpl; tauto | idtac].
assert (H02 : exd (I (I m d0 t0 p0) d t p) d); [simpl; tauto | idtac].
assert (H03 : exd (I (I m d0 t0 p0) d t p) d0); [simpl; tauto | idtac].
generalize (Halign da d d0 H01 H02 H03); simpl; elimeqdartdec.
generalize (neq_sym_point p0 (fpoint m da) (Hp3 da Hda)).
generalize (neq_sym_point p (fpoint m da) (Hp2 da Hda)).
auto with myorientation.
elim Hdc; clear Hdc; intro Hdc; try subst dc; try tauto.
   clear IHm.
  (* Case 2.3 : m = I L *)
  intros x [Hmap [Hless [Hemb Halign]]] Hexd.
  simpl in *; intuition.
  clear IHm.
 (* Case 3 : m = L *)
 intros x [Hmap [Hless [Hemb Halign]]] Hexd.
 simpl in *; intuition.
Qed.
