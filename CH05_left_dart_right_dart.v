(* ==================================== *)
(* ===== CH05_inv_hmap_inv_poly.v ===== *)
(* ==================================== *)

Require Export CH04_submap.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem one_left :
  forall (mr:fmap)(p:point)(x:dart)(y:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr ->
  inv_noalign_point mr p -> convex mr ->
  left_dart mr p x -> left_dart mr p y -> x = y.
Proof.
intros mr p x y Hmap Hpoly Hemb Halign Hconv [Hx1 [Hx2 Hx3]] [Hy1 [Hy2 Hy3]].
elim (eq_dart_dec x y); intro Heq; [trivial|idtac].
(* == Reecrire visible et invisible en ccw == *)
assert (H1 : ~ blue_dart mr (A_1 mr one x)).
 apply red_not_blue; apply (blue_A_1_red mr x Hmap Hpoly Hx1).
generalize Hx2; clear Hx2; unfold invisible.
elim blue_dart_dec; intro H2; [contradiction | intro Hx2; clear H1 H2].
assert (H1 : exd mr (A_1 mr zero (A_1 mr one x))).
 apply pred_exd_A_1; try assumption.
 generalize (blue_A_1_red mr x Hmap Hpoly Hx1).
 unfold red_dart; intuition.
assert (H2 : exd mr (A_1 mr one x)).
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hx1; intuition.
assert (H3 : fpoint mr (A_1 mr zero (A_1 mr one x)) <> fpoint mr (A_1 mr one x)).
 apply neq_sym_point; apply well_emb_A_1_zero; try assumption.
 generalize (blue_A_1_red mr x Hmap Hpoly Hx1).
 unfold red_dart; intuition.
generalize (Halign (A_1 mr zero (A_1 mr one x)) (A_1 mr one x) H1 H2 H3).
elim Hx2; clear Hx2; [idtac|contradiction].
intros Hx2 H; clear H1 H2 H3 H.
generalize Hx3; clear Hx3; unfold visible.
elim blue_dart_dec; intro H1; [intro Hx3; clear H1 | contradiction].
(**)
assert (H1 : ~ blue_dart mr (A_1 mr one y)).
 apply red_not_blue; apply (blue_A_1_red mr y Hmap Hpoly Hy1).
generalize Hy2; clear Hy2; unfold invisible.
elim blue_dart_dec; intro H2; [contradiction | intro Hy2; clear H1 H2].
assert (H1 : exd mr (A_1 mr zero (A_1 mr one y))).
 apply pred_exd_A_1; try assumption.
 generalize (blue_A_1_red mr y Hmap Hpoly Hy1).
 unfold red_dart; intuition.
assert (H2 : exd mr (A_1 mr one y)).
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hy1; intuition.
assert (H3 : fpoint mr (A_1 mr zero (A_1 mr one y)) <> fpoint mr (A_1 mr one y)).
 apply neq_sym_point; apply well_emb_A_1_zero; try assumption.
 generalize (blue_A_1_red mr y Hmap Hpoly Hy1).
 unfold red_dart; intuition.
generalize (Halign (A_1 mr zero (A_1 mr one y)) (A_1 mr one y) H1 H2 H3).
elim Hy2; clear Hy2; [idtac|contradiction].
intros Hy2 H; clear H1 H2 H3 H.
generalize Hy3; clear Hy3; unfold visible.
elim blue_dart_dec; intro H1; [intro Hy3; clear H1 | contradiction].
(* == == == *)
assert (Hx0 : exd mr x).
 apply (succ_exd mr zero x); try assumption.
 unfold blue_dart in Hx1; intuition.
assert (Hy0 : exd mr y).
 apply (succ_exd mr zero y); try assumption.
 unfold blue_dart in Hy1; intuition.
(**)
assert (Hp0 : fpoint mr x <> fpoint mr y).
 generalize (Hemb x Hx0).
 intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
 apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  apply neq_sym; assumption.
  apply exd_not_exd_neq with mr; try assumption.
   unfold blue_dart, succ, pred in Hx1.
   destruct Hx1 as [Hx1a [Hx1b [Hx1c Hx1d]]].
   apply not_neq_eq in Hx1b; rewrite Hx1b.
   apply not_exd_nil; assumption.
  elim (eq_dart_dec y (A_1 mr one x)).
   intro Heq0; rewrite Heq0 in Hy1.
   apply (blue_A_1_red mr) in Hx1; try assumption.
   apply blue_not_red in Hy1; contradiction.
   intro Heq0; assumption.
assert (Hp1 : (fpoint mr x) = (fpoint mr (A_1 mr one x))).
apply (well_emb_A_1_one mr x); try assumption.
 unfold blue_dart in Hx1; intuition.
assert (Hp2 : (fpoint mr y) = (fpoint mr (A_1 mr one y))).
apply (well_emb_A_1_one mr y); try assumption.
 unfold blue_dart in Hy1; intuition.
(**)
assert (Hexd1 : exd mr (A mr zero x)).
 apply (succ_exd_A mr zero x); try assumption.
 unfold blue_dart in Hx1; intuition.
assert (Hexd2 : exd mr (A_1 mr one x)).
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hx1; intuition.
assert (Hexd3 : exd mr (A_1 mr zero (A_1 mr one x))).
 apply pred_exd_A_1; try assumption.
 generalize (blue_A_1_red mr x Hmap Hpoly Hx1).
 unfold red_dart; intuition.
(**)
assert (Hp3 : fpoint mr y <> fpoint mr (A mr zero x)).
 generalize (Hemb y Hy0).
 intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
 apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  elim (eq_dart_dec y (A mr zero x)).
   intro Heq0; rewrite Heq0 in Hy1.
   apply (blue_A_red mr) in Hx1; try assumption.
   apply blue_not_red in Hy1; contradiction.
   intro Heq0; apply neq_sym; assumption.
  apply exd_not_exd_neq with mr; try assumption.
   unfold blue_dart, succ, pred in Hy1.
   destruct Hy1 as [Hy1a [Hy1b [Hy1c Hy1d]]].
   apply not_neq_eq in Hy1b; rewrite Hy1b.
   apply not_exd_nil; assumption.
  elim (eq_dart_dec (A mr zero x) (A_1 mr one y)).
   intro Heq0; rewrite <- Heq0 in Hy2.
   rewrite <- A_1_A with mr zero x in Hy2; try assumption.
   apply axiom_orientation_4 in Hy2; contradiction.
   intro Heq0; assumption.
(**)
elim (eq_point_dec_2 (fpoint mr (A mr zero x)) (fpoint mr (A_1 mr zero (A_1 mr one x)))); intro Hp4.
 assert (Hccw1 : ccw (fpoint mr x) (fpoint mr (A mr zero x)) (fpoint mr y)).
  apply (Hconv x Hx0 Hx1 y Hy0); try assumption.
  apply neq_sym_point; assumption.
 assert (Hccw2 : ccw (fpoint mr x) (fpoint mr y) (fpoint mr (A mr zero x))).
  rewrite Hp4; rewrite Hp1; apply ccw_axiom_1.
  assert (H1 : (A_1 mr one x) = (A mr zero (A_1 mr zero (A_1 mr one x)))).
   apply A_A_1; try assumption.
  pattern (A_1 mr one x) at 2; rewrite H1.
  assert (H2 : blue_dart mr (A_1 mr zero (A_1 mr one x))).
   apply red_A_1_blue; try assumption.
   apply blue_A_1_red; try assumption.
  apply (Hconv (A_1 mr zero (A_1 mr one x)) Hexd3 H2 y Hy0).
   rewrite <- Hp4; assumption.
   rewrite <- H1; rewrite <- Hp1.
   apply neq_sym_point; assumption.
 apply axiom_orientation_4 in Hccw2; contradiction.
(**)
assert (Hexd4 : exd mr (A mr zero y)).
 apply (succ_exd_A mr zero y); try assumption.
 unfold blue_dart in Hy1; intuition.
assert (Hexd5 : exd mr (A_1 mr one y)).
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hy1; intuition.
assert (Hexd6 : exd mr (A_1 mr zero (A_1 mr one y))).
 apply pred_exd_A_1; try assumption.
 generalize (blue_A_1_red mr y Hmap Hpoly Hy1).
 unfold red_dart; intuition.
(**)
assert (Hp5 : fpoint mr x <> fpoint mr (A mr zero y)).
 generalize (Hemb x Hx0).
 intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
 apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  elim (eq_dart_dec x (A mr zero y)).
   intro Heq0; rewrite Heq0 in Hx1.
   apply (blue_A_red mr) in Hy1; try assumption.
   apply blue_not_red in Hx1; contradiction.
   intro Heq0; apply neq_sym; assumption.
  apply exd_not_exd_neq with mr; try assumption.
   unfold blue_dart, succ, pred in Hx1.
   destruct Hx1 as [Hx1a [Hx1b [Hx1c Hx1d]]].
   apply not_neq_eq in Hx1b; rewrite Hx1b.
   apply not_exd_nil; assumption.
  elim (eq_dart_dec (A mr zero y) (A_1 mr one x)).
   intro Heq0; rewrite <- Heq0 in Hx2.
   rewrite <- A_1_A with mr zero y in Hx2; try assumption.
   apply axiom_orientation_4 in Hx2; contradiction.
   intro Heq0; assumption.
(**)
elim (eq_point_dec_2 (fpoint mr (A mr zero y)) (fpoint mr (A_1 mr zero (A_1 mr one y)))); intro Hp6.
 assert (Hccw1 : ccw (fpoint mr y) (fpoint mr (A mr zero y)) (fpoint mr x)).
  apply (Hconv y Hy0 Hy1 x Hx0); try assumption.
 assert (Hccw2 : ccw (fpoint mr y) (fpoint mr x) (fpoint mr (A mr zero y))).
  rewrite Hp6; rewrite Hp2; apply ccw_axiom_1.
  assert (H1 : (A_1 mr one y) = (A mr zero (A_1 mr zero (A_1 mr one y)))).
   apply A_A_1; try assumption.
  pattern (A_1 mr one y) at 2; rewrite H1.
  assert (H2 : blue_dart mr (A_1 mr zero (A_1 mr one y))).
   apply red_A_1_blue; try assumption.
   apply blue_A_1_red; try assumption.
  apply (Hconv (A_1 mr zero (A_1 mr one y)) Hexd6 H2 x Hx0).
   rewrite <- Hp6; assumption.
   rewrite <- H1; rewrite <- Hp2; assumption.
 apply axiom_orientation_4 in Hccw2; contradiction.
(* == Proof of (ccw APD) == *)
assert (Hccw1 : ccw (fpoint mr x) p (fpoint mr y)).
apply (ccw_axiom_5_bis p (fpoint mr (A mr zero x)) (fpoint mr y) (fpoint mr (A_1 mr zero (A_1 mr one x))) (fpoint mr x)).
(* = ccw CAP = *)
rewrite Hp1; assumption.
(* = ccw CAB = *)
apply ccw_axiom_1; apply ccw_axiom_1.
apply (Hconv x Hx0 Hx1 (A_1 mr zero (A_1 mr one x)) Hexd3).
 (* A <> C *)
 apply ccw_neq_point with p; rewrite Hp1; assumption.
 (* B <> C *)
 apply neq_sym_point; assumption.
(* = ccw CAD = *)
assert (H1 : (A_1 mr one x) = (A mr zero (A_1 mr zero (A_1 mr one x)))).
 apply A_A_1; try assumption.
rewrite Hp1; pattern (A_1 mr one x) at 2; rewrite H1.
assert (H2 : blue_dart mr (A_1 mr zero (A_1 mr one x))).
 apply red_A_1_blue; try assumption.
 apply blue_A_1_red; try assumption.
apply (Hconv (A_1 mr zero (A_1 mr one x)) Hexd3 H2 y Hy0).
 (* C <> D *)
 generalize (Hemb y Hy0).
 intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
 apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  elim (eq_dart_dec y (A_1 mr zero (A_1 mr one x))).
   intro Heq1; rewrite <- Heq1 in *; rewrite H1 in Hx2.
   apply axiom_orientation_4 in Hx2; contradiction.
   intro Heq1; apply neq_sym; assumption.
  apply exd_not_exd_neq with mr; try assumption.
   unfold blue_dart, succ, pred in Hy1.
   destruct Hy1 as [Hy1a [Hy1b [Hy1c Hy1d]]].
   apply not_neq_eq in Hy1b; rewrite Hy1b.
   apply not_exd_nil; assumption.
  elim (eq_dart_dec (A_1 mr zero (A_1 mr one x)) (A_1 mr one y)).
   intro Heq1; rewrite Heq1 in H2.
   apply (blue_A_1_red mr) in Hy1; try assumption.
   apply blue_not_red in H2; contradiction.
   intro Heq1; assumption.
 (* A <> D *)
 rewrite <- H1; rewrite <- Hp1.
 apply neq_sym_point; assumption.
(* = ccw APB = *)
assumption.
(* = ccw ABD = *)
apply (Hconv x Hx0 Hx1 y Hy0).
 (* A <> D *)
 apply neq_sym_point; assumption.
 (* B <> D *)
 assumption.
(* == Proof of (ccw DPA) == *)
assert (Hccw2 : ccw (fpoint mr y) p (fpoint mr x)).
apply (ccw_axiom_5_bis p (fpoint mr (A mr zero y)) (fpoint mr x) (fpoint mr (A_1 mr zero (A_1 mr one y))) (fpoint mr y)).
(* = ccw FDP = *)
rewrite Hp2; assumption.
(* = ccw FDE = *)
apply ccw_axiom_1; apply ccw_axiom_1.
apply (Hconv y Hy0 Hy1 (A_1 mr zero (A_1 mr one y)) Hexd6).
 (* D <> F *)
 apply ccw_neq_point with p; rewrite Hp2; assumption.
 (* E <> F *)
 apply neq_sym_point; assumption.
(* = ccw FDA = *)
assert (H1 : (A_1 mr one y) = (A mr zero (A_1 mr zero (A_1 mr one y)))).
 apply A_A_1; try assumption.
rewrite Hp2; pattern (A_1 mr one y) at 2; rewrite H1.
assert (H2 : blue_dart mr (A_1 mr zero (A_1 mr one y))).
 apply red_A_1_blue; try assumption.
 apply blue_A_1_red; try assumption.
apply (Hconv (A_1 mr zero (A_1 mr one y)) Hexd6 H2 x Hx0).
 (* A <> F *)
 generalize (Hemb x Hx0).
 intros [Hemb1 [Hemb2 [Hemb3 [Hemb4 Hemb5]]]].
 apply Hemb5; try assumption; clear Hemb1 Hemb2 Hemb3 Hemb4 Hemb5.
  elim (eq_dart_dec x (A_1 mr zero (A_1 mr one y))).
   intro Heq1; rewrite <- Heq1 in *; rewrite H1 in Hy2.
   apply axiom_orientation_4 in Hy2; contradiction.
   intro Heq1; apply neq_sym; assumption.
  apply exd_not_exd_neq with mr; try assumption.
   unfold blue_dart, succ, pred in Hx1.
   destruct Hx1 as [Hx1a [Hx1b [Hx1c Hx1d]]].
   apply not_neq_eq in Hx1b; rewrite Hx1b.
   apply not_exd_nil; assumption.
  elim (eq_dart_dec (A_1 mr zero (A_1 mr one y)) (A_1 mr one x)).
   intro Heq1; rewrite Heq1 in H2.
   apply (blue_A_1_red mr) in Hx1; try assumption.
   apply blue_not_red in H2; contradiction.
   intro Heq1; assumption.
 (* A <> D *)
 rewrite <- H1; rewrite <- Hp2; assumption.
(* = ccw DPE = *)
assumption.
(* = ccw DEA = *)
apply (Hconv y Hy0 Hy1 x Hx0).
 (* A <> D *)
 assumption.
 (* A <> E *)
 assumption.
(* == == *)
 apply ccw_axiom_1 in Hccw1.
 apply ccw_axiom_1 in Hccw1.
 apply ccw_axiom_2 in Hccw1.
 contradiction.
Qed.

Axiom one_right :
  forall (mr:fmap)(p:point)(x:dart)(y:dart),
  inv_hmap mr -> inv_poly mr -> well_emb mr ->
  inv_noalign_point mr p -> convex mr ->
  right_dart mr p x -> right_dart mr p y -> x = y.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma succ_A_cA :
  forall (m:fmap)(k:dim)(d:dart), 
  inv_hmap m -> exd m d -> succ m k d ->
  A m k d = cA m k d.
Proof.
intros m k d Hmap Hexd Hsucc.
assert (H0 : exd m (A m k d)).
apply (succ_exd_A m k d Hmap Hsucc).
generalize (A_cA m k d (A m k d) Hmap Hexd H0).
intuition.
Qed.

Lemma pred_A_1_cA_1 :
  forall (m:fmap)(k:dim)(d:dart), 
  inv_hmap m -> exd m d -> pred m k d ->
  A_1 m k d = cA_1 m k d.
Proof.
intros m k d Hmap Hexd Hpred.
assert (H0 : exd m (A_1 m k d)).
apply (pred_exd_A_1 m k d Hmap Hpred).
generalize (A_1_cA_1 m k d (A_1 m k d) Hmap Hexd H0).
intuition.
Qed.

(* ========================== *)

Lemma A_cA_1 :
  forall (m:fmap)(k:dim)(d:dart), 
  inv_hmap m -> exd m d ->
  succ m k d -> ~ pred m k d -> ~ succ m k (A m k d) ->
  A m k d = cA_1 m k d.
Proof.
intros m k d Hmap Hexd H1 H2 H3.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 elim (eq_dart_dec d0 d); intro Heq.
  subst d0; clear IHm Hexd.
  unfold succ, pred in *; simpl in *.
  rewrite not_exd_A_nil in H1; try tauto.
  elim Hexd; clear Hexd; intro Hexd.
   contradiction.
   apply IHm; try assumption.
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in *.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
 generalize H1 H2 H3; clear H1 H2 H3.
 unfold succ, pred; simpl. 
 elim (eq_dim_dec d0 k); intro Hdim; try subst d0.
(**)
elim (eq_dart_dec d1 d); intro Heq1; try subst d1.
 elim (eq_dart_dec d2 d); intro Heq2; try subst d2.
  elimeqdartdec; intros H1 H2 H3; tauto.
  elimeqdartdec; intros H1 H2 H3.
  elim (eq_dart_dec (cA m k d) d); intro Heq3.
   apply sym_eq; apply fixpoint_cA_1; try assumption.
   assert (H0 : cA m k d = d); [idtac|contradiction].
    apply fixpoint_cA; try assumption.
 elim (eq_dart_dec d2 d); intro Heq2; try subst d2.
  intros H1 H2 H3; apply exd_not_nil in Hmap1; tauto.
  elim (eq_dart_dec d1 (A m k d)); intro Heq3.
   intros H1 H2 H3; apply exd_not_nil in Hmap2; tauto.
   intros H1 H2 H3.
   elim (eq_dart_dec (cA m k d1) d); intro Heq5.
    generalize (IHm Hmap Hexd H1 H2 H3).
    intro H; pattern d at 2 in H; rewrite <- Heq5 in H.
    rewrite cA_1_cA in H; try assumption.
    apply sym_eq in H; contradiction.
    apply IHm; try assumption.
(**)
apply IHm; assumption.
Qed.

Lemma A_1_cA :
  forall (m:fmap)(k:dim)(d:dart), 
  inv_hmap m -> exd m d ->
  pred m k d -> ~ succ m k d -> ~ pred m k (A_1 m k d) ->
  A_1 m k d = cA m k d.
Proof.
intros m k d Hmap Hexd H1 H2 H3.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 elim (eq_dart_dec d0 d); intro Heq.
  subst d0; clear IHm Hexd.
  unfold succ, pred in *; simpl in *.
  rewrite not_exd_A_1_nil in H1; try tauto.
  elim Hexd; clear Hexd; intro Hexd.
   contradiction.
   apply IHm; try assumption.
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in *.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
 generalize H1 H2 H3; clear H1 H2 H3.
 unfold succ, pred; simpl. 
 elim (eq_dim_dec d0 k); intro Hdim; try subst d0.
(**)
elim (eq_dart_dec d2 d); intro Heq1; try subst d2.
 elim (eq_dart_dec d1 d); intro Heq2; try subst d1.
  elimeqdartdec; intros H1 H2 H3; tauto.
  elimeqdartdec; intros H1 H2 H3.
  elim (eq_dart_dec (cA_1 m k d) d); intro Heq3.
   apply sym_eq; apply fixpoint_cA; try assumption.
   assert (H0 : cA_1 m k d = d); [idtac|contradiction].
    apply fixpoint_cA_1; try assumption.
 elim (eq_dart_dec d1 d); intro Heq2; try subst d1.
  intros H1 H2 H3; apply exd_not_nil in Hmap2; tauto.
  elim (eq_dart_dec d2 (A_1 m k d)); intro Heq3.
   intros H1 H2 H3; apply exd_not_nil in Hmap1; tauto.
   intros H1 H2 H3.
   elim (eq_dart_dec (cA_1 m k d2) d); intro Heq5.
    generalize (IHm Hmap Hexd H1 H2 H3).
    intro H; pattern d at 2 in H; rewrite <- Heq5 in H.
    rewrite cA_cA_1 in H; try assumption.
    apply sym_eq in H; contradiction.
    apply IHm; try assumption.
(**)
apply IHm; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma not_exd_cF_nil :
  forall (m:fmap)(d:dart), 
  inv_hmap m -> ~ exd m d -> cF m d = nil.
Proof.
intros m d Hmap Hexd; unfold cF.
generalize (not_exd_cA_1 m zero d Hmap Hexd).
intro H1; rewrite H1.
apply (not_exd_cA_1 m one nil Hmap (not_exd_nil m Hmap)).
Qed.

Lemma not_exd_cF_1_nil :
  forall (m:fmap)(d:dart), 
  inv_hmap m -> ~ exd m d -> cF_1 m d = nil.
Proof.
intros m d Hmap Hexd; unfold cF_1.
generalize (not_exd_cA m one d Hmap Hexd).
intro H1; rewrite H1.
apply (not_exd_cA m zero nil Hmap (not_exd_nil m Hmap)).
Qed.

(* ========================== *)

Lemma inv_poly_cF :
  forall (m:fmap)(d:dart), 
  inv_hmap m -> inv_poly m -> exd m d ->
  cF m d =
  if (blue_dart_dec m d) then A m one (A m zero d)
  else if (red_dart_dec m d) then A_1 m one (A_1 m zero d)
  else (* black_dart m d *) d.
Proof.
intros m d Hmap Hpoly Hexd; unfold cF.
elim (blue_dart_dec m d); intro Hblue.
 apply sym_eq; rewrite <- A_cA_1 with m zero d; try tauto.
 apply A_cA_1; try tauto.
 apply succ_exd_A; try assumption.
 unfold blue_dart in Hblue; tauto.
 apply blue_A_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
 apply blue_A_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
 apply blue_A_red in Hblue; try assumption.
 apply red_A_blue in Hblue; try assumption.
 unfold blue_dart in *; intuition.
 unfold blue_dart in *; intuition.
 unfold blue_dart in *; intuition.
 apply blue_A_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
elim (red_dart_dec m d); intro Hred.
 rewrite pred_A_1_cA_1; try assumption.
 rewrite pred_A_1_cA_1; try assumption.
 trivial.
 unfold red_dart in *; intuition.
 apply pred_exd_A_1; try assumption.
 unfold red_dart in *; intuition.
 apply red_A_1_blue in Hred; try assumption.
 unfold blue_dart in *; intuition.
assert (Hblack : black_dart m d).
generalize (Hpoly d Hexd); clear Hpoly; tauto.
unfold black_dart in Hblack.
destruct Hblack as [H1 [H2 [H3 H4]]].
generalize (fixpt_cA_cA_1 m zero d Hmap Hexd H1 H3).
intros [H_1 H_2]; rewrite H_2.
generalize (fixpt_cA_cA_1 m one d Hmap Hexd H2 H4).
intros [H_3 H_4]; rewrite H_4.
trivial.
Qed.

Lemma inv_poly_cF_1 :
  forall (m:fmap)(d:dart), 
  inv_hmap m -> inv_poly m -> exd m d ->
  cF_1 m d =
  if (blue_dart_dec m d) then A_1 m zero (A_1 m one d)
  else if (red_dart_dec m d) then A m zero (A m one d)
  else (* black_dart m d *) d.
Proof.
intros m d Hmap Hpoly Hexd; unfold cF_1.
elim (blue_dart_dec m d); intro Hblue.
 apply sym_eq; rewrite <- A_1_cA with m one d; try tauto.
 apply A_1_cA; try tauto.
 apply pred_exd_A_1; try assumption.
 unfold blue_dart in Hblue; tauto.
 apply blue_A_1_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
 apply blue_A_1_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
 apply blue_A_1_red in Hblue; try assumption.
 apply red_A_1_blue in Hblue; try assumption.
 unfold blue_dart in *; intuition.
 unfold blue_dart in *; intuition.
 unfold blue_dart in *; intuition.
 apply blue_A_1_red in Hblue; try assumption.
 unfold red_dart in *; intuition.
elim (red_dart_dec m d); intro Hred.
 rewrite succ_A_cA; try assumption.
 rewrite succ_A_cA; try assumption.
 trivial.
 unfold red_dart in *; intuition.
 apply succ_exd_A; try assumption.
 unfold red_dart in *; intuition.
 apply red_A_blue in Hred; try assumption.
 unfold blue_dart in *; intuition.
assert (Hblack : black_dart m d).
generalize (Hpoly d Hexd); clear Hpoly; tauto.
unfold black_dart in Hblack.
destruct Hblack as [H1 [H2 [H3 H4]]].
generalize (fixpt_cA_cA_1 m one d Hmap Hexd H2 H4).
intros [H_1 H_2]; rewrite H_1.
generalize (fixpt_cA_cA_1 m zero d Hmap Hexd H1 H3).
intros [H_3 H_4]; rewrite H_3.
trivial.
Qed.

(* ========================== *)

Lemma blue_cF_blue :
  forall (m:fmap)(d:dart)(i:nat), 
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d ->
  blue_dart m (Iter (cF m) i d).
Proof.
intros m d i Hmap Hpoly Hexd Hblue.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 simpl in *.
 assert (H0 : exd m (Iter (cF m) i d)).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in IHi; tauto.
 assert (H : cF m (Iter (cF m) i d) = A m one (A m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H0).
  elim blue_dart_dec; intro H1; [trivial|contradiction].
 rewrite H; apply red_A_blue; try assumption.
 apply blue_A_red; try assumption.
Qed.

Lemma blue_cF_1_blue :
  forall (m:fmap)(d:dart)(i:nat), 
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d ->
  blue_dart m (Iter (cF_1 m) i d).
Proof.
intros m d i Hmap Hpoly Hexd Hblue.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 simpl in *.
 assert (H0 : exd m (Iter (cF_1 m) i d)).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in IHi; tauto.
 assert (H : cF_1 m (Iter (cF_1 m) i d) = A_1 m zero (A_1 m one (Iter (cF_1 m) i d))).
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H0).
  elim blue_dart_dec; intro H1; [trivial|contradiction].
 rewrite H; apply red_A_1_blue; try assumption.
 apply blue_A_1_red; try assumption.
Qed.

Lemma red_cF_red :
  forall (m:fmap)(d:dart)(i:nat), 
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d ->
  red_dart m (Iter (cF m) i d).
Proof.
intros m d i Hmap Hpoly Hexd Hred.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 simpl in *.
 assert (H0 : exd m (Iter (cF m) i d)).
  apply succ_exd with one; try assumption.
  unfold red_dart in IHi; tauto.
 assert (H : cF m (Iter (cF m) i d) = A_1 m one (A_1 m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H0).
  elim blue_dart_dec; intro H1.
   apply red_not_blue in IHi; contradiction.
  elim red_dart_dec; intro H2; [trivial|contradiction].
 rewrite H; apply blue_A_1_red; try assumption.
 apply red_A_1_blue; try assumption.
Qed.

Lemma red_cF_1_red :
  forall (m:fmap)(d:dart)(i:nat), 
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d ->
  red_dart m (Iter (cF_1 m) i d).
Proof.
intros m d i Hmap Hpoly Hexd Hred.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 simpl in *.
 assert (H0 : exd m (Iter (cF_1 m) i d)).
  apply succ_exd with one; try assumption.
  unfold red_dart in IHi; tauto.
 assert (H : cF_1 m (Iter (cF_1 m) i d) = A m zero (A m one (Iter (cF_1 m) i d))).
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H0).
  elim blue_dart_dec; intro H1.
   apply red_not_blue in IHi; contradiction.
  elim red_dart_dec; intro H2; [trivial|contradiction].
 rewrite H; apply blue_A_red; try assumption.
 apply red_A_blue; try assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma blue_dart_not_left_dart_until_i_visible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (Iter (cF_1 m) j d)) ->
  visible m (Iter (cF_1 m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hblue Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H1 : ~ left_dart m p (Iter (cF_1 m) i d)).
  apply (H i (le_n_Sn i)).
 assert (H2 : blue_dart m (Iter (cF_1 m) i d)).
  apply blue_cF_1_blue; try assumption.
 assert (H3 : visible m (Iter (cF_1 m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold left_dart in H1; simpl in *; clear H IHi.
 assert (H0 : ~ invisible m (A_1 m one (Iter (cF_1 m) i d)) p).
  intuition.
 apply not_invisible_visible in H0; clear H1 H3.
 assert (H1 : cF_1 m (Iter (cF_1 m) i d) = A_1 m zero (A_1 m one (Iter (cF_1 m) i d))).
  assert (H1 : exd m (Iter (cF_1 m) i d)).
   apply succ_exd with zero; try assumption.
   unfold blue_dart in H2; tauto. 
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H1).
  elim blue_dart_dec; intro He1; [trivial|contradiction].
 rewrite H1 in *; clear H1.
 apply visible_A_1_visible; try assumption.
  apply pred_exd_A_1; try assumption.
  unfold blue_dart in H2; tauto.
  apply blue_A_1_red; assumption.
Qed.

Lemma blue_dart_not_left_dart_until_i_visible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (Iter (cF_1 m) j d)) ->
  (forall (j:nat), j <= i -> visible m (Iter (cF_1 m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply blue_dart_not_left_dart_until_i_visible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma blue_dart_not_right_dart_until_i_visible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (A m zero (Iter (cF m) j d))) ->
  visible m (Iter (cF m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hblue Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : blue_dart m (Iter (cF m) i d)).
  apply blue_cF_blue; try assumption.
 assert (H02 : exd m (Iter (cF m) i d)).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H01; tauto.
 assert (H1 : ~ right_dart m p (A m zero (Iter (cF m) i d))).
  apply (H i (le_n_Sn i)).
 assert (H2 : red_dart m (A m zero (Iter (cF m) i d))).
  apply blue_A_red; try assumption.
 assert (H3 : visible m (Iter (cF m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold right_dart in H1; simpl in *; clear H IHi.
 apply visible_A_visible in H3; try assumption.
 assert (H0 : ~ invisible m (A m one (A m zero (Iter (cF m) i d))) p).
  intuition.
 apply not_invisible_visible in H0; clear H1 H3.
 assert (H1 : cF m (Iter (cF m) i d) = A m one (A m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1; [trivial|contradiction].
 rewrite H1 in *; clear H1; assumption.
Qed.

Lemma blue_dart_not_right_dart_until_i_visible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (A m zero (Iter (cF m) j d))) ->
  (forall (j:nat), j <= i -> visible m (Iter (cF m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply blue_dart_not_right_dart_until_i_visible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma red_dart_not_left_dart_until_i_visible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (A_1 m zero (Iter (cF m) j d))) ->
  visible m (Iter (cF m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : red_dart m (Iter (cF m) i d)).
  apply red_cF_red; try assumption.
 assert (H02 : exd m (Iter (cF m) i d)).
  apply succ_exd with one; try assumption.
  unfold red_dart in H01; tauto. 
 assert (H1 : ~ left_dart m p (A_1 m zero (Iter (cF m) i d))).
  apply (H i (le_n_Sn i)).
 assert (H2 : blue_dart m (A_1 m zero (Iter (cF m) i d))).
  apply red_A_1_blue; try assumption.
 assert (H3 : visible m (Iter (cF m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold left_dart in H1; simpl in *; clear H IHi.
 apply visible_A_1_visible in H3; try assumption.
 assert (H0 : ~ invisible m (A_1 m one (A_1 m zero (Iter (cF m) i d))) p).
  intuition.
 apply not_invisible_visible in H0; clear H1 H3.
 assert (H1 : cF m (Iter (cF m) i d) = A_1 m one (A_1 m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1.
   apply red_not_blue in H01; contradiction.
  elim red_dart_dec; intro He2; [trivial|contradiction].
 rewrite H1 in *; clear H1; assumption.
Qed.

Lemma red_dart_not_left_dart_until_i_visible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (A_1 m zero (Iter (cF m) j d))) ->
  (forall (j:nat), j <= i -> visible m (Iter (cF m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply red_dart_not_left_dart_until_i_visible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma red_dart_not_right_dart_until_i_visible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (Iter (cF_1 m) j d)) ->
  visible m (Iter (cF_1 m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H1 : ~ right_dart m p (Iter (cF_1 m) i d)).
  apply (H i (le_n_Sn i)).
 assert (H2 : red_dart m (Iter (cF_1 m) i d)).
  apply red_cF_1_red; try assumption.
 assert (H3 : visible m (Iter (cF_1 m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold right_dart in H1; simpl in *; clear H IHi.
 assert (H0 : ~ invisible m (A m one (Iter (cF_1 m) i d)) p).
  intuition.
 apply not_invisible_visible in H0; clear H1 H3.
 assert (H1 : cF_1 m (Iter (cF_1 m) i d) = A m zero (A m one (Iter (cF_1 m) i d))).
  assert (H1 : exd m (Iter (cF_1 m) i d)).
   apply succ_exd with one; try assumption.
   unfold red_dart in H2; tauto. 
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H1).
  elim blue_dart_dec; intro He1.
   apply red_not_blue in H2; contradiction.
  elim red_dart_dec; intro He2; [trivial|contradiction].
 rewrite H1 in *; clear H1.
 apply visible_A_visible; try assumption.
  apply succ_exd_A; try assumption.
  unfold red_dart in H2; tauto.
  apply red_A_blue; assumption.
Qed.

Lemma red_dart_not_right_dart_until_i_visible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> visible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (Iter (cF_1 m) j d)) ->
  (forall (j:nat), j <= i -> visible m (Iter (cF_1 m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply red_dart_not_right_dart_until_i_visible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma blue_dart_not_left_dart_until_i_invisible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (Iter (cF m) j d)) ->
  invisible m (Iter (cF m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hblue Hinv H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : blue_dart m (Iter (cF m) i d)).
  apply blue_cF_blue; try assumption.
 assert (H02 : exd m (Iter (cF m) i d)).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H01; tauto.
 assert (H1 : ~ left_dart m p (Iter (cF m) (S i) d)).
  apply (H (S i) (le_refl (S i))).
 assert (H2 : blue_dart m (Iter (cF m) (S i) d)).
  apply blue_cF_blue; try assumption.
 assert (H3 : invisible m (Iter (cF m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold left_dart in H1; simpl in *; clear H IHi.
 assert (H4 : cF m (Iter (cF m) i d) = A m one (A m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1; [trivial|contradiction].
 rewrite H4 in *; clear H4.
 apply invisible_A_invisible in H3; try assumption.
 rewrite <- A_1_A in H1; try assumption.
 assert (H0 : ~ visible m (A m one (A m zero (Iter (cF m) i d))) p).
  intuition.
 apply not_visible_invisible in H0; clear H1 H2 H3; assumption.
 apply succ_exd_A; try assumption.
 unfold blue_dart in H01; tauto.
 apply succ_exd_A; try assumption.
 apply blue_A_red in H01; try assumption.
 unfold red_dart in H01; tauto.
Qed.

Lemma blue_dart_not_left_dart_until_i_invisible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (Iter (cF m) j d)) ->
  (forall (j:nat), j <= i -> invisible m (Iter (cF m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply blue_dart_not_left_dart_until_i_invisible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma blue_dart_not_right_dart_until_i_invisible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (A m zero (Iter (cF_1 m) j d))) ->
  invisible m (Iter (cF_1 m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hblue Hinv H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : blue_dart m (Iter (cF_1 m) i d)).
  apply blue_cF_1_blue; try assumption.
 assert (H02 : exd m (Iter (cF_1 m) i d)).
  apply succ_exd with zero; try assumption.
  unfold blue_dart in H01; tauto.
 assert (H1 : ~ right_dart m p (A m zero (Iter (cF_1 m) (S i) d))).
  apply (H (S i) (le_refl (S i))).
 assert (H2 : red_dart m (A m zero (Iter (cF_1 m) (S i) d))).
  apply blue_A_red; try assumption.
  apply blue_cF_1_blue; try assumption.
 assert (H3 : invisible m (Iter (cF_1 m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold right_dart in H1; simpl in *; clear H IHi.
 assert (H4 : cF_1 m (Iter (cF_1 m) i d) = A_1 m zero (A_1 m one (Iter (cF_1 m) i d))).
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1; [trivial|contradiction].
 rewrite H4 in *; clear H4.
 assert (H03 : exd m (A_1 m one (Iter (cF_1 m) i d))).
  apply pred_exd_A_1; try assumption;
  unfold blue_dart in H01; tauto.
 rewrite <- A_A_1 in H1; try assumption.
 rewrite <- A_A_1 in H1; try assumption.
 rewrite <- A_A_1 in H2; try assumption.
 assert (H0 : ~ visible m (A_1 m one (Iter (cF_1 m) i d)) p).
  intuition.
 apply not_visible_invisible in H0; clear H1 H2 H3.
 apply invisible_A_1_invisible; try assumption.
 apply blue_A_1_red; try assumption.
 apply pred_exd_A_1; try assumption.
 apply blue_A_1_red in H01; try assumption.
 unfold red_dart in H01; tauto.
 apply pred_exd_A_1; try assumption.
 apply blue_A_1_red in H01; try assumption.
 unfold red_dart in H01; tauto.
Qed.

Lemma blue_dart_not_right_dart_until_i_invisible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> blue_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (A m zero (Iter (cF_1 m) j d))) ->
  (forall (j:nat), j <= i -> invisible m (Iter (cF_1 m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply blue_dart_not_right_dart_until_i_invisible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma red_dart_not_left_dart_until_i_invisible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (A_1 m zero (Iter (cF_1 m) j d))) ->
  invisible m (Iter (cF_1 m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : red_dart m (Iter (cF_1 m) i d)).
  apply red_cF_1_red; try assumption.
 assert (H02 : exd m (Iter (cF_1 m) i d)).
  apply succ_exd with one; try assumption.
  unfold red_dart in H01; tauto. 
 assert (H1 : ~ left_dart m p (A_1 m zero (Iter (cF_1 m) (S i) d))).
  apply (H (S i) (le_refl (S i))).
 assert (H2 : blue_dart m (A_1 m zero (Iter (cF_1 m) (S i) d))).
  apply red_A_1_blue; try assumption.
  apply red_cF_1_red; try assumption.
 assert (H3 : invisible m (Iter (cF_1 m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold left_dart in H1; simpl in *; clear H IHi.
 assert (H4 : cF_1 m (Iter (cF_1 m) i d) = A m zero (A m one (Iter (cF_1 m) i d))).
  generalize (inv_poly_cF_1 m (Iter (cF_1 m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1.
   apply red_not_blue in H01; contradiction.
  elim red_dart_dec; intro He2; [trivial|contradiction].
 rewrite H4 in *; clear H4.
 assert (H03 : exd m (A m one (Iter (cF_1 m) i d))).
  apply succ_exd_A; try assumption;
  unfold red_dart in H01; tauto.
 rewrite <- A_1_A in H1; try assumption.
 rewrite <- A_1_A in H1; try assumption.
 rewrite <- A_1_A in H2; try assumption.
 assert (H0 : ~ visible m (A m one (Iter (cF_1 m) i d)) p).
  intuition.
 apply not_visible_invisible in H0; clear H1 H3.
 apply invisible_A_invisible; try assumption.
 apply succ_exd_A; try assumption.
 apply red_A_blue in H01; try assumption.
 unfold blue_dart in H01; tauto.
 apply succ_exd_A; try assumption.
 apply red_A_blue in H01; try assumption.
 unfold blue_dart in H01; tauto.
Qed.

Lemma red_dart_not_left_dart_until_i_invisible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ left_dart m p (A_1 m zero (Iter (cF_1 m) j d))) ->
  (forall (j:nat), j <= i -> invisible m (Iter (cF_1 m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply red_dart_not_left_dart_until_i_invisible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)

Lemma red_dart_not_right_dart_until_i_invisible_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (Iter (cF m) j d)) ->
  invisible m (Iter (cF m) i d) p.
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H.
induction i.
 (* Cas 1 = 0 *)
 simpl in *; assumption.
 (* Cas 2 = S i *)
 assert (H01 : red_dart m (Iter (cF m) i d)).
  apply red_cF_red; try assumption.
 assert (H02 : exd m (Iter (cF m) i d)).
  apply succ_exd with one; try assumption.
  unfold red_dart in H01; tauto. 
 assert (H1 : ~ right_dart m p (Iter (cF m) (S i) d)).
  apply (H (S i) (le_refl (S i))).
 assert (H2 : red_dart m (Iter (cF m) (S i) d)).
  apply red_cF_red; try assumption.
 assert (H3 : invisible m (Iter (cF m) i d) p).
  apply IHi; intros j Hle; apply H; omega.
 unfold right_dart in H1; simpl in *; clear H IHi.
 assert (H4 : cF m (Iter (cF m) i d) = A_1 m one (A_1 m zero (Iter (cF m) i d))).
  generalize (inv_poly_cF m (Iter (cF m) i d) Hmap Hpoly H02).
  elim blue_dart_dec; intro He1.
   apply red_not_blue in H01; contradiction.
  elim red_dart_dec; intro He2; [trivial|contradiction].
 rewrite H4 in *; clear H4.
 rewrite <- A_A_1 in H1; try assumption.
 apply invisible_A_1_invisible in H3; try assumption.
 assert (H0 : ~ visible m (A_1 m one (A_1 m zero (Iter (cF m) i d))) p).
  intuition.
 apply not_visible_invisible in H0; clear H1 H3; try assumption.
 apply pred_exd_A_1; try assumption.
 unfold red_dart in H01; tauto.
 apply pred_exd_A_1; try assumption.
 apply red_A_1_blue in H01; try assumption.
 unfold blue_dart in H01; tauto.
Qed.

Lemma red_dart_not_right_dart_until_i_invisible_until_i : 
  forall (m:fmap)(d:dart)(p:point)(i:nat),
  inv_hmap m -> inv_poly m ->
  exd m d -> red_dart m d -> invisible m d p ->
  (forall (j:nat), j <= i -> ~ right_dart m p (Iter (cF m) j d)) ->
  (forall (j:nat), j <= i -> invisible m (Iter (cF m) j d) p).
Proof.
intros m d p i Hmap Hpoly Hexd Hred Hvis H1 j H2.
induction i.
 (* Cas 1 = 0 *)
 assert (H : j=0); [omega|idtac].
 subst j; simpl in *; assumption.
 (* Cas 2 = S i *)
 elim (eq_nat_dec (S i) j); intro Heq; try subst j.
  apply red_dart_not_right_dart_until_i_invisible_i; try assumption.
  apply IHi. intros k Hk; apply H1; omega. omega.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Definition prop_dec (m:fmap)(p:point)(d:dart)(P:fmap->point->dart->nat->Prop) :=
  forall (i:nat), {P m p d i} + {~ P m p d i}.

Lemma exist_forall_i :
  forall (m:fmap)(p:point)(d:dart)(P:fmap->point->dart->nat->Prop)(k:nat),
  prop_dec m p d P -> {exists i:nat, (i < k) /\ P m p d i} + {forall i:nat, ~(i < k) \/ ~ P m p d i}.
Proof.
intros m p d P k Hdec.
induction k.
 right; intro i; left; omega.
 elim IHk; clear IHk.
  intro IHk; left.
   elim IHk; clear IHk; intros x IHk.
   exists x; split; [omega|tauto].
  intro IHk.
  generalize (Hdec k); clear Hdec.
  intro H; elim H; clear H.
   intro H; left.
   exists k; split; [omega|tauto].
   intro H; right; intro i.
   elim (eq_nat_dec i k); intro Heq.
    rewrite Heq in *; tauto.
    generalize (IHk i); intro H0; elim H0.
     intro H1; left; omega.
     intro H1; right; assumption.
Qed.

(* ========================== *)

Definition right_dart_cF (m:fmap)(p:point)(d:dart)(i:nat) :=
  right_dart m p (A m zero (Iter (cF m) i d)).

Lemma right_dart_cF_dec : forall (m:fmap)(p:point)(d:dart),
  prop_dec m p d right_dart_cF. 
Proof.
unfold prop_dec, right_dart_cF.
intros m p d i; apply right_dart_dec.
Qed.

Lemma exd_left_dart_exd_right_dart_i :
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> left_dart m p d ->
  exists i, i < (MF.Iter_upb m d) /\ right_dart m p (A m zero (Iter (cF m) i d)).
Proof.
intros m d p Hmap Hpoly Hexd Hleft.
generalize (exist_forall_i m p d right_dart_cF (MF.Iter_upb m d) (right_dart_cF_dec m p d)).
intro H; elim H; clear H; intro H; unfold right_dart_cF in *; [intuition|idtac].
destruct Hleft as [H1 [H2 H3]]; assert False; [idtac|tauto].
generalize (blue_dart_not_right_dart_until_i_visible_i m d p ((MF.Iter_upb m d)-1) Hmap Hpoly Hexd H1 H3).
intro H0; simpl in *.
assert (H01 : Iter (cF m) ((MF.Iter_upb m d)-1) d = cF_1 m d).
 rewrite <- MF.Iter_f_f_1; try assumption.
 rewrite MF.Iter_upb_period; try assumption.
 simpl in *; tauto.
 assert (0 < (MF.Iter_upb m d)); [idtac|omega].
  apply MF.upb_pos; tauto.
assert (H02 : cF_1 m d = A_1 m zero (A_1 m one d)).
 generalize (inv_poly_cF_1 m d Hmap Hpoly Hexd).
 elim blue_dart_dec; intro He1; [trivial|contradiction].
rewrite H01 in H0; rewrite H02 in H0; clear H01 H02.
apply invisible_A_1_invisible in H2; try assumption.
apply invisible_not_visible in H2.
cut (visible m (A_1 m zero (A_1 m one d)) p); [contradiction|idtac].
apply H0; intros j Hj; generalize (H j); clear H H0.
intro H; elim H; clear H; intro H; try assumption.
assert (0 < (MF.Iter_upb m d)); [idtac|omega].
 apply MF.upb_pos; tauto.
apply pred_exd_A_1; try assumption.
unfold blue_dart in H1; tauto.
apply blue_A_1_red; assumption.
Qed.

(* ========================== *)

Definition left_dart_cF (m:fmap)(p:point)(d:dart)(i:nat) :=
  left_dart m p (A_1 m zero (Iter (cF m) i d)).

Lemma left_dart_cF_dec : forall (m:fmap)(p:point)(d:dart),
  prop_dec m p d left_dart_cF. 
Proof.
unfold prop_dec, left_dart_cF.
intros m p d i; apply left_dart_dec.
Qed.

Lemma exd_right_dart_exd_left_dart_i :
  forall (m:fmap)(d:dart)(p:point),
  inv_hmap m -> inv_poly m ->
  exd m d -> right_dart m p d ->
  exists i, i < (MF.Iter_upb m d) /\ left_dart m p (A_1 m zero (Iter (cF m) i d)).
Proof.
intros m d p Hmap Hpoly Hexd Hright.
generalize (exist_forall_i m p d left_dart_cF (MF.Iter_upb m d) (left_dart_cF_dec m p d)).
intro H; elim H; clear H; intro H; unfold left_dart_cF in *; [intuition|idtac].
destruct Hright as [H1 [H2 H3]]; assert False; [idtac|tauto].
generalize (red_dart_not_left_dart_until_i_visible_i m d p ((MF.Iter_upb m d)-1) Hmap Hpoly Hexd H1 H2).
intro H0; simpl in *.
assert (H01 : Iter (cF m) ((MF.Iter_upb m d)-1) d = cF_1 m d).
 rewrite <- MF.Iter_f_f_1; try assumption.
 rewrite MF.Iter_upb_period; try assumption.
 simpl in *; tauto.
 assert (0 < (MF.Iter_upb m d)); [idtac|omega].
  apply MF.upb_pos; tauto.
assert (H02 : cF_1 m d = A m zero (A m one d)).
 generalize (inv_poly_cF_1 m d Hmap Hpoly Hexd).
 elim blue_dart_dec; intro He1.
  apply red_not_blue in H1; intuition.
  elim red_dart_dec; intro He2; [trivial|contradiction].
rewrite H01 in H0; rewrite H02 in H0; clear H01 H02.
apply invisible_A_invisible in H3; try assumption.
apply invisible_not_visible in H3.
cut (visible m (A m zero (A m one d)) p); [contradiction|idtac].
apply H0; intros j Hj; generalize (H j); clear H H0.
intro H; elim H; clear H; intro H; try assumption.
assert (0 < (MF.Iter_upb m d)); [idtac|omega].
 apply MF.upb_pos; tauto.
apply succ_exd_A; try assumption.
unfold red_dart in H1; tauto.
apply red_A_blue; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem exd_left_dart_exd_right_dart :
  forall (m:fmap)(px:point), inv_hmap m -> inv_poly m ->
  (exists da:dart, exd m da /\ left_dart m px da) ->
  (exists db:dart, exd m db /\ right_dart m px db).
Proof.
intros m px Hmap Hpoly.
intro H; elim H; clear H; intros d [H1 H2].
generalize (exd_left_dart_exd_right_dart_i m d px Hmap Hpoly H1 H2).
intro H; simpl in *.
elim H; clear H; intros i [Hi1 Hi2].
exists (A m zero (Iter (cF m) i d)); split.
 destruct Hi2 as [Hi2 [Hi3 Hi4]].
 apply succ_exd with one; try assumption.
 unfold red_dart in Hi2; tauto.
 assumption.
Qed.

Theorem exd_right_dart_exd_left_dart :
  forall (m:fmap)(px:point), inv_hmap m -> inv_poly m ->
  (exists da:dart, exd m da /\ right_dart m px da) ->
  (exists db:dart, exd m db /\ left_dart m px db).
Proof.
intros m px Hmap Hpoly.
intro H; elim H; clear H; intros d [H1 H2].
generalize (exd_right_dart_exd_left_dart_i m d px Hmap Hpoly H1 H2).
intro H; simpl in *.
elim H; clear H; intros i [Hi1 Hi2].
exists (A_1 m zero (Iter (cF m) i d)); split.
 destruct Hi2 as [Hi2 [Hi3 Hi4]].
 apply succ_exd with zero; try assumption.
 unfold blue_dart in Hi2; tauto.
 assumption.
Qed.

(* ========================== *)

Lemma not_exd_left_dart_not_exd_right_dart :
  forall (m:fmap)(px:point), inv_hmap m -> inv_poly m ->
  (forall (d:dart), exd m d -> ~ left_dart m px d) ->
  (forall (d:dart), exd m d -> ~ right_dart m px d).
Proof.
unfold not in *.
intros m px Hmap Hpoly Hleft d Hexd Hright.
assert (H : exists da:dart, exd m da /\ right_dart m px da).
 exists d; split; assumption.
generalize (exd_right_dart_exd_left_dart m px Hmap Hpoly H).
intro H0; elim H0; clear H0; intros da [Hda1 Hda2].
apply (Hleft da); assumption.
Qed.

Lemma not_exd_right_dart_not_exd_left_dart :
  forall (m:fmap)(px:point), inv_hmap m -> inv_poly m ->
  (forall (d:dart), exd m d -> ~ right_dart m px d) ->
  (forall (d:dart), exd m d -> ~ left_dart m px d).
Proof.
unfold not in *.
intros m px Hmap Hpoly Hright d Hexd Hleft.
assert (H : exists da:dart, exd m da /\ left_dart m px da).
 exists d; split; assumption.
generalize (exd_left_dart_exd_right_dart m px Hmap Hpoly H).
intro H0; elim H0; clear H0; intros da [Hda1 Hda2].
apply (Hright da); assumption.
Qed.
