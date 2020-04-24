(* ========================= *)
(* ===== CH04_submap.v ===== *)
(* ========================= *)

Require Export CH03_init.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Fixpoint submap (m:fmap)(mr:fmap) {struct m} : Prop :=
  match m with
    V => True
  | I m0 d t p => submap m0 mr /\ exd mr d /\ (ftag mr d) = t /\ (fpoint mr d) = p
  | L m0 k x y => submap m0 mr /\ (A mr k x) = y /\ (A_1 mr k y) = x
  end.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma submap_exd :
  forall (m:fmap)(mr:fmap)(d:dart),
  submap m mr -> exd m d -> exd mr d.
Proof.
induction m.
 simpl; tauto.
 intros mr x Hsub Hexd.
 simpl in *.
 elim Hexd; clear Hexd.
  intro Hexd; subst x.
  tauto.
  intro Hexd; apply IHm; [tauto | assumption].
 intros mr x Hsub Hexd.
 simpl in *.
 apply IHm; [tauto | assumption].
Qed.

Lemma submap_succ :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> succ m k d -> succ mr k d.
Proof.
induction m.
 unfold succ; simpl; tauto.
 intros mr k x Hsub Hsucc.
 unfold succ in *; simpl in *.
 apply IHm; [tauto | assumption].
 intros mr k x Hsub Hsucc.
 simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 unfold succ in *; simpl in *.
 generalize Hsucc; clear Hsucc.
 elim (eq_dim_dec d k).
  intros H; subst d.
  elim eq_dart_dec.
   intros H; subst x.
   rewrite Hsub2; trivial.
   intros H1 H2; apply IHm; assumption.
   intros H1 H2; apply IHm; assumption.
Qed.

Lemma submap_pred :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> pred m k d -> pred mr k d.
Proof.
induction m.
 unfold pred; simpl; tauto.
 intros mr k x Hsub Hpred.
 unfold pred in *; simpl in *.
 apply IHm; [tauto | assumption].
 intros mr k x Hsub Hpred.
 simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 unfold pred in *; simpl in *.
 generalize Hpred; clear Hpred.
 elim (eq_dim_dec d k).
  intros H; subst d.
  elim eq_dart_dec.
   intros H; subst x.
   rewrite Hsub3; trivial.
   intros H1 H2; apply IHm; assumption.
   intros H1 H2; apply IHm; assumption.
Qed.

Lemma submap_A :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> succ m k d -> A m k d = A mr k d.
Proof.
induction m.
 unfold succ in *; simpl in *; tauto.
 intros mr k x Hsub Hsucc.
 unfold succ in *; simpl in *.
 apply IHm; tauto.
 intros mr k x Hsub Hsucc.
 unfold succ in *; simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 generalize Hsucc; clear Hsucc.
 elim (eq_dim_dec d k).
  intro H; subst d.
  elim eq_dart_dec.
   intro H; subst x.
   rewrite Hsub2; trivial.
   intros H1 H2; apply IHm; assumption.
  intros H1 H2; apply IHm; assumption.
Qed.

Lemma submap_A_1 :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> pred m k d -> A_1 m k d = A_1 mr k d.
Proof.
induction m.
 unfold pred in *; simpl in *; tauto.
 intros mr k x Hsub Hpred.
 unfold pred in *; simpl in *.
 apply IHm; tauto.
 intros mr k x Hsub Hpred.
 unfold pred in *; simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 generalize Hpred; clear Hpred.
 elim (eq_dim_dec d k).
  intro H; subst d.
  elim eq_dart_dec.
   intro H; subst x.
   rewrite Hsub3; trivial.
   intros H1 H2; apply IHm; assumption.
  intros H1 H2; apply IHm; assumption.
Qed.

Lemma submap_ftag :
  forall (m:fmap)(mr:fmap)(d:dart),
  submap m mr -> exd m d -> ftag m d = ftag mr d.
Proof.
induction m.
 simpl; tauto.
 intros mr x Hsub Hexd.
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 elim (eq_dart_dec d x); intro Heq.
  subst d; rewrite Hsub2; trivial.
  elim Hexd; clear Hexd; intro Hexd.
   subst x; tauto.
   apply IHm; assumption.
 intros mr x Hsub Hexd.
 simpl in *.
 apply IHm; tauto.
Qed.

Lemma submap_fpoint :
  forall (m:fmap)(mr:fmap)(d:dart),
  submap m mr -> exd m d -> fpoint m d = fpoint mr d.
Proof.
induction m.
 simpl; tauto.
 intros mr x Hsub Hexd.
 simpl in *.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 elim (eq_dart_dec d x); intro Heq.
  subst d; rewrite Hsub3; trivial.
  elim Hexd; clear Hexd; intro Hexd.
   subst x; tauto.
   apply IHm; assumption.
 intros mr x Hsub Hexd.
 simpl in *.
 apply IHm; tauto.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Lemma submap_not_exd :
  forall (m:fmap)(mr:fmap)(d:dart),
  submap m mr -> ~ exd mr d -> ~ exd m d.
Proof.
induction m.
 simpl; tauto.
 intros mr x Hsub Hexd.
 simpl in *.
 unfold not; intro Hfs.
 elim Hfs; clear Hfs.
 intro H; subst x; intuition.
 intro H; generalize (IHm mr x);
 clear IHm; intuition.
 intros mr x Hsub Hexd.
 simpl in *.
 apply (IHm mr x); [tauto | assumption].
Qed.

Lemma submap_not_succ :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> ~ succ mr k d -> ~ succ m k d.
Proof.
induction m.
 unfold succ; simpl; tauto.
 intros mr k x Hsub Hsucc.
 unfold succ in *; simpl in *.
 apply (IHm mr k x); [tauto | assumption].
 intros mr k x Hsub Hsucc.
 simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 unfold succ in *; simpl in *.
 generalize Hsucc; clear Hsucc.
 elim (eq_dim_dec d k).
  intros H; subst d.
  elim eq_dart_dec.
   intros H; subst x.
   rewrite Hsub2; trivial.
   intros H1 H2; apply (IHm mr k x); assumption.
   intros H1 H2; apply (IHm mr k x); assumption.
Qed.

Lemma submap_not_pred :
  forall (m:fmap)(mr:fmap)(k:dim)(d:dart),
  submap m mr -> ~ pred mr k d -> ~ pred m k d.
Proof.
induction m.
 unfold pred; simpl; tauto.
 intros mr k x Hsub Hpred.
 unfold pred in *; simpl in *.
 apply (IHm mr k x); [tauto | assumption].
 intros mr k x Hsub Hpred.
 simpl in *.
 destruct Hsub as [Hsub1 [Hsub2 Hsub3]].
 unfold pred in *; simpl in *.
 generalize Hpred; clear Hpred.
 elim (eq_dim_dec d k).
  intros H; subst d.
  elim eq_dart_dec.
   intros H; subst x.
   rewrite Hsub3; trivial.
   intros H1 H2; apply (IHm mr k x); assumption.
   intros H1 H2; apply (IHm mr k x); assumption.
Qed.

(* ========================= *)
(* =======  #######  ======= *)
(* ========================= *)

Definition submap_2 (m:fmap)(mr:fmap) : Prop :=
  (forall (d:dart), exd m d -> exd mr d /\ (ftag m d) = (ftag mr d) /\ (fpoint m d) = (fpoint mr d)) /\
  (forall (k:dim)(d:dart), succ m k d -> (A m k d) = (A mr k d)) /\
  (forall (k:dim)(d:dart), pred m k d -> (A_1 m k d) = (A_1 mr k d)).

(* ========================= *)

Lemma submap_2_refl :
  forall (m:fmap), submap_2 m m.
Proof.
intro m; unfold submap_2; tauto.
Qed.

(* ========================= *)

Lemma submap_submap_2 :
  forall (m:fmap)(mr:fmap),
  submap m mr -> submap_2 m mr.
Proof.
intros m mr H.
unfold submap_2; repeat split.
 apply submap_exd with m; assumption.
 apply submap_ftag; assumption.
 apply submap_fpoint; assumption.
 intros k d; apply submap_A; assumption.
 intros k d; apply submap_A_1; assumption.
Qed.

Lemma submap_2_submap :
  forall (m:fmap)(mr:fmap),
  inv_hmap m -> submap_2 m mr -> submap m mr.
Proof.
intros m mr Hmap H.
unfold submap_2 in H.
destruct H as [H1 [H2 H3]].
induction m.
 (* Cas 1 : m = V *)
 simpl in *; tauto.
 (* Cas 2 : m = I *)
 simpl in *; unfold prec_I in *; repeat split.
 apply IHm; try tauto.
  intros da Hda; split; [idtac|split].
  assert (H : da <> d).
   apply exd_not_exd_neq with m; tauto.
  generalize (H1 da); intuition.
  assert (H : da <> d).
   apply exd_not_exd_neq with m; tauto.
  generalize (H1 da); elimeqdartdec; intuition.
  assert (H : da <> d).
   apply exd_not_exd_neq with m; tauto.
  generalize (H1 da); elimeqdartdec; intuition.
 generalize (H1 d); intuition.
 generalize (H1 d); elimeqdartdec; intuition.
 generalize (H1 d); elimeqdartdec; intuition.
 (* Cas 3 : m = L *)
 simpl in *; unfold prec_L in *; repeat split.
 apply IHm; try tauto.
  intros k da Hda; generalize (H2 k da); unfold succ; simpl.
   elim (eq_dim_dec d k); intro Hdim; try subst d.
    elim (eq_dart_dec d0 da); intro Heq; try subst d0.
     unfold succ in *; simpl in *; intuition.
     unfold succ in *; simpl in *; intuition.
    unfold succ in *; simpl in *; intuition. 
  intros k da Hda; generalize (H3 k da); unfold pred; simpl.
   elim (eq_dim_dec d k); intro Hdim; try subst d.
    elim (eq_dart_dec d1 da); intro Heq; try subst d1.
     unfold pred in *; simpl in *; intuition.
     unfold pred in *; simpl in *; intuition.
    unfold pred in *; simpl in *; intuition.
 generalize (H2 d d0); unfold succ; simpl.
 elim (eq_dim_dec d d); intro Hdim; [clear Hdim | tauto].
 elimeqdartdec; intro H; rewrite <- H; trivial.
 apply exd_not_nil with m; intuition.
 generalize (H3 d d1); unfold pred; simpl.
 elim (eq_dim_dec d d); intro Hdim; [clear Hdim | tauto].
 elimeqdartdec; intro H; rewrite <- H; trivial.
 apply exd_not_nil with m; intuition.
Qed.
