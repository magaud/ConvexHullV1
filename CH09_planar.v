(* ========================= *)
(* ===== CH09_planar.v ===== *)
(* ========================= *)

Require Export CH08_well_emb_convex.

(* ========================== *)

Open Scope Z_scope.
Require Import ZArith.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma my_planar_genus : forall (m:fmap),
 planar m <-> (genus m = 0)%Z.
Proof.
intro m; split; unfold planar; trivial.
Qed.

Lemma my_genus_ec : forall (m:fmap),
 (genus m = 0)%Z <-> (ec m / 2 = nc m)%Z.
Proof.
intro m; split; unfold genus; lia.
Qed.

Lemma my_planar_ec : forall (m:fmap),
 planar m <-> (ec m / 2 = nc m)%Z.
Proof.
intro m; split; unfold planar, genus; lia.
Qed.

(* ========================== *)

Lemma my_plf_planar : forall (m:fmap),
  inv_hmap m -> plf m -> planar m.
Proof.
apply plf_planar.
Qed.

Lemma my_planar_plf : forall (m:fmap),
  inv_hmap m -> planar m -> plf m.
Proof.
intros m Hmap H.
apply planar_plf; try assumption.
Qed.

Lemma my_plf_genus : forall (m:fmap),
  inv_hmap m -> plf m -> (genus m = 0)%Z.
Proof.
apply plf_planar.
Qed.

Lemma my_genus_plf : forall (m:fmap),
  inv_hmap m -> (genus m = 0)%Z -> plf m.
Proof.
intros m Hmap H.
apply planar_plf; try assumption.
Qed.

Lemma my_plf_ec : forall (m:fmap),
  inv_hmap m -> plf m -> (ec m / 2 = nc m)%Z.
Proof.
intros m Hmap H.
generalize (plf_planar m Hmap H).
unfold planar, genus; lia.
Qed.

Lemma my_ec_plf : forall (m:fmap),
  inv_hmap m -> (ec m / 2 = nc m)%Z -> plf m.
Proof.
intros m Hmap H.
apply planar_plf; try assumption.
unfold genus; lia.
Qed.

(* ========================== *)

Lemma my_planar_V : planar V.
Proof.
apply planar_V.
Qed.

Lemma my_planar_planar_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> planar m -> planar (I m d t p).
Proof.
intros m d t p Hmap H.
apply planar_I; simpl in *; intuition.
Qed.

Lemma my_planar_I_planar :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap (I m d t p) -> planar (I m d t p) -> planar m.
Proof.
intros m d t p Hmap H.
unfold planar in *.
rewrite <- H; apply sym_eq.
apply eq_genus_I; assumption.
Qed.

Lemma my_planar_planar_L_0 :
  forall (m:fmap)(x:dart)(y:dart),
  inv_hmap (L m zero x y) -> planar m ->
  (~ eqc m x y) \/ (expf m (cA_1 m one x) y) ->
  planar (L m zero x y).
Proof.
intros m x y Hmap H H0.
simpl in Hmap.
elim H0; clear H0; intro H0.
apply not_eqc_planar; try intuition.
apply expf_planar_0; try intuition.
Qed.

Lemma my_planar_planar_L_1 :
  forall (m:fmap)(x:dart)(y:dart),
  inv_hmap (L m one x y) -> planar m ->
  (~ eqc m x y) \/ (expf m x (cA m zero y)) ->
  planar (L m one x y).
Proof.
intros m x y Hmap H H0.
simpl in Hmap.
elim H0; clear H0; intro H0.
apply not_eqc_planar; try intuition.
apply expf_planar_1; try intuition.
Qed.

Lemma my_planar_L_planar :
  forall (m:fmap)(k:dim)(x:dart)(y:dart),
  inv_hmap (L m k x y) -> planar (L m k x y) ->
  planar m.
Proof.
intros m k x y Hmap H.
simpl in Hmap.
apply inversion_planarity with k x y; intuition.
Qed.

(* ======================= *)

Lemma my_expf_eqc :
  forall (m:fmap)(d0:dart)(d1:dart),
  expf m d0 d1 -> eqc m d0 d1.
Proof.
intros m d0 d1.
unfold expf.
intros [H1 H2].
apply expf_eqc; assumption.
Qed.

Lemma my_not_eqc_not_expf :
  forall (m:fmap)(d0:dart)(d1:dart),
  ~ eqc m d0 d1 -> ~ expf m d0 d1.
Proof.
intros m d0 d1 H1 H2.
apply H1; apply my_expf_eqc; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Definition half_blue_succ (m:fmap)(d:dart) : Prop :=
  succ m zero d /\ ~ succ m one d /\
  ~ pred m zero d /\ ~ pred m one d.

Definition half_blue_pred (m:fmap)(d:dart) : Prop :=
  ~ succ m zero d /\ ~ succ m one d /\
  ~ pred m zero d /\ pred m one d.

Definition half_red_succ (m:fmap)(d:dart) : Prop :=
  ~ succ m zero d /\ succ m one d /\
  ~ pred m zero d /\ ~ pred m one d.

Definition half_red_pred (m:fmap)(d:dart) : Prop :=
  ~ succ m zero d /\ ~ succ m one d /\
  pred m zero d /\ ~ pred m one d.

Definition inv_half (m:fmap) : Prop :=
  forall (d:dart), exd m d ->
  black_dart m d \/ blue_dart m d \/ red_dart m d \/
  half_blue_succ m d \/ half_blue_pred m d \/
  half_red_succ m d \/ half_red_pred m d.

(* ======================= *)

Lemma inv_half_succ_zero :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_half m -> succ m zero d ->
  blue_dart m d \/ half_blue_succ m d.
Proof.
intros m d Hmap H Hsucc.
assert (H0 : exd m d).
 apply (succ_exd m zero d); tauto.
generalize (H d H0); clear H; intro H.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 left; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 right; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
Qed.

Lemma inv_half_succ_one :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_half m -> succ m one d ->
  red_dart m d \/ half_red_succ m d.
Proof.
intros m d Hmap H Hsucc.
assert (H0 : exd m d).
 apply (succ_exd m one d); tauto.
generalize (H d H0); clear H; intro H.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 left; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 right; assumption.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
Qed.

Lemma inv_half_pred_zero :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_half m -> pred m zero d ->
  red_dart m d \/ half_red_pred m d.
Proof.
intros m d Hmap H Hpred.
assert (H0 : exd m d).
 apply (pred_exd m zero d); tauto.
generalize (H d H0); clear H; intro H.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 left; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
 right; assumption.
Qed.

Lemma inv_half_pred_one :
  forall (m:fmap)(d:dart),
  inv_hmap m -> inv_half m -> pred m one d ->
  blue_dart m d \/ half_blue_pred m d.
Proof.
intros m d Hmap H Hpred.
assert (H0 : exd m d).
 apply (pred_exd m one d); tauto.
generalize (H d H0); clear H; intro H.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 left; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
elim H; clear H; intro H.
 right; assumption.
elim H; clear H; intro H.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
 destruct H as [h1 [h2 [h3 h4]]]; contradiction.
Qed.

(* ======================= *)

Lemma inv_half_L :
  forall (m:fmap)(k:dim)(d0:dart)(d1:dart),
  inv_hmap m -> exd m d0 -> exd m d1 ->
  ~ succ m k d0 -> ~ pred m k d1 ->
  inv_half (L m k d0 d1) -> inv_half m.
Proof.
intros m k x y Hmap Hx Hy Hs Hp.
induction k; simpl in *.
(* K1 : k = zero *)
unfold inv_half; intros H da Hda.
generalize (H da Hda); clear H.
intro H; elim H; clear H.
 (* black_dart m da *)
 unfold black_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 left; unfold black_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* blue_dart m da *)
 unfold blue_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec y da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 elim (eq_dart_dec x da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  right; right; right; right; left; unfold half_blue_pred, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; left; unfold blue_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* red_dart m da *)
 unfold red_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  right; right; right; right; right; left; unfold half_red_succ, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; left; unfold red_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_blue_succ m da *)
 unfold half_blue_succ at 1, succ, pred; simpl.
 elim (eq_dart_dec y da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 elim (eq_dart_dec x da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  left; unfold black_dart, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; left; unfold half_blue_succ, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_blue_pred m da *)
 unfold half_blue_pred at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; left; unfold half_blue_pred, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_red_succ m da *)
 unfold half_red_succ at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; right; left; unfold half_red_succ, succ, pred; intuition.
 (* half_red_pred m da *)
 unfold half_red_pred at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  left; unfold black_dart, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; right; right; unfold half_red_pred, succ, pred; intuition.
(* K2 : k = one *)
unfold inv_half; intros H da Hda.
generalize (H da Hda); clear H.
intro H; elim H; clear H.
 (* black_dart m da *)
 unfold black_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 left; unfold black_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* blue_dart m da *)
 unfold blue_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  right; right; right; left; unfold half_blue_succ, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; left; unfold blue_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* red_dart m da *)
 unfold red_dart at 1, succ, pred; simpl.
 elim (eq_dart_dec y da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 elim (eq_dart_dec x da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  right; right; right; right; right; right; unfold half_red_pred, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; left; unfold red_dart, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_blue_succ m da *)
 unfold half_blue_succ at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; left; unfold half_blue_succ, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_blue_pred m da *)
 unfold half_blue_pred at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  left; unfold black_dart, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; left; unfold half_blue_pred, succ, pred; intuition.
intro H; elim H; clear H.
 (* half_red_succ m da *)
 unfold half_red_succ at 1, succ, pred; simpl.
 elim (eq_dart_dec y da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 elim (eq_dart_dec x da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  left; unfold black_dart, succ, pred; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; right; left; unfold half_red_succ, succ, pred; intuition.
 (* half_red_pred m da *)
 unfold half_red_pred at 1, succ, pred; simpl.
 elim (eq_dart_dec x da); intro Heq1.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m y in Hy; intuition.
 elim (eq_dart_dec y da); intro Heq2.
  intros [h1 [h2 [h3 h4]]]; subst da.
  apply exd_not_nil with m x in Hx; intuition.
 intros [h1 [h2 [h3 h4]]].
 right; right; right; right; right; right; unfold half_red_pred, succ, pred; intuition.
Qed.

Lemma inv_half_I :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_hmap m -> inv_half m ->
  ~ exd m d -> inv_half (I m d t p).
Proof.
intros m d t p Hmap Half Hexd.
unfold inv_half; intros da Hda.
elim Hda; clear Hda; intro Hda.
subst da; left.
generalize (not_exd_black m d Hmap Hexd).
unfold black_dart, succ, pred; simpl; trivial.
generalize (Half da Hda).
unfold black_dart, blue_dart, red_dart;
unfold half_blue_succ, half_blue_pred;
unfold half_red_succ, half_red_pred;
unfold succ, pred; simpl; trivial.
Qed.

Lemma inv_half_L0 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m ->
  exd m d0 -> exd m d1 -> d0 <> d1 ->
  black_dart m d0 \/ half_blue_pred m d0 ->
  black_dart m d1 \/ half_red_succ m d1 ->
  inv_half (L m zero d0 d1).
Proof.
intros m d0 d1 Hmap Half Hexd0 Hexd1 Hneq Hd0 Hd1.
unfold inv_half; intros da Hda; simpl in Hda.
unfold black_dart, blue_dart, red_dart, half_blue_succ, half_blue_pred;
unfold half_red_succ, half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 da); intro Heq0; [subst d0 | idtac].
elim (eq_dart_dec d1 da); intro Heq1; [subst d1 | idtac].
cut False; [tauto | apply Hneq; trivial].
elim Hd0; clear Hd0; intro Hd0; destruct Hd0 as [h1 [h2 [h3 h4]]].
right; right; right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
elim (eq_dart_dec d1 da); intro Heq1; [subst d1 | idtac].
elim Hd1; clear Hd1; intro Hd1; destruct Hd1 as [h1 [h2 [h3 h4]]].
right; right; right; right; right; right; repeat split; try assumption.
apply exd_not_nil with m; assumption.
right; right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
generalize (Half da Hda).
unfold black_dart, blue_dart, red_dart, half_blue_succ, half_blue_pred;
unfold half_red_succ, half_red_pred, succ, pred; simpl; trivial.
Qed.

Lemma inv_half_L1 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m ->
  exd m d0 -> exd m d1 -> d0 <> d1 ->
  black_dart m d0 \/ half_red_pred m d0 ->
  black_dart m d1 \/ half_blue_succ m d1 ->
  inv_half (L m one d0 d1).
Proof.
intros m d0 d1 Hmap Half Hexd0 Hexd1 Hneq Hd0 Hd1.
unfold inv_half; intros da Hda; simpl in Hda.
unfold black_dart, blue_dart, red_dart, half_blue_succ, half_blue_pred;
unfold half_red_succ, half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 da); intro Heq0; [subst d0 | idtac].
elim (eq_dart_dec d1 da); intro Heq1; [subst d1 | idtac].
cut False; [tauto | apply Hneq; trivial].
elim Hd0; clear Hd0; intro Hd0; destruct Hd0 as [h1 [h2 [h3 h4]]].
right; right; right; right; right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
right; right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
elim (eq_dart_dec d1 da); intro Heq1; [subst d1 | idtac].
elim Hd1; clear Hd1; intro Hd1; destruct Hd1 as [h1 [h2 [h3 h4]]].
right; right; right; right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
right; left; repeat split; try assumption.
apply exd_not_nil with m; assumption.
generalize (Half da Hda).
unfold black_dart, blue_dart, red_dart, half_blue_succ, half_blue_pred;
unfold half_red_succ, half_red_pred, succ, pred; simpl; trivial.
Qed.

Lemma inv_half_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  submap m mr -> inv_hmap m ->
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  x <> nil -> max <> nil -> x <> max -> ~ exd mr x -> ~ exd mr max ->
  inv_half (CHID m mr x tx px max).
Proof.
intros m mr x tx px max Hsub Hmap Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hneq1 Hneq2 Hneq3 Hexd1 Hexd2.
induction m.
 (* Cas 1 : m = V *)
 simpl in *; unfold inv_half.
 intros da Hexd; simpl in *.
 elim Hexd; clear Hexd.
  intro Hexd; subst da; left.
  unfold black_dart, succ, pred; simpl; intuition.
  intro Hexd; intuition.
 (* Cas 2 : m = I *)
 simpl in Hsub, Hmap; unfold prec_I in Hmap.
 destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 generalize (IHm Hsub Hmap); clear IHm; intro IHm.
 assert (Hneq4 : d <> x). apply exd_not_exd_neq with mr; assumption.
 assert (Hneq5 : d <> max). apply exd_not_exd_neq with mr; assumption.
 simpl.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
apply inv_half_L0; try assumption.
simpl; unfold prec_I, prec_L; repeat split; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
simpl; apply and_not_not_or; split; try assumption.
apply max_CHID_3; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
simpl; left; trivial.
simpl; right; right; apply x_CHID_1.
unfold succ; simpl; intro H0.
apply max_CHID_4 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
unfold pred; simpl; intro H0.
apply x_CHID_5 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
simpl; elimeqdartdec; apply neq_sym; assumption.
apply inv_half_L1; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
simpl; apply and_not_not_or; split; try assumption.
apply max_CHID_3; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
apply inv_half_I; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
simpl; apply and_not_not_or; split; try assumption.
apply max_CHID_3; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
simpl; left; trivial.
simpl; right; right; apply x_CHID_1.
apply neq_sym; assumption.
unfold black_dart, succ, pred; simpl; elimeqdartdec.
left; repeat split; try assumption.
intro H0; apply max_CHID_1 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply max_CHID_4 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
intro H0; apply max_CHID_5 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
intro H0; apply max_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
elim (succ_dec (CHID m mr x tx px max) zero x).
unfold half_blue_succ, succ, pred; simpl; elimeqdartdec.
right; repeat split; try assumption.
intro H0; apply x_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_3 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_5 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
unfold black_dart, succ, pred; simpl; elimeqdartdec.
left; repeat split; try assumption.
intro H0; apply x_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_3 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_5 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
simpl; right; left; trivial.
simpl; left; trivial.
assert (t1 : inv_hmap (CHID m mr x tx px max)).
apply inv_hmap_CHID; assumption.
assert (t2 : ~ exd (CHID m mr x tx px max) d).
apply not_exd_CHID; assumption.
generalize (not_exd_black (CHID m mr x tx px max) d t1 t2).
unfold black_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; left; repeat split; assumption.
unfold half_red_succ, succ, pred; simpl; elimeqdartdec.
right; repeat split; try assumption.
intro H0; apply max_CHID_1 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply max_CHID_5 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_left_dart_less with m d; assumption.
intro H0; apply max_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
apply inv_half_L0; try assumption.
simpl; unfold prec_I, prec_L; repeat split; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
simpl; right; apply x_CHID_1.
simpl; left; trivial.
apply neq_sym; assumption.
elim (pred_dec (CHID m mr x tx px max) one x).
unfold half_blue_pred, succ, pred; simpl; elimeqdartdec.
right; repeat split; try assumption.
intro H0; apply x_CHID_4 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_right_dart_less with m d; assumption.
intro H0; apply x_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_3 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
unfold black_dart, succ, pred; simpl; elimeqdartdec.
left; repeat split; try assumption.
intro H0; apply x_CHID_4 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intros da Hda; apply map_right_dart_less with m d; assumption.
intro H0; apply x_CHID_2 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
intro H0; apply x_CHID_3 with m mr x tx px max; try assumption.
apply submap_not_exd with mr; assumption.
assert (t1 : inv_hmap (CHID m mr x tx px max)).
apply inv_hmap_CHID; assumption.
assert (t2 : ~ exd (CHID m mr x tx px max) d).
apply not_exd_CHID; assumption.
generalize (not_exd_black (CHID m mr x tx px max) d t1 t2).
unfold black_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; left; repeat split; assumption.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
apply inv_half_I; try assumption.
apply inv_hmap_CHID; assumption.
apply not_exd_CHID; try assumption.
(* ======= *)
 (* Cas 3 : m = L *)
 simpl in Hsub, Hmap; unfold prec_L in Hmap.
 destruct Hsub as [Hsub [Hsub1 Hsub2]].
 destruct Hmap as [Hmap [H1 [H2 [H3 [H4 H5]]]]].
 generalize (IHm Hsub Hmap); clear IHm; intro IHm.
 induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
apply inv_half_L0; try assumption.
apply inv_hmap_CHID; assumption.
apply blue_dart_CHID_1; try assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
apply red_dart_CHID_3; try assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
unfold invisible; elim (blue_dart_dec mr d1); intro H0.
cut False; [tauto|idtac].
apply blue_not_red with mr d1; try assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
left; rewrite Hsub2; assumption.
elim (eq_dart_dec d0 d1); try trivial.
intro H0; rewrite H0 in H_ccw.
apply ccw_neq_point in H_ccw; tauto.
elim (pred_dec (CHID m mr x tx px max) one d0).
unfold half_blue_pred, succ, pred.
right; repeat split; try assumption.
intro H0; apply blue_dart_CHID_5 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
rewrite Hsub1; assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply blue_dart_CHID_5 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
rewrite Hsub1; assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_zero_blue_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
elim (succ_dec (CHID m mr x tx px max) one d1).
unfold half_red_succ, succ, pred.
right; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_8 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
rewrite Hsub2; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_8 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
rewrite Hsub2; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_zero_red_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
apply inv_half_L1; try assumption.
apply inv_hmap_CHID; assumption.
apply red_dart_CHID_3; try assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
apply blue_dart_CHID_1; try assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
elim (eq_dart_dec d0 d1); try trivial.
intro H0; move H0 after Hsub; subst d1.
rewrite (fixpoint_cA m one d0 Hmap H1 H3 H4) in H5; assumption.
elim (pred_dec (CHID m mr x tx px max) zero d0).
unfold half_red_pred, succ, pred.
right; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_5 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_5 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
elim (succ_dec (CHID m mr x tx px max) zero d1).
unfold half_blue_succ, succ, pred.
right; repeat split; try assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_20 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_20 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
apply inv_half_L1; try assumption.
apply inv_hmap_CHID; assumption.
apply red_dart_CHID_11; try assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
apply not_invisible_visible; assumption.
rewrite Hsub1; assumption.
apply blue_dart_CHID_1; try assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
elim (eq_dart_dec d0 d1); try trivial.
intro H0; move H0 after Hsub; subst d1.
rewrite (fixpoint_cA m one d0 Hmap H1 H3 H4) in H5; assumption.
elim (pred_dec (CHID m mr x tx px max) zero d0).
unfold half_red_pred, succ, pred.
right; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_13 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
apply not_invisible_visible; assumption.
rewrite Hsub1; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply red_dart_CHID_1 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
intro H0; apply red_dart_CHID_13 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
apply not_invisible_visible; assumption.
rewrite Hsub1; assumption.
intro H0; apply red_dart_CHID_2 with m mr x tx px max d0; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply succ_one_red_dart; try assumption.
unfold succ; rewrite Hsub1.
apply exd_not_nil with m; assumption.
elim (succ_dec (CHID m mr x tx px max) zero d1).
unfold half_blue_succ, succ, pred.
right; repeat split; try assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_20 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
unfold black_dart, succ, pred.
left; repeat split; try assumption.
intro H0; apply blue_dart_CHID_2 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_3 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
intro H0; apply blue_dart_CHID_20 with m mr x tx px max d1; try assumption.
apply exd_not_exd_neq with m; try assumption.
apply submap_not_exd with mr; assumption.
apply pred_one_blue_dart; try assumption.
unfold pred; rewrite Hsub2.
apply exd_not_nil with m; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma eqc_succ_or_pred :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> eqc m d0 d1 -> d0 <> d1 ->
  (succ m zero d0 \/ succ m one d0 \/ pred m zero d0 \/ pred m one d0).
Proof.
induction m.
 (* K1 : m = V *)
 simpl in *; tauto.
 (* K2 : m = I *)
 intros x y Hmap Heqc Hneq.
 simpl in Hmap; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 simpl in Heqc.
 elim Heqc; clear Heqc; intro Heqc.
  destruct Heqc as [h1 h2].
  subst x; subst y; tauto.
  unfold succ, pred; simpl.
  apply (IHm x y); assumption.
 (* K3 : m = L *)
 intros x y Hmap Heqc Hneq.
 simpl in Hmap; unfold prec_L in Hmap.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
 induction d; simpl in *.
 (* K31 : d = zero *)
 elim Heqc; clear Heqc; intro Heqc.
 generalize (IHm x y Hmap Heqc Hneq); clear IHm; intro IHm.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq.
  subst d0; contradiction.
  left; assumption.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 right; left; assumption.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d1 x); intro Heq.
  subst d1; contradiction.
  right; right; left; assumption.
 unfold succ, pred in *; simpl in *.
 right; right; right; assumption.
 (**)
 elim Heqc; clear Heqc; intro Heqc.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq1.
  subst d0; left.
  apply exd_not_nil with m; assumption.
 elim (eq_dart_dec d1 x); intro Heq2.
  subst d1; right; right; left.
  apply exd_not_nil with m; assumption.
 apply (IHm x d0); try intuition.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq1.
  subst d0; left.
  apply exd_not_nil with m; assumption.
 elim (eq_dart_dec d1 x); intro Heq2.
  subst d1; right; right; left.
  apply exd_not_nil with m; assumption.
 apply (IHm x d1); try intuition.
 (* K32 : d = one *)
 elim Heqc; clear Heqc; intro Heqc.
 generalize (IHm x y Hmap Heqc Hneq); clear IHm; intro IHm.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 left; assumption.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq.
  subst d0; contradiction.
  right; left; assumption.
 elim IHm; clear IHm; intro IHm.
 unfold succ, pred in *; simpl in *.
 right; right; left; assumption.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d1 x); intro Heq.
  subst d1; contradiction.
  right; right; right; assumption.
 (**)
 elim Heqc; clear Heqc; intro Heqc.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq1.
  subst d0; right; left.
  apply exd_not_nil with m; assumption.
 elim (eq_dart_dec d1 x); intro Heq2.
  subst d1; right; right; right.
  apply exd_not_nil with m; assumption.
 apply (IHm x d0); try intuition.
 unfold succ, pred in *; simpl in *.
 elim (eq_dart_dec d0 x); intro Heq1.
  subst d0; right; left.
  apply exd_not_nil with m; assumption.
 elim (eq_dart_dec d1 x); intro Heq2.
  subst d1; right; right; right.
  apply exd_not_nil with m; assumption.
 apply (IHm x d1); try intuition.
Qed.

Lemma black_not_eqc :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> black_dart m d0 -> d0 <> d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Hblack Hneq Heqc.
generalize (eqc_succ_or_pred m d0 d1 Hmap Heqc Hneq).
destruct Hblack as [h1 [h2 [h3 h4]]].
intro H0; elim H0; clear H0; [contradiction|idtac].
intro H0; elim H0; clear H0; [contradiction|idtac].
intro H0; elim H0; clear H0; contradiction.
Qed.

Lemma black_eqc_eq :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> black_dart m d0 ->
  eqc m d0 d1 -> d0 = d1.
Proof.
intros m d0 d1 Hmap Hblack Heqc.
elim (eq_dart_dec d0 d1); try trivial.
intro H; cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma half_eqc_hbs_hrs :
  forall (m:fmap)(x:dart)(y:dart),
  inv_hmap m -> inv_half m -> eqc m x y -> x <> y ->
  half_blue_succ m x \/ half_red_succ m x -> 
  ~ half_blue_succ m y /\ ~ half_red_succ m y.
Proof.
induction m.
 (* K1 : V *)
 intros x y Hmap Half H0 Hneq.
 simpl in *; intuition.
 (* K2 : I *)
 intros x y Hmap Half H0 Hneq.
 simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 elim H0; clear H0; intro H0.
  destruct H0 as [h1 h2].
  subst x; subst y; tauto.
 assert (H1 : inv_half m); [idtac | clear Half].
  unfold inv_half; intros da Hda.
  assert (H1 : d = da \/ exd m da); [right; assumption | idtac].
  generalize (Half da H1); clear Half.
  unfold black_dart, blue_dart, red_dart;
  unfold half_blue_succ, half_blue_pred, half_red_succ, half_red_pred;
  unfold succ, pred; simpl; trivial.
 generalize (IHm x y Hmap H1 H0 Hneq); clear IHm; intro IHm.
 unfold half_blue_succ, half_blue_pred, half_red_succ, half_red_pred in *;
 unfold succ, pred in *; simpl in *; try assumption.
 (* K3 : L *)
assert (IHm1 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_blue_succ m x -> ~ half_blue_succ m y).
intros da db H1 H2 H3 H4 H5; apply or_introl with (half_blue_succ m da) (half_red_succ m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm2 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_blue_succ m x -> ~ half_red_succ m y).
intros da db H1 H2 H3 H4 H5; apply or_introl with (half_blue_succ m da) (half_red_succ m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm3 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_red_succ m x -> ~ half_blue_succ m y).
intros da db H1 H2 H3 H4 H5; apply or_intror with (half_blue_succ m da) (half_red_succ m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm4 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_red_succ m x -> ~ half_red_succ m y).
intros da db H1 H2 H3 H4 H5; apply or_intror with (half_blue_succ m da) (half_red_succ m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
 intros x y Hmap Half H0 Hneq.
 generalize Hmap; intro HmapL.
 simpl in Hmap; unfold prec_L in Hmap.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (eq_dart_dec d0 d1); intro Heq.
subst d1; generalize (fixpoint_cA m d d0 Hmap Hmap1 Hmap3 Hmap4); contradiction.
 induction d; simpl in H0; clear IHm.
 (* K31 : d = zero *)
assert (Hd0 : black_dart m d0 \/ half_blue_pred m d0).
 assert (t0 : succ (L m zero d0 d1) zero d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_zero (L m zero d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_pred, succ, pred; repeat split; assumption.
 unfold half_blue_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_red_succ m d1).
 assert (t0 : pred (L m zero d0 d1) zero d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_zero (L m zero d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_succ, succ, pred; repeat split; assumption.
 unfold half_red_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5 HmapL.
unfold half_blue_succ, half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Hx1.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec;
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d1 y); intro Hy1.
intro h0; subst y; split; do 2 (apply or_not_not_and; right); apply or_not_not_and; left;
apply neq_not_not_neq; apply exd_not_nil with m; assumption.
elim (eq_dart_dec d0 x); intro Hx0.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm3.
apply IHm3 with d1; assumption.
unfold half_red_succ, succ, pred in IHm4.
apply IHm4 with d1; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
unfold half_blue_pred, succ, pred in Hd0; intuition.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d0 y); intro Hy0.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst y; elimeqdartdec.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm3 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
split; do 3 (apply or_not_not_and; right); apply neq_not_not_neq;
unfold half_blue_pred, succ, pred in Hd0; intuition.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm4 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
split; do 3 (apply or_not_not_and; right); apply neq_not_not_neq;
unfold half_blue_pred, succ, pred in Hd0; intuition.
intro Hsucc; elim Hsucc; clear Hsucc; intros [h1 [h2 [h3 h4]]].
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_succ, succ, pred in IHm1.
apply IHm1 with x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
unfold half_red_succ, succ, pred in IHm2.
apply IHm2 with x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm3.
apply IHm3 with d1; assumption.
unfold half_red_succ, succ, pred in IHm4.
apply IHm4 with d1; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm3 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_succ, succ, pred in IHm3.
apply IHm3 with x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
unfold half_red_succ, succ, pred in IHm4.
apply IHm4 with x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm3.
apply IHm3 with d1; assumption.
unfold half_red_succ, succ, pred in IHm4.
apply IHm4 with d1; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm4 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
 (* K32 : d = one *)
assert (Hd0 : black_dart m d0 \/ half_red_pred m d0).
 assert (t0 : succ (L m one d0 d1) one d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_one (L m one d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_pred, succ, pred; repeat split; assumption.
 unfold half_red_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_blue_succ m d1).
 assert (t0 : pred (L m one d0 d1) one d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_one (L m one d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_succ, succ, pred; repeat split; assumption.
 unfold half_blue_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5 HmapL.
unfold half_blue_succ, half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Hx1.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec;
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d1 y); intro Hy1.
intro h0; subst y; split; do 3 (apply or_not_not_and; right);
apply neq_not_not_neq; apply exd_not_nil with m; assumption.
elim (eq_dart_dec d0 x); intro Hx0.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec.
apply exd_not_nil in Hmap2; intuition.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm1.
apply IHm1 with d1; assumption.
unfold half_red_succ, succ, pred in IHm2.
apply IHm2 with d1; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
unfold half_red_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d0 y); intro Hy0.
intro Hsucc; elim Hsucc; clear Hsucc;
intros [h1 [h2 [h3 h4]]]; subst y; elimeqdartdec.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm1 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
split; do 2 (apply or_not_not_and; right); apply or_not_not_and; left;
apply neq_not_not_neq; unfold half_red_pred, succ, pred in Hd0; intuition.
elim Hd0; clear Hd0; intro Hd0.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm2 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
split; do 2 (apply or_not_not_and; right); apply or_not_not_and; left;
apply neq_not_not_neq; unfold half_red_pred, succ, pred in Hd0; intuition.
intro Hsucc; elim Hsucc; clear Hsucc; intros [h1 [h2 [h3 h4]]].
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_succ, succ, pred in IHm1.
apply IHm1 with x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
unfold half_red_succ, succ, pred in IHm2.
apply IHm2 with x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm1.
apply IHm1 with d1; assumption.
unfold half_red_succ, succ, pred in IHm2.
apply IHm2 with d1; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm1 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_succ, succ, pred in IHm3.
apply IHm3 with x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
unfold half_red_succ, succ, pred in IHm4.
apply IHm4 with x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
split.
unfold half_blue_succ, succ, pred in IHm1.
apply IHm1 with d1; assumption.
unfold half_red_succ, succ, pred in IHm2.
apply IHm2 with d1; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm2 with d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
Qed.

Lemma half_eqc_hbp_hrp :
  forall (m:fmap)(x:dart)(y:dart),
  inv_hmap m -> inv_half m -> eqc m x y -> x <> y ->
  half_blue_pred m x \/ half_red_pred m x -> 
  ~ half_blue_pred m y /\ ~ half_red_pred m y.
Proof.
induction m.
 (* K1 : V *)
 intros x y Hmap Half H0 Hneq.
 simpl in *; intuition.
 (* K2 : I *)
 intros x y Hmap Half H0 Hneq.
 simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 elim H0; clear H0; intro H0.
  destruct H0 as [h1 h2].
  subst x; subst y; tauto.
 assert (H1 : inv_half m); [idtac | clear Half].
  unfold inv_half; intros da Hda.
  assert (H1 : d = da \/ exd m da); [right; assumption | idtac].
  generalize (Half da H1); clear Half.
  unfold black_dart, blue_dart, red_dart;
  unfold half_blue_succ, half_blue_pred, half_red_succ, half_red_pred;
  unfold succ, pred; simpl; trivial.
 generalize (IHm x y Hmap H1 H0 Hneq); clear IHm; intro IHm.
 unfold half_blue_succ, half_blue_pred, half_red_succ, half_red_pred in *;
 unfold succ, pred in *; simpl in *; try assumption.
 (* K3 : L *)
assert (IHm1 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_blue_pred m x -> ~ half_blue_pred m y).
intros da db H1 H2 H3 H4 H5; apply or_introl with (half_blue_pred m da) (half_red_pred m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm2 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_blue_pred m x -> ~ half_red_pred m y).
intros da db H1 H2 H3 H4 H5; apply or_introl with (half_blue_pred m da) (half_red_pred m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm3 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_red_pred m x -> ~ half_blue_pred m y).
intros da db H1 H2 H3 H4 H5; apply or_intror with (half_blue_pred m da) (half_red_pred m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
assert (IHm4 : forall (x:dart)(y:dart), inv_hmap m -> inv_half m -> eqc m x y -> x <> y -> half_red_pred m x -> ~ half_red_pred m y).
intros da db H1 H2 H3 H4 H5; apply or_intror with (half_blue_pred m da) (half_red_pred m da) in H5.
generalize (IHm da db H1 H2 H3 H4 H5); intros [t1 t2]; assumption.
 intros x y Hmap Half H0 Hneq.
 generalize Hmap; intro HmapL.
 simpl in Hmap; unfold prec_L in Hmap.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (eq_dart_dec d0 d1); intro Heq.
subst d1; generalize (fixpoint_cA m d d0 Hmap Hmap1 Hmap3 Hmap4); contradiction.
 induction d; simpl in H0; clear IHm.
 (* K31 : d = zero *)
assert (Hd0 : black_dart m d0 \/ half_blue_pred m d0).
 assert (t0 : succ (L m zero d0 d1) zero d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_zero (L m zero d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_pred, succ, pred; repeat split; assumption.
 unfold half_blue_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_red_succ m d1).
 assert (t0 : pred (L m zero d0 d1) zero d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_zero (L m zero d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_succ, succ, pred; repeat split; assumption.
 unfold half_red_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5 HmapL.
unfold half_blue_pred, half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Hx0.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec;
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d0 y); intro Hy0.
intro h0; subst y; split; apply or_not_not_and; left;
apply neq_not_not_neq; apply exd_not_nil with m; assumption.
elim (eq_dart_dec d1 x); intro Hx1.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec.
apply exd_not_nil in Hmap1; intuition.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm1.
apply IHm1 with d0; assumption.
unfold half_red_pred, succ, pred in IHm2.
apply IHm2 with d0; assumption.
unfold half_red_succ, succ, pred in Hd1; intuition.
elim (eq_dart_dec d1 y); intro Hy1.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst y; elimeqdartdec.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm1 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
split; apply or_not_not_and; right; apply or_not_not_and; left;
apply neq_not_not_neq; unfold half_red_succ, succ, pred in Hd1; intuition.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm2 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
split; apply or_not_not_and; right; apply or_not_not_and; left;
apply neq_not_not_neq; unfold half_red_succ, succ, pred in Hd1; intuition.
intro Hpred; elim Hpred; clear Hpred; intros [h1 [h2 [h3 h4]]].
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_pred, succ, pred in IHm1.
apply IHm1 with x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
unfold half_red_pred, succ, pred in IHm2.
apply IHm2 with x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm1 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm1.
apply IHm1 with d0; assumption.
unfold half_red_pred, succ, pred in IHm2.
apply IHm2 with d0; assumption.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_pred, succ, pred in IHm3.
apply IHm3 with x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
unfold half_red_pred, succ, pred in IHm4.
apply IHm4 with x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm2 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm1.
apply IHm1 with d0; assumption.
unfold half_red_pred, succ, pred in IHm2.
apply IHm2 with d0; assumption.
 (* K32 : d = one *)
assert (Hd0 : black_dart m d0 \/ half_red_pred m d0).
 assert (t0 : succ (L m one d0 d1) one d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_one (L m one d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_pred, succ, pred; repeat split; assumption.
 unfold half_red_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_blue_succ m d1).
 assert (t0 : pred (L m one d0 d1) one d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_one (L m one d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_succ, succ, pred; repeat split; assumption.
 unfold half_blue_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5 HmapL.
unfold half_blue_pred, half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Hx0.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec;
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d0 y); intro Hy0.
intro h0; subst y; split; apply or_not_not_and; right; apply or_not_not_and; left;
apply neq_not_not_neq; apply exd_not_nil with m; assumption.
elim (eq_dart_dec d1 x); intro Hx1.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst x; elimeqdartdec.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 y; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm3.
apply IHm3 with d0; assumption.
unfold half_red_pred, succ, pred in IHm4.
apply IHm4 with d0; assumption.
unfold half_blue_succ, succ, pred in Hd1; intuition.
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d1 y); intro Hy1.
intro Hpred; elim Hpred; clear Hpred;
intros [h1 [h2 [h3 h4]]]; subst y; elimeqdartdec.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm3 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
split; apply or_not_not_and; left; apply neq_not_not_neq;
unfold half_blue_succ, succ, pred in Hd1; intuition.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm4 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
split; apply or_not_not_and; left; apply neq_not_not_neq;
unfold half_blue_succ, succ, pred in Hd1; intuition.
intro Hpred; elim Hpred; clear Hpred; intros [h1 [h2 [h3 h4]]].
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_pred, succ, pred in IHm1.
apply IHm1 with x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
unfold half_red_pred, succ, pred in IHm2.
apply IHm2 with x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm3 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm3.
apply IHm3 with d0; assumption.
unfold half_red_pred, succ, pred in IHm4.
apply IHm4 with d0; assumption.
elim H0; clear H0; intro H0; [idtac | elim H0; clear H0; intros [t1 t2]].
split.
unfold half_blue_pred, succ, pred in IHm3.
apply IHm3 with x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
unfold half_red_pred, succ, pred in IHm4.
apply IHm4 with x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply IHm4 with d0 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 y; assumption.
split.
unfold half_blue_pred, succ, pred in IHm3.
apply IHm3 with d0; assumption.
unfold half_red_pred, succ, pred in IHm4.
apply IHm4 with d0; assumption.
Qed.

(* ========================== *)

Lemma half_eqc_hbs_1 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_blue_succ m d0 -> half_blue_succ m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_introl with (half_blue_succ m d0) (half_red_succ m d0) in Hd0.
generalize (half_eqc_hbs_hrs m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h1; assumption.
Qed.

Lemma half_eqc_hbs_2 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_blue_succ m d0 -> half_red_succ m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_introl with (half_blue_succ m d0) (half_red_succ m d0) in Hd0.
generalize (half_eqc_hbs_hrs m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h2; assumption.
Qed.

Lemma half_eqc_hbp_1 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_blue_pred m d0 -> half_blue_pred m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_introl with (half_blue_pred m d0) (half_red_pred m d0) in Hd0.
generalize (half_eqc_hbp_hrp m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h1; assumption.
Qed.

Lemma half_eqc_hbp_2 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_blue_pred m d0 -> half_red_pred m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_introl with (half_blue_pred m d0) (half_red_pred m d0) in Hd0.
generalize (half_eqc_hbp_hrp m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h2; assumption.
Qed.

Lemma half_eqc_hrs_1 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_red_succ m d0 -> half_blue_succ m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_intror with (half_blue_succ m d0) (half_red_succ m d0) in Hd0.
generalize (half_eqc_hbs_hrs m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h1; assumption.
Qed.

Lemma half_eqc_hrs_2 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_red_succ m d0 -> half_red_succ m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_intror with (half_blue_succ m d0) (half_red_succ m d0) in Hd0.
generalize (half_eqc_hbs_hrs m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h2; assumption.
Qed.

Lemma half_eqc_hrp_1 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_red_pred m d0 -> half_blue_pred m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_intror with (half_blue_pred m d0) (half_red_pred m d0) in Hd0.
generalize (half_eqc_hbp_hrp m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h1; assumption.
Qed.

Lemma half_eqc_hrp_2 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap m -> inv_half m -> d0 <> d1 ->
  half_red_pred m d0 -> half_red_pred m d1 ->
  ~ eqc m d0 d1.
Proof.
intros m d0 d1 Hmap Half Hneq Hd0 Hd1 Heqc.
apply or_intror with (half_blue_pred m d0) (half_red_pred m d0) in Hd0.
generalize (half_eqc_hbp_hrp m d0 d1 Hmap Half Heqc Hneq Hd0).
intros [h1 h2]; apply h2; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma half_eqc_expf :
  forall (m:fmap)(d0:dart)(d1:dart)(d2:dart),
  inv_hmap m -> inv_half m ->
  half_blue_succ m d0 \/ half_blue_pred m d0 \/
  half_red_succ m d0 \/ half_red_pred m d0 ->
  eqc m d0 d1 -> eqc m d0 d2 -> expf m d1 d2.
Proof.
induction m.
 (* K1 : V *)
 intros x y z Hmap Half H0 H1 H2.
 simpl in *; intuition.
 (* K2 : I *)
 intros x y z Hmap Half H0 H1 H2.
 simpl in *; unfold prec_I in Hmap.
 destruct Hmap as [Hmap [Hmap1 Hmap2]].
 elim H1; clear H1; intro H1.
 destruct H1 as [h1 h2].
 subst x; subst y.
 elim H2; clear H2; intro H2.
 destruct H2 as [h1 h2].
 subst z; clear h1.
 apply expf_refl; simpl.
 unfold prec_I; repeat split; assumption.
 left; trivial.
 apply eqc_exd_exd in H2; intuition.
 elim H2; clear H2; intro H2.
 destruct H2 as [h1 h2].
 subst x; subst z.
 apply eqc_exd_exd in H1; intuition.
assert (H : forall (m:fmap)(x:dart)(y:dart)(z:dart)(t:tag)(p:point),
inv_hmap m -> prec_I m x -> exd m y -> x <> y -> expf m y z -> expf (I m x t p) y z).
intros m0 x0 y0 z0 t0 p0 h1 h2 h3 h4 h5.
generalize (expf_I m0 x0 y0 z0 t0 p0 h1 h2 h3 h4).
intro H; intuition.
 apply H; try assumption.
 unfold prec_I; split; try assumption.
 apply eqc_exd_exd in H1; intuition.
 apply neq_sym; apply exd_not_exd_neq with m; try assumption.
 apply eqc_exd_exd in H1; intuition.
 apply IHm with x; try assumption.
 unfold inv_half; intros da Hda.
 assert (h0 : d = da \/ exd m da); [right; assumption | idtac].
 generalize (Half da h0); clear Half.
 unfold black_dart, blue_dart, red_dart;
 unfold half_blue_succ, half_blue_pred, half_red_succ, half_red_pred;
 unfold succ, pred; simpl; trivial.
 (* K3 : L *)
 intros x y z Hmap Half H0 H1 H2.
 generalize Hmap; intro HmapL.
 simpl in Hmap; unfold prec_L in Hmap.
 destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
(**)
assert (Hexd : exd m y).
 elim H1; clear H1; intro H1.
 apply eqc_exd_exd in H1; destruct H1 as [h1 h2]; assumption.
 elim H1; clear H1; intro H1; destruct H1 as [h1 h2]; clear h1; 
 apply eqc_exd_exd in h2; destruct h2 as [h1 h2]; assumption.
elim (eq_dart_dec d0 d1); intro Hneq.
subst d1; generalize (fixpoint_cA m d d0 Hmap Hmap1 Hmap3 Hmap4); contradiction.
(**)
 induction d; simpl in H1, H2.
 (* K31 : d = zero *)
assert (Hd0 : black_dart m d0 \/ half_blue_pred m d0).
 assert (t0 : succ (L m zero d0 d1) zero d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_zero (L m zero d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_pred, succ, pred; repeat split; assumption.
 unfold half_blue_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_red_succ m d1).
 assert (t0 : pred (L m zero d0 d1) zero d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_zero (L m zero d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_succ, succ, pred; repeat split; assumption.
 unfold half_red_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5.
apply expf_L0_CS; try assumption; clear Hexd.
elim expf_dec; intro Hexpf.
(*1*)
elim Hd0; clear Hd0; intro Hd0.
(*1.1*)
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
(*1.2*)
elim Hd1; clear Hd1; intro Hd1.
(*1.2.1*)
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
apply eqc_symm; apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
(*1.2.2*)
right; right; split.
(*1.2.2.1*)
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
(*1.2.2.1.1*)
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.1.1.1*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 (cA_1 m one d0) x).
apply eqc_symm; apply my_expf_eqc; assumption.
apply (eqc_trans m (cA_1 m one d0) y x); try assumption.
apply eqc_symm; assumption.
(*1.2.2.1.1.2*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 (cA_1 m one d0) x).
apply eqc_symm; apply my_expf_eqc; assumption.
apply eqc_symm; apply eqc_eqc_cA_1; assumption.
(*1.2.2.1.1.3*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.2*)
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.1.2.1*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 y x).
apply eqc_cA_1_eqc with one; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.2.2*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.2.3*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.3*)
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.1.3.1*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 (cA_1 m one d0) x).
apply eqc_symm; apply my_expf_eqc; assumption.
apply (eqc_trans m (cA_1 m one d0) y x); try assumption.
apply eqc_symm; assumption.
(*1.2.2.1.3.2*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 (cA_1 m one d0) x).
apply eqc_symm; apply my_expf_eqc; assumption.
apply eqc_symm; apply eqc_eqc_cA_1; assumption.
(*1.2.2.1.3.3*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.4*)
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.1.4.1*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 y x).
apply eqc_cA_1_eqc with one; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.4.2*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.1.4.3*)
apply my_not_eqc_not_expf; intro h0.
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2*)
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
(*1.2.2.2.1*)
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.2.1.1*)
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
(*1.2.2.2.1.1.1*)
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
(*1.2.2.2.1.1.2*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 d0 x).
apply eqc_symm; apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.1.1.3*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.1.2*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 d0 x).
apply eqc_symm; apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.1.3*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_1 m d1 x Hmap Half Heq1 Hd1).
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.2*)
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.2.2.1*)
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
(*1.2.2.2.2.1.1*)
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
(*1.2.2.2.2.1.2*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.2.1.3*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.2.2*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.2.3*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_1 m d0 x Hmap Half Heq0 Hd0).
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.3*)
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.2.3.1*)
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
(*1.2.2.2.3.1.1*)
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
(*1.2.2.2.3.1.2*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 d0 x).
apply eqc_symm; apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.3.1.3*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.3.2*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply (eqc_trans m d1 d0 x).
apply eqc_symm; apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.3.3*)
cut False; [tauto|idtac].
apply (half_eqc_hrs_2 m d1 x Hmap Half Heq1 Hd1).
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.4*)
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
(*1.2.2.2.4.1*)
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
(*1.2.2.2.4.1.1*)
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
(*1.2.2.2.4.1.2*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.4.1.3*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.4.2*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
(*1.2.2.2.4.3*)
cut False; [tauto|idtac].
apply (half_eqc_hbp_2 m d0 x Hmap Half Heq0 Hd0).
unfold half_red_pred, succ, pred; repeat split; assumption.
apply (eqc_trans m d0 d1 x).
apply eqc_cA_1_eqc with one; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*2*)
elim Hd0; clear Hd0; intro Hd0.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; apply expf_refl; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply expf_refl; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; apply expf_refl; assumption.
left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
right; right; apply IHm with d1; try assumption.
right; right; left; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; split.
rewrite fixpoint_cA_1; try assumption.
apply expf_refl; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd0 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply expf_refl; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply expf_refl; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
right; left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
right; right.
apply IHm with d0; try assumption.
right; left; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
right; right; apply IHm with d1; try assumption.
right; right; left; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; right; apply IHm with d0; try assumption.
right; left; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_eqc_cA_1; assumption.
apply IHm with d1; try assumption.
right; right; left; assumption.
apply eqc_refl; assumption.
right; right; apply IHm with d1; try assumption.
right; right; left; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; split.
apply IHm with d0; try assumption.
right; left; assumption.
apply eqc_cA_1_r; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; right; apply IHm with d0; try assumption.
right; left; assumption.
 (* K32 : d = one *)
assert (Hd0 : black_dart m d0 \/ half_red_pred m d0).
 assert (t0 : succ (L m one d0 d1) one d0).
  unfold succ; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_succ_one (L m one d0 d1) d0 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold red_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_red_pred, succ, pred; repeat split; assumption.
 unfold half_red_succ, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
assert (Hd1 : black_dart m d1 \/ half_blue_succ m d1).
 assert (t0 : pred (L m one d0 d1) one d1).
  unfold pred; simpl; elimeqdartdec.
  apply exd_not_nil with m; assumption.
 generalize (inv_half_pred_one (L m one d0 d1) d1 HmapL Half t0).
 intro h0; elim h0; clear h0.
 unfold blue_dart, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; right; unfold half_blue_succ, succ, pred; repeat split; assumption.
 unfold half_blue_pred, succ, pred; simpl; elimeqdartdec.
 intros [h1 [h2 [h3 h4]]]; left; unfold black_dart, succ, pred; repeat split; assumption.
(**)
apply inv_half_L in Half; try assumption; clear Hmap3 Hmap4 Hmap5.
apply expf_L1_CS; try assumption; clear Hexd.
elim expf_dec; intro Hexpf.
(*1*)
elim Hd0; clear Hd0; intro Hd0.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
elim Hd1; clear Hd1; intro Hd1.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
right; right; split.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_trans with y; try assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_trans with y; try assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_trans with y; try assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_trans with y; try assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
apply my_not_eqc_not_expf; intro h0.
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_trans with d0; try assumption.
apply eqc_symm; apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_trans with d1; try assumption.
apply eqc_cA_eqc with zero; try assumption.
apply my_expf_eqc; assumption.
apply eqc_symm; assumption.
(*2*)
elim Hd0; clear Hd0; intro Hd0.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; split.
apply expf_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; left; split.
apply expf_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; apply expf_refl; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
apply expf_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; split.
apply expf_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_trans with x; try assumption.
apply eqc_symm; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_trans with x; try assumption.
apply eqc_symm; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; apply expf_refl; assumption.
right; left; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; right; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
left; apply IHm with d1; try assumption.
left; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 d1; try assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; right; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_trans with x; try assumption.
apply eqc_symm; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply expf_refl; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_trans with x; try assumption.
apply eqc_symm; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d0 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
elim Hd1; clear Hd1; intro Hd1.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x; clear h1 h2 h3 h4.
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
apply black_eqc_eq in H1; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
left; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
right; right; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
apply black_eqc_eq in H2; try assumption; subst z.
right; left; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 d0; try assumption.
apply neq_sym; assumption.
left; apply IHm with d0; try assumption.
right; right; right; assumption.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
right; left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
apply black_eqc_eq in y2; try assumption; subst y.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
rewrite fixpoint_cA; try assumption.
apply expf_refl; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
destruct Hd1 as [hb1 [hb2 [hb3 hb4]]]; assumption.
apply black_eqc_eq in z2; try assumption; subst z.
left; apply expf_refl; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply black_not_eqc with m d1 x; try assumption.
apply eqc_symm; assumption.
elim H0; clear H0; [idtac | intro H0; elim H0; clear H0; [idtac | intro H0; [elim H0; clear H0]]].
unfold half_blue_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
right; left; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; split.
apply IHm with x; try assumption.
left; unfold half_blue_succ, succ, pred; repeat split; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
left; apply IHm with d1; try assumption.
left; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_1 with m d1 x; try assumption.
unfold half_blue_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_blue_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_blue_succ, succ, pred in Hd1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; right; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_eqc_cA; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
apply IHm with x; try assumption.
right; left; unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_eqc_cA; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_1 with m d0 x; try assumption.
unfold half_blue_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
left; apply IHm with d0; try assumption.
right; right; right; assumption.
unfold half_red_succ, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
unfold half_red_pred, succ, pred in Hd0; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
right; left; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; right; split.
apply IHm with x; try assumption.
right; right; left; unfold half_red_succ, succ, pred; repeat split; assumption.
apply IHm with d1; try assumption.
left; assumption.
apply eqc_cA_r; assumption.
left; apply IHm with d1; try assumption.
left; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
cut False; [tauto|idtac].
apply half_eqc_hbs_2 with m d1 x; try assumption.
unfold half_red_succ, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
unfold half_red_pred, succ, pred; simpl.
elim (eq_dart_dec d0 x); intro Heq0.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap2; intuition.
elim (eq_dart_dec d1 x); intro Heq1.
intros [h1 [h2 [h3 h4]]]; subst x.
apply exd_not_nil in Hmap1; intuition.
intros [h1 [h2 [h3 h4]]].
elim H1; clear H1; intro H1; [idtac | elim H1; clear H1; intros [y1 y2]].
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
left; apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
right; right; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_eqc_cA; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
elim H2; clear H2; intro H2; [idtac | elim H2; clear H2; intros [z1 z2]].
right; left; split.
apply IHm with d0; try assumption.
right; right; right; assumption.
apply eqc_refl; assumption.
apply IHm with x; try assumption.
right; right; right; unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_eqc_cA; assumption.
cut False; [tauto|idtac].
apply half_eqc_hrp_2 with m d0 x; try assumption.
unfold half_red_pred, succ, pred; repeat split; assumption.
apply eqc_symm; assumption.
left; apply IHm with d0; try assumption.
right; right; right; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Theorem planar_CHID :
  forall (m:fmap)(mr:fmap)(x:dart)(tx:tag)(px:point)(max:dart),
  submap m mr -> inv_hmap m ->
  inv_hmap mr -> inv_poly mr -> well_emb mr -> inv_noalign_point mr px -> convex mr ->
  x <> nil -> max <> nil -> x <> max -> ~ exd mr x -> ~ exd mr max ->
  planar m -> planar (CHID m mr x tx px max).
Proof.
intros m mr x tx px max Hsub Hmap Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hneq1 Hneq2 Hneq3 Hexd1 Hexd2 H.
induction m.
 (* Cas 1 : m = V *)
 simpl in *.
 apply my_planar_planar_I; try assumption.
 simpl; unfold prec_I; simpl;
 repeat split; intuition.
 (* Cas 2 : m = I *)
apply my_planar_I_planar in H; try assumption.
simpl in Hsub, Hmap.
unfold prec_I in Hmap.
destruct Hsub as [Hsub [Hsub1 [Hsub2 Hsub3]]].
destruct Hmap as [Hmap [Hneq4 Hexd3]].
generalize (IHm Hsub Hmap H); clear IHm; intro IHm.
 simpl.
 elim blue_dart_dec.
  elim invisible_dec.
   intros H_ccw H_blue.
(* == 1 == *)
apply my_planar_planar_I; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
(* ======= *)
   elim left_dart_dec.
    intros H_left H_ccw H_blue.
(* == 2 == *)
apply plf_planar.
simpl.
unfold prec_I, prec_L, succ, pred.
simpl; elimeqdartdec; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
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
 apply inv_hmap_CHID; intuition.
 apply (not_exd_CHID m mr x tx px max d); try assumption.
  apply (exd_not_exd_neq mr d x); assumption.
  apply (exd_not_exd_neq mr d max); assumption.
unfold pred; simpl; apply (max_CHID_5 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr max); try assumption.
 apply (map_left_dart_less m mr px d); try assumption.
elim (eq_dart_dec max d).
 intro Heq; subst d; contradiction.
 elimeqdartdec; intuition.
simpl.
repeat split.
apply planar_plf.
apply inv_hmap_CHID; intuition.
unfold planar in *.
apply IHm; clear IHm.
(**)
left.
unfold not.
intro h0.
elim h0; clear h0.
intros [h1 h2].
contradiction.
intro h0; elim h0; clear h0.
intros [h1 h2].
rewrite h2 in Hexd1.
contradiction.
intro h0.
apply eqc_exd_exd in h0.
destruct h0 as [h1 h2].
assert (h0 : ~ exd m max).
apply submap_not_exd with mr; assumption.
apply exd_max_exd_left_dart in h1; try assumption.
elim h1; clear h1.
intros da [hda1 hda2].
generalize (map_left_dart_less m mr px d Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hmap Hexd3 H_left).
intro h1; generalize (h1 da hda1).
intro h; contradiction.
(**)
elimeqdartdec.
left.
unfold not.
intro h0.
elim h0; clear h0.
intro h0.
elim h0; clear h0.
intros [h1 h2].
rewrite h1 in Hsub1.
contradiction.
intro h0.
elim h0; clear h0.
intros [h1 h2].
rewrite <- h2 in Hsub1.
contradiction.
intro h0.
apply eqc_exd_exd in h0.
destruct h0 as [h1 h2].
assert (h0 : ~ exd m max).
apply submap_not_exd with mr; assumption.
apply exd_max_exd_left_dart in h2; try assumption.
elim h2; clear h2.
intros da [hda1 hda2].
generalize (map_left_dart_less m mr px d Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hmap Hexd3 H_left).
intro h2; generalize (h2 da hda1).
intro h; contradiction.
(**)
intro h0; elim h0; clear h0.
intros [h1 h2]; clear h2.
elim h1; clear h1.
intros [h1 h2].
rewrite h1 in Hsub1.
contradiction.
intro h1; elim h1; clear h1.
intros [h1 h2].
rewrite <- h2 in Hsub1.
contradiction.
intro h0.
apply eqc_exd_exd in h0.
destruct h0 as [h1 h2].
assert (h0 : ~ exd m max).
apply submap_not_exd with mr; assumption.
apply exd_max_exd_left_dart in h2; try assumption.
elim h2; clear h2.
intros da [hda1 hda2].
generalize (map_left_dart_less m mr px d Hmr1 Hmr2 Hmr3 Hmr4 Hmr5 Hmap Hexd3 H_left).
intro h2; generalize (h2 da hda1).
intro h; contradiction.
(**)
intros [h1 h2]; clear h2.
elim h1; clear h1.
intros [h1 h2].
rewrite h1 in Hsub1.
contradiction.
intro h1; elim h1; clear h1.
intros [h1 h2].
rewrite <- h2 in Hsub1.
contradiction.
intro h0.
apply eqc_exd_exd in h0.
destruct h0 as [h1 h2].
assert (h0 : ~ exd (CHID m mr x tx px max) d).
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
contradiction.
(* ======= *)
    intros H_left H_ccw H_blue.
(* == 3 == *)
apply my_planar_planar_I; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
(* ======= *)
  elim red_dart_dec.
   elim invisible_dec.
    intros H_ccw H_red H_blue.
(* == 4 == *)
apply my_planar_planar_I; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
(* ======= *)
    elim right_dart_dec.
     intros H_right H_ccw H_red H_blue.
(* == 5 == *)
apply my_planar_planar_L_0; try assumption.
simpl; unfold prec_I, prec_L, succ, pred.
simpl; elimeqdartdec; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply (not_exd_CHID m mr x tx px max d); try assumption.
 apply (exd_not_exd_neq mr d x); assumption.
 apply (exd_not_exd_neq mr d max); assumption.
right; apply (x_CHID_1 m mr x tx px max); try assumption.
left; trivial.
unfold succ; simpl; apply (x_CHID_4 m mr x tx px max); try assumption.
 apply (submap_not_exd m mr x); try assumption.
 apply (map_right_dart_less m mr px d); try assumption.
unfold pred; simpl; apply eq_not_neq; apply not_exd_A_1_nil; try assumption.
 apply inv_hmap_CHID; intuition.
 apply (not_exd_CHID m mr x tx px max d); try assumption.
  apply (exd_not_exd_neq mr d x); assumption.
  apply (exd_not_exd_neq mr d max); assumption.
elim (eq_dart_dec d x); intro Heq.
 subst d; contradiction.
 assert (H0 : cA (CHID m mr x tx px max) zero x = x).
  apply fixpoint_cA; try assumption.
  apply inv_hmap_CHID; intuition.
  apply (x_CHID_1 m mr x tx px max); try assumption.
  apply (x_CHID_4 m mr x tx px max); try assumption.
   apply (submap_not_exd m mr x); try assumption.
   apply (map_right_dart_less m mr px d); try assumption.
  apply (x_CHID_3 m mr x tx px max); try assumption.
   apply (submap_not_exd m mr x); try assumption.
 rewrite H0; apply neq_sym; assumption.
apply my_planar_planar_I; try assumption.
simpl; unfold prec_I; simpl.
repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
(**)
left.
unfold not.
intro h0.
elim h0; clear h0.
intros [h1 h2].
rewrite <- h1 in Hsub1.
contradiction.
intro h0.
apply eqc_exd_exd in h0.
destruct h0 as [h1 h2].
assert (h0 : ~ exd (CHID m mr x tx px max) d).
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
contradiction.
(* ======= *)
     intros H_right H_ccw H_red H_blue.
(* == 6 == *)
assumption.
(* ======= *)
   intros H_red H_blue.
(* == 7 == *)
apply my_planar_planar_I; try assumption.
simpl; unfold prec_I; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
apply not_exd_CHID; try assumption.
apply exd_not_exd_neq with mr; assumption.
apply exd_not_exd_neq with mr; assumption.
(* ======= *)
 (* Cas 3 : m = L *)
apply my_planar_L_planar in H; try assumption.
simpl in Hsub, Hmap.
unfold prec_L in Hmap.
destruct Hsub as [Hsub [Hsub1 Hsub2]].
destruct Hmap as [Hmap [H1 [H2 [H3 [H4 H5]]]]].
generalize (IHm Hsub Hmap H); clear IHm; intro IHm.
induction d; simpl in *.
  elim ccw_dec.
   intros H_ccw.
(* == 8 == *)
apply my_planar_planar_L_0; try assumption.
simpl; unfold prec_L; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
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
 apply inv_hmap_CHID; intuition.
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
(**)
assert (h1 : blue_dart mr d0).
 apply succ_zero_blue_dart; try assumption.
 unfold succ; rewrite Hsub1.
 apply exd_not_nil with m; try assumption.
assert (h2 : red_dart mr d1).
 apply pred_zero_red_dart; try assumption.
 unfold pred; rewrite Hsub2.
 apply exd_not_nil with m; try assumption.
assert (h3 : d0 <> d1).
 assert (h3 : cA m zero d0 = d0).
  apply fixpoint_cA; try assumption.
  apply submap_not_pred with mr; try assumption.
  unfold blue_dart in h1; intuition.
 rewrite h3 in H5; assumption.
(**)
elim (eqc_dec (CHID m mr x tx px max) d0 d1); intro Heqc.
 elim (succ_dec (CHID m mr x tx px max) one d1); intro Hs1.
  assert (h0 : half_red_succ (CHID m mr x tx px max) d1).
   unfold half_red_succ; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_8; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   rewrite Hsub2; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  right; apply expf_symm.
  apply half_eqc_expf with d1; try assumption.
  apply inv_hmap_CHID; intuition.
  apply inv_half_CHID; intuition.
  right; right; left; assumption.
  apply eqc_refl; try assumption.
  apply eqc_exd_exd in Heqc; intuition.
  apply eqc_eqc_cA_1; try assumption.
  apply inv_hmap_CHID; intuition.
  apply eqc_symm; assumption.
  assert (h0 : black_dart (CHID m mr x tx px max) d1).
   unfold black_dart; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_8; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   rewrite Hsub2; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  assert (hmap : inv_hmap (CHID m mr x tx px max)).
   apply inv_hmap_CHID; intuition.
  generalize (black_not_eqc (CHID m mr x tx px max) d1 d0 hmap h0 (neq_sym d0 d1 h3)).
  intro heqc; apply eqc_symm in Heqc; contradiction.
 left; assumption.
(* ======= *)
   intros H_ccw.
(* == 9 == *)
assumption.
(* ======= *)
  elim invisible_dec.
   intros H_ccw.
(* == 10 == *)
apply my_planar_planar_L_1; try assumption.
simpl; unfold prec_L; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
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
 apply inv_hmap_CHID; intuition.
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
(**)
assert (h1 : red_dart mr d0).
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1.
 apply exd_not_nil with m; try assumption.
assert (h2 : blue_dart mr d1).
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2.
 apply exd_not_nil with m; try assumption.
assert (h3 : d0 <> d1).
 assert (h3 : cA m one d0 = d0).
  apply fixpoint_cA; try assumption.
  apply submap_not_pred with mr; try assumption.
  unfold red_dart in h1; intuition.
 rewrite h3 in H5; assumption.
(**)
elim (eqc_dec (CHID m mr x tx px max) d0 d1); intro Heqc.
 elim (pred_dec (CHID m mr x tx px max) zero d0); intro Hp0.
  assert (h0 : half_red_pred (CHID m mr x tx px max) d0).
   unfold half_red_pred; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_5; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  right; apply half_eqc_expf with d0; try assumption.
  apply inv_hmap_CHID; intuition.
  apply inv_half_CHID; intuition.
  right; right; right; assumption.
  apply eqc_refl; try assumption.
  apply eqc_exd_exd in Heqc; intuition.
  apply eqc_eqc_cA; try assumption.
  apply inv_hmap_CHID; intuition.
  assert (h0 : black_dart (CHID m mr x tx px max) d0).
   unfold black_dart; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_5; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  assert (hmap : inv_hmap (CHID m mr x tx px max)).
   apply inv_hmap_CHID; intuition.
  left; apply (black_not_eqc (CHID m mr x tx px max) d0 d1 hmap h0 h3).
 left; assumption.
(* ======== *)
   elim invisible_dec.
    intros H_ccw1 H_ccw2.
(* == 11 == *)
apply my_planar_planar_L_1; try assumption.
simpl; unfold prec_L; repeat split; try assumption.
apply inv_hmap_CHID; intuition.
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
 apply inv_hmap_CHID; intuition.
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
(**)
assert (h1 : red_dart mr d0).
 apply succ_one_red_dart; try assumption.
 unfold succ; rewrite Hsub1.
 apply exd_not_nil with m; try assumption.
assert (h2 : blue_dart mr d1).
 apply pred_one_blue_dart; try assumption.
 unfold pred; rewrite Hsub2.
 apply exd_not_nil with m; try assumption.
assert (h3 : d0 <> d1).
 assert (h3 : cA m one d0 = d0).
  apply fixpoint_cA; try assumption.
  apply submap_not_pred with mr; try assumption.
  unfold red_dart in h1; intuition.
 rewrite h3 in H5; assumption.
(**)
elim (eqc_dec (CHID m mr x tx px max) d0 d1); intro Heqc.
 elim (pred_dec (CHID m mr x tx px max) zero d0); intro Hp0.
  assert (h0 : half_red_pred (CHID m mr x tx px max) d0).
   unfold half_red_pred; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_13; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply not_invisible_visible; assumption.
   rewrite Hsub1; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  right; apply half_eqc_expf with d0; try assumption.
  apply inv_hmap_CHID; intuition.
  apply inv_half_CHID; intuition.
  right; right; right; assumption.
  apply eqc_refl; try assumption.
  apply eqc_exd_exd in Heqc; intuition.
  apply eqc_eqc_cA; try assumption.
  apply inv_hmap_CHID; intuition.
  assert (h0 : black_dart (CHID m mr x tx px max) d0).
   unfold black_dart; repeat split; try assumption.
   apply red_dart_CHID_1; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply red_dart_CHID_13; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
   apply not_invisible_visible; assumption.
   rewrite Hsub1; assumption.
   apply red_dart_CHID_2; try assumption.
   apply exd_not_exd_neq with mr; try assumption.
   apply submap_exd with m; assumption.
  assert (hmap : inv_hmap (CHID m mr x tx px max)).
   apply inv_hmap_CHID; intuition.
  left; apply (black_not_eqc (CHID m mr x tx px max) d0 d1 hmap h0 h3).
 left; assumption.
(* ======== *)
    intros H_ccw1 H_ccw2.
(* == 12 == *)
assumption.
(* ======== *)
Qed.
