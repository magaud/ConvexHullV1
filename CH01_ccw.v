(* ====================== *)
(* ===== CH01_ccw.v ===== *)
(* ====================== *)

Require Export Jordan5.

Open Scope R_scope.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Definition det (p q r : point) : R :=
  (fst p * snd q) - (fst q * snd p) - (fst p * snd r) + (fst r * snd p) +
  (fst q * snd r) - (fst r * snd q).

Lemma eq_det : forall (p q r : point),
  det p q r = det q r p.
Proof.
intros p q r.
unfold det; ring.
Qed.

Lemma neq_det : forall (p q r : point),
  det p q r = - det p r q.
Proof.
intros p q r.
unfold det; ring.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Definition ccw (p q r : point) : Prop :=
  (det p q r > 0).

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.
Proof.
intros p q r.
unfold ccw; apply Rgt_dec.
Qed.

(* ======= ####### ======= *)

Definition align (p q r : point) : Prop :=
  (det p q r = 0).

Lemma align_dec : forall (p q r : point),
  {align p q r} + {~align p q r}.
Proof.
intros p q r.
unfold align.
generalize (total_order_T (det p q r) 0).
generalize (Rlt_dichotomy_converse (det p q r) 0).
tauto.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma Rle_neq_lt : forall (r1 r2 : R),
  r1 <= r2 -> r1 <> r2 -> r1 < r2.
Proof.
intros r1 r2 H1 H2.
elim (Rdichotomy r1 r2).
trivial.
generalize (Rle_not_lt r2 r1).
tauto.
assumption.
Qed.

Lemma R_gt_0_plus : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 + r2 > 0.
Proof.
intros r1 r2 H1 H2.
apply Rgt_trans with r1.
 pattern r1 at 2; rewrite <- (Rplus_0_r r1).
 apply Rplus_gt_compat_l; assumption.
assumption.
Qed.

Lemma R_gt_0_mult : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
apply Rmult_gt_0_compat.
Qed.

Lemma R_gt_0_div : forall (r1 r2 : R),
  r1 > 0 -> r2 > 0 -> r1 * / r2 > 0.
Proof.
intros r1 r2 H1 H2.
apply R_gt_0_mult.
 assumption.
 unfold Rgt in *; auto with real.
Qed.

Lemma R_mult_div : forall (r1 r2 r3 : R),
  r1 = r2 * r3 -> r2 > 0 -> r1 * / r2 = r3.
Proof.
intros r1 r2 r3 H1 H2.
subst r1; auto with real.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma axiom_orientation_1 :
  forall (A:point)(B:point)(C:point),
  ccw A B C -> ccw B C A.
Proof.
intros A B C.
unfold ccw; rewrite eq_det; trivial.
Qed.

Lemma axiom_orientation_2 :
  forall (A:point)(B:point)(C:point),
  align A B C -> align B C A.
Proof.
intros A B C.
unfold align; rewrite eq_det; trivial.
Qed.

Lemma axiom_orientation_3 :
  forall (A:point)(B:point)(C:point),
  align A B C -> align A C B.
Proof.
intros A B C.
unfold align; rewrite neq_det.
generalize (Rplus_opp_r (det A C B)).
generalize (Rplus_0_l (det A C B)).
intros H1 H2 H3.
rewrite H3 in H2; clear H3.
rewrite Rplus_comm in H1.
rewrite H1 in H2; clear H1.
assumption.
Qed.

Hint Resolve axiom_orientation_1 axiom_orientation_2 axiom_orientation_3 : myorientation.

(* ======================= *)

Lemma axiom_orientation_4 :
  forall (A:point)(B:point)(C:point),
  ccw A B C -> ~ ccw A C B.
Proof.
intros A B C.
unfold ccw; rewrite neq_det.
generalize (Ropp_gt_lt_contravar (- det A C B) 0).
rewrite Ropp_involutive; rewrite Ropp_0.
intro H1; generalize (Rlt_le (det A C B) 0).
intro H2; generalize (Rle_not_lt 0 (det A C B)).
intro H3; tauto.
Qed.

Lemma axiom_orientation_5 :
  forall (A:point)(B:point)(C:point),
  ccw A B C -> ~ align A B C.
Proof.
intros A B C.
unfold ccw, align in *.
apply Rgt_not_eq; assumption.
Qed.

Lemma axiom_orientation_6 :
  forall (A:point)(B:point)(C:point),
  align A B C -> ~ ccw A B C.
Proof.
intros A B C.
unfold ccw, align in *.
intro H1; rewrite H1.
unfold not; intro H2.
apply Rgt_not_eq in H2; tauto.
Qed.

Hint Resolve axiom_orientation_4 axiom_orientation_5 axiom_orientation_6 : myorientation.

(* ======================= *)

Lemma axiom_orientation_7 :
  forall (A:point)(B:point)(C:point),
  ~ ccw A B C -> ccw A C B \/ align A B C.
Proof.
intros A B C H.
elim (ccw_dec A C B).
 intro H1; left; assumption.
 intro H1; right.
 unfold ccw, align in *.
 rewrite neq_det in H1.
 apply Rle_antisym.
  apply Rnot_gt_le; assumption.
  apply Rnot_gt_le; auto with real.
Qed.

Lemma axiom_orientation_8 :
  forall (A:point)(B:point)(C:point),
  ~ align A B C -> ccw A B C \/ ccw A C B.
Proof.
intros A B C H.
elim (ccw_dec A B C).
 intro H0; left; assumption.
 intro H0; right.
 apply axiom_orientation_7 in H0.
 elim H0; [trivial|contradiction].
Qed.

Hint Resolve axiom_orientation_7 axiom_orientation_8 : myorientation.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma ccw_axiom_1 : forall (p q r : point),
  ccw p q r -> ccw q r p.
Proof.
auto with myorientation.
Qed.

Lemma ccw_axiom_2 : forall (p q r : point),
  ccw p q r -> ~ ccw p r q.
Proof.
auto with myorientation.
Qed.

Lemma ccw_axiom_3 : forall (p q r : point),
  ~ align p q r -> (ccw p q r) \/ (ccw p r q).
Proof.
auto with myorientation.
Qed.

Lemma ccw_axiom_4 : forall (p q r t : point),
  (ccw t q r) -> (ccw p t r) -> (ccw p q t) -> (ccw p q r).
Proof.
intros p q r t H1 H2 H3.
unfold ccw in *.
assert (det t q r + det p t r + det p q t = det p q r).
unfold det; ring.
rewrite <- H.
apply R_gt_0_plus; [apply R_gt_0_plus; assumption | assumption].
Qed.

Lemma ccw_axiom_5 : forall (p q r s t : point),
  (ccw t s p) -> (ccw t s q) -> (ccw t s r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).
Proof.
intros p q r s t H1 H2 H3 H4 H5.
unfold ccw in *.
replace (det t p r) with ((det t p q * det t s r + det t q r * det t s p) * / (det t s q)).
apply R_gt_0_div.
 apply R_gt_0_plus.
  apply R_gt_0_mult; assumption.
  apply R_gt_0_mult; assumption.
 assumption.
apply R_mult_div.
 unfold det; ring.
 assumption.
Qed.

Lemma ccw_axiom_5_bis : forall (p q r s t : point),
  (ccw s t p) -> (ccw s t q) -> (ccw s t r) -> (ccw t p q) -> (ccw t q r) -> 
  (ccw t p r).
Proof.
intros p q r s t H1 H2 H3 H4 H5.
unfold ccw in *.
replace (det t p r) with ((det t p q * det s t r + det t q r * det s t p) * / (det s t q)).
apply R_gt_0_div.
 apply R_gt_0_plus.
  apply R_gt_0_mult; assumption.
  apply R_gt_0_mult; assumption.
 assumption.
apply R_mult_div.
 unfold det; ring.
 assumption.
Qed.
