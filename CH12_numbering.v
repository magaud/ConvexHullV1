(* ============================ *)
(* ===== CH12_numbering.v ===== *)
(* ============================ *)

Require Export CH11_exd.

(* ========================== *)

Open Scope Z_scope.
Require Import ZArith.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Definition P_fmap_dec (P:fmap->dart->Prop)(m:fmap) :=
  {forall d:dart, exd m d -> P m d} + {exists d:dart, exd m d /\ ~ P m d}.

Lemma P_forall_not_exists : forall (P:fmap->dart->Prop)(m:fmap),
  (forall d:dart, exd m d -> P m d) -> ~ (exists d:dart, exd m d /\ ~ P m d).
Proof.
intros P m HA HB.
elim HB; clear HB; intros d [h1 h2].
apply h2; apply HA; assumption.
Qed.

Lemma P_exists_not_forall : forall (P:fmap->dart->Prop)(m:fmap),
  (exists d:dart, exd m d /\ ~ P m d) -> ~ (forall d:dart, exd m d -> P m d).
Proof.
intros P m HA HB.
elim HA; clear HA; intros d [h1 h2].
apply h2; apply HB; assumption.
Qed.

Lemma P_not_exists_forall : forall (P:fmap->dart->Prop)(m:fmap), P_fmap_dec P m ->
  ~ (exists d:dart, exd m d /\ ~ P m d) -> (forall d:dart, exd m d -> P m d).
Proof.
intros P m H0 H.
elim H0; clear H0; intro H0.
assumption. contradiction.
Qed.

Lemma P_not_forall_exists : forall (P:fmap->dart->Prop)(m:fmap), P_fmap_dec P m ->
  ~ (forall d:dart, exd m d -> P m d) -> (exists d:dart, exd m d /\ ~ P m d).
Proof.
intros P m H0 H.
elim H0; clear H0; intro H0.
contradiction. assumption.
Qed.

(* ========================== *)

Definition P_fmap_dec_2 (P:fmap->dart->Prop)(m:fmap) :=
  {forall d:dart, exd m d -> ~ P m d} + {exists d:dart, exd m d /\ P m d}.

Lemma P_forall_not_exists_2 : forall (P:fmap->dart->Prop)(m:fmap),
  (forall d:dart, exd m d -> ~ P m d) -> ~ (exists d:dart, exd m d /\ P m d).
Proof.
intros P m HA HB.
elim HB; clear HB; intros d [h1 h2].
apply HA with d; assumption.
Qed.

Lemma P_exists_not_forall_2 : forall (P:fmap->dart->Prop)(m:fmap),
  (exists d:dart, exd m d /\ P m d) -> ~ (forall d:dart, exd m d -> ~ P m d).
Proof.
intros P m HA HB.
elim HA; clear HA; intros d [h1 h2].
apply HB with d; assumption.
Qed.

Lemma P_not_exists_forall_2 : forall (P:fmap->dart->Prop)(m:fmap), P_fmap_dec_2 P m ->
  ~ (exists d:dart, exd m d /\ P m d) -> (forall d:dart, exd m d -> ~ P m d).
Proof.
intros P m H0 H.
elim H0; clear H0; intro H0.
assumption. contradiction.
Qed.

Lemma P_not_forall_exists_2 : forall (P:fmap->dart->Prop)(m:fmap), P_fmap_dec_2 P m ->
  ~ (forall d:dart, exd m d -> ~ P m d) -> (exists d:dart, exd m d /\ P m d).
Proof.
intros P m H0 H.
elim H0; clear H0; intro H0.
contradiction. assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Fixpoint nl0 (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nl0 m0
  | L m0 zero x y => nl0 m0 + 1
  | L m0 one x y => nl0 m0
  end.

Fixpoint nl1 (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nl1 m0
  | L m0 zero x y => nl1 m0
  | L m0 one x y => nl1 m0 + 1
  end.

(* ========================== *)

Fixpoint nn (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 _ _ _ => nn m0 + 1
  | L m0 zero x y => nn m0
    + (if (pred_dec m0 one x) then 0 else -1)
    + (if (succ_dec m0 one y) then 0 else -1)
  | L m0 one x y => nn m0
    + (if (pred_dec m0 zero x) then 0 else -1)
    + (if (succ_dec m0 zero y) then 0 else -1)
  end.

Fixpoint nb (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nb m0
  | L m0 zero x y => nb m0 +
    if (pred_dec m0 one x) then 1 else 0
  | L m0 one x y => nb m0 +
    if (succ_dec m0 zero y) then 1 else 0
  end.

Fixpoint nr (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nr m0
  | L m0 zero x y => nr m0 +
    if (succ_dec m0 one y) then 1 else 0
  | L m0 one x y => nr m0 +
    if (pred_dec m0 zero x) then 1 else 0
  end.

(* ========================== *)

Fixpoint nhbs (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nhbs m0
  | L m0 zero x y => nhbs m0 +
    if (pred_dec m0 one x) then 0 else 1
  | L m0 one x y => nhbs m0 +
    if (succ_dec m0 zero y) then -1 else 0
  end.

Fixpoint nhbp (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nhbp m0
  | L m0 zero x y => nhbp m0 +
    if (pred_dec m0 one x) then -1 else 0
  | L m0 one x y => nhbp m0 +
    if (succ_dec m0 zero y) then 0 else 1
  end.

Fixpoint nhrs (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nhrs m0
  | L m0 zero x y => nhrs m0 +
    if (succ_dec m0 one y) then -1 else 0
  | L m0 one x y => nhrs m0 +
    if (pred_dec m0 zero x) then 0 else 1
  end.

Fixpoint nhrp (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 x t p => nhrp m0
  | L m0 zero x y => nhrp m0 +
    if (succ_dec m0 one y) then 0 else 1
  | L m0 one x y => nhrp m0 +
    if (pred_dec m0 zero x) then -1 else 0
  end.

Fixpoint nh (m:fmap) {struct m} : Z :=
  match m with
    V => 0
  | I m0 _ _ _ => nh m0
  | L m0 zero x y => nh m0
    + (if (pred_dec m0 one x) then -1 else 1)
    + (if (succ_dec m0 one y) then -1 else 1)
  | L m0 one x y => nh m0
    + (if (pred_dec m0 zero x) then -1 else 1)
    + (if (succ_dec m0 zero y) then -1 else 1)
  end.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma Zeven_ex : forall (n:Z),
  Zeven n -> exists m:Z, (n = m * 2)%Z.
Proof.
intro n; exists (Z.div2 n).
rewrite Zmult_comm.
apply Zeven_div2; auto.
Qed.

Lemma Zeven_2n2 : forall (n:Z),
  Zeven n -> (2 * (n / 2) = n)%Z.
Proof.
intros n H.
elim (Zeven_ex n H); intros x H0.
rewrite H0; rewrite (Z_div_mult x 2).
rewrite Zmult_comm; trivial.
lia.
Qed.

Lemma Zeven_2n : forall (n:Z), Zeven (2 * n).
Proof.
induction n; simpl; tauto.
Qed.

(* ========================== *)

Lemma mynumbering1 :
  forall (m:fmap), inv_hmap m -> planar m ->
  (nv m + ne m + nf m - nd m = 2 * nc m)%Z.
Proof.
intros m Hmap H.
generalize (my_planar_ec m).
intros [h1 h2]; generalize (h1 H).
intro h0; rewrite <- h0; ring_simplify.
cut (2 * (ec m / 2) = ec m)%Z.
intro h; rewrite h; unfold ec; trivial.
clear H h0 h1 h2.
cut (Zeven (ec m)).
apply Zeven_2n2; assumption.
apply even_ec; assumption.
Qed.

Lemma mynumbering2 : forall (m:fmap),
  (nh m = nhbs m + nhbp m + nhrs m + nhrp m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; apply IHm.
induction d; simpl; elim succ_dec; elim pred_dec; intros hp hs;
ring_simplify; (apply IHm || rewrite IHm; trivial).
Qed.

Lemma mynumbering3 : forall (m:fmap),
  (nd m = nn m + nb m + nr m + nh m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; ring_simplify; rewrite IHm; trivial.
induction d; simpl; elim succ_dec; elim pred_dec;
intros hp hs; ring_simplify; apply IHm.
Qed.

Lemma mynumbering4a : forall (m:fmap),
  (nl0 m = nb m + nhbs m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; apply IHm.
induction d; simpl.
elim pred_dec; intro hp; ring_simplify; rewrite IHm; trivial.
elim succ_dec; intro hs; ring_simplify; apply IHm.
Qed.

Lemma mynumbering4b : forall (m:fmap),
  (nl0 m = nr m + nhrp m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; apply IHm.
induction d; simpl.
elim succ_dec; intro hs; ring_simplify; rewrite IHm; trivial.
elim pred_dec; intro hp; ring_simplify; apply IHm.
Qed.

Lemma mynumbering5a : forall (m:fmap),
  (nl1 m = nr m + nhrs m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; apply IHm.
induction d; simpl.
elim succ_dec; intro hs; ring_simplify; apply IHm.
elim pred_dec; intro hp; ring_simplify; rewrite IHm; trivial.
Qed.

Lemma mynumbering5b : forall (m:fmap),
  (nl1 m = nb m + nhbp m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; apply IHm.
induction d; simpl.
elim pred_dec; intro hp; ring_simplify; apply IHm.
elim succ_dec; intro hs; ring_simplify; rewrite IHm; trivial.
Qed.

Lemma mynumbering6 : forall (m:fmap),
  (ne m = nd m - nl0 m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; ring_simplify; rewrite IHm; trivial.
induction d; simpl; (apply IHm || ring_simplify; rewrite IHm; trivial).
Qed.

Lemma mynumbering7 : forall (m:fmap),
  (nv m = nd m - nl1 m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; ring_simplify; rewrite IHm; trivial.
induction d; simpl; (apply IHm || ring_simplify; rewrite IHm; trivial).
Qed.

(* ========================== *)

Lemma eq_nhs_nhp : forall (m:fmap),
  (nhbs m + nhrs m = nhbp m + nhrp m)%Z.
Proof.
induction m.
simpl; trivial.
simpl; assumption.
induction d; simpl.
elim succ_dec; elim pred_dec; intros hp hs; ring_simplify; rewrite IHm; trivial.
elim succ_dec; elim pred_dec; intros hp hs; ring_simplify; rewrite IHm; trivial.
Qed.

Lemma Zeven_nh : forall (m:fmap), Zeven (nh m).
Proof.
intro m.
rewrite mynumbering2.
replace (nhbs m + nhbp m + nhrs m + nhrp m)%Z with (nhbs m + nhrs m + nhbp m + nhrp m)%Z.
rewrite eq_nhs_nhp.
replace (nhbp m + nhrp m + nhbp m + nhrp m)%Z with (2 * (nhbp m + nhrp m))%Z.
apply Zeven_2n.
ring_simplify; trivial.
ring_simplify; trivial.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

(* %%%%% JFD %%%%% *)

Lemma black_dart_dec : forall m z,
     inv_hmap m ->
         {black_dart m z} + {~black_dart m z}.
Proof.
  unfold black_dart. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma black_dart_not_others : forall m z,
     inv_half m -> exd m z -> black_dart m z ->
       ~blue_dart m z /\ ~red_dart m z /\
       ~half_blue_succ m z /\ ~half_blue_pred m z /\
       ~half_red_succ m z /\ ~half_red_pred m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

Lemma blue_dart_dec : forall m z,
     inv_hmap m ->
         {blue_dart m z} + {~blue_dart m z}.
Proof.
  unfold blue_dart. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma blue_dart_not_others : forall m z,
     inv_half m -> exd m z -> blue_dart m z ->
       ~black_dart m z /\ ~red_dart m z /\
       ~half_blue_succ m z /\ ~half_blue_pred m z /\
       ~half_red_succ m z /\ ~half_red_pred m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

Lemma red_dart_dec : forall m z,
     inv_hmap m ->
         {red_dart m z} + {~red_dart m z}.
Proof.
  unfold red_dart. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma red_dart_not_others : forall m z,
     inv_half m -> exd m z -> red_dart m z ->
       ~black_dart m z /\ ~blue_dart m z /\
       ~half_blue_succ m z /\ ~half_blue_pred m z /\
       ~half_red_succ m z /\ ~half_red_pred m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.


Lemma half_red_succ_dec : forall m z,
     inv_hmap m ->
         {half_red_succ m z} + {~half_red_succ m z}.
Proof.
  unfold half_red_succ. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma half_red_succ_not_others : forall m z,
     inv_half m -> exd m z -> half_red_succ m z ->
       ~black_dart m z /\ ~blue_dart m z /\ ~red_dart m z /\
       ~half_blue_succ m z /\ ~half_blue_pred m z /\
       ~half_red_pred m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

Lemma half_red_pred_dec : forall m z,
     inv_hmap m ->
         {half_red_pred m z} + {~half_red_pred m z}.
Proof.
  unfold half_red_pred. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma half_red_pred_not_others : forall m z,
     inv_half m -> exd m z -> half_red_pred m z ->
       ~black_dart m z /\ ~blue_dart m z /\ ~red_dart m z /\
       ~half_blue_succ m z /\ ~half_blue_pred m z /\
       ~half_red_succ m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

Lemma half_blue_succ_dec : forall m z,
     inv_hmap m ->
         {half_blue_succ m z} + {~half_blue_succ m z}.
Proof.
  unfold half_blue_succ. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma half_blue_succ_not_others : forall m z,
     inv_half m -> exd m z -> half_blue_succ m z ->
       ~black_dart m z /\ ~blue_dart m z /\ ~red_dart m z /\
       ~half_red_succ m z /\ ~half_blue_pred m z /\
       ~half_red_pred m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

Lemma half_blue_pred_dec : forall m z,
     inv_hmap m ->
         {half_blue_pred m z} + {~half_blue_pred m z}.
Proof.
  unfold half_blue_pred. intros.
  generalize (succ_dec m zero z).
  generalize (succ_dec m one z). 
  generalize (pred_dec m zero z).
  generalize (pred_dec m one z).
  tauto.
Qed.

Lemma half_blue_pred_not_others : forall m z,
     inv_half m -> exd m z -> half_blue_pred m z ->
       ~black_dart m z /\ ~blue_dart m z /\ ~red_dart m z /\
       ~half_blue_succ m z /\ ~half_red_pred m z /\
       ~half_red_succ m z.
Proof.
   unfold inv_half,black_dart,blue_dart,red_dart,
     half_blue_succ,half_blue_pred,half_red_succ,half_red_pred.
   intros. 
   generalize (H z H0). clear H. 
   tauto.
Qed.

(*===============================
                          TRANSITIONS
===============================*)

(* DOES EXIST IN CB ? *)

Lemma not_exd_black: forall m d t p,
   inv_hmap m -> ~exd m d ->
      black_dart (I m d t p) d.
Proof.
 unfold black_dart. unfold succ, pred. simpl. intros.
 fold (succ m one d). fold (succ m zero d).
 fold (pred m one d). fold (pred m zero d).
 split. intro. elim H0. apply succ_exd with zero. tauto. tauto.
 split. intro. elim H0. apply succ_exd with one. tauto. tauto.
 split. intro. elim H0. apply pred_exd with zero. tauto. tauto.
 intro. elim H0. apply pred_exd with one. tauto. tauto.
Qed.

Lemma black_to_hbs: forall m x y,
   inv_hmap (L m zero x y) -> black_dart m x ->
      half_blue_succ (L m zero x y) x.
Proof. 
  unfold half_blue_succ, black_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x x). split. 
   apply exd_not_nil with m. tauto. tauto. 
   elim (eq_dart_dec y x). intro.  
   rewrite a0 in H5,H7. 
   assert (~succ m zero x). unfold succ. tauto. 
   assert (~pred m zero x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m zero x H1 H3 H0 H9). tauto. 
   tauto. tauto.
Qed.

Lemma black_to_hrp: forall m x y,
   inv_hmap (L m zero x y) -> black_dart m y ->
      half_red_pred (L m zero x y) y.
Proof.
   unfold half_red_pred, black_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x y). intro. 
   rewrite <-a in H5,H7. 
   assert (~succ m zero x). unfold succ. tauto. 
   assert (~pred m zero x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m zero x H1 H3 H0 H9). tauto. 
   elim (eq_dart_dec y y). 
   split. tauto. split. tauto. 
   split. apply exd_not_nil with m. tauto. tauto. tauto.
   tauto. 
Qed.

Lemma black_to_hrs: forall m x y,
   inv_hmap (L m one x y) -> black_dart m x ->
      half_red_succ (L m one x y) x.
Proof. 
  unfold half_red_succ, black_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x x). split. tauto. 
   split. apply exd_not_nil with m. tauto. tauto. 
   split. tauto. 
   elim (eq_dart_dec y x). intro.  
   rewrite a0 in H5,H7. 
   assert (~succ m one x). unfold succ. tauto. 
   assert (~pred m one x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m one x H1 H3 H0 H9). tauto. 
   tauto. tauto.
Qed.

Lemma black_to_hbp: forall m x y,
   inv_hmap (L m one x y) -> black_dart m y ->
      half_blue_pred (L m one x y) y.
Proof.
   unfold half_blue_pred, black_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x y). intro. 
   rewrite <-a in H5,H7. 
   assert (~succ m one x). unfold succ. tauto. 
   assert (~pred m one x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m one x H1 H3 H0 H9). tauto. 
   elim (eq_dart_dec y y). 
   split. tauto. split. tauto.
   split. tauto. 
   apply exd_not_nil with m. tauto. tauto. tauto.
Qed.

Lemma hbp_to_blue: forall m x y,
   inv_hmap (L m zero x y) -> half_blue_pred m x ->
      blue_dart (L m zero x y) x.
Proof. 
  unfold half_blue_pred, blue_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x x). split. 
   apply exd_not_nil with m. tauto. tauto. 
   elim (eq_dart_dec y x). intro.  
   rewrite a0 in H5,H7. 
   assert (~succ m zero x). unfold succ. tauto. 
   assert (~pred m zero x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m zero x H1 H3 H0 H9). tauto. 
   tauto. tauto.
Qed.

Lemma hrs_to_red: forall m x y,
   inv_hmap (L m zero x y) -> half_red_succ m y ->
     red_dart (L m zero x y) y.
Proof. 
  unfold half_red_succ, red_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x y). intro. 
   rewrite a in H4,H7. 
   assert (~succ m zero y). unfold succ. tauto. 
   assert (~pred m zero y). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m zero y H1 H2 H0 H9). tauto. 
   elim (eq_dart_dec y y). 
   split. tauto. split. tauto. 
   split.   apply exd_not_nil with m. tauto. tauto. tauto. 
   tauto.
Qed.
 
Lemma hbs_to_blue: forall m x y,
   inv_hmap (L m one x y) -> half_blue_succ m y ->
      blue_dart (L m one x y) y.
Proof.
   unfold half_blue_succ, blue_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x y). intro. 
   rewrite a in H4,H7. 
   assert (~succ m one y). unfold succ. tauto. 
   assert (~pred m one y). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m one y H1 H2 H0 H9). tauto. 
   elim (eq_dart_dec y y). 
   split. tauto. split. tauto.
   split. tauto. 
   apply exd_not_nil with m. tauto. tauto. tauto.
Qed.

Lemma hrp_to_red: forall m x y,
   inv_hmap (L m one x y) ->half_red_pred m x ->
      red_dart (L m one x y) x.
Proof. 
  unfold half_red_pred, red_dart. 
   simpl. unfold prec_L. unfold succ, pred. 
   intros. decompose [and] H. clear H. 
   decompose [and] H0. clear H0.
   simpl. elim (eq_dart_dec x x). split. tauto. 
   split. apply exd_not_nil with m. tauto. tauto. 
   split. tauto. 
   elim (eq_dart_dec y x). intro.  
   rewrite a0 in H5,H7. 
   assert (~succ m one x). unfold succ. tauto. 
   assert (~pred m one x). unfold pred. tauto. 
   generalize (fixpt_cA_cA_1 m one x H1 H3 H0 H9). tauto. 
   tauto. tauto.
Qed.

(*===================================
                inv_half on I, L
===================================*)

Lemma inv_half_I_m : forall m x t p, 
  inv_hmap (I m x t p) -> inv_half (I m x t p) -> 
      inv_half m.
Proof.
  unfold inv_half. unfold black_dart, blue_dart, red_dart,
   half_blue_succ, half_blue_pred, half_red_succ, half_red_pred.
  simpl. unfold prec_I. unfold succ, pred. simpl. intros. 
   generalize (H0 d).  
     fold (succ m zero d). fold (succ m one d).
     fold (pred m zero d). fold (pred m one d). tauto. 
Qed.

Lemma inv_half_L_m : forall m k x y, 
  inv_hmap (L m k x y) -> inv_half (L m k x y) -> 
     inv_half m.
Proof.
  unfold inv_half. unfold black_dart, blue_dart, red_dart,
   half_blue_succ, half_blue_pred, half_red_succ, half_red_pred.
  simpl. unfold prec_L. unfold succ, pred. simpl. 
  induction k. 
  elim (eq_dim_dec zero one). intro. inversion a. 
  elim (eq_dim_dec zero zero). intros.   
   decompose [and] H. clear H. 
    generalize (H0 d H1). clear H0. 
 elim (eq_dart_dec x d). intro. rewrite <-a0. 
   elim (eq_dart_dec y d). intro.  
    rewrite a1 in H6,H8. rewrite <-a0 in H6,H8. 
    assert (~succ m zero x). unfold succ. tauto. 
    assert (~pred m zero x). unfold pred. tauto. 
      generalize (fixpt_cA_cA_1 m zero x H2 H4 H H0). tauto. 
   intro. elim (eq_dart_dec y x).  intro. 
    rewrite a1 in H6,H8. 
   assert (~succ m zero x). unfold succ. tauto. 
    assert (~pred m zero x). unfold pred. tauto. 
      generalize (fixpt_cA_cA_1 m zero x H2 H4 H H0). tauto. 
   intro. 
   assert (y <> nil). apply exd_not_nil with m. tauto. tauto. 
    fold (succ m zero x). fold (succ m one x).
        fold (pred m zero x). fold (pred m one x).
    intro. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. 
     elim (eq_dart_dec y d). intros a1 b1. 
       rewrite <-a1.  
    assert (x <> nil). apply exd_not_nil with m. tauto. tauto. 
    fold (succ m zero y). fold (succ m one y).
        fold (pred m zero y). fold (pred m one y). 
     intro. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. 
    intros b1 b2.   
     fold (succ m zero d). fold (succ m one d).
        fold (pred m zero d). fold (pred m one d). 
     intro H0. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. tauto.
  elim (eq_dim_dec one zero). intro. inversion a. 
  elim (eq_dim_dec one one). intros.   
   decompose [and] H. clear H. 
    generalize (H0 d H1). clear H0. 
 elim (eq_dart_dec x d). intro. rewrite <-a0. 
   elim (eq_dart_dec y x). intro.  
    rewrite a1 in H6,H8. 
    assert (~succ m one x). unfold succ. tauto. 
    assert (~pred m one x). unfold pred. tauto. 
      generalize (fixpt_cA_cA_1 m one x H2 H4 H H0). tauto. 
   intro.
   assert (y <> nil). apply exd_not_nil with m. tauto. tauto. 
    fold (succ m zero x). fold (succ m zero x).
        fold (pred m zero x). fold (pred m one x).
    intro. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. 
  intro. 
   elim (eq_dart_dec y d). intro.  rewrite <-a0. 
     fold (succ m zero y). fold (succ m one y).
        fold (pred m zero y). fold (pred m one y). 
      assert (x <> nil). apply exd_not_nil with m. tauto. tauto. 
   intro. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. 
   intro. 
     fold (succ m zero d). fold (succ m one d).
        fold (pred m zero d). fold (pred m one d). 
     intro H0. elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0.
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      elim H0. clear H0. tauto. clear H0. intro H0. 
      tauto. tauto.
Qed.

Definition dim_opp(k:dim):dim:=
 match k with zero => one | one => zero end.

Lemma L_not_succ_pred_L: forall m k x y,
  let m1 := L m k x y in
    inv_hmap m1 -> inv_half m1 -> 
   x <> y /\
     succ m1 k x /\ pred m1 k y /\ 
      ~ pred m1 k x /\ ~ succ m1 k y /\
        ~ succ m1 (dim_opp k) x /\ ~ pred m1 (dim_opp k) y.
Proof.
  intros. generalize H H0.
  unfold m1,inv_hmap,inv_half. fold inv_hmap. 
   unfold prec_L. fold m1. intros. 
  decompose [and] H1. clear H1. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  assert (x<>y). intro. rewrite <-H8 in H7,H9. 
  generalize (fixpt_cA_cA_1 m k x). tauto. 
  assert (succ m1 k x). unfold m1,succ. simpl. 
       elim eq_dart_dec. intro. 
       elim eq_dim_dec. intro.
       apply exd_not_nil with m. tauto. tauto. tauto. tauto. 
  assert (pred m1 k y). unfold m1,pred. simpl. 
       elim eq_dart_dec. intro. 
       elim eq_dim_dec. intro.
       apply exd_not_nil with m. tauto. tauto. tauto. tauto. 
  assert (~ pred m1 k x). 
       assert (exd m1 x). unfold m1. simpl. tauto. 
       generalize (H2 x H12).  
       unfold black_dart, blue_dart,red_dart,
       half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ.
       induction k. tauto. tauto.   
  assert (~ succ m1 k y). 
       assert (exd m1 y). unfold m1. simpl. tauto. 
       generalize (H2 y H13).  
       unfold black_dart, blue_dart,red_dart,
       half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ.
       induction k. tauto. tauto.   
  assert (~ succ m1 (dim_opp k) x). 
        assert (exd m1 x). unfold m1. simpl. tauto. 
        generalize (H2 x H14). intro. fold m1 in H15. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H15. 
        induction k. simpl. tauto. tauto. 
  assert (~ pred m1 (dim_opp k) y). 
        assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (H2 y H15). intro. fold m1 in H16. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H16. 
        induction k. simpl. tauto. tauto. 
  tauto. 
Qed.
  
Lemma L_not_succ_pred: forall m k x y,
  let m1 := L m k x y in
    inv_hmap m1 -> inv_half m1 ->
     x <> y /\ ~ pred m k x /\ ~ succ m k y /\
        ~ succ m (dim_opp k) x /\ ~ pred m (dim_opp k) y.
Proof.
  intros. generalize H H0.
  unfold m1,inv_hmap,inv_half. fold inv_hmap. 
   unfold prec_L. fold m1. intros. 
  decompose [and] H1. clear H1. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred_L m k x y H H0). fold m1. intros.
  assert (~ pred m k x). intro. 
     assert (pred m1 k x). unfold m1,pred. simpl. 
      elim eq_dim_dec. intros. 
       elim eq_dart_dec. intro. rewrite a0 in H8. tauto. 
        intro. fold (pred m k x). tauto. tauto. 
     tauto. 
  assert (~ succ m k y). intro. 
     assert (succ m1 k y). unfold m1,succ. simpl. 
      elim eq_dim_dec. intros. 
       elim eq_dart_dec. intro. rewrite a0 in H8. tauto. 
        intro. fold (succ m k y). tauto. tauto. 
     tauto. 
  assert (~ succ m (dim_opp k) x). 
     intro. assert (succ m1 (dim_opp k) x). 
     unfold m1,succ. simpl. 
      elim eq_dim_dec. intros. 
       induction k. simpl in a. inversion a.
       elim eq_dart_dec. intro.
      apply exd_not_nil with m. tauto. tauto. tauto.  
       fold (succ m (dim_opp k) x). tauto. tauto. 
   assert (~ pred m (dim_opp k) y). 
     intro. assert (pred m1 (dim_opp k) y). 
     unfold m1,pred. simpl. 
      elim eq_dim_dec. intros. 
       induction k. simpl in a. inversion a.
       elim eq_dart_dec. intro.
      apply exd_not_nil with m. tauto. tauto. tauto.  
       fold (pred m (dim_opp k) y). tauto. tauto. 
 tauto.
Qed.

(* ======================= 
    NUMBERING, CONTRIBUTION OF JFD
 ========================*)

(* 7-UPLE OF SETS *)

Inductive set7 : Set :=
  cset7 : set->set->set->set->set->set->set->set7.

Definition setn(S:set7):set:=
  match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s1
  end.

Definition setb(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s6
   end.

Definition setr(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s7
   end.

Definition sethbs(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s2
   end.

Definition sethbp(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s3
   end.

Definition sethrs(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s4
   end.

Definition sethrp(S:set7):set:=
   match S with
    cset7 s1 s2 s3 s4 s5 s6 s7 => s5
   end.

Inductive nat7:Set:=
   cnat7 : nat->nat->nat->nat->nat->nat->nat->nat7.

(* IN THE 7 SETS OF s, REMOVING AND ADDING 
  OF x AND y AMONG THE CASES *)

Fixpoint DsL_aux(m:fmap)(s:set7):set7:=
   match m with
     V => s
   | I m0 x t p => DsL_aux m0 s
   | L m0 zero x y => 
       let s0 := DsL_aux m0 s in 
       match s0 with (cset7 sn0 shbs0 shbp0 shrs0 shrp0 sb0 sr0) =>
        let s1:= 
            if pred_dec m0 one x
            then cset7 sn0 shbs0 (Ds shbp0 x) shrs0 shrp0 (Is sb0 x) sr0
            else cset7 (Ds sn0 x) (Is shbs0 x) shbp0 shrs0 shrp0 sb0 sr0 in
        match s1 with (cset7 sn1 shbs1 shbp1 shrs1 shrp1 sb1 sr1) =>
            if succ_dec m0 one y 
            then cset7 sn1 shbs1 shbp1 (Ds shrs1 y) shrp1 sb1 (Is sr1 y)
            else cset7 (Ds sn1 y) shbs1 shbp1 shrs1 (Is shrp1 y) sb1 sr1
        end
       end
   | L m0 one x y => 
       let s0 := DsL_aux m0 s in
       match s0 with (cset7 sn0 shbs0 shbp0 shrs0 shrp0 sb0 sr0) =>
        let s1 :=
            if pred_dec m0 zero x
            then cset7 sn0 shbs0 shbp0 shrs0 (Ds shrp0 x) sb0 (Is sr0 x)
            else cset7 (Ds sn0 x) shbs0 shbp0 (Is shrs0 x) shrp0 sb0 sr0 in
          match s1 with (cset7 sn1 shbs1 shbp1 shrs1 shrp1 sb1 sr1) =>
            if succ_dec m0 zero y 
            then cset7 sn1 (Ds shbs1 y) shbp1 shrs1 shrp1 (Is sb1 y) sr1
            else cset7 (Ds sn1 y) shbs1 (Is shbp1 y) shrs1 shrp1 sb1 sr1
          end
       end
  end.

(* INITIALISATION *)

Definition s7init(s:set):set7 := cset7 s Vs Vs Vs Vs Vs Vs.

(* GLOBAL FUNCTION : *)

Definition DsL(m:fmap) := DsL_aux m (s7init (fmap_to_set m)).

(* AUXILIARY RESULTS: *)

Lemma DsL_aux_Is: forall m s z,
  inv_hmap m -> ~exds s z -> incls (fmap_to_set m) s ->
    match (DsL_aux m (s7init s)) with cset7 sn shbs shbp shrs shrp sb sr =>
       DsL_aux m (s7init (Is s z)) = 
           cset7 (Is sn z) shbs shbp shrs shrp sb sr
    end.
Proof.
  induction m. simpl. unfold s7init. intros. tauto. 
  simpl. unfold prec_I. intros. inversion H1. simpl in H2. 
   apply IHm. tauto. tauto. apply exds2. intro. 
     generalize (H2 z0). tauto. 
  simpl. unfold prec_L. rename d0 into x, d1 into y. intros. 
  assert ( inv_hmap m). tauto. 
  inversion H1. simpl in H3. 
  induction d. 
    generalize (IHm s z H2 H0 H1). 
    elim pred_dec. 
       elim succ_dec. 
         elim (DsL_aux m (s7init s)). intros. rewrite H4. tauto. 
       induction (DsL_aux m (s7init s)). intros. rewrite H4. 
        simpl. elim (eq_dart_dec z y). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a0 in H. tauto. tauto. 
       elim succ_dec. 
       elim (DsL_aux m (s7init s)). intros. rewrite H4. 
          simpl. elim (eq_dart_dec z x). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a0 in H. tauto. tauto. 
     elim (DsL_aux m (s7init s)). intros. rewrite H4. 
          simpl. elim (eq_dart_dec z x). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <- a in H. tauto. 
         simpl. elim (eq_dart_dec z y). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a in H. tauto. tauto.
   generalize (IHm s z H2 H0 H1). 
    elim pred_dec.
      elim succ_dec. 
         elim (DsL_aux m (s7init s)). intros. rewrite H4. tauto. 
         elim (DsL_aux m (s7init s)). intros.  rewrite H4. 
         simpl. elim (eq_dart_dec z y). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a0 in H. tauto. tauto. 
      elim succ_dec.  
         elim (DsL_aux m (s7init s)). intros. rewrite H4. 
         simpl. elim (eq_dart_dec z x). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a0 in H. tauto. tauto. 
            simpl. generalize (IHm s z H2 H0 H1). 
              elim (DsL_aux m (s7init s)). intros. rewrite H5. 
        simpl. elim (eq_dart_dec z x). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <- a in H. tauto. 
         simpl. elim (eq_dart_dec z y). intro. 
         generalize (exd_exds m z). intros. generalize (H3 z). intros. 
           rewrite <-a in H. tauto. tauto.
Qed.

(* 3 PROPRERTIES OF setn : *)

(* OK: *)

Lemma incls_setn_DsL_aux: forall m s,
  inv_hmap m -> incls (fmap_to_set m) s ->
      incls (setn (DsL_aux m (s7init s))) s. 
Proof.
  induction m. simpl.
  intros; apply exds2; intros; tauto.
   simpl. unfold prec_I. intros.
    inversion H0. simpl in H1. 
    assert (inv_hmap m). tauto. 
    assert (incls (fmap_to_set m) s). apply exds2. intro. 
       generalize (H1 z). tauto. 
    apply (IHm s H2 H3). 
   simpl. unfold prec_L. intros. 
   rename d0 into x, d1 into y. 
   assert (inv_hmap m). tauto. 
   generalize (IHm s H1 H0). intro. clear IHm. 
   generalize H2. clear H2. 
   induction d. 
    elim pred_dec. 
       elim succ_dec. 
          elim (DsL_aux m (s7init s)). simpl. tauto. 
       elim (DsL_aux m (s7init s)). simpl. intros. 
          apply exds2. intros. inversion H2. generalize (H4 z). intros. 
          apply H5. apply exds_Ds_exds with y. tauto. 
    elim succ_dec.  
          elim (DsL_aux m (s7init s)). simpl. intros.  apply exds2. intros. 
          inversion H2. generalize (H4 z). intros. 
          apply H5. apply exds_Ds_exds with x. tauto. 
         elim (DsL_aux m (s7init s)). simpl. intros. 
            apply exds2. intros.  inversion H2. generalize (H4 z). intros. 
              apply H5. apply exds_Ds_exds with x.
                 apply exds_Ds_exds with y. tauto. 
   elim pred_dec.  
      elim succ_dec.  
          elim (DsL_aux m (s7init s)). simpl. intros. tauto. 
          elim (DsL_aux m (s7init s)). simpl. intros.   
             apply exds2. intros.   inversion H2. generalize (H4 z). intros. 
              apply H5. apply exds_Ds_exds with y. tauto. 
      elim succ_dec. simpl. intros.  generalize H2. clear H2. 
             elim (DsL_aux m (s7init s)). simpl. intros. 
               inversion H2. apply exds2. intros. generalize (H3 z). intros. 
          apply H5. apply exds_Ds_exds with x. tauto. 
     elim (DsL_aux m (s7init s)). simpl. intros. 
             apply exds2. intros.  inversion H2. generalize (H4 z). intros. 
              apply H5. apply exds_Ds_exds with x.
                 apply exds_Ds_exds with y. tauto. 
Qed.

(* OK: *)

Lemma exds_setn_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> exds s z -> black_dart m z -> 
       exds (setn (DsL_aux m (s7init s))) z. 
Proof.
  induction m. unfold black_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold black_dart,succ,pred. simpl. intros s z IM IH Ez.
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold (black_dart m z). intro. 
   assert (inv_half m). apply inv_half_I_m with d t p. simpl. unfold prec_I. 
    apply IM. apply IH. apply IHm. tauto. tauto. tauto. tauto. 
  unfold black_dart,pred,succ. intros. simpl in H. unfold prec_L,succ, pred in H.
     simpl in H,H2. rename d0 into x,d1 into y.
  generalize H2. clear H2. 
  decompose [and] H. clear H. 
  assert (inv_half m). apply (inv_half_L_m m d x y). 
    simpl. unfold prec_L. tauto. tauto. 
 induction d. 
  elim (eq_dim_dec zero one). intro. inversion a. 
  elim (eq_dim_dec zero zero). intros. 
    clear a b. generalize H7. clear H7. simpl. 
  elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  elim (eq_dart_dec y z). intro. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     intros. assert (black_dart m z). unfold black_dart. tauto. 
     generalize (IHm s z H2 H H1 H9). 
    elim (pred_dec m one x). 
      elim (succ_dec m one y). 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
       induction (DsL_aux m (s7init s)). simpl. intros. 
        generalize (exds_Ds s0 y z). tauto. 
      elim (succ_dec m one y). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
         generalize (exds_Ds s0 x z). tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
         generalize (exds_Ds (Ds s0 x) y z). 
           generalize (exds_Ds s0 x z). tauto. tauto. 
elim (eq_dim_dec one zero). intro. inversion a. 
  elim (eq_dim_dec one one). intros. 
    clear a b. generalize H7. clear H7. simpl. 
  elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  elim (eq_dart_dec y z). intro. rewrite <-a. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     intros. assert (black_dart m z). unfold black_dart. tauto.   
     generalize (IHm s z H2 H H1 H9). 
   elim (pred_dec m zero x). 
       elim (succ_dec m zero y). 
       induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
          generalize (exds_Ds s0 y z). tauto. 
    elim (succ_dec m zero y). 
       induction (DsL_aux m (s7init s)). simpl. intros. 
          generalize (exds_Ds s0 x z). tauto. 
       induction (DsL_aux m (s7init s)). simpl. intros. 
  generalize (exds_Ds (Ds s0 x) y z). 
           generalize (exds_Ds s0 x z). tauto. tauto. 
Qed.

(* RECIPROCAL, OK *)

Lemma exds_setn_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m ->  
      exds (setn (DsL_aux m (s7init s))) z -> black_dart m z. 
Proof.
  induction m. unfold black_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold black_dart,succ,pred. simpl. intros s z IM IH Ez.
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold (black_dart m z). 
   assert (inv_half m). apply inv_half_I_m with d t p. simpl. unfold prec_I. 
    apply IM. apply IH. apply IHm with s. tauto. tauto. tauto. 
  unfold black_dart,pred,succ. intros. simpl in H. unfold prec_L,succ, pred in H.
     simpl in H,H1. rename d0 into x,d1 into y.
  generalize H1. clear H1. 
  decompose [and] H. clear H. 
  assert (inv_half m). apply (inv_half_L_m m d x y). 
    simpl. unfold prec_L. tauto. tauto.  
induction d. simpl.
 elim (eq_dart_dec x z). intro.  rewrite <-a. 
  elim pred_dec.
     elim succ_dec. intros Sy Px. 
        generalize (IHm s x H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. tauto. 
     intros Sy Px. 
        generalize (IHm s x H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. 
        assert (exds s0 x). apply exds_Ds_exds with y.  tauto. 
        tauto. 
    elim succ_dec. intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        absurd (exds (Ds s0 x) x). apply not_exds_Ds. tauto. 
    intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros.
         absurd (exds (Ds (Ds s0 x) y) x). 
         assert (exds (Ds s0 x) x). apply exds_Ds_exds with y. tauto. 
          absurd (exds (Ds s0 x) x). apply not_exds_Ds. tauto. tauto. 
  elim (eq_dart_dec y z). intros a b. rewrite <-a. 
 elim pred_dec.
     elim succ_dec. intros Sy Px. 
        generalize (IHm s y H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. tauto. 
     intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        absurd (exds (Ds s0 y) y). apply not_exds_Ds. tauto. 
    elim succ_dec. intros Sy Px. 
        generalize (IHm s y H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        assert (exds s0 y). 
        apply exds_Ds_exds with x. tauto. 
        unfold black_dart in H6. tauto. 
    intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros.
         absurd (exds (Ds (Ds s0 x) y) y). 
         apply not_exds_Ds. tauto. 
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold (black_dart m z). 
   intros. apply IHm with s. tauto. tauto. 
   generalize H6. clear H6. 
    elim pred_dec.
     elim succ_dec. intros Sy Px. 
   induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     induction (DsL_aux m (s7init s)). simpl. intros. 
      apply exds_Ds_exds with y. tauto.
     elim succ_dec. intros Sy Px. 
      induction (DsL_aux m (s7init s)). simpl. intros. 
       apply exds_Ds_exds with x. tauto.
      induction (DsL_aux m (s7init s)). simpl. intros. 
       apply exds_Ds_exds with x. apply exds_Ds_exds with y. 
      tauto.
(* CASE one : *)
simpl.
 elim (eq_dart_dec x z). intro.  rewrite <-a. 
  elim pred_dec.
     elim succ_dec. intros Sy Px. 
        generalize (IHm s x H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. tauto. 
     intros Sy Px. 
        generalize (IHm s x H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. 
        assert (exds s0 x). apply exds_Ds_exds with y.  tauto. 
        tauto. 
    elim succ_dec. intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        absurd (exds (Ds s0 x) x). apply not_exds_Ds. tauto. 
    intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros.
         absurd (exds (Ds (Ds s0 x) y) x). 
         assert (exds (Ds s0 x) x). apply exds_Ds_exds with y. tauto. 
          absurd (exds (Ds s0 x) x). apply not_exds_Ds. tauto. tauto. 
  elim (eq_dart_dec y z). intros a b. rewrite <-a. 
 elim pred_dec.
     elim succ_dec. intros Sy Px. 
        generalize (IHm s y H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        unfold black_dart in H6. tauto. 
     intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        absurd (exds (Ds s0 y) y). apply not_exds_Ds. tauto. 
    elim succ_dec. intros Sy Px. 
        generalize (IHm s y H1 H). 
        induction (DsL_aux m (s7init s)). simpl. intros. 
        assert (exds s0 y). 
        apply exds_Ds_exds with x. tauto. 
        unfold black_dart in H6. tauto. 
    intros Sy Px. 
        induction (DsL_aux m (s7init s)). simpl. intros.
         absurd (exds (Ds (Ds s0 x) y) y). 
         apply not_exds_Ds. tauto. 
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold (black_dart m z). 
   intros. apply IHm with s. tauto. tauto. 
   generalize H6. clear H6. 
    elim pred_dec.
     elim succ_dec. intros Sy Px. 
   induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     induction (DsL_aux m (s7init s)). simpl. intros. 
      apply exds_Ds_exds with y. tauto.
     elim succ_dec. intros Sy Px. 
      induction (DsL_aux m (s7init s)). simpl. intros. 
       apply exds_Ds_exds with x. tauto.
      induction (DsL_aux m (s7init s)). simpl. intros. 
       apply exds_Ds_exds with x. apply exds_Ds_exds with y. 
      tauto.
Qed.

(* 2 PROPERTIES OF setb : *)

Lemma exds_setb_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> blue_dart m z -> 
       exds (setb (DsL_aux m (s7init s))) z. 
Proof.
  induction m. unfold blue_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold blue_dart, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold blue_dart. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold blue_dart. tauto. 
  unfold blue_dart, pred,succ. intros. 
  simpl in H1. generalize H1. clear H1. 
  rename d0 into x,d1 into y.
  simpl in H. unfold prec_L in H. decompose [and] H. clear H. 
  assert (inv_half m). apply (inv_half_L_m m d x y). 
    simpl. unfold prec_L. tauto. tauto. 
 induction d. 
  elim (eq_dim_dec zero one). intro. inversion a. 
  elim (eq_dim_dec zero zero). intros. 
    clear a b. generalize H6. clear H6. simpl. 
  elim (eq_dart_dec x z). intro. rewrite <-a. 
  elim (eq_dart_dec y x). intro. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
 intros. 
    elim (pred_dec m one x). intro. 
      elim (succ_dec m one y). 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto.
    tauto. 
   elim  (eq_dart_dec y z). 
  assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto.
  fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). intros. 
   assert (blue_dart m z). unfold blue_dart. tauto. 
     generalize (IHm s z H1 H H8). 
   elim (pred_dec m one x). 
     elim (succ_dec m one y). 
      induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     elim (succ_dec m one y). 
      induction (DsL_aux m (s7init s)). simpl. intros. tauto.    
     induction (DsL_aux m (s7init s)). simpl. intros. tauto. tauto. 
elim (eq_dim_dec one zero). intro. inversion a. 
  elim (eq_dim_dec one one). intros. 
    clear a b. generalize H6. clear H6. simpl. 
  elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  elim (eq_dart_dec y z). intro. rewrite <-a. 
     fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y).
    intros. 
      elim (pred_dec m zero x). 
       elim (succ_dec m zero y). intros. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim (succ_dec m zero y). 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     intros. assert (blue_dart m z). unfold blue_dart. tauto.   
     generalize (IHm s z H1 H H8). 
   elim (pred_dec m zero x). 
       elim (succ_dec m zero y). 
       induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim (succ_dec m zero y). 
       induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
Qed.

(* RECIPROCAL, OK:  *)

Lemma exds_setb_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (setb (DsL_aux m (s7init s))) z -> 
          blue_dart m z . 
Proof.
induction m. unfold black_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold blue_dart,succ,pred. simpl. intros s z IM IH Ez.
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold (blue_dart m z). 
   assert (inv_half m). apply inv_half_I_m with d t p. simpl. unfold prec_I. 
    apply IM. apply IH. apply IHm with s. tauto. tauto. tauto. 
  unfold blue_dart,pred,succ. intros. simpl in H. unfold prec_L,succ, pred in H.
     simpl in H,H1. rename d0 into x,d1 into y.
  generalize H1. clear H1. 
  decompose [and] H. clear H. 
  assert (inv_half m). apply (inv_half_L_m m d x y). 
    simpl. unfold prec_L. tauto. tauto.  
    fold (succ m d x) in H4. fold (pred m d y) in H5.
  assert (inv_hmap (L m d x y)). simpl. unfold prec_L. tauto. rename H6 into IHL.
induction d. simpl.
  elim pred_dec.
    elim succ_dec. intros Sy Px.  
        elim (eq_dart_dec x y). intro. rewrite <-a in Sy,H5. 
       unfold inv_half in H. generalize (H x H3). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H6. 
       tauto. intro. 
       generalize (IHm s z H1 H).  
        elim (eq_dart_dec x z). intro. rewrite <-a. 
        elim (eq_dart_dec y x). intro. symmetry in a0. tauto. intro. clear b0. 
        fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
        generalize (inv_half_pred_one m x H1 H Px). 
         intro. assert (half_blue_pred m x). unfold blue_dart in H6. tauto. 
         clear H6. unfold  half_blue_pred in H8. intros. split.
            apply exd_not_nil with m. tauto. tauto. tauto. intro. 
        elim (eq_dart_dec y z). intro. rewrite <-a. 
        induction (DsL_aux m (s7init s)). simpl. intros. unfold blue_dart in H6. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. unfold blue_dart in H6. 
        fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). tauto. 
     intros Sy Px.  
        elim (eq_dart_dec x z). intro. rewrite <-a. 
           elim (eq_dart_dec y x). intro. 
              rewrite a0 in H5,H7. 
           generalize (fixpt_cA_cA_1 m zero x). tauto. intro. 
            fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
            generalize (inv_half_pred_one m x H1 H Px). 
         intro. assert (half_blue_pred m x). unfold blue_dart in H6. tauto. 
         clear H6. unfold  half_blue_pred in H8. intros. split.
            apply exd_not_nil with m. tauto. tauto. tauto. intro. 
          elim (eq_dart_dec y z). intro. rewrite <-a. 
              generalize (IHm s y H1 H). 
             induction (DsL_aux m (s7init s)). simpl. intros. rewrite <-a in b. 
             unfold blue_dart in H6. 
             assert (succ (L m zero x y) zero y). 
            unfold succ. simpl. 
             elim eq_dart_dec. tauto. fold (succ m zero y). tauto.
             assert (pred (L m zero x y) zero y). unfold pred. simpl.
                    elim eq_dart_dec. intro. 
                   apply exd_not_nil with m. tauto. tauto. tauto. 
             set(m1:=L m zero x y). fold m1 in H9,H10,H0,IHL. 
             generalize (inv_half_pred_zero m1 y IHL H0 H10). 
             unfold red_dart,half_red_pred. tauto. 
             generalize (IHm s z H1 H). 
             induction (DsL_aux m (s7init s)). simpl. intros. 
             fold (succ m zero z) (succ m one z) 
                 (pred m zero z) (pred m one z). 
             fold (blue_dart m z). tauto. 
   elim succ_dec. intros Sy Px.  
        elim (eq_dart_dec x z). intro. rewrite <-a. 
           elim (eq_dart_dec y x). intro. 
              rewrite a0 in H7,Sy,H5. 
               generalize (fixpt_cA_cA_1 m zero x). tauto. intro. 
              generalize (IHm s x H1 H). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. tauto. intro. 
           elim (eq_dart_dec y z). intro. rewrite <-a. 
                generalize (IHm s y H1 H). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. tauto. intro. 
           generalize (IHm s z H1 H). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. 
            fold (succ m zero z) (succ m one z) 
                (pred m zero z) (pred m one z). tauto. 
     intro. intro. 
          elim (eq_dart_dec x z). intro. rewrite <-a. 
             elim (eq_dart_dec y x). intro. 
                rewrite a0 in H7,b,H5. 
               generalize (fixpt_cA_cA_1 m zero x). tauto. intro. 
                  generalize (IHm s x H1 H). 
               induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. tauto. intro. 
              elim (eq_dart_dec y z). intro. rewrite <-a. 
                generalize (IHm s y H1 H). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. 
           assert (succ (L m zero x y) zero y). 
            unfold succ. simpl. 
             elim eq_dart_dec. rewrite a. tauto. fold (succ m zero y). tauto.
             assert (pred (L m zero x y) zero y). unfold pred. simpl.
                    elim eq_dart_dec. intro. 
                   apply exd_not_nil with m. tauto. tauto. tauto. 
             set(m1:=L m zero x y). fold m1 in H9,H10,H0,IHL. 
             generalize (inv_half_pred_zero m1 y IHL H0 H10). 
             unfold red_dart,half_red_pred. tauto. 
            generalize (IHm s z H1 H). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  unfold blue_dart in H6. 
            fold (succ m zero z) (succ m one z) 
                (pred m zero z) (pred m one z). tauto. 
(* CASE one : A FAIRE...*)
simpl.
  set(m1:=L m one x y). 
  generalize IHL. simpl. unfold prec_L. intro. 
  decompose [and] IHL0. clear IHL0. 
  assert (x<>y). intro. rewrite <-H12 in H5,H7. 
  generalize (fixpt_cA_cA_1 m one x). tauto. 
  assert (succ m1 one x). unfold m1,succ. simpl. 
       elim eq_dart_dec. intro. 
       apply exd_not_nil with m. tauto. tauto. tauto. 
  assert (pred m1 one y). unfold m1,pred. simpl. 
       elim eq_dart_dec. intro. 
       apply exd_not_nil with m. tauto. tauto. tauto. 
  assert (~pred m one x). intro. 
       assert (pred m1 one x). unfold m1,pred. simpl. 
       elim eq_dart_dec. intro. symmetry in a. tauto.
         fold (pred m one x). tauto. 
        unfold inv_half in H0. generalize (H0 x H9). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H18. 
        tauto. 
   assert (~succ m one y). intro. 
       assert (succ m1 one y). unfold m1,succ. simpl. 
       elim eq_dart_dec. tauto. 
         fold (succ m one y). tauto. 
        unfold inv_half in H0. generalize (H0 y H8). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H19. 
        tauto. 
  assert (~pred m zero y). intro. 
        assert (pred m1 zero y). unfold m1,pred. simpl. 
         fold (pred m zero y). tauto. 
        unfold inv_half in H0. generalize (H0 y H8). intro. fold m1 in H20. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H20. 
        tauto. 
   assert (~succ m zero x). intro. 
       assert (succ m1 zero x). unfold m1,succ. simpl. 
         fold (succ m zero x). tauto. 
        unfold inv_half in H0. generalize (H0 x H9). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H21. 
        tauto. 
  generalize (IHm s z H6 H). 
  elim pred_dec. intro.
    elim succ_dec. intro.
        elim (eq_dart_dec x z). intro. rewrite <-a1. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
           elim H21; intro. symmetry in H22. tauto. 
           unfold blue_dart in H20. tauto. 
        elim (eq_dart_dec y z). intro. rewrite <-a1. 
           fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
           split. tauto. split. tauto. split. tauto. apply exd_not_nil with m. tauto. tauto. 
         fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
            induction (DsL_aux m (s7init s)). simpl. intros. 
            elim H21. intro. rewrite <-H22 in b0. tauto. 
            unfold blue_dart in H20. tauto. 
      intro. 
         elim (eq_dart_dec x z). intro. rewrite <-a0. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
           unfold blue_dart in H20. tauto. 
        elim (eq_dart_dec y z). intro. rewrite <-a0. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
            unfold blue_dart in H20. tauto. 
        fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
            induction (DsL_aux m (s7init s)). simpl. intros. 
            unfold blue_dart in H20. tauto. 
     elim succ_dec. intro.
        elim (eq_dart_dec x z). intro. rewrite <-a0. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
           elim H21; intro. symmetry in H22. tauto. 
           unfold blue_dart in H20. tauto. 
        elim (eq_dart_dec y z). intro. rewrite <-a0. 
           fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
           split. tauto. split. tauto. split. tauto. apply exd_not_nil with m. tauto. tauto. 
         fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
            induction (DsL_aux m (s7init s)). simpl. intros. 
            elim H21. intro. rewrite <-H22 in b0. tauto. 
            unfold blue_dart in H20. tauto.  
     intro. intro.
          elim (eq_dart_dec x z). intro. rewrite <-a. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
           unfold blue_dart in H20. tauto. 
        elim (eq_dart_dec y z). intro. rewrite <-a. 
            induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold blue_dart in H20. tauto.
        fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
            induction (DsL_aux m (s7init s)). simpl. intros. 
            unfold blue_dart in H20. tauto. 
Qed. 
         
(* 2 PROPERTIES OF setr: *)
           
(* OK: *)

Lemma exds_setr_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m ->red_dart m z -> 
       exds (setr (DsL_aux m (s7init s))) z. 
Proof. 
  induction m. unfold red_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold red_dart, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold red_dart. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold red_dart. tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  generalize (L_not_succ_pred_L m k x y  H H0). fold m1. intro. 
  unfold red_dart,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  induction k. simpl in H8,H10. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    elim (eq_dart_dec y z). intro. rewrite <-a. 
     fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    generalize (IHm s z H3 H2). unfold  red_dart. 
    elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    tauto. simpl in H8,H10.
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    elim (eq_dart_dec y z). intro. rewrite <-a. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
       generalize (IHm s z H3 H2). unfold  red_dart. 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
Qed.
     
(* RECIPROCAL, OK: *)

Lemma exds_setr_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (setr (DsL_aux m (s7init s))) z -> 
          red_dart m z . 
Proof.
 induction m. unfold red_dart, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold red_dart, succ,pred. simpl. intros.
    fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).  
    fold (red_dart m z). apply IHm with s. tauto. 
    apply (inv_half_I_m m d t p).  simpl. unfold prec_I. tauto. tauto. 
    tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold red_dart,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  unfold m1. unfold red_dart,succ,pred. simpl. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    generalize (IHm s x H3 H2). 
       elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
          elim H10. intro. symmetry in H11. tauto. 
          clear H6. intro. unfold red_dart in H1. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
          unfold red_dart in H1. tauto. 
       elim succ_dec.  
          induction (DsL_aux m (s7init s)). simpl. intros. 
            elim H10. intro. symmetry in H11. tauto. 
          clear H6. intro. unfold red_dart in H1. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
          unfold red_dart in H1. tauto. 
     elim (eq_dart_dec y z). intro. rewrite <-a. 
   fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y).  
     generalize (IHm s y H3 H2). 
       elim succ_dec. intros. 
         split. tauto. split. tauto. 
           split. apply exd_not_nil with m. tauto. tauto. tauto.
      elim pred_dec. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
          unfold red_dart in H1. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
          unfold red_dart in H1. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
      generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. 
             elim H10. tauto. 
              unfold red_dart in H1. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
                unfold red_dart in H1. tauto.  
      elim succ_dec.      
        induction (DsL_aux m (s7init s)). simpl. intros. 
                unfold red_dart in H1. tauto.
        induction (DsL_aux m (s7init s)). simpl. intros. 
                unfold red_dart in H1. tauto.
  tauto.
(* CASE one : *)
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. simpl in H8. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x).
        elim pred_dec. split. tauto. split. apply exd_not_nil with m. tauto. tauto. 
          split. tauto. tauto. 
       elim succ_dec.   
          generalize (IHm s x H3 H2). 
           induction (DsL_aux m (s7init s)). simpl. intros. 
            unfold red_dart in H1. 
            assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
          generalize (IHm s x H3 H2). 
          induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold red_dart in H1. 
            assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
        elim (eq_dart_dec). intro. rewrite <-a. 
         elim pred_dec. 
            elim succ_dec.  
              generalize (IHm s y H3 H2). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
               unfold red_dart in H1. tauto. 
              generalize (IHm s y H3 H2). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
               unfold red_dart in H1. tauto. 
              elim succ_dec.  
              generalize (IHm s y H3 H2). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
               unfold red_dart in H1. tauto. 
              generalize (IHm s y H3 H2). 
              induction (DsL_aux m (s7init s)). simpl. intros. 
               unfold red_dart in H1. tauto. 
           fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
           fold (red_dart m z). 
              intros. apply IHm with s.  tauto. tauto. 
              generalize H1. clear H1. 
                 induction (DsL_aux m (s7init s)). simpl. 
              elim pred_dec. 
                  elim succ_dec. simpl. tauto. 
                  simpl. tauto. 
              elim succ_dec. simpl. tauto. 
                  simpl. tauto. 
  tauto.
Qed.

(* 2 PROPERTIES OF sethbs: *)

(* OK: *)

Lemma exds_sethbs_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> half_blue_succ m z -> 
       exds (sethbs (DsL_aux m (s7init s))) z. 
Proof. 
  induction m. unfold half_blue_succ, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_blue_succ, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold half_blue_succ. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold half_blue_succ. tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_blue_succ,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim (eq_dart_dec y z). intro. rewrite a in H8. tauto.  
    generalize (IHm s z H3 H2). unfold   half_blue_succ. 
    elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    tauto. simpl in H8.
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
      elim (eq_dart_dec y z). intro. rewrite <-a. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     fold (half_blue_succ m z). 
       generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
               simpl in H1. generalize (exds_Ds s1 y z). tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros.   
           simpl in H1. generalize (exds_Ds s1 y z). tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
Qed.

(* RECIPROCAL, OK: *)

Lemma exds_sethbs_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (sethbs (DsL_aux m (s7init s))) z -> 
          half_blue_succ m z . 
Proof.
 induction m. unfold  half_blue_succ, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_blue_succ, succ,pred. simpl. intros.
    fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).  
    fold (half_blue_succ m z). apply IHm with s. tauto. 
    apply (inv_half_I_m m d t p).  simpl. unfold prec_I. tauto. tauto. 
    tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_blue_succ,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  unfold m1. unfold half_blue_succ,succ,pred. simpl. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x).  
    unfold half_blue_succ in IHm. 
    generalize (IHm s x H3 H2). 
       elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
           assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto.  
           assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto.  
        elim eq_dart_dec. intro. rewrite <-a. 
          fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y).  
      unfold half_blue_succ in IHm.   
      generalize (IHm s y H3 H2). 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
      unfold half_blue_succ in IHm. generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.      
        induction (DsL_aux m (s7init s)). simpl. intros. tauto.
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
(* CASE one : *)
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. simpl in H8. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
    unfold half_blue_succ in IHm. generalize (IHm s x H3 H2). 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
              generalize (exds_Ds s1 y x). tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
              generalize (exds_Ds s1 y x). tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
      elim (eq_dart_dec y z). intro. rewrite <-a. 
     fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
     unfold half_blue_succ in IHm. generalize (IHm s y H3 H2).  
       elim pred_dec. 
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
          absurd (exds (Ds s1 y) y). apply not_exds_Ds. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
          absurd (exds (Ds s1 y) y). apply not_exds_Ds. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
       fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
           fold ( half_blue_succ m z). 
              intros. apply IHm with s.  tauto. tauto. 
              generalize H1. clear H1. 
                 induction (DsL_aux m (s7init s)). simpl. 
              elim pred_dec. 
                  elim succ_dec. simpl. intros. apply exds_Ds_exds with y. tauto. 
                  simpl. tauto. 
              elim succ_dec. simpl.  intros. apply exds_Ds_exds with y. tauto. tauto. 
 tauto.
Qed.
 
(* 2 PROPERTIES OF sethbp : *)

(* OK: *)

Lemma exds_sethbp_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> half_blue_pred m z -> 
       exds (sethbp (DsL_aux m (s7init s))) z. 
Proof. 
  induction m. unfold half_blue_pred, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_blue_pred, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold half_blue_pred. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold half_blue_pred. tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_blue_pred,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
      elim pred_dec. 
        elim succ_dec. intros. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim (eq_dart_dec y z). intro. rewrite a in H8. tauto.  
    generalize (IHm s z H3 H2). unfold half_blue_pred. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
    generalize H8. clear H8.
    elim pred_dec. 
        elim succ_dec. 
           induction (DsL_aux m (s7init s)). simpl. intros. 
             generalize (exds_Ds s2 x z).  tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. 
             generalize (exds_Ds s2 x z).  tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    tauto. simpl in H8.
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
      elim (eq_dart_dec y z). intro. rewrite <-a. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto.  
   fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
    generalize (IHm s y H3 H2). unfold  half_blue_pred. 
      elim pred_dec. 
        elim succ_dec. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.     
         induction (DsL_aux m (s7init s)). simpl. intros.  tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros.  tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     fold (half_blue_pred m z). 
       generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto.
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.    
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
   induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
Qed.

(* RECIPROCAL, OK: *)

Lemma exds_sethbp_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (sethbp (DsL_aux m (s7init s))) z -> 
          half_blue_pred m z. 
Proof.
induction m. unfold half_blue_pred, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_blue_pred,succ,pred. simpl. 
  intros s z IM IH Ez.
   fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
   fold ( half_blue_pred m z). 
   assert (inv_half m). apply inv_half_I_m with d t p. simpl. unfold prec_I. 
    apply IM. apply IH. apply IHm with s. tauto. tauto. tauto. 
  unfold half_blue_pred,pred,succ. intros. simpl in H. 
    unfold prec_L,succ, pred in H.
     simpl in H,H1. rename d0 into x,d1 into y.
  generalize H1. clear H1. 
  decompose [and] H. clear H. 
  assert (inv_half m). apply (inv_half_L_m m d x y). 
    simpl. unfold prec_L. tauto. tauto.  
    fold (succ m d x) in H4. fold (pred m d y) in H5.
  assert (inv_hmap (L m d x y)). simpl. unfold prec_L. tauto. rename H6 into IHL.
  elim (eq_dart_dec x y). intro. rewrite <-a in H7,H5. 
 generalize (fixpt_cA_cA_1 m d x).  tauto. intro. 
induction d. simpl. 
  elim pred_dec.
    elim succ_dec. intros Sy Px.  
      elim (eq_dart_dec x z). intro. rewrite <-a. 
      induction (DsL_aux m (s7init s)). simpl. intros. 
      absurd (exds (Ds s2 x) x). apply not_exds_Ds. tauto. 
      elim (eq_dart_dec y z). intro. rewrite <-a. intro. 
      generalize (IHm s y H1 H). 
      induction (DsL_aux m (s7init s)). simpl. intros. 
      unfold half_blue_pred in H6. 
     assert (exds s2 y). apply exds_Ds_exds with x. tauto. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
      fold ( half_blue_pred m z). 
       generalize (IHm s z H1 H). 
      induction (DsL_aux m (s7init s)). simpl. intros. 
      assert (exds s2 z). apply exds_Ds_exds with x. tauto. tauto. 
    intros Sy Px. 
       elim (eq_dart_dec x z). intro. rewrite <-a. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
          absurd (exds (Ds s2 x) x). apply not_exds_Ds. tauto. 
        elim (eq_dart_dec y z). intro. rewrite <-a. intro. 
          generalize (IHm s y H1 H). 
         induction (DsL_aux m (s7init s)). simpl. intros. 
           assert (exds s2 y). apply exds_Ds_exds with x. tauto. 
            unfold half_blue_pred in H6. 
          assert (pred (L m zero x y) one y). 
            unfold pred. simpl. fold (pred m one y). tauto.
          assert (pred (L m zero x y) zero y). 
            unfold pred. simpl. elim eq_dart_dec. intro. 
             apply exd_not_nil with m. tauto. tauto. tauto. 
         set(m1:=L m zero x y). fold m1 in H11,H10,H0,IHL. 
              generalize (inv_half_pred_zero m1 y IHL H0 H11). 
                unfold red_dart,half_red_pred. tauto. 
        fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
             fold ( half_blue_pred m z). 
             generalize (IHm s z H1 H). 
             induction (DsL_aux m (s7init s)). simpl. intros. 
               assert (exds s2 z). apply exds_Ds_exds with x. tauto. 
        tauto. 
     elim succ_dec. intros Sy Px.  
         elim (eq_dart_dec x z). intro. rewrite <-a. 
           generalize (IHm s x H1 H). 
          induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold half_blue_pred in H6. tauto. 
         elim (eq_dart_dec y z). intro. rewrite <-a. 
           generalize (IHm s y H1 H). 
          induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold half_blue_pred in H6. tauto. 
          generalize (IHm s z H1 H). 
          fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
             fold ( half_blue_pred m z). 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           elim (eq_dart_dec x z). intro. rewrite <-a. 
           intros Sy Px. 
          generalize (IHm s x H1 H). 
          induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold half_blue_pred in H6. tauto. 
          elim (eq_dart_dec y z). intro. rewrite <-a. 
           generalize (IHm s y H1 H). 
          induction (DsL_aux m (s7init s)). simpl. intros. 
             unfold half_blue_pred in H6.  
          assert (pred (L m zero x y) one y). 
            unfold pred. simpl. fold (pred m one y). tauto.
          assert (pred (L m zero x y) zero y). 
            unfold pred. simpl. elim eq_dart_dec. intro. 
             apply exd_not_nil with m. tauto. tauto. tauto. 
         set(m1:=L m zero x y). fold m1 in H9,H10,H0,IHL. 
              generalize (inv_half_pred_zero m1 y IHL H0 H10). 
                unfold red_dart,half_red_pred. tauto. 
       fold (succ m zero z) (succ m one z) 
                 (pred m zero z) (pred m one z). 
             fold (half_blue_pred m z). 
             generalize (IHm s z H1 H). 
             induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  (* CASE one: *)
  set(m1:=(L m one x y)). intros. fold m1 in IHL. 
  generalize (L_not_succ_pred m one x y  IHL H0). simpl. intro.  
  generalize H6. clear H6.
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
    unfold half_blue_pred in IHm. generalize (IHm s x H1 H). 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
      elim (eq_dart_dec y z). intro. rewrite <-a. 
     fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
     unfold half_blue_pred in IHm. generalize (IHm s y H1 H).  
       elim pred_dec. 
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
          induction (DsL_aux m (s7init s)). simpl. intros. 
              assert (x <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
              assert (x <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
       fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
           fold ( half_blue_pred m z). 
              intros. apply IHm with s.  tauto. tauto. 
              generalize H6. clear H6. 
                 induction (DsL_aux m (s7init s)). simpl. 
              elim pred_dec. 
                  elim succ_dec. simpl. intros. tauto. 
                  simpl. tauto. 
              elim succ_dec. simpl.  intros. apply exds_Ds_exds with y. 
                    generalize (exds_Ds s2 y z). tauto. simpl. tauto. 
Qed.

(* 2 PROPERTIES OF sethrs : *)

(* OK: *)

Lemma exds_sethrs_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> half_red_succ m z -> 
       exds (sethrs (DsL_aux m (s7init s))) z. 
Proof. 
 induction m. unfold half_red_succ, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_red_succ, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold half_red_succ. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold half_red_succ. tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_red_succ,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    elim (eq_dart_dec y z). intro. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    generalize (IHm s z H3 H2). unfold half_red_succ. 
    elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros.  
             generalize (exds_Ds s3 y z). tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.    
         induction (DsL_aux m (s7init s)). simpl. intros.
             generalize (exds_Ds s3 y z). tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    tauto. simpl in H8.
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    generalize (IHm s y H3 H2). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. 
            unfold half_red_succ in H1. tauto.
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros.   tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
   elim (eq_dart_dec y z). intro. 
     assert (x <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z). 
     fold (half_red_succ m z). 
       generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros.   simpl in H1. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
Qed.

(* RECIPROCAL, OK: *)

Lemma exds_sethrs_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (sethrs (DsL_aux m (s7init s))) z -> 
          half_red_succ m z . 
Proof.
 induction m. unfold  half_red_succ, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_red_succ, succ,pred. simpl. intros.
    fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).  
    fold (half_red_succ m z). apply IHm with s. tauto. 
    apply (inv_half_I_m m d t p).  simpl. unfold prec_I. tauto. tauto. 
    tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_red_succ,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  unfold m1. unfold half_red_succ,succ,pred. simpl. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x).  
    unfold half_red_succ in IHm. 
    generalize (IHm s x H3 H2). 
       elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
             generalize (exds_Ds s3 y x). tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
              induction (DsL_aux m (s7init s)). simpl. intros. 
                  generalize (exds_Ds s3 y x). tauto. 
              induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        elim eq_dart_dec. intro. rewrite <-a. 
      unfold half_red_succ in IHm.   
      generalize (IHm s y H3 H2). 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
              absurd (exds (Ds s3 y) y). apply not_exds_Ds. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros.   
             absurd (exds (Ds s3 y) y). apply not_exds_Ds. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
      unfold half_red_succ in IHm. generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. 
                generalize (exds_Ds s3 y z). tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.      
        induction (DsL_aux m (s7init s)). simpl. intros.   
                generalize (exds_Ds s3 y z). tauto. 
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
(* CASE one : *)
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. simpl in H8. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
     fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x). 
    unfold half_red_succ in IHm. generalize (IHm s x H3 H2). 
    assert (y <> nil). apply exd_not_nil with m. tauto. tauto. 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
      elim (eq_dart_dec y z). intro. rewrite <-a. 
     fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y). 
     unfold half_red_succ in IHm. generalize (IHm s y H3 H2).  
       elim pred_dec. 
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
       fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
           fold ( half_red_succ m z). 
              intros. apply IHm with s.  tauto. tauto. 
              generalize H1. clear H1. 
                 induction (DsL_aux m (s7init s)). simpl. 
              elim pred_dec. 
                  elim succ_dec. simpl. intros. apply exds_Ds_exds with y. 
                    generalize (exds_Ds s3 y z). tauto. 
                  simpl. tauto. 
              elim succ_dec. simpl. tauto. 
                  simpl. tauto.  
 tauto.
Qed.

(* 2 PROPERTIES OF sethrp: *)

(* OK: *)

Lemma exds_sethrp_DsL_aux: forall m s z,
   inv_hmap m -> inv_half m -> half_red_pred m z -> 
       exds (sethrp (DsL_aux m (s7init s))) z. 
Proof. 
 induction m. unfold half_red_pred, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_red_pred, succ,pred. simpl. intros. 
    apply IHm. tauto. unfold half_red_pred. unfold succ,pred. 
    apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. 
    unfold half_red_pred. tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_red_pred,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    elim (eq_dart_dec y z). intro. rewrite <-a.
 fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y).
    generalize (IHm s y H3 H2). unfold half_red_pred. 
    elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. tauto.  
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.    
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
      generalize (IHm s z H3 H2). unfold half_red_pred. 
  elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. tauto.  
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.    
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
    tauto. simpl in H8.
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
       assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    elim eq_dart_dec. 
       assert (x <> nil). apply exd_not_nil with m. tauto. tauto. tauto. 
    generalize (IHm s z H3 H2). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. 
             generalize (exds_Ds s4 x z). 
            unfold half_red_pred in H1. tauto.
        induction (DsL_aux m (s7init s)). simpl. intros. 
              generalize (exds_Ds s4 x z). 
            unfold half_red_pred in H1. tauto. 
      elim succ_dec. intros.     
         induction (DsL_aux m (s7init s)). simpl. intros.  
             simpl in H1. unfold half_red_pred in H1.  tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. 
              unfold half_red_pred in H1.   tauto. 
tauto. 
Qed.

(* RECIPROCAL,  OK : *)

Lemma exds_sethrp_DsL_aux_rcp: forall m s z,
   inv_hmap m -> inv_half m -> 
       exds (sethrp (DsL_aux m (s7init s))) z -> 
          half_red_pred m z . 
Proof.
 induction m. unfold  half_red_pred, pred,succ. simpl. tauto. 
  simpl. unfold prec_I. unfold half_red_pred, succ,pred. simpl. intros.
    fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).  
    fold (half_red_pred m z). apply IHm with s. tauto. 
    apply (inv_half_I_m m d t p).  simpl. unfold prec_I. tauto. tauto. 
    tauto. 
  rename d into k,d0 into x,d1 into y.
  set(m1:=(L m k x y)). intros. 
  generalize H. unfold m1. simpl. unfold prec_L. intros. 
    decompose [and] H2. clear H2. 
  generalize (inv_half_L_m m k x y H H0). intro. 
  generalize (L_not_succ_pred m k x y  H H0). intro.  
  unfold half_red_pred,succ,pred,m1 in H1. simpl in H1. 
  generalize H1. clear H1. 
  unfold m1. unfold half_red_pred,succ,pred. simpl. 
  induction k. simpl in H8. 
    elim (eq_dim_dec zero one). intro. inversion a. 
      elim (eq_dim_dec zero zero). 
       intro. intro. clear a b. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    fold (succ m zero x) (succ m one x) (pred m zero x) (pred m one x).  
    unfold half_red_pred in IHm. 
    generalize (IHm s x H3 H2). 
       elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
              induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
              induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
        elim eq_dart_dec. intro. rewrite <-a. 
   fold (succ m zero y) (succ m one y) (pred m zero y) (pred m one y).  
      unfold half_red_pred in IHm.   
      generalize (IHm s y H3 H2). 
     assert (x<>nil). apply exd_not_nil with m. tauto. tauto. 
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
         elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.   
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
     fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
      unfold half_red_succ in IHm. generalize (IHm s z H3 H2). 
     fold (half_red_pred m z). 
      elim pred_dec. 
        elim succ_dec.  
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
           induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
      elim succ_dec.      
        induction (DsL_aux m (s7init s)). simpl. intros. tauto.  
        induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
  tauto.
(* CASE one : *)
  elim (eq_dim_dec one zero). intro. inversion a. 
      elim (eq_dim_dec one one). 
       intro. intro. clear a b. simpl in H8. 
    elim (eq_dart_dec x z). intro. rewrite <-a. 
    elim (eq_dart_dec y x). intro. symmetry in a0. tauto. 
    unfold half_red_succ in IHm. generalize (IHm s x H3 H2). 
    unfold half_red_pred.
        elim pred_dec. 
        elim succ_dec.
          induction (DsL_aux m (s7init s)). simpl. intros. 
             absurd (exds (Ds s4 x) x). apply not_exds_Ds. tauto. 
         induction (DsL_aux m (s7init s)). simpl. intros. 
             absurd (exds (Ds s4 x) x). apply not_exds_Ds. tauto. 
         elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
      elim (eq_dart_dec y z). intro. rewrite <-a. 
     unfold half_red_pred in IHm. generalize (IHm s y H3 H2).  
       elim pred_dec. 
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
              generalize (exds_Ds s4 x y). tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. 
              generalize (exds_Ds s4 x y). tauto.
        elim succ_dec. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto. 
          induction (DsL_aux m (s7init s)). simpl. intros. tauto.
       fold (succ m zero z) (succ m one z) (pred m zero z) (pred m one z).
           fold (half_red_pred m z). 
              intros. apply IHm with s.  tauto. tauto. 
              generalize H1. clear H1. 
                 induction (DsL_aux m (s7init s)). simpl. 
              elim pred_dec. 
                  elim succ_dec. simpl. intros. apply exds_Ds_exds with x. tauto. 
                  simpl. intros. apply exds_Ds_exds with x. tauto. 
              elim succ_dec. simpl. tauto. 
                  simpl. tauto.  
 tauto.
Qed.  

(*=======================================
                            MAIN  THEOREM
========================================*)

(* OK: *)

Lemma card_number : forall m,  inv_hmap m -> inv_half m ->
 match (DsL m) with cset7 sn shbs shbp shrs shrp sb sr =>
  Z_of_nat (card sn) = nn m /\ 
    Z_of_nat (card shbs) = nhbs m /\ Z_of_nat (card shbp) = nhbp m /\  
      Z_of_nat (card shrs) = nhrs m /\ Z_of_nat (card shrp) = nhrp m /\
        Z_of_nat (card sb) = nb m /\ Z_of_nat (card sr) = nr m
  end.
Proof.
  unfold DsL. intros. rename H0 into IH. 
  induction m. simpl. tauto. 
    simpl in H. unfold prec_I in H. 
    assert (incls (fmap_to_set m) (fmap_to_set m)). 
      apply exds2. tauto.
   assert (~exds (fmap_to_set m) d). 
   generalize (exd_exds m d). tauto. 
   assert (inv_hmap m). tauto. 
   generalize (IHm H2). clear IHm. 
   simpl. generalize (incls_setn_DsL_aux m (fmap_to_set m) H2 H0). 
   generalize (DsL_aux_Is m (fmap_to_set m) d H2 H1 H0). 
   induction (DsL_aux m (s7init (fmap_to_set m))). intros. simpl in H4. 
   rewrite H3. simpl. 
   assert (inv_half m).
   apply (inv_half_I_m m d t p). simpl. unfold prec_I; tauto. 
    apply IH.  rename H6 into Ih. 
   elim exds_dec. intro. 
     generalize (exd_exds m d). intros. 
     inversion H4. generalize (H7 d). intro. tauto. intro. 
  assert (Z_of_nat (card s) = nn m). tauto. 
  rewrite inj_S. rewrite H6. 
  split. lia. tauto. 
 simpl. 
   generalize H. intro IM. 
   simpl in H. 
   unfold prec_L in H. 
   rename d0 into x, d1 into y. 
   assert (inv_hmap m). tauto. 
   generalize (IHm H0). clear IHm. 
   assert (inv_half m). 
   apply (inv_half_L_m m d x y). simpl. 
   unfold prec_L. tauto. tauto. 
   elim (eq_dart_dec x y). intro. rewrite <-a in H. 
   generalize (fixpt_cA_cA_1 m d x). tauto. intro Dxy. 
   induction d. 
(* CASE zero: *)
 intro. generalize (H2 H1). clear H2. 
(* CASE 1.1: *)
    elim pred_dec. 
      elim succ_dec. intros a a0.  
         generalize (inv_half_pred_one m x H0 H1 a0). 
         unfold blue_dart. intro. 
         assert (half_blue_pred m x). tauto. clear H2.  
         generalize (exds_sethbp_DsL_aux m (fmap_to_set m) x H0 H1 H3). 
        generalize (inv_half_succ_one m y H0 H1 a). 
         unfold red_dart. intro. 
         assert (half_red_succ m y). tauto. clear H2. 
         generalize (exds_sethrs_DsL_aux m (fmap_to_set m) y H0 H1 H4). 
       intros. 
       assert (exd m x). tauto. 
       generalize (half_blue_pred_not_others m x H1 H7 H3).
       intros. 
       assert (~exds (setb (DsL_aux m (s7init (fmap_to_set m)))) x).
       intro. absurd (blue_dart m x). tauto. 
       apply exds_setb_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
        assert (exd m y). tauto. 
       generalize (half_red_succ_not_others m y H1 H10 H4).
       intros. 
       assert (~exds (setr (DsL_aux m (s7init (fmap_to_set m)))) y).
       intro. absurd (red_dart m y). tauto. 
       apply exds_setr_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
       induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
       simpl in H9,H12,H2,H5.
         split. lia. 
         split. lia. 
         split. rewrite exds_card_Ds. 
         rewrite inj_minus1. simpl. 
           assert (Z_of_nat (card s1) = nhbp m). tauto.
           rewrite H13. tauto. 
           generalize (exds_card_pos s1 x H5). intro. lia. tauto. 
         split. rewrite exds_card_Ds. 
         rewrite inj_minus1. simpl. 
           assert (Z_of_nat (card s2) = nhrs m). tauto.
           rewrite H13. tauto. 
           generalize (exds_card_pos s2 y H2). intro. lia. tauto. 
          split. lia. 
          split. elim exds_dec. intro. tauto. intro. 
            assert (Z_of_nat (card s4) = nb m). tauto. 
            rewrite inj_S. rewrite H13. lia. 
           elim exds_dec. intro. tauto. intro.  
            assert ( Z_of_nat (card s5) = nr m). tauto. 
            rewrite inj_S. rewrite H13. lia. 
(* CASE 1.2: *)
      intros a a0.  
         generalize (inv_half_pred_one m x H0 H1 a0). 
         unfold blue_dart. intro. 
         assert (half_blue_pred m x). tauto. clear H2.  
        assert (exd m x). tauto. 
        generalize (half_blue_pred_not_others m x H1 H2 H3).
        intros. 
       generalize (exds_sethbp_DsL_aux m (fmap_to_set m) x H0 H1 H3). intro. 
        assert (~exds (setb (DsL_aux m (s7init (fmap_to_set m)))) x).
       intro. absurd (blue_dart m x). tauto. 
       apply exds_setb_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
       elim (succ_dec m zero y). intro.
       assert (succ (L m zero x y) zero y). 
        unfold succ. simpl. elim eq_dart_dec. tauto. intro. clear b.
         fold (succ m zero y). tauto. 
       assert (pred (L m zero x y) zero y). unfold pred. simpl. 
         elim eq_dart_dec.  intro. apply exd_not_nil with m. tauto. tauto. tauto. 
         set(m1:=L m zero x y). fold m1 in IH,H8,H9. 
        unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H10). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H11. 
        tauto. intro. 
        elim (pred_dec m one y). intro. 
        assert (pred (L m zero x y) one y). unfold pred. simpl. 
        fold (pred m one y). tauto. 
        set(m1:=L m zero x y). fold m1 in IH,H8. 
        assert (pred (L m zero x y) zero y). unfold pred. simpl. 
         elim eq_dart_dec.  intro. apply exd_not_nil with m. tauto. tauto. tauto. 
        fold m1 in H9. 
        unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H10). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H11. 
        tauto. intro. 
        assert (black_dart m y). unfold black_dart. tauto. 
       assert (exd m y). tauto. 
        generalize (black_dart_not_others m y H1 H9 H8). 
        intros. 
        assert (exds  (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
        generalize (exds_setn_DsL_aux m (fmap_to_set m) y H0 H1 H11 H8). intro. 
        assert (~ half_red_pred m y). tauto. 
        assert (~ exds (sethrp (DsL_aux m (s7init (fmap_to_set m)))) y). 
        intro. elim H13. 
        apply exds_sethrp_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
        induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
        simpl in H6,H7,H12,H14.
        split. rewrite exds_card_Ds. rewrite inj_minus1.
        assert (Z_of_nat (card s) = nn m). tauto. rewrite H15. 
        simpl. lia. generalize (exds_card_pos s y H12). intros. lia. tauto. 
        split. assert ( Z_of_nat (card s0) = nhbs m). tauto. rewrite H15. lia. 
        split. rewrite exds_card_Ds. rewrite inj_minus1. 
        assert (Z_of_nat (card s1) = nhbp m). tauto. rewrite H15. simpl. tauto. 
        generalize (exds_card_pos s1 x H6). intros. lia. tauto. 
        split. assert (Z_of_nat (card s2) = nhrs m). tauto. rewrite H15. lia. 
        split. elim exds_dec. tauto. intros. 
        assert (Z_of_nat (card s3) = nhrp m). tauto. 
        rewrite inj_S. rewrite H15. lia. 
        split. elim exds_dec. tauto. intro. rewrite inj_S.
        assert (Z_of_nat (card s4) = nb m). tauto. rewrite H15. lia. 
        assert (Z_of_nat (card s5) = nr m). tauto. rewrite H15. lia.
 (* CASE 1.3 *)
   elim succ_dec. intros. 
     assert (exd m x). tauto. assert (exd m y). tauto. 
     set(m1:=L m zero x y). fold m1 in IH. 
     assert (succ m1 zero x). unfold succ,m1. simpl.  
       elim eq_dart_dec. intro. apply exd_not_nil with m. tauto. tauto. tauto. 
     elim (succ_dec m one x). intro. 
       assert (succ m1 one x).  unfold succ,m1. simpl.  
       fold (succ m one x). tauto. 
       unfold inv_half in IH. assert (exd m1 x). unfold m1. simpl. tauto. 
        generalize (IH x H7). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H8. 
        tauto. intro. 
     elim (pred_dec m zero x). intro.
       assert (pred m1 zero x). unfold pred,m1. simpl.  
       elim eq_dart_dec. intro. symmetry in a1. tauto. intro. 
       fold (pred m zero x). tauto.  
       unfold inv_half in IH. assert (exd m1 x). unfold m1. simpl. tauto. 
        generalize (IH x H7). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H8. 
        tauto. intro. 
    assert (black_dart m x). unfold black_dart. tauto. 
    assert (pred m1 zero y). unfold pred,m1. simpl.  
       elim eq_dart_dec. intro. apply exd_not_nil with m. tauto. tauto. tauto. 
    assert (succ m1 one y). unfold succ,m1. simpl.  
       fold (succ m one y). tauto. 
    elim (pred_dec m one y). intro. 
       assert (pred m1 one y). unfold pred,m1. simpl.  
        fold (pred m one y). tauto.  
    unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H10). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H11. 
        tauto. intro. 
    elim (succ_dec m zero y). intro. 
       assert (succ m1 zero y). unfold succ,m1. simpl. 
       elim eq_dart_dec. tauto. fold (succ m zero y). tauto. 
     unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H10). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H11. 
        tauto. intro.  
    assert (half_red_succ m y). 
        unfold half_red_succ. tauto. 
    assert (~half_blue_succ m x). 
     generalize (black_dart_not_others m x). tauto. 
    assert (~red_dart m y). 
     generalize (half_red_succ_not_others m y). tauto. 
    assert (exds (fmap_to_set m) x). generalize (exd_exds m x). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) x).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (exds (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
    assert (exds (sethrs (DsL_aux m (s7init (fmap_to_set m)))) y).
      apply  exds_sethrs_DsL_aux. tauto. tauto. tauto.
    assert (~exds (sethbs (DsL_aux m (s7init (fmap_to_set m)))) x).
      intro. elim H10. 
      apply  exds_sethbs_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto.  
    assert (~exds (setr (DsL_aux m (s7init (fmap_to_set m)))) y).
      intro. elim H11. 
      apply  exds_setr_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto.  
    induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
    simpl in H13,H14,H15,H16,H17.
    decompose [and] H2. clear H2. 
    split. rewrite exds_card_Ds. rewrite inj_minus1. simpl. 
       rewrite H18. lia. generalize (exds_card_pos s x H13). intros. lia. tauto. 
    split. elim exds_dec. tauto. intros.  rewrite inj_S. rewrite H20. lia. 
    split. rewrite H19; lia. 
    split. rewrite exds_card_Ds. rewrite inj_minus1. simpl. 
       rewrite H21. tauto. generalize (exds_card_pos s2 y H15). intros. lia. tauto.  
    split. rewrite H22. lia.
    split.  rewrite H23. lia.
    elim exds_dec. tauto. intro. rewrite inj_S. rewrite H25. lia.
(* CASE 1.4: *)
    intros Sy Px. 
     assert (exd m x). tauto. assert (exd m y). tauto. 
     set(m1:=L m zero x y). fold m1 in IH. 
     assert (succ m1 zero x). unfold succ,m1. simpl.  
       elim eq_dart_dec. intro. apply exd_not_nil with m. tauto. tauto. tauto. 
    assert (pred m1 zero y). unfold pred,m1. simpl.  
       elim eq_dart_dec. intro. apply exd_not_nil with m. tauto. tauto. tauto. 
    elim (succ_dec m one x). intro. 
       assert (succ m1 one x).  unfold succ,m1. simpl.  
       fold (succ m one x). tauto. 
       unfold inv_half in IH. assert (exd m1 x). unfold m1. simpl. tauto. 
        generalize (IH x H7). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H8. 
        tauto. intro. 
     elim (pred_dec m zero x). intro.
       assert (pred m1 zero x). unfold pred,m1. simpl.  
       elim eq_dart_dec. intro. symmetry in a0. tauto. intro. clear b0.
       fold (pred m zero x). tauto.  
       unfold inv_half in IH. assert (exd m1 x). unfold m1. simpl. tauto. 
        generalize (IH x H7). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H8. 
        tauto. intro. 
    assert (black_dart m x). unfold black_dart. tauto. 
    elim (succ_dec m one y). intro. 
    assert (succ m1 one y). unfold succ,m1. simpl.  
       fold (succ m one y). tauto. 
        unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H8). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H9. 
        tauto. intro. 
    elim (pred_dec m one y). intro. 
       assert (pred m1 one y). unfold pred,m1. simpl.  
        fold (pred m one y). tauto.  
        unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H8). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H9. 
        tauto. intro. 
    elim (succ_dec m zero y). intro. 
       assert (succ m1 zero y). unfold succ,m1. simpl. 
       elim eq_dart_dec. tauto. fold (succ m zero y). tauto. 
     unfold inv_half in IH. assert (exd m1 y). unfold m1. simpl. tauto. 
        generalize (IH y H8). intro. 
        unfold black_dart, blue_dart,red_dart,
        half_blue_pred, half_blue_succ,  half_red_pred, half_red_succ in H9. 
        tauto. intro.  
    assert (black_dart m y). 
        unfold black_dart. tauto. 
    assert (~half_blue_succ m x). 
     generalize (black_dart_not_others m x). tauto. 
    assert (~half_red_pred m y). 
     generalize (half_red_pred_not_others m y). tauto. 
    assert (exds (fmap_to_set m) x). generalize (exd_exds m x). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) x).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (exds (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) y).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (~exds (sethbs (DsL_aux m (s7init (fmap_to_set m)))) x).
      intro. elim H8. 
      apply  exds_sethbs_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
    assert (~exds (sethrp (DsL_aux m (s7init (fmap_to_set m)))) y).
      intro. elim H9. 
      apply  exds_sethrp_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
    induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
    simpl in H11,H12,H13,H14,H15.
    decompose [and] H16. clear H16. 
    split.
       assert (exds (Ds s x) y). 
       generalize (exds_Ds s x y). tauto. 
        assert (0 < card (Ds s x))%nat.
        apply (exds_card_pos (Ds s x) y). tauto. 
       generalize (exds_card_Ds (Ds s x) y H16). intros.
       generalize (exds_card_Ds s x H11). intros.
       assert (1 <  card s)%nat. lia. 
       rewrite H25,H26. rewrite inj_minus1. 
         rewrite inj_minus1. simpl. rewrite H17. lia. 
       lia. lia. 
     split. elim exds_dec. tauto. intro. 
        rewrite inj_S. rewrite H19. lia. 
     split. rewrite H18. lia. 
     split. rewrite H20. lia. 
     split. elim exds_dec. tauto. intro. 
        rewrite inj_S. rewrite H21. lia. 
     split. rewrite H22. lia. 
     lia. 
(* CASE one : EN COURS *)
  intro. generalize (H2 H1). clear H2. 
(* CASE 2.1: *)
    elim pred_dec. 
      elim succ_dec. intros a a0.  
         generalize (inv_half_pred_zero m x H0 H1 a0). 
         unfold red_dart. intro. 
         assert (half_red_pred m x). tauto. clear H2.  
         generalize (exds_sethrp_DsL_aux m (fmap_to_set m) x H0 H1 H3). 
        generalize (inv_half_succ_zero m y H0 H1 a). 
         unfold blue_dart. intro. 
         assert (half_blue_succ m y). tauto. clear H2. 
         generalize (exds_sethbs_DsL_aux m (fmap_to_set m) y H0 H1 H4). 
       intros. 
       assert (exd m x). tauto. 
       generalize (half_red_pred_not_others m x H1 H7 H3).
       intros. 
       assert (~exds (setr (DsL_aux m (s7init (fmap_to_set m)))) x).
       intro. absurd (red_dart m x). tauto. 
       apply exds_setr_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
        assert (exd m y). tauto. 
       generalize (half_blue_succ_not_others m y H1 H10 H4).
       intros. 
       assert (~exds (setb (DsL_aux m (s7init (fmap_to_set m)))) y).
       intro. absurd (blue_dart m y). tauto. 
       apply exds_setb_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
       induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
       simpl in H9,H12,H2,H5.
         split. lia. 
         split. rewrite exds_card_Ds. 
           rewrite inj_minus1. simpl. 
           assert (Z_of_nat (card s0) = nhbs m). tauto. rewrite H13. 
           lia.   
           generalize (exds_card_pos s0 y H2). intro. lia. tauto. 
         split. assert (Z_of_nat (card s1) = nhbp m). tauto.
           rewrite H13. lia. 
        split. assert (Z_of_nat (card s2) = nhrs m). tauto.
           rewrite H13. lia. 
        split. rewrite exds_card_Ds. 
         rewrite inj_minus1. simpl. 
           assert (Z_of_nat (card s3) = nhrp m). tauto.
           rewrite H13. tauto. 
           generalize (exds_card_pos s3 x H5). intro. lia. tauto. 
        split. elim exds_dec. tauto. intro.  
           rewrite inj_S. 
           assert ( Z_of_nat (card s4) = nb m). tauto. 
            rewrite H13. lia. 
        elim exds_dec. tauto. intro.  
           rewrite inj_S. 
           assert ( Z_of_nat (card s5) = nr m). tauto. 
         rewrite H13. lia. 
(* CASE 2.2: *)
      intros a a0.  
         generalize (inv_half_pred_zero m x H0 H1 a0). 
         unfold red_dart. intro. 
         assert (half_red_pred m x). tauto. clear H2.  
        assert (exd m x). tauto. 
        generalize (half_red_pred_not_others m x H1 H2 H3).
        intros. 
       generalize (exds_sethrp_DsL_aux m (fmap_to_set m) x H0 H1 H3). intro. 
        assert (~exds (setr (DsL_aux m (s7init (fmap_to_set m)))) x).
       intro. absurd (red_dart m x). tauto. 
       apply exds_setr_DsL_aux_rcp with (fmap_to_set m). 
       tauto. tauto. tauto.
       generalize (L_not_succ_pred m one x y IM IH). simpl. intro Lsp. 
       assert (black_dart m y). unfold black_dart. tauto. 
        assert (exd m y). tauto. 
        generalize (black_dart_not_others m y H1 H9 H8). 
        intros. 
        assert (exds  (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
        generalize (exds_setn_DsL_aux m (fmap_to_set m) y H0 H1 H11 H8). intro. 
        assert (~ half_blue_pred m y). tauto. 
        assert (~ exds (sethbp (DsL_aux m (s7init (fmap_to_set m)))) y). 
        intro. elim H13. 
        apply exds_sethbp_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
        induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
        simpl in H6,H7,H12,H14.
        decompose [and] H5. clear H5. 
        split. rewrite exds_card_Ds. rewrite inj_minus1.
        simpl. lia. generalize (exds_card_pos s y H12). intros. lia. tauto. 
        split. rewrite H17. lia. 
        split. elim exds_dec. tauto. intros.  rewrite inj_S. rewrite H16. lia. 
        split. rewrite H18. lia. 
        split.  rewrite exds_card_Ds. rewrite inj_minus1. simpl.
             rewrite H19; lia. 
             generalize (exds_card_pos s3 x H6). intros. lia. tauto. 
        split. rewrite H20. lia. 
        elim exds_dec. tauto. intro. rewrite inj_S. rewrite H22. lia.  
 (* CASE 2.3 *)
   elim succ_dec. intros. 
     assert (exd m x). tauto. assert (exd m y). tauto. 
     set(m1:=L m zero x y). fold m1 in IH,IM. 
     generalize (L_not_succ_pred m one x y IM IH). simpl. intro Lsp. 
     assert (black_dart m x). unfold black_dart. tauto. 
     assert (half_blue_succ m y). unfold half_blue_succ. tauto. 
     assert (~half_red_succ m x). 
     generalize (black_dart_not_others m x). tauto. 
     assert (~blue_dart m y). 
     generalize (half_blue_succ_not_others m y). tauto. 
    assert (exds (fmap_to_set m) x). generalize (exd_exds m x). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) x).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (exds (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
    assert (exds (sethbs (DsL_aux m (s7init (fmap_to_set m)))) y).
      apply  exds_sethbs_DsL_aux. tauto. tauto. tauto.
    assert (~exds (sethrs (DsL_aux m (s7init (fmap_to_set m)))) x).
      intro. elim H7. 
      apply  exds_sethrs_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto.  
    assert (~exds (setb (DsL_aux m (s7init (fmap_to_set m)))) y).
      intro. elim H8. 
      apply  exds_setb_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
    induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
    simpl in H13,H14,H10,H12.
    decompose [and] H2. clear H2. 
    split. rewrite exds_card_Ds. rewrite inj_minus1. simpl. 
       rewrite H15. lia. generalize (exds_card_pos s x H10). intros. lia. tauto. 
    split. rewrite exds_card_Ds. rewrite inj_minus1. simpl. 
       rewrite H17. lia. 
       generalize (exds_card_pos s0 y H12). intros. lia. tauto.
    split. rewrite H16. lia. 
    split. elim exds_dec. tauto. intro. 
       rewrite inj_S. rewrite H18. lia.
    split. rewrite H19. lia. 
    split. elim exds_dec. tauto. intro. 
       rewrite inj_S. rewrite H20. lia.
    rewrite H22. lia.
(* CASE 2.4: *)
    intros Sy Px. 
     assert (exd m x). tauto. assert (exd m y). tauto. 
     set(m1:=L m zero x y). fold m1 in IH. 
       generalize (L_not_succ_pred m one x y IM IH). simpl. intro Lsp. 
     assert (black_dart m x). unfold black_dart. tauto. 
     assert (black_dart m y). unfold black_dart. tauto. 
     assert (~half_red_succ m x). 
       generalize (black_dart_not_others m x). tauto. 
     assert (~half_blue_pred m y). 
       generalize (black_dart_not_others m y). tauto.
     assert (exds (fmap_to_set m) x). generalize (exd_exds m x). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) x).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (exds (fmap_to_set m) y). generalize (exd_exds m y). tauto. 
    assert (exds (setn (DsL_aux m (s7init (fmap_to_set m)))) y).
      apply  exds_setn_DsL_aux. tauto. tauto. tauto. tauto. 
    assert (~exds (sethrs (DsL_aux m (s7init (fmap_to_set m)))) x).
      intro. elim H6. 
      apply  exds_sethrs_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
    assert (~exds (sethbp (DsL_aux m (s7init (fmap_to_set m)))) y).
      intro. elim H7. 
      apply  exds_sethbp_DsL_aux_rcp with (fmap_to_set m). tauto. tauto. tauto. 
    induction (DsL_aux m (s7init (fmap_to_set m))). simpl. intros. 
    simpl in H11,H12,H13,H9.
    decompose [and] H14. clear H14. 
    split.
       assert (exds (Ds s x) y). 
       generalize (exds_Ds s x y). tauto. 
        assert (0 < card (Ds s x))%nat.
        apply (exds_card_pos (Ds s x) y). tauto. 
       generalize (exds_card_Ds (Ds s x) y H14). intros.
       generalize (exds_card_Ds s x H9). intros.
       assert (1 <  card s)%nat. lia. 
       rewrite H23,H24. rewrite inj_minus1. 
         rewrite inj_minus1. simpl. rewrite H15. lia. 
       lia. lia. 
     split. rewrite H17. lia.  
     split. elim exds_dec. tauto. intro. 
        rewrite inj_S. rewrite H16. lia. 
     split. elim exds_dec. tauto. intro. 
        rewrite inj_S. rewrite H18. lia. 
     split. rewrite H19. lia. 
     split. rewrite H20. lia. 
     rewrite H22. lia. 
Qed.

Theorem color_numbers_pos : forall m, inv_hmap m -> inv_half m ->
   (0 <= nn m)%Z /\  (0 <= nhbs m)%Z /\ (0 <= nhbp m)%Z /\ 
     (0 <= nhrs m)%Z /\ (0 <= nhrp m)%Z /\  (0 <= nb m)%Z /\ (0 <= nr m)%Z.
Proof.
  intros. 
  generalize (card_number m H H0). 
  elim (DsL m). intros. lia. 
Qed.

(*===============================================
                     SOME RESULTS ON sets (of darts) 
                             (CAN BE GENERALIZED)
================================================*)

Lemma exds2_le_2_card : forall (s:set)(x y:dart),
  exds s x -> exds s y -> x <> y -> (2 <= card s)%nat.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
 elim (exds_dec s d). intro. 
  elim H. clear H. intro. 
     elim H0. rewrite H. tauto. intro. rewrite H in a. 
     apply IHs with x y. tauto. tauto. tauto. 
  clear H. intro.
     elim H0. intro. rewrite H2 in a. 
     apply IHs with x y. tauto. tauto. tauto. intro. 
   apply IHs with x y. tauto. tauto. tauto. intro. 
 elim H. clear H. intro. rewrite H in H0. 
    assert (exds s y). tauto. 
    generalize (exds_card_pos s y H2). intro. lia. 
 intro.   generalize (exds_card_pos s x H2). intro. lia.
Qed. 

(* and Reciprocals: *)

Lemma card_1_exds : forall (s:set),
     card s = 1%nat -> exists x, exds s x.
Proof.
induction s.
 simpl in |- *. intros. inversion H. 
 simpl in |- *.
 elim (exds_dec s d). intros. 
  split with d.  tauto. 
 intros. split with d. tauto. 
Qed.

Lemma le_2_card_exds2 : forall (s:set),
     (2 <= card s)%nat -> 
         exists x, exists y, exds s x /\ exds s y /\ x <> y.
Proof.
induction s.
 simpl in |- *. intros. inversion H. 
 simpl in |- *.
 elim (exds_dec s d). intros. 
  elim (IHs H). intros. 
    elim H0. intros y Hxy. 
  split with x. split with y. tauto. 
 intros. 
  elim  (eq_nat_dec (card s) 1)%nat. intro. 
  generalize (card_1_exds s a). intro.
  elim H0. intros. 
  split with x. split with d. 
  split. tauto. split. tauto. intro. rewrite <-H2 in b. tauto. 
intro. assert (2 <= card s)%nat. lia. 
  generalize (IHs H0). intro. 
  elim H1. clear H1. intros.
  elim H1. clear H1. intros.
  split with x. split with x0. 
  tauto.
Qed. 

(*========================================
                                   SOME USEFUL RESULTS
=========================================*)

Lemma inv_poly_half: forall  (m:fmap),
   inv_poly m -> inv_half m.
Proof.
  unfold  inv_poly, inv_half. intros.
  generalize (H d). tauto.
Qed.

Lemma inv_poly_I_m :
  forall (m:fmap)(d:dart)(t:tag)(p:point),
  inv_poly (I m d t p) -> inv_poly m.
Proof.
intros m d t p H da Hda.
apply or_intror with (d = da) (exd m da) in Hda.
generalize (H da Hda); clear H Hda.
unfold black_dart, blue_dart, red_dart, succ, pred; simpl; trivial.
Qed.

(* OK: *)

Lemma inv_poly_L0_x_y:  forall m x y, 
  inv_hmap (L m zero x y) -> inv_poly (L m zero x y) -> 
      half_blue_pred m x /\ half_red_succ m y.
Proof.
intros m x y Im Ip. generalize Im Ip. 
simpl. unfold inv_poly,prec_L.
unfold black_dart,blue_dart,red_dart,half_blue_pred,half_red_succ.
unfold succ,pred. simpl. intros. 
 assert (exd m x). tauto.
 assert (exd m y). tauto. rename H into Ex, H0 into Ey. 
elim (eq_dart_dec x y). intro. rewrite <-a in Im0. 
   generalize (fixpt_cA_cA_1 m zero x). tauto. intro Dxy. 
generalize (Ip0 x Ex). 
assert (inv_half (L m zero x y)). 
apply inv_poly_half. tauto. 
generalize (L_not_succ_pred m zero x y Im H). 
unfold succ,pred. simpl. 
elim eq_dart_dec. 
elim eq_dart_dec. intro. symmetry in a. tauto. 
intros b a. clear a b. intros. 
assert (y <> nil). 
apply exd_not_nil with m. tauto. tauto. 
assert 
(~ A m one x <> nil /\ ~ A_1 m zero x <> nil /\ A_1 m one x <> nil). 
tauto. clear H1.
generalize (Ip0 y Ey). 
elim eq_dart_dec. 
elim eq_dart_dec. tauto. 
intros b a. clear a b. intros. tauto. 
elim eq_dart_dec. intros a b. clear a b. 
assert (x <> nil). apply exd_not_nil with m. tauto. tauto. intro. 
assert ( ~ A m zero y <> nil /\
     A m one y <> nil /\ x <> nil /\ ~ A_1 m one y <> nil). tauto. clear H4. 
tauto. 
tauto. tauto.
Qed.

Lemma inv_poly_L0:  forall m x y z, 
   inv_hmap (L m zero x y) ->  inv_poly (L m zero x y) -> 
     x <> z -> y <> z -> 
          black_dart m z \/ blue_dart m z \/  red_dart m z.
Proof.
intros m x y z Im Ip. generalize Im Ip. 
simpl. unfold inv_poly,prec_L.
unfold black_dart,blue_dart,red_dart.
unfold succ,pred. simpl. intros. 
 assert (exd m x). tauto.
 assert (exd m y). tauto. rename H into Ex, H0 into Ey. 
elim (eq_dart_dec x y). intro. rewrite <-a in Im0. 
   generalize (fixpt_cA_cA_1 m zero x). tauto. intro Dxy. 
elim (exd_dec m z). intro Ez.
generalize (Ip0 z Ez). 
elim eq_dart_dec. tauto. 
elim eq_dart_dec. tauto. intros. 
generalize H. clear H. 
 fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
   fold (black_dart m z) (blue_dart m z) (red_dart m z). tauto. 
intro. left. 
   fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
split. intro. elim b. apply succ_exd with zero. tauto. tauto. 
split. intro. elim b. apply succ_exd with one. tauto. tauto. 
split. intro. elim b. apply pred_exd with zero. tauto. tauto. 
intro. elim b. apply pred_exd with one. tauto. tauto. 
Qed.

Lemma inv_poly_L1_x_y:  forall m x y, 
  inv_hmap (L m one x y) -> inv_poly (L m one x y) -> 
      half_red_pred m x /\ half_blue_succ m y.
Proof.
intros m x y Im Ip. generalize Im Ip. 
simpl. unfold inv_poly,prec_L.
unfold black_dart,blue_dart,red_dart,half_red_pred,half_blue_succ.
unfold succ,pred. simpl. intros. 
 assert (exd m x). tauto.
 assert (exd m y). tauto. rename H into Ex, H0 into Ey. 
elim (eq_dart_dec x y). intro. rewrite <-a in Im0. 
   generalize (fixpt_cA_cA_1 m one x). tauto. intro Dxy. 
generalize (Ip0 x Ex). 
assert (inv_half (L m one x y)). 
apply inv_poly_half. tauto. 
generalize (L_not_succ_pred m one x y Im H). 
unfold succ,pred. simpl. 
elim eq_dart_dec. 
elim eq_dart_dec. intro. symmetry in a. tauto. 
intros b a. clear a b. intros. 
assert (y <> nil). 
apply exd_not_nil with m. tauto. tauto. 
assert 
(~ A m zero x <> nil /\ A_1 m zero x <> nil /\ ~A_1 m one x <> nil). 
tauto. clear H1.
generalize (Ip0 y Ey). 
elim eq_dart_dec. 
elim eq_dart_dec. tauto. 
intros b a. clear a b. intros. tauto. 
elim eq_dart_dec. intros a b. clear a b. 
assert (x <> nil). apply exd_not_nil with m. tauto. tauto. intro. 
assert ( A m zero y <> nil /\
     ~ A m one y <> nil /\ ~ A_1 m zero y <> nil). tauto. clear H4. 
tauto. 
tauto. tauto.
Qed.

Lemma inv_poly_L1:  forall m x y z, 
   inv_hmap (L m one x y) ->  inv_poly (L m one x y) -> 
     x <> z -> y <> z -> 
          black_dart m z \/ blue_dart m z \/  red_dart m z.
Proof.
intros m x y z Im Ip. generalize Im Ip. 
simpl. unfold inv_poly,prec_L.
unfold black_dart,blue_dart,red_dart.
unfold succ,pred. simpl. intros. 
 assert (exd m x). tauto.
 assert (exd m y). tauto. rename H into Ex, H0 into Ey. 
elim (eq_dart_dec x y). intro. rewrite <-a in Im0. 
   generalize (fixpt_cA_cA_1 m one x). tauto. intro Dxy. 
elim (exd_dec m z). intro Ez.
generalize (Ip0 z Ez). 
elim eq_dart_dec. tauto. 
elim eq_dart_dec. tauto. intros. 
generalize H. clear H. 
 fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
   fold (black_dart m z) (blue_dart m z) (red_dart m z). tauto. 
intro. left. 
   fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
split. intro. elim b. apply succ_exd with zero. tauto. tauto. 
split. intro. elim b. apply succ_exd with one. tauto. tauto. 
split. intro. elim b. apply pred_exd with zero. tauto. tauto. 
intro. elim b. apply pred_exd with one. tauto. tauto. 
Qed.

(*========================================
                          PROOFS FOR hbs

Theorem inv_poly_nhbs: forall m,  
   inv_hmap m -> inv_poly m -> nhbs m = 0.

          ( SIMILAR FOR THE OTHERS : hbp,hrs,hrp)
========================================*)

(* OK : *)

Lemma nhbs_pos : forall m z,  
   inv_hmap m -> inv_half m -> half_blue_succ m z ->
       (nhbs m > 0)%Z.
Proof.
induction m. simpl. unfold half_blue_succ. unfold succ,pred. simpl. tauto. 
simpl. unfold half_blue_succ,prec_I. unfold succ,pred. simpl. intro z. 
 fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z).
fold (half_blue_succ m z). intros. apply IHm with z. tauto. 
apply (inv_half_I_m m d t p). simpl. unfold prec_I. tauto. tauto. tauto. 
simpl. unfold half_blue_succ,prec_L,succ,pred.  
rename d0 into x, d1 into y. intros z IM IH. 
assert (inv_hmap (L m d x y)). unfold inv_hmap,prec_L, succ,pred. tauto. 
decompose [and] IM; clear IM. 
assert (inv_half m). apply (inv_half_L_m m d x y). tauto. tauto. 
generalize (color_numbers_pos m H0 H5).
 elim (eq_dart_dec x y). intro. rewrite <-a in H4,H6. 
   generalize (fixpt_cA_cA_1 m d x H0 H2). unfold pred,succ. tauto. intro Dxy. 
induction d. simpl. 
  fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
  elim eq_dart_dec. intro. rewrite <-a. 
  elim eq_dart_dec. intro. symmetry in a0; tauto. 
  elim pred_dec.  tauto. intros. decompose [and] H7. clear H7. lia.
   elim eq_dart_dec. intro. 
    assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  elim pred_dec. fold (succ m zero z) (pred m zero z).
fold (half_blue_succ m z). intros. 
  generalize (IHm z H0 H5 H8). intro. lia. intros. lia.
simpl.
  fold (succ m zero z) (pred m zero z) (succ m one z) (pred m one z). 
  elim eq_dart_dec. intro. rewrite <-a. 
    assert (y<>nil). apply exd_not_nil with m. tauto. tauto. tauto.  
  elim eq_dart_dec. 
     assert (x<>nil). apply exd_not_nil with m. tauto. tauto. tauto. 
  elim (succ_dec m zero y). intros. 
(* ICI, y et z sont tous deux half_blue_succ... *)
 fold  (succ m one z) (pred m one z) in H8. 
 fold (half_blue_succ m z) in H8.
  generalize (L_not_succ_pred m one x y H IH). simpl. intro. 
 assert (half_blue_succ m y). unfold half_blue_succ. 
 fold (pred m one y) in H4. tauto. 
 generalize (exds_sethbs_DsL_aux m (fmap_to_set m) z H0 H5 H8). intro. 
generalize (exds_sethbs_DsL_aux m (fmap_to_set m) y H0 H5 H10). intro. 
 generalize (card_number m H0 H5). fold (DsL m) in H11,H12.
  induction (DsL m). simpl in H11,H12. 
 intros. decompose [and] H13. clear H13. 
  assert (2 <= card s0)%nat.  
  apply (exds2_le_2_card s0 y z H12 H11 b).  
  rewrite <-H16. lia. 
intros.  fold  (succ m one z) (pred m one z) in H8. 
 fold (half_blue_succ m z) in H8.
 assert (nhbs m > 0)%Z. apply IHm with z. tauto. tauto. tauto. 
lia.
Qed.

(* OK! *)

Lemma nhbs_pos_rcp : forall m,  
   inv_hmap m -> inv_half m ->  (nhbs m > 0)%Z -> 
    exists z, half_blue_succ m z.
Proof.
induction m. simpl. intros. inversion H1.
simpl. unfold half_blue_succ,prec_I. unfold succ,pred. simpl.
intros. assert (inv_half m). apply (inv_half_I_m m d t p). 
simpl. unfold prec_I. tauto. tauto. tauto. 
simpl. unfold half_blue_succ,prec_L,succ,pred.  
rename d0 into x, d1 into y. intros IM IH. 
assert (inv_hmap (L m d x y)). unfold inv_hmap,prec_L, succ,pred. tauto. 
decompose [and] IM; clear IM. 
assert (inv_half m). apply (inv_half_L_m m d x y). tauto. tauto. 
generalize (color_numbers_pos m H0 H5).
 elim (eq_dart_dec x y). intro. rewrite <-a in H4,H6. 
   generalize (fixpt_cA_cA_1 m d x H0 H2). unfold pred,succ. tauto. intro Dxy. 
   intro. 
  decompose [and] H7. clear H7. 
induction d. simpl. 
 elim pred_dec. intros. 
  assert (nhbs m > 0)%Z. lia. 
  elim (IHm H0 H5 H14). intros z0 hz0. 
  generalize (L_not_succ_pred m zero x y H IH). simpl. intro.
  assert (half_blue_pred m x). unfold  half_blue_pred. tauto. 
  split with z0. 
   elim eq_dart_dec. intro. rewrite <-a0 in hz0. 
    unfold half_blue_succ in hz0. unfold half_blue_pred in H17. tauto. 
   elim eq_dart_dec. intro. rewrite <-a0 in hz0. 
    unfold half_blue_succ in hz0. tauto. 
  fold (succ m zero z0) (pred m zero z0) (succ m one z0) (pred m one z0). 
   fold (half_blue_succ m z0). tauto. 
 intros. 
   generalize (L_not_succ_pred m zero x y H IH). simpl. intro.
   split with x. 
     elim (eq_dart_dec x x). 
      elim eq_dart_dec. intro. symmetry in a. tauto. 
        fold (succ m zero x) (pred m zero x) (succ m one x) (pred m one x). 
   intros. assert (y <> nil). apply exd_not_nil with m. tauto. tauto. tauto. tauto. 
generalize (L_not_succ_pred m one x y H IH). simpl. intro.
 elim succ_dec. simpl. intros.  
 generalize (card_number m H0 H5). 
generalize (exds_sethbs_DsL_aux_rcp m (fmap_to_set m)). 
 fold (DsL m). 
  induction (DsL m). simpl. intros. 
  decompose [and] H17. clear H17. 
  assert (2 <= nhbs m)%Z. lia. 
  assert (2 <= card s0)%nat. lia. 
 generalize (le_2_card_exds2 s0 H24). intro. 
  elim H26. clear H26. intros.
  elim H26. clear H26. intros.
 decompose [and] H26. clear H26. 
 generalize (H16 x0 H0 H5 H27).
 generalize (H16 x1 H0 H5 H29). intros. 
  assert (half_blue_succ m y). unfold  half_blue_succ. tauto. 
  fold (succ m one x) in H3. fold (pred m one y) in H4. 
  clear H18 H19 H20 H21 H22 H23 H25. 
 elim (eq_dart_dec y x0). intro. 
   split with x1. 
     elim eq_dart_dec. intro. rewrite <-a1 in H26. 
      unfold half_blue_succ in H26. tauto. intro. 
      elim eq_dart_dec. intro. rewrite a0 in a1. tauto. intro.
    fold (succ m zero x1) (pred m zero x1) (succ m one x1) (pred m one x1). 
     fold (half_blue_succ m x1). assumption. 
    intro. 
   split with x0. 
     elim eq_dart_dec. intro. rewrite <-a0 in H28. 
        unfold half_blue_succ in H28. tauto. intro. 
     elim eq_dart_dec. tauto. intro. 
  fold (succ m zero x0) (pred m zero x0) (succ m one x0) (pred m one x0). 
     fold (half_blue_succ m x0). assumption. 
intros. 
  fold (succ m one x) in H3. fold (pred m one y) in H4. 
  assert (nhbs m > 0)%Z. lia. 
  generalize (IHm H0 H5 H16). intro. 
  elim H17. intros. 
  split with x0. 
   elim eq_dart_dec. intro. rewrite <-a in H18.
        unfold half_blue_succ in H18. tauto. intro. 
    elim eq_dart_dec. intro. rewrite <-a in H18.
        unfold half_blue_succ in H18. tauto. intro. 
    fold (succ m zero x0) (pred m zero x0) (succ m one x0) (pred m one x0). 
     fold (half_blue_succ m x0). assumption. 
Qed. 

Theorem inv_poly_nhbs: forall m,  
   inv_hmap m -> inv_poly m -> (nhbs m = 0)%Z.
Proof.
  intros. assert (inv_half m). apply inv_poly_half. tauto. 
  generalize (color_numbers_pos m H H1).
  intros. assert ( 0 <= nhbs m)%Z. tauto. clear H2. 
  elim (Z.eq_dec (nhbs m) 0). tauto. intro. 
  assert (nhbs m > 0)%Z. lia. clear b H3. 
  generalize (nhbs_pos_rcp m H H1 H2). intros.
  elim H3. intros z Hz. 
  unfold inv_poly in H0. 
  assert (exd m z). unfold  half_blue_succ in Hz. 
  apply succ_exd with zero. tauto. tauto. 
  generalize (H0 z H4). intro. 
  generalize (half_blue_succ_not_others m z H1 H4 Hz). tauto. 
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma inv_poly_nhbs_0 : forall (m:fmap),
  inv_hmap m -> inv_poly m -> (nhbs m = 0)%Z.
Proof.
apply inv_poly_nhbs.
Qed.

Lemma inv_poly_nhbp_0 : forall (m:fmap),
  inv_hmap m -> inv_poly m -> (nhbp m = 0)%Z.
Proof.
Admitted.

Lemma inv_poly_nhrs_0 : forall (m:fmap),
  inv_hmap m -> inv_poly m -> (nhrs m = 0)%Z.
Proof.
Admitted.

Lemma inv_poly_nhrp_0 : forall (m:fmap),
  inv_hmap m -> inv_poly m -> (nhrp m = 0)%Z.
Proof.
Admitted.

Lemma inv_poly_nh_0 : forall (m:fmap),
  inv_hmap m -> inv_poly m -> (nh m = 0)%Z.
Proof.
intros m h1 h2.
rewrite mynumbering2.
rewrite inv_poly_nhbs_0; try assumption.
rewrite inv_poly_nhbp_0; try assumption.
rewrite inv_poly_nhrs_0; try assumption.
rewrite inv_poly_nhrp_0; try assumption.
ring.
Qed.

Theorem nc_nf : forall (m:fmap),
  inv_hmap m -> inv_poly m -> planar m ->
  (nc m = nn m + 1 -> nf m = nn m + 2)%Z.
Proof.
intros m h1 h2 h3 h.
generalize (mynumbering1 m h1 h3).
intro H; rewrite h in H; clear h.
rewrite mynumbering7 in H.
rewrite mynumbering6 in H.
rewrite mynumbering5b in H.
rewrite mynumbering4a in H.
rewrite mynumbering3 in H.
ring_simplify in H.
rewrite inv_poly_nh_0 in H; try assumption.
rewrite inv_poly_nhbp_0 in H; try assumption.
rewrite inv_poly_nhbs_0 in H; try assumption.
ring_simplify in H.
assert (nb m = nr m).
assert (nb m + nhbs m = nr m + nhrp m)%Z.
rewrite <- mynumbering4a, <- mynumbering4b; trivial.
rewrite inv_poly_nhbs_0, inv_poly_nhrp_0 in H0; try assumption.
ring_simplify in H0.
assumption.
rewrite H0 in H.
ring_simplify in H.
assert (nf m = 2 * nn m + 2 - nn m)%Z.
rewrite <- H; ring.
rewrite H1; ring.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)


Lemma nd_ge_0 : forall (m:fmap), (nd m >= 0)%Z.
Proof.
induction m.
(* K1 : m = V *)
simpl; lia.
(* K2 : m = I *)
simpl; lia.
(* K3 : m = L *)
simpl; assumption.
Qed.

Lemma ex_dart_nd_gt_0 : forall (m:fmap),
  (exists d:dart, exd m d) -> (nd m > 0)%Z.
Proof.
induction m.
(* K1 : m = V *)
intro H; elim H; clear H.
intro da; simpl; tauto.
(* K2 : m = I *)
intro H; elim H; clear H.
intros da Hda; simpl.
generalize (nd_ge_0 m).
intro H; lia.
(* K3 : m = L *)
intro H; elim H; clear H.
intros da Hda; simpl in *.
apply IHm; exists da; assumption.
Qed.

Lemma nd_gt_0_ex_dart : forall (m:fmap),
  (nd m > 0)%Z -> (exists d:dart, exd m d).
Proof.
induction m.
(* K1 : m = V *)
intro H; simpl in *.
cut False; [tauto|lia].
(* K2 : m = I *)
intro H; simpl in *.
exists d; left; trivial.
(* K3 : m = L *)
intro H; simpl in *.
apply IHm; assumption.
Qed.

(* ========================== *)

Lemma nd_ge_nn : forall (m:fmap),
  inv_hmap m -> (nd m >= nn m)%Z.
Proof.
induction m.
(* K1 : m = V *)
simpl; lia.
(* K2 : m = I *)
simpl; unfold prec_I.
intros [Hmap [Hmap1 Hmap2]].
generalize (IHm Hmap); lia.
(* K3 : m = L *)
induction d; simpl; unfold prec_L;
intros [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]];
generalize (IHm Hmap); clear IHm; intro IHm.
elim succ_dec; intro hs.
elim pred_dec; intro hp.
ring_simplify; assumption.
ring_simplify; lia.
elim pred_dec; intro hp.
ring_simplify; lia.
ring_simplify; lia.
elim succ_dec; intro hs.
elim pred_dec; intro hp.
ring_simplify; assumption.
ring_simplify; lia.
elim pred_dec; intro hp.
ring_simplify; lia.
ring_simplify; lia.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)


Lemma all_black_ex_not_black_dec :
  forall (m:fmap), inv_hmap m ->
  {forall d:dart, exd m d -> black_dart m d} +
  {exists d:dart, exd m d /\ ~ black_dart m d}.
Proof.
induction m.
(* K1 : m = V *)
simpl; tauto.
(* K2 : m = I *)
simpl; unfold prec_I.
intros [Hmap [Hmap1 Hmap2]].
generalize (IHm Hmap); clear IHm; intro IHm.
elim IHm; clear IHm; intro IHm.
left; intros da Hda.
elim Hda; clear Hda; intro Hda; try subst da.
generalize (not_exd_black m d t p Hmap Hmap2).
unfold black_dart, succ, pred; simpl; trivial.
generalize (IHm da Hda).
unfold black_dart, succ, pred; simpl; trivial.
right; elim IHm; clear IHm; intros da [Hda1 Hda2].
exists da; split.
right; assumption.
unfold black_dart, succ, pred in *; simpl in *; assumption.
(* K3 : m = L *)
simpl; unfold prec_L.
intros [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
generalize (IHm Hmap); clear IHm; intro IHm.
induction d; right.
(* K31 : d = zero *)
exists d0; split; try assumption.
unfold black_dart, succ, pred; simpl.
elimeqdartdec.
apply or_not_not_and; left.
apply neq_not_not_neq.
apply exd_not_nil with m; assumption.
(* K32 : d = one *)
exists d0; split; try assumption.
unfold black_dart, succ, pred; simpl.
elimeqdartdec.
apply or_not_not_and; right.
apply or_not_not_and; left.
apply neq_not_not_neq.
apply exd_not_nil with m; assumption.
Qed.

Lemma ex_not_black_not_all_black : forall (m:fmap),
  (exists d:dart, exd m d /\ ~ black_dart m d) ->
  ~ (forall d:dart, exd m d -> black_dart m d).
Proof.
intros m HA HB.
elim HA; clear HA.
intros d [h1 h2].
apply h2; apply HB; assumption.
Qed.

Lemma all_black_not_ex_not_black : forall (m:fmap),
  (forall d:dart, exd m d -> black_dart m d) ->
  ~ (exists d:dart, exd m d /\ ~ black_dart m d).
Proof.
intros m HB HA.
apply ex_not_black_not_all_black with m; assumption.
Qed.

Lemma not_ex_not_black_all_black :
  forall (m:fmap), inv_hmap m ->
  ~ (exists d:dart, exd m d /\ ~ black_dart m d) ->
  (forall d:dart, exd m d -> black_dart m d).
Proof.
intros m Hmap H.
generalize (all_black_ex_not_black_dec m Hmap).
intro H0; elim H0; clear H0; intro H0.
assumption. contradiction.
Qed.

Lemma not_all_black_ex_not_black :
  forall (m:fmap), inv_hmap m ->
  ~ (forall d:dart, exd m d -> black_dart m d) ->
  (exists d:dart, exd m d /\ ~ black_dart m d).
Proof.
intros m Hmap H.
generalize (all_black_ex_not_black_dec m Hmap).
intro H0; elim H0; clear H0; intro H0.
contradiction. assumption.
Qed.

(* ========================== *)

Lemma nd_eq_nn_all_black :
  forall (m:fmap), inv_hmap m ->
  nd m = nn m -> (forall (d:dart), exd m d -> black_dart m d).
Proof.
induction m.
(* K1 : m = V *)
simpl; tauto.
(* K2 : m = I *)
simpl; unfold prec_I.
intros [Hmap [Hmap1 Hmap2]] H da Hda.
elim Hda; clear Hda; intro Hda.
subst d; generalize (not_exd_black m da t p Hmap Hmap2).
unfold black_dart, succ, pred; simpl; trivial.
assert (t0 : nd m = nn m); [lia|idtac].
generalize (IHm Hmap t0 da Hda); clear IHm t0.
unfold black_dart, succ, pred; simpl; trivial.
(* K3 : m = L *)
simpl inv_hmap; unfold prec_L.
intros [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
induction d; simpl in *.
(* K31 : d = zero *)
elim (pred_dec m one d0); intro H1.
elim (succ_dec m one d1); intro H2.
intros H da Hda.
cut False; [tauto|idtac].
assert (t0 : nd m = nn m); [lia|idtac].
generalize (IHm Hmap t0 d0 Hmap1); clear IHm t0.
unfold black_dart, succ, pred; simpl.
intros [h1 [h2 [h3 h4]]]; contradiction.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
elim (succ_dec m one d1); intro H2.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
(* K32 : d = one *)
elim (pred_dec m zero d0); intro H1.
elim (succ_dec m zero d1); intro H2.
intros H da Hda.
cut False; [tauto|idtac].
assert (t0 : nd m = nn m); [lia|idtac].
generalize (IHm Hmap t0 d0 Hmap1); clear IHm t0.
unfold black_dart, succ, pred; simpl.
intros [h1 [h2 [h3 h4]]]; contradiction.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
elim (succ_dec m zero d1); intro H2.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
intros H da Hda.
cut False; [tauto|idtac].
generalize (nd_ge_nn m Hmap); lia.
Qed.

Lemma all_black_nd_eq_nn :
  forall (m:fmap), inv_hmap m ->
  (forall (d:dart), exd m d -> black_dart m d) -> nd m = nn m.
Proof.
induction m.
(* K1 : m = V *)
simpl; tauto.
(* K2 : m = I *)
simpl; unfold prec_I.
intros [Hmap [Hmap1 Hmap2]] H.
assert (H0 : nd m = nn m -> (nd m + 1 = nn m + 1)%Z);
[lia | apply H0; clear H0].
apply IHm; clear IHm; try assumption.
intros da Hda.
apply or_intror with (d = da) (exd m da) in Hda.
generalize (H da Hda).
unfold black_dart, succ, pred; simpl; trivial.
(* K3 : m = L *)
simpl inv_hmap; unfold prec_L.
intros [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]] H.
induction d; simpl in *.
(* K31 : d = zero *)
cut False; [tauto|idtac].
generalize (H d0 Hmap1).
unfold black_dart, succ, pred; simpl.
elimeqdartdec.
intros [h1 [h2 [h3 h4]]].
apply h1.
apply exd_not_nil with m; assumption.
(* K32 : d = one *)
cut False; [tauto|idtac].
generalize (H d0 Hmap1).
unfold black_dart, succ, pred; simpl.
elimeqdartdec.
intros [h1 [h2 [h3 h4]]].
apply h2.
apply exd_not_nil with m; assumption.
Qed.

Lemma nd_eq_nn_not_ex_not_black :
  forall (m:fmap), inv_hmap m ->
  nd m = nn m -> ~ (exists d:dart, exd m d /\ ~ black_dart m d).
Proof.
intros m Hmap H.
generalize (nd_eq_nn_all_black m Hmap H).
apply all_black_not_ex_not_black.
Qed.

Lemma not_ex_not_black_nd_eq_nn :
  forall (m:fmap), inv_hmap m ->
  ~ (exists d:dart, exd m d /\ ~ black_dart m d) -> nd m = nn m.
Proof.
intros m Hmap H.
generalize (not_ex_not_black_all_black m Hmap H).
apply all_black_nd_eq_nn; assumption.
Qed.

Lemma ex_not_black_nd_neq_nn :
  forall (m:fmap), inv_hmap m ->
  (exists d:dart, exd m d /\ ~ black_dart m d) -> nd m <> nn m.
Proof.
intros m Hmap H1 H2.
apply (ex_not_black_not_all_black m H1).
apply nd_eq_nn_all_black; assumption.
Qed.

Lemma nd_neq_nn_ex_not_black :
  forall (m:fmap), inv_hmap m ->
  nd m <> nn m -> (exists d:dart, exd m d /\ ~ black_dart m d).
Proof.
intros m Hmap H.
apply not_all_black_ex_not_black; try assumption.
intro H0; apply H.
apply all_black_nd_eq_nn; assumption.
Qed.

(* ========================== *)
(* ======= ########## ======= *)
(* ========================== *)

Lemma nhbs_L0 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap (L m zero d0 d1) -> inv_poly (L m zero d0 d1) ->
  nhbs (L m zero d0 d1) = nhbs m.
Proof.
intros m d0 d1 Hmap Hpoly; simpl.
simpl in Hmap; unfold prec_L in Hmap.
destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (pred_dec m one d0); intro h0.
ring_simplify; trivial.
cut (blue_dart (L m zero d0 d1) d0).
unfold blue_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; contradiction.
apply succ_zero_blue_dart; try assumption.
simpl; unfold prec_L; repeat split; assumption.
unfold succ; simpl; elimeqdartdec.
apply exd_not_nil with m; try assumption.
Qed.

Lemma nhbp_L0 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap (L m zero d0 d1) -> inv_poly (L m zero d0 d1) ->
  (nhbp (L m zero d0 d1) + 1 = nhbp m)%Z.
Proof.
intros m d0 d1 Hmap Hpoly; simpl.
simpl in Hmap; unfold prec_L in Hmap.
destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (pred_dec m one d0); intro h0.
ring_simplify; trivial.
cut (blue_dart (L m zero d0 d1) d0).
unfold blue_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; contradiction.
apply succ_zero_blue_dart; try assumption.
simpl; unfold prec_L; repeat split; assumption.
unfold succ; simpl; elimeqdartdec.
apply exd_not_nil with m; try assumption.
Qed.

Lemma nhrs_L0 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap (L m zero d0 d1) -> inv_poly (L m zero d0 d1) ->
  (nhrs (L m zero d0 d1) + 1 = nhrs m)%Z.
Proof.
intros m d0 d1 Hmap Hpoly; simpl.
simpl in Hmap; unfold prec_L in Hmap.
destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (succ_dec m one d1); intro h0.
ring_simplify; trivial.
cut (red_dart (L m zero d0 d1) d1).
unfold red_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; contradiction.
apply pred_zero_red_dart; try assumption.
simpl; unfold prec_L; repeat split; assumption.
unfold pred; simpl; elimeqdartdec.
apply exd_not_nil with m; try assumption.
Qed.

Lemma nhrp_L0 :
  forall (m:fmap)(d0:dart)(d1:dart),
  inv_hmap (L m zero d0 d1) -> inv_poly (L m zero d0 d1) ->
  nhrp (L m zero d0 d1) = nhrp m.
Proof.
intros m d0 d1 Hmap Hpoly; simpl.
simpl in Hmap; unfold prec_L in Hmap.
destruct Hmap as [Hmap [Hmap1 [Hmap2 [Hmap3 [Hmap4 Hmap5]]]]].
elim (succ_dec m one d1); intro h0.
ring_simplify; trivial.
cut (red_dart (L m zero d0 d1) d1).
unfold red_dart, succ, pred; simpl; elimeqdartdec.
intros [h1 [h2 [h3 h4]]]; contradiction.
apply pred_zero_red_dart; try assumption.
simpl; unfold prec_L; repeat split; assumption.
unfold pred; simpl; elimeqdartdec.
apply exd_not_nil with m; try assumption.
Qed.

