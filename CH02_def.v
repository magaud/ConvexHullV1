(* ====================== *)
(* ===== CH02_def.v ===== *)
(* ====================== *)

Require Export CH01_ccw.
Require Import Extraction.
Open Scope nat_scope.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Fixpoint max_dart (m:fmap) {struct m} : dart :=
  match m with
    V => 0
  | I m0 x t p =>
    if (le_lt_dec x (max_dart m0)) then (max_dart m0) else x
  | L m0 k x y => max_dart m0
  end.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Definition black_dart (m:fmap)(d:dart) : Prop :=
  ~ succ m zero d /\ ~ succ m one d /\
  ~ pred m zero d /\ ~ pred m one d.

Definition blue_dart (m:fmap)(d:dart) : Prop :=
  succ m zero d /\ ~ succ m one d /\
  ~ pred m zero d /\ pred m one d.

Definition red_dart (m:fmap)(d:dart) : Prop :=
  ~ succ m zero d /\ succ m one d /\
  pred m zero d /\ ~ pred m one d.

(* ======================= *)

Lemma black_dart_dec : forall (m:fmap)(d:dart),
  {black_dart m d} + {~ black_dart m d}.
Proof.
intros.
unfold black_dart.
generalize (succ_dec m zero d).
generalize (succ_dec m one d).
generalize (pred_dec m zero d).
generalize (pred_dec m one d).
tauto.
Qed.

Lemma blue_dart_dec : forall (m:fmap)(d:dart),
  {blue_dart m d} + {~ blue_dart m d}.
Proof.
intros.
unfold blue_dart.
generalize (succ_dec m zero d).
generalize (succ_dec m one d).
generalize (pred_dec m zero d).
generalize (pred_dec m one d).
tauto.
Qed.

Lemma red_dart_dec : forall (m:fmap)(d:dart),
  {red_dart m d} + {~ red_dart m d}.
Proof.
intros.
unfold red_dart.
generalize (succ_dec m zero d).
generalize (succ_dec m one d).
generalize (pred_dec m zero d).
generalize (pred_dec m one d).
tauto.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Definition invisible (m:fmap)(d:dart)(p:point) : Prop :=
  if (blue_dart_dec m d) then
  (ccw (fpoint m d) (fpoint m (A m zero d)) p) \/ (align (fpoint m d) (fpoint m (A m zero d)) p)
  else (* red_dart m d *) (ccw (fpoint m (A_1 m zero d)) (fpoint m d) p) \/ (align (fpoint m (A_1 m zero d)) (fpoint m d) p).

Definition visible (m:fmap)(d:dart)(p:point) : Prop :=
  if (blue_dart_dec m d) then
  (ccw (fpoint m d) p (fpoint m (A m zero d)))
  else (* red_dart m d *) (ccw (fpoint m (A_1 m zero d)) p (fpoint m d)).

(* ======================= *)

Lemma invisible_dec : forall (m:fmap)(d:dart)(p:point), 
   {invisible m d p} + {~ invisible m d p}.
Proof.
intros m d p.
unfold invisible.
elim (blue_dart_dec); intro H.
generalize (ccw_dec (fpoint m d) (fpoint m (A m zero d)) p).
generalize (align_dec (fpoint m d) (fpoint m (A m zero d)) p).
tauto.
generalize (ccw_dec (fpoint m (A_1 m zero d)) (fpoint m d) p).
generalize (align_dec (fpoint m (A_1 m zero d)) (fpoint m d) p).
tauto.
Qed.

Lemma visible_dec : forall (m:fmap)(d:dart)(p:point), 
   {visible m d p} + {~ visible m d p}.
Proof.
intros m d p.
unfold visible.
elim (blue_dart_dec); intro H.
generalize (ccw_dec (fpoint m d) p (fpoint m (A m zero d))); tauto.
generalize (ccw_dec (fpoint m (A_1 m zero d)) p (fpoint m d)); tauto.
Qed.

(* ======================= *)

Lemma invisible_not_visible : 
  forall(m:fmap)(d:dart)(p:point),
  invisible m d p -> ~ visible m d p.
Proof.
intros m d p.
unfold invisible, visible.
elim (blue_dart_dec m d).
 intros Hblue H.
 elim H; clear H; intro H.
  apply ccw_axiom_2; assumption.
  apply axiom_orientation_6; apply axiom_orientation_3; assumption.
 intros Hblue H.
 elim H; clear H; intro H.
  apply axiom_orientation_4; assumption.
  apply axiom_orientation_6; apply axiom_orientation_3; assumption.
Qed.

Lemma visible_not_invisible : 
  forall(m:fmap)(d:dart)(p:point),
  visible m d p -> ~ invisible m d p.
Proof.
intros m d p.
unfold visible, invisible.
elim (blue_dart_dec m d).
 intros Hblue H1.
 generalize H1; intro H2.
 apply axiom_orientation_4 in H1.
 apply axiom_orientation_5 in H2.
 unfold not in *; intro H3.
 elim H3; clear H3; intro H3.
  apply H1; assumption.
  apply H2; apply axiom_orientation_3; assumption.
 intros Hblue H1.
 generalize H1; intro H2.
 apply axiom_orientation_4 in H1.
 apply axiom_orientation_5 in H2.
 unfold not in *; intro H3.
 elim H3; clear H3; intro H3.
  apply H1; assumption.
  apply H2; apply axiom_orientation_3; assumption.
Qed.

Lemma not_visible_invisible : 
  forall(m:fmap)(d:dart)(p:point),
  ~ visible m d p -> invisible m d p.
Proof.
intros m d p.
unfold visible, invisible.
elim (blue_dart_dec m d); intros Hblue H1; 
apply axiom_orientation_7 in H1; intuition.
Qed.

Lemma not_invisible_visible : 
  forall(m:fmap)(d:dart)(p:point),
  ~ invisible m d p -> visible m d p.
Proof.
intros m d p.
unfold invisible, visible.
elim (blue_dart_dec m d).
 intros Hblue H.
 generalize (axiom_orientation_7 (fpoint m d) (fpoint m (A m zero d)) p).
 intuition.
 intros Hblue H.
 generalize (axiom_orientation_7 (fpoint m (A_1 m zero d)) (fpoint m d) p).
 intuition.
Qed.

(* ======================= *)

Lemma visible_invisible_dec : forall (m:fmap)(d:dart)(p:point), 
   {visible m d p} + {invisible m d p}.
Proof.
intros m d p.
generalize (visible_dec m d p).
intro H; elim H; clear H.
 intro H; left; tauto.
 intro H; apply not_visible_invisible in H; right; tauto.
Qed.

Lemma invisible_visible_dec : forall (m:fmap)(d:dart)(p:point), 
   {invisible m d p} + {visible m d p}.
Proof.
intros m d p.
generalize (visible_invisible_dec m d p); tauto.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Definition left_dart (m:fmap)(p:point)(d:dart) : Prop :=
  blue_dart m d /\ invisible m (A_1 m one d) p /\ visible m d p.

Definition right_dart (m:fmap)(p:point)(d:dart) : Prop :=
  red_dart m d /\ visible m d p /\ invisible m (A m one d) p.

(* ======================= *)

Lemma left_dart_dec : forall (m:fmap)(p:point)(d:dart),
  {left_dart m p d} + {~ left_dart m p d}.
Proof.
intros.
unfold left_dart.
generalize (blue_dart_dec m d).
generalize (invisible_dec m (A_1 m one d) p).
generalize (visible_dec m d p).
tauto.
Qed.

Lemma right_dart_dec : forall (m:fmap)(p:point)(d:dart),
  {right_dart m p d} + {~ right_dart m p d}.
Proof.
intros.
unfold right_dart.
generalize (red_dart_dec m d).
generalize (visible_dec m d p).
generalize (invisible_dec m (A m one d) p).
tauto.
Qed.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Definition CH2 (x1:dart)(t1:tag)(p1:point)(x2:dart)(t2:tag)(p2:point)(max:dart) : fmap :=
  let m0 := (I (I V x1 t1 p1) x2 t2 p2) in
  let m1 := L (I m0 (max+1) t1 p1) one (max+1) x1 in
  let m2 := L (I m1 (max+2) t2 p2) one (max+2) x2 in
  L (L m2 zero x1 (max+2)) zero x2 (max+1).

Fixpoint CHID (m:fmap)(mr:fmap)(x:dart)(t:tag)(p:point)(max:dart) {struct m} : fmap :=
  match m with 
    V => I V x t p
  | I m0 x0 t0 p0 =>
    if (blue_dart_dec mr x0) then
      if (invisible_dec mr x0 p) then
        (I (CHID m0 mr x t p max) x0 t0 p0)
      else if (left_dart_dec mr p x0) then
             (L (L (I (I (CHID m0 mr x t p max) x0 t0 p0) max t p) one max x) zero x0 max)
           else (I (CHID m0 mr x t p max) x0 t0 p0)
    else if (red_dart_dec mr x0) then
           if (invisible_dec mr x0 p) then
             (I (CHID m0 mr x t p max) x0 t0 p0)
           else if (right_dart_dec mr p x0) then 
                  (L (I (CHID m0 mr x t p max) x0 t0 p0) zero x x0)
                else (CHID m0 mr x t p max)
         else (I (CHID m0 mr x t p max) x0 t0 p0)
  | L m0 zero x0 y0 =>
    if (ccw_dec (fpoint mr x0) (fpoint mr y0) p) then
      (L (CHID m0 mr x t p max) zero x0 y0)
    else (CHID m0 mr x t p max)
  | L m0 one x0 y0 =>
    if (invisible_dec mr x0 p) then
      (L (CHID m0 mr x t p max) one x0 y0)
    else if (invisible_dec mr y0 p) then
           (L (CHID m0 mr x t p max) one x0 y0)
         else (CHID m0 mr x t p max)
  end.

Fixpoint CHI (m1:fmap)(m2:fmap)(max:dart) {struct m1} : fmap :=
  match m1 with
    V => m2
  | I m0 x t p => CHI m0 (CHID m2 m2 x t p max) (max+1)
  | _ => V
  end.

Definition CH (m:fmap) : fmap :=
  match m with
    V => V
  | I V x t p => I V x t p
  | I (I m0 x1 t1 p1) x2 t2 p2 =>
    CHI m0 (CH2 x1 t1 p1 x2 t2 p2 (max_dart m)) ((max_dart m)+3)
  | _ => V
  end.

(* ======================= *)
(* ======= ####### ======= *)
(* ======================= *)

Extraction Language OCaml.
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Constant R => "float". 
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rplus => "fun x y -> x+.y".
Extract Constant Rmult => "fun x y -> x*.y".
Extract Constant Ropp => "fun x -> -.x".
Extract Constant total_order_T => "fun x y -> if (x<y) then (Inleft true) else if (x=y) then (Inleft false) else (Inright)".
Extraction "fmaps" CH.
