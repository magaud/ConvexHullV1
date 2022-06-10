Require Export Jordan1.
Require Import Euclid.
Require Export Compare.
(*==========================================================

              TOPOLOGICAL FMAPS, HMAPS -

              WITH TAGS AND EMBEDDINGS

           PART 2 : SETS OF DARTS, PATHS, ORBITS 

         WITH NOETHERIAN INDUCTION ON A BIJECTION f
         WITH SIGNATURES AND MODULES

           VERSION WITH set AND card REFINED: OK

COMPLETE: OK!!
============================================================*)
(*
cd Desktop/JFD/JFD08/GALAPAGOS/HMAPSTE_08/

coqtop -opt

Load Jordan1.
*)

(*=========================================================
                     SETS OF DARTS 

       FOR NOETHERIAN INDUCTIVE REASONINGS
==========================================================*)

Inductive set:Set:=
    Vs : set | Is : set -> dart -> set.

Fixpoint exds(s:set)(z:dart){struct s}:Prop:=
  match s with
     Vs => False
   | Is s0 x => x=z \/ exds s0 z
  end.

Lemma exds_dec: forall(s:set)(z:dart),
  {exds s z}+{~exds s z}.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intro.
   generalize (eq_dart_dec d z).
   generalize (IHs z).
   tauto.
Qed.

(* IF NO DART IS IN s, s IS Vs: *)

Lemma not_exds_Vs: forall s:set,
  (forall z:dart, ~exds s z) -> s = Vs.
Proof.
intros.
induction s.
 tauto.
 generalize (H d).
   simpl in |- *.
   tauto.
Qed.

Lemma not_exds_diff: forall(s:set)(z:dart),
  ~exds s z -> 
    forall(t:dart), exds s t -> z <> t.
Proof.
intros.
induction s.
 simpl in H0.
   tauto.
 simpl in H0.
   simpl in H.
   elim H0.
  intros.
    rewrite <- H1.
    intro.
    symmetry  in H2.
    tauto.
  apply IHs.
    tauto.
Qed.

(* SUPPRESSION OF ALL OCCURRENCES of z: *)

Fixpoint Ds(s:set)(z:dart){struct s}:set:=
  match s with
     Vs => Vs
   | Is s0 x =>
       if eq_dart_dec x z then (Ds s0 z)
       else Is (Ds s0 z) x
  end.

Lemma not_exds_Ds:forall(s:set)(z:dart),
   ~exds (Ds s z) z.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    apply (IHs z).
  simpl in |- *.
    generalize (IHs z).
    tauto.
Qed.

Lemma exds_Ds:forall(s:set)(x z:dart),
   x <> z ->
     (exds s z <-> exds (Ds s x) z).
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    rewrite a.
    generalize (IHs x z).
    tauto.
  intro.
    simpl in |- *.
    generalize (IHs x z).
    tauto.
Qed.

Lemma exds_Ds_diff:forall(s:set)(x z:dart),
   exds (Ds s x) z -> x <> z.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros x z.
   elim (eq_dart_dec d x).
  intro.
    apply IHs.
  simpl in |- *.
    intros.
    elim H.
   intro.
     rewrite <- H0.
     intro.
     rewrite H1 in b.
     tauto.
   apply IHs.
Qed.

Lemma Ds_s:forall(s:set)(z:dart),
  ~exds s z <-> Ds s z = s.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    rewrite a.
    generalize (IHs z).
    intros.
    split.
   tauto.
   intro.
     assert (exds (Is s z) z).
    simpl in |- *.
      tauto.
    rewrite <- H0 in H1.
      absurd (exds (Ds s z) z).
     apply not_exds_Ds.
     tauto.
  intro.
    split.
   intros.
     generalize (IHs z).
     intros.
     assert (Ds s z = s).
    tauto.
    rewrite H1.
      tauto.
   intros.
     injection H.
     generalize (IHs z).
     tauto.
Qed.

Lemma not_exds_Ds_bis:forall(s:set)(x z:dart),
   ~exds s z -> ~exds (Ds s x) z.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d x).
  intro.
    apply IHs.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs x z).
    tauto.
Qed.

Lemma exds_Ds_exds:forall(s:set)(x z:dart),
   exds (Ds s x) z -> exds s z.
Proof.
intros.
generalize (exds_dec s z).
intro.
generalize (exds_dec (Ds s x) z).
intro.
generalize (not_exds_Ds_bis s x z).
tauto.
Qed.

(* "cardinal" of a (multi-)set: *)

Fixpoint card(s:set):nat:=
  match s with
     Vs => 0%nat
   | Is s0 x => 
       if exds_dec s0 x then card s0
       else (1 + card s0)%nat
  end.

Lemma card_Ds:forall (s:set)(z:dart),
  (card (Ds s z) <= card s)%nat.
Proof.
induction s.
 simpl in |- *.
   intro.
   lia.
 simpl in |- *.
   intro.
   elim (eq_dart_dec d z).
  intro.
    elim (exds_dec s d).
   intro.
     apply IHs.
   intro.
     generalize (IHs z).
     intro.
     lia.
  simpl in |- *.
    elim (exds_dec s d).
   elim (exds_dec (Ds s z) d).
    intros.
      apply IHs.
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H in b0.
       tauto.
     tauto.
   elim (exds_dec (Ds s z) d).
    intros.
      generalize (IHs z).
      intro.
      lia.
    intros.
      generalize (IHs z).
      intro.
      lia.
Qed.

Lemma not_exds_card_Ds:forall (s:set)(z:dart),
  ~exds s z -> card (Ds s z) = card s.
Proof.
intros.
generalize (Ds_s s z).
intros.
assert (Ds s z = s).
 tauto.
 rewrite H1.
   tauto.
Qed.

Lemma exds_card_pos:forall (s:set)(z:dart),
  exds s z -> (0 < card s)%nat.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s d).
  intro.
    apply (IHs d a); tauto.
  intro.
    lia.
Qed.

Lemma exds_card_Ds:forall (s:set)(z:dart),
  exds s z -> card (Ds s z) = (card s - 1)%nat.
Proof.
induction s.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (eq_dart_dec d z).
  intro.
    elim (exds_dec s d).
   intro.
     rewrite a in a0.
     apply IHs.
     tauto.
   intro.
     rewrite a in b.
     rewrite not_exds_card_Ds.
    lia.
    tauto.
  simpl in |- *.
    elim (exds_dec (Ds s z) d).
   elim (exds_dec s d).
    intros.
      rewrite IHs.
     tauto.
     tauto.
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H0 in b0.
       tauto.
     tauto.
   elim (exds_dec s d).
    intros.
      generalize (exds_Ds s z d).
      assert (z <> d).
     intro.
       rewrite H0 in b0.
       tauto.
     tauto.
    intros.
      rewrite IHs.
 assert (0 < card s)%nat.
      apply exds_card_pos with z.
        tauto.
      lia.
     tauto.
Qed.

Lemma exds_card_Ds_inf:forall (s:set)(z:dart),
  exds s z -> (card (Ds s z) < card s)%nat.
Proof.
intros.
generalize (exds_card_pos s z H).
generalize (exds_card_Ds s z H).
intros.
lia.
Qed.

(* ==========================================================
          RELATIONSHIPS BETWEEN sets AND fmaps
===========================================================*)

(* fmap to set *)

Fixpoint fmap_to_set(m:fmap):set:=
 match m with
     V => Vs
   | I m0 x _ _ => Is (fmap_to_set m0) x
   | L m0 _ _ _ => (fmap_to_set m0)
 end.

Lemma exd_exds:forall(m:fmap)(z:dart),
  exd m z <-> exds (fmap_to_set m) z.
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (IHm z); tauto.
 simpl in |- *.
   tauto.
Qed.

Fixpoint ndN (m:fmap):nat:=
 match m with
    V => 0%nat
  | I m0 x _ _ => 
       if exd_dec m0 x then ndN m0
       else (1 + ndN m0)%nat
  | L m0 _ _ _ => ndN m0
 end.

Lemma nd_card:forall(m:fmap),
  ndN m = card (fmap_to_set m).
Proof.
induction m.
 simpl in |- *.
   tauto.
 simpl in |- *.
   elim (exd_dec m d).
  elim (exds_dec (fmap_to_set m) d).
   tauto.
   intros.
     generalize (exd_exds m d).
     tauto.
  elim (exds_dec (fmap_to_set m) d).
   intros.
     generalize (exd_exds m d).
     tauto.
   rewrite IHm.
     tauto.
 simpl in |- *.
   tauto.
Qed.

(* ========================================================
          ALWAYS (multi-)sets
==========================================================*)

(* s1 - s2: *)

Fixpoint set_minus(s1 s2:set){struct s1}:set:=
 match s1 with
     Vs => Vs
   | Is s0 x =>
       if exds_dec s2 x then set_minus s0 s2
       else Is (set_minus s0 s2) x
 end.

Lemma not_exds_minus: forall(s1 s2:set)(z:dart),
  ~ exds s1 z ->
     ~ exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    apply IHs1.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs1 s2 z).
    tauto.
Qed.

Lemma exds_set_minus: forall(s1 s2:set)(z:dart),
  exds s1 z -> ~exds s2 z ->
     exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    elim H.
   intro.
     rewrite H1 in a.
     tauto.
   intro.
     apply IHs1.
    tauto.
    tauto.
  simpl in |- *.
    intro.
    elim H.
   tauto.
   generalize (IHs1 s2 z).
tauto.
Qed.

Lemma not_exds_set_minus: forall(s1 s2:set)(z:dart),
  exds s2 z -> ~exds (set_minus s1 s2) z.
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec s2 d).
  intro.
    apply IHs1.
    tauto.
  simpl in |- *.
    intro.
    generalize (IHs1 s2 z).
    intro.
    assert (d <> z).
   intro.
     rewrite H1 in b.
     tauto.
  tauto.
Qed.

Lemma exds_set_minus_eq:forall(s1 s2:set)(z:dart),
  (exds s1 z /\ ~exds s2 z) <-> exds (set_minus s1 s2) z.
Proof.
intros.
generalize (not_exds_set_minus s1 s2 z).
generalize (exds_set_minus s1 s2 z).
generalize (exds_dec s2 z).
generalize (exds_dec (set_minus s1 s2) z).
generalize (exds_dec s1 z).
generalize (not_exds_minus s1 s2 z).
tauto.
Qed.

(* s1 INCLUDED IN (OR OBS. EQUAL TO) s2 *)

Inductive incls(s1 s2:set):Prop:=
  exds2 : (forall z:dart, exds s1 z -> exds s2 z) 
          -> incls s1 s2.

(* USEFUL: *)

Lemma set_minus_s_Ds :forall(s1 s2:set)(x:dart), 
  ~ exds s1 x -> exds s2 x -> 
     set_minus s1 (Ds s2 x) = set_minus s1 s2. 
Proof.
induction s1.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   elim (exds_dec (Ds s2 x) d).
  elim (exds_dec s2 d).
   intros.
     apply IHs1.
    tauto.
    tauto.
   intros.
     generalize (exds_Ds s2 x d).
     intros.
     assert (x <> d).
    intro.
      rewrite H2 in H.
      tauto.
    tauto.
  elim (exds_dec s2 d).
   intros.
     generalize (exds_Ds s2 x d).
     intros.
     assert (x <> d).
    intro.
      rewrite H2 in H.
      tauto.
    tauto.
   intros.
     rewrite IHs1.
    tauto.
    tauto.
    tauto.
Qed.

(* OK: *)

Lemma card_minus_set:forall(s1 s2:set),
  incls s2 s1 -> 
    (card (set_minus s1 s2) + card s2 = card s1)%nat.
Proof.
induction s1.
 simpl in |- *.
   intros.
   inversion H.
   simpl in H0.
   generalize (not_exds_Vs s2 H0).
   intro.
   rewrite H1.
   simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   inversion H.
   simpl in H0.
   elim (exds_dec s2 d).
  elim (exds_dec s1).
   intros.
     apply IHs1.
     constructor.
     intros.
     elim (H0 z H1).
    intro.
      rewrite <- H2.
      tauto.
    tauto.
   intros.
     generalize (IHs1 (Ds s2 d)).
     intros.
     inversion H.
     assert (incls (Ds s2 d) s1).
    constructor.
      intros.
      assert (d <> z).
     intro.
       rewrite H4 in H3.
       apply (not_exds_Ds s2 z H3).
     generalize (exds_Ds s2 d z H4).
       intro.
       assert (exds s2 z).
      tauto.
      assert (exds (Is s1 d) z).
       apply H2.
         tauto.
       simpl in H7.
         tauto.
    generalize (set_minus_s_Ds s1 s2 d b a).
      intro.
      rewrite H4 in H1.
      generalize (exds_card_Ds s2 d a).
      intro.
      rewrite H5 in H1.
      rewrite <- H1.
     generalize (exds_card_pos s2 d a).
       intro.
       lia.
     tauto.
  intro.
    simpl in |- *.
    elim (exds_dec (set_minus s1 s2) d).
   elim (exds_dec s1 d).
    intros.
      apply IHs1.
      constructor.
      intros.
      elim (H0 z H1).
     intro.
       rewrite H2 in b.
       tauto.
     tauto.
    intros.
      generalize (exds_set_minus_eq s1 s2 d).
      tauto.
   elim (exds_dec s1 d).
    intros.
      elim b0.
      apply (exds_set_minus s1 s2 d a b).
    intros.
      rewrite <- IHs1 with s2.
     lia.
     constructor.
       intros.
       elim (H0 z).
      intro.
        rewrite H2 in b.
        tauto.
      tauto.
      tauto.
Qed.

(*===========================================================
             NOETHERIAN RELATION ON (MULTI-)SETS 
===========================================================*)

Definition Rs(sy sx:set):=
  (card sy < card sx)%nat.

Lemma Acc_set:forall s:set, Acc Rs s.
Proof.
induction s.
 apply Acc_intro.
   unfold Rs at 1 in |- *.
   simpl in |- *.
   intros.
   inversion H.
 apply Acc_intro.
   intro y.
   unfold Rs at 1 in |- *.
   simpl in |- *.
   inversion IHs.
   intro.
   elim (eq_nat_dec (card y) (card s)).
  intro.
    apply Acc_intro.
    intro y0.
    unfold Rs at 1 in |- *.
    rewrite a.
    intro.
    apply H.
    unfold Rs in |- *.
    tauto.
  intro.
    apply Acc_intro.
    unfold Rs at 1 in |- *.
    intros.
    generalize H0.
    clear H0.
    elim (exds_dec s d).
   intros.
     apply H.
     unfold Rs in |- *.
     lia.
   intros.
      apply H.
     unfold Rs in |- *.
     lia.
Qed.

Lemma Rs_wf : well_founded Rs.
Proof.
unfold well_founded in |- *.
apply Acc_set.
Qed.

Lemma exds_Rs_Ds:
 forall(s:set)(z:dart),
   exds s z -> Rs (Ds s z) s.
Proof.
unfold Rs in |- *.
simpl in |- *.
intros.
apply exds_card_Ds_inf.
tauto.
Qed.

(*==========================================================

   PATHS AND ORBITS OF ANY PERMUTATION f ON A hmap

	 WITH NOETHERIAN SET INDUCTION

         MODULE Type Sigf, MODULE Mf:

==========================================================*)

(* ITERATOR FOR A FUNCTION g: *)

Fixpoint Iter(g:dart->dart)(n:nat)(z:dart){struct n}:dart:=
  match n with
    0%nat => z
  | S n0 => g (Iter g n0 z)
 end.

(* SIGNATURE FOR BIJECTIONS : *)

Module Type Sigf.
(* f : bijection dans une hmap m, avec 
domaine de definition (exd m) : dart -> Prop *)
Parameter f : fmap -> dart -> dart.
Parameter f_1 : fmap -> dart -> dart.
Axiom exd_f:forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (f m z)).
Axiom bij_f : forall m:fmap, 
  inv_hmap m -> bij_dart (exd m) (f m).
Axiom exd_f_1:forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (f_1 m z)).
Axiom bij_f_1 : forall m:fmap, 
  inv_hmap m -> bij_dart (exd m) (f_1 m).
Axiom f_1_f : forall (m:fmap)(z:dart), 
  inv_hmap m -> exd m z -> f_1 m (f m z) = z.
Axiom f_f_1 : forall (m:fmap )(z:dart), 
  inv_hmap m -> exd m z -> f m (f_1 m z) = z.
End Sigf.

(*========================================================
      GENERAL PROPERTIES OF ORBITS WRT A BIJECTION f: 
=========================================================*)

(* FUNCTOR : *)

Module Mf(M:Sigf)<:Sigf 
   with Definition f:=M.f
   with Definition f_1:=M.f_1.
Definition f:=M.f.
Definition f_1:=M.f_1.
Definition exd_f:=M.exd_f.
Definition exd_f_1:=M.exd_f_1.
Definition bij_f:=M.bij_f.
Definition bij_f_1:=M.bij_f_1.
Definition f_1_f:=M.f_1_f.
Definition f_f_1:=M.f_f_1.

Lemma exd_Iter_f:forall(m:fmap)(n:nat)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (Iter (f m) n z)).
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (exd_f m (Iter (f m) n z)).
   generalize (IHn z).
   generalize (IHn (Iter (f m) n z)).
tauto.
Qed.

Lemma exd_Iter_f_1:forall(m:fmap)(n:nat)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (Iter (f_1 m) n z)).
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   generalize (exd_f_1 m (Iter (f_1 m) n z)).
   generalize (IHn z).
   generalize (IHn (Iter (f_1 m) n z)).
tauto.
Qed.

(*========================================================
                 ITERATIONS IN ORBITS:
	       WITH NOETHERIAN INDUCTION
=======================================================*)

(* REMAINING DARTS DURING f ITERATION ON z STARTING FROM 
A set sx: *)

Theorem Iter_rem_F :
 forall (m:fmap)(z:dart),
  forall sx: set, (forall sy: set, Rs sy sx -> set)
    -> set.
Proof.
 intros m z.
 refine
    (fun sx F =>
     let n:= ((ndN m)-(card sx))%nat in
     let zn := Iter (f m) n z in
     match exds_dec sx zn with
       left _ => F (Ds sx zn) _
     | right _ => sx
     end).
 apply exds_Rs_Ds.
 tauto.
Defined.

Definition Iter_rem_aux(m:fmap)(z:dart):
  set -> set
 := Fix Rs_wf (fun _:set => set) (Iter_rem_F m z).

(* UPPER_BOUND OF THE f ITERATION NUMBER 
STARTING FROM A SET: *)

Definition Iter_upb_aux(m:fmap)(z:dart)(s:set):nat:=
  ((ndN m) - (card (Iter_rem_aux m z s)))%nat.

(* REMAINING DARTS IN THE f ITERATION 
STARTING FROM THE FMAP DART SET: *)

Definition Iter_rem(m:fmap)(z:dart):set:=
  Iter_rem_aux m z (fmap_to_set m).

(* UPPER_BOUND OF THE f ITERATION NUMBER 
STARTING FROM THE FMAP DART SET: *)

Definition Iter_upb(m:fmap)(z:dart):nat:=
  ((ndN m) - (card (Iter_rem m z)))%nat.

(* DART SETS CONTAINING THE f-ORBIT: *)

Definition Iter_orb_aux(m:fmap)(z:dart)(s:set):set:=
  set_minus (fmap_to_set m) (Iter_rem_aux m z s).

Definition Iter_orb(m:fmap)(z:dart):set:=
  set_minus (fmap_to_set m) (Iter_rem m z).

(* FIXPOINT EQUATION TO CHARACTERIZE THE REMAINING
   DART SET, STARTING FROM A SET: *)

Theorem Iter_rem_aux_equation :
  forall(m:fmap)(z:dart)(sx:set),
  Iter_rem_aux m z sx =
    let n := ((ndN m) - (card sx))%nat in
    let zn := Iter (f m) n z in
    if exds_dec sx zn
    then Iter_rem_aux m z (Ds sx zn)
    else sx.
Proof.
intros m z sx.
unfold Iter_rem_aux in |- *.
rewrite Fix_eq.
 auto.
 intros x0 f0 g0 Heqfg.
   unfold Iter_rem_F in |- *.
   destruct (exds_dec x0 (Iter (f m) 
     ((ndN m - card x0))%nat z)).
  rewrite Heqfg.
    trivial.
  trivial.
Qed.

(*========================================================
 EXISTENCY PROPERTIES OF ITERATED DARTS, upb IN ORBITS...:
	       WITH NOETHERIAN IND. 
=======================================================*)

(* FOR THE FOLLOWING LEMMA: *)

Definition P1
 (m:fmap)(z:dart)(s:set):Prop:=
    let sr := Iter_rem_aux m z s in
    let n := Iter_upb_aux m z s in
    ~ exds sr (Iter (f m) n z).

(* THE upb_ITERATED DART BY f DOES NOT REMAIN: *)

Lemma not_exds_rem_upb :
  forall(m:fmap)(z:dart)(s:set),
   let sr := Iter_rem_aux m z s in
    let n := Iter_upb_aux m z s in
    ~ exds sr (Iter (f m) n z).
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P1 m z) _).
unfold P1 in |- *.
unfold Iter_upb_aux in |- *.
simpl in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
   unfold Rs in |- *.
   simpl in |- *.
   apply exds_card_Ds_inf.
   tauto.
 tauto.
Qed.

(* THE upb_ITERATED DART BY f DOES NOT REMAIN: *)

Lemma not_exds_Iter_rem_upb :
 forall(m:fmap)(z:dart),
  let n:= Iter_upb m z in
   ~ exds (Iter_rem m z) (Iter (f m) n z).
Proof.
unfold Iter_rem in |- *.
unfold Iter_upb in |- *.
intros m z.
unfold Iter_rem in |- *.
generalize (not_exds_rem_upb m z (fmap_to_set m)).
simpl in |- *.
unfold Iter_upb_aux in |- *.
tauto.
Qed.

(* THE upb_ITERATED DART BY f IS IN m: *)

Lemma  exd_Iter_upb:
  forall(m:fmap)(z:dart), inv_hmap m ->
   exd m z -> exd m (Iter (f m) (Iter_upb m z) z).
Proof.
intros.
generalize (exd_Iter_f m (Iter_upb m z) z).
tauto.
Qed.

(* THE upb_ITERATED DART BY f IS IN THE COMPLEMENTARY: *)

Lemma exd_Iter_orb_upb :
 forall(m:fmap)(z:dart),
  inv_hmap m -> exd m z ->
   let n:= Iter_upb m z in
     exds (Iter_orb m z) (Iter (f m) n z).
Proof.
unfold Iter_orb in |- *.
intros.
apply exds_set_minus.
 generalize (exd_exds m (Iter (f m) (Iter_upb m z) z)).
   intro.
   generalize (exd_Iter_upb m z H H0).
   tauto.
 apply not_exds_Iter_rem_upb.
Qed.

(* NOT REMAINING EQUIVALENT TO BEING IN THE COMPLEMENTARY: *)

Lemma exds_rem_orb:forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m t ->
  (~exds (Iter_rem m z) t <-> exds (Iter_orb m z) t).
Proof.
intros.
unfold Iter_orb in |- *.
generalize (exds_set_minus_eq (fmap_to_set m) (Iter_rem m z) t).
generalize (exd_exds m t).
tauto.
Qed.

Definition R3
 (m:fmap)(z t:dart)(s:set):Prop:=
  ~ exds s t ->
   let sr := Iter_rem_aux m z s in
    ~ exds sr t.

Lemma LR3:forall(m:fmap)(z t:dart)(s:set),
  ~ exds s t ->
   let sr := Iter_rem_aux m z s in
    ~ exds sr t.
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (R3 m z t) _).
unfold R3 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  apply not_exds_Ds_bis.
    tauto.
 tauto.
Qed.

Definition R2
 (m:fmap)(z:dart)(s:set):Prop:=
   let sr := Iter_rem_aux m z s in
    ~ exds sr (Iter (f m) (ndN m - card s)%nat z).

Lemma LR2 :
  forall(m:fmap)(z:dart)(s:set),
   let sr := Iter_rem_aux m z s in
    ~ exds sr (Iter (f m) (ndN m - card s)%nat z).
Proof.
intros m z.
simpl in |- *.
refine (well_founded_ind Rs_wf (R2 m z) _).
unfold R2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply LR3.
   apply not_exds_Ds.
 tauto.
Qed.

(* OK!! BUT lia IS LONG... *)

Definition R1
 (m:fmap)(z:dart)(i:nat)(s:set):Prop:=
   let sr := Iter_rem_aux m z s in
   let n := Iter_upb_aux m z s in
      (ndN m - card s <= i <= n)%nat -> 
       ~ exds sr (Iter (f m) i z).
Lemma LR1 :
  forall(m:fmap)(z:dart)(i:nat)(s:set),
   let sr := Iter_rem_aux m z s in
   let n := Iter_upb_aux m z s in
     (ndN m - card s <= i <= n)%nat -> 
      ~ exds sr (Iter (f m) i z).
Proof.
intros m z i.
refine (well_founded_ind Rs_wf (R1 m z i) _).
unfold R1 in |- *.
unfold Iter_upb_aux in |- *.
intros.
elim (eq_nat_dec i (ndN m - card x)%nat).
 intro.
   rewrite a.
   apply LR2.
 intro.
   generalize H0.
   rewrite Iter_rem_aux_equation.
   simpl in |- *.
   elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
  intros.
    apply H.
   unfold Rs in |- *.
     apply exds_card_Ds_inf.
     tauto.
   split.
    generalize (exds_card_Ds x 
        (Iter (f m) (ndN m - card x)%nat z) a).
      intro.
      rewrite H2.
      elim H0.
      intros.
      clear H a H1 H2 H0 H4.
      lia.
    tauto.
  intros.
    clear H H0 b0.
    lia.
Qed.

(* VERY IMPORTANT: COROLLARIES: *)

Lemma not_exds_Iter_f_i :
  forall(m:fmap)(z:dart)(i:nat),
   let sr := Iter_rem m z in
   let n := Iter_upb m z in
     (i <= n)%nat -> ~ exds sr (Iter (f m) i z).
Proof.
simpl in |- *.
unfold Iter_upb in |- *.
unfold Iter_rem in |- *.
intros.
apply LR1.
generalize (nd_card m).
intro.
rewrite H0.
simpl in |- *.
unfold Iter_upb in |- *.
unfold Iter_upb_aux in |- *.
lia.
Qed.

Lemma exds_Iter_f_i :
  forall(m:fmap)(z:dart)(i:nat),
  inv_hmap m -> exd m z ->
   let s := Iter_orb m z in
   let n := Iter_upb m z in
     (i <= n)%nat -> exds s (Iter (f m) i z).
Proof.
intros.
assert (exd m (Iter (f m) i z)).
 generalize (exd_Iter_f m i z H).
   intro.
   tauto.
 generalize (exds_rem_orb m z (Iter (f m) i z) H H2).
   unfold s in |- *.
   intros.
   generalize (not_exds_Iter_f_i m z i).
   simpl in |- *.
   tauto.
Qed.

(*========================================================
          card PROPERTIES OF ORBITS:
	    WITH NOETHERIAN INDUCTION
=======================================================*)

(* card OF THE REMAINING / ndN IN THE fmap: *)

Definition P2
 (m:fmap)(z:dart)(s:set):Prop:=
  (card s < ndN m ->
    card (Iter_rem_aux m z s) < ndN m)%nat.

Lemma card_rem_aux:forall(m:fmap)(z:dart)(s:set),
  (card s < ndN m ->
    card (Iter_rem_aux m z s) < ndN m)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P2 m z) _).
unfold P2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
     < card x)%nat.
   apply exds_card_Ds_inf.
     tauto.
   lia.
  tauto.
Qed.

Definition P2_bis
 (m:fmap)(z:dart)(s:set):Prop:=
  (card s <= ndN m ->
    card (Iter_rem_aux m z s) <= ndN m)%nat.

Lemma card_rem_aux_bis:forall(m:fmap)(z:dart)(s:set),
   (card s <= ndN m ->
    card (Iter_rem_aux m z s) <= ndN m)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P2_bis m z) _).
unfold P2_bis in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   apply H.
  unfold Rs in |- *.
    apply exds_card_Ds_inf.
    tauto.
  assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
          < card x)%nat.
   apply exds_card_Ds_inf.
     tauto.
   lia.
  tauto.
Qed.

(* THEN: *)

Lemma upb_pos_aux:forall(m:fmap)(z:dart),
  exd m z ->
      (card (Iter_rem m z) < ndN m)%nat.
Proof.
intros.
unfold Iter_rem in |- *.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec (fmap_to_set m) (Iter (f m) (ndN m - card (fmap_to_set m)) z)).
 intro.
   apply card_rem_aux.
   assert
    (card (Ds (fmap_to_set m) 
      (Iter (f m) (ndN m - card (fmap_to_set m)) z)) <
     card (fmap_to_set m))%nat.
  apply exds_card_Ds_inf.
    tauto.
  generalize (nd_card m).
    intro.
    lia.
 intro.
   generalize (nd_card m).
   intro.
   assert (ndN m - card (fmap_to_set m) = 0)%nat.
  lia.
  rewrite H1 in b.
    simpl in b.
    generalize (exd_exds m z).
    intro.
    generalize (exds_dec (fmap_to_set m) z).
    tauto.
Qed.

(* OK, IMPORTANT: COROLLARY*)

Theorem upb_pos:forall(m:fmap)(z:dart),
  exd m z -> (0 < Iter_upb m z)%nat.
Proof.
unfold Iter_upb in |- *.
intros.
generalize (upb_pos_aux m z).
intros.
generalize (H0 H).
intro.
lia.
Qed.

Definition Q1(m:fmap)(z:dart)(s:set):Prop:=
   (card (Iter_rem_aux m z s) <= card s)%nat.

Lemma LQ1:forall(m:fmap)(z:dart)(s:set),
   (card (Iter_rem_aux m z s) <= card s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (Q1 m z) _).
unfold Q1 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   assert (card (Ds x (Iter (f m) 
     (ndN m - card x) z)) < card x)%nat.
  apply exds_card_Ds_inf.
    tauto.
  assert
   (card (Iter_rem_aux m z 
      (Ds x (Iter (f m) (ndN m - card x) z))) <=
    card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
   apply H.
     unfold Rs in |- *.
     tauto.
   lia.
 intro.
   lia.
Qed.

Definition Q2(m:fmap)(z:dart)(s:set):Prop:=
  exds s (Iter (f m) (ndN m - card s)%nat z) ->
      (card (Iter_rem_aux m z s) < card s)%nat.

Lemma LQ2:forall(m:fmap)(z:dart)(s:set),
  exds s (Iter (f m) (ndN m - card s) z) ->
      (card (Iter_rem_aux m z s) < card s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (Q2 m z) _).
unfold Q2 in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intro.
   assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
         < card x)%nat.
  apply exds_card_Ds_inf.
    tauto.
  assert
   (card (Iter_rem_aux m z (Ds x (Iter (f m) 
      (ndN m - card x) z))) <=
    card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
   apply LQ1.
   lia.
 tauto.
Qed.

(*==========================================================
     SOME LEMMAS, THEN RESULTS ABOUT PERIODICITY
===========================================================*)

(* L2 : *)

Definition PL2(m:fmap)(z t:dart)(x:set):Prop:=
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0 -> 
        ~ exds (Iter_rem_aux m z (Ds x zn0)) t.

Lemma L2:forall(m:fmap)(z t:dart)(x:set),
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0 -> 
        ~ exds (Iter_rem_aux m z (Ds x zn0)) t.
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (PL2 m z t) _).
unfold PL2 in |- *.
intros.
generalize H3.
clear H3.
rewrite (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 tauto.
 tauto.
Qed.

(* L3: *)

Definition PL3(m:fmap)(z t:dart)(x:set):Prop:=
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0.

Lemma L3:forall(m:fmap)(z t:dart)(x:set),
  inv_hmap m -> exd m z -> exds x t ->
    let sr:= Iter_rem_aux m z x in
    let zn0 := (Iter (f m) (ndN m - card x)%nat z) in
    ~exds sr t -> 
       exds x zn0. 
Proof.
intros m z t.
refine (well_founded_ind Rs_wf (PL3 m z t) _).
unfold PL3 in |- *.
intros.
generalize H3.
clear H3.
rewrite (Iter_rem_aux_equation m z x).
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 tauto.
 tauto.
Qed.

(* EXTRACTION, OK: *)

Definition P4(m:fmap)(z t:dart)(s:set):Set:=
 inv_hmap m -> exd m z -> exds s t ->
   (card s <= ndN m)%nat ->
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
   ~ exds sr t ->
      {i:nat | (i < nr)%nat /\ Iter (f m) i z = t}.

Lemma ex_i_aux :forall(m:fmap)(z t:dart)(s:set),
 inv_hmap m -> exd m z -> exds s t ->
   (card s <= ndN m)%nat ->
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
   ~ exds sr t ->
      {i:nat | (i < nr)%nat /\ Iter (f m) i z = t}.
Proof.
intros m z t.
refine (well_founded_induction Rs_wf (P4 m z t) _).
unfold P4 in |- *.
unfold Iter_upb_aux in |- *.
intros.
rewrite Iter_rem_aux_equation.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x)%nat z)).
 intro.
   elim (eq_dart_dec (Iter (f m) (ndN m - card x)%nat z) t).
  intro.
    split with (ndN m - card x)%nat.
    split.
   assert
    (card (Iter_rem_aux m z (Ds x (Iter (f m) 
        (ndN m - card x) z))) <=
     card (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
    assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
               < card x)%nat.
     apply exds_card_Ds_inf.
       tauto.
     apply LQ1.
    generalize (exds_card_Ds_inf x 
         (Iter (f m) (ndN m - card x)%nat z)).
      intros.
      generalize (H6 a).
      intro.
      lia.
   tauto.
  intro.
    apply H.
   unfold Rs in |- *.
     apply exds_card_Ds_inf.
     tauto.
   tauto.
   tauto.
   generalize (exds_Ds x (Iter (f m) (ndN m - card x)%nat z) t).
     tauto.
   assert (card (Ds x (Iter (f m) (ndN m - card x) z))
     < card x)%nat.
    apply exds_card_Ds_inf.
      tauto.
    lia.
   apply L2.
    tauto.
    tauto.
    tauto.
    tauto.
    tauto.
 intro.
   absurd (exds x (Iter (f m) (ndN m - card x)%nat z)).
  tauto.
  eapply L3.
   tauto.
   tauto.
   apply H2.
     tauto.
Qed.

(* IF t IS REMOVED, THERE EXISTS i < nr, S.T. t IS THE ith ITERATED: OK *)

Lemma ex_i :forall(m:fmap)(z t:dart),
 inv_hmap m -> exd m z -> exd m t ->
   let sr:= Iter_rem m z in
   let nr:= Iter_upb m z in
   ~ exds sr t ->
      {i : nat | (i < nr)%nat /\ Iter (f m) i z = t}.
Proof.
unfold Iter_rem in |- *.
unfold Iter_upb in |- *.
intros.
generalize ex_i_aux.
simpl in |- *.
unfold Iter_rem in |- *.
unfold Iter_upb_aux in |- *.
intros.
apply H3.
 tauto.
 tauto.
 generalize (exd_exds m t).
   tauto.
 rewrite nd_card.
   lia.
 tauto.
Qed.

(* THIS APPLIES TO THE nr-th ITERATED *)

Lemma ex_i_upb :forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z -> 
   let nr:= Iter_upb m z in
 {i : nat | (i < nr)%nat /\ Iter (f m) i z = Iter (f m) nr z}.
Proof.
intros.
unfold nr in |- *.
apply ex_i.
 tauto.
 tauto.
 generalize (exd_Iter_f m (Iter_upb m z) z).
   tauto.
 generalize not_exds_rem_upb.
   simpl in |- *.
   intros.
   unfold Iter_rem in |- *; unfold Iter_upb in |- *.
   unfold Iter_rem in |- *.
   unfold Iter_upb_aux in H1.
   apply H1.
Qed.

(* A RESULT OF PERIODICITY: *)

Lemma Iter_plus:forall(m:fmap)(z:dart)(p i:nat),
 inv_hmap m -> exd m z -> 
   Iter (f m) (p + i)%nat z = Iter (f m) i z -> 
      Iter (f m) p z = z.
Proof.
induction i.
 simpl in |- *.
   assert (p + 0 = p)%nat.
  lia.
  rewrite H.
    tauto.
 simpl in |- *.
   assert (p + S i = S (p + i))%nat.
  lia.
  rewrite H.
    simpl in |- *.
    clear H.
    intros.
    assert
     (f_1 m (f m (Iter (f m) (p + i)%nat z)) = 
         f_1 m (f m (Iter (f m) i z))).
   rewrite H1.
     tauto.
   rewrite f_1_f in H2.
    rewrite f_1_f in H2.
     apply IHi.
      tauto.
      tauto.
      tauto.
     tauto.
     generalize (exd_Iter_f m i z).
       tauto.
    tauto.
    generalize (exd_Iter_f m (p + i) z).
      tauto.
Qed.

(* ITS INVERSE: *)

Lemma Iter_plus_inv:forall(m:fmap)(z:dart)(p i:nat),
 inv_hmap m -> exd m z -> 
   Iter (f m) p z = z -> 
     Iter (f m) (p + i)%nat z = Iter (f m) i z.
Proof.
induction i.
 simpl in |- *.
   assert (p + 0 = p)%nat.
  lia.
  rewrite H.
    tauto.
 simpl in |- *.
   assert (p + S i = S (p + i))%nat.
  lia.
  rewrite H.
    simpl in |- *.
    clear H.
    intros.
    rewrite IHi.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

(* AND n TIMES: *)

Lemma Iter_mult:forall(m:fmap)(z:dart)(n p:nat),
 inv_hmap m -> exd m z -> 
     Iter (f m) p z = z ->  Iter (f m) (n*p)%nat z = z.
Proof.
induction n.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite Iter_plus_inv.
    apply (IHn p H H0 H1).
  tauto.
  tauto.
  tauto.
Qed.

(* PERIODICITY + n TIMES: *)

Lemma Iter_plus_mult:forall(m:fmap)(z:dart)(n p i:nat),
 inv_hmap m -> exd m z -> 
    Iter (f m) p z = z -> 
      Iter (f m) (i + n*p)%nat z = Iter (f m) i z.
Proof.
intros.
induction n.
 simpl in |- *.
   assert (i + 0 = i)%nat.
  lia.
  rewrite H2.
    tauto.
 simpl in |- *.
   assert (i + (p + n * p) = p + (i + n * p))%nat.
  lia.
  rewrite H2.
    rewrite Iter_plus_inv.
   tauto.
   tauto.
   tauto.
   tauto.
Qed.

Lemma Iter_comp:forall(m:fmap)(i j:nat)(z:dart),
  Iter (f m) (i+j)%nat z = Iter (f m) i (Iter (f m) j z).
Proof.
induction i.
 simpl in |- *.
   tauto.
 simpl in |- *.
   intros.
   rewrite IHi.
   tauto.
Qed.

Lemma f_1_Iter_f:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z ->
    (f_1 m) (Iter (f m) (S i) z) = Iter (f m) i z.
Proof.
induction i.
 simpl in |- *.
   intros.
   apply f_1_f.
  trivial.
  trivial.
 simpl in |- *.
   intros.
   rewrite f_1_f.
  tauto.
  tauto.
  assert (f m (Iter (f m) i z) = Iter (f m) (S i) z).
   simpl in |- *.
     tauto.
   rewrite H1.
     generalize (exd_Iter_f m (S i) z).
     tauto.
Qed. 

Lemma Iter_f_f_1  :forall(m:fmap)(i j:nat)(z:dart),
  inv_hmap m -> exd m z -> (j <= i)%nat ->
    Iter (f_1 m) j (Iter (f m) i z) = 
        Iter (f m) (i - j)%nat z.
Proof.
 induction i.
 intros.
   assert (j = 0)%nat.
  lia.
  rewrite H2.
    simpl in |- *.
    trivial.
 induction j.
  simpl in |- *.
    tauto.
  intros.
    simpl in |- *.
    assert (f m (Iter (f m) i z) = Iter (f m) (S i) z).
   simpl in |- *.
     tauto.
   rewrite H2.
     rewrite IHj.
    assert (S i - j = S (i - j))%nat.
     lia.
     rewrite H3.
       apply f_1_Iter_f.
      trivial.
      trivial.
    trivial.
    trivial.
    lia.
Qed.

Lemma Iter_f_f_1_i:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f_1 m) i (Iter (f m) i z) = z. 
Proof.
intros.
rewrite Iter_f_f_1.
 assert (i - i = 0)%nat.
  lia.
  rewrite H1.
    simpl in |- *.
    trivial.
 trivial.
 trivial.
 lia.
Qed.

(* IMMEDIATE: USEFUL *)

Lemma Iter_f_Si:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f m) (S i) z = Iter (f m) i (f m z).
Proof.
simpl in |- *.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.

(* IMMEDIATE: USEFUL *)

Lemma Iter_f_1_Si:forall(m:fmap)(i:nat)(z:dart),
  inv_hmap m -> exd m z -> 
    Iter (f_1 m) (S i) z = Iter (f_1 m) i (f_1 m z).
Proof.
simpl in |- *.
intros.
induction i.
 simpl in |- *.
    tauto.
simpl in |- *.
  rewrite IHi in |- *.
   tauto.
Qed.
   

(*==========================================================

                nr IS THE LOWEST PERIOD... 

===========================================================*)

Definition diff_int_aux
  (m:fmap)(z:dart)(a b:nat)(t:dart): Prop:=
   forall i : nat, (a <= i <= b)%nat -> 
     Iter (f m) i z <> t.

Lemma diff_int_aux_dec:forall(m:fmap)(z:dart)(a b:nat)(t:dart),
  {diff_int_aux m z a b t} + {~diff_int_aux m z a b t}.
Proof.
intros.
elim (le_gt_dec b a).
 intro.
   elim (eq_nat_dec a b).
  intro.
    rewrite <- a1.
    elim (eq_dart_dec (Iter (f m) a z) t).
   intro.
     right.
     unfold diff_int_aux in |- *.
     intro.
     generalize a2.
     apply H.
     lia.
   intro.
     left.
     unfold diff_int_aux in |- *.
     intros.
     assert (i = a).
    lia.
    rewrite H0.
      tauto.
  intro.
    left.
    unfold diff_int_aux in |- *.
    intros.
    lia.
 induction b.
  intro.
    absurd (0 > a)%nat.
   lia.
   tauto.
  intro.
    elim (eq_nat_dec a b).
   intro.
     rewrite a0.
     elim (eq_dart_dec (Iter (f m) b z) t).
    intro.
      right.
      unfold diff_int_aux in |- *.
      intro.
      generalize a1.
      apply H.
      lia.
    intro.
      elim (eq_dart_dec (Iter (f m) (S b) z) t).
     intro.
       right.
       unfold diff_int_aux in |- *.
       intro.
       generalize a1.
       apply H.
       lia.
     intro.
       left.
       unfold diff_int_aux in |- *.
       intros.
       assert (i = b \/ i = S b).
      lia.
      elim H0.
       intro.
         rewrite H1.
         tauto.
       intro.
         rewrite H1.
         tauto.
   intro.
     assert (b > a)%nat.
    lia.
    elim (IHb H).
     intro.
       elim (eq_dart_dec (Iter (f m) (S b) z) t).
      intro.
        right.
        unfold diff_int_aux in |- *.
        intro.
        generalize a1.
        apply H0.
        lia.
      intro.
        left.
        unfold diff_int_aux in |- *.
        intros.
        unfold diff_int_aux in a0.
        elim (eq_nat_dec i (S b)).
       intro.
         rewrite a1.
         tauto.
       intro.
         assert (a <= i <= b)%nat.
        lia.
        apply (a0 i H1).
     intro.
       right.
       unfold diff_int_aux in |- *.
       unfold diff_int_aux in b2.
       intro.
       apply b2.
       intros.
       apply H0.
       lia.
Qed.

(* DIFFERENCE IN AN INTERVAL *)

Definition diff_int
  (m:fmap)(z:dart)(a b:nat): Prop:=
   forall i j : nat, (a <= i /\ i < j /\ j <= b)%nat -> 
     Iter (f m) i z <> Iter (f m) j z.

Lemma diff_int_le:forall(m:fmap)(z:dart)(a b:nat),
  (b <= a)%nat -> diff_int m z a b.
Proof.
intros.
unfold diff_int in |- *.
intros.
lia.
Qed.

Lemma diff_int_dec:forall(m:fmap)(z:dart)(a b:nat),
  {diff_int m z a b} + {~diff_int m z a b}.
Proof.
intros.
induction b.
 left.
   unfold diff_int in |- *.
   intros.
   lia.
 elim IHb.
  intro.
    generalize (diff_int_aux_dec m z a b (Iter (f m) (S b) z)).
    intros.
    elim H.
   intro.
     clear IHb H.
     left.
     unfold diff_int in |- *.
     intros.
     unfold diff_int in a0.
     unfold diff_int_aux in a1.
     elim (eq_nat_dec j (S b)).
    intro.
      rewrite a2.
      apply a1.
      lia.
    intro.
      apply a0.
      lia.
   intro.
     clear IHb H.
     unfold diff_int_aux in b0.
     right.
     unfold diff_int in |- *.
     intro.
     apply b0.
     intros.
     apply H.
     lia.
  intro.
    unfold diff_int in b0.
    right.
    unfold diff_int in |- *.
    intro.
    apply b0.
    intros.
    apply H.
    lia.
Qed.

(* EXISTENCY Of THE z^i IN AN INTERVAL *)

Definition exds_int(m:fmap)(z:dart)(a b:nat)(s:set):Prop:=
  forall i:nat, (a <= i <= b)%nat ->  
    exds s (Iter (f m) i z).

Lemma exds_int_gt:forall(m:fmap)(z:dart)(a b:nat)(s:set),
  (b < a)%nat -> exds_int m z a b s.
Proof.
intros.
unfold exds_int in |- *.
intros.
absurd (b < a)%nat.
 lia.
 tauto.
Qed.

Lemma exds_int_dec : forall(m:fmap)(z:dart)(a b:nat)(s:set),
  {exds_int m z a b s} + {~exds_int m z a b s}.
Proof.
intros.
elim (le_gt_dec a b).
 intro.
   induction b.
  elim (exds_dec s z).
   intro.
     left.
     unfold exds_int in |- *.
     intros.
     assert (i = 0)%nat.
    lia.
    rewrite H0.
      simpl in |- *.
      tauto.
   intro.
     right.
     unfold exds_int in |- *.
     intro.
     apply b.
     assert (exds s (Iter (f m) 0%nat z)).
    apply H.
      lia.
    simpl in H0.
      tauto.
  elim (eq_nat_dec a (S b)).
   intro.
     rewrite <- a1.
     elim (exds_dec s (Iter (f m) a z)).
    intro.
      left.
      unfold exds_int in |- *.
      intros.
      assert (i = a).
     lia.
     rewrite H0.
       tauto.
    intro.
      right.
      unfold exds_int in |- *.
      intro.
      apply b0.
      apply H.
      lia.
   intro.
     assert (a <= b)%nat.
    lia.
    elim (IHb H).
     intro.
       elim (exds_dec s (Iter (f m) (S b) z)).
      intro.
        left.
        unfold exds_int in |- *.
        intros.
        elim (eq_nat_dec i (S b)).
       intro.
         rewrite a3.
         tauto.
       intro.
         unfold exds_int in a1.
         apply a1.
         lia.
      intro.
        right.
        unfold exds_int in |- *.
        intro.
        apply b1.
        apply H0.
        lia.
     intro.
       right.
       unfold exds_int in |- *.
       intro.
       apply b1.
       unfold exds_int in |- *.
       intros.
       apply H0.
       lia.
 intro.
   left.
   apply exds_int_gt.
   lia.
Qed. 

(* OK: *)

Lemma rem_1_step :forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->  
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
     (card sr + 1 <= card s <-> 
       exds s (Iter (f m) (ndN m - card s) z))%nat. 
Proof.
simpl in |- *.
intros.
generalize (Iter_rem_aux_equation m z s).
simpl in |- *.
intro.
split.
 intro.
   generalize H0.
   elim (exds_dec s (Iter (f m) (ndN m - card s) z)).
  tauto.
  intros.
    rewrite H2 in H1.
    absurd (card s + 1 <= card s)%nat.
   lia.
   tauto.
 intro.
   generalize (LQ2 m z s H1).
   intro.
 lia.
Qed.

(* OK: *)

Lemma rem_2_steps :forall(m:fmap)(z:dart)(s:set),
 inv_hmap m -> 
   let sr:= Iter_rem_aux m z s in
   let nr:= Iter_upb_aux m z s in
     (card sr + 2 <= card s -> 
       exds (Ds s (Iter (f m) (ndN m - card s) z)) 
         (Iter (f m) (ndN m + 1 - card s) z))%nat. 
Proof.
intros.
generalize (rem_1_step m z 
   (Ds s (Iter (f m) (ndN m - card s)%nat z)) H).
simpl in |- *.
generalize (rem_1_step m z s H).
simpl in |- *.
intros.
assert (card (Iter_rem_aux m z s) + 1 <= card s)%nat.
 unfold sr in H0.
   clear H1 H2; lia.
 assert (exds s (Iter (f m) (ndN m - card s)%nat z)).
  tauto.
  generalize (Iter_rem_aux_equation m z s).
    simpl in |- *.
    elim (exds_dec s (Iter (f m) (ndN m - card s) z)).
   intros.
     assert (card (Ds s (Iter (f m) (ndN m - card s) z)) + 1 
        = card s)%nat.
    rewrite exds_card_Ds.
     clear H1 H2 H3 H4 a H5.
       lia.
     tauto.
    assert (card (Ds s (Iter (f m) (ndN m - card s) z)) 
        = card s - 1)%nat.
     clear H1 H2 H3 H4 a H5.
       lia.
     unfold sr in H0.
       rewrite H7 in H2.
       rewrite <- H5 in H2.
       assert (card (Iter_rem_aux m z s) + 1 <= card s - 1)%nat.
      clear H1 H2 H3 H4 a H5 H6 H7.
        lia.
      assert (ndN m + 1 - card s = ndN m - (card s - 1))%nat.
       clear H1 H2 H3 H4 a H5 H6 H7 H8.
         lia.
       rewrite <- H9 in H2.
         tauto.
   tauto.
Qed.

(* OK: ALL z^i FOR n0 <=i <= nr-1 EXIST IN s: *)

Definition P6(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
      exds_int m z n0 (nr - 1) s)%nat.

(* OK: LONG... *)

Lemma LP6:forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
      exds_int m z n0 (nr - 1) s)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P6 m z) _).
unfold P6 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
intro.
generalize (Iter_rem_aux_equation m z x).
simpl in |- *.
intro.
rewrite H4.
generalize H4.
simpl in |- *.
elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
 intros.
   clear H4.
   generalize 
      (exds_card_Ds x (Iter (f m) (ndN m - card x)%nat z) a).
   intro.
   generalize (H (Ds x (Iter (f m) (ndN m - card x)%nat z))).
   intros.
   generalize (rem_1_step m z x H0).
   simpl in |- *.
   intros.
   assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
  tauto.
  clear H7.
    elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) 
      (card x))%nat.
   intro.
     rewrite <- H5.
     assert (ndN m - card (Iter_rem_aux m z x) - 1 
      = ndN m - card x)%nat.
    clear H3 H4 H8.
      lia.
    rewrite H7.
      unfold exds_int in |- *.
      intros.
      assert (i = ndN m - card x)%nat.
     clear H1 H3 H4 H8 a0 H7.
       lia.
     rewrite H10.
       tauto.
   intro.
     assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
    clear H1 H3 H4.
      lia.
    generalize (rem_2_steps m z x H0 H7).
      intro.
      rewrite H4 in H6.
      assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
     clear H3 H4 H5 H8 b.
       lia.
     rewrite H10 in H6.
       rewrite <- H5.
       rewrite <- H5 in H6.
       unfold exds_int in |- *.
       intros.
       elim (eq_nat_dec (ndN m - card x) i)%nat.
      intro.
        rewrite <- a0.
        tauto.
      intro.
        assert
         (exds_int m z (ndN m + 1 - card x)
            (ndN m - card (Iter_rem_aux m z x) - 1)
            (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
       apply H6.
        unfold Rs in |- *.
          clear H1 H3 H5 H8 b H10 H11 b0.
          lia.
        tauto.
        clear H3 H5 H4 H8 H7 H10 H11 b0.
          lia.
        tauto.
       unfold exds_int in H12.
         assert (exds (Ds x (Iter (f m) 
       (ndN m - card x) z)) (Iter (f m) i z))%nat.
        apply H12.
          clear H10.
          clear H1 H3 H5 H4 H8 H7 H8 b.
          lia.
        eapply exds_Ds_exds.
          apply H13.
 tauto.
Qed.

(* OK: FOR ALL n0 < j <= nr-1, z^n0 <> z^j: 
LENGHT: SYMPLIFY: TOO MUCH lias... *)

Definition P7(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
   exds s (Iter (f m) n0 z) -> 
     forall j:nat, n0 < j <= nr - 1 ->
       Iter (f m) n0 z <> Iter (f m) j z)%nat.

Lemma LP7:forall(m:fmap)(z:dart)(s:set),
inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
   exds s (Iter (f m) n0 z) -> 
     forall j:nat, n0 < j <= nr - 1 ->
       Iter (f m) n0 z <> Iter (f m) j z)%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P7 m z) _).
unfold P7 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (LQ1 m z x).
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
 tauto.
 clear H4.
   intro.
   clear H4.

   elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) 
        (card x))%nat.
  intro.
    clear H5.
    lia.
  intro.
    assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
   lia.
   generalize (rem_2_steps m z x H0 H4).
     intro.
     clear b H5.
     elim
      (eq_dart_dec (Iter (f m) (ndN m - card x) z)
         (Iter (f m) 
         (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
    intros.
      assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
        = card x - 1)%nat.
     rewrite exds_card_Ds.
      tauto.
      tauto.
     assert (card (Ds x (Iter (f m) (ndN m - card x) z)) 
           <= ndN m)%nat.
      lia.
      generalize (LP6 m z 
          (Ds x (Iter (f m) (ndN m - card x) z)) H0 H7)%nat.
        simpl in |- *.
        intros.
        rewrite H5 in H8.
        unfold Iter_upb_aux in H8.
        generalize (Iter_rem_aux_equation m z x).
        simpl in |- *.
        elim (exds_dec x (Iter (f m) (ndN m - card x) z)).
       intros.
         clear a0.
         rewrite <- H9 in H8.
         assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
        clear H3 a H5 H7 H9.
          lia.
        rewrite H10 in H8.
          generalize (H8 H6).
          intro.
          clear H8.
          unfold exds_int in H11.
          assert
           (exds (Ds x (Iter (f m) (ndN m - card x) z))
              (Iter (f m) 
           (ndN m - card (Iter_rem_aux m z x) - 1) z))%nat.
         apply H11.
           split.
          clear H3 a H H7 H9 H10.
            lia.
          apply le_refl.
         rewrite <- a in H8.
           absurd
            (exds (Ds x (Iter (f m) (ndN m - card x) z))
               (Iter (f m) (ndN m - card x) z))%nat.
          apply not_exds_Ds.
          tauto.
       tauto.
    intros.
      elim (eq_nat_dec 
          (ndN m - card (Iter_rem_aux m z x) - 1) j)%nat.
     intro.
       rewrite <- a.
       tauto.
     intro.
       generalize (H (Ds x (Iter (f m)
          (ndN m - card x) z)))%nat.
       intro.
       assert
        (forall j : nat,
         ndN m - card (Ds x (Iter (f m) (ndN m - card x) z)) 
   < j <= ndN m - card (Iter_rem_aux m z 
          (Ds x (Iter (f m) (ndN m - card x) z))) - 1 ->
         Iter (f m) 
  (ndN m - card (Ds x (Iter (f m) (ndN m - card x) z))) z <>
         Iter (f m) j z)%nat.
      apply H5.
       unfold Rs in |- *.
         rewrite exds_card_Ds.
        clear H1 H3 b b0.
          lia.
        tauto.
       tauto.
       generalize (exds_card_Ds x 
         (Iter (f m) (ndN m - card x) z) H2)%nat.
         intro.
         rewrite H7.
         clear H3 H4 b b0 H7.
         lia.
       generalize (exds_card_Ds x 
          (Iter (f m) (ndN m - card x) z) H2)%nat.
         intro.
         rewrite H7.
         assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
        clear H3 b b0 H7.
          lia.
        rewrite H8.
          tauto.
      clear H5.
        generalize (exds_card_Ds x 
              (Iter (f m) (ndN m - card x) z) H2)%nat.
        intro.
        rewrite H5 in H7.
        generalize (Iter_rem_aux_equation m z x).
        simpl in |- *.
        elim (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
       intros.
         clear a.
         rewrite <- H8 in H7.
         assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
        clear H3 b b0 H5 H8.
          lia.
        rewrite H9 in H7.
          intro.
          assert (Iter (f m) (S (ndN m - card x)) z 
             = Iter (f m) (S j) z)%nat.
         simpl in |- *.
           rewrite H10.
           tauto.
         generalize H11.
           assert (S (ndN m - card x) = ndN m + 1 - card x)%nat.
          clear H9.
            clear H5.
            clear H3 b b0 H8 H10 H11.
            lia.
          rewrite H12.
            apply H7.
            split.
           rewrite <- H12.
             apply lt_n_S.
             tauto.
           clear H12.
             clear H9.
             clear H5.
             clear H4.
             clear H1 b H8 H10 H11.
             elim H3.
             intros.
             clear H1.
             clear H3.
             lia.
       tauto.
Qed.

(* OK: FOR ALL n0 <= i < j <= nr-1, z^i <> z^j: 
LENGHT: SYMPLIFY: TOO MUCH lias... *)

Definition P8(m:fmap)(z:dart)(s:set):Prop:= 
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
     diff_int m z n0 (nr - 1))%nat.

Lemma LP8:forall(m:fmap)(z:dart)(s:set),
 inv_hmap m ->
  (card s <= ndN m ->
   let n0:= ndN m - card s in
   let nr:= Iter_upb_aux m z s in
    exds s (Iter (f m) n0 z) -> 
     diff_int m z n0 (nr - 1))%nat.
Proof.
intros m z.
refine (well_founded_ind Rs_wf (P8 m z) _).
unfold P8 in |- *.
unfold Iter_upb_aux in |- *.
intros.
generalize (rem_1_step m z x H0).
simpl in |- *.
intro.
assert (card (Iter_rem_aux m z x) + 1 <= card x)%nat.
 tauto.
 clear H3.
   elim (eq_nat_dec (card (Iter_rem_aux m z x) + 1) 
       (card x))%nat.
  intro.
    clear H4.
    assert (ndN m - card (Iter_rem_aux m z x) - 1 
         = ndN m - card x)%nat.
   lia.
   rewrite H3.
     apply diff_int_le.
     apply le_refl.
  intro.
    assert (card (Iter_rem_aux m z x) + 2 <= card x)%nat.
   lia.
   clear b H4.
     generalize (rem_2_steps m z x H0 H3).
     intro.
     generalize (LP7 m z x H0 H1 H2).
     intro.
     unfold diff_int in |- *.
     intros.
     elim (eq_nat_dec (ndN m - card x) i)%nat.
    intro.
      rewrite <- a.
      unfold Iter_upb_aux in H5.
      apply H5.
      split.
     rewrite a.
       tauto.
     tauto.
    intro.
      assert (card (Ds x (Iter (f m) (ndN m - card x) z))
          = card x - 1)%nat.
     rewrite exds_card_Ds.
      tauto.
      tauto.
     generalize (Iter_rem_aux_equation m z x).
       simpl in |- *.
       elim (exds_dec x (Iter (f m) (ndN m - card x) z))%nat.
      intros.
        clear a.
        clear H5.
     generalize (H (Ds x (Iter (f m) (ndN m - card x) z)))%nat.
        intros.
        assert
         (diff_int m z 
         (ndN m - card (Ds x (Iter (f m) (ndN m - card x) z)))
            (ndN m -
             card (Iter_rem_aux m z 
         (Ds x (Iter (f m) (ndN m - card x) z))) -
             1))%nat.
       apply H5.
        unfold Rs in |- *.
          apply exds_card_Ds_inf.
          tauto.
        tauto.
        rewrite H7.
          lia.
        rewrite H7.
          assert (ndN m - (card x - 1) = ndN m + 1 - card x)%nat.
         clear H5.
           clear H.
           clear H8.
           lia.
         rewrite H9.
           tauto.
       clear H5 H.
         rewrite <- H8 in H9.
         unfold diff_int in H9.
         rewrite H7 in H9.
         apply H9.
         split.
        clear H8 H9.
          clear H1 H3 H4.
          clear H0.
          lia.
        tauto.
      tauto.
Qed.

(* ALL DARTS IN AN f-ORBIT ARE DISTINCT: *)  

Definition diff_orb(m:fmap)(z:dart):Prop:=
 let nr:= Iter_upb_aux m z (fmap_to_set m) in
  (diff_int m z 0 (nr - 1))%nat.

Theorem exd_diff_orb:forall(m:fmap)(z:dart),
   inv_hmap m -> exd m z ->
      diff_orb m z.
intros.
unfold diff_orb in |- *.
generalize (nd_card m).
intro.
assert (ndN m - card (fmap_to_set m) = 0)%nat.
 rewrite H1.
   lia.
 cut
  (diff_int m z (ndN m - card (fmap_to_set m))
     (Iter_upb_aux m z (fmap_to_set m) - 1))%nat.
  rewrite H2.
    tauto.
  apply LP8.
   tauto.
   rewrite H1.
     apply le_refl.
   rewrite H2.
     simpl in |- *.
     generalize (exd_exds m z).
     tauto.
Qed.

(* OK: nr IS A PERIOD OF THE f-ORBIT 
(IN FACT, IT IS THE LOWEST ONE, SINCE n0 = 0 
AND ALL z^i DIFFER FROM z = z^n0 = z^0, FOR n0 < i <= nr-1) *)

Theorem Iter_upb_period:forall(m:fmap)(z:dart),
 inv_hmap m -> exd m z ->
  let nr:= Iter_upb m z in
    Iter (f m) nr z = z.
Proof.
simpl in |- *.
intros.
generalize (ex_i_upb m z H H0).
simpl in |- *.
intros.
elim H1.
intros i Hi.
clear H1.
elim (eq_nat_dec i 0%nat).
 intro.
   rewrite a in Hi.
   simpl in Hi.
   symmetry  in |- *.
   tauto.
 intro.
   decompose [and] Hi.
   clear Hi.
   assert (f_1 m (Iter (f m) i z) =
         f_1 m (Iter (f m) (Iter_upb m z) z)).
  rewrite H2.
    tauto.
  set (i1 := (i - 1)%nat) in |- *.
    set (nr1 := (Iter_upb m z - 1)%nat) in |- *.
    assert (i = S i1).
   unfold i1 in |- *.
     lia.
   assert (Iter_upb m z = S nr1).
    unfold nr1 in |- *.
      lia.
    rewrite H5 in H3.
      rewrite H4 in H3.
      simpl in H3.
      rewrite f_1_f in H3.
     rewrite f_1_f in H3.
      unfold i1 in H3.
        unfold nr1 in H3.
        absurd (Iter (f m) (i - 1)%nat z = 
     Iter (f m) (Iter_upb m z - 1)%nat z).
       generalize (LP8 m z (fmap_to_set m) H).
         simpl in |- *.
         intros.
         unfold diff_int in H6.
         assert
          (forall i j : nat,
           ndN m - card (fmap_to_set m) <= i /\
           i < j <= Iter_upb_aux m z (fmap_to_set m) - 1 ->
           Iter (f m) i z <> Iter (f m) j z)%nat.
        apply H6.
         rewrite nd_card.
           apply le_refl.
         assert (ndN m - card (fmap_to_set m) = 0)%nat.
          rewrite nd_card.
            simpl in |- *.
            lia.
          rewrite H7.
            simpl in |- *.
            generalize (exd_exds m z).
            tauto.
        apply H7.
          split.
         clear H6.
           clear H7.
           clear H2.
           rewrite nd_card.
           lia.
         clear H7 H6.
           clear H2.
           split.
          lia.
          unfold Iter_upb in |- *.
            unfold Iter_upb_aux in |- *.
            unfold Iter_rem in |- *.
            apply le_refl.
       tauto.
      tauto.
      generalize (exd_Iter_f m nr1 z).
        tauto.
     tauto.
     generalize (exd_Iter_f m i1 z).
       tauto.
Qed.

(* WE HAVE: z^(i + n*p) = z^i FOR ALL i *)

Lemma Iter_period:forall(m:fmap)(z:dart)(i n:nat),
 inv_hmap m -> exd m z ->
  let p:= Iter_upb m z in
    Iter (f m) (i + n*p)%nat z =  Iter (f m) i z.
Proof.
intros.
intros.
assert (Iter (f m) p z = z).
 unfold p in |- *.
   apply Iter_upb_period.
  tauto.
  tauto.
 rewrite Iter_plus_mult.
  trivial.
  assumption.
  assumption.
  assumption.
Qed.

(* WE HAVE: z^i = z^(i mod p) FOR ALL i *)



(* RECALL:
modulo
     : forall n : nat,
       n > 0 ->
       forall m : nat, 
         {r : nat | exists q : nat, m = q * n + r /\ n > r}
*)

Lemma mod_p:forall(m:fmap)(z:dart)(i:nat),
 inv_hmap m -> exd m z ->
  let p := Iter_upb m z in
   {j :nat | Iter (f m) i z  = Iter (f m) j z /\ (j < p)%nat}.
Proof.
intros.
assert (p > 0)%nat.
 unfold p in |- *.
   generalize (upb_pos m z H0).
   intro.
   lia.
 generalize (modulo p H1 i).
   intro.
   elim H2.
   intros r Hr.
   split with r.
   elim Hr.
   intros q Hq.
   elim Hq.
   clear Hq.
   intros.
   split.
  rewrite H3.
    rewrite plus_comm.
    unfold p in |- *.
    rewrite Iter_period.
   trivial.
   tauto.
   tauto.
  lia.
Qed.



(* ALL DARTS IN AN f-ORBIT HAVE THE SAME PERIOD: *) 

Lemma period_uniform : forall(m:fmap)(z:dart)(i:nat),
 inv_hmap m -> exd m z ->
    Iter_upb m z = Iter_upb m (Iter (f m) i z).
Proof.
intros.
set (zi := Iter (f m) i z) in |- *.
set (p := Iter_upb m z) in |- *.
set (q := Iter_upb m zi) in |- *.
generalize (Iter_upb_period m z H H0).
simpl in |- *.
fold p in |- *.
intro.
assert (exd m zi).
 unfold zi in |- *.
   generalize (exd_Iter_f m i z H).
   tauto.
 generalize (Iter_upb_period m zi H H2).
   simpl in |- *.
   fold q in |- *.
   intro.
   assert (Iter (f m) (i + q)%nat z = Iter (f m) q zi).
  unfold zi in |- *.
    rewrite plus_comm.
    apply Iter_comp.
  assert (Iter (f m) q z = z).
   apply (Iter_plus m z q i H H0).
     fold zi in |- *.
     rewrite plus_comm.
     rewrite <- H3.
     tauto.
   assert (Iter (f m) p zi = zi).
    unfold zi in |- *.
      rewrite <- Iter_comp.
      rewrite plus_comm.
      assert (i + p = i + 1 * p)%nat.
     lia.
     rewrite H6.
       unfold p in |- *.
       rewrite Iter_period.
      trivial.
      trivial.
      trivial.
    clear H4.
      elim (lt_eq_lt_dec p q).
     intro.
       elim a.
      clear a.
        intro.
        generalize (exd_diff_orb m zi H H2).
        unfold diff_orb in |- *.
        unfold Iter_upb in q.
        unfold Iter_rem in q.
        unfold Iter_upb_aux in |- *.
        fold q in |- *.
        unfold diff_int in |- *.
        intros.
        absurd (Iter (f m) p zi = zi).
       intro.
         symmetry  in H7.
         replace zi with (Iter (f m) 0%nat zi) in H7.
        generalize H7.
          clear H7.
          apply H4.
          split.
         lia.
         split.
          unfold p in |- *.
            apply upb_pos.
            tauto.
          lia.
        simpl in |- *.
          trivial.
       tauto.
      tauto.
     intro.
       generalize (exd_diff_orb m z H H0).
       unfold diff_orb in |- *.
       unfold Iter_upb in p.
       unfold Iter_rem in p.
       unfold Iter_upb_aux in |- *.
       fold p in |- *.
       unfold diff_int in |- *.
       intros.
       symmetry  in H5.
       absurd (z = Iter (f m) q z).
      replace z with (Iter (f m) 0%nat z).
       apply H4.
         split.
        lia.
        split.
         unfold q in |- *.
           apply upb_pos.
           tauto.
         lia.
       simpl in |- *.
         trivial.
      tauto.
Qed.

(* UNICITY OF THE INDICE mod p: *)

Lemma unicity_mod_p:forall(m:fmap)(z:dart)(j k:nat),
 inv_hmap m -> exd m z ->
  let p := Iter_upb m z in
   (j < p)%nat -> (k < p)%nat -> 
    Iter (f m) j z = Iter (f m) k z -> j = k.
Proof.
intros.
generalize (exd_diff_orb m z H H0).
unfold diff_orb in |- *.
unfold Iter_upb in p.
unfold Iter_upb_aux in |- *.
unfold Iter_rem in p.
fold p in |- *.
unfold diff_int in |- *.
intros.
elim (le_gt_dec j k).
 elim (eq_nat_dec j k).
  intros.
    tauto.
  intros.
    absurd (Iter (f m) j z = Iter (f m) k z).
   apply (H4 j k).
     lia.
   tauto.
 intro.
   symmetry in H3.
   absurd (Iter (f m) k z = Iter (f m) j z).
  apply (H4 k j).
    lia.
  tauto. 
Qed.

(*===========================================================
                 PATHS in f-ORBITS:
==========================================================*)

(* REFLEXIVE EXISTENCE OF A PATH: *)

Definition expo(m:fmap)(z t:dart):Prop:=
   exd m z /\ exists i:nat, Iter (f m) i z = t.

(* FOR THE DECIDABILITY: ... *)

Definition expo1
 (m:fmap)(z t:dart):Prop:=
   exd m z /\
     let p:= Iter_upb m z in 
       exists j:nat, (j < p)%nat /\ Iter (f m) j z = t.

Lemma expo_expo1: 
  forall(m:fmap)(z t:dart), inv_hmap m ->
    (expo m z t <-> expo1 m z t). 
Proof.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
unfold expo in |- *.
unfold expo1 in |- *.
intros.
split.
 intros.
   elim H0.
   clear H0.
   intros.
   split.
  tauto.
  elim H1.
    intros i Hi.
    clear H1.
    generalize (mod_p m z i H H0).
    simpl in |- *.
    intros.
    elim H1.
    intros j Hj.
    split with j.
    split.
   tauto.
   rewrite Hi in Hj.
     symmetry  in |- *.
     tauto.
 intros.
   elim H0.
   clear H0.
   intros.
   split.
  tauto.
  elim H1.
    intros.
    split with x.
    tauto.
Qed.

(* OK, GIVES THE "SMALLEST" INDICE j ST zj = zi: *)

Definition modulo(m:fmap)(z:dart)(i:dart)
    (hi:inv_hmap m)(he:exd m z):nat.
Proof.
intros.
assert
 (let p := Iter_upb m z in
  {j : nat | Iter (f m) i z = Iter (f m) j z /\ (j < p)%nat}).
 apply mod_p.
  tauto.
  tauto.
 simpl in H.
   elim H.
   intros.
   apply x.
Defined.

(* EXISTENCE OF THE EXTREMITY DARTS: *)

Lemma expo_exd:
  forall(m:fmap)(z t:dart),
   inv_hmap m -> expo m z t -> exd m t.
Proof.
unfold expo in |- *.
intros.
decompose [and] H0.
elim H2.
intros i Hi.
rewrite <- Hi.
generalize (exd_Iter_f m i z).
tauto.
Qed.

(* REFLEXIVITY: *)

Lemma expo_refl:
  forall(m:fmap)(z:dart), exd m z -> expo m z z.
Proof.
intros.
unfold expo in |- *.
split.
 tauto.
 split with 0%nat.
   simpl in |- *.
   tauto.
Qed.

(* TRANSITIVITY: *)

Lemma expo_trans:
  forall(m:fmap)(z t u:dart),
  expo m z t -> expo m t u -> expo m z u.
Proof.
unfold expo in |- *.
intros.
intuition.
elim H2.
intros j Hj.
elim H3.
intros i Hi.
split with (i + j)%nat.
rewrite Iter_comp.
rewrite Hj.
tauto.
Qed.

(* SYMMETRY: OK!! *)

Lemma expo_symm:forall(m:fmap)(z t:dart),
  inv_hmap m -> 
     expo m z t -> expo m t z.
Proof.
intros m z t Hm He.
assert (exd m t).
 apply expo_exd with z.
  tauto.
  tauto.
 unfold expo in |- *.
   unfold expo in He.
   intuition.
   elim H1.
   intros i Hi.
   rewrite <- Hi.
   clear H1.
   generalize (mod_p m z i Hm H0).
   intro.
   simpl in H1.
   elim H1.
   intros r Hr.
   elim Hr.
   clear Hr H1.
   intros.
   split with (Iter_upb m z - r)%nat.
   rewrite H1.
   rewrite <- Iter_comp.
   assert (Iter_upb m z - r + r = Iter_upb m z)%nat.
  lia.
  rewrite H3.
    apply Iter_upb_period.
   tauto.
   tauto.
Qed.

(* THERE EXISTS j <= n S.T. zj = t: INDUCTIVE DEF. *)

Fixpoint ex_j
 (m:fmap)(z t:dart)(n:nat){struct n}:Prop:=
match n with
   0%nat => z = t
 | S n0 => Iter (f m) n z = t \/ ex_j m z t n0
end. 

Lemma ex_j_dec:
 forall(m:fmap)(z t:dart)(n:nat),
  {ex_j m z t n} + {~ex_j m z t n}.
Proof.
induction n.
 simpl in |- *.
   apply eq_dart_dec.
 simpl in |- *.
   generalize (eq_dart_dec (f m (Iter (f m) n z)) t).
   tauto.
Qed.

(* THERE EXISTS j <= n S.T. zj = t: COMMON DEF. EQUIVALENT TO INDUCTIVE DEF.: *)

Lemma ex_j_exist_j:forall(m:fmap)(z t:dart)(n:nat),
  ex_j m z t n <-> 
     exists j :nat, (j <= n)%nat /\ Iter (f m) j z = t.
Proof.
induction n.
 simpl in |- *.
   split.
  intro.
    split with 0%nat.
    split.
   lia.
   simpl in |- *.
     tauto.
  intro.
    elim H.
    intros j Hj.
    intuition.
    inversion H0.
    rewrite H2 in H1.
    simpl in |- *.
    simpl in H1.
    tauto.
 simpl in |- *.
   split.
  intro.
    elim H.
   intro.
     split with (S n).
     split.
    clear IHn H; lia.
    simpl in |- *.
      tauto.
   intro.
     assert (exists j : nat, (j <= n)%nat 
            /\ Iter (f m) j z = t).
    tauto.
    elim H1.
      intros j Hj.
      split with j.
      split.
     clear IHn H; lia.
     tauto.
  intros.
    elim H.
    intros j Hj.
    elim (eq_nat_dec j (S n)).
   intro.
     rewrite a in Hj.
     simpl in Hj.
     tauto.
   intro.
     assert (exists j : nat, (j <= n)%nat 
        /\ Iter (f m) j z = t).
    split with j.
      split.
     clear IHn H;lia.
     tauto.
    tauto.
Qed.

(* t IS A ITERATED SUCC OF z IN AN ORBIT IS EQUIVALENT TO: there exists j <= p-1 s.t. zj = t: *)

Lemma expo1_ex_j: 
  forall(m:fmap)(z t:dart), inv_hmap m -> exd m z ->
  let p:= Iter_upb m z in
    (ex_j m z t (p - 1)%nat <-> expo1 m z t).
Proof.
intros.
generalize (Iter_upb_period m z H H0).
generalize (upb_pos m z H0).
rename H into hm.
rename H0 into hz.
fold p in |- *.
intros Hp1 Hp2.
generalize (ex_j_exist_j m z t (p - 1)%nat).
unfold expo1 in |- *.
fold p in |- *.
intros.
split.
 intro.
   assert (exists j : nat, (j <= p - 1)%nat 
       /\ Iter (f m) j z = t).
  tauto.
  elim H1.
    intros j Hj.
    split.
   tauto.
   split with j.
     split.
    clear H H0 H1; lia.
    tauto.
 intro.
   elim H0.
   intros.
   elim H2.
   clear H0 H2.
   intros i Hj.
   assert (exists j : nat, (j <= p - 1)%nat 
        /\ Iter (f m) j z = t).
  split with i.
    split.
   clear H H1; lia.
   tauto.
  tauto.
Qed.

(* DECIDABILITY OF expo1: *)

Lemma expo1_dec : 
  forall (m:fmap)(z t:dart), 
   inv_hmap m -> exd m z ->
     {expo1 m z t} + {~expo1 m z t}.
Proof.
intros.
set (p := Iter_upb m z) in |- *.
generalize (ex_j_dec m z t (p - 1)).
intro.
elim H1.
 intro.
   left.
   generalize (expo1_ex_j m z t H H0).
   simpl in |- *.
   fold p in |- *.
   tauto.
 intro.
   right.
   intro.
   generalize (expo1_ex_j m z t H H0).
   simpl in |- *.
   fold p in |- *.
   tauto.
Qed.

(* DECIDABILITY: OK!! *)

Lemma expo_dec: forall(m:fmap)(z t:dart),
  inv_hmap m ->  
    {expo m z t} + {~expo m z t}.
Proof.
intros m z t hm.
generalize (expo_expo1 m z t hm).
generalize (expo1_dec m z t hm).
intros.
elim (exd_dec m z).
 tauto.
 unfold expo in |- *.
   tauto.
Qed.

(* ALL DARTS OF AN ORBIT HAVE THE SAME period: *)

Lemma period_expo : forall(m:fmap)(z t:dart),
 inv_hmap m -> expo m z t ->
    Iter_upb m z = Iter_upb m t.
Proof.
unfold expo in |- *.
intros.
elim H0.
clear H0.
intros.
elim H1.
intros i Hi.
rewrite <- Hi.
apply period_uniform.
 tauto.
 tauto.
Qed.

(*===========================================================
                between in f-ORBITS:
==========================================================*)

(* v IS between z AND t IN AN f-ORBIT: *)

Definition between(m:fmap)(z v t:dart):Prop:=
 inv_hmap m -> exd m z ->  
  exists i:nat, exists j:nat, 
   Iter (f m) i z = v /\
     Iter (f m) j z = t /\
       (i <= j < Iter_upb m z)%nat.

(* OK: *)

Lemma between_expo1:forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> 
    between m z v t ->
      expo1 m z v /\ expo1 m z t. 
Proof.
unfold between in |- *.
intros.
generalize (H1 H H0).
clear H1.
intro.
elim H1.
intros i Hi.
clear H1.
elim Hi.
clear Hi.
intros j Hj.
decompose [and] Hj.
clear Hj.
unfold expo1 in |- *.
split.
 split.
  tauto.
  split with i.
    split.
   lia.
   tauto.
 split.
  tauto.
  split with j.
    split.
   tauto.
   tauto.
Qed.

Lemma between_expo:forall(m:fmap)(z v t:dart),
  inv_hmap m -> exd m z -> 
    between m z v t ->
      expo m z v /\ expo m z t. 
Proof.
intros.
generalize (between_expo1 m z v t H H0 H1).
intros.
generalize (expo_expo1 m z v H).
generalize (expo_expo1 m z t H).
tauto.
Qed.

(* OK: *)

Lemma between_expo_refl_1:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (between m z z t <-> expo1 m z t). 
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   generalize (H1 H H0).
   clear H1.
   intro.
   elim H1.
   clear H1.
   intros i Hi.
   elim Hi.
   intros j Hj.
   split.
  tauto.
  split with j.
    tauto.
 intros.
   intuition.
   elim H5.
   intros i Hi.
   clear H5.
   split with 0%nat.
   split with i.
   simpl in |- *.
   split.
  tauto.
  split.
   tauto.
lia.
Qed.

(* IDEM: *)

Lemma between_expo_refl_2:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (between m z t t <-> expo1 m z t). 
Proof.
intros.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   generalize (H1 H H0).
   clear H1.
   intro.
    intuition.
   elim H1.
   clear H1.
   intros i Hi.
   elim Hi.
   intros j Hj.
   split with j.
    tauto.
intros.
  decompose [and] H1.
  clear H1.
  elim H5.
  clear H5.
  intros j Hj.
  split with j.
  split with j.
  split.
  tauto.
split.
  tauto.
split.
  lia.
 tauto.
Qed.

Lemma expo_between_1:forall(m:fmap)(z t:dart),
  inv_hmap m -> exd m z -> 
    (expo1 m z t <-> between m z t (f_1 m z)).  
Proof.
intros.
rename H0 into Ez.
unfold between in |- *.
unfold expo1 in |- *.
split.
 intros.
   intuition.
   elim H4.
   intros j Hj.
   clear H4.
   split with j.
   split with (Iter_upb m z - 1)%nat.
   split.
  tauto.
  split.
   set (nr := Iter_upb m z) in |- *.
     assert (Iter (f m) nr z = z).
    unfold nr in |- *.
      apply Iter_upb_period.
     tauto.
     tauto.
    assert (0 < nr)%nat.
     unfold nr in |- *.
       apply upb_pos.
       tauto.
     assert (f_1 m (Iter (f m) nr z) = f_1 m z).
      rewrite H0.
        tauto.
      rewrite <- Iter_f_f_1.
       simpl in |- *.
         tauto.
       tauto.
       tauto.
       lia.
   lia.
 intros.
   split.
  tauto.
  intuition.
    elim H0.
    clear H0.
    intros i Hi.
    elim Hi.
    intros j Hj.
    split with i.
    split.
   lia.
   tauto.
Qed.

Lemma expo_between_3:forall(m:fmap)(x y z:dart),
  inv_hmap m -> expo1 m x y -> expo1 m x z -> 
    between m x z y \/ between m (f m y) z (f_1 m x). 
Proof.
unfold expo1 in |- *.
unfold between in |- *.
intros.
intuition.
elim H3.
clear H3.
intros i Hi.
elim H4.
intros j Hj.
clear H4.
elim (le_lt_dec j i).
 intro.
   left.
   intros.
   split with j.
   split with i.
   split.
  tauto.
  split.
   tauto.
   lia.
 intro.
   right.
   intros.
   intuition.
   split with (j - i - 1)%nat.
   split with (Iter_upb m x - (2 + i))%nat.
   assert (Iter_upb m (f m y) = Iter_upb m x).
  rewrite <- H5.
    assert (Iter (f m) (S i) x = f m (Iter (f m) i x)).
   simpl in |- *.
     tauto.
   rewrite <- H8.
     rewrite <- period_uniform.
    tauto.
    tauto.
    tauto.
  split.
   rewrite <- H5.
     assert (f m (Iter (f m) i x) = Iter (f m) (S i) x).
    simpl in |- *.
      tauto.
    rewrite H9.
      rewrite <- Iter_comp.
      assert (j - i - 1 + S i = j)%nat.
     lia.
     rewrite H10.
       tauto.
   split.
    rewrite <- H5.
      assert (f m (Iter (f m) i x) = Iter (f m) (S i) x).
     simpl in |- *.
       tauto.
     rewrite H9.
       rewrite <- Iter_comp.
       assert (Iter_upb m x - (2 + i) + S i = 
                Iter_upb m x - 1)%nat.
      lia.
      rewrite H10.
        rewrite <- f_1_Iter_f.
       assert (S (Iter_upb m x - 1) = Iter_upb m x)%nat.
        lia.
        rewrite H11.
          rewrite Iter_upb_period.
         tauto.
         tauto.
         tauto.
       tauto.
       tauto.
    rewrite H8.
      lia.
Qed.

End Mf.

(*=======================================================
         
           INSTANCIATION OF Mf TO A_k_orbits

========================================================*)

(* SIGNATURE FOR A DIMENSION: *)

Module Type Sigd.
Parameter k:dim.
End Sigd.

(* FUNCTOR: *)

Module McA(Md:Sigd)<:Sigf.
Definition f := fun(m:fmap)(z:dart) => cA m Md.k z.
Definition f_1 := fun(m:fmap)(z:dart) => cA_1 m Md.k z.
Definition exd_f := 
   fun(m:fmap)(z:dart) => exd_cA m Md.k z. 
Definition exd_f_1 := 
   fun(m:fmap)(z:dart) => exd_cA_1 m Md.k z. 
Definition bij_f := 
   fun(m:fmap)(h:inv_hmap m) => bij_cA m Md.k h.
Definition bij_f_1 := 
   fun(m:fmap)(h:inv_hmap m) => bij_cA_1 m Md.k h.
Definition f_1_f := fun(m:fmap)(z:dart) => cA_1_cA m Md.k z.
Definition f_f_1 := fun(m:fmap)(z:dart) => cA_cA_1 m Md.k z.
End McA.

(* INSTANCIATIONS OF Sigd: *)

Module Md0<:Sigd.
Definition k:=zero.
End Md0.

Module Md1<:Sigd.
Definition k:=one.
End Md1.

(* OK, BUT THE DIRECT COMPOSITION IS IMPOSSIBLE... : *)

Module McA0:=McA Md0.

Module MA0:= Mf McA0.

Module McA1:=McA Md1.

Module MA1:= Mf McA1.

(*========================================================
       FACE OPERATIONS IN HMAPS: F, F_1, cF, cF_1
========================================================*)

(* Following operations are designed for hmaps,
but are defined on fmap for convenience *)

(* Successor F in a face - direct version, 
designed for hmaps: *)

Definition F(m:fmap)(z:dart):=
  A_1 m one (A_1 m zero z).

(* To have a successor in a (direct) face for x: *)

Definition succf(m:fmap)(z:dart):Prop:=
  pred m zero z /\ pred m one (A_1 m zero z).

(* Decidability of succf:*)

Lemma succf_dec :
  forall (m:fmap)(z:dart),
    {succf m z}+{~succf m z}.
Proof.
intros.
unfold succf in |- *.
elim (pred_dec m one (A_1 m zero z)).
 elim (pred_dec m zero z).
  tauto.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma succf_exd : forall (m:fmap)(z:dart),
  inv_hmap m -> succf m z -> exd m z.
Proof.
unfold succf in |- *.
intros.
unfold pred in H0.
elim (exd_dec m z).
 tauto.
 intro.
   elim H0.
   intros.
   clear H0.
   elim H1.
   apply not_exd_A_1_nil.
  tauto.
  tauto.
Qed.

(* Predecessor in a face - direct version: *)

Definition F_1 (m:fmap)(z:dart):=
  A m zero (A m one z).

(* To have a predecessor in a (direct) face for z: *)

Definition predf(m:fmap)(z:dart):Prop:=
  succ m one z /\ succ m zero (A m one z).

(* Decidability of succf: *)

Lemma predf_dec :
  forall (m:fmap)(z:dart),
    {predf m z}+{~predf m z}.
Proof.
unfold predf in |- *.
intros.
generalize (succ_dec m one z).
generalize (succ_dec m zero (A m one z)).
 tauto.
Qed.

Lemma predf_exd : forall (m:fmap)(z:dart),
  inv_hmap m -> predf m z -> exd m z.
Proof.
unfold predf in |- *.
intros.
apply succ_exd with one.
  tauto.
 tauto.
Qed.

(* OK: *)

Lemma F_nil : forall m:fmap,
    inv_hmap m -> F m nil = nil.
Proof.
intros.
unfold F in |- *.
assert (A_1 m zero nil = nil).
 apply A_1_nil.
   tauto.
 rewrite H0.
   apply A_1_nil.
   tauto.
Qed.

(* IDEM: *)

Lemma F_1_nil : forall m:fmap,
    inv_hmap m -> F_1 m nil = nil.
Proof.
intros.
unfold F_1 in |- *.
assert (A m one nil = nil).
 apply A_nil.
   tauto.
 rewrite H0.
   apply A_nil.
   tauto.
Qed.

(* OK: *)

Lemma succf_exd_F : forall (m:fmap)(z:dart),
  inv_hmap m -> succf m z -> exd m (F m z).
Proof.
unfold succf in |- *.
unfold F in |- *.
intros.
apply pred_exd_A_1.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma predf_exd_F_1 : forall (m:fmap)(z:dart),
    inv_hmap m -> predf m z -> exd m (F_1 m z).
Proof.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
apply succ_exd_A.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma succf_F: forall (m:fmap)(z:dart),
  inv_hmap m -> (succf m z <-> F m z <> nil).
Proof.
intros.
unfold succf in |- *.
unfold F in |- *.
unfold pred in |- *.
 intuition.
rewrite H1 in H0.
apply H0.
apply A_1_nil.
 tauto.
Qed.

Lemma predf_F_1: forall (m:fmap)(z:dart),
  inv_hmap m -> (predf m z <-> F_1 m z <> nil).
Proof.
intros.
unfold predf in |- *.
unfold F_1 in |- *.
unfold succ in |- *.
 intuition.
rewrite H1 in H0.
apply H0.
apply A_nil.
 tauto.
Qed.

(* OK: *)

Lemma not_exd_F_nil : forall (m:fmap)(z:dart),
    inv_hmap m -> ~exd m z -> F m z = nil.
Proof.
unfold F in |- *.
intros.
apply not_exd_A_1_nil.
 tauto.
 assert (A_1 m zero z = nil).
  apply not_exd_A_1_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

Lemma not_exd_F_1_nil : forall (m:fmap)(z:dart),
    inv_hmap m -> ~exd m z -> F_1 m z = nil.
Proof.
unfold F_1 in |- *.
intros.
apply not_exd_A_nil.
 tauto.
 assert (A m one z = nil).
  apply not_exd_A_nil.
   tauto.
   tauto.
  rewrite H1.
    apply not_exd_nil.
    tauto.
Qed.

(* F and F_1 are inverses: *)

Lemma F_F_1 : forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> exd m (F_1 m z) ->
     F m (F_1 m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_1_A.
 rewrite A_1_A.
  tauto.
  tauto.
  unfold succ in |- *.
    intro.
    rewrite H2 in H1.
    rewrite A_nil in H1.
   absurd (exd m nil).
    apply not_exd_nil.
      tauto.
    tauto.
   tauto.
 tauto.
 unfold succ in |- *.
   intro.
   rewrite H2 in H1.
   absurd (exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
Qed.

(* IDEM: *)

(* ATTENTION !! PROPAGATION DE exd m (F_1 m z) AU LIEU DE
exd m (F m z) *)

Lemma F_1_F : forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> exd m (F m z) ->
    F_1 m (F m z) = z.
Proof.
unfold F in |- *; unfold F_1 in |- *.
intros.
rewrite A_A_1.
 rewrite A_A_1.
  tauto.
  tauto.
  unfold pred in |- *.
    intro.
    rewrite H2 in H1.
    rewrite A_1_nil in H1.
   absurd (exd m nil).
    apply not_exd_nil.
      tauto.
    tauto.
   tauto.
 tauto.
 unfold pred in |- *.
   intro.
   rewrite H2 in H1.
   absurd (exd m nil).
  apply not_exd_nil.
    tauto.
  tauto.
Qed.

(* OK: *)

Lemma inj_F_succf :
   forall m:fmap, inv_hmap m ->
      inj_dart (succf m) (F m).
Proof.
intros.
unfold inj_dart in |- *.
unfold succf in |- *.
unfold F in |- *.
intros.
 intuition.
generalize (inj_A_1 m zero H).
unfold inj_dart in |- *.
intro.
apply H1.
  tauto.
 tauto.
generalize (inj_A_1 m one H).
  unfold inj_dart in |- *.
  intro.
  apply H6.
  tauto.
 tauto.
 tauto.
Qed.

(* IDEM:*)

Lemma inj_F_1_predf :
 forall m:fmap, inv_hmap m ->
      inj_dart (predf m) (F_1 m).
Proof.
intros.
unfold inj_dart in |- *.
unfold predf in |- *.
unfold F_1 in |- *.
intros.
 intuition.
generalize (inj_A m one H).
unfold inj_dart in |- *.
intro.
apply H1.
  tauto.
 tauto.
generalize (inj_A m zero H).
  unfold inj_dart in |- *.
  intro.
  apply H6.
  tauto.
 tauto.
 tauto.
Qed.

(*=========================================================
                 CLOSURES cF, cF_1 OF F, F_1 :
==========================================================*)

(* SUCCESSOR IN A COMPLETED FACE: *)

Definition cF (m:fmap)(z:dart):=
  cA_1 m one (cA_1 m zero z).

Definition cF_1 (m:fmap)(z:dart):=
  cA m zero (cA m one z).

Lemma exd_cF_not_nil : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> cF m z <> nil).
Proof.
unfold cF in |- *.
intros.
split.
 intro.
   assert (cA_1 m zero z <> nil).
  generalize (succ_pred_clos m zero z H H0).
    tauto.
  generalize (succ_pred_clos m one (cA_1 m zero z) H).
    intros.
    assert (exd m (cA_1 m zero z)).
   generalize (exd_cA_cA_1 m zero z H H0).
     tauto.
   tauto.
intro.
   assert (exd m (cA_1 m zero z)).
  eapply cA_1_exd.
   tauto.
   apply H0.
  eapply exd_cA_1_exd.
   tauto.
   apply H1.
Qed.

(* Idem: *)

Lemma exd_cF_1_not_nil : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> cF_1 m z <> nil).
Proof.
intros.
split.
 intro.
   assert (cA m one z <> nil).
  generalize (exd_cA m one z).
    intro.
    apply exd_not_nil with m.
    tauto.
   tauto.
 assert (exd m (cA m one z)).
  generalize (exd_cA_cA_1 m one z H H0).
     tauto.
 generalize (succ_pred_clos m zero (cA m one z) H H2).
    tauto.
intro.
  unfold cF_1 in H0.
  apply exd_cA_exd with one.
  tauto.
 eapply cA_exd.
    tauto.
  apply H0.
Qed.

Lemma exd_cF : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (cF m z)).
Proof.
unfold cF in |- *.
intros.
split.
 intro.
   assert (exd m (cA_1 m zero z)).
  generalize (exd_cA_cA_1 m zero z H H0).
    tauto.
  generalize (exd_cA_cA_1 m one (cA_1 m zero z) H H1).
    tauto.
 intro.
   assert (exd m (cA_1 m zero z)).
  eapply exd_cA_1_exd.
   tauto.
   apply H0.
  eapply exd_cA_1_exd.
   tauto.
   apply H1.
Qed.

(* IDEM: *)

Lemma exd_cF_1 : forall (m:fmap)(z:dart),
  inv_hmap m -> (exd m z <-> exd m (cF_1 m z)).

Proof.
unfold cF_1 in |- *.
intros.
split.
 intro.
   assert (exd m (cA m one z)).
  generalize (exd_cA_cA_1 m one z H H0).
    tauto.
  generalize (exd_cA_cA_1 m zero (cA m one z) H H1).
    tauto.
 intro.
   assert (exd m (cA m one z)).
  eapply exd_cA_exd.
   tauto.
   apply H0.
  eapply exd_cA_exd.
   tauto.
   apply H1.
Qed.

Lemma inj_cF :
  forall (m:fmap), inv_hmap m ->
      inj_dart (exd m) (cF m).
Proof.
unfold inj_dart in |- *.
unfold cF in |- *.
intros.
generalize inj_cA_1.
intros.
generalize (H3 m zero H).
unfold inj_dart in |- *.
intros.
eapply H4.
 tauto.
 tauto.
generalize (H3 m one H).
unfold inj_dart in |- *.
intro.
 eapply H5.
  generalize (exd_cA_cA_1 m zero x).
    tauto.
  generalize (exd_cA_cA_1 m zero x').
    tauto.
tauto.
Qed.

(* IDEM: *)

Lemma inj_cF_1 :
  forall (m:fmap), inv_hmap m ->
    inj_dart (exd m) (cF_1 m).
Proof.
unfold inj_dart in |- *.
unfold cF_1 in |- *.
intros.
generalize inj_cA.
intros.
generalize (H3 m one H).
unfold inj_dart in |- *.
intros.
eapply H4.
 tauto.
 tauto.
generalize (H3 m zero H).
unfold inj_dart in |- *.
intro.
 eapply H5.
  generalize (exd_cA_cA_1 m one x).
    tauto.
  generalize (exd_cA_cA_1 m one x').
    tauto.
tauto.
Qed.

Lemma cF_cF_1:forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> cF m (cF_1 m z) = z.
Proof.
intros.
unfold cF in |- *.
unfold cF_1 in |- *.
rewrite cA_1_cA.
 rewrite cA_1_cA.
  tauto.
  tauto.
  tauto.
 tauto.
 generalize (exd_cA_cA_1 m one z H H0).
   tauto.
Qed.

Lemma cF_1_cF:forall (m:fmap)(z:dart),
  inv_hmap m -> exd m z -> cF_1 m (cF m z) = z.
Proof.
intros.
unfold cF in |- *.
unfold cF_1 in |- *.
rewrite cA_cA_1.
 rewrite cA_cA_1.
  tauto.
  tauto.
  tauto.
 tauto.
 generalize (exd_cA_cA_1 m zero z H H0).
   tauto.
Qed.

Lemma surj_cF :
  forall (m:fmap), inv_hmap m ->
      surj_dart (exd m) (cF m).
Proof.
unfold surj_dart in |- *.
intros.
split with (cF_1 m y).
rewrite cF_cF_1.
 split.
  generalize (exd_cF_1 m y).
    tauto.
  tauto.
 tauto.
 tauto.
Qed.

Lemma bij_cF :
  forall (m:fmap), inv_hmap m ->
      bij_dart (exd m) (cF m).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cF.
   tauto.
 apply surj_cF.
   tauto.
Qed.

(* IDEM: *)

Lemma surj_cF_1 :
  forall (m:fmap), inv_hmap m ->
      surj_dart (exd m) (cF_1 m).
Proof.
unfold surj_dart in |- *.
intros.
split with (cF m y).
rewrite cF_1_cF.
 split.
  generalize (exd_cF m y).
    tauto.
  tauto.
 tauto.
 tauto.
Qed.

(* IDEM: *)

Lemma bij_cF_1 :
  forall (m:fmap), inv_hmap m ->
      bij_dart (exd m) (cF_1 m).
Proof.
unfold bij_dart in |- *.
intros.
split.
 apply inj_cF_1.
   tauto.
 apply surj_cF_1.
   tauto.
Qed.

(*=========================================================
       ORBITS IN FACES BY INSTANCIATION :
===========================================================*)

(* TO CATCH THE ORBITS IN FACES: *)

Module McF<:Sigf.
Definition f := cF.
Definition f_1 := cF_1.
Definition exd_f := exd_cF. 
Definition exd_f_1 := exd_cF_1. 
Definition bij_f := bij_cF.
Definition bij_f_1 := bij_cF_1.
Definition f_1_f := cF_1_cF.
Definition f_f_1 := cF_cF_1.
End McF.

Module MF:= Mf McF.

(*==========================================================
                         END of Part 2
===========================================================*)


