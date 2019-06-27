Require Import List.

Notation "[]"    := nil.
Notation "[ z ]" := (cons z []) (z at level 200).

(* Permutations by transpositions *)

Inductive perm (a : Set)
             : list a -> list a -> Prop :=
  perm_nil   : perm a [] []
| perm_cons  : forall (x : a) (s t : list a),
               perm a s t -> perm a (x::s) (x::t)
| perm_swap  : forall (x y : a) (s : list a),
               perm a (x::y::s) (y::x::s)
| perm_trans : forall (s t u : list a),
               perm a s t -> perm a t u -> perm a s u.

Notation "s ~~ t" := (perm _ s t) (at level 70, no associativity).

Theorem perm_refl :
  forall (a : Set) (s : list a), s ~~ s.
Proof.
intros.
induction s as [| x s].
  - apply perm_nil.
  - apply perm_cons.
    apply IHs.
Qed.

Theorem perm_symm : 
  forall (a : Set) (s t : list a), s ~~ t -> t ~~ s.
Proof.
intros.
induction H.
  - apply perm_nil.
  - apply perm_cons.
    apply IHperm.
  - apply perm_swap.
  - apply (perm_trans a u t s).
    * apply IHperm2.
    * apply IHperm1.
Qed.

(* Total order *)

Definition antisymmetric (a : Set) (rel : a -> a -> bool) :=
  forall (x y : a),
  (rel x y = true /\ rel y x = true) -> x = y.

Definition transitive (a : Set) (rel : a -> a -> bool) :=
  forall (x y z : a),
  (rel x y = true /\ rel y z = true) -> rel x z = true.

Definition connex (a : Set) (rel : a -> a -> bool) :=
  forall (x y : a), rel x y = true \/ rel y x = true.

Definition total_order (a : Set) : Set := {
  cmp : a -> a -> bool |
  antisymmetric a cmp /\ transitive a cmp /\ connex a cmp
}.

(* Partial order *)

Lemma partial_order : forall (a : Set) (cmp : total_order a) (x y : a),
  proj1_sig cmp x y = false -> proj1_sig cmp y x = true /\ x <> y.
Proof.
  destruct cmp as (rel, (antisym, (trans, conn))).
  simpl.
  intros.
  case (conn x y).
  - rewrite H. intro. discriminate. (* or "congruence" *)
  - intro Hyx.
    split.
    + assumption.
    + intro Heq. (* x <> y is x = y -> False *)
      rewrite Heq in *.
      rewrite H in Hyx.
      discriminate.
Qed.

(* Inserting an item in a sorted list *)

Fixpoint insert (a : Set) (cmp : total_order a)
             (s : list a) (x : a) :=
  match s with
    y::s' => 
      if   proj1_sig cmp x y  (* Print exist. or Program *)
      then x :: s
      else y :: insert a cmp s' x
  | [] => x:: s
  end.

Lemma insert_inv2 :
  forall (a : Set) (cmp : total_order a)
         (s : list a) (x y : a),
  proj1_sig cmp x y = false -> y :: insert a cmp s x = insert a cmp (y::s) x.
Proof.
intros.
unfold insert at 2.
fold insert.
case_eq (proj1_sig cmp x y).
  - intro.
    rewrite H0 in *.
    discriminate.
  - intro.
    reflexivity.
Qed.

(* Insertion sort *)

Fixpoint sort (a : Set) (cmp : total_order a)
              (s : list a) :=
  match s with
      [] => []
  | x::s => insert a cmp (sort a cmp s) x
  end.

(* Insertion adds a key *)

Lemma perm_insert :
  forall (a : Set) (cmp : total_order a) (s : list a) (x : a),
  insert a cmp s x ~~ x::s.
Proof.
intros.
induction s as [|y s]; simpl. (* ";" is a pipe *)
  - repeat constructor.
  - case (proj1_sig cmp x y).
    * apply perm_refl.
    * econstructor; constructor.
      assumption.
Qed.

(* Totally ordered lists *)

Inductive ord_list (a : Set) (cmp : total_order a)
                 : list a -> Prop :=
  ord_nil  : ord_list a cmp []
| ord_one  : forall x : a, ord_list a cmp [x]
| ord_more : forall (x y : a) (s : list a),
                proj1_sig cmp x y = true  (* x <= y in mind *)
             -> ord_list a cmp (y::s)
             -> ord_list a cmp (x::y::s).

Lemma ord_cons :
  forall (a : Set) (cmp : total_order a) (x : a) (s : list a),
  ord_list a cmp (x::s) -> ord_list a cmp s.
Proof.
intros.
induction s as [|y t].
  - apply ord_nil.
  - inversion H.
    assumption.
Qed.

(* Insertion preserves the ordering *)

Lemma ord_insert :
  forall (a : Set) (cmp : total_order a) (s : list a) (x : a),
  ord_list a cmp s -> ord_list a cmp (insert a cmp s x).
Proof.
intros.
induction s as [|y s].
  - simpl.
    apply ord_one.
  - simpl.
    case_eq (proj1_sig cmp x y).
      * intro. 
        apply ord_more; assumption.
      * intro.
        destruct s as [|z t].
          + simpl.
            apply ord_more.
              -- apply partial_order.
                 assumption.
              -- apply ord_one.
          + set (s := z::t) in *.
            simpl.
            case_eq (proj1_sig cmp x z).
              -- intro.
                 apply ord_more.
                   ** apply partial_order.
                      assumption.
                   ** apply ord_more.
                        ++ assumption.
                        ++ apply (ord_cons a cmp y s).
                           assumption.
             -- intro.
                apply ord_more.
                  ** inversion H.
                     assumption.
                  ** inversion H.
                     apply (insert_inv2 a cmp t x z) in H1.
                     rewrite H1.
                     apply IHs.
                     apply H6.
Defined.

(* Insertion sort is indeed a sorting algorithm *)

Theorem is_sorted :
  forall (a : Set) (cmp: total_order a) (s : list a),
  ord_list a cmp (sort a cmp s) /\ perm a (sort a cmp s) s.
Proof.
split.
  - induction s as [|x s].
      * simpl.
        apply ord_nil.
      * simpl.
        apply ord_insert.
        apply IHs.
  - induction s as [|x s].
      * simpl.
        apply perm_nil.
      * simpl.
        assert (insert a cmp (sort a cmp s) x ~~ x :: sort a cmp s).
          + apply perm_insert.
          + eapply perm_trans with (t := x :: sort a cmp s).
              -- exact H.
              -- apply perm_cons.
                 exact IHs.
Defined.

(*
Lemma perm_insert :
  forall (a : Set) (cmp : total_order a) (s : list a) (x : a),
  insert a cmp s x ~~ x::s.
Proof.
intros.
induction s as [| y s]; simpl. (* ";" is a pipe *)
  - repeat constructor. (* apply perm_cons. apply perm_nil. *)
  - case (proj1_sig cmp x y).
      * apply perm_refl.
      * assert (y :: insert a cmp s x ~~ y :: x :: s).
        + apply(perm_cons).
          exact IHs.
        + set (swap := perm_swap a y x s).
          clearbody swap.
          apply (perm_trans _ _ _ _ H swap).
Qed.
*)
(*
Lemma perm_insert :
  forall (a : Set) (cmp : total_order a) (s : list a) (x : a),
  insert a cmp s x ~~ x::s.
Proof.
intros.
induction s as [| y s].
  - unfold insert.
    apply perm_cons.
    apply perm_nil.
  - unfold insert.
    fold insert.
    destruct cmp as [cmp' H].
    case (cmp' x y).
      + apply perm_refl.
(*
      + eapply perm_trans with (t := y::x::s). (* existential apply *)
      + apply (perm_trans a _ (y::x::s) _); cycle 1.
*)
          * apply perm_swap.
          * apply perm_cons.
            exact IHs.
Qed.
*)
