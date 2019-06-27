Set Implicit Arguments.

Inductive mylist (a : Set) : nat -> Set :=
  MyNull : mylist a 0
| MyCons : forall n, a -> mylist a n -> mylist a (S n).

(* Require Import Coq.Program.Tactics Coq.Logic.JMeq. *)
(* Program  *)

Fixpoint append (a : Set) (k k' : nat) (x : mylist a k) 
                (y : mylist a k') : mylist a (k+k') :=
  match x with
    MyNull _ => y
  | @MyCons _ p hd tl =>
      @MyCons _ _ hd (@append _ _ _ tl y)
end.

Print append.
Print mylist.

Fixpoint length a k (x : mylist a k) : nat :=
  match x with
 | MyNull _ => 0
 | MyCons hd tl => 1 + length tl
end.

Print length.

Definition bool_len n (x : mylist bool n) :=
  @length bool n x.

Print bool_len.

Ltac ByDefinition ident := 
  unfold ident; fold ident.

Require Import Omega.

Ltac ByLawsOfArithmetic' :=
try apply gt_Sn_n;
try apply eq_S.

Ltac ByLawsOfArithmetic :=
ByLawsOfArithmetic';
auto.

Theorem LowHanging : forall a k (x : mylist a k),
  @length a k x = k.

intros a k x.
induction x as [|n hd tl IH];
ByDefinition length;
ByLawsOfArithmetic.


  exact IH.

Qed.

(* Theorem LowHanging' : forall a k (x : mylist a k),
  @length a k x = k.

refine (fun a k x => _).
refine (match x with 
          MyNull _ => _
        | @MyCons _ p hd tl => _
        end).
refine (ltac:(unfold length)).
refine (eq_refl 0).
refine (ltac:(unfold length)).
refine (ltac:(fold length)).
Print LowHanging.
 *)


