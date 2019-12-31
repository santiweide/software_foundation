(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.
(*ploy and highrt order functions*)
(*介绍一下polymorphism,多态。泛化能力是很重要的～*)
Inductive boollist:Type :=
  | bool_nil
  | bool_cons(b : bool)(l:boollist).
Inductive list(X:Type):Type :=
  | nil
  | cons (x:X)(l:list X).
Check list.
Check (nil bool).
Check (cons bool).
Check (cons bool true (nil bool)).
Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).
(*
list: Type -> Type
nil nat: list nat
cons nat: nat -> list nat -> list nat
cons nat 3 (nil nat): list nat
*)
Fixpoint repeat (X:Type)(x:X)(count:nat):list X:=
  match count with
  | 0=> nil X
  | S count' => cons X x (repeat X x count')
  end.
Example test_repeat1:
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.
(*
Exercise: 2 stars, standard (mumble_grumble)
Consider the following two inductively defined types.
*)
Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).
Check mumble.
Check a.
Check (b a 1).
Check c.
Check d nat (b a 1).
Check d bool (b a 1).
Check e bool.
Check e bool true.
(*e bool: bool -> grumble bool*)
(*e bool true: grumble bool*)
End MumbleGrumble.
(*Type Annotation Interface*)
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)






