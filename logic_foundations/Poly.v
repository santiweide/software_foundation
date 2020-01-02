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
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.
(* Supplying Type Arguments Explicitly *)
Definition mynil : list nat := nil.
Check @nil.
Definition mynil' := @nil nat.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
Check [1;2;3].
Check [true;false;true].
Compute [1;2;3]++[1;2;3].

Definition list123''' := [1;2;3].
(* Exercise: 2 stars, standard, optional (poly_exercises) *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [| n l' IHl']. reflexivity.
  simpl. rewrite IHl'. reflexivity.
Qed.
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| k l' IHl']. simpl. reflexivity.
  simpl. rewrite IHl'. reflexivity. 
Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [|n l1 IHl1']. reflexivity.
  simpl. rewrite IHl1'. reflexivity.
Qed.
(* Exercise: 2 stars, standard, optional (more_poly_exercises) *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1']. 
  induction l2 as [| n l2' IHl2']. reflexivity. simpl.
  rewrite <- app_assoc. reflexivity. 
  simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl']. reflexivity.
  simpl.
  rewrite  rev_app_distr. simpl. rewrite IHl'. reflexivity.
Qed.

(* Polymorphic Pairs *)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.
Check pair nat nat.
Compute @pair.
Print pair.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
Check list(prod nat nat).
Check @list(prod nat nat).
Check list(@prod nat nat).
Check (@fst (prod nat nat)).
Check list _.
Check (prod (list nat) (list nat)).
Check @nil _.
Check @nil nat.
Check prod Type Type.
Check prod (list nat) (list nat).
Check (nat * nat)%type.
(* Exercise: 1 star, standard, optional (combine_checks) *)
Check @combine.
Check list nat.
Check (@nil nat).
Check (@nil nat).
Check prod (list nat) (list nat).
Check ((list nat) * (list nat))%type.
Check (nil,nil).
Check (list nat*list nat)%type.
Check (list nat,list nat).
Check (@nil nat,@nil nat).
Check @fst (nat*nat)%type.
Check @fst.
Check fst.
Check (nat*nat)%type.
(* Exercise: 2 stars, standard, recommended (split) *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ((@nil X) , (@nil Y))
  | (x,y)::t => ((x:: (fst (split t)) , y::(snd (split t))))
  end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.
(* Polymorphic Options *)
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.
End OptionPlayground.
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.
(* Exercise: 1 star, standard, optional (hd_error_poly) *)
Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.
Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Admitted.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Admitted.
(*Functions as Data*)
(* Higher-Order Functions *)
Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).
Check @doit3times.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.
Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.
Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.
Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.
(*匿名函数*)
Example test_anon_fun':
  doit3times (fun n=>n*n) 2 = 256.
Proof. reflexivity. Qed.
Example test_filter2':
  filter (fun l=> (length l)=? 1)
    [[1; 2];[3];[4];[5;6;7];[];[8]]=[[3];[4];[8]].
Proof. reflexivity. Qed.
(*
Exercise: 2 stars, standard (filter_even_gt7)
Use filter (instead of Fixpoint) to write a Coq function filter_even_gt7 that takes a list of natural numbers as input and returns a list of just those that are even and greater than 7.
*)
Definition filter_even_gt7 (l : list nat) : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.










