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
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Qed.
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
Use filter (instead of Fixpoint) to write a Coq function filter_even_gt7 
that takes a list of natural numbers as input 
and returns a list of just those that are even and greater than 7.
*)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => 7 <=? x) (filter evenb l).
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(*
Exercise: 3 stars, standard (partition)
Use filter to write a Coq function partition:
      partition : ∀X : Type,
                  (X → bool) → list X → list X * list X
Given a set X, a test function of type X → bool and a list X, 
partition should return a pair of lists. 
The first member of the pair is the sublist of the original list 
containing the elements that satisfy the test, and the second is 
the sublist containing those that fail the test. The order of elements 
in the two sublists should be the same as their order in the original list.
*)
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  := (filter test l ,filter (fun x=> negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(*Map,映射操作。给出一个[x1 x2 ... xn],得到[f x1 f x2 ... f xn]*)
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2 : map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
(*Exercise: 3 stars, standard (map_rev)
Show that map and rev commute. You may need to define an auxiliary lemma.
*)

Theorem map_theo: forall (X Y:Type) (f:X->Y)(l:list X)(k: X),
  map f (l ++ [k]) = map f (l) ++ [f k].
Proof.
  intros X Y f l k. induction l as [| n l' IHl']. reflexivity.
  simpl. rewrite IHl'. reflexivity.
Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| n l' IHl']. reflexivity.
  simpl. rewrite <- IHl'. rewrite map_theo. reflexivity.
Qed.

(* Exercise: 2 stars, standard, recommended (flat_map) 
The function map maps a list X to a list Y using a function of type X → Y. 
We can define a similar function, flat_map, 
which maps a list X to a list Y using a function f of type X → list Y.
Your definition should work by 'flattening' the results of f.*)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
  match l with 
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
 
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.
(*Fold => map reduce的函数式特性*)
Fixpoint fold {X Y:Type} (f: X->Y->Y)(l:list X)(b:Y):Y :=
  match l with 
  | nil => b
  | h :: t => f h (fold f t b)
  end.
Compute fold plus [1;2;3;4] 0.
Check fold andb.

Example fold_example1:
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2:
  fold andb [true;false] true = false.
Proof. reflexivity. Qed.

Example fold_example3:
  fold app [[1];[];[2;3];[4]] [9] = [1;2;3;4;9].
Proof. reflexivity. Qed.
(*构造函数的函数：Functions That Construct Functions*)
Definition constfun {X:Type} (x:X): nat->X:=
  fun (k:nat) => x.
(*上面的例子使用匿名函数作为函数的返回值*)
Definition ftrue := constfun true.
Example constfun_exp1: ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_exp2: ftrue 1 = true.
Proof. reflexivity. Qed.
(*ftrue忽略参数nat的值，只返回true（意义何在.....*)
Check plus.
Definition plus3 := plus 3.
Check plus3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.
(*Additional Exercise*)
Module Exercises.
(* Exercise: 2 stars, standard (fold_length) *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.
Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l as [| n l' IHl']. reflexivity.
  simpl. rewrite <- IHl'. reflexivity.
Qed.
Check andb.
(* Exercise: 3 stars, standard (fold_map)
We can also define map in terms of fold. Finish fold_map below. *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y := 
  match l with
  | [] => []
  | h :: t => fold (fun h t => (f h)::t) l []
  end.
Example test_fold_map1 : fold_map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_fold_map2: fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_fold_map3:
    fold_map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
(* Exercise: 2 stars, advanced (currying) *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. reflexivity.
Qed.
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p. reflexivity.
Qed.
(* Exercise: 2 stars, advanced (nth_error_informal)*)
 Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.
(*
informal proof...do not do formal!!!!aaaaAAAA
Theorem nth_error_theo : forall X n l,
  length l = n -> @nth_error X l n = None.
Proof.
  intros X n l H. rewrite <- H. 
  induction l as [| n' l' IHl']. reflexivity.
  apply
  simpl. rewrite IHl'. reflexivity.
  rewrite <- H. simpl. 
Qed.
*)
(*
The following exercises explore an alternative way of defining natural numbers, using the so-called Church numerals, named after mathematician Alonzo Church. We can represent a natural number n as a function that takes a function f as a parameter and returns f iterated n times.
*)
Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.
Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.
Definition three : cnat := @doit3times.
Compute  fun (X : Type) (f : X -> X) (x : X) => f x.
Compute one bool negb false.
Compute two bool negb false.
Compute negb false.
Compute negb (negb false).
Compute one (bool->bool) (one bool) negb false.
Compute one nat S O.
Compute one nat S (one nat S O).
Compute two nat S O.
Compute one nat S (two nat S O).
Compute one (nat->nat) (two nat) S O.
(* Exercise: 1 star, advanced (church_succ) *)
Definition succ (n : cnat) : cnat := 
  fun (X : Type)(f:X->X)(x:X)=> (one X f) (n X f x).
Compute zero nat S O.
Compute succ zero nat S O.
Compute one nat S O.
Compute succ one nat S O.
Compute two nat S O.
Compute succ two nat S O.
Compute three nat S O.
Compute succ three nat S O.
Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.
(*耶!!!!!!虽然只是1星习题但是好~开~心~*)
(*
Exercise: 1 star, advanced (church_plus)
Addition of two natural numbers:
*)
Definition plus (n m : cnat) : cnat :=
  fun (X : Type)(f:X->X)(x:X)=>  (m X f) (n X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.
Compute one nat S O.
(*
Exercise: 2 stars, advanced (church_mult)
Multiplication:
*)
Definition mult (n m : cnat) : cnat :=
 fun (X : Type)(f:X->X)(x:X)=> m X (n X f) x.
Compute mult one zero nat S O.
Compute mult two one nat S O.
Compute mult three two nat S O.
Compute mult two three nat S O.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.
(* Exercise: 2 stars, advanced (church_exp) 
Exponentiation:
(Hint: Polymorphism plays a crucial role here. However, choosing the right type to iterate over can be tricky. If you hit a "Universe inconsistency" error, try iterating over a different type. Iterating over cnat itself is usually problematic.)
*)
Definition exp (n m : cnat) : cnat :=
  fun (X : Type)=> m (X->X) (n X).
Compute exp one two nat S O.
Compute exp two two nat S O.
Compute exp three two nat S O.
Compute exp two three nat S O.
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.
End Church.
End Exercises.
