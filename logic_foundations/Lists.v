(*递归描述的数据结构*)
From LF Require Export Induction.
Module NatList.
Inductive natprod: Type := 
|  pair (n1 n2: nat).
Check (pair 3 5).
Definition fst(p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd(p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst(pair 3 5)).
Notation "( x , y )" := (pair x y).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.
Fixpoint minus (n m : nat) : nat :=
   match n, m with
   | O   , _    => O
   | S _ , O    => n
   | S n', S m' => minus n' m'
   end.
(* Can't match on a pair with multiple patterns: 
Definition bad_fst (p : natprod) : nat :=
  match p with
  | x, y => x
  end.
(* Can't match on multiple values with pair patterns: *)
Definition bad_minus (n m : nat) : nat :=
  match n, m with
  | (O   , _   ) => O
  | (S _ , O   ) => n
  | (S n', S m') => bad_minus n' m'
  end.
 不允许pair匹配多值"*"下面证明为啥pair不允许被匹配多值*)
Theorem surjective_pairing' : forall (n m: nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.
Theorem surjective_pairing_stuck: forall (p:natprod),
  p = (fst p, snd p).
Proof.
  simpl.
Abort.
Theorem surjetive_pairing: forall p:natprod,
  p = (fst p,snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
(* Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.
(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.
(*cons == construct*)
Inductive natlist : Type:=
  | nil
  | cons (n:nat)(l:natlist).
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Print mylist.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
Notation "x + y" := (plus x y)
                      (at level 50, left associativity).
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => n :: (repeat n count')
  end.
Fixpoint length (l: natlist): nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Fixpoint app (l1 l2:natlist):natlist :=
  match l1 with
  | nil => l2
  | h :: t => h:: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.
(*
Exercise: 2 stars, standard, recommended (list_funs)
Complete the definitions of nonzeros, oddmembers, and countoddmembers below. Have a look at the tests to understand what these functions should do.
*)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  reflexivity. Qed.
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match evenb(h) with
            | true => oddmembers t
            | false => h :: oddmembers t
            end
  end. 
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  simpl. reflexivity. Qed.
Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. reflexivity. Qed.
(*
Exercise: 3 stars, advanced (alternate)
Complete the definition of alternate, which interleaves two lists into one, alternating between elements taken from the first list and elements from the second. See the tests below for more specific examples.
*)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => 
    match l2 with
    | nil => h1::t1
    | h2 :: t2 => h1::h2::( alternate t1 t2 )
    end
  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.
(* Bags via Lists*)
(* Exercise: 3 stars, standard, recommended (bag_functions) *)
Definition bag := natlist.
Fixpoint count (v:nat)(s:bag) :nat :=
  match s with
  | nil => 0
  | h::t => 
    match h=?v with
    | true => S (count v t)
    | false => count v t
    end  
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.
(*很像匿名函数*)
Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Definition add (v:nat) (s:bag) : bag := v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | 0 => false
  | _ => true
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.
(* Exercise: 3 stars, standard, optional (bag_more_functions) *)
Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => 
    match v=?h with
    | true => t
    | false => h :: (remove_one v t)
    end
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with 
  | nil => nil
  | h :: t => 
    match v=?h with
    | true => remove_all v t
    | false => h :: (remove_all v t)
    end
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => 
    match (count h s1)<=?(count h s2) with
    | true => subset t s2
    | false => false
    end
  end.
Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.
(*Reasoning about Lists*)
Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(*tl means tail*)
Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.
(* pred 指的是前驱 
Compute Nat.pred (S(S 0)).*)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.
(* let's prove that reversing a list does not change its length. Our first attempt gets stuck in the successor case...*)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity. 
  - simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'.
    reflexivity.
Qed.

(* Exercise: 3 stars, standard (list_exercises) *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  simpl. induction l2 as [| n l2' IHl2']. reflexivity.
  rewrite -> app_nil_r. reflexivity.
  simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| n l IHl']. reflexivity.
  simpl. rewrite -> rev_app_distr.
  simpl. rewrite -> IHl'.
  reflexivity.
Qed.

(* Exercise: 2 stars, standard (eqblist) *)
(* Fill in the definition of eqblist, which compares lists of numbers for equality. Prove that eqblist l l yields true for every list l. *)
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => 
    match l2 with
    | nil => true
    | h :: t => false
    end
  | h1 :: t1 => 
    match l2 with
    | nil => false
    | h2 :: t2 => 
      match h1 =? h2 with
      | true => eqblist t1 t2
      | false => false
      end
    end
  end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl']. reflexivity.
  simpl. rewrite <- eql_theo, IHl'. reflexivity. 
Qed.

(* Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s as [| n l IHl]. reflexivity.
  reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s as [| n l IHl]. reflexivity.
  destruct n. simpl. rewrite -> leb_n_Sn. reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

(*
Exercise: 4 stars, advanced (rev_injective)
Prove that the rev function is injective — that is,
    ∀(l1 l2 : natlist), rev l1 = rev l2 → l1 = l2.
(There is a hard way and an easy way to do this.)
*)
Theorem bag_theo_one: forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. induction l1 as [| n l1 IHl1]. simpl.
  intros H. rewrite H. 
  induction l2 as [| n l2 IHl2]. reflexivity.
  rewrite <- IHl2. simpl. rewrite -> rev_involutive.

Abort.






