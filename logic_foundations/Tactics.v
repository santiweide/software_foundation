
(* 1. 介绍如何利用辅助引理来进行正向证明和反向证明的方法 *)
(* 2. 关于data constructors的reason*)
(* 3. 如何获得更强的归纳假设  *)
Set Warnings "-notation-overridden,-parsing". 
From LF Require Export Poly.
Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed. 
Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.
Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.
(* Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros n eq1. apply eq1.
Qed.
Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H. Qed.
  
Theorem silly3: forall (n:nat),
  true = (n=?5)-> (S (S n)) =? 7 = true.
Proof.
  intros n eql. simpl. rewrite -> eql. destruct n.
  reflexivity. simpl. reflexivity. 
  Qed.
(* Exercise: 3 stars, standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
 intros l l' H. rewrite <- rev_involutive. 
 rewrite H. rewrite -> rev_involutive. rewrite -> rev_involutive.
  reflexivity. Qed.
Theorem rev_exercise1_apply : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
 intros l l' H.
 rewrite H. 
 symmetry.
 apply rev_involutive. 
 Qed.
(* apply with Tactic*)
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
  Qed.
(* Exercise: 3 stars, standard, optional (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p.
  