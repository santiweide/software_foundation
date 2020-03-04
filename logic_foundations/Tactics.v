
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
  intros n m' o p eq1 eq2.
  apply trans_eq with (m :=m').
  apply eq2. apply eq1.
  Qed.
(* The 内射injection and discriminate Tactics   *)
(* 通过在此时编写注入H，我们要求Coq使用构造函数的注入性生成可以从H推断出的所有方程式。
每个这样的方程式都作为前提添加到目标中。在本示例中，添加前提n = m。*)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.
Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
Theorem injection_ex2 : forall (n m:nat),
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm. Qed.
(* Exercise: 1 star, standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j -> x = y. 
Proof.
  intros X x y z l j.
  intros H HH.  injection HH.
  intros HH1 HH2. symmetry. apply HH2. Qed.
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n. intros H. destruct n. reflexivity. discriminate H. Qed.
Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.
(* Exercise: 1 star, standard (discriminate_ex3) *)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j.
  intros contra. discriminate contra. Qed.
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
(* Using Tactics on Hypotheses *)
Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.
Theorem silly3' : forall(n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem plus_n_n_injective_1 : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    - simpl. intros m H. destruct m as [|m'].
      + reflexivity.
      + inversion H.
    - simpl. intros m H. destruct m as [|m'].
      + inversion H.
      + apply f_equal. 
  apply IHn'. inversion H.
  rewrite <- plus_n_Sm in H1.
  symmetry in H1. rewrite <- plus_n_Sm in H1.
  inversion H1. reflexivity.
Qed.
(*varying the Induction Hypothesis*)
(* 有时候，控制得到H是什么是很重要的。不同的intros时机会导致不同的H产生。
上一题就明显体现了这一点。
 *)
(* Exercise: 2 stars, standard (eqb_true)*)
Theorem eqb_true: forall n m, 
  n =? m = true -> n=m.
Proof.
  intros n. induction n as [|n']. 
  - intros m H. destruct m. reflexivity. inversion H.
  - intros m H. destruct m. inversion H. simpl in H.
  apply IHn' in H. rewrite H. reflexivity.
Qed.
Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
        (* Stuck again here, just like before. *)
Abort.
Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

(* Exercise: 3 stars, standard, recommended (gen_dep_practice) *)
(* Prove this by induction on l. *)
(* nth_error:如果list不够n长，则nth_error返回None，否则返回从左向右数第n个元素*)
(* 求证：如果length l==n，那么nth_err l n返回一定是None*)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n -> nth_error l n = None.
Proof.
  intros n X l. 
  generalize dependent n.  
  induction l as [| l']. simpl. reflexivity.
  intros n H. rewrite <- H. apply IHl. reflexivity.
Qed.
(*Unfolding Definitions*)
Theorem mult_comm: forall n m:nat, n*m=m*n.
Proof.
intros n m. 
generalize dependent m.
induction n as [| n IHn]. 
- induction m as [| m IHm]. reflexivity.
simpl. apply IHm.
- induction m as [| m IHm]. simpl.
apply IHn. 
(* assert(S n * m + S n = m * S n + S n). *)
(* rewrite IHm. reflexivity. *)
assert(n * S m= n * m + n).
{
  rewrite IHn with (m:=S m).
  simpl. rewrite plus_comm. symmetry.
  rewrite IHn with (m:=m). reflexivity.
}
simpl in IHm. symmetry in IHm.
simpl. 
assert(m + n * S m = n + m * S n).
rewrite H. rewrite IHm. 
rewrite plus_assoc.
symmetry. rewrite plus_assoc.
rewrite plus_comm with (n:=m + n*m).
rewrite plus_assoc.
reflexivity.
rewrite H0. reflexivity.
Qed.

Theorem subthe1: forall n m p o:nat, n+m+(p+o)=n+p+(m+o).
Proof.
intros n m p o. rewrite plus_assoc.
symmetry. rewrite plus_assoc. 
rewrite plus_comm with (m:=p).
rewrite plus_comm with (n:=n+m). 
rewrite plus_assoc.
reflexivity.
Qed.
Theorem subthe2: forall n m p:nat, n*(m+p)=n*m+n*p.
Proof.
intros n m p. induction n as [| n' IHn']. simpl. reflexivity.
simpl. rewrite IHn'. apply subthe1.
Qed.
Theorem mult_assoc: forall n m p:nat,n*(m*p)=(n*m)*p.
Proof.
intros n m p. induction n as [| n' IHn].
- simpl. reflexivity.
- simpl. rewrite IHn. rewrite mult_comm with (n:=m+n'*m).
  rewrite subthe2 with(n:=p).
  rewrite mult_comm with(n:=p).
  rewrite mult_comm with(m:=n'*m).
  reflexivity.
Qed.
Definition square n:=n*n.
Lemma squar_mult: forall n m, square (n*m) = square n * square m.
Proof.
intros n m. unfold square. 
rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.
Definition foo (x:nat) := 5.
Fact silly_fact_1: forall m, foo m+1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl. 
  reflexivity.
Qed.
Definition bar x:=
  match x with
  | 0 => 5
  | S _ => 5
  end.
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.
Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Fact silly_fact_2': forall m, bar m+1 = bar (m+1)+1.
Proof.
intros m.
unfold bar.
destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.
(* Here is an implementation of the split function mentioned in chapter Poly: *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.
(* Prove that split and combine are inverses in the following sense: *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - intros l1 l2 H. simpl in H.
    injection H as H. rewrite <- H. rewrite <- H0. simpl. reflexivity. 
  - destruct x as (x,y).
    destruct l1 as [| x'].
    + intros l2 H. simpl in H.
      destruct (split l) in H. discriminate H.
    + destruct l2 as [| y'].
      * intros H. simpl in H. destruct (split l). discriminate H.
      * intros H. simpl.
        assert(G: split l = (l1, l2)). {
          simpl in H. destruct (split l). 
          injection H as H. rewrite <- H0. rewrite <- H2. reflexivity.
        }
      apply IHl in G. rewrite <- G. 
      simpl in H. destruct (split l) in H. injection H as H.
      rewrite <- H. rewrite <- H1. reflexivity.
Qed.
(*↑ referring to https://github.com/marshall-lee/software_foundations/blob/master/lf/Tactics.v*)
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.
Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.
Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        eqn: again in the same way, allowing us to finish the
        proof. *)
      destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.
(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn:H0.
  - destruct (f true) eqn:H1. 
    + destruct (f true)eqn:H2. 
      * apply H2. 
      * discriminate H1.
    + destruct (f false)eqn:H2.
      * apply H1.
      * apply H2.
  - destruct (f false) eqn:H1.
    + destruct (f true)eqn:H2.
      * apply H2.
      * apply H1.
    +  rewrite H1. apply H1.
Qed.   
(** [] *)
(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.
    Here are the ones we've seen:
      - [intros]: move hypotheses/variables from goal to context
      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])
      - [apply]: prove goal using a hypothesis, lemma, or constructor
      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)
      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching
      - [simpl]: simplify computations in the goal
      - [simpl in H]: ... or a hypothesis
      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal
      - [rewrite ... in H]: ... or a hypothesis
      - [symmetry]: changes a goal of the form [t=u] into [u=t]
      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]
      - [unfold]: replace a defined constant by its right-hand side in
        the goal
      - [unfold... in H]: ... or a hypothesis
      - [destruct... as...]: case analysis on values of inductively
        defined types
      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis
      - [induction... as...]: induction on values of inductively
        defined types
      - [injection]: reason by injectivity on equalities
        between values of inductively defined types
      - [discriminate]: reason by disjointness of constructors on
        equalities between values of inductively defined types
      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H]
      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (eqb_sym)  *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  generalize dependent m.  
  induction n as [| n' IHn].
  - induction m as [| m' IHm].
    + reflexivity.
    + simpl. reflexivity.
  - induction m as [| m' IHm].
    + simpl. reflexivity.
    + simpl. rewrite IHn with (m:=m'). reflexivity. 
Qed.
(** **** Exercise: 3 stars, standard, optional (eqb_trans)  *)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p. 
  generalize dependent m.
  generalize dependent p.
  induction n as [| n' IHn].
  - induction m as [| m' IHm].
     + induction p as [| p' IHp].
        * simpl. reflexivity.
        * discriminate.
     + discriminate.
  - induction m as [| m' IHm].
     + induction p as [| p' IHp].
        * simpl. discriminate.
        * simpl. discriminate.
     + induction p as [| p' IHp].
        * simpl. discriminate.
        * simpl. apply IHn.
Qed.

(** **** Exercise: 3 stars, advanced (split_combine)  

    We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split (combine l1 l2) = (l1,l2)] to be true?) *)

Definition split_combine_statement : Prop
  (* ("[: Prop]" means that we are giving a name to a
     logical proposition here.) *)
  := forall X Y (l1:list X) (l2:list Y), length l1 = length l2->split (combine l1 l2) = (l1,l2).
Theorem split_combine : split_combine_statement.
Proof.
  intros X Y. induction l1 as [| x].
  - simpl. intros l2 H. destruct l2 as [| y].
    + reflexivity.
    + discriminate.
  - destruct l2 as [| y].
    + discriminate.
    + intros H. injection H as H. 
      apply IHl1 in H. simpl.
      rewrite H. reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (filter_exercise)  

    This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf.
  induction l as [| x'].
  - simpl. discriminate.
  - simpl. destruct (test x') eqn:H.
    + intros H1. injection H1 as H1. rewrite H1 in H. apply H.
    +  apply IHl.
Qed.
(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  

    Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (eqb 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (eqb 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. (* FILL IN HERE *) Admitted.

Example test_existsb_4 : existsb evenb [] = false.
Proof. (* FILL IN HERE *) Admitted.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

