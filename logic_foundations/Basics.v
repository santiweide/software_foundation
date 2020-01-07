(*逻辑代数运算*)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
(* !(a&&b)*)
(* Exercise: 1 star, standard (nandb)*)
Definition nandb (b1:bool) (b2:bool) : bool := 
  match b1, b2 with
  | true,true => false
  | _,_ => true
end.
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(* a && b && c*)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1,b2,b3 with
  | true,true,true => true
  | _,_,_ => false
end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(*关于自然数的函数和定理*)
(*判断是不是一个偶数*)
Fixpoint evenb (n:nat):bool:=
  match n with
  | 0 => true
  | S 0 => false
  | S (S p) => evenb p
end.
(*判断是不是一个偶数*)
Fixpoint oddb (n:nat):bool:=
  match n with
  | 0 => false
  | S 0 => true
  | S (S p) => oddb p
end.
(*加法定义*)
Fixpoint plus (n m:nat) :nat :=
  match n with
  | 0 => m
  | S p => S (plus p m)
end.
(*乘法定义*)
Fixpoint mult (n m:nat) :nat :=
  match n with
  | 0 => 0
  | S p => plus m (mult p m)
end.
(*指数运算的定义*)
Fixpoint exp (base pow: nat):nat :=
  match pow with
  | 0 => S 0
  | S p => mult p (exp base p)
end.
(* Exercise: 1 star, standard (factorial)
(*阶乘的方程*) *)
Fixpoint factorial(n:nat):nat :=
  match n with  
  | 0 => 1
  | 1 => 1
  | S p => mult n (factorial p)
end.
Example factorial1 :(factorial 3) = 6.  
Proof. simpl. reflexivity. Qed.
Example factorial2 :(factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(*Notation*)
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
(* Check ((0 + 1) + 1). *)
(*定义更多自然数的关系运算/表达式*)
(*利用前驱定义”等于关系“*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
(*利用前驱定义“小于或等于关系”*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m'=> leb n' m'
      end
  end.
Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.
(* Exercise: 1 star, standard (ltb)
(* 定义“小于运算” *) *)
Definition ltb (n m : nat) : bool :=
  match (leb n m) with
  | true => negb((eqb n m))
  | false => false
end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(*一些证明*)
(*证明对于任意自然数n，0+n = n*)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
Theorem plus_1_1: forall n:nat, 1+n=S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_1: forall n:nat,0*n=0.
Proof.
  intros n. reflexivity. Qed.
(*带有条件的证明*)
Theorem plus_id_example: forall n m:nat,
  n=m->
  n+n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

(* Exercise: 1 star, standard (plus_id_exercise)
(*证明一个自然数加0等于他本身*) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.
(**)
Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. 
Qed.
Theorem mult_eql: forall n m:nat,
  m=n -> m * n = m * m.
Proof.
  intros m n.
  intros H.
  rewrite H.
  reflexivity.
Qed.
(* Exercise: 2 stars, standard (mult_S_1) *)
(*证明：对于任意自然数n,m,如果m是n的直接后继，
则有m * (1+n) = m * m*)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_1.
  rewrite -> mult_eql.
  reflexivity.
  rewrite -> H.
  reflexivity.  
Qed.
Theorem plus_1_neq_0: forall n:nat,
  (n+1)=?0=false.
Proof.
  intros n.
  destruct n as [| q] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b:bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
(*枚举法/归纳法：destructive*)
Theorem andb_commutative: forall b c,
 andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.
(* Exercise: 1 star, standard (andb3)*)
Theorem andb3_exchange: 
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.
(*Exercise: 2 stars, standard (andb_true_elim2)*)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
  reflexivity.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
  reflexivity.
  simpl.
  intro H.
  rewrite H.
  reflexivity.
Qed.
(*Exercise: 1 star, standard (zero_nbeq_plus_1)*)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  reflexivity.
  reflexivity.
Qed.
(* Exercise: 1 star, standard (indentity_fn_applied_twice)*)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.
(* Exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  destruct b eqn:Eb.
  reflexivity.  
  reflexivity.
  Qed.
  
(* The Import statement on the next line tells Coq to use the
   standard library String module.  We'll use strings more in later
   chapters, but for the moment we just need syntax for literal
   strings for the grader comments. *)
From Coq Require Export String.
(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

(* Exercise: 3 stars, standard, optional (andb_eq_orb)*)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  simpl.
  destruct c eqn:Ec.
  reflexivity.
  intro H.
  rewrite -> H.
  reflexivity.
  simpl.
  intro H.
  rewrite -> H.
  reflexivity.
Qed.
(* Exercise: 3 stars, standard (binary)*)
Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).
Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => (B m)
  | A m => B m
  | B m => A (incr(m))
end.


(*Test for increase(0--7)*)
Example test_bin_incr1: (incr Z) = (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: incr (incr Z) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3: incr (incr (incr Z)) = B (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4: incr (incr (incr (incr Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5: incr (incr (incr (incr (incr Z)))) = B (A (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6:  incr (incr (incr (incr (incr (incr Z))))) = A (B (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr7: incr (incr (incr (incr (incr (incr (incr Z)))))) = B (B (B Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr8: incr (incr (incr (incr (incr (incr (incr (incr Z))))))) = A (A (A (B Z))).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A m => plus (bin_to_nat(m)) (bin_to_nat(m))
  | B m => S (plus (bin_to_nat(m)) (bin_to_nat(m)))
end.

(*Test for 2 based-10 based(0--8)*)
Example test_bin_incr11: bin_to_nat Z = 0.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr12: bin_to_nat (incr Z) = 1.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr13: bin_to_nat (incr ((incr Z))) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr14: bin_to_nat (incr (incr (incr Z)))= 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr15: bin_to_nat (incr (incr (incr (incr Z))))= 4.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr16: bin_to_nat (incr (incr (incr (incr (incr Z))))) = 5.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr17: bin_to_nat (incr((incr (incr (incr (incr (incr Z))))))) = 6.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr18: bin_to_nat (incr(incr((incr (incr (incr (incr (incr Z)))))))) = 7.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr19: bin_to_nat (incr(incr(incr((incr (incr (incr (incr (incr Z)))))))))  = 8.
Proof. simpl. reflexivity. Qed.



