From LF Require Export Basics.
Theorem plus_n_O : forall n:nat,
  n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.
Theorem minus_diag: forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| q IHq].
  -simpl. reflexivity.
  -simpl. rewrite -> IHq. reflexivity. Qed.
(*indiction:带出一个感应S以后的推理的利器？*)
(*Exercise: 2 stars, standard, recommended (basic_induction)*)
(*证明任何自然数和0相乘等于0*)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| q IHq].
  simpl. reflexivity.
  simpl. rewrite -> IHq. reflexivity. Qed.
(*下面两个Theorem证明自然数范围内的加法交换律*)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n IHn']. 
  simpl. reflexivity.
  induction m as [| m IHm'].
  simpl. rewrite -> IHn'. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  simpl. induction m as [| m' IHm']. reflexivity.
  simpl. rewrite <- IHm'. reflexivity.
  simpl. rewrite -> IHn'. simpl. 
  rewrite plus_n_Sm. reflexivity.
Qed.
(*证明自然数范围内的加法结合律*)
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.
Qed.
(* Exercise: 2 stars, standard (double_plus) *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n IHn']. reflexivity.
  simpl. rewrite -> IHn'. 
  rewrite plus_n_Sm.
  reflexivity.
Qed.
(* Exercise: 2 stars, standard, optional (evenb_S)*)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn']. reflexivity.
  destruct n' eqn:E.
  reflexivity.
  rewrite -> IHn'.
  rewrite -> negb_involutive.
  simpl.
  reflexivity.
Qed.
(*Proof with proofs*)
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.
Theorem plus_assoc': forall n m p: nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0*)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.
(*Exercise: 2 stars, advanced, recommended (plus_comm_informal)*)
Theorem plus_comm': forall n m: nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.
(*Exercise: 2 stars, standard, optional (eqb_refl_informal)*)
Theorem eql_theo: forall n: nat,
  true= (n =? n).
Proof.
  intros n. induction n as [| n IHn'].
  - reflexivity. 
  - simpl. rewrite <- IHn'. reflexivity.
Qed.




