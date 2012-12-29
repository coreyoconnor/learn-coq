Require Import Arith.
Require Import ZArith.

Theorem le_mult_mult :
  forall a b c d : nat, a <= c -> b <= d -> a*b <= c*d.
Proof.
  intros a b c d H H0.
  Print le_trans.
  apply le_trans with (m := c*b).
  Print mult_le_compat_r.
  apply mult_le_compat_r.
  apply H.
  apply mult_le_compat_l.
  apply H0.
Qed.

Print le_mult_mult.

Theorem le_mult_mult' :
  forall a b c d : nat, a <= c -> b <= d -> a*b <= c*d.
Proof.
  intros a b c d H H0.
  eapply le_trans.
  eapply mult_le_compat_r.
  apply H.
  eapply mult_le_compat_l.
  apply H0.
Qed.

Theorem my_lt_S : forall n p : nat, n < p -> n < S p.
Proof.
  intros n p H.
  SearchPattern (_ < S _).
  (* well, obviously we could use the predefined lt_S. Skip that for now *)
  (* In the book trivial is used and "Note that the occurrence of lt found in the
hypothesis H is delta reduced automatically by [trivial].."
Well, I'd like to do this explicitly for now. *)
  unfold lt in H.
  unfold lt.
  apply le_S.
  apply H.
Qed.

Definition opaque_f : nat->nat->nat.
  intros.
  assumption.
Qed.

(* interesting.. assumption used the *first* hypothesis that matched. There
is a bias in the search. Which makes sense. I suppose that the witness can be
tailored by using apply to specify which hypothesis to apply.
*)
Print opaque_f.

Open Scope Z_scope.

Definition Zsquare_diff (x y : Z) := x*x - y*y.

Theorem unfold_example :
  forall x y : Z, x * x = y * y -> Zsquare_diff x y * Zsquare_diff (x+y)(x*y) = 0.
Proof.
  intros x y H_eq.
  unfold Zsquare_diff at 1.
  (* I don't know how to deal with equality yet....*)
Abort.

Section ex_5_2_6.
  Parameters (A:Type)
             (P Q: A->Prop).
  Theorem ex_imp_ex :
    (ex P) -> (forall x : A, P x -> Q x) -> (ex Q).
    intros H H0.
    elim H.
    intros x Hx.
    exists x.
    apply H0.
    apply Hx.
  Qed.

  Theorem ex_5_9_a :
    (exists (x : A), P x \/ Q x) -> (ex P) \/ (ex Q).
  Proof.
    intros H.
    elim H.
    intros x H_PQ.
    elim H_PQ.
    intros H_Px.
    left.
    exists x.
    apply H_Px.
    intros H_Qx.
    right.
    exists x.
    apply H_Qx.
  Qed.

  Theorem ex_5_9_b :
    (ex P) \/ (ex Q) -> (exists x: A, P x \/ Q x).
  Proof.
    intro H_or.
    elim H_or.
    intro H_Px.
    elim H_Px.
    intros x H_Px'.
    exists x.
    left.
    apply H_Px'.
    intro H_ex_Qx.
    elim H_ex_Qx.
    intros x H_Qx.
    exists x.
    right.
    apply H_Qx.
  Qed.

  Theorem ex_5_9_c :
    (exists x : A, forall R:A -> Prop, R x) -> 2 = 3.
  Proof.
    intros H.
    elim H.
    intros x Hx.
    elim (Hx (fun y:A => False)).
  Qed.

  Theorem ex_5_9_d :
    (forall x : A, P x) -> ~(exists y : A, ~ P y).
  Proof.
    intros.
    unfold not.
    intros.
    elim H0.
    intros.
    apply H1.
    apply H.
  Qed.
End ex_5_2_6.

Theorem eq_sym' : forall (A:Type) (a b :A), a=b -> b=a.
Proof.
  intros A a b.
  intros H_eq_a_b.
  rewrite H_eq_a_b.
  reflexivity.
Qed.

Theorem Zmult_distr_1 : forall n x : Z, n*x+x = (n+1)*x.
Proof.
  intros n x.
  Print Zmult_plus_distr_l.
  rewrite -> Zmult_plus_distr_l.
  rewrite -> Zmult_1_l.
  reflexivity.
Qed.

Theorem regroup : forall x:Z, x+x+x+x+x = 5 * x.
Proof.
  intros x.
  pattern x at 1.
  rewrite <- Zmult_1_l.
  Print Zmult_distr_1.
  repeat rewrite -> Zmult_distr_1.
  auto with zarith.
Qed.

Close Scope Z_scope.

Theorem plus_permute2 :
  forall n m p:nat, n+m+p = n+p+m.
Proof.
  intros n m p.
  Print plus_comm.
  Print plus_assoc.
  rewrite <- plus_assoc.
  Print plus_comm.
  pattern (m+p) at 1.
  rewrite plus_comm.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

(* intuitively I read rewrite <- X as "use X to rewrite the goal to contain the left
side of X"
No idea if that's correct, but works OK so far.
*)
