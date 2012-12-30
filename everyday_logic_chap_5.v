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

(* According to the book this should find Zmult_1_l. However, no such theorem is
found. Hmmm. *)

SearchRewrite (1 * _)%Z.

(* however, this does find a rewrite *)
SearchRewrite (_ * 1)%Z.

Definition my_True : Prop := forall P:Prop, P->P.

Definition my_False : Prop := forall P:Prop, P.

Theorem m_I : my_True.
Proof.
  unfold my_True. (* not required, but I like being clear *)
  intros P p.
  assumption.
Qed.

(* This should be impossible to prove. *)
Theorem my_F : my_False.
Proof.
  unfold my_False.
  intros P.
  (* Well, we need a witness of P but we only have a proposition of P.
nothing more. darn!
*)
Abort.

(* OK. Anything should be provable if my_False is in the assumptions. *)

Theorem my_False_ind : forall P:Prop, my_False -> P.
Proof.
  intros P F.
  unfold my_False in F. (* also not required, but nice for clarity. *)
  apply F.
Qed.

(* Well, yep, for any proposition, if my_False is in the assumption we can prove
that assumption. *)

Print my_False_ind.

Theorem my_False_ind' : forall P:Prop, my_False -> P.
Proof.
  exact (fun (P0 : Prop) (f : my_False) => f P0).
Qed.

Definition my_not (P : Prop) : Prop := P -> my_False.

Section leibniz.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Variable A : Set.

  Definition leibniz (a b : A) : Prop :=
    forall P:A -> Prop, P a -> P b.

  Require Import Relations.

  Theorem leibniz_sym : symmetric A leibniz.
  Proof.
    unfold symmetric.
    unfold leibniz.
    intros x y H Q.
    apply H.
    trivial.
  Qed.

  Theorem leibniz_refl : reflexive A leibniz.
  Proof.
    unfold reflexive.
    intros x.
    unfold leibniz.
    intros P0.
    trivial.
  Qed.

  Theorem leibniz_trans : transitive A leibniz.
  Proof.
    unfold transitive.
    intros x y z.
    unfold leibniz.
    intros P0 P1.
    intros P2.
    intros H_P2_x.
    apply P1.
    apply P0.
    apply H_P2_x.
  Qed.

  Theorem leibniz_equiv : equiv A leibniz.
  Proof.
    unfold equiv.
    split.
    apply leibniz_refl.
    split.
    apply leibniz_trans.
    apply leibniz_sym.
  Qed.

  Theorem leibniz_least_reflexive :
    forall R:relation A, reflexive A R -> inclusion A leibniz R.
  Proof.
    intros R H_refl.
    unfold inclusion.
    intros x y H_l_x_y.
    unfold relation in R.
    unfold leibniz in H_l_x_y.
    unfold reflexive in H_refl.
    apply H_l_x_y.
    apply H_refl.
  Qed.

  Theorem leibniz_eq : forall a b : A, leibniz a b -> a = b.
  Proof.
    intros a b H_l_a_b.
    unfold leibniz in H_l_a_b.
    pattern a.
    apply H_l_a_b.
    trivial.
  Qed.

  Theorem eq_leibniz : forall a b : A, a = b -> leibniz a b.
  Proof.
    intros a b.
    intros H_eq.
    unfold leibniz.
    intros P0 H_P0.
    rewrite <- H_eq.
    apply H_P0.
  Qed.

  Theorem leibniz_ind :
    forall (x:A) (P:A->Prop), P x -> forall y:A, leibniz x y -> P y.
  Proof.
    intros x P0 H_P0 y H_l_x_y.
    unfold leibniz in H_l_x_y.
    apply H_l_x_y.
    apply H_P0.
  Qed.

  Unset Implicit Arguments.
End leibniz.


Definition my_and (P Q : Prop) := forall R:Prop, (P->Q->R)->R.
Definition my_or (P Q : Prop) := forall R:Prop, (P->R)->(Q->R)->R.
Definition my_ex (A:Set) (P:A->Prop) := forall R:Prop, (forall x:A, P x -> R) -> R.


Section ex_5_5_4.
  Theorem my_and_l : forall P Q : Prop, my_and P Q -> P.
  Proof.
    intros P0 Q0 H_my_and.
    unfold my_and in H_my_and.
    apply H_my_and.
    intros.
    apply H.
  Qed.

  Theorem my_and_r : forall P Q : Prop, my_and P Q -> Q.
  Proof.
    intros.
    unfold my_and in H.
    apply H.
    intros.
    apply H1.
  Qed.

  Theorem my_and_ind : forall P Q R : Prop, (P->Q->R)-> my_and P Q -> R.
  Proof.
    intros P0 Q0 R.
    intros H_and_f.
    unfold my_and.
    intros H_and.
    apply H_and_f.
    apply H_and.
    intros.
    exact H.
    apply H_and.
    trivial.
  Qed.

  Theorem my_or_l : forall P Q : Prop, P -> my_or P Q.
  Proof.
    intros.
    unfold my_or.
    intros R H_l H_r.
    apply H_l.
    apply H.
  Qed.

  Theorem my_or_r : forall P Q : Prop, Q -> my_or P Q.
  Proof.
    intros.
    unfold my_or.
    intros R H_l H_r.
    apply H_r.
    apply H.
  Qed.

  Theorem my_or_ind : forall P Q R : Prop, (P->R) -> (Q->R) -> my_or P Q -> R.
  Proof.
    intros P0 Q0 R H_l H_r H_my_or.
    unfold my_or in H_my_or.
    apply H_my_or.
    apply H_l.
    apply H_r.
  Qed.

  Theorem my_or_false_r : forall P : Prop, my_or P my_False -> P.
  Proof.
    intros P0.
    unfold my_or.
    intros.
    apply H.
    trivial.
    apply my_False_ind.
  Qed.

  Theorem my_or_refl : forall P Q : Prop, my_or P Q -> my_or Q P.
  Proof.
    intros P0 Q0 H_or_p_q.
    unfold my_or.
    intros R H_l H_r.
    unfold my_or in H_or_p_q.
    apply H_or_p_q.
    apply H_r.
    apply H_l.
  Qed.

  Theorem my_ex_ind : forall (A:Set) (P:A->Prop) (a:A), P a -> my_ex A P.
  Proof.
    intros A0 P0 a H_P0.
    unfold my_ex.
    intros R H_p_r.
    apply H_p_r with (x := a).
    exact H_P0.
  Qed.

  Theorem my_not_ex : forall (A:Set) (P:A->Prop),
                        my_not (my_ex A P) -> forall a:A, my_not (P a).
  Proof.
    intros A0 P0 H_not_ex a.
    unfold my_not.
    intro H_P0.
    unfold my_not in H_not_ex.
    apply H_not_ex.
    unfold my_ex.
    intros R H_x_P0.
    apply H_x_P0 with (x := a).
    exact H_P0.
  Qed.
End ex_5_5_4.

