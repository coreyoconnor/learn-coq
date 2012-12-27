Require Import Arith.

Parameters (prime_divisor : nat -> nat)
           (prime : nat -> Prop)
           (divides : nat -> nat -> Prop).

Open Scope nat_scope.


Check (prime (prime_divisor 220)).
Check (divides (prime_divisor 220) 20).

Check (divides 3).

Parameter binary_word : nat -> Set.

Definition short : Set := binary_word 32.
Definition long : Set := binary_word 64.

(* I have a hard time understanding the difference between Prop and Set.
I currently have the sense that Prop is the sort used for logic. While Set is the sort
used for programs.
Which, would mean that "not" could not be applied to Set. Which makes sense:
what's the negation of a program?
*)

Check not.

Check (let d := prime_divisor 220 in prime d /\ divides d 220).

Require Import List.

Parameters (decomp1 : nat -> list nat)
           (decomp2 : nat -> nat*nat).

Check (decomp1 220).
Check list nat.
Check (decomp2 2123).

(* OK. The type of pair is A*B while the term of pairs uses the "standard" notation
(A,B). *)
Check (4,2).

(* I guess prod is the non infix operator version of *? but only on the type level? *)
Check prod.
Check (prod nat nat).

(* How can I check what the * type operator is then? *)

Check pair.
Check (pair 4 3).
Check (pair 4 3 : prod nat nat).

Check le_n.
Check le_S.
Check (le_n 36).
Definition le_36_37 := le_S 36 36 (le_n 36).
Check le_36_37.
Definition le_36_38 := le_S 36 37 le_36_37.
Check le_36_38.
Check (le_S _ _ (le_S _ _ (le_n 36))).

Parameter iterate : forall A:Set, (A->A) -> nat -> A -> A.
Check (iterate nat).
Check (iterate _ (mult 2)).

(* twice if a function that applies a function twice to a given value.
We have to explicitly account for the application of the type to the function.
 *)

Definition twice : forall A:Set, (A->A) -> A -> A
  := fun A f a => f (f a).

Check mult.
Check (mult 2).
Check (twice nat (mult 2)).

Eval compute in
    (twice nat (mult 2) 2).
Eval compute in
    (twice _ (twice _ (mult 2)) 2).
Eval compute in
    (twice (nat->nat) (fun f x => f (f x)) (mult 3) 1).

Theorem le_i_SSi : forall i : nat, i <= S (S i).
  Proof (fun i:nat => le_S _ _ (le_S _ _ (le_n i))).

Definition compose : forall A B C : Set, (A->B) -> (B->C) -> A -> C
  := fun A B C f g x => g (f x).

Print compose.

Require Import ZArith.

Check (fun (A:Set) (f: Z-> A) => compose _ _ _ Z_of_nat f).

Check (compose _ _ _ Zabs_nat (plus 32) (-45)%Z).

Eval compute in
    (compose _ _ _ Zabs_nat (plus 32) (-45)%Z).

Check (le_i_SSi 1515).

Check (le_S _ _ (le_i_SSi 1515)).

(* The book claims that this will fail. In the version of Coq I'm using, 8.4, the
joker is replaced by an existential variable. At least that's what I think is happening
I'm not entirely sure...
*)
Check (iterate _ (fun x => x) 23).

(* With at least Coq 8.4 the implicit argument system is much improved IMO.
Implicit arguments can be defined a priori by surrounding the arguments with curly
brackets. The book was written when this was the standard method:

Implicit Arguments compose [A B C].

Which is an posteriori method. With at least coq 8.4 there is a new posteriori method.
This method better matches the a priori method of curly brackets IMO.
*)
Arguments compose {A B C} f g x.
Check (compose Zabs_nat (plus 34)).

Eval compute in
    (compose Zabs_nat (plus 34) 223%Z).

(* how nice! *)

Check (compose (C := Z) S).

(* The follow also works with coq 8.4 but inserts an existential variable *)
Check (compose S).

(* I wonder how to use these existential variables? *)

(* Lets try with.. *)
Reset compose.
Set Implicit Arguments.

Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (a:A) := g (f a).
Definition thrice (A:Set) (f:A->A) := compose f (compose f f ).
Unset Implicit Arguments.

Print compose.

(* Ah neat! The print tells me which arguments are implicit!.
Lets try using the curly bracket method.
*)
Reset compose.
Definition compose {A B C} (f : A->B) (g : B->C) (a:A) := g (f a).
Print compose.

(* Well, that was almost the same but A B C are "maximally inserted".
I presume this means that the types are the upper bounds of the inferred sort?
Does the Arguments square brackets for implicit arguments which are not maximally
inserted work as well?
*)
Reset compose.
(* nope! The following does not compile.
Definition compose [A B C] (f : A->B) (g : B->C) (a:A) := g (f a).
*)

Definition compose {A B C : Set} (f : A->B) (g : B->C) (a:A) := g (f a).
Print compose.

(* Well, that was the same as before when I didn't specify : Set *)

(* Strange... I've already imported ZArith. I had to import ZArith again. Perhaps
due to the previous Reset?
*)
Require Import ZArith.
Check (list Z). (* sort Set *)

Section A_declared.
  Variables (A:Set)(P Q:A -> Prop)(R:A->A->Prop).

  Theorem all_perm : (forall a b :A, R a b) -> forall a b:A, R b a.
    intro.
    exact (fun a b : A => H b a).
  Qed.

  Theorem all_imp_dist : (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
    intros H0 H1.
    exact (fun a : A => H0 a (H1 a)).
  Qed.

  Theorem all_delta : (forall a b:A, R a b) -> (forall a:A, R a a).
    intros H0.
    exact (fun a : A => H0 a a).
  Qed.
End A_declared.

Definition my_plus : nat->nat->nat := iterate nat S.
Eval compute in (my_plus 3 4).

(* We never defined iterate. Just declared it. So Eval resulted in
"iterate nat S 3 4"
which is as good as we can do with just a declaration.
Neat!
*)

Definition my_mult (n p:nat) : nat := iterate nat (my_plus n) p 0.
Eval compute in (my_mult 3 4).

Definition my_expo (x n:nat) : nat := iterate nat (my_mult x) n 1.

Definition ackermann (n:nat) : nat -> nat :=
  iterate (nat -> nat)
          (fun (f:nat -> nat) (p:nat) => iterate nat f (S p) 1)
          n
          S.

(* Well, now I do some strange stuff. I want to check that a term when interpreted as a proposition
has a given type.
So I define the term. Then check that the term as a proposition has a type.
Then I prove the term can be inhabited.
This is weird, but hey, it works. I'm sure there is a better way.
*)
Section Exercise_4_4.
  Definition id := forall A:Set, A -> A.
  Check (id -> Prop) : Type.
  Theorem id_spec : id.
  Proof.
    unfold id.
    intros.
    apply H.
  Qed.

  Print id_spec.

  Definition diag := forall A B:Set, (A->A->B)->A->B.

  Check (diag -> Prop) : Type.

  Theorem diag_spec : diag.
  Proof.
    unfold diag.
    exact (fun (A B : Set) (f : A->A->B) A => f A A).
  Qed.


  Definition permute := forall A B C:Set, (A->B->C)->B->A->C.
  Check (permute -> Prop) : Type.

  Theorem permute_spec : permute.
  Proof.
    unfold permute.
    exact (fun (A B C:Set) (f : A->B->C) B A => f A B).
  Qed.

  Print permute_spec.

End Exercise_4_4.

Check (forall P:Prop, P->P).
Check (fun (P:Prop) (p:P) => p).

Section Exercise_4_5.
  Definition all_perm_def := forall (A:Type) (P:A->A->Prop), (forall x y:A, P x y)
                                                             -> forall x y:A, P y x.

  Theorem all_perm_4_5 : all_perm_def.
  Proof.
    unfold all_perm_def.
    intros H_A H_P H_0.
    exact (fun (x y:H_A) => H_0 y x).
  Qed.

  Print all_perm_4_5.
  
  Definition resolution_def :=
    forall (A:Type) (P Q R S:A -> Prop), (forall a:A, Q a -> R a -> S a)
                                           -> (forall b:A, P b -> Q b)
                                                -> (forall c:A, P c -> R c -> S c).

  Theorem resolution_4_5 : resolution_def.
  Proof.
    unfold resolution_def.
    intros.
    apply H.
    apply H0.
    assumption.
    assumption.
  Qed.

  Print resolution_4_5.
End Exercise_4_5.


Theorem thirty_six : 9*4=6*6.
  apply (refl_equal 36).
Qed.

Print thirty_six.

