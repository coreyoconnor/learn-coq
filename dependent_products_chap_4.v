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
(* nope
Definition compose [A B C] (f : A->B) (g : B->C) (a:A) := g (f a).
*)

Definition compose {A B C : Set} (f : A->B) (g : B->C) (a:A) := g (f a).
Print compose.

(* Well, that was the same as before when I didn't specify : Set *)
