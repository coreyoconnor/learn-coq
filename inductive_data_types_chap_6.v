Inductive month : Set :=
  | January  | February | March  | April     | May
  | June     | July    | August | September | October
  | November | December.

Print month_rect.
Print month_ind.
Print month_rec.

Inductive season : Set :=
  | Winter | Spring | Summer | Fall.

Print month_rec.

Definition season_for_month : month -> season
  := month_rec (fun _ => season)
               Winter Winter Winter
               Spring Spring Spring
               Summer Summer Summer
               Fall Fall Fall.

Print season_for_month.

Definition season_for_month' (m : month) : season :=
  match m with
      | January => Winter
      | February => Winter
      | March => Winter
      | April => Spring
      | May => Spring
      | June => Spring
      | July => Summer
      | August => Summer
      | September => Summer
      | October => Fall
      | November => Fall
      | December => Fall
  end.


Theorem month_equal :
  forall m : month, m = January \/ m = February \/ m = March     \/
                    m = April   \/ m = May      \/ m = June      \/
                    m = July    \/ m = August   \/ m = September \/
                    m = October \/ m = November \/ m = December.
Proof.
  intro m.
  pattern m.
  Check month_ind.
  apply month_ind.
  left. reflexivity.
  right. left. reflexivity.
  right. right. left. reflexivity.
  right. right. right. left. reflexivity.
  right. right. right. right. left. reflexivity.
  right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right. left. reflexivity.
  right. right. right. right. right. right. right. right. right.
  right. left. reflexivity.
  right. right. right. right. right. right. right. right. right.
  right. right. reflexivity.
Qed.

(* right? right. *)

Theorem bool_equal_0 : forall b : bool, b = true \/ b = false.
Proof.
  Check bool_ind.
  Check or_introl.
  Check or_intror.
  Check refl_equal.
  Check (bool_ind (fun b : bool => b = true \/ b = false)
                  (or_introl _ (refl_equal true))
                  (or_intror _ (refl_equal false))).
  exact (bool_ind (fun b : bool => b = true \/ b = false)
                  (or_introl _ (refl_equal true))
                  (or_intror _ (refl_equal false))).
Qed.

Theorem t : True \/ True.
Proof.
  Print or_introl.
  Print True.
  exact (or_introl True I).
Qed.

(* yep.. still don't know what I'm doing... :-[ *)


Theorem bool_equal_1 : forall b : bool, b = true \/ b = false.
Proof.
  intro b.
  pattern b.
  Check bool_ind.
  apply bool_ind.
  left.
  reflexivity.
  right.
  reflexivity.
Qed.

Section six_1_3.
  Definition f_0 (b : bool) :=
    match b with
    | true  => 1
    | false => 2
    end.

  Print f_0.

  Definition month_length (leap : bool) (m : month) : nat :=
    match m with
    | January  => 31
    | February => if leap then 29 else 28
    | March => 31
    | April => 30
    | May => 31
    | June => 30
    | July => 31
    | August => 31
    | September => 30
    | October => 31
    | November => 30
    | December => 31
    end.

  Check month_rec.
  Definition month_length' (leap : bool) : month -> nat :=
    month_rec (fun (m : month) => nat)
              31
              (if leap then 29 else 28)
              31
              30
              31
              30
              31
              31
              30
              31
              30
              31.

  Definition month_length'' (leap : bool) (m : month) : nat :=
    match m with
    | February => if leap then 29 else 28
    | April => 30
    | June => 30
    | September => 30
    | November => 30
    | otherwise => 31
    end.

  Eval compute in month_length'' false April.

End six_1_3.

Section ex_6_6.
  Definition bool_and (b1 b2 : bool) : bool :=
    match b1 with
    | true  => b2
    | false => false
    end.

  Definition bool_or (b1 b2 : bool) : bool :=
    match b1 with
    | true  => true
    | false => b2
    end.

  Definition bool_xor (b1 b2 : bool) : bool :=
    match b1 with
    | false => b2
    | true => match b2 with
              | true  => false
              | false => true
              end
    end.

  Definition bool_not (b : bool) : bool :=
    match b with
    | false => true
    | true  => false
    end.

  Definition bool_eq (b1 b2 : bool) : bool :=
    match b1 with
    | false => bool_not b2
    | true  => b2
    end.
              
  Theorem bool_xor_not_eq_iso : forall b1 b2 : bool,
                                     bool_xor b1 b2 = bool_not (bool_eq b1 b2).
  Proof.
    intros b1 b2.
    unfold bool_xor.
    unfold bool_not.
    unfold bool_eq.
    pattern b1.
    apply bool_ind.
    reflexivity.
    pattern b2.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.
  
  Theorem bool_not_and_iso_or_not_not : forall b1 b2 : bool,
                                          bool_not (bool_and b1 b2) =
                                          bool_or (bool_not b1) (bool_not b2).
  Proof.
    intros b1 b2.
    unfold bool_or.
    pattern b1.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

  Theorem bool_not_not_iso : forall b : bool, bool_not (bool_not b) = b.
  Proof.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

  Theorem bool_or_not_iso_true : forall b : bool, bool_or b (bool_not b) = true.
  Proof.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

  Theorem bool_eq_iso_eq : forall b1 b2 : bool, b1 = b2 -> bool_eq b1 b2 = true.
  Proof.
    intros b1 b2.
    pattern b2.
    apply bool_ind.
    intros H_b1_eq_true.
    rewrite -> H_b1_eq_true.
    simpl bool_eq.
    reflexivity.
    intros H_b1_eq_false.
    rewrite -> H_b1_eq_false.
    simpl bool_eq.
    reflexivity.
  Qed.

  Theorem not_or_eq_and_not_not : forall b1 b2 : bool,
                                    bool_not (bool_or b1 b2) = bool_and (bool_not b1)
                                                                        (bool_not b2).
  Proof.
    intros b1 b2.
    pattern b1.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.

  Theorem or_and_and_eq_and_or : forall b1 b2 b3 : bool,
                                   bool_or (bool_and b1 b3) (bool_and b2 b3) =
                                   bool_and (bool_or b1 b2) b3.
  Proof.
    intros b1 b2 b3.
    pattern b1.
    apply bool_ind.
    simpl.
    pattern b2.
    apply bool_ind.
    simpl.
    unfold bool_or.
    pattern b3.
    apply bool_ind.
    reflexivity.
    reflexivity.
    pattern b3.
    apply bool_ind.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  Qed.
End ex_6_6.

Require Import ZArith.

Inductive plane : Set := point : Z -> Z -> plane.

Print plane_ind.

Definition abscissa (p : plane) : Z :=
  match p with point x y => x end.

Reset plane.

Record plane : Set := point { abscissa : Z; ordinate : Z }.

Print plane.

Print abscissa.

Open Scope Z_scope.

Definition ex_6_8 (p : plane) : Z :=
  let (abscissa, ordinate) := p
  in Zabs abscissa + Zabs ordinate.

Eval compute in ex_6_8 (point 1 3).

Inductive vehicle : Set :=
  | bicycle   : nat -> vehicle
  | motorized : nat -> nat -> vehicle.

Print vehicle_ind.

Definition nb_wheels (v : vehicle) : nat :=
  match v with
  | bicycle _     => 2%nat
  | motorized _ n => n
  end.

Definition nb_seats (v : vehicle) : nat :=
  match v with
  | bicycle   n   => n
  | motorized n _ => n
  end.

Check vehicle_rec.

Definition nb_seats' (v : vehicle) : nat :=
  vehicle_rec (fun _   => nat)
              (fun n   => n)
              (fun n _ => n)
              v.

Print nb_seats'.
