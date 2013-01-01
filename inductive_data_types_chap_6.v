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

