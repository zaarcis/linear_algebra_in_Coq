Require Export fin.
Require Import notations decidables Setoid Morphisms.

Definition vect A n := fin n -> A.
Definition vect_eq {A n} (v1 v2: vect A n) := forall i, v1 i = v2 i.
Definition vect_sym {A n} (v: vect A n): vect A n := fun i => v (fin_sym i).

Definition remove_element {A n} (num: fin (S n)) (v: vect A (S n)): vect A n :=
 fun i => if le_dec i.1 num.1 then v (le_to_fin (le_S _ _ i.2)) else v (le_to_fin (Le.le_n_S _ _ i.2)).

Definition vect_swap {A n} (i j: fin n) (v: vect A n): vect A n :=
 fun m => if eq_dec i.1 m.1 then v j else if eq_dec j.1 m.1 then v i else v m.
Theorem vect_swap_involutive {A n} (i j: fin n) (v: vect A n): vect_eq (vect_swap i j (vect_swap i j v)) v.
 unfold vect_eq, vect_swap; intro; destruct i, j, i0; simpl; repeat destruct eq_dec; f_equal; apply fin_eq_thm; simpl;
 congruence.
Qed.
Theorem vect_swap_sym {A n} (i j: fin n) (v: vect A n): vect_eq (vect_swap i j v) (vect_swap j i v).
 unfold vect_eq, vect_swap; intro; destruct i, j, i0; simpl; repeat destruct eq_dec; f_equal; apply fin_eq_thm; simpl;
 congruence.
Qed.

Definition vect_fold_right' {A B n} (f: B -> A -> B) (i: fin n) (start: B) (v: vect A n) :=
 let fix aux {A B n i} (f: B -> A -> B) (v: vect A n): i <= n -> B -> B :=
  match i with
  | O => fun (H: O <= n) b => f b (v (fin_zero n))
  | S m => fun (H: S m <= n) b => f (aux f v (Le.le_Sn_le _ _ H) b) (v (le_to_fin H))
  end
 in aux f v i.2 start.
Definition vect_fold_left' {A B n} (f: B -> A -> B) (i: fin n) (start: B) (v: vect A n) := vect_fold_right' f i start (vect_sym v).
Definition vect_fold_right {A B n} (f: B -> A -> B) (start: B) (v: vect A n) := vect_fold_right' f (fin_limit n) start v.
Definition vect_fold_left {A B n} (f: B -> A -> B) (start: B) (v: vect A n) := vect_fold_left' f (fin_limit n) start v.

Definition vect_to_list {A n} (v: vect A n): list A := vect_fold_left (fun x y => cons y x) nil v.


Instance vect_eq_Equiv A n: Equivalence (vect_eq (A:=A) (n:=n)).
 split; unfold Reflexive, Symmetric, Transitive, vect_eq; congruence.
Qed.
Instance vect_sym_Proper A n: Proper (vect_eq ==> vect_eq) (vect_sym (A:=A) (n:=n)).
 unfold Proper, respectful, vect_eq, vect_sym; auto.
Qed.
Instance remove_element_Proper A n num: Proper (vect_eq ==> vect_eq) (remove_element (A:=A) (n:=n) num).
 unfold Proper, respectful, vect_eq, remove_element; intros; destruct le_dec; auto.
Qed.
Instance vect_swap_Proper A n i j: Proper (vect_eq ==> vect_eq) (vect_swap (A:=A) (n:=n) i j).
 unfold Proper, respectful, vect_eq, vect_swap; intros; repeat destruct eq_dec; auto.
Qed.
Instance vect_fold_right'_Proper A B n f i start: Proper (vect_eq ==> eq) (vect_fold_right' (A:=A) (B:=B) (n:=n) f i start).
 unfold Proper, respectful, vect_eq, vect_fold_right'; destruct i; simpl; intros;
 induction x; rewrite H; [| rewrite IHx]; auto.
Qed.
Instance vect_fold_left'_Proper A B n f i start: Proper (vect_eq ==> eq) (vect_fold_left' (A:=A) (B:=B) (n:=n) f i start).
 unfold Proper, respectful, vect_fold_left'; intros; rewrite H; auto.
Qed.
Instance vect_fold_right_Proper A B n f start: Proper (vect_eq ==> eq) (vect_fold_right (A:=A) (B:=B) (n:=n) f start) :=
 vect_fold_right'_Proper A B n f (fin_limit n) start.
Instance vect_fold_left_Proper A B n f start: Proper (vect_eq ==> eq) (vect_fold_left (A:=A) (B:=B) (n:=n) f start) :=
 vect_fold_left'_Proper A B n f (fin_limit n) start.
