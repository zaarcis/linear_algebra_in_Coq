Require Export vectors.
Require Import notations decidables Setoid Morphisms.

Definition matr A rows cols := fin rows -> fin cols -> A.
Definition matr_eq {A rows cols} (M1 M2: matr A rows cols) := forall i j, M1 i j = M2 i j.

Definition matr_row {A rows cols} (i: fin rows) (M: matr A rows cols): vect A cols := fun j => M i j.
Definition matr_col {A rows cols} (j: fin cols) (M: matr A rows cols): vect A rows := fun i => M i j.

Definition matr_transpose {A rows cols} (M: matr A rows cols): matr A cols rows := fun i j => M j i.

Definition remove_row {A rows cols} (num: fin (S rows)) (M: matr A (S rows) cols): matr A rows cols :=
 fun i j => if le_dec i.1 num.1 then M (le_to_fin (le_S _ _ i.2)) j else M (le_to_fin (Le.le_n_S _ _ i.2)) j.
Definition remove_col {A rows cols} (num: fin (S cols)) (M: matr A rows (S cols)): matr A rows cols :=
 fun i j => if le_dec j.1 num.1 then M i (le_to_fin (le_S _ _ j.2)) else M i (le_to_fin (Le.le_n_S _ _ j.2)).


Instance matr_eq_Equiv A n: Equivalence (vect_eq (A:=A) (n:=n)).
 split; unfold Reflexive, Symmetric, Transitive, matr_eq; congruence.
Qed.
Instance matr_row_Proper A rows cols i: Proper (matr_eq ==> vect_eq) (matr_row (A:=A) (rows:=rows) (cols:=cols) i).
 unfold Proper, respectful, matr_eq, vect_eq, matr_row; auto.
Qed.
Instance matr_col_Proper A rows cols i: Proper (matr_eq ==> vect_eq) (matr_col (A:=A) (rows:=rows) (cols:=cols) i).
 unfold Proper, respectful, matr_eq, vect_eq, matr_col; auto.
Qed.
Instance matr_transpose_Proper A rows cols: Proper (matr_eq ==> matr_eq) (matr_transpose (A:=A) (rows:=rows) (cols:=cols)).
 unfold Proper, respectful, matr_eq, matr_transpose; auto.
Qed.
Instance remove_row_Proper A rows cols num: Proper (matr_eq ==> matr_eq) (remove_row (A:=A) (rows:=rows) (cols:=cols) num).
 unfold Proper, respectful, matr_eq, remove_row; intros; repeat destruct le_dec; auto.
Qed.
Instance remove_col_Proper A rows cols num: Proper (matr_eq ==> matr_eq) (remove_col (A:=A) (rows:=rows) (cols:=cols) num).
 unfold Proper, respectful, matr_eq, remove_col; intros; repeat destruct le_dec; auto.
Qed.

