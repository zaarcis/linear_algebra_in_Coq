Require Import notations decidables Setoid Morphisms.
Require Export vectors.
Require Import List.

Definition transp n := prod (fin n) (fin n).
Definition perm n := list (transp n).

Definition vect_transp {A n} (v: vect A n) (t: transp n) := vect_swap (fst t) (snd t) v.
Definition vect_perm {A n} (p: perm n) (v: vect A n) := fold_left vect_transp p v.

Definition transp_eq {n} (t1 t2: transp n) := forall A (v: vect A n), vect_eq (vect_transp v t1) (vect_transp v t2).
Definition perm_eq {n} (p1 p2: perm n) := forall A (v: vect A n), vect_eq (vect_perm p1 v) (vect_perm p2 v).
Definition perm_mult {n} (p1 p2: perm n): perm n := List.app p1 p2.
Definition perm_inv {n} (p: perm n): perm n := List.rev p.

Instance transp_eq_Equiv n: Equivalence (transp_eq (n:=n)).
 split; unfold Reflexive, Symmetric, Transitive, transp_eq; intros;
 [ reflexivity | symmetry | rewrite H ]; auto.
Qed.
Instance perm_eq_Equiv n: Equivalence (perm_eq (n:=n)).
 split; unfold Reflexive, Symmetric, Transitive, perm_eq; intros;
 [ reflexivity | symmetry | rewrite H ]; auto.
Qed.

Instance vect_transp_Proper A n: Proper (vect_eq ==> transp_eq ==> vect_eq) (vect_transp (A:=A) (n:=n)).
 unfold Proper, respectful, transp_eq, vect_transp; intros; rewrite H; auto.
Qed.

Theorem transp_involutive {n} (t: transp n): perm_eq (t :: t :: nil) nil.
 intros A v; apply vect_swap_involutive. Qed.
Theorem transp_mult_left {n} (t: transp n) (p: perm n): t :: p = perm_mult (t :: nil) p.
 reflexivity. Qed.
Theorem transp_mult_rigth {n} (t: transp n) (p: perm n): p ++ t :: nil = perm_mult p (t :: nil).
 reflexivity. Qed.

Instance vect_perm_Proper A n: Proper (perm_eq ==> vect_eq ==> vect_eq) (vect_perm (A:=A) (n:=n)).
 pose proof vect_swap_Proper; unfold Proper, respectful in *; intros.
 assert (forall p v1 v2, vect_eq v1 v2 -> vect_eq (vect_perm (A:=A) (n:=n) p v1) (vect_perm p v2)) by
  (induction p; intros; simpl; unfold vect_transp; auto).
 etransitivity; auto.
Qed.

Theorem perm_mult_app {A n} (v: vect A n) (p1 p2: perm n): vect_perm (perm_mult p1 p2) v = vect_perm p2 (vect_perm p1 v).
 apply fold_left_app. Qed.
Theorem perm_mult_assoc {n} (p1 p2 p3: perm n): perm_mult (perm_mult p1 p2) p3 = perm_mult p1 (perm_mult p2 p3).
 unfold perm_eq, vect_eq, perm_mult; rewrite List.app_assoc; auto.
Qed.
Instance perm_mult_Proper n: Proper (perm_eq ==> perm_eq ==> perm_eq) (perm_mult (n:=n)).
 unfold Proper, respectful, perm_eq; intros.
 repeat rewrite perm_mult_app; rewrite H, H0; reflexivity.
Qed.

Theorem transp_involutive_left {n} (t: transp n) (p: perm n): perm_eq (t :: t :: p) p.
 assert (t :: t :: p = perm_mult (t :: t :: nil) p) by auto.
 rewrite H, transp_involutive; reflexivity.
Qed.
Theorem transp_involutive_right {n} (t: transp n) (p: perm n): perm_eq (perm_mult p (t :: t :: nil)) p.
 unfold perm_mult; rewrite transp_involutive, app_nil_r; reflexivity.
Qed.

Theorem perm_mult_nil_left {n} (p: perm n): perm_mult nil p = p.
 reflexivity. Qed.
Theorem perm_mult_nil_right {n} (p: perm n): perm_mult p nil = p.
 apply app_nil_r. Qed.

Theorem perm_mult_inv {n} (p1 p2: perm n): perm_inv (perm_mult p1 p2) = perm_mult (perm_inv p2) (perm_inv p1).
 apply rev_app_distr. Qed.
Theorem perm_inv_mult_left {n} (p: perm n): perm_eq (perm_mult (perm_inv p) p) nil.
 induction p.
  reflexivity.
  rewrite (transp_mult_left a p), perm_mult_inv, perm_mult_assoc; simpl; rewrite transp_involutive_left; auto.
Qed.
Theorem perm_inv_mult_right {n} (p: perm n): perm_eq (perm_mult p (perm_inv p)) nil.
 induction p.
  reflexivity.
  rewrite (transp_mult_left a p), perm_mult_inv, perm_mult_assoc, <- (perm_mult_assoc p), IHp; apply transp_involutive_left.
Qed.

Theorem perm_inv_involutive {n} (p: perm n): perm_eq (perm_inv (perm_inv p)) p.
 unfold perm_inv; rewrite rev_involutive; reflexivity.
Qed.

(*
Definition T1 {A n} (v1 v2: vect A n) (t: transp n): vect_eq (vect_transp v1 t) (vect_transp v2 t) -> vect_eq v1 v2.
 intro. unfold vect_transp in *. rewrite <- (twice_transp_is_id t). rewrite <- (twice_transp_is_id t A v2).
 rewrite H. reflexivity.
Qed.

Definition T2 {A n} (v1 v2: vect A n) (p: perm n): vect_eq (vect_perm p v1) (vect_perm p v2) -> vect_eq v1 v2.
 revert v1 v2. induction p.
  simpl in *. auto.
  simpl in *. intros. apply IHp in H. apply T1 with (t:=a). auto.
Qed.
*)

Theorem T0 {n} (p p1 p2: perm n): perm_eq p1 p2 -> perm_eq (perm_mult p p1) (perm_mult p p2).
 intro; rewrite H; reflexivity.
Qed.

Theorem T1 {n} (p: perm n): perm_eq nil p -> perm_eq (perm_inv p) nil.
 intro; apply (T0 (perm_inv p)) in H; rewrite perm_inv_mult_left, perm_mult_nil_right in H; auto.
Qed.

Instance perm_inv_Proper n: Proper (perm_eq ==> perm_eq) (perm_inv (n:=n)).
 unfold Proper, respectful.
 induction x; intros.
  symmetry; exact (T1 y H).
  intros.
   apply (T0 (a :: nil)) in H; simpl in H; rewrite transp_involutive_left in H; apply IHx in H.
   rewrite transp_mult_left, perm_mult_inv, H; simpl (perm_inv (a :: nil)).
   rewrite transp_mult_left, perm_mult_inv, perm_mult_assoc; simpl; rewrite transp_involutive_right; reflexivity.
Qed.


Inductive parity := even | odd.
Definition change_parity p := match p with even => odd | odd => even end.
Definition transp_is_id {n} (p: transp n) := eq_dec (fst p).1 (snd p).1.
Definition perm_parity {n} (p: perm n) :=
 List.fold_left (fun p t => if transp_is_id t then p else change_parity p) p even.
