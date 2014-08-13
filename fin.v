Require Import notations proof_irrelevances decidables.

Definition fin n := { i: nat | i <= n }.
Definition le_to_fin {n i} (p: i <= n): fin n := exist _ _ p.

Definition fin_zero n: fin n := exist _ 0 (Le.le_0_n n).
Definition fin_limit n: fin n := exist _ n (le_n n).

Definition fin_pred {n} (i: fin n): fin n := exist _ (pred i.1) (NPeano.Nat.le_le_pred _ _ i.2).
Definition fin_sym {n} (i: fin n): fin n := exist _ (n - i.1) (Minus.le_minus _ _).
Definition fin_S {n} (i: fin n): fin n.
 exists (if le_dec n i.1 then i.1 else S i.1); destruct le_dec, i; auto.
Defined.

Theorem fin_eq_thm {limit} (n m: fin limit): n = m <-> n.1 = m.1.
 destruct n, m; simpl; split; intros; [inversion H; auto | destruct H; f_equal; apply le_PI].
Qed.

Theorem fin_neq_thm {limit} (n m: fin limit): n <> m <-> n.1 <> m.1.
 split; intro; intro; elim H; apply fin_eq_thm; auto.
Qed.

