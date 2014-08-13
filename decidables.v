Require Import Le.

Definition le_dec: forall m n, {m<=n} + {n<m}.
  refine (
    fix f m n: {m<=n} + {n<m} :=
    match m, n with
    | O, _ => left _ _
    | _, O => right _ _
    | S mm, S nn => match f mm nn with
                    | left _ => left _ _
                    | right _ => right _ _ end end);
 [ apply le_0_n |
   apply le_n_S; apply le_0_n |
   apply le_n_S; assumption |
   apply le_n_S; assumption ].
Defined.

Definition lt_dec: forall m n, {m<n} + {n<=m}.
  refine (
    fix f m n: {m<n} + {n<=m} :=
    match m, n with
    | _, O => right _ _
    | O, _ => left _ _
    | S mm, S nn => match f mm nn with
                    | left _ => left _ _
                    | right _ => right _ _ end end);
 [ apply le_0_n |
   apply le_n_S, le_0_n |
   apply le_0_n |
   apply le_n_S; assumption |
   apply le_n_S; assumption ].
Defined.

Definition lt_eq_lt_dec: forall m n, {m<n} + {m=n} + {n<m}.
  refine (
    fix f (m n:nat): {m<n} + {m=n} + {n<m} :=
    match m, n with
    | O, O => inleft _ (right _ _)
    | O, _ => inleft _ (left _ _)
    | _, O => inright _ _
    | S mm, S nn => match f mm nn with
                    | inleft (left _) => inleft _ (left _ _)
                    | inleft (right _) => inleft _ (right _ _)
                    | inright _ => inright _ _ end end);
 [ reflexivity |
   apply le_n_S; apply le_0_n |
   apply le_n_S; apply le_0_n |
   apply le_n_S; assumption |
   f_equal; assumption |
   apply le_n_S; assumption ].
Defined.

Definition eq_dec: forall (m n:nat), {m=n} + {m<>n}.
  refine (
    fix f (m n:nat): {m=n} + {m<>n} :=
    match m, n with
    | O, O => left _ _
    | S mm, S nn => match f mm nn with
                    | left _ => left _ _
                    | right _ => right _ _ end
    | _, _ => right _ _ end);
 [ reflexivity |
   apply O_S |
   apply not_eq_sym, O_S |
   f_equal; assumption |
   apply not_eq_S; assumption ].
Defined.
