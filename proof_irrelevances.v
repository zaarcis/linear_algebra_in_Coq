Require Import Arith. 
Require Import Eqdep_dec. 
Require Import Peano_dec. 

Theorem K_nat: forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p. 
 intros; apply K_dec_set with (p := p). apply eq_nat_dec. assumption. 
Qed. 

Theorem eq_rect_eq_nat: forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h. 
 intros; apply K_nat with (p := h); reflexivity. 
Qed. 

Scheme le_ind' := Induction for le Sort Prop. 

Theorem le_PI {n m} (p q : n <= m): p = q. 
 induction p using le_ind'. 
 replace (le_n n) with (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
 2:reflexivity. 
 generalize (refl_equal n). 
 pattern n at 2 4 6 10, q; case q; [intro | intros m l e]. 
 rewrite <- eq_rect_eq_nat; trivial. 
 contradiction (le_Sn_n m); rewrite <- e; assumption. 
 replace (le_S n m p) with 
 (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))). 
 2:reflexivity. 
 generalize (refl_equal (S m)). 
 pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS]. 
 contradiction (le_Sn_n m); rewrite Heq; assumption. 
 injection HeqS; intro Heq; generalize l HeqS. 
 rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat. 
 rewrite (IHp l0); reflexivity. 
Qed.