From mathcomp Require Import all_ssreflect ssralg all_fingroup zmodp perm.
From HB Require Import structures.
Require Import Logic.Eqdep_dec.
Import EqNotations.

From mathcomp Require Import ssreflect.eqtype.

Set Printing Implicit Defensive.

(*                                                                            *)
(*                                                                            *)
(*           FORMALIZING GAGGLES LOGICS' SINTAXIS AND SEMANTICS               *)
(*                                                                            *)
(*                                                                            *)

Open Scope group_scope.

(* Changing universal quantification utf8 symbols  *)
Notation "'ℕ'" := nat.
Definition Z2 := bool.
Identity Coercion bool_of_sign : Z2 >-> bool.
Lemma addbA : associative addb.
Proof. by case; case; case. Qed.
Lemma addFb : left_id false addb.
Proof. by case. Qed.
Lemma addbC : commutative addb.
Proof. by case; case. Qed.
HB.instance Definition _ := Finite.on Z2.
HB.instance Definition _ := isMulGroup.Build Z2
  addbA addFb addbb.
Definition oneZ2 := (true : Z2).
Definition zeroZ2 := (false : Z2).
Notation "∃" := oneZ2.
Notation "∀" := zeroZ2.
Notation "─" := oneZ2. (* '\---' with Agda's key-bindings *)
Notation "⊹" := zeroZ2. (* ⊹ '\+ ' with Agda's key-bindings*)
Notation "'Æ'" := Z2.
Notation "±" := Z2.

Lemma mulgE (x y : Z2) : x * y = x (+) y.
Proof. by[]. Qed.
Lemma addTb (x : Z2) : ─ * x = ~~x.
Proof. by[]. Qed.
Lemma addbT (x : Z2) : x * ─ = ~~x.
Proof. by case: x. Qed.

Goal (∃ * ∃ = ∀)%g. by[]. Qed.
Goal (∃ * ⊹ = ─)%g. by[]. Qed.
Goal (⊹ * ─ = ─)%g. by[]. Qed.
Goal (⊹ * ⊹ = ∀)%g. by[]. Qed.

Inductive pos := Pos n of (0 < n).
Coercion pos_val (p : pos) := let: Pos n _ := p in n.
HB.instance Definition _ := [isSub for pos_val].
HB.instance Definition _ := [Countable of pos by <:].

Section Comp_Mul.

Set Implicit Arguments.
Variable T : finType.

Definition perm_type2 : predArgType := perm_type T.
Definition perm_of2 of phant T := perm_type2.
Identity Coercion type2_of_perm2 : perm_of2 >-> perm_type2.

Notation "{ 'perm2' T }" := (perm_of2 (Phant T)).

Definition pval2 (p : {perm2 T}) := let: Perm f _ := p in f.
HB.instance Definition _ := [isSub for pval2].
HB.instance Definition _ := [Finite of perm_type2 by <:].

Implicit Types (x y : T) (s t : {perm2 T}) (S : {set T}).

Definition comp_mul s t : {perm2 T} := perm (inj_comp (@perm_inj T s) (@perm_inj T t)).
Definition comp_one : {perm2 T} := perm (@inj_id T).
Definition comp_inv s : {perm2 T} := perm (can_inj (perm_invK s)).

Lemma comp_oneP : left_id comp_one comp_mul.
Proof.
  by move=> s; apply/permP => x; rewrite permE /= permE.
Qed.

Lemma comp_invP : left_inverse  comp_one comp_inv comp_mul.
Proof.
  by move=> s; apply/permP=> x; rewrite !permE /= permE iinv_f;
  last exact: perm_inj.
Qed.

Lemma comp_mulP : associative comp_mul.
Proof.
  by move=> s t u; apply/permP=> x; do !rewrite permE /=.
Qed.

HB.instance Definition _ := isMulGroup.Build (perm_type2)
  comp_mulP comp_oneP comp_invP.

Lemma compM s t x : (s * t : {perm2 T})%g x = s (t x).
Proof. by rewrite permE /=. Qed.

End Comp_Mul.

HB.lock Definition perm2 T f injf : perm_type2 T := Perm (@perm_proof T f injf).
Canonical perm_unlock2 := Unlockable perm2.unlock.

Notation "{ 'perm2' T }" := (perm_of2 _ (Phant T))
  (at level 0, format "{ 'perm2'  T }") : type_scope.
Notation "''Sym_' n" := {perm2 'I_n}
  (at level 8, n at level 2, format "''Sym_' n").

Bind Scope group_scope with perm_type2.
Bind Scope group_scope with perm_of2.

Variable T : finType.
Variable p : {perm2 T}.

Lemma perm_mul_comp [T : finType] (x y : {perm T}) : perm_mul x y = comp_mul y x.
Proof.
  apply permP => a.
  by rewrite !permE /=.
Qed.

Class Atomic_Skeleton := {
    sk_arity : ℕ;
    sk_permutation : 'Sym_sk_arity.+1;
    sk_sign : sk_arity.+1.-tuple ±;
    sk_quantification : Æ;
    sk_type : sk_arity.+1.-tuple pos;
}.
Definition sk_sign_input {C : Atomic_Skeleton} := [tuple tnth (@sk_sign C) (lift ord_max i) | i < (@sk_arity C)].
Definition sk_sign_output {C : Atomic_Skeleton} := tnth (@sk_sign C) ord_max.
Definition sk_type_input {C : Atomic_Skeleton} := [tuple tnth (@sk_type C) (lift ord_max i) | i < (@sk_arity C)].
Definition sk_type_output {C : Atomic_Skeleton} := tnth (@sk_type C) ord_max.

(* Si vols fer-ho val més la pena mirar una manera de definir les permutacions tal com les tuples tenen les llistes (alguna definició inductiva que no fagi ús de la aritat) *)

(* Definition eq_as C D := *)
(*   let: {| sk_arity := n; sk_permutation := σ; sk_sign := s; sk_quantification := q; sk_type := t |} := C in *)
(*   let: {| sk_arity := m; sk_permutation := τ; sk_sign := r; sk_quantification := p; sk_type := u |} := D in *)
(*   (match (n == m) as o return (n == m = o) -> bool with *)
(*   | true => fun Heq => (cast_perm (f_equal succn (eqP Heq)) σ == τ) && (tval s == tval r) && (q == p) && (tval t == tval u) *)
(*   | false => fun=> false *)
(*   end) (erefl _). *)

(* Lemma eq_asP C D : reflect (C = D) (eq_as C D). *)
(* Proof. *)
(*   case: C => [n σ s q t]; case: D => [m τ r p u]. *)
(*   case Heqnm : (n == m); last first. *)
(*     rewrite /eq_as. rewrite {1}Heqnm. *)
(*     have H : (erefl (n == m) = Heqnm). *)
(*     rewrite Heqnm. *)
(*   move: r u τ. rewrite -(eqP Heqnm); intros. *)
(*   case Heq: (eq_as C D); rewrite /eq_as/= in Heq. *)

(* HB.about hasDecEq. *)
(* HB.about Countable. *)
(* HB.instance Definition _ := hasDecEq.on Atomic_Skeleton. *)
(* HB.instance Definition _ := Countable.on Atomic_Skeleton. *)


Definition Boolean_Negation (C : Atomic_Skeleton) (b : Z2) : Atomic_Skeleton :=
  if b then
    match C with
    | {|
        sk_arity := n0;
        sk_permutation := σ;
        sk_sign := s;
        sk_quantification := q;
        sk_type := t;
      |} =>
      ({|
          sk_arity := n0;
          sk_permutation := σ;
          sk_sign := map_tuple [eta negb] s;
          sk_quantification := ─ * q;
          sk_type := t;
        |})%g
    end
  else C.

Theorem sk_β_is_action : is_action [set: ±] Boolean_Negation.
Proof.
  rewrite /Boolean_Negation.
  apply: is_total_action => [//|] /=.
  case => n σ s q t; case; case => //=; f_equal; last by rewrite /mulg /= negbK.
  apply: eq_from_tnth => i. by rewrite !tnth_map /mulg /= negbK.
Qed.

Definition sk_β := Action (sk_β_is_action).

Definition sk_Residuation (C : Atomic_Skeleton) (p : 'Sym_sk_arity.+1) : Atomic_Skeleton
  :=
  let: n := (@ord_max sk_arity) in
  let: i := (p n) in
  let: s := (tnth sk_sign i) in
  {|
    sk_arity := sk_arity;
    sk_permutation := (sk_permutation * p : 'Sym_sk_arity.+1)%g;
    sk_sign :=
      if (i != n) then
        [tuple if (p j) != n
           then ─ * s * tnth sk_sign (((tperm ord_max (p ord_max) : 'Sym_sk_arity.+1) * p)%g j)
           else s | j < sk_arity.+1]
      else [tuple tnth sk_sign (p i) | i < sk_arity.+1];
    sk_quantification :=
      if (i != n) then
        ─ * s * sk_quantification
      else sk_quantification;
    sk_type :=
      [tuple tnth sk_type (p i) | i < sk_arity.+1]
  |}.

Section Of_arity.
Variable n : nat.

Class ary_Skeleton := {
    sa : @Atomic_Skeleton;
    eqs_arity : n == sk_arity
  }.
Coercion sa : ary_Skeleton >-> Atomic_Skeleton.

Definition ska_Residuation
  (C : ary_Skeleton) (s : 'Sym_n.+1) :=
  {| sa := sk_Residuation C (cast_perm (f_equal S (eqP eqs_arity)) s);
    eqs_arity := eqs_arity
  |}.
End Of_arity.

Coercion ary_id (C : Atomic_Skeleton) : (ary_Skeleton sk_arity) :=
  {|
    sa := C;
    eqs_arity := eq_refl sk_arity
  |}.

HB.instance Definition _ {n : nat} := [isSub of (ary_Skeleton n) for @sa n].
(* ary_Skeleton hauria de tenir una instance de Finite. *)

Definition cast_ary_sk {m} {n} (eq_mn : m = n) (C : ary_Skeleton m) :=
  let: erefl in _ = n := eq_mn return ary_Skeleton n in C.

Lemma sa_inj {n} : injective (@sa n).
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.

Theorem sk_α_is_action {n} : is_action [set: 'Sym_n.+1] (@ska_Residuation n).
Proof.
  rewrite /ska_Residuation/sk_Residuation.
  apply: is_total_action => [C|C p1 p2];
    case: C => C Heq;
    apply sa_inj => /=;
    case: C Heq => n0 p s q t Heq.
    f_equal.
    - rewrite -permP => x.
      (* You can improve most of these proves by using compM, and proving also that cast_perm of 1 is always 1 and cast_perm of a product is product of cast_perms, comes from cast_perm_morphM. *)
      by rewrite permE /= cast_permE permE /= cast_ordKV.
    - rewrite /= cast_permE permE /= cast_ordKV eq_refl /=.
      apply eq_from_tnth => i.
      by rewrite tnth_map cast_permE permE /= cast_ordKV tnth_ord_tuple.
    - by rewrite cast_permE permE /= cast_ordKV eq_refl.
    - apply eq_from_tnth => x.
      rewrite tnth_map /=.
      f_equal.
        apply (@perm_inj _ (cast_perm (f_equal S (eqP Heq)) 1)).
        by rewrite cast_permE permE /= cast_ordKV tnth_ord_tuple.
  case H1 : (cast_perm (f_equal succn (eqP Heq)) (p1 * p2) ord_max != ord_max);
    last (move: H1 => /eqP H1);
    (case H2 : (cast_perm (f_equal succn (eqP Heq)) p1 ord_max != ord_max);
      last (move: H2 => /eqP H2);
      (case H3 : (cast_perm (f_equal succn (eqP Heq)) p2 ord_max != ord_max);
        last move : H3 => /eqP H3);
      (f_equal;
        first 1 [
        by rewrite /= -mulgA cast_perm_morphM |
        apply eq_from_tnth => x;
        rewrite !tnth_map !tnth_ord_tuple;
          case H6 : (x != ord_max);
          first (
          case H4 : (cast_perm (f_equal succn (eqP Heq)) (p1 * p2) x != ord_max);
            last (move: H4 => /eqP H4);
            (case H5 : (cast_perm (f_equal succn (eqP Heq)) p2 x != ord_max);
              last (move: H5 => /eqP H5)));
              last (move: H6 => /eqP H6)];
       last 1 [apply eq_from_tnth => x; rewrite !tnth_map !tnth_ord_tuple;
       by rewrite !cast_permE !permE /= cast_ordK];
       try (rewrite !cast_permE permE /= in H1 H2 H3;
              by rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3 H2 eq_refl in H1);
       try (rewrite -[in RHS]H1 in H4;
              by rewrite (perm_inj H4) eq_refl in H6);
       try (rewrite !cast_permE !permE /= in H1 H2 H3;
            rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3 in H1;
              by rewrite H1 eq_refl in H2);
       try (rewrite !cast_permE !permE /= in H1 H2 H3;
            move: H1; rewrite -[in RHS]H2 => /cast_ord_inj/perm_inj H1;
            by rewrite H1 !cast_ordKV eq_refl in H3);
       try (rewrite !cast_permE !permE /= in H1 H2 H3;
            by rewrite !cast_permE !permE /= !cast_ordK)
    )).
  - + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      rewrite !H1 /=.
      move: H1 (H4) => /negbTE H1 /negbTE H4'.
      rewrite !H1 !H4' /=.
      have H7 : (forall p' : 'Sym_n.+1, cast_ord (f_equal succn (eqP Heq))
         (p' (cast_ord (esym (f_equal succn (eqP Heq))) x)) ==
       cast_ord (f_equal succn (eqP Heq))
         (p' (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false).
        intros. apply/negbTE/eqP => /cast_ord_inj/perm_inj/cast_ord_inj/eqP.
        apply/negP. exact: H6.
      rewrite -{2}compM -{1}[p1 (p2 (cast_ord _ x))]compM.
      rewrite !H7.
      have H8 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP. apply/negP.
        exact: H3.
      have H9 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP. apply/negP.
        exact: H5.
      rewrite !H8.
      move: H5 => /negbTE H5.
      rewrite !H5 !cast_ordK /= !H4 !H4' !H9.
      rewrite !addTb !mulgE !addNb !negbK !addbN.
      rewrite addbA -[_(+)(_ _ (_ _ (p1 (p2 _))))(+)_]addbA.
      rewrite [_ _ (_ _ (p1 (p2 _)))(+)_ _ (_ _ (p1 (cast_ord _ _)))]addbC addbA.
      by rewrite addbb addFb.
      (* I shoud be able to prove that in general the case x == ord_max is equivalent to the the proof for sk_quantification.
         Re-use it.
       *)
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      move: (H1) (H4) => /negbTE H1' /negbTE H4'.
      have H7 : (cast_ord (f_equal succn (eqP Heq)) (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
       cast_ord (f_equal succn (eqP Heq)) (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) = false).
        apply/negbTE/negP => /eqP/cast_ord_inj/perm_inj/perm_inj/cast_ord_inj.
        exact/eqP.
      have H9 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP. apply/negP.
        exact: H3.
      rewrite H1' H4' H7 H9 /=.
      rewrite  -{1}[p2 (_ _ x)](cast_ordK (f_equal succn (eqP Heq))) H5.
      by rewrite !addTb !mulgE !addNb -addbC.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      have H7 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) ==
        cast_ord (f_equal succn (eqP Heq)) (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/negP => /eqP/cast_ord_inj/perm_inj.
        exact/eqP.
      have H8 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
        cast_ord (f_equal succn (eqP Heq)) (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/negP => /eqP/cast_ord_inj/perm_inj.
        exact/eqP.
      have H10 : cast_ord (f_equal succn (eqP Heq))
                      (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x)) ==
                    cast_ord (f_equal succn (eqP Heq))
                      (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/negP => /eqP/cast_ord_inj/perm_inj/cast_ord_inj.
        exact/eqP.
      move: (H1) (H5) => /negbTE H1' /negbTE H5'.
      rewrite !H1 !H1' !H5' !H7 !H10 !cast_ordK !H8 !H4 eq_refl /=.
      by rewrite !addTb !mulgE !addNb negbK addbC addbA addbb addFb.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H5 in H4.
      by rewrite H4 eq_refl in H2.
    + rewrite !cast_permE !permE /= in H1 H2 H3.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      move: (H1) (H2) (H3) => /negbTE H1' /negbTE H2' /negbTE H3'.
      have H9 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP. apply/negP.
        exact: H3.
      rewrite !H6 !H1 !H3 !H1' !H3' !H9 !eq_refl /= !H2' /=.
      rewrite !addTb !mulgE !addNb negbK !addbN addbA.
      by rewrite [(_ (+) _) as X in (X (+) _ _ ord_max)]addbC !addbA addbb addFb.
  - rewrite tnth_map. rewrite tnth_ord_tuple. rewrite cast_permE permE /= in H1.
    rewrite compM tpermD; last first.
    - apply/eqP => /perm_inj/esym. apply/eqP. exact: H3.
    - rewrite eq_sym !cast_permE /= cast_ordK. exact: H1.
    rewrite !cast_permE !permE /= cast_ordK H1.
    rewrite !mulgA !mulgE [in RHS]/= ![in _ (+) _ _ (_ _ (p1 (cast_ord _ _)))]addbC.
    by rewrite !addbA addbb addFb [_ (+) ─]addbC.
  - + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      have H9 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP. apply/negP.
        exact: H5.
      have H7 : (cast_ord (f_equal succn (eqP Heq)) (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
       cast_ord (f_equal succn (eqP Heq)) (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) = false).
        apply/negbTE/negP => /eqP/cast_ord_inj/perm_inj/perm_inj/cast_ord_inj.
        exact/eqP.
      move: (H5) (H4) => /negbTE H5' /negbTE H4'.
      rewrite !H4' !H9 !H7 /=.
      by rewrite -[(p2 _) in LHS](cast_ordK (f_equal succn (eqP Heq))) H3.
    + rewrite -[in RHS]H5 in H3.
      apply perm_inj in H3.
      by rewrite H3 eq_refl in H6.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      rewrite !H4 eq_refl /=.
      by rewrite -[(p2 _) in LHS](cast_ordK (f_equal succn (eqP Heq))) H3.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).
      rewrite -[(p2 _)](cast_ordK (f_equal succn (eqP Heq))) H5 in H4.
      by rewrite H4 eq_refl in H2.
    + rewrite !H6 !H3 !H1 !H2.
      rewrite !cast_permE !permE /= in H1 H2 H3.
      repeat (rewrite !cast_permE !permE /=).
      move: (H1) (H2) => /negbTE H1' /negbTE H2'.
      rewrite H1' H2' !eq_refl /=.
      by rewrite -[(p2 _) in LHS](cast_ordK (f_equal succn (eqP Heq))) H3.
  - rewrite cast_permE permE /=.
    rewrite cast_permE /= in H3.
    rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3.
    by rewrite cast_permE.
  - + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /=).
      move: (H4) (H5) => /negbTE H4' /negbTE H5'.
      have H8 : cast_ord (f_equal succn (eqP Heq)) (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x)) ==
                cast_ord (f_equal succn (eqP Heq))
                  (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP.
        exact/negP.
      have H9 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max))) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/perm_inj/eqP.
        exact/negP.
      by rewrite !H4' !H5' !H8 !H9 !cast_ordK.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      by rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H5 H2 eq_refl in H4.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      rewrite -[in RHS]H4 in H2.
      move: H2 => /cast_ord_inj/perm_inj H2.
      by rewrite -H2 cast_ordKV eq_refl in H5.
    + rewrite !cast_permE !permE /= in H1 H2 H3.
      repeat (rewrite !cast_permE !permE /=). rewrite !cast_ordK.
      move: (H1) (H3) => /negbTE H1' /negbTE H3'.
      by rewrite !H6 !H1 !H3 !H1' !H3' !eq_refl !H2.
  - f_equal. f_equal.
    by rewrite tnth_map /= tnth_ord_tuple !cast_permE !permE /= cast_ordK.
  - + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /=). rewrite !cast_ordK.
      move: (H5) (H4) => /negbTE H5' /negbTE H4'.
      have H7 : cast_ord (f_equal succn (eqP Heq))
          (p1 (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x))) ==
        cast_ord (f_equal succn (eqP Heq))
          (p1 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP.
        exact/negP.
      have H8 : cast_ord (f_equal succn (eqP Heq)) (p2 (cast_ord (esym (f_equal succn (eqP Heq))) x)) ==
                cast_ord (f_equal succn (eqP Heq))
                  (p2 (cast_ord (esym (f_equal succn (eqP Heq))) ord_max)) = false.
        apply/negbTE/eqP => /cast_ord_inj/perm_inj/eqP.
        exact/negP.
      rewrite !H1 eq_refl /= !H5' !H8 !cast_ordK !H4' /= !H7.
      by rewrite mulgA !mulgE addbb addFb.
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /=). rewrite !cast_ordK.
      by rewrite !H1 eq_refl /= -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H5.
    + rewrite !cast_permE !permE /= in H1 H2 H3.
      repeat (rewrite !cast_permE !permE /=). rewrite !cast_ordK.
      move: (H2) (H3) => /negbTE H2' /negbTE H3'.
      rewrite !H6 !H1 !H3 !H3' !eq_refl !H2 !H2' /=.
      by rewrite mulgA !mulgE addbb addFb.
  - rewrite cast_permE permE /= in H1.
    rewrite tnth_map tnth_ord_tuple !cast_permE !permE /= cast_ordK.
    by rewrite H1 eq_refl /= mulgA !mulgE addbb addFb.
Qed.

Definition sk_α {n} := Action (sk_α_is_action (n:=n)).

Lemma ska_Residuation_arity_invariant (C : Atomic_Skeleton) (p : 'Sym_sk_arity.+1) : @sk_arity C = @sk_arity ((ska_Residuation {| sa:= C; eqs_arity := eq_refl _|} p)).
Proof.
  rewrite /ska_Residuation /=.
  by case: (unlift ord_max (p ord_max)).
Qed.

Definition inOrbit (C D : Atomic_Skeleton) := (@sk_arity C == @sk_arity D)&&(@sk_sign_output C*@sk_quantification C == @sk_sign_output D*@sk_quantification D).

Section Morphb.
Variable aT rT : finType.
Variable opa : aT -> aT -> aT.
Variable opr : rT -> rT -> rT.
Variable f : aT -> rT.
Implicit Type D : {pred aT}.

Definition dmorphb D :=
  allpairs opr (map f (enum D)) (map f (enum D)) ==
    map f (allpairs opa (enum D) (enum D)).

Lemma dmorphPn D :
  reflect (exists2 x, x \in D & exists2 y, y \in D & f (opa x y) <> opr (f x) (f y))
          (~~ dmorphb D).
Proof.
  apply: (iffP idP) => [morphf | [x Dx [y Dy neqfxy]]]; last first.
    move: Dx; rewrite -(mem_enum D) => /rot_to[i G defG].
    move: Dy; rewrite -(mem_enum D) => /rot_to[j F defF].
    rewrite /dmorphb/allpairs.
    set N := (length G).+1.
    apply/eqP => /(f_equal (fun k => nth (f x) k (i * N + j))).
    rewrite (nth_map x).
    (* The proof consist on rotating i * N + j times the allpairs until you get the pair (i, j), so that we can somehow use defE and defF and neqfxy.

    rewrite (nth_map _).
    move: (H) => /(f_equal (_ (i, j))).
    -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
    rewrite inE /= -(mem_enum D) -(mem_rot i) defE inE in Dxy.
    rewrite andb_orr andbC andbN in Dxy.
    by rewrite eqfxy map_f //; case/andP: Dxy. *)
    admit. admit.
  pose p := [pred x in D | [exists (y | y \in D), f (opa x y) != opr (f x) (f y)]].
  case: (pickP p) => [x /= /andP[ Dx /exists_inP[y Dy /eqP eqfxy]]| no_p].
    by exists x; last exists y.
  rewrite /dmorphb in morphf.
  admit.
(*
map_inj_in_uniq ?enum_uniq // in injf => x y Dx Dy eqfxy.
apply: contraNeq (negbT (no_p x)) => ne_xy /=; rewrite -mem_enum Dx.
by apply/existsP; exists y; rewrite /= !inE eq_sym ne_xy -mem_enum Dy eqfxy /=.
*)
Admitted.

Definition morphb := dmorphb aT.

Lemma dmorphP D : reflect {in D &, morphism_2 f opa opr} (dmorphb D).
Proof.
  rewrite -[dmorphb D]negbK.
  case (@dmorphPn D) => [nomorphf | morphf]; constructor.
    case: nomorphf => x Dx [y Dy /eqP neqxy /=] morphf.
    by case/eqP: neqxy; apply: morphf.
  move=> x y Dx Dy; apply/eqP; apply/idPn=> nxy; case: morphf.
  by exists x => //; exists y => //=; apply/eqP.
Qed.

Lemma morphP : reflect (morphism_2 f opa opr) morphb.
Proof. by apply: (iffP (dmorphP _)) => injf x y => [|_ _]; apply: injf. Qed.

End Morphb.

Arguments morphb [_] [_] [_] [_] _.
Arguments morphP [_] [_] [_] [_] _.

Definition morphbg [C D : FinGroup.type] (f : C -> D) := (morphb f (opa := mulg) (opr := mulg)).

Section MorDefSection.

Variable S T : FinGroup.type.
Implicit Type f : S -> T.

Inductive Mor := Morph (mval : {ffun S -> T}) & (morphbg mval).
Coercion mval (p : Mor)  := let: Morph g _ := p in g.
Definition morph_of of phant T := Mor.
Identity Coercion type_of_morph : morph_of >-> Mor.

HB.instance Definition _ := [isSub of Mor for mval].
HB.instance Definition _ := [Finite of Mor by <:].

Lemma morph_proof f : {morph f : x y / x * y} -> morphbg (finfun f).
Proof.
  by move=> g_morph; apply/morphP => x y; rewrite !ffunE g_morph.
Qed.

End MorDefSection.

HB.lock Definition morph S T f morphf :=
  Morph _ _ (@morph_proof S T f morphf).
Canonical morph_unlock := Unlockable morph.unlock.

HB.lock Definition fun_of_morph S T (u : Mor S T) : S -> T := val u.
Canonical fun_of_morph_unlock := Unlockable fun_of_morph.unlock.
Coercion fun_of_morph : Mor >-> Funclass.

Section AutDefSection.

Variable C : FinGroup.type.
Variable f : {perm C}.

Inductive Aut := Autom (f : {perm2 C}) of (morphbg f).
Coercion aval (p : Aut) := let: Autom f _ := p in f.
Definition aut_of of phant T := Aut.
Identity Coercion type_of_aut : aut_of >-> Aut.

HB.instance Definition _ := [isSub of Aut for aval].
HB.instance Definition _ := [Finite of Aut by <:].

Lemma aut_proof (g : {perm C}) : {morph g : x y / x * y} -> morphbg g.
Proof.
  by move=> g_morph; apply/morphP => x y; rewrite g_morph.
Qed.

End AutDefSection.

HB.lock Definition aut C f injf morphf :=
  @Autom C (@perm C f injf) (@aut_proof C (@perm C f injf) morphf).
Canonical aut_unlock := Unlockable aut.unlock.

HB.lock Definition fun_of_aut C (u : Aut C) : C -> C := val u.
Canonical fun_of_aut_unlock := Unlockable fun_of_aut.unlock.
Coercion fun_of_aut : Aut >-> Funclass.

Section general_Groups.

Open Scope group_scope.
Variable C D : FinGroup.type.

Definition dprod_mul (s t : C * D) :=
  let: (x, y) := s in let: (u, v) := t in
  (x * u, y * v).
Definition dprod_one := (1 : C, 1 : D).
Definition dprod_inv (s : C * D) :=
  let: (x, y) := s in
  (x^-1, y^-1).

Lemma dprod_oneP : left_id dprod_one dprod_mul.
Proof.
  by case => /= a b; rewrite !mul1g.
Qed.

Lemma dprod_invP : left_inverse  dprod_one dprod_inv dprod_mul.
Proof.
  by case => /= a b; rewrite !mulVg.
Qed.

Lemma dprod_mulP : associative dprod_mul.
Proof.
  by case => a b; case => c d; case => e f /=; rewrite !mulgA.
Qed.

HB.instance Definition _ := isMulGroup.Build (C * D)%type
  dprod_mulP dprod_oneP dprod_invP.

Lemma aut_mul_proof (f g : Aut C) : {morph (comp_mul f g) : x y / x * y}.
Proof.
  case: f => f Hf; case: g => g Hg x y.
  by rewrite !permE /= (morphP _ Hg) (morphP _ Hf).
Qed.

Definition aut_mul (f g : Aut C) := aut (aut_mul_proof f g).

Lemma aut_one_proof : {morph (perm_one C) : x y / x * y}.
Proof. move => x y. by rewrite !permE. Qed.

Definition aut_one : Aut C := aut aut_one_proof.

Lemma aut_inv_proof (f : Aut C) : {morph (comp_inv f) : x y / x * y}.
Proof.
  case: f => f Hf x y /=.
  by apply: (@perm_inj _ f); rewrite !permE /= (morphP _ Hf) !perm_invK.
Qed.

Definition aut_inv (f : Aut C) := aut (aut_inv_proof f).

Lemma perm_of_aut_inj : injective (@aval C).
Proof.
  case => f Hf; case => g Hg. exact: val_inj.
Qed.

Lemma autP (f g : Aut C) : (f =1 g) <-> f = g.
Proof. by split=> [| -> //]; rewrite unlock => eq_sv; apply/val_inj/permP. Qed.

Lemma avalE (f : Aut C) : aval f = f :> (C -> C).
Proof. by rewrite [@fun_of_aut]unlock. Qed.

Lemma autE f f_inj f_morph : @aut C f f_inj f_morph =1 f.
Proof.
  move=> x. rewrite -avalE [@aut]unlock /=.
  by rewrite -(permE f_inj) [@perm]unlock. Qed.

Lemma fun_of_morph_inj : injective (@mval C D).
Proof.
  case => f Hf; case => g Hg. exact: val_inj.
Qed.

Lemma morP (f g : Mor C D) : (f =1 g) <-> f = g.
Proof. by split=> [| -> //]; move/ffunP => /= eq_sv; apply/val_inj. Qed.

Lemma morphE f f_morph : @morph C D f f_morph =1 f.
Proof.
  move=> x. rewrite [@morph]unlock /=.
  by rewrite -[in RHS]ffunE.
Qed.

Lemma morph_morph (f : Mor C D) : {morph f : x y / x * y}.
Proof. exact: (morphP _ (valP f)). Qed.
Hint Resolve morph_morph : core.

Lemma aut_oneP : left_id aut_one aut_mul.
Proof.
  move => s; apply/autP => x.
  by rewrite autE /= avalE /= autE -avalE.
Qed.

Lemma aut_invP : left_inverse  aut_one aut_inv aut_mul.
Proof.
  move=> s; apply/autP=> x. rewrite !autE /= avalE /= autE iinv_f //.
  exact: perm_inj.
Qed.

Lemma aut_mulP : associative aut_mul.
Proof.
  by move => s r t; apply/autP => x; rewrite !autE /= !avalE autE !avalE autE /= -!avalE.
Qed.

HB.instance Definition _ := isMulGroup.Build (Aut C)
  aut_mulP aut_oneP aut_invP.

Lemma autM (f g : Aut C) : forall x, (f * g) x = f (g x).
Proof.
  intros. by rewrite autE /= !avalE.
Qed.

Lemma aut_morph (f : Aut C) : {morph f : x y / x * y}.
Proof. rewrite -avalE. exact: (morphP _ (valP f)). Qed.
Hint Resolve aut_morph : core.

End general_Groups.

Section semiprod_Group.

Open Scope group_scope.
Variable C D : FinGroup.type.

Lemma autg1 [aT : FinGroup.type] (f : Aut aT) : f 1 = 1.
Proof.
  have a : aT. exact: 1.
  move: (erefl (f a)). rewrite -{1}(mulg1 a) (aut_morph f) -{2}(mulg1 (f a)).
  by move => /(f_equal (fun n => (f a)^-1 * n)); rewrite !mulgA mulVg !mul1g.
Qed.

Lemma aut_invg [aT : FinGroup.type] (f : Aut aT) x : f x^-1 = (f x)^-1.
Proof.
  move: (autg1 f).
  rewrite -{1}(mulgV x) -(mulgV (f x)) (aut_morph f) => /(f_equal (fun n => (f x)^-1 * n)).
  by rewrite !mulgA mulVg !mul1g.
Qed.

Lemma mor1 [aT rT : FinGroup.type] (f : Mor aT rT) : f 1 = 1.
Proof.
  have a : aT. exact: 1.
  move: (erefl (f a)). rewrite -{1}(mulg1 a) (morph_morph f) -{2}(mulg1 (f a)).
  by move => /(f_equal (fun n => (f a)^-1 * n)); rewrite !mulgA mulVg !mul1g.
Qed.

Lemma mor_inv [aT rT : FinGroup.type] (f : Mor aT rT) x : f x^-1 = (f x)^-1.
Proof.
  move: (mor1 f).
  rewrite -{1}(mulgV x) -(mulgV (f x)) (morph_morph f) => /(f_equal (fun n => (f x)^-1 * n)).
  by rewrite !mulgA mulVg !mul1g.
Qed.

Variable φ : Mor D (Aut C).

Definition SemiDProd : Type := (C * D)%type.
HB.instance Definition _ := isFinite.Build SemiDProd (@prod_enumP C D).

Definition semiprod_mul (s t : SemiDProd) :=
  let: (x, y) := s in let: (u, v) := t in
  (x * (φ y u), y * v).
Definition semiprod_one : SemiDProd := (1 : C, 1 : D).
Definition semiprod_inv (s : SemiDProd) :=
  let: (x, y) := s in
  ((φ y^-1 x^-1), y^-1).

Lemma semiprod_oneP : left_id semiprod_one semiprod_mul.
Proof.
  by case => /= a b; rewrite !mul1g mor1 autE.
Qed.

Lemma semiprod_invP : left_inverse  semiprod_one semiprod_inv semiprod_mul.
Proof.
  case => /= a b.
  by rewrite -(aut_morph (φ b^-1)) !mulVg autg1.
Qed.

Lemma semiprod_mulP : associative semiprod_mul.
Proof.
  case => a b; case => c d; case => e f /=.
  by rewrite !mulgA !(morph_morph φ) autE /= (aut_morph (φ b)) mulgA !avalE.
Qed.

HB.about isMulGroup.
HB.instance Definition _ := isMulGroup.Build SemiDProd semiprod_mulP semiprod_oneP semiprod_invP.

End semiprod_Group.

Section tuple_Group.

Open Scope group_scope.
Variable n : nat.
Variable C : FinGroup.type.
Implicit Type s t : n.-tuple C.

Definition tuple_mul s t : n.-tuple C :=
  map_tuple (fun i => tnth s i * tnth t i) (ord_tuple n).
Definition tuple_one :=
  map_tuple (fun => (1 : C)) (ord_tuple n).
Definition tuple_inv s :=
  map_tuple (fun i => (tnth s i)^-1) (ord_tuple n).

Lemma tuple_oneP : left_id tuple_one tuple_mul.
Proof.
  move => a; apply eq_from_tnth => i.
  by rewrite !tnth_map tnth_ord_tuple mul1g.
Qed.

Lemma tuple_invP : left_inverse  tuple_one tuple_inv tuple_mul.
Proof.
  move => a; apply eq_from_tnth => i.
  by rewrite !tnth_map tnth_ord_tuple mulVg.
Qed.

Lemma tuple_mulP : associative tuple_mul.
Proof.
  move => a b c; apply eq_from_tnth => i.
  by rewrite !tnth_map !tnth_ord_tuple !mulgA.
Qed.

HB.instance Definition _ := isMulGroup.Build (n.-tuple C)%type
  tuple_mulP tuple_oneP tuple_invP.

End tuple_Group.

Definition γ (C : Atomic_Skeleton) (p : ((@sk_arity C).+1.-tuple ±) 'Sym_(@sk_arity C).+1).
  :=
  let (b, a) := p in sk_β (sk_α C a) b.

Lemma residuate_sk_sign_output (C : Atomic_Skeleton) p :
  @sk_sign_output (sk_Residuation C p) =
    if (p ord_max != ord_max)
    then ─ * tnth (@sk_sign C) (p ord_max) * @sk_sign_output C
    else @sk_sign_output C.
Proof.
  move: p.
  case: C => /=; intros.
  rewrite /sk_sign_output/sk_Residuation /=.
  case Hp : (p0 ord_max != ord_max);
    rewrite tnth_map tnth_ord_tuple.
    by rewrite Hp permE /= tpermR.
  by move: Hp => /eqP ->.
Qed.

Lemma negation_sk_sign_output (C : Atomic_Skeleton) b :
  @sk_sign_output (Boolean_Negation C b) =
    if b then ~~(@sk_sign_output C)
    else @sk_sign_output C.
Proof.
  case: b => //=; rewrite /sk_sign_output.
  case: C => /=; intros.
  by rewrite tnth_map.
Qed.

Lemma γ_sign_invariant (C : Atomic_Skeleton) p : @sk_sign_output (γ C p) * @sk_quantification (γ C p) = @sk_sign_output C * @sk_quantification C.
Proof.
  rewrite /γ/=.
  case: p; case => p; rewrite cast_perm_id;
    rewrite negation_sk_sign_output;
    rewrite !residuate_sk_sign_output;
    case Heq : (p ord_max != ord_max) => /=;
      rewrite Heq !mulgE //= !addNb !addbN !negbK //;
    by rewrite addbA [in X in X (+) _]addbC addbA addbb addFb.
Qed.

(* In here we show that inOrbit truly reflect that C and D are on the same orbit, by showing that it is equivalent to having a list of residuations and negations from one connective to the other. *)
Lemma inOrbitP (C D : Atomic_Skeleton) :
  reflect
     (exists l : seq (± * 'Sym_sk_arity.+1), foldr (fun x => fun => γ C x) C l = D)
     (inOrbit C D).
Proof.
  rewrite /inOrbit.
  (* To begin with we want to prove that it is not possible for residuated connectives to have different arity.  *)
  case Heq_arity: (@sk_arity C == @sk_arity D) => /=; last first.
    apply: ReflectF => [[l /(f_equal (fun C'=>@sk_arity C')) Hl]].
    have nH1 : forall (C' : Atomic_Skeleton) p, @sk_arity (γ C' p) = @sk_arity C'.
      by case; intros; case: p0; case.
    have nH : forall (C' : ary_Skeleton (@sk_arity C)) (l' : seq (± * 'Sym_sk_arity.+1)), @sk_arity (foldr (fun x => fun => γ C' x) C' l') = @sk_arity C'.
      move => C'; case => [//|/= p l'].
      by rewrite nH1.
    rewrite (nH C l) in Hl. move: Heq_arity => /eqP. by rewrite Hl.
  (* Now we show that it is not possible for residuated connectives to have different difference between the sign and the quantification sign. *)
  case Heq_sign:
    (@sk_sign_output C * @sk_quantification C == @sk_sign_output D * @sk_quantification D); last first.
    apply: ReflectF => [[l /(f_equal (fun C' => @sk_sign_output C' * @sk_quantification C')) Hl]].
    have nH : forall (C' : Atomic_Skeleton) (l' : seq (± * 'Sym_sk_arity.+1)), @sk_sign_output (foldr (fun x => fun => γ C' x) C' l') * @sk_quantification (foldr (fun x => fun => γ C' x) C' l') = @sk_sign_output C' * @sk_quantification C'.
      move => C'; case => [//|/= p l'].
      by rewrite γ_sign_invariant.
    rewrite (nH C l) in Hl. move: Heq_sign => /eqP. by rewrite Hl.
  (* Finally it is necesary to see that having equal difference and arity is enough to find a sequence between them. *)
  apply: ReflectT.
  (* Using that C and D have the same arity we can get rid of D and write it with the same arity as C, so that we can operate on their permutations. *)
  case: D Heq_arity Heq_sign => /=; intros.
  move: sk_sign0 sk_permutation0 sk_type0 Heq_sign.
  rewrite -(eqP Heq_arity); intros.
  (* First you residuate C until you have the same permutation as D, then you flip the signs, by acting with (j n+1)-(j n+1), on each component until you have the same sign list, the quantification comes free as the difference is equal in both connectives. *)
  Admitted.


(* Cal construir l'estructura de hasDecEq i Finite sobre Atomic_Skeleton i ary_Skeleton respectivament. *)

(* If necessary in the future for has_connective_Family:

 of hasDecEq T

inOrbit (assignment x) (assignment y);

CONTINUAR.

Em caldrà formalitzar probablement producte directe i semidirecte de dos grups, aleshores hauré de fer servir la següent definició sobre l'acció del producte semidirecte que introduiré després.
En conseqüència caldra fer una nova inOrbit per a les noves accions, sense fer ús de l'acció lliure.
 *)

(* Maybe it would be more easy to work with pointed orbits. *)
HB.mixin Record is_connective_Family T := {
    orbit_par : eqType;
    orbit_group : orbit_par -> FinGroup.type;
    orbit_action : forall (i : orbit_par), {action orbit_group i &-> Atomic_Skeleton};
    skeleton_assignment : T -> Atomic_Skeleton;
    orbit_assignment : T -> orbit_par;
    assignment_wf : forall x y,
      orbit_assignment x = orbit_assignment y ->
      exists g, skeleton_assignment y = orbit_action (orbit_assignment x) (skeleton_assignment x) g;
    assignment_pinj : forall x y,
      orbit_assignment x = orbit_assignment y -> skeleton_assignment x = skeleton_assignment y -> x = y
  }.

HB.structure Definition Connective_Family
  := {T of is_connective_Family T}.

(* Class Connectives := { *)
(*   connective_set : Type; *)
(*   assignment : (connective_set -> Atomic_Skeleton) *)
(* }. *)

(* This definition is not really necessary. *)
Class Connective {C : Connective_Family.type} := {
    var : C;
    skeleton := skeleton_assignment var
}.

(* Canvia i revisa els noms sign_output/input. *)
Definition arity {C : Connective_Family.type} (c : C) := @sk_arity (skeleton_assignment c).
Definition permutation {C : Connective_Family.type} (c : C) := @sk_permutation (skeleton_assignment c).
Definition sign {C : Connective_Family.type} (c : C) := @sk_sign (skeleton_assignment c).
Definition sign_output {C : Connective_Family.type} (c : C) := @sk_sign_output (skeleton_assignment c).
Definition sign_input {C : Connective_Family.type} (c : C) := @sk_sign_input (skeleton_assignment c).
Definition quantification {C : Connective_Family.type} (c : C) := @sk_quantification (skeleton_assignment c).
Definition type {C : Connective_Family.type} (c : C) := @sk_type (skeleton_assignment c).
Definition type_output {C : Connective_Family.type} (c : C) := @sk_type_output (skeleton_assignment c).
Definition type_input {C : Connective_Family.type} (c : C) := @sk_type_input (skeleton_assignment c).

Module Of_arity.
Section section.
Variable n : nat.
Variable C : Connective_Family.type.

Inductive Connective := Var c of n == @arity C c.
Coercion to_connective cn := let: Var c _ := cn in c.

HB.instance Definition _ := [isSub of Connective for to_connective].
Lemma val_inj : injective to_connective.
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.
End section.
End Of_arity.

HB.instance Definition _ {C : Connective_Family.type} {n} := [isSub of (Of_arity.Connective n C) for @Of_arity.to_connective n C].

Module Of_type.
Section section.
Variable n : pos.
Variable C : Connective_Family.type.

Inductive Connective := Var c of n == @type_output C c.
Coercion to_connective cn := let: Var c _ := cn in c.

HB.instance Definition _ := [isSub of Connective for to_connective].
Lemma val_inj : injective to_connective.
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.
End section.
End Of_type.

HB.instance Definition _ {C : Connective_Family.type} {n} := [isSub of (Of_type.Connective n C) for @Of_type.to_connective n C].

Module Letter.

Class Atomic_Skeleton := {
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type_output : pos;
}.
Coercion to_atomic_skeleton (P : Atomic_Skeleton) :=
  match P with
    {| sk_sign := s; sk_quantification := q; sk_type_output := t |} =>
      gaggle.Build_Atomic_Skeleton (1)%g  (@Tuple _ _ [::s] (eq_refl _)) q (@Tuple _ _ [::t] (eq_refl _))
  end.
Definition Connective := Of_arity.Connective 0.
End Letter.

Variable AS : Letter.Atomic_Skeleton.
Coercion Letter.to_atomic_skeleton : Letter.Atomic_Skeleton >-> Atomic_Skeleton.

Module Strict.
Section section.
Variable C : Connective_Family.type.

Inductive Connective := Var c of @arity C c > 0.
Coercion to_connective cn := let: Var c _ := cn in c.

HB.instance Definition _ := [isSub of Connective for to_connective].
Lemma val_inj : injective to_connective.
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.
End section.
End Strict.

HB.instance Definition _ {C : Connective_Family.type} := [isSub of (Strict.Connective C) for @Strict.to_connective C].

Inductive typed_Formula {C : Connective_Family.type} : pos -> Type :=
  | composition :
      forall (c : C),
      (forall i : 'I_(arity c), typed_Formula (tnth (type c) (lift ord_max i))) ->
      typed_Formula (tnth (type c) ord_max)
.
Definition Formula {C : Connective_Family.type} := {k & @typed_Formula C k}.

(* PERMUTATIONS and α-ACTION *)

(* versió inductiva -la del Guillaume- tb? *)

(* STRUCTURES *)

(*
    We begin by defining a structural family for each orbit of the action on skeletons with elements in the connective family.
    Something key in this first half is being able to characterize each orbit with a function like inOrbit.
    Each set of possible value in the equalities in inOrbit uniquely determine the orbit.
    This lets us identify the orbit without needing to resort to a representative of the family.
    We then instantiate a different copy of this family with the original connective as a component whenever available.
 *)

(* Maybe defining a structure as a connective_Family with the actions closed on it and a disponibility value on each connective.
     Then for each connective_Family create a structure by closing the orbits and adding the available connectives themselves in the disponibility values.
     This is done on the dependent product of orbit_groups by orbit_par.
     How to do the assignment of connectives?
     In an imperative style I would fill all structures with None and then change the ones corresponding to orbit_assignments and skeleton_assignments (this would require checking on each one) of connectives c into Some c.
 *)

(* When instantiating the idea would be to provide a proof of all this propositions for each kind of actions, so that it doesn't depend on the connective_family but in the way actions are defined. *)
HB.mixin Record is_structure_Family (C : Connective_Family.type) S := {
    structure_of_connective : C -> S;
    connective_of_structure : S -> option C;
    reflection_of_connective : forall x, connective_of_structure (structure_of_connective x) = Some x;
    some_connective : forall x y, connective_of_structure x = Some y -> structure_of_connective y = x;

    structure_skeleton_assignment : S -> Atomic_Skeleton;
    structure_orbit_assignment : S -> @orbit_par C;
    compatible_skeleton_assignment : forall x,
      structure_skeleton_assignment (structure_of_connective x) = skeleton_assignment x;
    compatible_orbit_assignment : forall x,
      structure_orbit_assignment (structure_of_connective x) = orbit_assignment x;

    structure_action : forall i : orbit_par, {action orbit_group i &-> S};
    action_compatible : forall (x : S) (g : orbit_group (structure_orbit_assignment x)),
      structure_skeleton_assignment (structure_action (structure_orbit_assignment x) x g) =
        orbit_action (structure_orbit_assignment x) (structure_skeleton_assignment x) g;
  }.

HB.structure Definition Structure_Family (C : Connective_Family.type)
  := {T of is_structure_Family C T}.

(* An orbit of a connective is parametrized by the sign tuple and the permutation while determining quantification from them. *)
(* Similarly it can be represented as those atomic skeletons of fixed arity and signs product  *)
(* It makes no sense doing this with the general groups because it might not be a structure_family.

    To proceed we will assume a bijection F between the {s : S & structure_orbit_assignment s = i} and (orbit_group i) such that (structure_action i x y) = (@mulg (orbit_group i) x (F y)).
    Which are the conditions on the action on skeletons and the group so that the orbit has a bijection with the group sending the action to the group operation?
 *)
Definition structure_Orbit {C : Connective_Family.type} := { i : @orbit_par C & orbit_group i }.
Definition connective_to_Orbit {C : Connective_Family.type} := .

(* In our case orbit_par shoud be a countable type where each orbit of strict connectives has a particular arity and sign * quantification and each orbit of letter connectives is just itself. *)

Class Structure {C : Connective_Family.type} {S : Structure_Family.type} :=
  {
    structure_var : A;
    structure_skeleton := assignment structure_var
  }.
Definition C_of_Ss {A} (S : @Structures A) := A.
Definition S_of_Cs (C : @Connective_Family.type) := @Build_Structures C.
Definition C_of_S {C : Connective_Family.type} {B} (S : @Structure _ B) : @Connective (C_of_Ss B) :=
  {|
    var := structure_var
  |}.
Definition S_of_C {A} (C : @Connective A) : @Structure A (S_of_Cs A) :=
  {|
    structure_var := var
  |}.

(* Boolean negation to be done and added over formulas.
   As an alternative one could leave the sign over formulas as ill-defined (it takes whatever value is required by context).
 *)
Inductive typed_Structural_Formula {C : Connective_Family.type} {S : Structures} : pos -> Type :=
  | from_formula {k} : @typed_Formula A k -> typed_Structural_Formula k
  | structural_composition
    : forall C : Structure,
      (forall i : 'I_(@sk_arity (@structure_skeleton _ _ C)),
          typed_Structural_Formula
            (tnth (@sk_type (@structure_skeleton _ _ C)) (lift ord_max i))) ->
      typed_Structural_Formula (tnth (@sk_type (@structure_skeleton _ _ C)) ord_max).
Definition Structural_Formula {C : Connective_Family.type} {S : Structures} := sigT typed_Structural_Formula.

Definition orbit_of_skeleton (C : Atomic_Skeleton) : Connective_Family.type :=
  {|
    connective_set := 'Sym_sk_arity.+1;
    assignment := fun p => (sk_α {| sa:= C; eqs_arity := eq_refl _|} p)
  |}.

Lemma orbit_arity (C : Atomic_Skeleton)
  (D : @Connective (orbit_of_skeleton C)) :
  @sk_arity C = @sk_arity (@skeleton _ D).
Proof. by[]. Qed.

Lemma orbit_set (C : Atomic_Skeleton) :
  @connective_set (orbit_of_skeleton C) = 'Sym_sk_arity.+1.
Proof. by[]. Qed.

Class sig_Class {A : Type} {B : A -> Type} :=
  {
    sig_fst : A;
    sig_snd : B sig_fst
  }.

(* Each connective from Generators creates a full independent orbit of connectives. *)
Definition full_Connective_Family.type (Generators : Connective_Family.type) :=
  {|
    connective_set := @sig_Class (@Connective Generators) (fun C => 'Sym_sk_arity.+1);
    assignment :=
      fun Cp =>
                (sk_α {| sa:= skeleton; eqs_arity := eq_refl _|} (@sig_snd _ _ Cp))
  |}.

(* change connective_set to a subtype of the other connective_set.
    I need to somehow store the original connective in its individual orbit.
 *)

Class Singleton (T : Type) (a : T) : Type :=
  {
    element := a
  }.

Lemma Singleton_contractible {T : Type} (a : T) (h1 h2 : Singleton a) : h1 = h2.
Proof.
  by case: h2; case: h1.
Qed.

Lemma Singleton_eq {T : Type} (a : T) (h : Singleton a) : (@element _ _ h) = a.
Proof.
  by case: h.
Qed.

Definition arity_full {Generators : Connective_Family.type} (C : @Connective (full_Connective_Family.type Generators)) :
  arity (@sig_fst _ _ (@var _ C)) = arity C.
Proof.
  by[].
Qed.

(* Fes atenció pq la segona component de connective_set depen directament de la variable C, no de la primera component. *)

Definition restricted_orbit {Generators : Connective_Family.type}
  (C : @Connective (full_Connective_Family.type Generators)) : Connective_Family.type :=
  {|
    connective_set :=
      @sig_Class
        (@Singleton (@Connective Generators) (@sig_fst _ _ (@var _ C)))
        (fun eC => 'Sym_(arity (@element _  _ eC)).+1);
    assignment :=
      fun Cp =>
        let: C' := @sig_fst _ _ Cp in
        let: p := @sig_snd _ _ Cp in
        (sk_α
           {| sa:= (@skeleton _ (@sig_fst _ _ (@var _ C)));
                eqs_arity := eq_refl _ |} p)
  |}.

Definition restricted_of_full_C {Generators : Connective_Family.type}
  (C : @Connective (full_Connective_Family.type Generators)) : @Connective (restricted_orbit C) :=
  {|
    var :=
      {|
        sig_fst := (@Build_Singleton _ (@sig_fst _ _ (@var _ C)));
        sig_snd := (@sig_snd _ _ (@var _ C))
      |} : (@connective_set (restricted_orbit C))
  |}.

Definition full_of_restricted_C {Generators : Connective_Family.type}
  (C : @Connective (full_Connective_Family.type Generators)) (D : @Connective (restricted_orbit C)) :
  @Connective (full_Connective_Family.type Generators) :=
  {|
    var :=
      {|
        sig_fst := (@element _ _ (@sig_fst _ _ (@var _ D)));
        sig_snd := (@sig_snd _ _ (@var _ D))
      |} : (@connective_set (full_Connective_Family.type Generators))
  |}.

(*
El problema ve de que són diferents aritats de diferents connectius (per molt que siguin iguals).
 *)

Definition Residuation' {Generators : Connective_Family.type}
  (C : @Structure _ (S_of_Cs (full_Connective_Family.type Generators)))
  (p : 'Sym_(@sk_arity (@structure_skeleton _ _ C)).+1) :
  @Structure _ (S_of_Cs (full_Connective_Family.type Generators)) :=
  {|
    structure_var :=
      {|
        sig_fst := @sig_fst _ _ (@structure_var _ _ C);
        sig_snd := (p * (@sig_snd _ _ (@structure_var _ _ C)))%g
      |} : (@connective_set (full_Connective_Family.type Generators))
  |}.

Definition Residuation {Generators : Connective_Family.type} (C : @Connective (full_Connective_Family.type Generators))
  (D : @Structure _ (S_of_Cs (restricted_orbit C)))
  (p : 'Sym_(@sk_arity (@skeleton _ C)).+1) :
  @Structure _ (S_of_Cs (restricted_orbit C)) :=
  {|
    structure_var :=
      {|
        sig_fst := @Build_Singleton _ (@sig_fst _ _ (@var  _ C));
        sig_snd := ((@sig_snd _ _ (@structure_var _ _ D)) * p)%g
      |} : (@connective_set (restricted_orbit C))
  |}.

Theorem α_is_action {Generators : Connective_Family.type} {C : @Connective (full_Connective_Family.type Generators)} :
  is_action [set: 'Sym_(arity C).+1] (@Residuation _ C).
Proof.
  rewrite /Residuation.
  rewrite /is_action; split.
Admitted.

Definition α {Generators : Connective_Family.type} {C : @Connective (full_Connective_Family.type Generators)} :=
  Action (α_is_action (C:=C)).

Lemma arity_restricted {Generators : Connective_Family.type} {C : @Connective (full_Connective_Family.type Generators)}
  (D : @Structure _ (S_of_Cs (restricted_orbit C))) : @sk_arity (@structure_skeleton _ _ D) = arity C.
Proof.
  by case: D; case: C => /= [[C s]] [D p].
Qed.

Lemma arity_S_of_C {C : Connective_Family.type} {C : Connective} : @sk_arity (@structure_skeleton _ _ (S_of_C C)) = arity C.
Proof.
  by[].
Qed.

Lemma arity_C_of_S {C : Connective_Family.type} {B : Structures} {C : Structure} : arity (C_of_S C) =  @sk_arity (@structure_skeleton _ _ C).
Proof.
  by[].
Qed.

Lemma arity_full_of_restricted_C {Generators : Connective_Family.type} {C : @Connective (full_Connective_Family.type Generators)} D : arity (@full_of_restricted_C _ C D) = arity C.
Proof.
  by case: D; case: C => /= [[C s]] [D p].
Qed.

(* ATOMIC CALCULUS *)

(* Agafar tota l'òrbita per la negació i la residuació. *)

Definition unsigned_function
  (s : ±) {C : Connective_Family.type} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type)
  (X Y : Structural_Formula)
  :=
  f
    (if s then X else Y)
    (if s then Y else X).

Definition unsigned_pivoted_function_S
  {C : Connective_Family.type} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type) (C : @Structure _ S)
  (X : forall i:'I_(@sk_arity (@structure_skeleton _ _ C)),
      typed_Structural_Formula (tnth sk_type (lift ord_max i)))
  (U : Structural_Formula)
  :=
  unsigned_function (@sk_sign_output (@structure_skeleton _ _ C)) f
    U (existT _
         (@sk_type_output (@structure_skeleton _ _ C)) (structural_composition C X)).

Definition unsigned_pivoted_function_C
  {C : Connective_Family.type} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type) (C : @Connective A)
  (φ : forall i:'I_(arity C),
      typed_Formula (tnth (type C) (lift ord_max i)))
  (U : Structural_Formula)
  :=
  unsigned_function (tnth (sign C) ord_max) f
    U (existT _
         (tnth (type C) ord_max) (from_formula (composition C φ))).

(* Lacks dr2 and connective sets non equal to a full orbit. *)

Definition cast_Formula {C : Connective_Family.type} {S : Structures} [n m : pos] (eq_mn : m = n) (φ : typed_Structural_Formula m) :=
  let: erefl in _ = n := eq_mn return typed_Structural_Formula n in φ.

Lemma calculus_type_wf (Generators : Connective_Family.type)
            (C : @Connective (full_Connective_Family.type Generators)) (p : 'Sym_(arity C).+1)
            (i:'I_(@sk_arity
                     (@structure_skeleton _ _
                        (S_of_C (@full_of_restricted_C _ C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p))))))) :
    (tnth (@sk_type (@skeleton _ C))
                       (p (lift ord_max i))) =
      (tnth
         (@sk_type (@structure_skeleton _ _
           (S_of_C (@full_of_restricted_C _ C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p)))))) (lift ord_max i)).
rewrite /arity. move : Generators C p i => [gset gass] [[/= C s]] /= p i.
rewrite !tnth_map.
f_equal.
rewrite  !cast_perm_morphM.
rewrite !tnth_ord_tuple !permE /=.
f_equal. by rewrite cast_permE !cast_ord_id.
Qed.


(* I need to prove an equality for the type of the residuation. *)
Inductive Calculus {Generators : Connective_Family.type}
  : @Structural_Formula _ (S_of_Cs (@full_Connective_Family.type Generators)) ->
    @Structural_Formula _ (S_of_Cs (@full_Connective_Family.type Generators)) -> Type
  :=
  | LRule (C : @Connective (@full_Connective_Family.type Generators))
    : forall (X : forall i:'I_(arity C),
          typed_Structural_Formula (tnth (type C) (lift ord_max i))),
      forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type C) (lift ord_max i))),
      (forall i:'I_(arity C),
          unsigned_function
            (tnth (sign C) (lift ord_max i) * (quantification C))
            Calculus
            (existT _ (tnth (type C) (lift ord_max i)) (X i))
            (existT _ (tnth (type C) (lift ord_max i)) (from_formula (φ i)))) ->
      unsigned_pivoted_function_S Calculus (S_of_C C)
        X
        (existT _ (tnth (type C) ord_max) (from_formula (composition C φ)))
  | RRule (C : @Connective (@full_Connective_Family.type Generators))
    : forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type C) (lift ord_max i))),
      forall U : Structural_Formula,
      unsigned_pivoted_function_S Calculus (S_of_C C)
        (fun i => from_formula (φ i)) U ->
      unsigned_pivoted_function_C Calculus C φ U
  | dr1 (C : @Connective (full_Connective_Family.type Generators))
      (p : 'Sym_(arity C).+1)
    : forall (X : forall i:'I_(arity C).+1,
          typed_Structural_Formula (tnth (@sk_type (@skeleton _ C)) i)),
      unsigned_pivoted_function_S Calculus
        (S_of_C C)
        (fun i => X (lift ord_max i))
        (existT _ _ (X ord_max)) ->
      unsigned_pivoted_function_S Calculus
        (S_of_C (@full_of_restricted_C _ C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p))))
        (fun i =>
           cast_Formula (@calculus_type_wf _ _ p i)
           ((X (p (lift ord_max i)))))
        (existT _ _ (X (p ord_max))).
