From mathcomp Require Import all_ssreflect  all_fingroup zmodp.

Unset Printing Implicit Defensive.

(*                                                                                                                       *)
(*                                                                                                                       *)
(*        FORMALIZING GAGGLES LOGICS' SINTAXIS AND SEMANTICS         *)
(*                                                                                                                       *)
(*                                                                                                                       *)

Inductive Quant := | ex : Quant | fo : Quant.
(* changing universal quantification utf8 symbols  *)
Notation "∃" := ex.
Notation "∀" := fo.
Notation "─" := Zp1.
Notation "＋" := Zp0.
Notation "±" := 'Z_2.
Notation "'Æ'" := Quant.


Inductive Atomic_Skeleton :=
  |  boneS : forall (n : nat), 'S_n.+1 -> ± -> Æ -> nat -> ('I_n -> nat) -> ('I_n -> ±) -> Atomic_Skeleton
.

Inductive BAF_L :=
  |  connective : forall (c : Atomic_Skeleton), (let: (boneS n _ _ _ _ _ _) := c in ('I_n -> BAF_L)) -> BAF_L
  |  T : BAF_L
  |  F : BAF_L
  |  Neg : BAF_L -> BAF_L
  |  Con : BAF_L -> BAF_L -> BAF_L
  |  Dis : BAF_L -> BAF_L -> BAF_L
.
