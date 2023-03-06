From mathcomp Require Import all_ssreflect  all_fingroup zmodp.

Unset Printing Implicit Defensive.

(*                                                                                                                                 *)
(*                                                                                                                                 *)
(*        FORMALIZING GAGGLES LOGICS' SINTAXIS AND SEMANTICS         *)
(*                                                                                                                                 *)
(*                                                                                                                                 *)

(* changing universal quantification utf8 symbols  *)
Notation "'ℕ'" := nat.
Notation "∃" := Zp1.
Notation "∀" := Zp0.
Notation "─" := Zp1.
Notation "＋" := Zp0.
Notation "±" := 'Z_2.
Notation "'Æ'" := 'Z_2.

(* Two possible alternatives are mathcomps lists, which are almost the same of this but have the lemmas proved, or ('I_n -> nat) -> ('I_n -> ±) *)
Inductive tupla {T} : ℕ -> Type :=
  | empty : tupla 0
  | cons : forall n, T -> tupla n -> tupla n.+1
.

(* Alternatives are, using Inductive Types or simply a tuple *)
Class Atomic_Skeleton := {
    sk_arity : ℕ;
    sk_permutation : 'S_sk_arity.+1;
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type : ℕ;
    sk_type_source : @tupla ℕ sk_arity;
    sk_tonicity : @tupla ± sk_arity
}.

(* Pensar una bona manera d'escriure les lletres desde els esquelets en general. *)
Class Propositional_Letter_Skeleton := {
    propositional_letter_skeleton (sign : ±) (quant : Æ) (type : ℕ) := Build_Atomic_Skeleton 0 (1) sign quant type empty empty
}.
(* Maybe I'll add some Coercions in here. *)

Class Assignment {T} := {
  connective : (T -> Atomic_Skeleton)
}.

Class Connective {T} {A} := {
    symbol : T;
    skeleton := @connective T A symbol
}.

Definition arity {T} {A} (C : @Connective T A) := @sk_arity (@skeleton _ _ C).
Class Propositional_Letter {T} {A} := {
    var : T;
    letter_skeleton := @connective T A var;
    min : sk_arity = 0
}.

(* There are some problems with the height in the definition when defining the exponential (both with tuplas and ordinals) *)
Inductive Formula {T} {A} :=
  | variable : Propositional_Letter -> Formula
  | operation : forall (C : Connective), ('I_(arity C) -> Formula) -> Formula
.
