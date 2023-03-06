From mathcomp Require Import all_ssreflect  all_fingroup zmodp.

Unset Printing Implicit Defensive.

(*                                                                                                                                  *)
(*                                                                                                                                  *)
(*               FORMALIZING GAGGLES LOGICS' SINTAXIS AND SEMANTICS                    *)
(*                                                                                                                                  *)
(*                                                                                                                                  *)

(* changing universal quantification utf8 symbols  *)
Notation "'ℕ'" := nat.
Notation "∃" := (@Zp1 1).
Notation "∀" := (@Zp0 1).
Notation "─" := (@Zp1 1). (* '\---' with Agda's key-bindings *)
Notation "⊹" := (@Zp0 1). (* ⊹ '\+ ' with Agda's key-bindings*)
Notation "±" := 'Z_2.
Notation "'Æ'" := 'Z_2.

(* Two possible alternatives are mathcomps lists, which are almost the same of this but have the lemmas proved, or ('I_n -> nat) -> ('I_n -> ±) *)
Inductive tupla {T} : ℕ -> Type :=
  | empty : tupla 0
  | cons n : T -> tupla n -> tupla n.+1
.

(* Passa-ho a Fixpoint *)
Definition first_of {T} {n} (L : @tupla T n) (pos : n > 0) : T.
  destruct L. discriminate.
  exact t.
Defined.

(* Millor escriu-ho desprès com a Fixpoint *)
Definition In {T} {n} (L : @tupla T n) (i : 'I_n) : T.
  elim: L i => [[//]| m t L Hi i].
  case: i => i iord.
  case: i iord => /= [//| i] iord.
  apply ltnSE in iord. apply Hi. exact: Ordinal iord.
Defined.

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
(* Millor fer-ho com ell en l'article, per a sigmplificar, i una coercion *)
Class Propositional_Letter_Skeleton := {
    propositional_letter_skeleton (sign : ±) (quant : Æ) (type : ℕ) := Build_Atomic_Skeleton 0 (1) sign quant type empty empty
}.
(* Maybe I'll add some Coercions in here. *)

Class Assignment {T} := {
  connective : (T -> Atomic_Skeleton)
}.

Class Connective {T} {A} := {
    var : T;
    skeleton := @connective T A var
}.

Definition arity [T] [A] (C : @Connective T A) := @sk_arity (@skeleton _ _ C).
Definition type [T] [A] (C : @Connective T A) := @sk_type (@skeleton _ _ C).
Definition type_source [T] [A] (C : @Connective T A) := @sk_type_source (@skeleton _ _ C).

Module Of_type.
Class Connective {T} {A} k := {
    var : T;
    skeleton := @connective T A var;
    eq_type : sk_type = k
}.
End Of_type.

Module Letter.
Class Connective {T} {A} := {
    var : T;
    skeleton := @connective T A var;
    min : sk_arity = 0
}.
End Letter.
Definition letter_to_connective {T} {A} (P : @Letter.Connective T A) : @Connective T A :=
  match P with {| Letter.var := var0; Letter.min := _ |} => (Build_Connective T A var0) end.
Coercion letter_to_connective : Letter.Connective >-> Connective.

Module Strict.
Class Connective {T} {A} := {
    var : T;
    skeleton := @connective T A var;
    pos : sk_arity > 0
  }.
End Strict.
Definition strict_to_connective {T} {A} (P : @Strict.Connective T A) : @Connective T A :=
  match P with {| Strict.var := var0; Strict.pos := _ |} => (Build_Connective T A var0) end.
Coercion strict_to_connective : Strict.Connective >-> Connective.

Fixpoint exponential (n : ℕ) (T : Type) :=
  match n with
  | 0 => T
  | n.+1 => (T * exponential n T)%type
  end.

Inductive Formula {T : Type} {A : @Assignment T} : ℕ -> Type :=
  | variable : forall P : @Letter.Connective T A, Formula (type P)
  | operation : forall (C : @Connective T A), (forall i : 'I_(@arity T A C), Formula (In (type_source C) i)) -> Formula (type C)
.
