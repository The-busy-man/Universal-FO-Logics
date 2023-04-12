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

(* Changing universal quantification utf8 symbols  *)
Notation "'ℕ'" := nat.
Definition Z2 := 'Z_2.
Definition oneZ2 := (1%:R : Z2)%R.
Definition zeroZ2 := (0 : Z2)%R.
Notation "∃" := oneZ2.
Notation "∀" := zeroZ2.
Notation "─" := oneZ2. (* '\---' with Agda's key-bindings *)
Notation "⊹" := zeroZ2. (* ⊹ '\+ ' with Agda's key-bindings*)
Notation "'Æ'" := Z2.
Notation "±" := Z2.

Definition sign_to_bool (i : ±) :=
  match i with
  Ordinal n _ =>
    match n with
    | 0 => true
    | _.+1 => false
    end
  end
.
Coercion sign_to_bool : Z2 >-> bool.

Goal (∃ + ∃ = ∀)%R. exact: char_Zp. Qed.
Goal (∃ + ⊹ = ─)%R.
by[]. Qed.
Goal (⊹ + ─ = ─)%R.
by[]. Qed.
Goal (⊹ + ⊹ = ∀)%R.
by rewrite GRing.add0r. Qed.

Class Atomic_Skeleton := {
    sk_arity : ℕ;
    sk_permutation : 'S_sk_arity.+1;
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type_output : ℕ;
    sk_type_input : sk_arity.-tuple ℕ;
    sk_sign_input : sk_arity.-tuple ±
}.

(* Arregla-ho a tot arreu *)
Class Connectives := {
  connective_set : Type;
  assignment : (connective_set -> Atomic_Skeleton)
}.

Class Connective {A : Connectives} := {
    var : connective_set;
    skeleton := assignment var
}.

Definition arity {A} (C : Connective) := @sk_arity (@skeleton A C).
Definition permutation {A} (C : Connective) := @sk_permutation (@skeleton A C).
Definition sign {A} (C : Connective) := @sk_sign (@skeleton A C).
Definition sign_input {A} (C : Connective) := @sk_sign_input (@skeleton A C).
Definition quantification {A} (C : Connective) := @sk_quantification (@skeleton A C).
Definition type_output {A} (C : Connective) := @sk_type_output (@skeleton A C).
Definition type_input {A} (C : Connective) := @sk_type_input (@skeleton A C).
Section Of_type.
Variable k : nat.

Class typed_Connective {A : Connectives} := {
    ct : @Connective A;
    eq_type : @sk_type_output (skeleton) = k
}.
End Of_type.

Module Letter.
Class Atomic_Skeleton := {
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type_output : ℕ;
}.
Definition to_atomic_skeleton (P : Atomic_Skeleton) :=
  match P with
    {| sk_sign := s; sk_quantification := q; sk_type_output := t |} =>
      gaggle.Build_Atomic_Skeleton 0 (1) s q t (@Tuple _ _ nil (eq_refl _)) (@Tuple _ _ nil (eq_refl _))
  end.
Class Connective {A : Connectives} := {
    var : connective_set;
    skeleton := assignment var;
    min : sk_arity = 0
}.
Definition to_connective {A}
  (P : Connective) : gaggle.Connective :=
    match P with
      {| var := var0; min := _ |} => (gaggle.Build_Connective A var0)
    end.
End Letter.
Coercion Letter.to_atomic_skeleton : Letter.Atomic_Skeleton >-> Atomic_Skeleton.
Coercion Letter.to_connective : Letter.Connective >-> Connective.

Module Strict.
Class Connective {A : Connectives} := {
    var : connective_set;
    skeleton := assignment var;
    pos : sk_arity > 0
  }.
Definition to_connective {A : Connectives}
  (P : Connective) : gaggle.Connective :=
  match P with
    {| Strict.var := var0; Strict.pos := _ |} =>
      {|
        gaggle.var := var0
      |}
  end.
End Strict.
Coercion Strict.to_connective : Strict.Connective >-> Connective.

Inductive typed_Formula {A : Connectives} : ℕ -> Type :=
  | composition :
      forall (C : @Connective A),
      (forall i : 'I_(@arity A C), typed_Formula (tnth (type_input C) i)) ->
      typed_Formula (type_output C)
.
Definition Formula {A : Connectives} := {k & typed_Formula k}.

Inductive Signed T :=
  | signed : Z2 -> T -> Signed T
.

Definition Boolean_Negation (C : Atomic_Skeleton) : Atomic_Skeleton :=
  match C with
  | {|
      sk_arity := n0;
      sk_permutation := σ;
      sk_sign := s_o;
      sk_quantification := q;
      sk_type_output := t_o;
      sk_type_input := t_i;
      sk_sign_input := s_i
    |} =>
      ({|
          sk_arity := n0;
          sk_permutation := σ;
          sk_sign := ─ + s_o;
          sk_quantification := ─ + q;
          sk_type_output := t_o;
          sk_type_input := t_i;
          sk_sign_input := [ tuple ─ + tnth s_i i | i < n0 ]
        |})%R
  end.
(* Cal convertir-ho en una acció sobre els connectius mitjançant mathcomp.fingroup.action *)

Definition Boolean_Action (A : Connectives) : Connectives :=
  {|
  connective_set := Signed connective_set;
  assignment :=
    fun sC : Signed connective_set =>
    match sC with
    | @signed _ (@Ordinal _ 0 _) t => assignment t
    | @signed _ (@Ordinal _ _.+1 _) t =>
        Boolean_Negation (assignment t)
    end
|}.

Definition and_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := 1;
    sk_sign := ⊹;
    sk_quantification := ∃;
    sk_type_output := 1;
    sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
    sk_sign_input := @Tuple 2 _ [:: 0; 0]%R (eq_refl _)
  |}.
Definition or_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := 1;
    sk_sign := ─;
    sk_quantification := ∀;
    sk_type_output := 1;
    sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
    sk_sign_input := @Tuple 2 _ [:: 1; 1]%R (eq_refl _)
  |}.
Definition lres_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := tperm (@Ordinal 3 0 (eq_refl _)) (@Ordinal 3 2 (eq_refl _));
    sk_sign := ─;
    sk_quantification := ∀;
    sk_type_output := 1;
    sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
    sk_sign_input := @Tuple 2 _ [:: ⊹; ─]%R (eq_refl _)
  |}.

Definition and_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ =>
         {|
           sk_arity := 2;
           sk_permutation := 1;
           sk_sign := ⊹;
           sk_quantification := ∃;
           sk_type_output := 1;
           sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
           sk_sign_input := @Tuple 2 _ [:: 0; 0]%R (eq_refl _)
         |})
  |}.
Definition or_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ =>
         {|
           sk_arity := 2;
           sk_permutation := 1;
           sk_sign := ─;
           sk_quantification := ∀;
           sk_type_output := 1;
           sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
           sk_sign_input := @Tuple 2 _ [:: 1; 1]%R (eq_refl _)
         |})
  |}.
Definition lres_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ =>
         {|
           sk_arity := 2;
           sk_permutation := tperm (@Ordinal 3 0 (eq_refl _)) (@Ordinal 3 2 (eq_refl _));
           sk_sign := ─;
           sk_quantification := ∀;
           sk_type_output := 1;
           sk_type_input := @Tuple 2 _ [:: 1; 1] (eq_refl _);
           sk_sign_input := @Tuple 2 _ [:: ⊹; ─]%R (eq_refl _)
         |})
  |}.

Goal @assignment (Boolean_Action and_connective) (signed (@connective_set and_connective) ⊹ 0%R) = @assignment and_connective 0%R.
  by[].
Qed.
(* Cal pensar una manera general per a que portar les proves decidibles no es fagi carregos. *)
Goal @assignment (Boolean_Action and_connective) (signed (@connective_set and_connective) ─ 0%R) = @assignment or_connective 0%R.
  move => /=.
  rewrite GRing.addr0.
  rewrite -GRing.mulrnDr.
  rewrite char_Zp; last by[].
  f_equal.
  rewrite /mktuple. rewrite /map_tuple.
Admitted.

(* PERMUTATIONS and α-ACTION *)

(* After arranging the actions, Sintaxis will be done.
   It will have to be reworked by subtituting my tuples, using decent coercions and cycles.
 *)

(* Has de fer manualment la descomposició en cicles, a mathcomp no la tenen.
   Fer servir connect/dfs de fingraph, porbit de perm o traject.
   Probablement utilitzant un conjunt com a prod_tpermP.
 *)

(* proposed by Kazuhiko Sakaguchi *)
Definition fun_of_cycle (T : eqType) (xs : seq T) (x : T) : T :=
  nth x (rot 1 xs) (index x xs).

Lemma index_rot1 {T} l x : uniq l -> x \in l -> (index x l) = let n := (@index T x (rot 1 l)) in if (n == (size l).-1) then 0 else n.+1.
Proof.
  case: l; simpl; intros. reflexivity.
  move: H => /andP [ainl Hl].
  rewrite /rot /= drop0 take0.
  rewrite in_cons in H0. move: H0 => /orP [/eqP Heq | xinl].
    rewrite Heq !eq_refl.
    rewrite index_cat. apply negbTE in ainl.
    by rewrite ainl /= eq_refl addn0 eq_refl.
  case Heq: (a == x); simpl.
    rewrite (eqP Heq) in ainl.
    apply negbTE in ainl.
    rewrite xinl in ainl. discriminate.
  rewrite index_cat xinl. rewrite -index_mem in xinl. apply ltn_eqF in xinl.
  by rewrite xinl.
Qed.

(* Aquest tipus de resultats genèrics han d'anar en un altre fitxer. *)
Lemma connective_set_default_index_inj {T : eqType} {l} {x y : T} : x \in l -> y \in l -> index x l = index y l -> x = y.
Proof.
  elim: l; simpl; intros.
    discriminate.
  case Haeqx: (x == a); case Haeqy: (y == a);
  rewrite -cat1s mem_cat in H0; rewrite mem_seq1 in H0;
  rewrite -cat1s mem_cat in H1; rewrite mem_seq1 in H1.
  - rewrite -(eqP Haeqy) in Haeqx.
    exact: (eqP Haeqx).
  - rewrite eq_sym in Haeqx. rewrite eq_sym in Haeqy.
    by rewrite Haeqx Haeqy in H2.
  - rewrite eq_sym in Haeqx. rewrite eq_sym in Haeqy.
    by rewrite Haeqx Haeqy in H2.
  rewrite Haeqx in H0. rewrite Haeqy in H1.
  rewrite !Bool.orb_false_l in H0 H1.
  rewrite eq_sym in Haeqx. rewrite eq_sym in Haeqy.
  rewrite Haeqx Haeqy in H2.
  injection H2 as H2.
  exact: (H H0 H1 H2).
Qed.

Inductive cycle (T : eqType) := Cycle l of (@uniq T l).
Coercion seq_of_cycle {T : eqType} (c : cycle T) := let: Cycle l _ := c in l.

HB.instance Definition _ {T} := [isSub of cycle T for seq_of_cycle].
HB.instance Definition _ {T} := [eqMixin of cycle T by <:].

(* Pots demostrar-ho també fent servir:
  apply: (@can_inj _ _ _ (fun z => (nth z (rot (size l).-1 l) (index z l)))).
   D'altre banda, demo molt millorable.
*)
Lemma cycle_proof [T : finType] (l : cycle T) : injective [fun z => fun_of_cycle T l z].
Proof.
  move: l => [l Hl] x y /=.
  rewrite /fun_of_cycle.
  case xinl: (x\in l); case yinl: (y\in l) => // /eqP.
  - rewrite -(rot_uniq 1) in Hl.
    rewrite (set_nth_default y x) ?(nth_uniq y _ _ Hl) ?size_rot ?index_mem // => /eqP.
    exact (connective_set_default_index_inj xinl yinl).
  - rewrite -(index_mem x) -(size_rot 1) in xinl.
    apply (mem_nth x) in xinl. move => yinrot. rewrite (eqP yinrot) in xinl.
    rewrite mem_rot in xinl.
    rewrite nth_default in xinl.
      rewrite yinl in xinl.
      discriminate.
    rewrite -index_mem ltnNge in yinl.
    rewrite size_rot.
    exact: (negbFE yinl).
  - rewrite -(index_mem y) -(size_rot 1) in yinl.
    apply (mem_nth y) in yinl. move => yinrot. rewrite -(eqP yinrot) in yinl.
    rewrite mem_rot in yinl.
    rewrite nth_default in yinl.
      rewrite xinl in yinl.
      discriminate.
    rewrite -index_mem ltnNge in xinl.
    rewrite size_rot.
    exact: (negbFE xinl).
  rewrite !(nth_default). exact/eqP.
  - rewrite -index_mem ltnNge in yinl.
    rewrite size_rot.
    exact: (negbFE yinl).
  rewrite -index_mem ltnNge in xinl.
  rewrite size_rot.
  exact: (negbFE xinl).
Qed.

(* Cycles come out of a list as its rotation. *)
Definition cperm {T : finType} (l : cycle T) := perm (cycle_proof l).

Definition tpermJ_res {n} (i j : 'I_n) : (i <> j) ->
  let i' := (lift (ord_max) i) in let j' := (lift (ord_max) j) in
  (tperm i' (ord_max) ^ tperm j' (ord_max))%g = tperm i' j'.
Proof.
  intros.
  rewrite /i' /j'.
  rewrite tpermJ tpermR tpermD.
  - reflexivity.
  - apply/negP => /eqP. apply: (contra_not _ H).
    symmetry. exact: (lift_inj H0).
  exact: (neq_lift _ _).
Qed.

(* Semantical type input is posing a serious problem here, as the type input must change, in order to respect composition restrictions (both in Permute and partial_Residuation).
   Furthermore, when residuating a with the ord_max component, through partial_Residuation, the new component might of any possible type.
   Therefore, we need a different kind of residuation for all types we are interested in returning.
   In case we want sequents to have the same types in both sides it gets simply solved by interchanging type output and type input in the type sequence.
   THIS CHANGES ARE NOT REFLECTED IN THE ARTICLES DEFINITIONS!
 *)
Definition sk_partial_Residuation (C : Atomic_Skeleton) (i : 'I_(sk_arity)) : Atomic_Skeleton :=
  let s := (tnth sk_sign_input i) in
  let n := (@ord_max sk_arity) in
  (* Si l'opacitat no et donès problemes, aleshores utilitza lift ord_max *)
  let i' := lift n i in
  {|
    sk_arity := sk_arity;
    sk_permutation := (tperm i' n) * sk_permutation;
    sk_sign := ─ + s + sk_sign;
    sk_quantification := ─ + s + sk_quantification;
    sk_type_output := sk_type_output;
    sk_type_input := sk_type_input;
    sk_sign_input := [ tuple let: s' := tnth sk_sign_input j in
                       if j == i then s' else ─ + s + s' | j < n]
  |}%R
.

Definition sk_Permute (C : Atomic_Skeleton) (p : 'S_(sk_arity)) : Atomic_Skeleton :=
  let n := Ordinal (leqnn sk_arity.+1) in
  {|
    sk_arity := sk_arity;
    sk_permutation := (lift_perm ord_max ord_max p * sk_permutation)%g;
    sk_sign := sk_sign;
    sk_quantification := sk_quantification;
    sk_type_output := sk_type_output;
    sk_type_input := [tuple tnth sk_type_input (p i) | i < n];
    sk_sign_input := [tuple tnth sk_sign_input (p i) | i < n]
  |}%R
.

Definition unlift_seq {n} (cs : seq 'I_n) (x : 'I_n) :=
  map (unlift x) cs.

Lemma unlift_some_seq {n} (c : seq 'I_n) (x : 'I_n) :
  x\notin c -> {d : seq 'I_n.-1 | c = map (lift x) d & map (unlift x) c = map Some d}.
Proof.
  elim: c => /= [_| a l IHl Hx].
    exact: (exist2 _ _ [::]).
  move: Hx. rewrite in_cons negb_or => /andP [/unlift_some Hx /IHl IHlx].
  apply (exist2 _ _ ((proj1_sig Hx) :: (proj1_sig IHlx))) => /=.
    f_equal. exact: (proj2_sig Hx).1. exact: (proj2_sig IHlx).1.
  f_equal. exact: (proj2_sig Hx).2. exact: (proj2_sig IHlx).2.
Qed.

Lemma unlift_some_seq_seq {n} (cs : seq (seq 'I_n)) (x : 'I_n) :
  all (fun c => x\notin c) cs -> {cs' : seq (seq 'I_n.-1) | cs = map (map (lift x)) cs' & map (map (unlift x)) cs = map (map Some) cs'}.
Proof.
  elim: cs => /= [_| a l IHl Hx].
    exact: (exist2 _ _ [::]).
  move: Hx => /andP [/unlift_some_seq Hx /IHl IHlx].
  apply (exist2 _ _ ((proj1_sig Hx) :: (proj1_sig IHlx))) => /=.
    f_equal. exact: (proj2_sig Hx).1. exact: (proj2_sig IHlx).1.
  f_equal. exact: (proj2_sig Hx).2. exact: (proj2_sig IHlx).2.
Qed.

Lemma unlift_inj {n} {h : 'I_n} [i1 i2 : 'I_n] : unlift h i1 = unlift h i2 -> i1 = i2.
Proof.
  case: (unliftP h i1) => [j Hj|]; case: (unliftP h i2) => [j' Hj' H|H1 H2]//.
  injection H as H. by rewrite Hj Hj' H.
  by rewrite H1 H2.
Qed.

Lemma Some_inj {A : Type} : injective (@Some A).
Proof.
  rewrite /injective => x y H.
  by injection H.
Qed.

Definition unlift_perm_fun {n} i j (s : 'S_n) k :=
  if k is Some k'
  then unlift j (s (lift i k'))
  else unlift j (s i).

Lemma unlift_perm_fun_inj {n} i j (s : 'S_n) : injective (unlift_perm_fun i j s).
Proof.
  rewrite /unlift_perm_fun => x y.
  case: x => [x|]; case: y => [y| //];
    first (by move /unlift_inj/perm_inj/lift_inj => ->);
  move/unlift_inj/perm_inj/eqP; by rewrite ?lift_eqF // eq_sym lift_eqF.
Qed.

Definition unlift_perm {n} i j (s : 'S_n) :=
  perm (unlift_perm_fun_inj i j s).

Definition option_perm_fun {T : finType} (p : {perm T}) k :=
  if k is Some k'
  then Some (p k')
  else None.

Definition option_perm_fun_inj {T : finType} (p : {perm T}) : injective (option_perm_fun p).
Proof.
  rewrite /option_perm_fun.
  case => [x|] [// y|//].
  move => H. apply Some_inj in H.
  apply perm_inj in H. by rewrite H.
Qed.

Definition option_perm {T : finType} (p : {perm T}) :=
  perm (option_perm_fun_inj p).

Lemma unlift_inj_iff {n m} (f : 'I_n -> 'I_m) (f_inj : injective f) x y :
  unlift x y <-> unlift (f x) (f y).
Proof.
  case: (@eqP _ x y) => [-> | nH].
    by rewrite !unlift_none.
  assert (Heq : f x != f y). by apply/eqP => /f_inj.
  split.
    by rewrite (proj2_sig (unlift_some Heq)).2.
  move: nH => /eqP nH.
  by rewrite (proj2_sig (unlift_some nH)).2.
Qed.

Lemma option_some_proof {T U : Type} (f : option T -> option U) (f_wd : forall x : option T, x -> f x) x : ~ (f (Some x) = None).
  case Heq: (f (Some x)) => [//|].
  move: (f_wd (Some x) (eq_refl true)).
  by rewrite Heq.
Qed.

Definition option_some {T U : Type} (f : option T -> option U) (f_wd : forall x : option T, x -> f x) : T -> U
  :=
  fun x =>
    (match f (Some x) as o return f (Some x) = o -> U with
    | Some a => fun=> a
    | None => fun Ho => False_rect U (option_some_proof f f_wd x Ho)
    end) (Logic.eq_refl _).

Definition option_match_some_rw {A P vSome vNone o} {x:A} (H:Some x = o)
  : match o return P o with None => vNone | Some y => vSome y end  = rew [P] H in vSome x
  := match H with Logic.eq_refl => Logic.eq_refl end.

Definition option_match_none_rw {A P vSome vNone} {o : option A} (H:None = o)
  : match o return P o with None => vNone | Some y => vSome y end  = rew [P] H in vNone
  := match H with Logic.eq_refl => Logic.eq_refl end.

Definition constant_rw T P (x y:T) (H:x=y) B b
  : rew [fun z => P z -> B] H in (fun _ => b) = fun _ => b
  := match H with Logic.eq_refl => Logic.eq_refl end.

Lemma option_some_wf {T U : Type} (f : option T -> option U) (f_wd : forall x : option T, x -> f x) x : f (Some x) = Some (option_some f f_wd x).
Proof.
  case Heq: (f (Some x)) => [a|].
    rewrite /option_some (option_match_some_rw (Logic.eq_sym Heq)).
    by rewrite constant_rw.
  by apply option_some_proof in Heq.
Qed.

Lemma option_some_finj {T : Type} (f : option T -> option T) (f_wd : forall x : option T, x -> f x) (f_inj : injective f) : injective (option_some f f_wd).
Proof.
  move => x y.
  case Heqx : (f (Some x)) => [a|]; case Heqy : (f (Some y)) => [b|].
  - rewrite /option_some.
    rewrite (option_match_some_rw (Logic.eq_sym Heqx)).
    rewrite (option_match_some_rw (Logic.eq_sym Heqy)).
    rewrite !constant_rw => Heqab.
    rewrite Heqab -Heqy in Heqx.
    move: Heqx => /f_inj Heqx.
    exact: (Some_inj _ _ Heqx).
  - move: (f_wd (Some y) (eq_refl true)).
    by rewrite Heqy.
  - move: (f_wd (Some x) (eq_refl true)).
    by rewrite Heqx.
  rewrite -Heqy in Heqx.
  move: Heqx => /f_inj Heqx.
  by apply Some_inj in Heqx.
Qed.

Lemma unlift_perm_unlift [n : ℕ] (i j : 'I_n) (s : 'S_n) (k : 'I_n):
  unlift_perm i j s (unlift i k) = unlift j (s k).
Proof.
  rewrite permE/unlift_perm_fun.
  case: (@eqP _ i k) => [-> | /eqP nHeq].
    by rewrite unlift_none.
  move: (unlift_some nHeq) => [k' Hunit Hcounit].
  by rewrite Hcounit -Hunit.
Qed.

Lemma unlift_some_perm {n} (i j : 'I_n.+1) (s : 'S_n.+1) :
  (s i = j) -> {p : 'S_n | s = lift_perm i j p & unlift_perm i j s = option_perm p}.
Proof.
  move => H.
  assert (unlift_wd : forall (x : option 'I_n), x -> (unlift_perm i j s x)).
    move => x. rewrite /unlift_perm permE/unlift_perm_fun.
    case: x => [x|//] Hx.
    rewrite -H -(unlift_inj_iff _ perm_inj).
    by rewrite (proj2_sig (unlift_some (neq_lift i x))).2.
  apply (exist2 _ _ (perm (option_some_finj _ unlift_wd perm_inj))).
    rewrite -permP => x.
    rewrite permE/lift_perm_fun.
    case: (@eqP _ i x) => Heq.
      by rewrite -Heq unlift_none.
    move: Heq => /eqP Heq.
    move: (unlift_some Heq) => [k Hunit Hcounit].
    rewrite Hcounit permE Hunit -{1}H.
    case Hsome: (unlift_perm i j s (Some k)) => [a|].
      rewrite /option_some.
      rewrite (option_match_some_rw (Logic.eq_sym Hsome)) constant_rw.
      rewrite -Hcounit unlift_perm_unlift Hunit -H in Hsome.
      rewrite Hunit in Heq.
      move: Heq => /eqP/(contra_not (@perm_inj _ s _ _))/eqP.
      move /(unlift_some) => /= [k' Hunit' Hcounit'].
      rewrite Hunit'. rewrite Hsome in Hcounit'.
      by rewrite (Some_inj _ _ Hcounit').
    rewrite -Hcounit unlift_perm_unlift Hunit -H in Hsome.
    rewrite Hunit in Heq.
    move: Heq => /eqP/(contra_not (@perm_inj _ s _ _))/eqP Heq.
    by rewrite (proj2_sig (unlift_some Heq)).2 /= in Hsome.
  rewrite -permP => x.
  rewrite !permE/unlift_perm_fun/option_perm_fun.
  case: x => [a|].
    rewrite permE.
    case Hsome : (unlift_perm i j s (Some a)) => [b|].
      rewrite /option_some.
      rewrite (option_match_some_rw (Logic.eq_sym Hsome)).
      rewrite constant_rw.
      by rewrite permE /= in Hsome.
    rewrite permE/= in Hsome.
    move: (neq_lift i a) => /eqP/(contra_not (@perm_inj _ s _ _))/eqP Heq.
    move: (unlift_some Heq) => [k Hunit Hcounit].
    by rewrite -H Hcounit in Hsome.
  by rewrite H unlift_none.
Qed.

Lemma ord_max_residuate {T : finType} (s : {perm T}) x : (s * (tperm x (s x)))%g x = x.
Proof.
  by rewrite permE /= tpermR.
Qed.

Lemma neqP {A : eqType} {a b : A} : a == b = false -> a != b.
Proof.
  by move => /eqP/eqP.
Qed.


(* versió inductiva tb?
*)
Definition sk_Residuation
  (C : Atomic_Skeleton) (s : 'S_(sk_arity).+1) : Atomic_Skeleton :=
  let n := sk_arity in
  match unlift ord_max (s ord_max) with
  | Some i =>
      sk_Permute
        (sk_partial_Residuation C i)
        (proj1_sig (unlift_some_perm _ _
                      (s * (tperm ord_max (s ord_max)))%g
                      (ord_max_residuate s ord_max)))
  | None =>
      sk_Permute C
        (proj1_sig (unlift_some_perm _ _
                      (s * (tperm ord_max (s ord_max)))%g
                      (ord_max_residuate s ord_max)))
  end.
Section Of_arity.
Variable n : nat.

Class ary_Skeleton := {
    sa : @Atomic_Skeleton;
    eqs_arity : n = sk_arity
  }.
Class ary_Connective {A : Connectives} := {
    ca : @Connective A;
    eqc_arity : n = @sk_arity skeleton
}.

Definition ska_Residuation
  (C : ary_Skeleton) (s : 'S_n.+1) :=
  match unlift ord_max (s ord_max) with
  | Some i =>
      {| sa := sk_Permute
           (sk_partial_Residuation sa (cast_ord eqs_arity i))
           (cast_perm eqs_arity (proj1_sig (unlift_some_perm _ _
                      (s * (tperm ord_max (s ord_max)))%g
                      (ord_max_residuate s ord_max))));
        eqs_arity := eqs_arity
      |}
  | None =>
      {| sa := sk_Permute sa
           (cast_perm eqs_arity (proj1_sig (unlift_some_perm _ _
                      (s * (tperm ord_max (s ord_max)))%g
                      (ord_max_residuate s ord_max))));
        eqs_arity := eqs_arity
      |}
  end.
End Of_arity.
Coercion ca : ary_Connective >-> Connective.
Coercion sa : ary_Skeleton >-> Atomic_Skeleton.

(* Cal Residuació tb sobre connectius. *)

Goal
  (sk_Residuation and_skeleton
  (tperm (@Ordinal 3 0 (eq_refl _)) (@Ordinal 3 2 (eq_refl _))))
  = lres_skeleton.
  rewrite /sk_Residuation.
  move: (@unlift_some _ ord_max (tperm
         (Ordinal (n:=3) (m:=0)
            (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 3)))
         (Ordinal (n:=3) (m:=2)
            (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (3 - 3))) ord_max)) => [|j Heqj1 Heqj2].
    by rewrite permE /=.
  rewrite Heqj2.
  rewrite /sk_Permute/ord_max/and_skeleton/lres_skeleton/sk_sign/sk_arity/sk_type_output/sk_quantification.
  move: (unlift_some_perm (Ordinal (n:=3) (m:=2) (ltnSn 2))
           (Ordinal (n:=3) (m:=2) (ltnSn 2))
           (tperm
              (Ordinal (n:=3) (m:=0)
                 (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 3)))
              (Ordinal (n:=3) (m:=2)
                 (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (3 - 3))) *
            tperm (Ordinal (n:=3) (m:=2) (ltnSn 2))
              (tperm
                 (Ordinal (n:=3) (m:=0)
                    (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 3)))
                 (Ordinal (n:=3) (m:=2)
                    (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (3 - 3)))
                 (Ordinal (n:=3) (m:=2) (ltnSn 2))))
           (ord_max_residuate
              (tperm
                 (Ordinal (n:=3) (m:=0)
                    (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 3)))
                 (Ordinal (n:=3) (m:=2)
                    (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (3 - 3))))
              (Ordinal (n:=3) (m:=2) (ltnSn 2)))) => [p Heqp1 Heqp2].
  f_equal => //=.
  - rewrite -Heqp1 -permP => x. rewrite !permE/=.
    rewrite mulg1.
    case: x => n Hn.
    case: n Hn => /= [Hn| n Hn].
      repeat (rewrite permE /=).
      rewrite -Heqj1 permE /= /ord_max.
      exact: ord_inj.
    case: n Hn => /= [Hn| n Hn].
      repeat (rewrite permE /=).
      rewrite -Heqj1 permE /= /ord_max.
      exact: ord_inj.
    case: n Hn => //= Hn.
      repeat (rewrite permE /=).
      rewrite -Heqj1 permE /= /ord_max.
      exact: ord_inj.
  - rewrite (tnth_nth ord_max) /=.
    move: (f_equal (@nat_of_ord 3) Heqj1).
    by rewrite lift_max permE /= => <- /=.
  - rewrite (tnth_nth ord_max) /=.
    move: (f_equal (@nat_of_ord 3) Heqj1).
    rewrite lift_max permE /= => <- /=.
    by rewrite GRing.addr0 -GRing.mulrnDr char_Zp.
  - apply eq_from_tnth => x.
    rewrite !(tnth_nth 0) /=.
    case: x => n Hn.
      (* tractar amb tnth o [tuple _] *)
    have H : tnth
          (Tuple (n:=2) (tval:=[:: 1; 1])
             (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) 2)) \o p
             =1 (nth 0 [:: 1; 1]) \o (nat_of_ord (n:=2)) \o p.
    move => x /=. by rewrite /tnth (set_nth_default 0).
    rewrite (eq_map H) /=.
    rewrite (nth_map (@Ordinal 2 0 (eq_refl _)));
      last by rewrite size_enum_ord.
    rewrite permE /= -permP in Heqp2.
    case: n Hn => /= [Hn| n Hn].
      have {16}->: 0 = nat_of_ord (@Ordinal 2 0 (eq_refl _)). by[].
      rewrite nth_ord_enum.
      move: Heqp2 => /(_ (Some (Ordinal (n:=2) (m:=0) (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 2))))).
      repeat (rewrite permE /=).
      have nHeq : (Ordinal (n:=3) (m:=2) (ltnSn 2)) != (Ordinal (n:=3) (m:=0) (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 3))). by[].
      move: (unlift_some nHeq) => [i Heqi1 Heqi2].
      move: Heqi1 => /(f_equal (nat_of_ord (n:=3))) Heqi1.
      rewrite lift_max in Heqi1.
      rewrite Heqi2 => /(Some_inj _ _) /(f_equal (nat_of_ord (n:=2))) /=.
      by rewrite -Heqi1 => <- /=.
    case: n Hn => /= [Hn|//].
    have {14}->: 1 = nat_of_ord (@Ordinal 2 1 (eq_refl _)). by[].
    rewrite nth_ord_enum.
    move: Heqp2 => /(_ (Some (Ordinal (n:=2) (m:=1) (eq_refl _)))).
    repeat (rewrite permE /=).
    have nHeq : ord_max != lift ord_max (Ordinal (n:=2) (m:=1) (eq_refl _)). by[].
    move: (unlift_some nHeq) => [i Heqi1 Heqi2].
    move: Heqi1 => /(f_equal (nat_of_ord (n:=3))) Heqi1.
    rewrite lift_max in Heqi1.
    rewrite Heqi2 => /(Some_inj _ _) /(f_equal (nat_of_ord (n:=2))) /=.
    move => <-.
    case: i Heqi1 Heqi2.
    by case => //; case => //; case => //.
  apply eq_from_tnth => x.
  rewrite !(tnth_nth (@Ordinal 2 0 (eq_refl _))) /=.
  case: x => n Hn.
  rewrite (nth_map (@Ordinal 2 0 (eq_refl _)));
    last by rewrite size_enum_ord.
  rewrite !(tnth_nth (@Ordinal 2 0 (eq_refl _))).
  rewrite (nth_map (@Ordinal 2 0 (eq_refl _)));
    last by rewrite size_enum_ord.
  rewrite nth_ord_enum /= nth_ord_enum /=.
  case: n Hn => [Hn | n Hn].
    rewrite -permP in Heqp2.
    move: Heqp2 => /(_ (Some (Ordinal (n:=2) (m:=0) (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 2))))).
    repeat (rewrite permE /=).
    have nHeq : ord_max != Ordinal (n:=3) (m:=0) (eq_refl _). by[].
    move: (unlift_some nHeq) => /= [i Heqi1 Heqi2].
    apply (f_equal (nat_of_ord (n:=3))) in Heqi1.
    rewrite lift_max in Heqi1.
    rewrite Heqi2 => /(Some_inj _ _) /(f_equal (@nat_of_ord 2)).
    have <- : Ordinal (n:=2) (m:=0) Hn = Ordinal (n:=2) (m:=0) (eqxx (T:=Datatypes_nat__canonical__eqtype_Equality) (1 - 2)). by apply ord_inj.
    rewrite -Heqi1 => H.
    have <- : p (Ordinal (n:=2) (m:=0) Hn) = j.
      apply ord_inj. rewrite -H.
      apply (f_equal (@nat_of_ord 3)) in Heqj1.
      rewrite lift_max permE /= in Heqj1.
      by rewrite -Heqj1.
    rewrite eq_refl.
    by rewrite (tnth_nth (@Ordinal 2 0 (eq_refl _))) -H /=.
  case: n Hn => // Hn.
  rewrite -permP in Heqp2.
  move: Heqp2 => /(_ (Some (Ordinal (n:=2) (m:=1) (eq_refl _)))).
  repeat (rewrite permE /=).
  have nHeq : ord_max != lift ord_max (Ordinal (n:=2) (m:=1) (eq_refl _)). by[].
  move: (unlift_some nHeq) => /= [i Heqi1 Heqi2].
  apply lift_inj in Heqi1.
  rewrite Heqi2 -Heqi1 => /(Some_inj _ _).
  have <- : Ordinal (n:=2) (m:=1) Hn = Ordinal (n:=2) (m:=1) (eq_refl _). by apply ord_inj.
  move => <-.
  have <-: (Ordinal (n:=2) (m:=0) (eq_refl _)) = j.
    apply ord_inj.
    apply (f_equal (@nat_of_ord 3)) in Heqj1.
    rewrite lift_max permE /= in Heqj1.
    by rewrite -Heqj1.
  have -> : (@Ordinal 2 1 Hn) == @Ordinal 2 0 (eq_refl _) = false.
    by apply /negPf/eqP => /(f_equal (@nat_of_ord 2)).
  by rewrite (tnth_nth (@Ordinal 2 0 (eq_refl _))) /=.
Qed.

(* Comprovar que són accions *)

(* Total action should be defined over all permutations of natural numbers, which is problematic as we have been using properties of finite types.
   For the moment we might work with sets of connectives of bounded height.
   Furthermore, this will also imply that our Atomic_Skeletons will be finite.
   Our first approach will be reducing all skeletons to be of fixed arity.
 *)

Theorem sk_α_is_action {n} : is_action [set: 'S_n.+1] (ska_Residuation n).
Proof.
  apply: is_total_action => [C|C p1 p2].
    case: C;
    case => n0 p s q t ti si Heq.
    rewrite /ska_Residuation {1}permE unlift_none.
    rewrite /sk_Permute /=.
    have -> :
          (lift_perm ord_max ord_max
            (cast_perm Heq
               (ssrfun.s2val
                  (unlift_some_perm ord_max ord_max (1 * tperm ord_max ((1%g : 'S_n.+1) ord_max))
                     (ord_max_residuate 1 ord_max)))) * sk_permutation)%g = sk_permutation.
      admit.
    have -> :
      [tuple tnth sk_type_input
         (cast_perm Heq
            (ssrfun.s2val
               (unlift_some_perm ord_max ord_max (1 * tperm ord_max ((1%g : 'S_n.+1) ord_max))
                            (ord_max_residuate 1 ord_max))) i)
             | i < sk_arity] = sk_type_input.
      admit.
    have -> :
      [tuple tnth sk_sign_input
                   (cast_perm Heq
                      (ssrfun.s2val
                         (unlift_some_perm ord_max ord_max (1 * tperm ord_max ((1%g : 'S_n.+1) ord_max))
                            (ord_max_residuate 1 ord_max))) i)
             | i < sk_arity] = sk_sign_input.
      admit.
    by f_equal.
  rewrite !/ska_Residuation.
  rewrite {1}permE /=.
  case Heqa: (unlift ord_max (p2 ord_max)) => [a|];
  case Heqb: (unlift ord_max (p2 (p1 ord_max))) => [b|].
  - f_equal.
Admitted.

Definition sk_α {n} := Action (sk_α_is_action (n:=n)).


(* Convertir-ho en una acció sobre certs conjunts de connectius *)

Definition orbit_of_skeleton (C : Atomic_Skeleton) : Connectives :=
  {|
    connective_set := 'S_sk_arity.+1;
    assignment := fun p => (sk_α {| sa:= C; eqs_arity := Logic.eq_refl _|} p)
  |}.

Lemma ska_Residuation_arity_invariant (C : Atomic_Skeleton) (p : 'S_sk_arity.+1) : @sk_arity C = @sk_arity ((ska_Residuation _ {| sa:= C; eqs_arity := Logic.eq_refl _|} p)).
Proof.
  rewrite /ska_Residuation /=.
  by case: (unlift ord_max (p ord_max)).
Qed.

Lemma orbit_arity (C : Atomic_Skeleton) (D : @Connective (orbit_of_skeleton C)) :
  @sk_arity C = @sk_arity (@skeleton _ D).
Proof.
  move: D. rewrite /orbit_of_skeleton.
  case => /= lD.
  move: C lD => /= [aC pC sC qC toC tiC siC] lD.
  by rewrite -ska_Residuation_arity_invariant.
Qed.

Lemma orbit_set (C : Atomic_Skeleton) : @connective_set (orbit_of_skeleton C) = 'S_sk_arity.+1.
Proof. by[]. Qed.

(* STRUCTURES *)

(* Una definició diferent alternativa seria que structure_set hagues de contenir als connectius A però en poguès tenir més. *)
(* We set a new class because formulas from structures are defined independently from connectives.
   With a duplicate definition it is easier for us to tell them appart.
 *)
Class Structures {A : Connectives} :=
  {
    structure_set := @connective_set A;
    structure_assignment := @assignment A
  }.
Class Structure {A : Connectives} {S : @Structures A} :=
  {
    structure_var : connective_set;
    structure_skeleton := assignment structure_var
  }.
Definition S_to_Cs {A} (S : @Structures A) := A.
Definition C_to_Ss (C : @Connectives) := @Build_Structures C.
Definition S_to_C {A : Connectives} {B} (S : @Structure _ B) : @Connective (S_to_Cs B) :=
  {|
    var := structure_var
  |}.
Definition C_to_S {A} (C : @Connective A) : @Structure A (C_to_Ss A) :=
  {|
    structure_var := var
  |}.

(* Boolean negation to be done and added over formulas.
   As an alternative one could leave the sign over formulas as ill-defined (it takes whatever value is required by context).
 *)
Inductive typed_Structural_Formula {A : Connectives} {S : Structures} : ℕ -> Type :=
  | from_formula {k} : @typed_Formula A k -> typed_Structural_Formula k
  | structural_composition
    : forall C : Structure,
      (forall i : 'I_(@sk_arity (@structure_skeleton _ _ C)),
          typed_Structural_Formula (tnth (@sk_type_input (@structure_skeleton _ _ C)) i)) ->
      typed_Structural_Formula (@sk_type_output (@structure_skeleton _ _ C)).
Definition Structural_Formula {A : Connectives} {S : Structures} := sigT typed_Structural_Formula.

Definition Residuation {C : Atomic_Skeleton} (D : @Structure _ (C_to_Ss (orbit_of_skeleton C))) (p : 'S_(@sk_arity C).+1) : @Structure _ (C_to_Ss (orbit_of_skeleton C)) :=
  @Build_Structure _ (C_to_Ss (orbit_of_skeleton C))
    (p * (cast_perm (f_equal S (Logic.eq_sym (orbit_arity C (S_to_C D))))
              (@sk_permutation (@skeleton _ (S_to_C D)))))%g.

Theorem α_is_action {C : Atomic_Skeleton} : is_action [set: 'S_(@sk_arity C).+1] (@Residuation C).
Proof.
  apply is_total_action.
    rewrite /Residuation. move => [lD D].
    rewrite mul1g. f_equal.
    rewrite -permP => x.
    rewrite cast_permE /=.
Admitted.

(* Each connective from Generators creates a full independent orbit of connectives. *)
Definition full_Connectives (Generators : Connectives) :=
  {|
    connective_set := sigT (fun (C : @Connective Generators) => 'S_sk_arity.+1);
    assignment := fun Cp =>
                  let: existT C p := Cp in
                    (sk_α {| sa:= skeleton; eqs_arity := Logic.eq_refl _|} p)
  |}.

Definition α {C : Atomic_Skeleton} := Action (α_is_action (C:=C)).


(* ATOMIC CALCULUS *)

(* Agafar tota l'òrbita per la negació i la residuació. *)
(* Potser val la pena fer-ho com comentava el Guillaume i de moment limitar-ho tot només sobre esquelets. *)

Definition unsigned_function
  (s : ±) {A : Connectives} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type)
  (X Y : Structural_Formula)
  :=
  f
    (if s then Y else X)
    (if s then X else Y).

Definition unsigned_pivoted_function_S
  {A : Connectives} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type) (C : @Structure _ S)
  (X : forall i:'I_(@sk_arity (@structure_skeleton _ _ C)),
      typed_Structural_Formula (tnth sk_type_input i))
  (U : Structural_Formula)
  :=
  unsigned_function (@sk_sign (@structure_skeleton _ _ C)) f
    U (existT _
           (@sk_type_output (@structure_skeleton _ _ C)) (structural_composition C X)).

Definition unsigned_pivoted_function_C
  {A : Connectives} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type) (C : @Connective A)
  (φ : forall i:'I_(arity C),
      typed_Formula (tnth (type_input C) i))
  (U : Structural_Formula)
  :=
  unsigned_function (sign C) f
    U (existT _
           (type_output C) (from_formula (composition C φ))).

(* stopped due to some formalisation problems. *)

(* semantical types are a little bit problematic here, as we need a different residuated skeleton, depending on the type of the consequent in dr1. *)
(* Lacks dr2 and connective sets non equal to a full orbit. *)
Inductive Derivation {Generators : Connectives}
  : @Structural_Formula _ (C_to_Ss (@full_Connectives Generators)) ->
    @Structural_Formula _ (C_to_Ss (@full_Connectives Generators)) -> Type
  :=
  | LRule (C : @Connective (@full_Connectives Generators))
    :
      forall (X : forall i:'I_(arity C),
          typed_Structural_Formula (tnth (type_input C) i)),
      forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type_input C) i)),
      (forall i:'I_(arity C),
          unsigned_function (tnth (sign_input C) i + (quantification C))%R
            Derivation
            (existT _ (tnth (type_input C) i) (X i))
            (existT _ (tnth (type_input C) i) (from_formula (φ i)))) ->
      unsigned_pivoted_function_S Derivation (C_to_S C)
        X
        (existT _ (type_output C) (from_formula (composition C φ)))
  | RRule (C : @Connective (@full_Connectives Generators))
    :
      forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type_input C) i)),
      forall U : Structural_Formula,
      unsigned_pivoted_function_S Derivation (C_to_S C)
        (fun i => from_formula (φ i)) U ->
      unsigned_pivoted_function_C Derivation C φ U
  | dr1 (C : @Connective (@full_Connectives Generators)) (p : 'S_(arity C).+1)
    :
      forall (X : forall i:'I_(arity C),
          typed_Structural_Formula (tnth (type_input C) i)),
      forall U : Structural_Formula,
      unsigned_pivoted_function_S Derivation (C_to_S C)
.
