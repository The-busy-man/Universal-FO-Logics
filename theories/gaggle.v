From mathcomp Require Import all_ssreflect ssralg all_fingroup zmodp perm.
From HB Require Import structures.
Require Import Logic.Eqdep_dec.
Import EqNotations.
From Coq Require Import Lia.

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
Definition bool_to_sign (b : bool) : Z2 :=
  if b then @Ordinal 2 0 (eq_refl _) else @Ordinal 2 1 (eq_refl _).
Coercion bool_to_sign : bool >-> Z2.

Goal (∃ + ∃ = ∀)%R. exact: char_Zp. Qed.
Goal (∃ + ⊹ = ─)%R.
by[]. Qed.
Goal (⊹ + ─ = ─)%R.
by[]. Qed.
Goal (⊹ + ⊹ = ∀)%R.
by rewrite GRing.add0r. Qed.

Inductive pos := Pos n of (0 < n).

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
Definition sign_output {A} (C : Connective) := @sk_sign_output (@skeleton A C).
Definition sign_input {A} (C : Connective) := @sk_sign_input (@skeleton A C).
Definition quantification {A} (C : Connective) := @sk_quantification (@skeleton A C).
Definition type {A} (C : Connective) := @sk_type (@skeleton A C).
Definition type_output {A} (C : Connective) := @sk_type_output (@skeleton A C).
Definition type_input {A} (C : Connective) := @sk_type_input (@skeleton A C).
Section Of_type.

Variable k : pos.
Class typed_Connective {A : Connectives} := {
    ct : @Connective A;
    eq_type : @sk_type_output (skeleton) = k
}.
End Of_type.

Module Letter.
Class Atomic_Skeleton := {
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type_output : pos;
}.
Definition to_atomic_skeleton (P : Atomic_Skeleton) :=
  match P with
    {| sk_sign := s; sk_quantification := q; sk_type_output := t |} =>
      gaggle.Build_Atomic_Skeleton (1)%g  (@Tuple _ _ [::s] (eq_refl _)) q (@Tuple _ _ [::t] (eq_refl _))
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

Inductive typed_Formula {A : Connectives} : pos -> Type :=
  | composition :
      forall (C : @Connective A),
      (forall i : 'I_(@arity A C), typed_Formula (tnth (type C) (lift ord_max i))) ->
      typed_Formula (tnth (type C) ord_max)
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
      sk_sign := s;
      sk_quantification := q;
      sk_type := t;
    |} =>
      ({|
          sk_arity := n0;
          sk_permutation := σ;
          sk_sign := map_tuple (fun x => ─ + x) s;
          sk_quantification := ─ + q;
          sk_type := t;
        |})%R
  end.

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
(* Cal convertir-ho en una acció *)

Definition and_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := 1;
    sk_sign := @Tuple 3 _ [:: ⊹; ⊹; ⊹]%R (eq_refl _);
    sk_quantification := ∃;
    sk_type := @Tuple 3 _ [:: (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _))] (eq_refl _);
  |}.
Definition or_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := 1;
    sk_sign := @Tuple 3 _ [:: ─; ─; ─]%R (eq_refl _);
    sk_quantification := ∀;
    sk_type := @Tuple 3 _ [:: (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _))] (eq_refl _);
  |}.
Definition lres_skeleton : Atomic_Skeleton :=
  {|
    sk_arity := 2;
    sk_permutation := tperm (@Ordinal 3 0 (eq_refl _)) (@Ordinal 3 2 (eq_refl _));
    sk_sign := @Tuple 3 _ [:: ⊹; ─; ─]%R (eq_refl _);
    sk_quantification := ∀;
    sk_type := @Tuple 3 _ [:: (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _)); (@Pos 1 (eq_refl _))] (eq_refl _);
  |}.

Definition and_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ => and_skeleton)
  |}.
Definition or_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ => or_skeleton)
  |}.
Definition lres_connective : Connectives :=
  {|
    connective_set := 'I_1;
    assignment :=
      (fun _ => lres_skeleton)
  |}.

Goal @assignment (Boolean_Action and_connective) (@signed (@connective_set and_connective) ⊹ 0%R) = @assignment and_connective 0%R.
Proof. by[]. Qed.
(* Cal pensar una manera general per a que portar les proves decidibles no es fagi carregos. *)
Goal @assignment (Boolean_Action and_connective) (@signed (@connective_set and_connective) ─ 0%R) = @assignment or_connective 0%R.
Proof.
  rewrite /=/and_skeleton/or_skeleton/=.
  f_equal.
    apply eq_from_tnth => x.
    rewrite tnth_map.
    case: x. do 3 (try case) => //.
  by rewrite -GRing.mulrnDr char_Zp.
Qed.

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

Definition unlift_seq {n} (cs : seq 'I_n) (x : 'I_n) :=
  map (unlift x) cs.

Lemma unlift_some_seq {n} (c : seq 'I_n) (x : 'I_n) :
  x\notin c ->
    {d : seq 'I_n.-1 |
        c = map (lift x) d & map (unlift x) c = map Some d}.
Proof.
  elim: c => /= [_| a l IHl Hx].
    exact: (exist2 _ _ [::]).
  move: Hx. rewrite in_cons negb_or => /andP [/unlift_some Hx /IHl IHlx].
  apply (exist2 _ _ ((proj1_sig Hx) :: (proj1_sig IHlx))) => /=.
    f_equal. exact: (proj2_sig Hx).1. exact: (proj2_sig IHlx).1.
  f_equal. exact: (proj2_sig Hx).2. exact: (proj2_sig IHlx).2.
Qed.

Lemma unlift_some_seq_seq {n} (cs : seq (seq 'I_n)) (x : 'I_n) :
  all (fun c => x\notin c) cs ->
    {cs' : seq (seq 'I_n.-1) |
        cs = map (map (lift x)) cs' & map (map (unlift x)) cs = map (map Some) cs'}.
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

Definition unlift_perm_fun {n} i j (s : 'Sym_n) k :=
  if k is Some k'
  then unlift j (s (lift i k'))
  else unlift j (s i).

Definition perm_inj2 {T : finType} {s : {perm2 T}} := @perm_inj T s.
Hint Resolve perm_inj2 : core.

Lemma unlift_perm_fun_inj {n} i j (s : 'Sym_n) : injective (unlift_perm_fun i j s).
Proof.
  rewrite /unlift_perm_fun => x y.
  case: x => [x|]; case: y => [y| //];
    first (move /unlift_inj/perm_inj/lift_inj => -> //=);
  move/unlift_inj/perm_inj/eqP; by rewrite ?lift_eqF // eq_sym lift_eqF.
Qed.

Definition unlift_perm {n} i j (s : 'Sym_n) :=
  perm (unlift_perm_fun_inj i j s).

Definition option_perm_fun {T : finType} (p : {perm T}) k :=
  if k is Some k'
  then Some (p k')
  else None.

Definition option_perm_fun_inj {T : finType} (p : {perm T}) :
  injective (option_perm_fun p).
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

Lemma option_some_proof {T U : Type} (f : option T -> option U)
  (f_wd : forall x : option T, x -> f x) x : ~ (f (Some x) = None).
Proof.
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
    end) (erefl _).

Definition option_match_some_rw {A P vSome vNone o} {x:A} (H:Some x = o)
  : match o return P o with None => vNone | Some y => vSome y end  = rew [P] H in vSome x
  := match H with erefl => erefl end.

Definition option_match_none_rw {A P vSome vNone} {o : option A} (H:None = o)
  : match o return P o with None => vNone | Some y => vSome y end  = rew [P] H in vNone
  := match H with erefl => erefl end.

Definition constant_rw T P (x y:T) (H:x=y) B b
  : rew [fun z => P z -> B] H in (fun _ => b) = fun _ => b
  := match H with erefl => erefl end.

Lemma option_some_wf {T U : Type} (f : option T -> option U) (f_wd : forall x : option T, x -> f x) x : f (Some x) = Some (option_some f f_wd x).
Proof.
  case Heq: (f (Some x)) => [a|].
    rewrite /option_some (option_match_some_rw (esym Heq)).
    by rewrite constant_rw.
  by apply option_some_proof in Heq.
Qed.

Lemma option_some_finj {T : Type} (f : option T -> option T) (f_wd : forall x : option T, x -> f x) (f_inj : injective f) : injective (option_some f f_wd).
Proof.
  move => x y.
  case Heqx : (f (Some x)) => [a|]; case Heqy : (f (Some y)) => [b|].
  - rewrite /option_some.
    rewrite (option_match_some_rw (esym Heqx)).
    rewrite (option_match_some_rw (esym Heqy)).
    rewrite !constant_rw => Heqab.
    rewrite Heqab -Heqy in Heqx.
    move: Heqx => /f_inj Heqx.
    exact: (Some_inj Heqx).
  - move: (f_wd (Some y) (eq_refl true)).
    by rewrite Heqy.
  - move: (f_wd (Some x) (eq_refl true)).
    by rewrite Heqx.
  rewrite -Heqy in Heqx.
  move: Heqx => /f_inj Heqx.
  by apply Some_inj in Heqx.
Qed.

Lemma unlift_perm_unlift [n : ℕ] (i j : 'I_n) (s : 'Sym_n) (k : 'I_n):
  unlift_perm i j s (unlift i k) = unlift j (s k).
Proof.
  rewrite permE/unlift_perm_fun.
  case: (@eqP _ i k) => [-> | /eqP nHeq].
    by rewrite unlift_none.
  move: (unlift_some nHeq) => [k' Hunit Hcounit].
  by rewrite Hcounit -Hunit.
Qed.

Lemma unlift_some_perm {n} (i j : 'I_n.+1) (s : 'Sym_n.+1) :
  (s i = j) -> {p : 'Sym_n | s = lift_perm i j p & unlift_perm i j s = option_perm p}.
Proof.
  move => H.
  assert (unlift_wd : forall (x : option 'I_n), x -> (unlift_perm i j s x)).
    move => x. rewrite /unlift_perm permE/unlift_perm_fun.
    case: x => [x|//] Hx.
    rewrite -H -(unlift_inj_iff perm_inj).
    by rewrite (proj2_sig (unlift_some (neq_lift i x))).2.
  apply (exist2 _ _ (perm (option_some_finj unlift_wd perm_inj))).
    rewrite -permP => x.
    rewrite permE/lift_perm_fun.
    case: (@eqP _ i x) => Heq.
      by rewrite -Heq unlift_none.
    move: Heq => /eqP Heq.
    move: (unlift_some Heq) => [k Hunit Hcounit].
    rewrite Hcounit permE Hunit -{1}H.
    case Hsome: (unlift_perm i j s (Some k)) => [a|].
      rewrite /option_some.
      rewrite (option_match_some_rw (esym Hsome)) constant_rw.
      rewrite -Hcounit unlift_perm_unlift Hunit -H in Hsome.
      rewrite Hunit in Heq.
      move: Heq => /eqP/(contra_not (@perm_inj _ s _ _))/eqP.
      move /(unlift_some) => /= [k' Hunit' Hcounit'].
      rewrite Hunit'. rewrite Hsome in Hcounit'.
      by rewrite (Some_inj Hcounit').
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
      rewrite (option_match_some_rw (esym Hsome)).
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

(* Em cal canviar el producte del grup de permutacions per la seva versió commutativa.
    Hauria de fer un {perm T} que fagi servir comp en comptes de perm_mul.
 *)
(* versió inductiva tb? *)

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
           then ─ + s + tnth sk_sign (((tperm ord_max (p ord_max) : 'Sym_sk_arity.+1) * p)%g j)
           else s | j < sk_arity.+1]
      else [tuple tnth sk_sign (p i) | i < sk_arity.+1];
    sk_quantification :=
      if (i != n) then
        ─ + s + sk_quantification
      else sk_quantification;
    sk_type :=
      [tuple tnth sk_type (p i) | i < sk_arity.+1]
  |}%R.


Section Of_arity.
Variable n : nat.

Class ary_Skeleton := {
    sa : @Atomic_Skeleton;
    eqs_arity : n == sk_arity
  }.
Class ary_Connective {A : Connectives} := {
    ca : @Connective A;
    eqc_arity : n == @sk_arity skeleton
}.
Coercion ca : ary_Connective >-> Connective.
Coercion sa : ary_Skeleton >-> Atomic_Skeleton.

Definition ska_Residuation
  (C : ary_Skeleton) (s : 'Sym_n.+1) :=
  {| sa := sk_Residuation C (cast_perm (f_equal S (eqP eqs_arity)) s);
    eqs_arity := eqs_arity
  |}.
End Of_arity.

HB.instance Definition _ {n : nat} := [isSub of (ary_Skeleton n) for @sa n].
HB.instance Definition _ {A : Connectives} {n : nat} := [isSub of (ary_Connective n) for @ca n A].

(* Total action should be defined over all permutations of natural numbers, which is problematic as we have been using properties of finite types.
   For the moment we might work with sets of connectives of bounded height.
   Furthermore, this will also imply that our Atomic_Skeletons will be finite.
   Our first approach will be reducing all skeletons to be of fixed arity.
 *)

Definition cast_ary_sk {m} {n} (eq_mn : m = n) (C : ary_Skeleton m) :=
  let: erefl in _ = n := eq_mn return ary_Skeleton n in C.

Lemma sa_inj {n} : injective (@sa n).
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.

Lemma ca_inj {A} {n} : injective (@ca A n).
Proof.
  move => x y H.
  apply val_inj.
  exact: H.
Qed.

Goal
  (sk_Residuation and_skeleton
  (tperm (@Ordinal 3 0 (eq_refl _)) (@Ordinal 3 2 (eq_refl _))))
  = lres_skeleton.
Admitted.

(*
  rewrite /sk_Residuation/and_skeleton/lres_skeleton /=.
  f_equal.
  - by rewrite /sk_permutation mul1g.
  - apply eq_from_tnth => x.
    rewrite !permE /= !tnth_map.
    rewrite tnth_ord_tuple /=.
    case: x.
    (case; try case; try case) => //= Hproof.
      by rewrite /ord_max !permE /=.
    rewrite /ord_max !permE /=.
    rewrite !(tnth_nth (@Ordinal 2 0 (eq_refl _))) !permE /=.
    by rewrite !GRing.addr0.
  - have <-: (ord_max = @Ordinal 3 2 (eq_refl _)). exact: ord_inj.
    have <-: (ord_max = @Ordinal 3 2 Hproof). exact: ord_inj.
    rewrite !permE /= !tpermL /= !(tnth_nth (@Ordinal 2 0 (eq_refl _))) /=.
    by rewrite !GRing.addr0.
  - have <-: (ord_max = @Ordinal 3 2 (eq_refl _)). exact: ord_inj.
    rewrite !permE /= !(tnth_nth (@Ordinal 2 0 (eq_refl _))) /=.
    by rewrite GRing.addr0 -GRing.mulrnDr char_Zp.
  apply eq_from_tnth => x.
  rewrite tnth_map.
  case: x. (case; try case; try case) => //= Hproof;
    rewrite tnth_ord_tuple ?(tnth_nth 0) ?(tnth_nth (@Pos 1 (eq_refl _))) /=.
  - have ->: (Ordinal Hproof = @Ordinal 3 0 (eq_refl _)). exact: ord_inj.
    by rewrite tpermL.
  - have ->: (Ordinal Hproof = @Ordinal 3 1 (eq_refl _)). exact: ord_inj.
    by rewrite tpermD.
  have ->: (Ordinal Hproof = @Ordinal 3 2 (eq_refl _)). exact: ord_inj.
  by rewrite tpermR.
Qed.
*)

Lemma char2 (x : Z2) : (x + x = 0)%R.
Proof.
  by rewrite -GRing.mulr2n -GRing.mulr_natr char_Zp // GRing.mulr0.
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
      first (by rewrite /= -mulgA cast_perm_morphM);
      (try (
        apply eq_from_tnth => x;
        rewrite !tnth_map !tnth_ord_tuple));
      last (by rewrite !cast_permE !permE /= cast_ordK))).
  - case H4 : (cast_perm (f_equal succn (eqP Heq)) (p1 * p2) x != ord_max);
      case H5 : (cast_perm (f_equal succn (eqP Heq)) p2 x != ord_max);
        case H6 : (x != ord_max).
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
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
      Focus 1.
      rewrite [(─ + _)%R in RHS]GRing.addrA.
      rewrite [(─ + _)%R in RHS]GRing.addrC.
      rewrite [(_ + (─ + _ + _))%R in RHS]GRing.addrA.
      rewrite [(_ + (─ + _))%R in RHS]GRing.addrC.
      rewrite [(─ + _ + _)%R in RHS]GRing.addrA.
      by rewrite [(─ + _ + _)%R in RHS]GRing.addrA char2 GRing.add0r.
      (* I shoud be able to prove that in general the case x == ord_max is equivalent to the the proof for sk_quantification.
         Re-use it.
       *)
    + rewrite !cast_permE !permE /= in H1 H2 H3 H4 H5.
      repeat (rewrite !cast_permE !permE /= !cast_ordK).

  - rewrite tnth_map. rewrite tnth_ord_tuple. rewrite cast_permE permE /= in H1.
    rewrite compM tpermD; last first.
    - apply/eqP => /perm_inj/esym. apply/eqP. exact: H3.
    - rewrite eq_sym !cast_permE /= cast_ordK. exact: H1.
    rewrite !cast_permE !permE /= cast_ordK H1.
    rewrite !GRing.addrA. rewrite char2 GRing.add0r.
    rewrite -[in RHS]GRing.addrA.
    rewrite [(_ + q)%R in RHS]GRing.addrC.
    rewrite [in RHS]GRing.addrA.
    rewrite [in RHS]GRing.addrC.
    rewrite !GRing.addrA. rewrite char2 GRing.add0r.
    by rewrite [(_ + ─)%R in RHS]GRing.addrC.
  - admit.
  - rewrite cast_permE permE /=.
    rewrite cast_permE /= in H3.
    rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3.
    by rewrite cast_permE.
  - admit.
  - f_equal. f_equal.
    by rewrite tnth_map /= tnth_ord_tuple !cast_permE !permE /= cast_ordK.
  - admit.
  - rewrite !cast_permE permE /= in H1 H2 H3.
    by rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3 H2 eq_refl in H1.
  - admit.
  - rewrite cast_permE permE /= in H1.
    rewrite tnth_map tnth_ord_tuple !cast_permE !permE /= cast_ordK.
    by rewrite H1 eq_refl /= GRing.addrA char2 GRing.add0r.
  - admit.
  - rewrite !cast_permE !permE /= in H1 H2 H3.
    rewrite -[p2 _](cast_ordK (f_equal succn (eqP Heq))) H3 in H1.
    by rewrite H1 eq_refl in H2.
  - admit.
  - rewrite -[in RHS]H2 in H1.
    apply (f_equal (cast_perm (f_equal succn (eqP Heq)) p1^-1)) in H1.
    rewrite !cast_permE /= !cast_ordK in H1 H3.
    rewrite compM !permK cast_ordKV in H1.
    by rewrite H1 eq_refl in H3.
  - admit.
Admitted.

(*
  - case H4 : (x != cast_perm (f_equal succn (eqP Heq)) (p1 * p2) ord_max);
      case H5 : (x != cast_perm (f_equal succn (eqP Heq)) p2 ord_max);
        case H6 : (
                    cast_perm (f_equal succn (eqP Heq)) p2 ord_max
                      != cast_perm (f_equal succn (eqP Heq)) p1 ord_max);
      case H7 : (x != ord_max).
    + rewrite !permE /=. rewrite !tpermD. rewrite cast_permE permE /=.
    have -> : tperm ord_max (cast_perm (f_equal succn (eqP Heq)) p2 ord_max)
       (cast_perm (f_equal succn (eqP Heq)) p2 x) != cast_perm (f_equal succn (eqP Heq)) p1 ord_max.
    apply/eqP=>/(f_equal (tperm ord_max (cast_perm (f_equal succn (eqP Heq)) p2 ord_max))).
    rewrite tpermK. tpermD.
    - move /(f_equal ). move/(perm_inj). => /eqP.
    case H7 : ((cast_perm (f_equal succn (eqP Heq)) p2 *
      tperm ord_max (cast_perm (f_equal succn (eqP Heq)) p2 ord_max))%g x
     != cast_perm (f_equal succn (eqP Heq)) p1 ord_max).
      case H4 : (x != cast_perm (f_equal succn (eqP Heq)) (p1 * p2) ord_max).
      rewrite !cast_permE !permE /=.
      rewrite  cast_ordKV.
  - admit.
      by rewrite cast_permE permE /= cast_ordKV tnth_ord_tuple.
  f_equal.
  - simpl.
    rewrite cast_permE permE /=.
    admit.
  - simpl.
    rewrite cast_permE permE /=.
    admit.
  apply eq_from_tnth => x.
  rewrite !tnth_map /sk_type.
  f_equal.
  rewrite !cast_permE permE /=.
  f_equal.*)
Admitted.

Definition sk_α {n} := Action (sk_α_is_action (n:=n)).

Lemma ska_Residuation_arity_invariant (C : Atomic_Skeleton) (p : 'Sym_sk_arity.+1) : @sk_arity C = @sk_arity ((ska_Residuation _ {| sa:= C; eqs_arity := eq_refl _|} p)).
Proof.
  rewrite /ska_Residuation /=.
  by case: (unlift ord_max (p ord_max)).
Qed.

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
Definition C_of_Ss {A} (S : @Structures A) := A.
Definition S_of_Cs (C : @Connectives) := @Build_Structures C.
Definition C_of_S {A : Connectives} {B} (S : @Structure _ B) : @Connective (C_of_Ss B) :=
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
Inductive typed_Structural_Formula {A : Connectives} {S : Structures} : ℕ -> Type :=
  | from_formula {k} : @typed_Formula A k -> typed_Structural_Formula k
  | structural_composition
    : forall C : Structure,
      (forall i : 'I_(@sk_arity (@structure_skeleton _ _ C)),
          typed_Structural_Formula
            (tnth (@sk_type (@structure_skeleton _ _ C)) (lift ord_max i))) ->
      typed_Structural_Formula (tnth (@sk_type (@structure_skeleton _ _ C)) ord_max).
Definition Structural_Formula {A : Connectives} {S : Structures} := sigT typed_Structural_Formula.

Definition orbit_of_skeleton (C : Atomic_Skeleton) : Connectives :=
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

(* Record sig_Class {A : Type} {B : A -> Type} := *)
(*   { *)
(*     sig_fst : A; *)
(*     sig_snd : B sig_fst *)
(*   }. *)

(* Each connective from Generators creates a full independent orbit of connectives. *)
Definition full_Connectives (Generators : Connectives) :=
  {|
    connective_set := @sigT (@Connective Generators) (fun C => 'Sym_sk_arity.+1);
    assignment :=
      fun Cp =>
                (sk_α {| sa:= skeleton; eqs_arity := eq_refl _|} (@projT2 _ _ Cp))
  |}.

Definition generator {Generators : Connectives} (C : @Connective Generators)
  : @Connective (full_Connectives Generators) :=
  {|
    var :=
       (existT _ C
       (1%g : 'Sym_(arity C).+1))
      : @connective_set (full_Connectives Generators)
  |}.

Notation sig_fst := projT1.
Notation sig_snd := projT2.

(* change connective_set to a subtype of the other connective_set.
    I need to somehow store the original connective in its individual orbit.
 *)

Class Singleton (T : Type) (a : T) : Type :=
  {
    element := a
  }.

Lemma Singleton_contractible {T : Type} (a : T) (h1 h2 : Singleton T a) : h1 = h2.
Proof.
  by case: h2; case: h1.
Qed.

Lemma Singleton_eq {T : Type} (a : T) (h : Singleton T a) : (@element _ _ h) = a.
Proof.
  by case: h.
Qed.

Definition arity_full {Generators : Connectives} (C : @Connective (full_Connectives Generators)) :
  arity (@sig_fst _ _ (@var _ C)) = arity C.
Proof.
  by[].
Qed.

(* Fes atenció pq la segona component de connective_set depen directament de la variable C, no de la primera component. *)
Definition restricted_orbit {Generators : Connectives}
  (C : @Connective (full_Connectives Generators)) : Connectives :=
  {|
    connective_set :=
      @sig (Singleton (@Connective Generators) (@sig_fst _ _ (@var _ C))) (fun C => 'Sym_(arity (@element _  _ C)).+1);
    assignment :=
      fun Cp => let: C' := @sig_fst _ _ Cp in let: p := @sig_snd _ _ Cp in
                (sk_α {| sa:= (@skeleton _ (@sig_fst _ _ (@var _ C))); eqs_arity := eq_refl _ |} p)
  |}.

Definition restricted_of_full_C {Generators : Connectives}
  (C : @Connective (full_Connectives Generators)) : @Connective (restricted_orbit C) :=
  {|
    var :=
      {|
        sig_fst := (Build_Singleton _ (@sig_fst _ _ (@var _ C)));
        sig_snd := (@sig_snd _ _ (@var _ C))
      |} : (@connective_set (restricted_orbit C))
  |}.

Definition full_of_restricted_C {Generators : Connectives}
  (C : @Connective (full_Connectives Generators)) (D : @Connective (restricted_orbit C)) :
  @Connective (full_Connectives Generators) :=
  {|
    var :=
      {|
        sig_fst := (@element _ _ (@sig_fst _ _ (@var _ D)));
        sig_snd := (@sig_snd _ _ (@var _ D))
      |} : (@connective_set (full_Connectives Generators))
  |}.

(*
El problema ve de que són diferents aritats de diferents connectius (per molt que siguin iguals).
 *)

Definition Residuation' {Generators : Connectives}
  (C : @Structure _ (S_of_Cs (full_Connectives Generators)))
  (p : 'Sym_(@sk_arity (@structure_skeleton _ _ C)).+1) :
  @Structure _ (S_of_Cs (full_Connectives Generators)) :=
  {|
    structure_var :=
      {|
        sig_fst := @sig_fst _ _ (@structure_var _ _ C);
        sig_snd := (p * (@sig_snd _ _ (@structure_var _ _ C)))%g
      |} : (@connective_set (full_Connectives Generators))
  |}.

Definition Residuation {Generators : Connectives} (C : @Connective (full_Connectives Generators))
  (D : @Structure _ (S_of_Cs (restricted_orbit C)))
  (p : 'Sym_(@sk_arity (@skeleton _ C)).+1) :
  @Structure _ (S_of_Cs (restricted_orbit C)) :=
  {|
    structure_var :=
      {|
        sig_fst := Build_Singleton _ (@sig_fst _ _ (@var  _ C));
        sig_snd := (p * (@sig_snd _ _ (@structure_var _ _ D)))%g
      |} : (@connective_set (restricted_orbit C))
  |}.

Theorem α_is_action {Generators : Connectives} {C : @Connective (full_Connectives Generators)} :
  is_action [set: 'Sym_(arity C).+1] (Residuation C).
Proof.
  rewrite /Residuation.
  rewrite /is_action; split.
Admitted.

Definition α {Generators : Connectives} {C : @Connective (full_Connectives Generators)} :=
  Action (α_is_action (C:=C)).

Lemma arity_restricted {Generators : Connectives} {C : @Connective (full_Connectives Generators)}
  (D : @Structure _ (S_of_Cs (restricted_orbit C))) : @sk_arity (@structure_skeleton _ _ D) = arity C.
Proof.
  by case: D; case: C => /= [[C s]] [D p].
Qed.

Lemma arity_S_of_C {A : Connectives} {C : Connective} : @sk_arity (@structure_skeleton _ _ (S_of_C C)) = arity C.
Proof.
  by[].
Qed.

Lemma arity_C_of_S {A : Connectives} {B : Structures} {C : Structure} : arity (C_of_S C) =  @sk_arity (@structure_skeleton _ _ C).
Proof.
  by[].
Qed.

Lemma arity_full_of_restricted_C {Generators : Connectives} {C : @Connective (full_Connectives Generators)} D : arity (full_of_restricted_C C D) = arity C.
Proof.
  by case: D; case: C => /= [[C s]] [D p].
Qed.

(*
  Ha insitit en que sembla que estigui havent de donar massa sovint les inferencies.
  CPDT Adam Chlipala.
  Gallinette.
  Structures Canoniques (+) type classes, hierarchy builder (tb fet per Enrico Tassi, pots preguntar-li).
    - declarer des instances sur les classes.
  types dependents => bool
  conditions de bonnes formation.
 *)

(* ATOMIC CALCULUS *)

(* Agafar tota l'òrbita per la negació i la residuació. *)

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
      typed_Structural_Formula (tnth sk_type (lift ord_max i)))
  (U : Structural_Formula)
  :=
  unsigned_function (@sk_sign_output (@structure_skeleton _ _ C)) f
    U (existT _
         (@sk_type_output (@structure_skeleton _ _ C)) (structural_composition C X)).

Definition unsigned_pivoted_function_C
  {A : Connectives} {S : Structures}
  (f : Structural_Formula -> Structural_Formula -> Type) (C : @Connective A)
  (φ : forall i:'I_(arity C),
      typed_Formula (tnth (type C) (lift ord_max i)))
  (U : Structural_Formula)
  :=
  unsigned_function (tnth (sign C) ord_max) f
    U (existT _
         (tnth (type C) ord_max) (from_formula (composition C φ))).

(* Lacks dr2 and connective sets non equal to a full orbit. *)

(* Els errors venen de que cal veure que les aritats son iguals i que els tipos son iguals (ja que les formules depenen de la tupla de tipos) *)

Definition cast_Formula {A : Connectives} {S : Structures} [n m : nat] (eq_mn : m = n) (φ : typed_Structural_Formula m) :=
  let: erefl in _ = n := eq_mn return typed_Structural_Formula n in φ.

Lemma calculus_type_wf (Generators : Connectives)
            (C : @Connective (full_Connectives Generators)) (p : 'Sym_(arity C).+1)
            (i:'I_(@sk_arity
                     (@structure_skeleton _ _
                        (S_of_C (full_of_restricted_C C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p))))))) :
    (tnth (@sk_type (@skeleton _ C))
                       (p (lift ord_max i))) =
      (tnth
         (@sk_type (@structure_skeleton _ _
           (S_of_C (full_of_restricted_C C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p)))))) (lift ord_max i)).
rewrite /arity. move : Generators C p i => [gset gass] [[/= C s]] /= p i.
rewrite !tnth_map.
f_equal.
rewrite  !cast_perm_morphM.
rewrite !tnth_ord_tuple !permE /=.
f_equal. by rewrite cast_permE !cast_ord_id.
Qed.


(* I need to prove an equality for the type of the residuation. *)
Inductive Calculus {Generators : Connectives}
  : @Structural_Formula _ (S_of_Cs (@full_Connectives Generators)) ->
    @Structural_Formula _ (S_of_Cs (@full_Connectives Generators)) -> Type
  :=
  | LRule (C : @Connective (@full_Connectives Generators))
    : forall (X : forall i:'I_(arity C),
          typed_Structural_Formula (tnth (type C) (lift ord_max i))),
      forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type C) (lift ord_max i))),
      (forall i:'I_(arity C),
          unsigned_function
            (tnth (sign C) (lift ord_max i) + (quantification C))%R
            Calculus
            (existT _ (tnth (type C) (lift ord_max i)) (X i))
            (existT _ (tnth (type C) (lift ord_max i)) (from_formula (φ i)))) ->
      unsigned_pivoted_function_S Calculus (S_of_C C)
        X
        (existT _ (tnth (type C) ord_max) (from_formula (composition C φ)))
  | RRule (C : @Connective (@full_Connectives Generators))
    : forall (φ : forall i:'I_(arity C),
          typed_Formula (tnth (type C) (lift ord_max i))),
      forall U : Structural_Formula,
      unsigned_pivoted_function_S Calculus (S_of_C C)
        (fun i => from_formula (φ i)) U ->
      unsigned_pivoted_function_C Calculus C φ U
  | dr1 (C : @Connective (full_Connectives Generators))
      (p : 'Sym_(arity C).+1)
    : forall (X : forall i:'I_(arity C).+1,
          typed_Structural_Formula (tnth (@sk_type (@skeleton _ C)) i)),
      unsigned_pivoted_function_S Calculus
        (S_of_C C)
        (fun i => X (lift ord_max i))
        (existT _ _ (X ord_max)) ->
      unsigned_pivoted_function_S Calculus
        (S_of_C (full_of_restricted_C C (C_of_S (@α _ _ (S_of_C (restricted_of_full_C C)) p))))
        (fun i =>
           cast_Formula (calculus_type_wf _ _ p i)
           ((X (p (lift ord_max i)))))
        (existT _ _ (X (p ord_max))).
