From mathcomp Require Import all_ssreflect ssralg all_fingroup zmodp solvable.cyclic.
Require Import Logic.Eqdep_dec.

Unset Printing Implicit Defensive.

(*                                                                            *)
(*                                                                            *)
(*           FORMALIZING GAGGLES LOGICS' SINTAXIS AND SEMANTICS               *)
(*                                                                            *)
(*                                                                            *)

(* Changing universal quantification utf8 symbols  *)
Notation "'ℕ'" := nat.
Definition oneZ2 := (1%:R : 'Z_2)%R.
Definition zeroZ2 := (0 : 'Z_2)%R.
Notation "∃" := oneZ2.
Notation "∀" := zeroZ2.
Notation "─" := oneZ2. (* '\---' with Agda's key-bindings *)
Notation "⊹" := zeroZ2. (* ⊹ '\+ ' with Agda's key-bindings*)
Notation "'Æ'" := 'Z_2.
Notation "±" := 'Z_2.

Goal (∃ + ∃ = ∀)%R.
by rewrite GRing.natr1;apply char_Zp. Qed.
Goal (∃ + ⊹ = ─)%R.
by[]. Qed.
Goal (⊹ + ─ = ─)%R.
by[]. Qed.
Goal (⊹ + ⊹ = ∀)%R.
by rewrite GRing.add0r. Qed.

(*
   Two possible alternatives are mathcomp's lists, which are almost the same
   but have the lemmas proved, or ('I_n -> nat) -> ('I_n -> ±)
*)

(* S'ha de millorar moltíssim el tipus inductiu, pot fer molt pesat treballar-hi.
   Cal manera de fàcil accès a cada posició.
   Millor fes servir les de mathcomp.
   Estan a ssreflect.tuple
 *)
Inductive tupla {T} : ℕ -> Type :=
  | empty : tupla 0
  | cons n : T -> tupla n -> tupla n.+1
.
(* Pensar a fer una tupla dependent. *)

(* Passar-ho a Fixpoint *)
Definition head_of {T} {n} (L : @tupla T n) (pos : n > 0) : T.
  destruct L. discriminate.
  exact t.
Defined.

(* Millor escriu-ho després com a Fixpoint *)
Definition In {T} {n} (L : @tupla T n) (i : 'I_n) : T.
  elim: L i => [[//]| m t L Hi i].
  case: i => i iord.
  case: i iord => /= [//| i] iord.
  apply ltnSE in iord. apply Hi. exact: Ordinal iord.
Defined.

Fixpoint dmap {T} {n} {T'} (f : ℕ -> T -> T') (t : tupla n) :=
  match t with
  | empty => empty
  | cons n a t' => cons n (f 0 a) (dmap (fun n => (f n.+1)) t')
  end
.

Lemma leqVgtT : forall m n : ℕ, (m <= n) + (n <= m).
Proof.
  elim => [| n IHn m].
    by left.
  case: m => [|m].
    by right.
  case: (IHn m) => [H | H].
    left. exact: H.
  right. exact: H.
Defined.

Lemma leq_eqVltT : forall {m n : ℕ}, (n <= m) -> (n = m) + (n < m).
Proof.
  elim => [| m IHn n nleqm].
    left. rewrite leqn0 in H. exact: (eqP H).
  case: n nleqm; intros.
    by right.
  case: (IHn n nleqm) => H.
    left. by f_equal.
  right. exact: H.
Defined.

Definition revert_ordinal {n} (i : 'I_n) : 'I_n.
Proof.
  move: i => [i ileqn].
  assert (n-i.+1 < n).
    rewrite -{2}(subn0 n).
    apply ltn_sub2l.
      by apply (@leq_ltn_trans i).
    by[].
  exact: (Ordinal H).
Defined.

Goal dmap (fun m n => (m, n^2)) (cons 2 2 (cons 1 1 (cons 0 0 (empty)))) <> dmap (fun m n => (m, n^2)) (cons 2 1 (cons 1 1 (cons 0 1 (empty)))).
  by[]. Qed.

(* Alternatives are, using Inductive Types or simply a tuple *)
Class Atomic_Skeleton := {
    sk_arity : ℕ;
    sk_permutation : 'S_sk_arity.+1;
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type : ℕ;
    sk_type_input : @tupla ℕ sk_arity;
    sk_sign_input : @tupla ± sk_arity
}.

(*
   Pensar una bona manera d'escriure les lletres desde els esquelets en general.
   Millor fer-ho com ell en l'article, per a sigmplificar, i una coercion.
*)

Class Assignment := {
  set : Type;
  connective : (set -> Atomic_Skeleton)
}.

Class Connective {A : Assignment} := {
    var : set;
    skeleton := connective var
}.

Definition arity {A} (C : Connective) := @sk_arity (@skeleton A C).
Definition type {A} (C : Connective) := @sk_type (@skeleton A C).
Definition type_input {A} (C : Connective) := @sk_type_input (@skeleton A C).

Module Of_type.
Class Connective {A : Assignment} k := {
    var : set;
    skeleton := connective var;
    eq_type : sk_type = k
}.
End Of_type.

Module Letter.
Class Atomic_Skeleton := {
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type : ℕ;
}.
Definition to_atomic_skeleton (P : Atomic_Skeleton) :=
  match P with
    {| sk_sign := s; sk_quantification := q; sk_type := t |} =>
      gaggle.Build_Atomic_Skeleton 0 (1) s q t empty empty
  end.
Class Connective {A : Assignment} := {
    var : set;
    skeleton := connective var;
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
Class Connective {A : Assignment} := {
    var : set;
    skeleton := connective var;
    pos : sk_arity > 0
  }.
Definition to_connective {A : Assignment}
  (P : Connective) : gaggle.Connective :=
  match P with
    {| Strict.var := var0; Strict.pos := _ |} =>
      {|
        gaggle.var := var0
      |}
  end.
End Strict.
Coercion Strict.to_connective : Strict.Connective >-> Connective.

Fixpoint exponential (n : ℕ) (T : Type) :=
  match n with
  | 0 => T
  | n.+1 => (T * exponential n T)%type
  end.

Inductive Formula {A : Assignment} : ℕ -> Type :=
  | variable : forall P : @Letter.Connective A, Formula (type P)
  | operation :
      forall (C : @Connective A),
      (forall i : 'I_(@arity A C), Formula (In (type_input C) i)) ->
      Formula (type C)
.

Inductive signed T :=
  | sign : 'Z_2 -> T -> signed T
.

Definition Boolean_Negation (C : Atomic_Skeleton) : Atomic_Skeleton :=
  match C with
  | {|
      sk_arity := n0;
      sk_permutation := σ;
      sk_sign := s_o;
      sk_quantification := q;
      sk_type := t_o;
      sk_type_input := t_i;
      sk_sign_input := s_i
    |} =>
      ({|
          sk_arity := n0;
          sk_permutation := σ;
          sk_sign := ─ + s_o;
          sk_quantification := ─ + q;
          sk_type := t_o;
          sk_type_input := t_i;
          sk_sign_input := dmap (fun _ s => ─ + s) s_i
        |})%R
  end.
(* Cal convertir-ho en una acció sobre els connectius mitjançant mathcomp.fingroup.action *)

Definition Boolean_Action (A : Assignment) : Assignment :=
  {|
  set := signed set;
  connective :=
    fun sC : signed set =>
    match sC with
    | @sign _ (@Ordinal _ 0 _) t => connective t
    | @sign _ (@Ordinal _ _.+1 _) t =>
        Boolean_Negation (connective t)
    end
|}.

Definition and_connective : Assignment :=
  {|
    set := 'I_1;
    connective :=
      (fun _ =>
         {|
           sk_arity := 2;
           sk_permutation := 1;
           sk_sign := ⊹;
           sk_quantification := ∃;
           sk_type := 1;
           sk_type_input := (cons 1 1 (cons 0 1 empty));
           sk_sign_input := (cons 1 ⊹ (cons 0 ⊹ empty))
         |})
  |}.
Definition or_connective : Assignment :=
  {|
    set := 'I_1;
    connective :=
      (fun _ =>
         {|
           sk_arity := 2;
           sk_permutation := 1;
           sk_sign := ─;
           sk_quantification := ∀;
           sk_type := 1;
           sk_type_input := (cons 1 1 (cons 0 1 empty));
           sk_sign_input := (cons 1 ─ (cons 0 ─ empty))
         |})
  |}.

Goal @connective (Boolean_Action and_connective) (sign (@set and_connective) ⊹ 0%R) = @connective and_connective 0%R.
  by[].
Qed.
Goal @connective (Boolean_Action and_connective) (sign (@set and_connective) ─ 0%R) = @connective or_connective 0%R.
  move => /=.
  rewrite GRing.addr0.
  rewrite GRing.natr1.
  rewrite char_Zp; last by[].
  by[].
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
Lemma set_default_index_inj {T : eqType} {l} {x y : T} : x \in l -> y \in l -> index x l = index y l -> x = y.
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

(* Pots demostrar-ho també fent servir:
  apply: (@can_inj _ _ _ (fun z => (nth z (rot (size l).-1 l) (index z l)))).
   D'altre banda, demo molt millorable.
*)
Lemma cycle_proof [T : finType] (l : seq T) : uniq l -> injective [fun z => fun_of_cycle _ l z].
Proof.
  move => Hl x y /=.
  rewrite /fun_of_cycle.
  case xinl: (x\in l); case yinl: (y\in l) => // /eqP.
  - rewrite -(rot_uniq 1) in Hl.
    rewrite (set_nth_default y x) ?(nth_uniq y _ _ Hl) ?size_rot ?index_mem // => /eqP.
    exact (set_default_index_inj xinl yinl).
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
Definition cperm {T : finType} (l : seq T) (Hl : uniq l) := perm (cycle_proof _ Hl).

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

Definition sk_Residuation (C : Atomic_Skeleton) (i : 'I_(sk_arity)) : Atomic_Skeleton :=
  let s := (In sk_sign_input i) in
  let n := Ordinal (leqnn sk_arity.+1) in
  (* Si l'opacitat no et donès problemes, aleshores utilitza lift ord_max *)
  let i' := Ordinal (ltn_trans (ltn_ord i) (leqnn sk_arity.+1)) in
  {|
    sk_arity := sk_arity;
    sk_permutation := (tperm i' n) * sk_permutation;
    sk_sign := ─ + s + sk_sign;
    sk_quantification := ─ + s + sk_quantification;
    sk_type := sk_type;
    sk_type_input := sk_type_input;
    sk_sign_input := dmap (fun n s' => if n == i then s' else ─ + s + s') sk_sign_input
  |}%R
.

Lemma dmap_feq {T T' : Type}
  (f : ℕ -> T -> T') (g : ℕ -> T -> T') {n} (t : tupla n) :
  (forall n x, f n x = g n x) -> dmap f t = dmap g t.
Proof.
  elim: t f g; simpl; intros.
    reflexivity.
  f_equal.
  exact: H0.
  exact: H.
Qed.

Lemma dmap_comp {T T' T'' : Type}
  (f : ℕ -> T -> T') (g : ℕ -> T' -> T'') {n} (t : tupla n) :
  dmap g (dmap f t) = dmap (fun n x => g n (f n x)) t.
Proof.
  elim: t f g; intros.
    reflexivity.
  simpl. f_equal.
  exact: H.
Qed.

Lemma dmap_id {T : Type} {n} (t : @tupla T n) : dmap (fun _ x => x) t = t.
Proof.
  elim: t; intros.
    reflexivity.
  simpl. by rewrite H.
Qed.

Lemma involutive_residuation (C : Atomic_Skeleton) (i : 'I_(sk_arity)) : sk_Residuation (sk_Residuation C i) i = C.
Proof.
  rewrite /sk_Residuation.
  case: C i; simpl; intros.
  assert
    (H : (In (dmap
             (fun (n : ℕ)
                  (s' : 'Z_2) =>
                if n == i then s' else
                  ─ + In (sk_sign_input0) i + s') sk_sign_input0) i = In sk_sign_input0 i)%R).
    elim: sk_sign_input0 i; intros.
      reflexivity.
    case: i; intros;
    case: m i; simpl; intros.
      reflexivity.
    exact: H.
  f_equal.
  - by rewrite mulgA tperm2 mul1g.
  - rewrite H.
    rewrite -[(─ + _)%R](GRing.mulr1n).
    rewrite GRing.addrA -GRing.mulrnDr.
    by rewrite GRing.mulrn_char // GRing.add0r.
  - rewrite H.
    rewrite -[(─ + _)%R](GRing.mulr1n).
    rewrite GRing.addrA -GRing.mulrnDr.
    by rewrite GRing.mulrn_char // GRing.add0r.
  simpl. rewrite H. clear H.
  rewrite dmap_comp. simpl.
  rewrite (dmap_feq _ (fun _ x => x)); intros.
    exact: dmap_id.
  case Heq: (n == i).
    reflexivity.
  rewrite -[(─ + _)%R](GRing.mulr1n).
  rewrite GRing.addrA -GRing.mulrnDr.
  by rewrite GRing.mulrn_char // GRing.add0r.
Qed.

(*
   Demostrar que sk_Residuation és bijectiva i involutiva, demostrar que la composició d'aplicacions forma un grup.
   Agafar el subgrup generat per les sk_Residuation.
   Demostrar que la seva aplicació és ben-definida com a acció sobre els connectius.
   tb tperm_prod i tpermJ_res.
*)

Inductive extend T :=
  | emb : T -> extend T
  | npoint : extend T
.
(* Coercion per a extend.
   Seria còmode poder escollir la variable del nou connectiu.
*)

(* Add the Residuation of C in index i to assignment A.
*)
Definition Residuation {A : Assignment} (C : Connective) (i : 'I_(sk_arity)) :=
  {|
    set := extend set;
    connective :=
      fun sC : extend set =>
        match sC with
        | emb t => connective t
        | npoint => sk_Residuation skeleton i
        end
  |}
.

Goal
  @connective
    (Residuation (Build_Connective (and_connective) 0%R) 1%R)
    (@npoint set)
  =
    {|
      sk_arity := 2;
      sk_permutation := tperm (Ordinal (erefl (1 < 3))) (Ordinal (erefl (2 < 3)));
      sk_quantification := ∀;
      sk_sign := ─;
      sk_type := 1;
      sk_type_input := cons 1 1%nat (cons 0 1%nat empty);
      sk_sign_input := cons 1 ─ (cons 0 ⊹ empty)
    |}%R.
  rewrite /= /sk_Residuation /=.
  rewrite mulg1.
  rewrite !GRing.addr0.
  rewrite GRing.nat1r char_Zp; last by[].
  repeat f_equal; apply UIP_dec; apply Bool.bool_dec.
Qed.

(* Cal expressar-ho de manera que t \in ts estigui accessible en el productori.
   Provaré a definir cperms mitjançant trajects i demostrar això per una seqüència de naturals i les seves porbits/traject (canvi amb porbit_traject).
   eq_porbit_mem.
*)
Lemma cycle_prod [T : finType] (s : {perm T}) : {ts : seq (seq T) | {Ht : all uniq ts | s = (\prod_(t in ts) cperm t (allP Ht t))%g}}.

(* Abans em cal definir les permutations d'una manera apropiada.
   Un altre cop mathcomp té bones solucions:
   tperm són les transposicions, i el lema prod_tpermP dona la descomposició d'una permutació en transposicions.
   Per altre banda, porbit és l'òrbit d'una permutació.
*)
