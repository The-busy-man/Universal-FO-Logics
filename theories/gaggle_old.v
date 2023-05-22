From mathcomp Require Import all_ssreflect ssralg all_fingroup zmodp.
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
Definition oneZ2 := (1%:R : 'Z_2)%R.
Definition zeroZ2 := (0 : 'Z_2)%R.
Notation "∃" := oneZ2.
Notation "∀" := zeroZ2.
Notation "─" := oneZ2. (* '\---' with Agda's key-bindings *)
Notation "⊹" := zeroZ2. (* ⊹ '\+ ' with Agda's key-bindings*)
Notation "'Æ'" := 'Z_2.
Notation "±" := 'Z_2.

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
Definition type {A} (C : Connective) := @sk_type_output (@skeleton A C).
Definition type_input {A} (C : Connective) := @sk_type_input (@skeleton A C).

Module Of_type.
Class Connective {A : Connectives} k := {
    var : connective_set;
    skeleton := assignment var;
    eq_type : sk_type_output = k
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

Fixpoint exponential (n : ℕ) (T : Type) :=
  match n with
  | 0 => T
  | n.+1 => (T * exponential n T)%type
  end.

(* Canviar variable per propositional_letter i operation per composition *)
Inductive Formula {A : Connectives} : ℕ -> Type :=
  | variable : forall P : @Letter.Connective A, Formula (type P)
  | operation :
      forall (C : @Connective A),
      (forall i : 'I_(@arity A C), Formula (tnth (type_input C) i)) ->
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
  connective_set := signed connective_set;
  assignment :=
    fun sC : signed connective_set =>
    match sC with
    | @sign _ (@Ordinal _ 0 _) t => assignment t
    | @sign _ (@Ordinal _ _.+1 _) t =>
        Boolean_Negation (assignment t)
    end
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

Goal @assignment (Boolean_Action and_connective) (sign (@connective_set and_connective) ⊹ 0%R) = @assignment and_connective 0%R.
  by[].
Qed.
(* Cal pensar una manera general per a que portar les proves decidibles no es fagi carregos. *)
Goal @assignment (Boolean_Action and_connective) (sign (@connective_set and_connective) ─ 0%R) = @assignment or_connective 0%R.
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

(*
Lemma vrefl {T} (P : pred T) : forall x, P x -> x = x. by[].
Qed.
Definition vrefl_rect {T} (P : pred T) := vrefl P.
Canonical cycle_subType {T : eqType} := [isSub for (@list_of_cycle T)].
Definition cycle_eqMixin {T : eqType} := Eval hnf in [eqMixin of cycle T by <:].
Canonical cycle_eqType {T : eqType} := Eval hnf in EqType (cycle T) cycle_eqMixin.
*)

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

(* Defineix una igualtat per a cicles que consisteixi en fer rotar la llista fins a trobar un primer element igual i després comprovar si són iguals com a llistes *)
Lemma rot_proof {T : finType} n {s : seq T} : uniq s -> uniq (rot n s).
Proof. by rewrite rot_uniq. Qed.

Definition rot_cycle {T : finType} n (c : cycle T) :=
  let: Cycle l H := c in Cycle _ (rot n l) (rot_proof n H).

Definition head_rot {T : finType} (l : seq T) x :=
  if (x\in l) then Some (rot (index x l) l)
  else None.

Definition head_cycle {T : finType} (c : cycle T) x :=
  if (x\in (seq_of_cycle c)) then Some (rot_cycle (index x c) c)
  else None.

Definition rot_eq {T : finType} (c c' : cycle T) :=
  let: Cycle l _ := c in
  let: Cycle l' _ := c' in
  match l, l' with
  | [::], [::] => true
  | [::], _ => false
  | x :: s, _ => match (head_cycle c' x) with
                 | Some d' => let: Cycle s' _ := d' in
                              l == s'
                 | None => false
                 end
  end.

(* Cycles come out of a list as its rotation. *)
Definition cperm {T : finType} (l : cycle T) := perm (cycle_proof l).

Definition eqcyc {T : finType} (l l' : cycle T) (c : cperm l) (c' : cperm l') := rot_eq l l'.

(*
Lemma rot_cperm_id {T : finType} n (c : cycle T) : cperm (rot_cycle n c) = cperm c.
Proof.
  rewrite -permP.
  case: c => [l Hl]. rewrite /cperm.
  apply: (ftrans (permE _)).
  apply: fsym.
  apply: (ftrans (permE _)).
  rewrite /eqfun /fun_of_cycle /= => x.
  elim: l Hl => /= [//| l] Hl.

Lemma eqcycP {T : finType} (l l' : cycle T) : reflect  (eqcyc l l').
  rewrite/Equality.axiom; move => [l1 Hl1] [l2 Hl2].
  elim: l1 Hl1 => [/=| x l1] Hl1.
    case: l2 Hl2 => /= [| y l2] Hl2.
      apply: ReflectT; f_equal. apply: UIP_dec.
      exact: Bool.bool_dec.
    apply: ReflectF; f_equal => nH. injection nH.
    discriminate.
 *)

Definition disjoint {T : finType} (l l' : seq T) := all (fun i => i \notin l') l.

Inductive decomp_cperm {T : finType} (s : {perm T}) :=
  Cycle_list (cs : seq (cycle T)) of
    (s = \prod_(c <- cs) cperm c)%g &
    forall (c c' : cycle T), c \in cs -> c' \in cs -> c != c' -> disjoint c c' &
    uniq cs &
    all (fun l => length (seq_of_cycle l) >= 2) cs.
Coercion list_of_decomp {T : finType} {s : {perm T}} (cs : decomp_cperm s) : seq (cycle T) :=
  let: Cycle_list l _ _ _ _ := cs in l.

(* Demostració per inducció, fent servir prod_tpermP. *)
Theorem prod_cpermP {T : finType} (s : {perm T}) : decomp_cperm s.
Proof.
Admitted.

Theorem uniq_prod_cpermP {T : finType} (s : {perm T}) (cs1 cs2 : decomp_cperm s) :
  perm_eq (map cperm (list_of_decomp cs1)) (map cperm (list_of_decomp cs2)).
Proof.
Admitted.

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

Definition take_cycle {T : eqType} n (c : cycle T) :=
  let: Cycle l Hl := c in
  Cycle _ (take n l) (take_uniq n Hl).

Definition drop_cycle {T : eqType} n (c : cycle T) :=
  let: Cycle l Hl := c in
  Cycle _ (drop n l) (drop_uniq n Hl).

Lemma cperm_head_tperm {T : finType} (c : cycle T) :
  (cperm c = (cperm (drop_cycle 1 c)) * (cperm (take_cycle 2 c)))%g.
Proof.
  rewrite -permP /cperm.
  apply: (ftrans (permE (cycle_proof c))).
  apply: fsym.
  apply: (ftrans (permE _)) => x /=.
  rewrite (permE (cycle_proof (take_cycle 2 c))).
  rewrite (permE (cycle_proof (drop_cycle 1 c))).
  rewrite /fun_of_cycle.
  case: c => [l Hl]. case: l Hl => [//|a l] /= /andP [Ha Hl].
  case: l Ha Hl => [//|b l] /= Ha /andP [Hb Hl].
  move: Ha. rewrite in_cons negb_or => /andP [/negbTE Hneqab Ha].
  rewrite take0 /rot /= -/(rot 1 l) drop0 take0.
  case Heqax: (a == x); case Heqbx: (b == x) => /=.
  - rewrite -(eqP Heqbx) in Heqax. rewrite Heqax in Hneqab. discriminate.
  - case Hx: (x \in l).
      rewrite (eqP Heqax) in Ha. move: Ha => /negP Ha. by[].
    apply negbT in Hx.
    rewrite (nth_default x); first by rewrite Heqax.
    by rewrite size_cat /= addnS ltnS (memNindex Hx) addn0.
  - case: l Ha Hb Hl => /= [| c l] Ha Hb Hl.
      by rewrite Hneqab eq_refl.
    move: Ha. rewrite in_cons negb_or => /andP [/negbTE Hneqac Ha].
    move: Hb. rewrite in_cons negb_or => /andP [/negbTE Hneqbc Hb].
    by rewrite Hneqbc Hneqac.
  case Hx: (x \in l).
    elim: l Ha Hb Hx Hl => /= [| c l IHl] Ha Hb Hx Hl.
      by rewrite Heqax Heqbx.
    move: Ha. rewrite in_cons negb_or => /andP [/negbTE Hneqac Ha].
    move: Hb. rewrite in_cons negb_or => /andP [/negbTE Hneqbc Hb].
    move: Hx. rewrite in_cons => /orP [Heqxc| Hx].
      rewrite eq_sym in Heqxc.
      rewrite nth_cat. rewrite Heqxc.
      case: l Ha Hb Hl IHl => /= [| d l] Ha Hb Hl IHl.
        by rewrite Hneqab eq_refl.
      move: Ha. rewrite in_cons negb_or => /andP [/negbTE Hneqad Ha].
      move: Hb. rewrite in_cons negb_or => /andP [/negbTE Hneqbd Hb].
      by rewrite Hneqad Hneqbd.
    move: Hl => /andP [/negbTE Hc Hl].
    case Heqxc: (c == x).
      rewrite (eqP Heqxc) Hx in Hc. discriminate.
    apply: (IHl Ha Hb Hx Hl).
  apply negbT in Hx.
  rewrite !(nth_default x) //.
  + by rewrite size_cat /= addnS ltnS (memNindex Hx) addn0.
  + by rewrite Heqax Heqbx.
  by rewrite size_cat /= addnS ltnS (memNindex Hx) addn0.
Qed.

(* prens una decomp_cperm, mostres que només pot tenir un cicle contenint n.+1, comproves si existeix amb head_cycle i defineixes l'acció per la residuació sobre la transposició (take 2) que acabem de veure en cas que hi hagi n amb la composició de permutacions de components.*)

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

(*
Goal lift_perm ord_max ord_max (tperm _ (@Ordinal 2 0 _) (@Ordinal 2 1 _)).
*)

Fixpoint head_cycle_list {T : finType} (cs : seq (cycle T)) (x : T) :=
  match cs with
  | [::] => None
  | c :: cs' =>
      match (head_cycle c x) with
      | None =>
          match (head_cycle_list cs' x) with
          | None => None
          | Some ds => Some (c::ds)
          end
      | Some d => Some (cs' ++ [::d])
      end
  end.

Lemma head_cycle_len {T : finType} (c d : cycle T) (x : T) : (head_cycle c x) = Some d -> size d = size c.
Proof.
  rewrite /head_cycle.
  case: c d => [l Hl] [s Hs].
  case Hx: (x \in l) => // Heq.
  injection Heq as Heq.
  by rewrite /= -Heq size_rot.
Qed.

Lemma head_cycle_mem {T : finType} (c d : cycle T) (x : T) : (head_cycle c x) = Some d -> (x \in (seq_of_cycle d)).
Proof.
  rewrite /head_cycle.
  case: c d => [l Hl] [s Hs].
  case Hx: (x \in l) => //= H.
  injection H as Heq.
  by rewrite -Heq mem_rot.
Qed.

Lemma head_cycle_head {T : finType} (c d : cycle T) (x y : T) : Some d = (head_cycle c x) -> head y d = x.
Proof.
  rewrite /head_cycle.
  case: c d => [l Hl] [s Hs].
  case Hx: (x \in l) => //= H.
  injection H as Heq.
  by rewrite Heq /rot drop_index.
Qed.

Definition cons_cycle_proof {T : finType} (x : T) (c : cycle T) : x\notin (seq_of_cycle c) -> uniq (x :: c).
Proof.
  case: c. intros.
  move: (andb_true_intro (conj H i)).
  by rewrite /= -(cons_uniq).
Defined.

Definition cons_cycle {T : finType} (x : T) (c : cycle T) (Hx : x\notin (seq_of_cycle c))
  : cycle T :=
  Cycle _ (x :: c) (cons_cycle_proof x c Hx)
.

Inductive head_cycle_seq {T : finType} (x : T) : (seq (cycle T)) -> (seq (cycle T)) -> Type :=
  | is_head_cycle : forall (y : T)  (c : cycle T) (cs : seq (cycle T)),
      uniq cs ->
      all (fun d => x\notin (seq_of_cycle d)) cs ->
      forall Hy : y\notin (seq_of_cycle c),
      forall Hx : x\notin seq_of_cycle (cons_cycle y c Hy),
      head_cycle_seq x (cs++[::(cons_cycle x (cons_cycle y c Hy) Hx)]) (cs++[::(cons_cycle x  (cons_cycle y c Hy) Hx)])
  | isnot_head_cycle : forall (cs : seq (cycle T)),
      uniq cs ->
      all (fun c => x\notin (seq_of_cycle c)) cs ->
      head_cycle_seq x cs cs
  | rotate_head_cycle : forall (c : cycle T) (cs ds : seq (cycle T)) n,
      head_cycle_seq x (c::cs) (c::ds) -> head_cycle_seq x ((rot_cycle n c)::cs) (c::ds)
  | rotate_cycle : forall (cs cs' ds : seq (cycle T)),
      perm_eq cs cs' -> head_cycle_seq x cs ds -> head_cycle_seq x cs' ds
.

Lemma head_cycle_list_correct {T : finType} (cs : seq (cycle T)) (x : T) (Huniq : uniq cs) :
  head_cycle_seq x cs
    (match head_cycle_list cs x with
     | Some ds => ds
     | None => cs
     end).
Proof.
  elim: cs Huniq => /= [_ | c0 cs0 IHcs0 /andP [Hc0 Huniq0]].
    exact: (isnot_head_cycle _ _ _).
  move: IHcs0 => /(_ Huniq0) IHcs0.
  remember (match head_cycle_list cs0 x with
            | Some ds => ds
            | None => cs0
            end) as ds0.
  elim: IHcs0 Heqds0 Huniq0 Hc0 => /= [y c cs Huniq Hall Hy Hx| cs Huniq Hall| c cs ds n Hcs IHcs| cs cs' ds Hperm Hcs IHcs] Heqds0 Huniq0 Hc0.
  - rewrite /head_cycle.
    case Hxin: (x\in (seq_of_cycle c0)).
Admitted.

Definition uniq_cycle {T : eqType} (c : cycle T) : uniq (seq_of_cycle c) :=
  let: Cycle l Hl := c in Hl.

Lemma map_cycle_proof {T U: eqType} (f : T -> U) (f_inj : injective f) (c : cycle T) : uniq (map f c).
Proof.
  case: c => l Hl.
  by rewrite (map_inj_uniq f_inj).
Qed.

Definition map_cycle {T U: eqType} (f : T -> U) (f_inj : injective f) (c : cycle T)
  := Cycle _ (map f c) (map_cycle_proof f f_inj c).

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

Lemma map_cycle_inj {T U : eqType} (f : T -> U) f_inj : injective (map_cycle f f_inj).
Proof.
  rewrite /map_cycle/injective; case => l Hl; case => s Hs H.
  injection H as H. move: Hl Hs.
  rewrite (inj_map f_inj H) => Hl Hs.
  f_equal.
  exact: (UIP_dec Bool.bool_dec).
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

(*
Lemma unlift_inj_eq {n m} (f : 'I_n -> 'I_m) (f_inj : injective f) x y :
  f (unlift x y) <-> unlift (f x) (f y).
Proof.
  case: (@eqP _ x y) => [-> | nH].
    by rewrite !unlift_none.
  assert (Heq : f x != f y). by apply/eqP => /f_inj.
  split.
    by rewrite (proj2_sig (unlift_some Heq)).2.
  move: nH => /eqP nH.
  by rewrite (proj2_sig (unlift_some nH)).2.
Qed.
*)

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

Definition option_match_none_rw {A P vSome vNone} {o : option A} {x:A} (H:None = o)
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
      rewrite (option_match_some_rw (Logic.eq_sym Hsome)) constant_rw.
      by rewrite permE /= in Hsome.
    rewrite permE/= in Hsome.
    move: (neq_lift i a) => /eqP/(contra_not (@perm_inj _ s _ _))/eqP Heq.
    move: (unlift_some Heq) => [k Hunit Hcounit].
    by rewrite -H Hcounit in Hsome.
  by rewrite H unlift_none.
Qed.

Lemma cycle_in_fix {T : finType} (c : cycle T) (x : T) :
  x \notin (seq_of_cycle c) -> (cperm c) x == x.
Proof.
  rewrite permE/fun_of_cycle /= => /memNindex H.
  by rewrite nth_default // H size_rot.
Qed.

(*
Definition unlift_perm {n} (i j : 'I_n.+1) (s : 'S_n.+1) (max_wd : s (ord_max) = ord_max) : 'S_n.
*)

Lemma nmem_cons_cycle_l {T : finType} x y (c : cycle T) Hy :
  x \notin seq_of_cycle (cons_cycle y c Hy) -> x != y.
Proof.
  case: c Hy => /= [l Hl] Hy.
  by rewrite in_cons negb_or => /andP [Hx _].
Qed.

Lemma nmem_cons_cycle_r {T : finType} x y (c : cycle T) Hy :
  x \notin seq_of_cycle (cons_cycle y c Hy) -> x \notin (seq_of_cycle c).
Proof.
  case: c Hy => /= [l Hl] Hy.
  by rewrite in_cons negb_or => /andP [_ Hx].
Qed.

Lemma all_prod_id {T : finType} (cs : seq (cycle T)) x : all (fun d => (cperm d x == x)) cs -> (\prod_(d <- cs) cperm d)%g x = x.
Proof.
  elim: cs => /= [| a l IHl].
    by rewrite big_nil permE.
  move => /andP [/eqP Hx /IHl Hl].
  by rewrite big_cons permE /= Hx.
Qed.

Lemma all_imp {T : Type} (P Q : T -> bool) l (H : forall n, P n -> Q n) : all P l -> all Q l.
Proof.
  elim: l => /= [//| a l IHl].
  move => /andP [Ha /IHl Hl]. apply/andP.
  split.
    exact: (H _ Ha).
  exact: Hl.
Qed.

(* versió inductiva tb?
*)

(* I used head_cycle_seq inductive type to have an inductive definition carrying the desired properties of our decomposition, it goes along a fixpoint construction called head_cycle_list for cycles of cycles. *)
(* Em torna a donar problemes el rewrite, https://coq.inria.fr/library/Coq.Init.Logic.html
   seccions posteriors a EqNotations.
   La diferència amb l'anterior cas és que ara utilitzem la prova que fa que el patern-matching sigui dependent.
   Has de trovar una manera de substituir constant_rw en el cas en que el rewrite no és constant.
   En general, com reescriure les definicions que portin demostracions?
   Potser necessito un have generalitzat on fer la substitució?
   En el cas en que una prova concreta molesti al dependre d'altres termes puc fer servir generalize.
   Per a igualtats entre igualtats, com som a un eqType podem fer servir eq_irrelevance.
 *)
Definition sk_Residuation
  (C : Atomic_Skeleton) (s : 'S_(sk_arity).+1) : Atomic_Skeleton :=
  let n := sk_arity in
  (if (s ord_max) == ord_max as o
         return (s ord_max == ord_max) = o -> Atomic_Skeleton
   then fun Heq =>
      sk_Permute C
        (proj1_sig (unlift_some_perm _ _ _ (eqP Heq)))
   else fun nHeq =>
      sk_Permute
        (sk_partial_Residuation C
      (* Comprova estar residuant amb la bona coordenada *)
           (proj1_sig (unlift_some (neqP nHeq))))
        (proj1_sig (unlift_some_perm _ _
                      (s * (tperm ord_max (s ord_max)))%g
                      (ord_max_residuate s ord_max)))
  ) (Logic.eq_refl _).

Definition sk_Residuation
  (C : Atomic_Skeleton) (p : 'S_(sk_arity).+1) : Atomic_Skeleton :=
  let: n := sk_arity in
  let: Cycle_list cs0 Hprod Hdis Huniq Hlen := (prod_cpermP p) in
  (fix skRfix cs ds
     (hproof : head_cycle_seq (ord_max) cs ds) :=
  match hproof with
  | is_head_cycle y c cs' Huniq Hnew Hnew2 Hx =>
      sk_Permute
        (sk_Permute
           (sk_partial_Residuation C
              (proj1_sig (unlift_some
                            (nmem_cons_cycle_l _ _ _ _ Hx))))
           (proj1_sig (unlift_some_perm
                         ord_max
                         ord_max
                         (cperm c)
                         (eqP (cycle_in_fix _ _
                                 (nmem_cons_cycle_r _ _ _ _ Hx))))))
        (proj1_sig (unlift_some_perm
                      ord_max
                      ord_max
                      (\prod_(d <- cs') cperm d)%g
                      (all_prod_id _ _
                         (all_imp _ _ cs'
                            (fun d => cycle_in_fix (T:='I_n.+1) d (@ord_max n))
                            Hnew))))
  | isnot_head_cycle cs' Huniq Hnew =>
      sk_Permute C
        (proj1_sig (unlift_some_perm
                      ord_max
                      ord_max
                      (\prod_(d <- cs') cperm d)%g
                      (all_prod_id _ _
                         (all_imp _ _ cs'
                            (fun d => cycle_in_fix (T:='I_n.+1) d (@ord_max n))
                            Hnew))))
  | rotate_head_cycle c cs' ds n Hrot => skRfix _ _ Hrot
  | rotate_cycle cs' cs'' ds Hcs Hrot => skRfix _ _ Hrot
  end
  ) cs0 (let Ods := (head_cycle_list cs0 ord_max) in
     match Ods with
     | Some ds => ds
     | None => cs0
     end) (head_cycle_list_correct cs0 ord_max Huniq).

(* Cal Residuació tb sobre connectius. *)

Lemma involutive_residuation (C : Atomic_Skeleton) (i : 'I_(sk_arity)) :
  sk_Residuation (sk_Residuation C i) i = C.
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

Goal
  assignment
    (Residuation (Build_Connective (and_connective) 0%R) 1%R)
    (@npoint connective_set)
  =
    {|
      sk_arity := 2;
      sk_permutation := tperm (Ordinal (erefl (1 < 3))) (Ordinal (erefl (2 < 3)));
      sk_quantification := ∀;
      sk_sign := ─;
      sk_type_output := 1;
      sk_type_input := cons 1 1%nat (cons 0 1%nat empty);
      sk_sign_input := cons 1 ─ (cons 0 ⊹ empty)
    |}%R.
  rewrite /= /sk_Residuation /=.
  rewrite mulg1.
  rewrite !GRing.addr0.
  rewrite GRing.nat1r char_Zp; last by[].
  repeat f_equal; apply UIP_dec; apply Bool.bool_dec.
Qed.


Definition sk_partial_Residuation (C : Atomic_Skeleton) (i : 'I_(sk_arity)) : Atomic_Skeleton :=
  let s := (tnth sk_sign_input i) in
  let n := (@ord_max sk_arity) in
  let i' := lift n i in
  {|
    sk_arity := sk_arity;
    sk_permutation := (tperm i' n) * sk_permutation;
    sk_sign := (─ + s) + sk_sign;
    sk_quantification := ─ + s + sk_quantification;
    sk_type := [tuple if j == i then else tnth sk_type j | j < n.+1];
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


(* Codi correcte. *)

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

Goal @assignment (Boolean_Action and_connective) (@signed (@connective_set and_connective) ─ 0%R) = @assignment or_connective 0%R.
Proof.
  rewrite /=/and_skeleton/or_skeleton/=.
  f_equal.
    apply eq_from_tnth => x.
    rewrite tnth_map.
    case: x. do 3 (try case) => //.
  by rewrite -GRing.mulrnDr char_Zp.
Qed.

(* PERMUTATIONS. *)

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

Variable φ : {morphism D >-> Aut [set: C]}

Lemma (x y : sdprod_by C D).

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


Lemma sk_Residuation_arity (C : Atomic_Skeleton) (σ : 'Sym_sk_arity.+1) : @sk_arity C == @sk_arity (sk_Residuation C σ).
Proof. by case: C σ. Qed.

Definition ska_Residuation
  (C : ary_Skeleton) (σ : 'Sym_n.+1) : ary_Skeleton :=
  let: {| sa := sa; eqs_arity := eqs |} := C in
  let: σ' := (cast_perm (f_equal succn (eqP eqs)) σ) in
  {|
    sa := sk_Residuation sa σ';
    eqs_arity := (eq_op_trans (eqs) (sk_Residuation_arity sa σ'))
  |}.
