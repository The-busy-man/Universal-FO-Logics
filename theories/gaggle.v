From mathcomp Require Import all_ssreflect ssralg all_fingroup zmodp finmap.
Require Import Logic.Eqdep_dec.

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

(*
   Two possible alternatives are mathcomp's lists, which are almost the same
   but have the lemmas proved, or ('I_n -> nat) -> ('I_n -> ±)
*)

(* S'ha de millorar moltíssim el tipus inductiu, pot fer molt pesat treballar-hi.
   Cal manera de fàcil accès a cada posició.
   Millor fes servir les de mathcomp.
   Estan a ssreflect.tuple
 *)
(* Pensar a fer una tupla dependent. *)

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

(* Alternatives are, using Inductive Types or simply a tuple *)
(* canviar type per type_output. *)
Class Atomic_Skeleton := {
    sk_arity : ℕ;
    sk_permutation : 'S_sk_arity.+1;
    sk_sign : ±;
    sk_quantification : Æ;
    sk_type_output : ℕ;
    sk_type_input : sk_arity.-tuple ℕ;
    sk_sign_input : sk_arity.-tuple ±
}.

(*
   Pensar una bona manera d'escriure les lletres desde els esquelets en general.
   Millor fer-ho com ell en l'article, per a sigmplificar, i una coercion.
*)

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
Coercion list_of_cycle {T : eqType} (c : cycle T) := let: Cycle l _ := c in l.

Open Scope eq_scope.

Lemma vrefl {T} (P : pred T) : forall x, P x -> x = x. by[].
Qed.
Definition vrefl_rect {T} (P : pred T) := vrefl P.
Canonical cycle_subType {T : eqType} := [subType for (@list_of_cycle T)].
Definition cycle_eqMixin {T : eqType} := Eval hnf in [eqMixin of cycle T by <:].
Canonical cycle_eqType {T : eqType} := Eval hnf in EqType (cycle T) cycle_eqMixin.

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
  if (x\in (list_of_cycle c)) then Some (rot_cycle (index x c) c)
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
    all (fun l => length (list_of_cycle l) >= 2) cs.
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

Lemma head_cycle_mem {T : finType} (c d : cycle T) (x : T) : (head_cycle c x) = Some d -> (x \in (list_of_cycle d)).
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

(* Necessito aprendre a tractar proves opaques. *)

(* We need to convert into 'S_n the cycles not containing n. *)
Lemma unlift_seq {n} (l : seq (ordinal_eqType n.+1)) : size l > 0 -> ord_max \notin l -> {s : seq (ordinal_eqType n) | l = map (lift ord_max) s & map (unlift ord_max) l = map Some s}.
Proof.
  elim: l => [//|a l IHl] /=; intros.
  move: H0. rewrite in_cons negb_or => /andP [Hneqa H0].
  move: (unlift_some Hneqa) => /= [j _ _].
  case: l H IHl H0 => [| b l]; intros.
Admitted.
  (*
    exact: [::j].
  rewrite /= ltnS in IHl.
  move: IHl => /(_ (leq0n _))/(_ H0) IHl.
  apply (cons j) in IHl.
  exact: IHl.
Qed.*)
Definition unlift_cycle {n} (c : cycle (ordinal_eqType n.+1)) : size c > 0 -> ord_max \notin (list_of_cycle c) -> {d : cycle (ordinal_eqType n) | list_of_cycle c = map (lift ord_max) (list_of_cycle d) & map (unlift ord_max) (list_of_cycle c) = map Some (list_of_cycle d)}.
Proof.
  case: c => [l Hl].
Admitted.
(*
  elim: l => [//|a l IHl] /=; intros.
  move: H0. rewrite in_cons negb_or => /andP [Hneqa H0].
  move: (unlift_some Hneqa) => /= [j _ _].
  case: l H IHl H0 => [| b l]; intros.
    exact: [::j].
  rewrite /= ltnS in IHl.
  move: IHl => /(_ (leq0n _))/(_ H0) IHl.
  apply (cons j) in IHl.
  exact: IHl.
Qed.*)
Definition unlift_seq_cycle {n} (cs : seq (cycle (ordinal_eqType n.+1))) :
  all (fun c => size (list_of_cycle c) > 0) cs ->
  all (fun c => ord_max \notin (list_of_cycle c)) cs ->
  {ds : seq (cycle (ordinal_eqType n)) | all2 (fun c d => list_of_cycle c == map (lift ord_max) (list_of_cycle d)) cs ds & all2 (fun c d => map (unlift ord_max) (list_of_cycle c) == map Some (list_of_cycle d)) cs ds}.
Admitted.

Definition sk_Residuation (C : Atomic_Skeleton) (p : 'S_(sk_arity).+1) : Atomic_Skeleton.
Proof.
  set n := sk_arity.
  move: (prod_cpermP p) => [cs Hprod Hdis Huniq Hlen].
  remember (head_cycle_list cs (ord_max)) as Ods.
  case: Ods HeqOds => [ds |]; intros.
    case: cs Hprod Hdis Hlen Huniq HeqOds => [//|c cs] /=; intros.
    remember (head_cycle c (ord_max)) as Oc.
    case: Oc HeqOds HeqOc => [d| //]; intros.
    move: d HeqOds HeqOc => [l Hl].
    case: l Hl => [//| xn]; case => [//| a]; intros.
    assert (H1: all (fun c0 : cycle (ordinal_eqType sk_arity.+1) => 0 < size c0) cs).
      intros.
    move: (unlift_seq_cycle cs). => [cs _ _].
    remember (map (map (unlift ord_max)) (map list_of_cycle cs)) as cs'.
    
    assert (Haord : a != ord_max).
      move: (head_cycle_head _ _ _ a HeqOc) => /=.
      move: (Hl) => /= /andP [Hxn /andP [Ha Huql]].
      move: Hxn. rewrite in_cons negb_or => /andP [/negbTE Hneqan Hxn] Heqxn.
      rewrite Heqxn in Hneqan.
      apply/negP => /eqP H.
      by rewrite H /= eq_refl in Hneqan.
    move: (unlift_some Haord) => /= [a' _ _].
    move: (sk_Permute C (\prod_(c0 <- cs) (cperm ds))%g) => D.

    apply: sk_partial_Residuation (sk_Permute) a'.
    case: l Hl Hprod Hlen Hdis Huniq HeqOds HeqOc => [//| a l] /=; intros.
  case Opds: (head_cycle_list cs n).
  :=
  let: n := sk_arity in
  let: Cycle_list cs Hprod Hdis := (prod_cpermP p) in
  match (head_cycle_list cs n) with
  | None => ?
  | Some ds =>
      match ds with
      | [::] => False_ind
                 sk_partial_Residuation
  end.

(* Cal Residuació tb sobre connectius. *)



Lemma dmap_feq {T T' : Type}
  (f : ℕ -> T -> T') (g : ℕ -> T -> T') {n} (t : tuple n) :
  (forall n x, f n x = g n x) -> dmap f t = dmap g t.
Proof.
  elim: t f g; simpl; intros.
    reflexivity.
  f_equal.
  exact: H0.
  exact: H.
Qed.

Lemma dmap_comp {T T' T'' : Type}
  (f : ℕ -> T -> T') (g : ℕ -> T' -> T'') {n} (t : tuple n) :
  dmap g (dmap f t) = dmap (fun n x => g n (f n x)) t.
Proof.
  elim: t f g; intros.
    reflexivity.
  simpl. f_equal.
  exact: H.
Qed.

Lemma dmap_id {T : Type} {n} (t : @tuple T n) : dmap (fun _ x => x) t = t.
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
