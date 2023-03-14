From mathcomp Require Import all_ssreflect ssralg zmodp.
Require Import gaggle.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Unset Printing Implicit Defensive.

(*                                                                            *)
(*                                                                            *)
(*           FORMALIZING Lambek Calculus SINTAXIS AND SEMANTICS               *)
(*                                                                            *)
(*                                                                            *)

(* We work only non-associative Lambek Calculus.
   It is shown that its display system corresponds to Lambek's original
   formulation.
   At the end some miscellanea is found for sanity checks.
*)

Inductive lkf :=
  | var : ℕ -> lkf
  | tensor_lkf : lkf -> lkf -> lkf
  | rresidual_lkf : lkf -> lkf -> lkf
  | lresidual_lkf : lkf -> lkf -> lkf
.

Declare Scope lkf_scope.

Notation "a '·' b" := (tensor_lkf a b) (at level 30).
Notation "a '/' b" := (lresidual_lkf a b) (at level 40, left associativity).
Notation "a '\' b" := (rresidual_lkf a b) (at level 50).
Notation "a ∧ b" := (and a b) (at level 80, right associativity).
Notation "a ∨ b" := (or a b) (at level 85, right associativity).


Structure kripke (worlds : eqType) := {
  val : ℕ -> worlds -> Prop;
  rel : worlds -> worlds -> worlds -> Prop
}.

(* Following Dunn's approach, but without the D notation *)
Fixpoint force {W} (M : kripke W) (w : W) (φ : lkf) :=
  let R := rel W M in let V := val W M in
  match φ with
  | var n => V n w
  | φ · ψ => exists (u v : W), R u v w ∧ force M u φ ∧ force M v ψ
  | φ / ψ => forall (u v : W), R w v u -> force M v ψ -> force M u φ
  | φ \ ψ => forall (u v : W), R u w v-> force M u φ -> force M v ψ
  end
.

Declare Scope lkf_scope.
Delimit Scope lkf_scope with lkf.
Notation "M ; s ⊨ φ " :=
  (force M s φ) (at level 60, format "M ; s  ⊨  φ") : lkf_scope.
Print Grammar pattern.
Definition sat φ := forall W (M : kripke W) s, (M;s⊨φ)%lkf.
Notation "⊨ φ" := (sat φ) (at level 60) : lkf_scope.

Definition sat_derivation φ ψ:= (⊨φ->⊨ψ)%lkf.
Notation "φ ⊩ ψ" := (sat_derivation φ ψ) (at level 60).


(*  CALCULI  *)

(* Original Calculi *)
Inductive derivation : lkf -> lkf -> Type :=
  | axiom_id : forall φ : lkf, derivation φ φ
  | res1 : forall φ ψ ρ : lkf, derivation (φ·ψ) ρ -> derivation φ (ρ/ψ)
  | res2 : forall φ ψ ρ : lkf, derivation (φ·ψ) ρ -> derivation ψ (φ\ρ)
  | res3 : forall φ ψ ρ : lkf, derivation φ (ρ/ψ) -> derivation (φ·ψ) ρ
  | res4 : forall φ ψ ρ : lkf, derivation ψ (φ\ρ) -> derivation (φ·ψ) ρ
  | cut_rule : forall φ ψ ρ : lkf, derivation φ ψ -> derivation ψ ρ -> derivation φ ρ
.

Notation "φ ⊢ ψ" := (derivation φ ψ) (at level 60).

Proposition lres_tensor_K φ ψ : (φ/ψ)·ψ⊢φ.
Proof.
  apply res3.
  exact: (axiom_id _).
Qed.

Proposition tensor_lres_K φ ψ : φ⊢φ·ψ/ψ.
Proof.
  apply res1.
  exact: (axiom_id _).
Qed.

Proposition rres_tensor_K φ ψ : φ ⊢ ψ\ψ·φ.
Proof.
  apply res2.
  exact: (axiom_id _).
Qed.

Proposition tensor_rres_K φ ψ : ψ·(ψ\φ)⊢φ.
Proof.
  apply res4.
  exact: (axiom_id _).
Qed.

Lemma tensor_lton_pos φ ψ ρ : φ⊢ψ -> φ·ρ⊢ψ·ρ.
Proof.
  intros; apply res3.
  apply (cut_rule _ ψ). exact: H.
  exact: (tensor_lres_K _ _).
Qed.

Lemma tensor_rton_pos φ ψ ρ : φ⊢ψ -> ρ·φ⊢ρ·ψ.
Proof.
  intros. apply res4.
  apply (cut_rule _ ψ). exact: H.
  exact: (rres_tensor_K _ _).
Qed.

Lemma rres_lton_pos φ ψ ρ : φ⊢ψ -> ρ\φ⊢ρ\ψ.
Proof.
  intros. apply res2.
  apply (cut_rule _ φ).
    exact: (tensor_rres_K _ _).
  exact: H.
Qed.

Lemma lres_rton_pos φ ψ ρ : φ⊢ψ -> φ/ρ⊢ψ/ρ.
Proof.
  intros. apply res1.
  apply (cut_rule _ φ).
    exact: (lres_tensor_K _ _).
  exact: H.
Qed.

Lemma rres_rton_neg φ ψ ρ : φ⊢ψ -> ψ\ρ⊢φ\ρ.
Proof.
  intros. apply res2. apply res3.
  apply (cut_rule _ ψ).
    exact: H.
  apply res1. apply res4. exact: (axiom_id _).
Qed.

Lemma lres_lton_neg φ ψ ρ : φ⊢ψ -> ρ/ψ⊢ρ/φ.
Proof.
  intros. apply res1. apply res4.
  apply (cut_rule _ ψ).
    exact: H.
  apply res2. apply res3. exact: (axiom_id _).
Qed.

Proposition lk_tensorR : forall (φ ψ ρ η : lkf), φ⊢ρ -> ψ⊢η -> φ·ψ⊢ρ·η.
Proof.
  intros.
  apply (cut_rule _ (φ·η)).
    exact: (tensor_rton_pos _ _ _ H0).
  exact: (tensor_lton_pos _ _ _ H).
Qed.

Proposition lk_rresR : forall (φ ψ ρ η : lkf), ρ⊢φ -> ψ⊢η -> φ\ψ⊢ρ\η.
Proof.
  intros.
  apply (cut_rule _ (ρ\ψ)).
    exact: (rres_rton_neg _ _ _ H).
  exact: (rres_lton_pos _ _ _ H0).
 Qed.

Proposition lk_lresR : forall (φ ψ ρ η : lkf), φ⊢ρ -> η⊢ψ -> φ/ψ⊢ρ/η.
Proof.
  intros.
  apply (cut_rule _ (φ/η)).
    exact: (lres_lton_neg _ _ _ H0).
  exact: (lres_rton_pos _ _ _ H).
Qed.



Inductive lks :=
  | formula : lkf -> lks
  | tensor_lks : lks -> lks -> lks
  | rresidual_lks : lks -> lks -> lks
  | lresidual_lks : lks -> lks -> lks
.
Coercion formula : lkf >-> lks.

Notation "''' φ" := (formula φ) (at level 0).
Notation "φ [·] ψ" := (tensor_lks φ ψ) (at level 30).
Notation "φ [\] ψ" := (rresidual_lks φ ψ) (at level 40).
Notation "φ [/] ψ" := (lresidual_lks φ ψ) (at level 50).

Definition is_formula X :=
  match X with
  | 'φ => true
  | _ => false
  end
.

(* Goré's 1998 article Lambek Calculi *)
Inductive display_derivation : lks -> lks -> Type :=
  | display_id : forall (φ : lkf), display_derivation φ φ
  | display1 : forall X Y Z,
      display_derivation X (Z [/] Y) -> display_derivation (X [·] Y) Z
  | display2 : forall X Y Z,
      display_derivation (X [·] Y) Z -> display_derivation Y (X [\] Z)
  | display3 : forall X Y Z,
      display_derivation Y (X [\] Z) -> display_derivation X (Z [/] Y)
  | tensorL : forall X (φ ψ : lkf),
      display_derivation (φ [·] ψ) X -> display_derivation (φ·ψ) X
  | tensorR : forall X Y (φ ψ : lkf),
      display_derivation X φ -> display_derivation Y ψ -> display_derivation (X [·] Y) (φ·ψ)
  | rresL : forall X (φ ψ : lkf),
      display_derivation X (φ [\] ψ) -> display_derivation X (φ \ ψ)
  | rresR : forall X Y (φ ψ : lkf),
      display_derivation X φ -> display_derivation ψ Y -> display_derivation (φ \ ψ) (X [\] Y)
  | lresL : forall X (φ ψ : lkf),
      display_derivation X (φ [/] ψ) -> display_derivation X (φ / ψ)
  | lresR : forall X Y (φ ψ : lkf),
      display_derivation φ X -> display_derivation Y ψ -> display_derivation (φ / ψ) (X [/] Y)
  | cut : forall X Y Z, display_derivation X Y -> display_derivation Y Z -> display_derivation X Z
.

Declare Scope str_scope.
Delimit Scope str_scope with lks.

Notation "X ; Y" := (X [·] Y) (at level 30).
Notation "X ⊢ Y" := (display_derivation X Y) (at level 60) : str_scope.

Module Display.

(* Primer cal formalitzar la tonicitat, desprès podras demostrar que certs connectors estructurals apareixen en certes tonicitats.
   Desprès caldrà derivationtruir una nova traducció τ que respecti aquesta estructura.
 *)

Local Open Scope ring_scope.
(* This tonicity is left ill-defined over formulas and undefined over non-realizable formulas. *)
Inductive tonicity : lks -> 'Z_2 -> Type :=
  | leaf_p : forall (φ : lkf), tonicity φ ⊹
  | leaf_m : forall (φ : lkf), tonicity φ ─
  | fusion_p : forall X Y,
      tonicity X ⊹ -> tonicity Y ⊹ -> tonicity (X; Y) ⊹
  | lres_m : forall X Y,
      tonicity X ─ -> tonicity Y ⊹ -> tonicity (X[/] Y) ─
  | rres_m : forall X Y,
      tonicity X ⊹ -> tonicity Y ─ -> tonicity (X[\] Y) ─
.
Close Scope ring_scope.

(* Note that proofs derivationist of permutations of variables of each other. *)
Lemma tonicity_display X Y: ((X⊢Y)%lks -> (tonicity X 0)*(tonicity Y ─))%R.
Proof.
  elim; intros.
  - split.
    + exact: (leaf_p _).
    + exact: (leaf_m _).
  - remember (Z [/] Y0) as W. move: H HeqW => [HX [|||Z' Y' HZ HY|]] // HeqW.
    injection HeqW as HeqZ HeqY. rewrite HeqZ in HZ. rewrite HeqY in HY.
    split; first apply fusion_p.
    + exact: HX.
    + exact: HY.
    + exact: HZ.
  - remember (X0; Y0) as W. move: H HeqW => [[||X' Y' HX HY||] HZ] // HeqW.
    injection HeqW as HeqX HeqY. rewrite HeqX in HX. rewrite HeqY in HY.
    split; last apply rres_m.
    + exact: HY.
    + exact: HX.
    + exact: HZ.
  - remember (X0[\] Z) as W. move: H HeqW => [HY [||||X' Y' HX HZ]] // HeqW.
    injection HeqW as HeqX HeqZ. rewrite HeqX in HX. rewrite HeqZ in HZ.
    split; last apply lres_m.
    + exact: HX.
    + exact: HZ.
    + exact: HY.
  - move: H => [_ HX].
    split.
    + exact: (leaf_p _).
    + exact: HX.
  - move: H H0 => [HX _] [HY _].
    split; first apply fusion_p.
    + exact: HX.
    + exact: HY.
    + exact: (leaf_m _).
  - move: H => [HX _].
    split.
    + exact: HX.
    + exact: (leaf_m _).
  - move: H H0 => [HX _] [_ HY].
    split; last apply rres_m.
    + exact: (leaf_p _).
    + exact: HX.
    + exact: HY.
  - move: H => [HX _].
    split.
    + exact: HX.
    + exact: (leaf_m _).
  - move: H H0 => [_ HX] [HY _].
    split; last apply lres_m.
    + exact: (leaf_p _).
    + exact: HX.
    + exact: HY.
  move: H H0 => [HX HY] [_ HZ].
  split.
  - exact: HX.
  - exact: HZ.
Qed.

Lemma tonicity_formula X : (tonicity X ⊹ -> tonicity X ─ -> is_formula X)%R.
Proof.
  case: X; simpl; intros.
  - by[].
  - inversion H0.
  - inversion H.
  inversion H.
Qed.
Goal forall X Y Z, notT (X⊢Y;Z)%lks.
intros. move/tonicity_display => [_ H]. inversion H.
Qed.

Fixpoint τ (s : 'Z_2) (X : lks) (tX : tonicity X s):=
  match tX with
  | leaf_p φ => φ
  | leaf_m φ => φ
  | fusion_p X Y tX tY => (τ ⊹ X tX)%R·(τ ⊹ Y tY)%R
  | lres_m X Y tX tY => (τ ─ X tX)%R/(τ ⊹ Y tY)%R
  | rres_m X Y tX tY => (τ ⊹ X tX)%R\(τ ─ Y tY)%R
  end
.

Fixpoint τ_blind X :=
  match X with
  | 'ψ => ψ
  | X;Y => (τ_blind X)·(τ_blind Y)
  | X[/]Y => (τ_blind X)/(τ_blind Y)
  | X[\]Y => (τ_blind X)\(τ_blind Y)
  end
.


Proposition τ_correct X s tX : (τ s X tX) = τ_blind X.
Proof.
  elim: tX; try by[]; intros Y Z tY IHY tZ IHZ; by rewrite /= IHY IHZ.
Qed.

Proposition τ_formula φ s tφ : τ s 'φ tφ = φ.
Proof.
  remember 'φ as X. case: tφ HeqX => ψ; try discriminate;
  by injection 1 as Heqφ; rewrite Heqφ.
Qed.

(*
   Cut gives to calculi a Category structure (modulo some equivalence between
   deduction rules).
   We're going to see that τ is a functor from the category of the display
   calculi to the original calculi.
*)

(*
   In Coq <-> allows you to rewrite, rewriting of HITs is problematic, so <->
   requires Types of height ⊹ (Props).
   As for now, deduction is a set and not a Proposition.
   I defined it this way in order to prove strong induction below, not really
   important for our objectives.
 *)
Theorem dp_lambek X Y : (X ⊢ Y)%lks -> (τ_blind X ⊢ τ_blind Y).
Proof.
  intros. elim: H; simpl; intros.
  - exact: (axiom_id _).
  - exact: (res3 _ _ _ H).
  - exact: (res2 _ _ _ H).
  - apply res1. exact: (res4 _ _ _ H).
  - exact: H.
  - exact: (lambek.lk_tensorR _ _ _ _ H H0).
  - exact: H.
  - exact: (lambek.lk_rresR _ _ _ _ H H0).
  - exact: H.
  - exact: (lambek.lk_lresR _ _ _ _ H H0).
  exact: (cut_rule _ _ _ H H0).
Qed.

Corollary dp_lambek_lkf (φ ψ : lkf) : (φ ⊢ ψ)%lks -> (φ ⊢ ψ).
Proof.
  exact: (dp_lambek _ _).
Qed.


Theorem tensorL_inv (X : lks) (φ ψ : lkf) : (φ·ψ⊢X)%lks -> (φ;ψ⊢X)%lks.
Proof.
  intros. apply (cut _ (φ·ψ)).
  - apply tensorR; exact: (display_id _).
  - exact: H.
Qed.

Theorem lresL_inv (X : lks) (φ ψ : lkf) : (X⊢φ/ψ)%lks -> (X⊢φ[/]ψ)%lks.
Proof.
  intros. apply (cut _ (φ/ψ)).
  - exact: H.
  - apply lresR; exact: (display_id _).
Qed.

Theorem rresL_inv (X : lks) (φ ψ : lkf) : (X⊢φ\ψ)%lks -> (X⊢φ[\]ψ)%lks.
Proof.
  intros. apply (cut _ (φ\ψ)).
  - exact: H.
  - apply rresR; exact: (display_id _).
Qed.


(* Havia entès malament el que eren les estructures, no són més que connectors externs entre fòrmules.
   He de demostrar que en aquells llocs on hi hagi tonicitat negativa no pot haver-hi ; i on hi hagi tonicitat positiva no pot haver-hi / o \ *)

Close Scope str_scope.

(*
   ' is a functor from the category of the original calculi and the category
   of the display calculi given by Goré *Substructural Logics on Display*
*)
Theorem lambek_dp_lkf φ ψ : (φ⊢ψ) -> (φ⊢ψ)%lks.
Proof.
  intros. elim H; intros.
  - exact: (display_id _).
  - apply /lresL /display3 /display2. exact: (tensorL_inv _ _ _ H0).
  - apply /rresL /display2. exact: (tensorL_inv _ _ _ H0).
  - apply /tensorL /display1. exact: (lresL_inv _ _ _ H0).
  - apply /tensorL /display1 /display3. exact: (rresL_inv _ _ _ H0).
  - apply (cut _ ψ0). exact: H0. exact: H1.
Qed.

(*
   The fiber of τ is contractible, so that we can derivationider structures somehow
   equal to formulas (provably equivalent).
*)

Definition sequent (s : 'Z_2) X Y :=
  match s with
  | (Ordinal 0 _) => (X⊢Y)%lks
  | _ => (Y⊢X)%lks
  end
.

(* The tonicity also seems to check whether the structure is appropiate.
*)
Proposition τ_sequent s X tX : sequent s X (τ s X tX).
Proof.
  elim: X s tX; intros.
  - case: s l tX; case; intros;
    rewrite τ_formula; exact: (display_id _).
  - remember (l; l0) as Z. case: tX HeqZ; try discriminate; simpl; intros.
    apply: tensorR.
    + injection HeqZ as HeqX _. move: t. rewrite HeqX; intros. exact (X 0%R _).
    + injection HeqZ as _ HeqY. move: t0. rewrite HeqY; intros. exact (X0 0%R _).
  - remember (l[\] l0) as Z. case: tX HeqZ; try discriminate; simpl; intros.
    apply: rresR.
    + injection HeqZ as HeqX _. move: t. rewrite HeqX; intros. exact (X 0%R _).
    + injection HeqZ as _ HeqY. move: t0. rewrite HeqY; intros. exact (X0 ─ _).
  remember (l[/] l0) as Z. case: tX HeqZ; try discriminate; simpl; intros.
  apply: lresR.
  + injection HeqZ as HeqX _. move: t. rewrite HeqX; intros. exact (X ─ _).
  + injection HeqZ as _ HeqY. move: t0. rewrite HeqY; intros. exact (X0 0%R _).
Qed.

(* Therefore, formula's derivations will be provably equivalent to those derivations of structures with appropiate tonicities. *)
Theorem lambek_dp X Y tX tY : (τ ⊹ X tX⊢τ ─ Y tY)%R -> (X⊢Y)%lks.
Proof.
  intros. apply: (cut _ (τ ─ Y tY)).
    apply: (cut _ (τ 0%R X tX)).
      exact: (τ_sequent 0%R _ _).
    apply: lambek_dp_lkf. exact H.
  exact: (τ_sequent ─ _ _).
Qed.

(*
   Furthermore, τ is left inverse of ', so that the original calculi is a
   reflective subcategory of the display calculi.
*)

End Display.

Module Semantics.

Proposition sm_lres_tensor_K φ ψ : (φ/ψ)·ψ ⊩ φ.
Proof.
  intros H W M s.
  pose R := rel W M.
  pose V := val W M.
  rewrite /sat /= in H.
  specialize H with W M s as [r [t [HV [H HR]]]].
  exact: (H _ _ HV HR).
Qed.

Proposition sm_tensor_lres_K φ ψ : φ⊩φ·ψ/ψ.
Proof.
  intros H W M s.
  pose R := rel W M.
  pose V := val W M.
  rewrite /sat /= in H.
  specialize H with W M s.
  move => /= t r HR HV.
  exists s. exists r. split; last split.
  - exact: HR.
  - exact: H.
  exact: HV.
Qed.

End Semantics.


(*  SOME MISCELLANEA  *)

Definition lass_law := forall φ ψ ρ, (φ·ψ)·ρ⊢φ·(ψ·ρ).
Definition rass_law := forall φ ψ ρ, φ·(ψ·ρ)⊢(φ·ψ)·ρ.

Proposition lres_K (φ ψ ρ:lkf) : (lass_law) -> (φ/ψ)·(ψ/ρ)⊢φ/ρ.
Proof.
  intro lass. apply res1.
  apply (cut_rule _ ((φ/ψ)·((ψ/ρ)·ρ))); first exact: (lass _ _ _).
  apply (cut_rule _ ((φ/ψ)·ψ)).
  apply tensor_rton_pos.
  - exact: (lres_tensor_K _ _).
  - exact: (lres_tensor_K _ _).
Qed.

(* Tant per l'igualtat i l'inclusió hauries d'escriure una versió Fixpoint i una versió inductiva. *)

Inductive subformula : lkf -> lkf -> Type :=
  | sub_refl φ : subformula φ φ
  | sub_tensorl φ ψ ψ' : subformula φ ψ -> subformula φ (ψ·ψ')
  | sub_tensorr φ ψ ψ' : subformula φ ψ -> subformula φ (ψ'·ψ)
  | sub_lresl φ ψ ψ' : subformula φ ψ -> subformula φ (ψ'/ψ)
  | sub_lresr φ ψ ψ' : subformula φ ψ -> subformula φ (ψ'/ψ)
  | sub_rresl φ ψ ψ' : subformula φ ψ -> subformula φ (ψ'\ψ)
  | sub_rresr φ ψ ψ' : subformula φ ψ -> subformula φ (ψ'\ψ)
.

Inductive substructure : lks -> lks -> Type :=
  | sub_refl_lks X : substructure X X
  | sub_tensorl_lks X Y Z : substructure X Y -> substructure X (Y;Z)
  | sub_tensorr_lks X Y Z : substructure X Z -> substructure X (Y;Z)
  | sub_lresl_lks X Y Z : substructure X Y -> substructure X (Y[/]Z)
  | sub_lresr_lks X Y Z : substructure X Z -> substructure X (Y[/]Z)
  | sub_rresl_lks X Y Z : substructure X Y -> substructure X (Y[\]Z)
  | sub_rresr_lks X Y Z : substructure X Z -> substructure X (Y[\]Z)
.

Definition strict_substructure X Y := (substructure X Y * (X <> Y))%type.

Proposition substructure_trans X Y Z : substructure X Y -> substructure Y Z -> substructure X Z.
Proof.
  intros. move: H. elim H0; intros.
  - exact: H.
  - apply: sub_tensorl_lks. exact: (H H1).
  - apply: sub_tensorr_lks. exact: (H H1).
  - apply: sub_lresl_lks. exact: (H H1).
  - apply: sub_lresr_lks. exact: (H H1).
  - apply: sub_rresl_lks. exact: (H H1).
  - apply: sub_rresr_lks. exact: (H H1).
Qed.

Fixpoint depth (X : lks) :=
  match X with
  | 'φ => 0
  | X; Y => (maxn (depth X) (depth Y)).+1
  | X[/] Y => (maxn (depth X) (depth Y)).+1
  | X[\] Y => (maxn (depth X) (depth Y)).+1
end.
Fixpoint fusion_depth (X : lks) :=
  match X with
  | 'φ => 0
  | X; Y => (maxn (fusion_depth X) (fusion_depth Y)).+1
  | X[/] Y => (maxn (fusion_depth X) (fusion_depth Y))
  | X[\] Y => (maxn (fusion_depth X) (fusion_depth Y))
end.
Fixpoint lres_depth (X : lks) :=
  match X with
  | 'φ => 0
  | X; Y => (maxn (lres_depth X) (lres_depth Y))
  | X[/] Y => (maxn (lres_depth X) (lres_depth Y)).+1
  | X[\] Y => (maxn (lres_depth X) (lres_depth Y))
end.
Fixpoint rres_depth (X : lks) :=
  match X with
  | 'φ => 0
  | X; Y => (maxn (rres_depth X) (rres_depth Y))
  | X[/] Y => (maxn (rres_depth X) (rres_depth Y))
  | X[\] Y => (maxn (rres_depth X) (rres_depth Y)).+1
end.
Definition der_depth (X Y : lks) := maxn (depth X) (depth Y).

(*
  assert (no_fixl: forall W U, W <> W; U).
    intros. intro nH. elim: W U nH; try discriminate; intros.
    injection nH as nH _. exact : (H _ nH).
  assert (no_fixr: forall W U, W <> U; W).
    intros. intro nH. elim: W U nH; try discriminate; intros.
    injection nH as _ nH. exact : (H0 _ nH). *)

Proposition substructure_cancel X Y Z:
  (substructure (X; Y) Z -> (notT (substructure Z X) * notT (substructure Z Y))) *
  (substructure (X[\] Y) Z -> (notT (substructure Z X) * notT (substructure Z Y))) *
  (substructure (X[/] Y) Z -> (notT (substructure Z X) * notT (substructure Z Y))).
Proof.
  elim: Z X Y; intros; (split; first split); intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H1.
    + move: H5 H4 H2 H1 => _ _ _ _.
      elim: l H; intros; split; intro nH.
      * inversion nH.
      * move: (H0 '(l) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l; l1) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      * move: (H0 (l; l1) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l[\]l1) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      * move: (H0 (l[\]l1) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l[/]l1) l0) => [[IH _] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      move: (H0 (l[/]l1) l0) => [[IH _] _].
      move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
    + move: (H X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [[_ /(_ H4) [IHX IHY]] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[_ /(_ H4) [IHX IHY]] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [_ /(_ H4) [IHX IHY]]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [_ /(_ H4) [IHX IHY]]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_tensorr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
    + move: H5 H4 H2 H1 => _ _ _ _.
      elim: l H; intros; split; intro nH.
      * inversion nH.
      * move: (H0 '(l) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l; l1) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      * move: (H0 (l; l1) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l[\]l1) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      * move: (H0 (l[\]l1) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
      * move: (H2 (l[/]l1) l0) => [[_ IH] _].
        move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
      move: (H0 (l[/]l1) l0) => [[_ IH] _].
      move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
    + move: (H X Y) => [[_ /(_ H4)[IHX IHY]] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[_ /(_ H4) [IHX IHY]] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [_ /(_ H4) [IHX IHY]]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [_ /(_ H4) [IHX IHY]]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_rresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[/(_ H4) [IHX IHY] _] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  - inversion H1.
      move: (H X Y) => [[_ /(_ H4) [IHX IHY]] _]. split.
        intro nH.
        apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
        exact: (IHX nH).
      intro nH.
      apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHY nH).
    move: (H0 X Y) => [[_ /(_ H4) [IHX IHY]] _]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  inversion H1.
  - move: H5 H4 H2 H1 => _ _ _ _.
    elim: l H; intros; split; intro nH.
    + inversion nH.
    + move: (H0 '(l) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
    + move: (H2 (l; l1) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
    + move: (H0 (l; l1) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
    + move: (H2 (l[\]l1) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
    + move: (H0 (l[\]l1) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
    + move: (H2 (l[/]l1) l0) => [_ IH].
      move: (IH nH) => [IHX IHY]. exact: (IHX (sub_refl_lks _)).
    move: (H0 (l[/]l1) l0) => [_ IH].
    move: (IH nH) => [IHX IHY]. exact: (IHY (sub_refl_lks _)).
  - move: (H X Y) => [_ /(_ H4)[IHX IHY]]. split.
      intro nH.
      apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
      exact: (IHX nH).
    intro nH.
    apply (substructure_trans _ _ _ (sub_lresl_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHY nH).
  move: (H0 X Y) => [_ /(_ H4) [IHX IHY]]. split.
    intro nH.
    apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
    exact: (IHX nH).
  intro nH.
  apply (substructure_trans _ _ _ (sub_lresr_lks _ _ _ (sub_refl_lks _))) in nH.
  exact: (IHY nH).
Qed.

Proposition substructure_antisym X Y : substructure X Y -> substructure Y X -> Y = X.
Proof.
  elim: Y X; intros.
  - inversion H. reflexivity.
  - inversion H1. reflexivity.
      by move: (substructure_cancel l l0 X) => [[/(_ H2) [/(_ H5) nH _] _] _].
    by move: (substructure_cancel l l0 X) => [[/(_ H2) [_ /(_ H5) nH] _] _].
  - inversion H1. reflexivity.
      by move: (substructure_cancel l l0 X) => [[_ /(_ H2) [/(_ H5) nH] _] _].
    by move: (substructure_cancel l l0 X) => [[_ /(_ H2) [_ /(_ H5) nH]] _].
  inversion H1. reflexivity.
    by move: (substructure_cancel l l0 X) => [_ /(_ H2) [/(_ H5) nH] _].
  by move: (substructure_cancel l l0 X) => [_ /(_ H2) [_ /(_ H5) nH]].
Qed.

Lemma strict_subformula_ind (P : lks -> Type) :
  (forall X, (forall Y, substructure Y X -> Y <> X -> P Y) -> P X)-> forall X, P X.
Proof.
  intros. apply X; elim: X0; intros.
  - inversion H. contradiction.
  - apply X; intros. inversion H.
    + contradiction.
    + apply X0. exact: (substructure_trans _ _ _ H1 H5).
      destruct Y.
      * inversion H1. rewrite H8 in H2. by exfalso.
      * intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
      * intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
      intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    apply X1. exact: (substructure_trans _ _ _ H1 H5).
    destruct Y.
     + inversion H1. rewrite H8 in H2. by exfalso.
     + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
     + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
  - apply X; intros. inversion H.
    + contradiction.
    + apply X0. exact: (substructure_trans _ _ _ H1 H5).
      destruct Y.
      * inversion H1. rewrite H8 in H2. by exfalso.
      * intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
      * intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
      intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    apply X1. exact: (substructure_trans _ _ _ H1 H5).
    destruct Y.
    + inversion H1. rewrite H8 in H2. by exfalso.
    + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
  apply X; intros. inversion H.
  - contradiction.
  - apply X0. exact: (substructure_trans _ _ _ H1 H5).
    destruct Y.
    + inversion H1. rewrite H8 in H2. by exfalso.
    + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    + intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
    intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
  apply X1. exact: (substructure_trans _ _ _ H1 H5).
  destruct Y.
  - inversion H1. rewrite H8 in H2. by exfalso.
  - intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
  - intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
  intro nH. rewrite nH in H1 H2. by rewrite (substructure_antisym _ _ H1 H5) in H2.
Qed.
Lemma lkf_eq_dec : forall (A B : lkf), { A = B } + { A <> B }.
Proof.
  elim; intros;
    try (
      destruct B; intros; try (right; intros nH; discriminate);
      destruct (H B1); destruct (H0 B2);
      try (right; intros nH; injection nH as eq1 eq2; apply n; exact: eq1);
      first (left; rewrite e e0; reflexivity);
      right; intros nH; injection nH as eq1 eq2; apply n; exact: eq2
      ).
  - elim B; intros;
      try (destruct H; destruct H0; right; intros nH; discriminate).
    case H: (n == n0).
    + rewrite (eqnP H). left. reflexivity.
    right. intros nH. injection nH as nH.
    rewrite nH eq_refl in H. discriminate.
Qed.

Open Scope str_scope.

Lemma lks_eq_dec : forall (A B : lks), { A = B } + { A <> B }.
Proof.
  elim; intros;
    try (
      destruct B; intros; try (right; intros nH; discriminate);
      destruct (H B1); destruct (H0 B2);
      try (right; intros nH; injection nH as eq1 eq2; apply n; exact: eq1);
      first (left; rewrite e e0; reflexivity);
      right; intros nH; injection nH as eq1 eq2; apply n; exact: eq2
      ).
  - elim B; intros;
      try (destruct H; destruct H0; right; intros nH; discriminate).
    case (lkf_eq_dec l l0).
    + left. rewrite e. reflexivity.
    right. intros nH. injection nH as nH. exact: (n nH).
Qed.

(* Demostrar un reflect entre igualtats *)
Fixpoint eq_lkf (A B : lkf) : bool :=
  match A , B with
  | var n, var m => n == m
  | M·N, L·K => (eq_lkf M L)&&(eq_lkf N K)
  | M/N, L/K => (eq_lkf M L)&&(eq_lkf N K)
  | M\N, L\K => (eq_lkf M L)&&(eq_lkf N K)
  | _, _ => false
end.

Fixpoint eq_lks (A B : lks) : bool :=
  match A , B with
  | ' N, 'M  => eq_lkf N M
  | M[·]N, L[·]K => (eq_lks M L)&&(eq_lks N K)
  | M[/]N, L[/]K => (eq_lks M L)&&(eq_lks N K)
  | M[\]N, L[\]K => (eq_lks M L)&&(eq_lks N K)
  | _, _ => false
end.

Lemma eq_lkfP A B : reflect (A = B) (eq_lkf A B).
Proof.
  elim: B A; intros.
  - case: A; simpl; intros; try (right; discriminate).
     + apply: (@equivP (n0 = n)).
       exact: eqP.
     + split. move ->. reflexivity.
       intro H. injection H. exact: (fun n => n).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
Qed.

(* Probablement aquesta demo es pot repetir en un cas molt més general, és quasi igual a l'anterior *)

Theorem eq_lksP A B : reflect (A = B) (eq_lks A B).
Proof.
  elim: B A; intros.
  - case: A; simpl; intros; try (right; discriminate).
     + apply: (@equivP (l0 = l)).
       exact: eq_lkfP.
     + split. move ->. reflexivity.
       intro H. injection H. exact: (fun n => n).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
  - case: A; simpl; intros; try (right; discriminate).
    case: (H l1); simpl.
      move => ->. case: (H0 l2). move ->. left. reflexivity.
      right. intro nH. injection nH as nH. exact (n nH).
    right. intro nH. injection nH as nH. exact (n nH).
Qed.

Inductive proof_comp : forall {A B C D}, (A⊢B)->(C⊢D)->Type :=
  | refl_id : forall {A B} (L : A⊢B),
      proof_comp L L
  | Sdisplay1 : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (display1 A B C M)
  | Sdisplay2 : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (display2 A B C M)
  | Sdisplay3 : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (display3 A B C M)
  | StensorL : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (tensorL A B C M)
  | StensorR : forall {A B C D E F} (L : E⊢F) M N,
      proof_comp L M -> proof_comp L N -> proof_comp L (tensorR A B C D M N)
  | SrresL : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (rresL A B C M)
  | SlresrL : forall {A B C D E} (L : D⊢E) M,
      proof_comp L M -> proof_comp L (lresL A B C M)
  | Scut : forall {A B C D E} (L : D⊢E) M N,
      proof_comp L M -> proof_comp L N -> proof_comp L (cut A B C M N)
.
Notation "L ≤ M" := (proof_comp L M) (at level 70).

Lemma transport {X : Type} {A : X -> Type} {x y : X} : x = y -> A x -> A y.
Proof.
  move ->. exact: (fun n => n).
Qed.

Lemma min_id_transport : forall A B (M : A⊢B) X,
    M≤(display_id X) -> A = X ∧ B = X.
Proof.
  intros. inversion H; split. reflexivity. exact: H3.
Qed.

Goal forall X Y, ~X·Y = X.
  intros. elim X; intros; intros nH; try discriminate.
  injection nH as nH eqY. rewrite eqY in H. exact: (H nH).
Qed.

Goal forall X Y, ~Y·X = X.
  intros. elim X; intros; intros nH; try discriminate.
  injection nH as eqY nH. rewrite eqY in H0. exact: (H0 nH).
Qed.

Ltac prepare M d temp := revert dependent M; revert dependent d;
  repeat (intro; intro; intro temp;
          repeat (try (apply (inj_pair2_eq_dec _ lks_eq_dec) in temp);
                  try (apply (inj_pair2_eq_dec _ lkf_eq_dec) in temp));
          revert temp; intros ?K0).

Lemma min_id : forall (φ : lkf) (M : φ ⊢ φ), M≤(display_id φ) -> M = display_id φ.
Proof.
  intros.
  inversion H. move: H0 H1 => _ _.
  prepare M φ temp.
  rewrite <- K1. exact: K0.
Qed.

(* Pensar en com es pot fer útil aquesta inducció forta, donat que tal com és una destrucció no faria seguiment de la derivationtrucció de la prova. *)
Lemma strong_ind (P : forall A B, A⊢B -> Type)
  (base : forall (φ : lkf), P φ φ (display_id φ))
  (step_display1 : forall X Y Z (M : X⊢Z[/]Y),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P (X[·]Y) Z (display1 X Y Z M))
  (step_display2 : forall X Y Z (M : X[·]Y⊢Z),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P Y (X[\]Z) (display2 X Y Z M))
  (step_display3 : forall X Y Z (M : Y⊢X[\]Z),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P X (Z[/]Y) (display3 X Y Z M))
  (step_tensorL : forall (φ ψ:lkf) X (M : φ[·]ψ⊢X),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P (φ·ψ) X (tensorL X φ ψ M))
  (step_tensorR : forall (φ ψ:lkf) X Y (M : X⊢φ) (N:Y⊢ψ),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      (forall A B (L : A⊢B), L ≤ N -> P A B L) ->
      P (X[·]Y) (φ·ψ) (tensorR X Y φ ψ M N))
  (step_rresL : forall (φ ψ:lkf) X (M : X⊢φ[\]ψ),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P X (φ\ψ) (rresL X φ ψ M))
  (step_rresR : forall (φ ψ:lkf) X Y (M : X⊢φ) (N:ψ⊢Y),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      (forall A B (L : A⊢B), L ≤ N -> P A B L) ->
      P (φ\ψ) (X[\]Y) (rresR X Y φ ψ M N))
  (step_lresL : forall (φ ψ:lkf) X (M : X⊢φ[/]ψ),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      P X (φ/ψ) (lresL X φ ψ M))
  (step_lresR : forall (φ ψ:lkf) X Y (M : φ⊢X) (N:Y⊢ψ),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      (forall A B (L : A⊢B), L ≤ N -> P A B L) ->
      P (φ/ψ) (X[/]Y) (lresR X Y φ ψ M N))
  (step_cut : forall X Y Z (M : X⊢Y) (N:Y⊢Z),
      (forall A B (L : A⊢B), L ≤ M -> P A B L) ->
      (forall A B (L : A⊢B), L ≤ N -> P A B L) ->
      P X Z (cut X Y Z M N))
    : forall A B L, P A B L.
Proof.
  intros.
  apply:
    (display_derivation_rect
       (fun C D (N : C⊢D) => forall E F (M : E⊢F), M ≤ N -> P E F M)
         _ _ _ _ _ _ _ _ _ _ _ A B L A B L (refl_id L)); intros.
  - move: (H) => /min_id_transport [eqA eqB]. revert dependent M.
    rewrite eqA. rewrite eqB. intros.
    apply min_id in H. rewrite H. exact: (base _).
  - inversion H.
    + move: H5 H8 H7 H6 H0 H1 => _ _ _ _ _ _. move: L0 L1 L2 A0 B0 => _ _ _ _ _.
      revert dependent M. rewrite H2. rewrite H3. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_display1. exact: X0.
      * rewrite K1 in H7. rewrite K0 in H7. exact: (X0 _ _ _ H7).
    + prepare M d temp.
      rewrite K1 in H5. rewrite K0 in H5. exact: (X0 _ _ _ H5).
  - inversion H.
    + move: H5 H8 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_display2. exact: X0.
      * rewrite K1 in H10. rewrite K0 in H10. exact: (X0 _ _ _ H10).
    + prepare M d temp. 
      rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
  - inversion H.
    + move: H5 H8 => _ _. revert dependent M. rewrite H3. rewrite H2. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_display3. exact: X0.
      * rewrite K1 in H10. rewrite K0 in H10. exact: (X0 _ _ _ H10).
    + prepare M d temp.
      rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
  - inversion H.
    + move: H5 H8 H7 H6 H1 H0 => _ _ _ _ _ _. revert dependent M.
      rewrite H3. rewrite H2. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_tensorL. exact: X0.
      * rewrite K1 in H7. rewrite K0 in H7. exact: (X0 _ _ _ H7).
    + prepare M d temp.
      rewrite K1 in H5. rewrite K0 in H5. exact: (X0 _ _ _ H5).
 - inversion H.
   + move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
     inversion H; prepare M d temp.
     * rewrite K1 in K0. rewrite K0. apply step_tensorR.
       - exact: X0.
       - exact: X1.
     * rewrite K1 in H11. rewrite K0 in H11. exact: (X0 _ _ _ H11).
    + prepare M d temp.
      rewrite K1 in H5. rewrite K0 in H5. exact: (X0 _ _ _ H5).
  - inversion H.
    + move: H5 H8 H7 H6 H1 H0 => _ _ _ _ _ _. revert dependent M.
      rewrite H3. rewrite H2. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_rresL. exact: X0.
      * rewrite K1 in H6. rewrite K0 in H6. exact: (X0 _ _ _ H6).
    +prepare M d temp.
      rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
 - inversion H.
   move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
   inversion H; prepare M d temp.
   rewrite K1 in K0. rewrite K0. apply step_rresR.
   * exact: X0.
   * exact: X1.
- inversion H.
  + move: H5 H6 H8 H7 H0 H1 => _ _ _ _ _ _. revert dependent M.
    rewrite H3. rewrite H2. intros.
    inversion H; prepare M d temp.
    * rewrite K1 in K0. rewrite K0. apply step_lresL. exact: X0.
    * rewrite K1 in H6. rewrite K0 in H6. exact: (X0 _ _ _ H6).
  + prepare M d temp.
    rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
 - inversion H.
   move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
   inversion H; prepare M d temp.
   rewrite K1 in K0. rewrite K0. apply step_lresR.
   * exact: X0.
   * exact: X1.
 - inversion H.
   + move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
     inversion H; prepare M d temp.
     * rewrite K1 in K0. rewrite K0. apply step_cut.
       - exact: X0.
       - exact: X1.
     * rewrite K1 in H13. rewrite K0 in H13. exact: (X0 _ _ _ H13).
    + prepare M d temp.
      rewrite K1 in H7. rewrite K0 in H7. exact: (X0 _ _ _ H7).
Qed.
