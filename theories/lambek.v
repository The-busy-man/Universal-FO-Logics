From mathcomp Require Import all_ssreflect.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Unset Printing Implicit Defensive.

(*                                                                                     *)
(*                                                                                     *)
(*               FORMALIZING Lambek Calculus SINTAXIS AND SEMANTICS                    *)
(*                                                                                     *)
(*                                                                                     *)

Notation "'ℕ'" := nat.

(* We work non-associative Lambek Calculus.
    It's shown that its display system corresponds to Lambek's original formulation.
    At the end some miscellanea is found for sanity checks.
 *)

Inductive lkf :=
  | var : ℕ -> lkf
  | tensor_lkf : lkf -> lkf -> lkf
  | rresidual_lkf : lkf -> lkf -> lkf
  | lresidual_lkf : lkf -> lkf -> lkf
.

Notation "a '·' b" := (tensor_lkf a b) (at level 30).
Notation "a '/' b" := (lresidual_lkf a b) (at level 40, left associativity).
Notation "a '\' b" := (rresidual_lkf a b) (at level 45, right associativity).
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
Notation "M ; s ⊨ φ " := (force M s φ) (at level 50, format "M ; s  ⊨  φ") : lkf_scope.
Print Grammar pattern.
Definition sat φ := forall W (M : kripke W) s, (M;s⊨φ)%lkf.
Notation "⊨ φ" := (sat φ) (at level 50) : lkf_scope.

Definition sat_cons φ ψ:= (⊨φ->⊨ψ)%lkf.
Notation "φ ⊩ ψ" := (sat_cons φ ψ) (at level 50).


(*  CALCULI  *)

(* Original Calculi *)
Inductive cons : lkf -> lkf -> Type :=
  | axiom_id : forall φ : lkf, cons φ φ
  | res1 : forall φ ψ ρ : lkf, cons (φ·ψ) ρ -> cons φ (ρ/ψ)
  | res2 : forall φ ψ ρ : lkf, cons (φ·ψ) ρ -> cons ψ (φ\ρ)
  | res3 : forall φ ψ ρ : lkf, cons φ (ρ/ψ) -> cons (φ·ψ) ρ
  | res4 : forall φ ψ ρ : lkf, cons ψ (φ\ρ) -> cons (φ·ψ) ρ
  | cut_rule : forall φ ψ ρ : lkf, cons φ ψ -> cons ψ ρ -> cons φ ρ
.

Notation "φ ⊢ ψ" := (cons φ ψ) (at level 50).

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

Proposition rres_tensor_K φ ψ : φ⊢ψ\ψ·φ.
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
Notation "φ [/] ψ" := (lresidual_lks φ ψ) (at level 45).

(* Goré's 1998 article Lambek Calculi *)
Inductive display_cons : lks -> lks -> Type :=
  | display_id : forall X, display_cons X X
  | display1 : forall X Y Z, display_cons X (Z [/] Y) -> display_cons (X [·] Y) Z
  | display2 : forall X Y Z, display_cons (X [·] Y) Z -> display_cons Y (X [\] Z)
  | display3 : forall X Y Z, display_cons Y (X [\] Z) -> display_cons X (Z [/] Y)
  | tensorL : forall X (φ ψ : lkf), display_cons (φ [·] ψ) X -> display_cons (φ·ψ) X
  | tensorR : forall X Y (φ ψ : lkf), display_cons X φ -> display_cons Y ψ -> display_cons (X [·] Y) (φ·ψ)
  | rresL : forall X (φ ψ : lkf), display_cons X (φ [\] ψ) -> display_cons X (φ \ ψ)
  | rresR : forall X Y (φ ψ : lkf), display_cons X φ -> display_cons ψ Y -> display_cons (φ \ ψ) (X [\] Y)
  | lresL : forall X (φ ψ : lkf), display_cons X (φ [/] ψ) -> display_cons X (φ / ψ)
  | lresR : forall X Y (φ ψ : lkf), display_cons φ X -> display_cons Y ψ -> display_cons (φ / ψ) (X [/] Y)
  | cut : forall X Y Z, display_cons X Y -> display_cons Y Z -> display_cons X Z
.

Declare Scope str_scope.
Delimit Scope str_scope with lks.

Notation "X ; Y" := (X [·] Y) (at level 30).
Notation "X ⊢ Y" := (display_cons X Y) (at level 50) : str_scope.

Module Display.

Fixpoint τ φ :=
  match φ with
  | 'ψ => ψ
  | φ[·]ψ => (τ φ)·(τ ψ)
  | φ[\]ψ => (τ φ)\(τ ψ)
  | φ[/]ψ => (τ φ)/(τ ψ)
  end
.

(* Cut gives to calculi a Category structure (modulo some equivalence between deduction rules).
     We're going to see that τ is a functor from the category of the display calculi to the original calculi  *)
(* In Coq <-> allows you to rewrite, rewriting of HITs is problematic, so <-> requires Types of height 0 (Props) *)
(* As for now, deduction is a set and not a Proposition.
    I did like this in order to prove strong induction below, not really important for our objectives.
 *)
Theorem dp_lambek X Y : (X ⊢ Y)%lks -> (τ X ⊢ τ Y).
Proof.
  intros. elim: H; simpl; intros.
  - exact: (axiom_id _).
  - exact: (res3 _ _ _ H).
  - exact: (res2 _ _ _ H).
  - apply res1. exact: (res4 _ _ _ H).
  - exact: H.
  - exact: (lk_tensorR _ _ _ _ H H0).
  - exact: H.
  - exact: (lk_rresR _ _ _ _ H H0).
  - exact: H.
  - exact: (lk_lresR _ _ _ _ H H0).
  exact: (cut_rule _ _ _ H H0).
Qed.

Theorem dp_lambek_lkf (φ ψ : lkf) : (φ ⊢ ψ)%lks -> (φ ⊢ ψ).
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

(* ' is a functor from the category of the original calculi and the category of the display calculi given by Goré *Substructural Logics on Display* *)
Theorem lambek_dp X Y : (X⊢Y) -> (X⊢Y)%lks.
Proof.
  intros. elim H; intros.
  - exact: (display_id _).
  - apply /lresL /display3 /display2. exact: (tensorL_inv _ _ _ H0).
  - apply /rresL /display2. exact: (tensorL_inv _ _ _ H0).
  - apply /tensorL /display1. exact: (lresL_inv _ _ _ H0).
  - apply /tensorL /display1 /display3. exact: (rresL_inv _ _ _ H0).
  - apply (cut _ ψ). exact: H0. exact: H1.
Qed.

(* Furthermore, τ is left inverse of ', so that the original calculi is a reflective subcategory of the display calculi. *)
Goal forall φ, τ('φ) = φ.
  reflexivity.
Qed.

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

Lemma lkf_eq_dec : forall (A B : lkf), { A = B } + { A <> B }.
Proof.
  elim; intros;
    try (
      destruct B; intros; try (right; intros nH; discriminate);
      destruct (H B1); destruct (H0 B2); try (right; intros nH; injection nH as eq1 eq2; apply n; exact: eq1);
      first (left; rewrite e e0; reflexivity);
      right; intros nH; injection nH as eq1 eq2; apply n; exact: eq2
      ).
  - elim B; intros; try (destruct H; destruct H0; right; intros nH; discriminate).
    case H: (n == n0).
    + rewrite (eqnP H). left. reflexivity.
    right. intros nH. injection nH as nH. rewrite nH eq_refl in H. discriminate.
Qed.

Open Scope str_scope.

Lemma lks_eq_dec : forall (A B : lks), { A = B } + { A <> B }.
Proof.
  elim; intros;
    try (
      destruct B; intros; try (right; intros nH; discriminate);
      destruct (H B1); destruct (H0 B2); try (right; intros nH; injection nH as eq1 eq2; apply n; exact: eq1);
      first (left; rewrite e e0; reflexivity);
      right; intros nH; injection nH as eq1 eq2; apply n; exact: eq2
      ).
  - elim B; intros; try (destruct H; destruct H0; right; intros nH; discriminate).
    case (lkf_eq_dec l l0).
    + left. rewrite e. reflexivity.
    right. intros nH. injection nH as nH. exact: (n nH).
Qed.

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
  | 'N, 'M  => eq_lkf N M
  | M[·]N, L[·]K => (eq_lks M L)&&(eq_lks N K)
  | M[/]N, L[/]K => (eq_lks M L)&&(eq_lks N K)
  | M[\]N, L[\]K => (eq_lks M L)&&(eq_lks N K)
  | _, _ => false
end.

Inductive proof_comp : forall {A B C D}, (A⊢B)->(C⊢D)->Type :=
  | refl_id : forall {A B} (L : A⊢B), proof_comp L L
  | Sdisplay1 : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (display1 A B C M)
  | Sdisplay2 : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (display2 A B C M)
  | Sdisplay3 : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (display3 A B C M)
  | StensorL : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (tensorL A B C M)
  | StensorR : forall {A B C D E F} (L : E⊢F) M N, proof_comp L M -> proof_comp L N -> proof_comp L (tensorR A B C D M N)
  | SrresL : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (rresL A B C M)
  | SlresrL : forall {A B C D E} (L : D⊢E) M, proof_comp L M -> proof_comp L (lresL A B C M)
  | Scut : forall {A B C D E} (L : D⊢E) M N, proof_comp L M -> proof_comp L N -> proof_comp L (cut A B C M N)
.
Notation "L ≤ M" := (proof_comp L M) (at level 70).

Lemma transport {X : Type} {A : X -> Type} {x y : X} : x = y -> A x -> A y.
Proof.
  move ->. exact: (fun n => n).
Qed.

Lemma min_id_transport : forall A B (M : A⊢B) X, M≤(display_id X) -> A = X ∧ B = X.
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

Lemma min_id : forall X (M : X ⊢ X), M≤(display_id X) -> M = display_id X.
Proof.
  intros.
  inversion H. apply (inj_pair2_eq_dec _ lks_eq_dec) in H5. apply (inj_pair2_eq_dec _ lks_eq_dec) in H5.
   apply (inj_pair2_eq_dec _ lks_eq_dec) in H6. apply (inj_pair2_eq_dec _ lks_eq_dec) in H6.
  rewrite <- H5. exact: H6.
Qed.

Ltac prepare M d temp := revert dependent M; revert dependent d;
        repeat (intro; intro; intro temp; repeat (try (apply (inj_pair2_eq_dec _ lks_eq_dec) in temp); try (apply (inj_pair2_eq_dec _ lkf_eq_dec) in temp)); revert temp; intros ?K0).

Lemma strong_ind (P : forall A B, A⊢B -> Type)
  (base : forall X, P X X (display_id X))
  (step_display1 : forall X Y Z (M : X⊢Z[/]Y), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P (X[·]Y) Z (display1 X Y Z M))
  (step_display2 : forall X Y Z (M : X[·]Y⊢Z), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P Y (X[\]Z) (display2 X Y Z M))
  (step_display3 : forall X Y Z (M : Y⊢X[\]Z), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P X (Z[/]Y) (display3 X Y Z M))
  (step_tensorL : forall (φ ψ:lkf) X (M : φ[·]ψ⊢X), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P (φ·ψ) X (tensorL X φ ψ M))
  (step_tensorR : forall (φ ψ:lkf) X Y (M : X⊢φ) (N:Y⊢ψ), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P (X[·]Y) (φ·ψ) (tensorR X Y φ ψ M N))
  (step_rresL : forall (φ ψ:lkf) X (M : X⊢φ[\]ψ), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P X (φ\ψ) (rresL X φ ψ M))
  (step_rresR : forall (φ ψ:lkf) X Y (M : X⊢φ) (N:ψ⊢Y), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P (φ\ψ) (X[\]Y) (rresR X Y φ ψ M N))
  (step_lresL : forall (φ ψ:lkf) X (M : X⊢φ[/]ψ), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P X (φ/ψ) (lresL X φ ψ M))
  (step_lresR : forall (φ ψ:lkf) X Y (M : φ⊢X) (N:Y⊢ψ), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P (φ/ψ) (X[/]Y) (lresR X Y φ ψ M N))
  (step_cut : forall X Y Z (M : X⊢Y) (N:Y⊢Z), (forall A B (L : A⊢B), L ≤ M -> P A B L) -> P X Z (cut X Y Z M N))
    : forall A B L, P A B L.
Proof.
  intros. apply: (display_cons_rect (fun C D (N : C⊢D) => forall E F (M : E⊢F), M ≤ N -> P E F M) _ _ _ _ _ _ _ _ _ _ _ A B L A B L (refl_id L)); intros.
  (* Les diferents parts de la prova consisteixen en demostrar que l'única forma d'arribar a l'últim pas de la demostració és mitjançant l'últim argument, i fent servir transitivitat tenim que el nostre argument ha de ser més petit que que el precedent. *)
  - (* Per evitar un argument així de lleig cal fer servir transport *)
    move: (H) => /min_id_transport [eqA eqB]. revert dependent M.
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
    + move: H5 H8 H7 H6 H1 H0 => _ _ _ _ _ _. revert dependent M. rewrite H3. rewrite H2. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_tensorL. exact: X0.
      * rewrite K1 in H7. rewrite K0 in H7. exact: (X0 _ _ _ H7).
    + prepare M d temp.
      rewrite K1 in H5. rewrite K0 in H5. exact: (X0 _ _ _ H5).
 - inversion H.
   + move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
     inversion H; prepare M d temp.
     * rewrite K1 in K0. rewrite K0. apply step_tensorR. exact: X0.
     * rewrite K1 in H11. rewrite K0 in H11. exact: (X0 _ _ _ H11).
    + prepare M d temp.
      rewrite K1 in H5. rewrite K0 in H5. exact: (X0 _ _ _ H5).
  - inversion H.
    + move: H5 H8 H7 H6 H1 H0 => _ _ _ _ _ _. revert dependent M. rewrite H3. rewrite H2. intros.
      inversion H; prepare M d temp.
      * rewrite K1 in K0. rewrite K0. apply step_rresL. exact: X0.
      * rewrite K1 in H6. rewrite K0 in H6. exact: (X0 _ _ _ H6).
    +prepare M d temp.
      rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
 - inversion H.
   move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
   inversion H; prepare M d temp.
   rewrite K1 in K0. rewrite K0. apply step_rresR. exact: X0.
- inversion H.
  + move: H5 H6 H8 H7 H0 H1 => _ _ _ _ _ _. revert dependent M. rewrite H3. rewrite H2. intros.
    inversion H; prepare M d temp.
    * rewrite K1 in K0. rewrite K0. apply step_lresL. exact: X0.
    * rewrite K1 in H6. rewrite K0 in H6. exact: (X0 _ _ _ H6).
  + prepare M d temp.
    rewrite K1 in H4. rewrite K0 in H4. exact: (X0 _ _ _ H4).
 - inversion H.
   move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
   inversion H; prepare M d temp.
   rewrite K1 in K0. rewrite K0. apply step_lresR. exact: X0.
 - inversion H.
   + move: H8 H5 => _ _. revert dependent M. rewrite H2. rewrite H3. intros.
     inversion H; prepare M d temp.
     * rewrite K1 in K0. rewrite K0. apply step_cut. exact: X0.
     * rewrite K1 in H13. rewrite K0 in H13. exact: (X0 _ _ _ H13).
    + prepare M d temp.
      rewrite K1 in H7. rewrite K0 in H7. exact: (X0 _ _ _ H7).
Qed.

Close Scope str_scope.
