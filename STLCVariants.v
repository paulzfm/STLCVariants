(**-- Simply Typed Lambda-Calculus Boolean Extensions --**)

(* I am using Coq 8.12.0. *)

(* ################################################################# *)
(** * Auxilaries *)

Set Warnings "-notation-overridden,-parsing".

Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Unicode.Utf8_core. (* to make most symbols easy to read *)

Open Scope string_scope.

(* Bool *)

Ltac destr_bool :=
 intros; destruct_all bool; simpl in *; trivial; try discriminate.

Lemma not_true_iff_false: ∀ b: bool,
  b ≠ true ↔ b = false.
Proof.
  destr_bool; intuition.
Qed.

(* String *)

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : ∀ s, true = beq_string s s.
Proof. intros s. unfold beq_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem beq_string_true_iff : ∀ x y : string,
  beq_string x y = true ↔ x = y.
Proof.
   intros x y.
   unfold beq_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_string_false_iff : ∀ x y : string,
  beq_string x y = false
  ↔ x ≠ y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Lemma beq_stringP : ∀ x y, reflect (x = y) (beq_string x y).
Proof.
  intros x y. apply iff_reflect. rewrite beq_string_true_iff. reflexivity.
Qed.

(* Total maps *)

Definition total_map (A:Type) := string → A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (λ _, v).

Notation "{ ↦ d }" := (t_empty d) (at level 0).

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  λ x', if beq_string x x' then v else m x'.

Notation "m '&' { a ↦ x }" := 
  (t_update m a x) (at level 20).
Notation "m '&' { a ↦ x ; b ↦ y }" := 
  (t_update (m & { a ↦ x }) b y) (at level 20).
Notation "m '&' { a ↦ x ; b ↦ y ; c ↦ z }" := 
  (t_update (m & { a ↦ x ; b ↦ y }) c z) (at level 20).
Notation "m '&' { a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t }" :=
    (t_update (m & { a ↦ x ; b ↦ y ; c ↦ z }) d t) (at level 20).
Notation "m '&' { a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u }" :=
    (t_update (m & { a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t }) e u) (at level 20).
Notation "m '&' { a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u ; f ↦ v }" :=
    (t_update (m & { a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u }) f v) (at level 20).

Lemma t_apply_empty:  ∀ (A:Type) (x: string) (v: A), { ↦ v } x = v.
Proof.
  intros A x v. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : ∀ A (m: total_map A) x v,
  (m & {x ↦ v}) x = v.
Proof.
  intros A m x v. unfold t_update. rewrite <- beq_string_refl.
  reflexivity.
Qed.

Theorem t_update_neq : ∀ (X:Type) v x1 x2
                         (m : total_map X),
  x1 ≠ x2 →
  (m & {x1 ↦ v}) x2 = m x2.
Proof.
  intros X v x1 x2 m H. unfold t_update.
  apply beq_string_false_iff in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : ∀ A (m: total_map A) v1 v2 x,
    m & {x ↦ v1 ; x ↦ v2} = m & {x ↦ v2}.
Proof.
  intros A m v1 v2 x. unfold t_update.
  apply functional_extensionality. intros y.
  destruct (beq_string x y).
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : ∀ X x (m : total_map X),
  m & { x ↦ m x } = m.
Proof.
  intros X x m. unfold t_update. apply functional_extensionality.
  intros y. destruct (beq_stringP x y) as [H | H].
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : ∀ (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 ≠ x1 →
  m & { x2 ↦ v2 ; x1 ↦ v1 }
  =  m & { x1 ↦ v1 ; x2 ↦ v2 }.
Proof.
  intros X v1 v2 x1 x2 m H1.
  unfold t_update. apply functional_extensionality. intros y.
  destruct (beq_stringP x1 y) as [H | H].
  - rewrite H in H1. apply beq_string_false_iff in H1.
    rewrite H1. reflexivity.
  - reflexivity.
Qed.

(* Partial maps *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Notation "∅" := empty.

Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  m & { x ↦ (Some v) }.

Notation "m '&' {{ a ↦ x }}" := 
  (update m a x) (at level 20).
Notation "m '&' {{ a ↦ x ; b ↦ y }}" := 
  (update (m & {{ a ↦ x }}) b y) (at level 20).
Notation "m '&' {{ a ↦ x ; b ↦ y ; c ↦ z }}" := 
  (update (m & {{ a ↦ x ; b ↦ y }}) c z) (at level 20).
Notation "m '&' {{ a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t }}" :=
    (update (m & {{ a ↦ x ; b ↦ y ; c ↦ z }}) d t) (at level 20).
Notation "m '&' {{ a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u }}" :=
    (update (m & {{ a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t }}) e u) (at level 20).
Notation "m '&' {{ a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u ; f ↦ v }}" :=
    (update (m & {{ a ↦ x ; b ↦ y ; c ↦ z ; d ↦ t ; e ↦ u }}) f v) (at level 20).

Lemma apply_empty : ∀ (A: Type) (x: string),  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : ∀ A (m: partial_map A) x v,
    (m & {{ x ↦ v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : ∀ (X:Type) v x1 x2
                       (m : partial_map X),
  x2 ≠ x1 →
  (m & {{ x2 ↦ v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : ∀ A (m: partial_map A) v1 v2 x,
    m & {{ x ↦ v1 ; x ↦ v2 }} = m & {{x ↦ v2}}.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : ∀ X v x (m : partial_map X),
  m x = Some v →
  m & {{x ↦ v}} = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : ∀ (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 ≠ x1 →
  m & {{x2 ↦ v2 ; x1 ↦ v1}}
  = m & {{x1 ↦ v1 ; x2 ↦ v2}}.
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(* ################################################################# *)
(** * Useful tactics *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ => 
  match type of T with Prop =>
    solve [ 
      inversion H; 
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 2.

(* ################################################################# *)
(** * The original system: STLC with booleans *)

Module STLCBool.

(* Simple types *)
Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty → ty → ty
  .

(* Terms *)
Inductive tm : Type :=
    (* Pure STLC *)
  | var : string → tm                (* variable *)
  | app : tm → tm → tm              (* application *)
  | abs : string → ty → tm → tm    (* abstraction *)
    (* Booleans *)
  | tt  : tm                          (* true *)
  | ff  : tm                          (* false *)
  | ite : tm → tm → tm → tm        (* if-then-else *)
  .

(* Values *)
Inductive value : tm → Prop :=
  | v_abs : ∀ x T t, value (abs x T t)   (* abstractions *)
  | v_true : value tt                         (* true *)
  | v_false : value ff                        (* false *)
  .

Hint Constructors value.

(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst x s t :=
  match t with
  | var x' =>
      if beq_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if beq_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tt =>
      tt
  | ff =>
      ff
  | ite t1 t2 t3 =>
      ite ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Small-step operational semantics *)
Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | E_Beta : ∀ x T t12 v2,
      value v2 →
      (app (abs x T t12) v2) ⇒ [x:=v2]t12
  | E_App1 : ∀ t1 t1' t2,
      t1 ⇒ t1' →
      app t1 t2 ⇒ app t1' t2
  | E_App2 : ∀ v1 t2 t2',
      value v1 →
      t2 ⇒ t2' →
      app v1 t2 ⇒ app v1 t2'
  | E_IfTrue : ∀ t1 t2,
      (ite tt t1 t2) ⇒ t1
  | E_IfFalse : ∀ t1 t2,
      (ite ff t1 t2) ⇒ t2
  | E_If : ∀ t1 t1' t2 t3,
      t1 ⇒ t1' →
      (ite t1 t2 t3) ⇒ (ite t1' t2 t3)

where "t1 '⇒' t2" := (step t1 t2).

Hint Constructors step.

(* Typing context *)
Definition ctx := partial_map ty.

(* Typing judgments *)
Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : ctx → tm → ty → Prop :=
  | T_Var : ∀ Γ x T,
      Γ x = Some T →
      Γ ⊢ var x ∈ T
  | T_Abs : ∀ Γ x T11 T12 t12,
      Γ & {{ x ↦ T11 }} ⊢ t12 ∈ T12 →
      Γ ⊢ abs x T11 t12 ∈ Arrow T11 T12
  | T_App : ∀ T11 T12 Γ t1 t2,
      Γ ⊢ t1 ∈ Arrow T11 T12 →
      Γ ⊢ t2 ∈ T11 →
      Γ ⊢ app t1 t2 ∈ T12
  | T_True : ∀ Γ,
       Γ ⊢ tt ∈ Bool
  | T_False : ∀ Γ,
       Γ ⊢ ff ∈ Bool
  | T_If : ∀ t1 t2 t3 T Γ,
       Γ ⊢ t1 ∈ Bool →
       Γ ⊢ t2 ∈ T →
       Γ ⊢ t3 ∈ T →
       Γ ⊢ ite t1 t2 t3 ∈ T

where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

(* Free occurrences *)
Inductive appears_free_in : string → tm → Prop :=
  | afi_var : ∀ x,
      appears_free_in x (var x)
  | afi_app1 : ∀ x t1 t2,
      appears_free_in x t1 → 
      appears_free_in x (app t1 t2)
  | afi_app2 : ∀ x t1 t2,
      appears_free_in x t2 → 
      appears_free_in x (app t1 t2)
  | afi_abs : ∀ x y T11 t12,
      y ≠ x  →
      appears_free_in x t12 →
      appears_free_in x (abs y T11 t12)
  | afi_if1 : ∀ x t1 t2 t3,
      appears_free_in x t1 →
      appears_free_in x (ite t1 t2 t3)
  | afi_if2 : ∀ x t1 t2 t3,
      appears_free_in x t2 →
      appears_free_in x (ite t1 t2 t3)
  | afi_if3 : ∀ x t1 t2 t3,
      appears_free_in x t3 →
      appears_free_in x (ite t1 t2 t3).

Hint Constructors appears_free_in.

(* A term is _closed_ if it contains no free variables: *)
Definition closed (t:tm) := ∀ x, ¬ appears_free_in x t.

(* Context invariance *)
Lemma free_in_context : ∀ x t T Γ,
  appears_free_in x t →
  Γ ⊢ t ∈ T →
  ∃ T', Γ x = Some T'.
Proof.
  intros x t T Γ H H0.
  generalize dependent Γ. (* Quantify a variable again. *)
  generalize dependent T.
  induction H;
         intros; try solve [inversion H0; eauto].
  - (* afi_abs *)
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite update_neq in H7; assumption.
Qed.

Corollary typable_empty__closed : ∀ t T,
  ∅ ⊢ t ∈ T  →
  closed t.
Proof with eauto.
  intros t T H x contra.
  apply free_in_context with (T:=T) (Γ:=empty) in contra...
  destruct contra as [T' HT']. inversion HT'.
Qed.

(* Context invariance lemma *)
Lemma context_invariance : ∀ Γ Γ' t T,
  Γ ⊢ t ∈ T  →
  (∀ x, appears_free_in x t → Γ x = Γ' x) →
  Γ' ⊢ t ∈ T.
Proof with eauto.
  intros.
  generalize dependent Γ'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Γ'] we use to
       instantiate is [Γ & {{x↦T11}}] *)
    unfold update. unfold t_update.
    destruct (beq_string x x1) eqn: Hx0x1...
    rewrite beq_string_false_iff in Hx0x1. auto.
  - (* T_App *)
    apply T_App with T11...
Qed.

Corollary empty_context_invariance : ∀ Γ T t,
  ∅ ⊢ t ∈ T →
  Γ ⊢ t ∈ T.
Proof.
  intros Γ T t H.
  eapply context_invariance. eassumption.
  apply typable_empty__closed in H. unfold closed in H.
  intros. apply (H x) in H0. inversion H0.
Qed.

(* Substitution lemma *)
Lemma substitution_preserves_typing : ∀ Γ x U t v T,
  Γ & {{ x ↦ U }} ⊢ t ∈ T →
  ∅ ⊢ v ∈ U   →
  Γ ⊢ [x:=v]t ∈ T.
Proof with eauto.
  intros Γ x U t v T Ht Ht'.
  generalize dependent Γ. generalize dependent T.
  induction t; intros T Γ H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* tvar *)
    rename s into y. destruct (beq_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H2.
      inversion H2; subst.
      apply empty_context_invariance...
    + (* x≠y *)
      apply T_Var. rewrite update_neq in H2...
  - (* tabs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (beq_stringP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H5. apply H5.
    + (* x≠y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- beq_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

(* Main theorem of type preservation *)
Theorem preservation : ∀ t t' T,
  ∅ ⊢ t ∈ T →
  t ⇒ t' →
  ∅ ⊢ t' ∈ T.
Proof with eauto.
  remember (@empty ty) as Γ.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Γ; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

End STLCBool.

(* ################################################################# *)
(** * Q1: T-FunnyAbs *)

Module STLCBool_FunnyAbs.

(* Simple types *)
Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty → ty → ty
  .

(* Terms *)
Inductive tm : Type :=
    (* Pure STLC *)
  | var : string → tm                (* variable *)
  | app : tm → tm → tm              (* application *)
  | abs : string → ty → tm → tm    (* abstraction *)
    (* Booleans *)
  | tt  : tm                          (* true *)
  | ff  : tm                          (* false *)
  | ite : tm → tm → tm → tm        (* if-then-else *)
  .

(* Values *)
Inductive value : tm → Prop :=
  | v_abs : ∀ x T t, value (abs x T t)   (* abstractions *)
  | v_true : value tt                         (* true *)
  | v_false : value ff                        (* false *)
  .

Hint Constructors value.

(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst x s t :=
  match t with
  | var x' =>
      if beq_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if beq_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tt =>
      tt
  | ff =>
      ff
  | ite t1 t2 t3 =>
      ite ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Small-step operational semantics *)
Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | E_Beta : ∀ x T t12 v2,
      value v2 →
      (app (abs x T t12) v2) ⇒ [x:=v2]t12
  | E_App1 : ∀ t1 t1' t2,
      t1 ⇒ t1' →
      app t1 t2 ⇒ app t1' t2
  | E_App2 : ∀ v1 t2 t2',
      value v1 →
      t2 ⇒ t2' →
      app v1 t2 ⇒ app v1 t2'
  | E_IfTrue : ∀ t1 t2,
      (ite tt t1 t2) ⇒ t1
  | E_IfFalse : ∀ t1 t2,
      (ite ff t1 t2) ⇒ t2
  | E_If : ∀ t1 t1' t2 t3,
      t1 ⇒ t1' →
      (ite t1 t2 t3) ⇒ (ite t1' t2 t3)

where "t1 '⇒' t2" := (step t1 t2).

Hint Constructors step.

(* Typing context *)
Definition ctx := partial_map ty.

(* Typing judgments *)
Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : ctx → tm → ty → Prop :=
  | T_Var : ∀ Γ x T,
      Γ x = Some T →
      Γ ⊢ var x ∈ T
  | T_Abs : ∀ Γ x T11 T12 t12,
      Γ & {{ x ↦ T11 }} ⊢ t12 ∈ T12 →
      Γ ⊢ abs x T11 t12 ∈ Arrow T11 T12
  | T_App : ∀ T11 T12 Γ t1 t2,
      Γ ⊢ t1 ∈ Arrow T11 T12 →
      Γ ⊢ t2 ∈ T11 →
      Γ ⊢ app t1 t2 ∈ T12
  | T_True : ∀ Γ,
       Γ ⊢ tt ∈ Bool
  | T_False : ∀ Γ,
       Γ ⊢ ff ∈ Bool
  | T_If : ∀ t1 t2 t3 T Γ,
       Γ ⊢ t1 ∈ Bool →
       Γ ⊢ t2 ∈ T →
       Γ ⊢ t3 ∈ T →
       Γ ⊢ ite t1 t2 t3 ∈ T
    (* FunnyAbs *)
  | T_FunnyAbs : ∀ x t,
       ∅ ⊢ abs x Bool t ∈ Bool  (* <--- here is empty *)

where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

Notation ill := (abs "x" Bool (var "z")).

Theorem preservation_not_hold : ∃ t t' T,
  ∅ ⊢ t ∈ T ∧
  t ⇒ t' ∧
  ¬ (∅ ⊢ t' ∈ T).
Proof.
  exists (app (abs "x" Bool (abs "y" Bool (var "x"))) ill).  (* t *)
  exists (["x":=ill](abs "y" Bool (var "x"))).               (* t' *)
  exists (Arrow Bool Bool).                                  (* T *)
  split. eauto.
  split. auto.
  simpl. unfold not. intros H. inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  assert (Hcontra: empty "y" = (empty & {{ "y" ↦ Bool }}) "y") by
    (rewrite H0; auto).
  inversion Hcontra.
Qed.

End STLCBool_FunnyAbs.

(* ################################################################# *)
(** * Q2: T-FunnyAbs' *)

Module STLCBool_FunnyAbs'.

(* Simple types *)
Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty → ty → ty
  .

(* Terms *)
Inductive tm : Type :=
    (* Pure STLC *)
  | var : string → tm                (* variable *)
  | app : tm → tm → tm              (* application *)
  | abs : string → ty → tm → tm    (* abstraction *)
    (* Booleans *)
  | tt  : tm                          (* true *)
  | ff  : tm                          (* false *)
  | ite : tm → tm → tm → tm        (* if-then-else *)
  .

(* Values *)
Inductive value : tm → Prop :=
  | v_abs : ∀ x T t, value (abs x T t)   (* abstractions *)
  | v_true : value tt                         (* true *)
  | v_false : value ff                        (* false *)
  .

Hint Constructors value.

(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst x s t :=
  match t with
  | var x' =>
      if beq_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if beq_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tt =>
      tt
  | ff =>
      ff
  | ite t1 t2 t3 =>
      ite ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Small-step operational semantics *)
Reserved Notation "t1 '⇒' t2" (at level 40).

Inductive step : tm → tm → Prop :=
  | E_Beta : ∀ x T t12 v2,
      value v2 →
      (app (abs x T t12) v2) ⇒ [x:=v2]t12
  | E_App1 : ∀ t1 t1' t2,
      t1 ⇒ t1' →
      app t1 t2 ⇒ app t1' t2
  | E_App2 : ∀ v1 t2 t2',
      value v1 →
      t2 ⇒ t2' →
      app v1 t2 ⇒ app v1 t2'
  | E_IfTrue : ∀ t1 t2,
      (ite tt t1 t2) ⇒ t1
  | E_IfFalse : ∀ t1 t2,
      (ite ff t1 t2) ⇒ t2
  | E_If : ∀ t1 t1' t2 t3,
      t1 ⇒ t1' →
      (ite t1 t2 t3) ⇒ (ite t1' t2 t3)

where "t1 '⇒' t2" := (step t1 t2).

Hint Constructors step.

(* Typing context *)
Definition ctx := partial_map ty.

(* Typing judgments *)
Reserved Notation "Γ '⊢' t '∈' T" (at level 40).

Inductive has_type : ctx → tm → ty → Prop :=
  | T_Var : ∀ Γ x T,
      Γ x = Some T →
      Γ ⊢ var x ∈ T
  | T_Abs : ∀ Γ x T11 T12 t12,
      Γ & {{ x ↦ T11 }} ⊢ t12 ∈ T12 →
      Γ ⊢ abs x T11 t12 ∈ Arrow T11 T12
  | T_App : ∀ T11 T12 Γ t1 t2,
      Γ ⊢ t1 ∈ Arrow T11 T12 →
      Γ ⊢ t2 ∈ T11 →
      Γ ⊢ app t1 t2 ∈ T12
  | T_True : ∀ Γ,
       Γ ⊢ tt ∈ Bool
  | T_False : ∀ Γ,
       Γ ⊢ ff ∈ Bool
  | T_If : ∀ t1 t2 t3 T Γ,
       Γ ⊢ t1 ∈ Bool →
       Γ ⊢ t2 ∈ T →
       Γ ⊢ t3 ∈ T →
       Γ ⊢ ite t1 t2 t3 ∈ T
    (* FunnyAbs *)
  | T_FunnyAbs : ∀ x t Γ,
       Γ ⊢ abs x Bool t ∈ Bool    (* <--- Γ *)

where "Γ '⊢' t '∈' T" := (has_type Γ t T).

Hint Constructors has_type.

(* Free occurrences *)
Inductive appears_free_in : string → tm → Prop :=
  | afi_var : ∀ x,
      appears_free_in x (var x)
  | afi_app1 : ∀ x t1 t2,
      appears_free_in x t1 → 
      appears_free_in x (app t1 t2)
  | afi_app2 : ∀ x t1 t2,
      appears_free_in x t2 → 
      appears_free_in x (app t1 t2)
  | afi_abs : ∀ x y T11 t12,
      y ≠ x  →
      appears_free_in x t12 →
      appears_free_in x (abs y T11 t12)
  | afi_if1 : ∀ x t1 t2 t3,
      appears_free_in x t1 →
      appears_free_in x (ite t1 t2 t3)
  | afi_if2 : ∀ x t1 t2 t3,
      appears_free_in x t2 →
      appears_free_in x (ite t1 t2 t3)
  | afi_if3 : ∀ x t1 t2 t3,
      appears_free_in x t3 →
      appears_free_in x (ite t1 t2 t3).

Hint Constructors appears_free_in.

(* Context invariance lemma: note that we require
   `Γ x = Γ' x` only when `x in Γ`. *)
Lemma context_invariance : ∀ Γ Γ' t T,
  Γ ⊢ t ∈ T  →
  (∀ x, appears_free_in x t → Γ x ≠ None →
             Γ x = Γ' x) →
  Γ' ⊢ t ∈ T.
Proof with eauto.
  intros.
  generalize dependent Γ'.
  induction H; intros; auto.
  - (* T_Var *)
    apply T_Var. rewrite <- H0...
    rewrite H. unfold not. intros contra. inversion contra.
  - (* T_Abs *)
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Γ'] we use to
       instantiate is [Γ & {{x↦T11}}] *)
    unfold update. unfold t_update.
    destruct (beq_string x x1) eqn: Hx0x1...
    rewrite beq_string_false_iff in Hx0x1. auto.
  - (* T_App *)
    apply T_App with T11...
Qed.

Corollary empty_context_invariance : ∀ Γ T t,
  ∅ ⊢ t ∈ T →
  Γ ⊢ t ∈ T.
Proof.
  intros Γ T t H.
  eapply context_invariance. eassumption.
  unfold not. intros x _ contra. elimtype False. apply contra.
  auto.
Qed.

(* Substitution lemma *)
Lemma substitution_preserves_typing : ∀ Γ x U t v T,
  Γ & {{ x ↦ U }} ⊢ t ∈ T →
  ∅ ⊢ v ∈ U   →
  Γ ⊢ [x:=v]t ∈ T.
Proof with eauto.
  intros Γ x U t v T Ht Ht'.
  generalize dependent Γ. generalize dependent T.
  induction t; intros T Γ H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  - (* tvar *)
    rename s into y. destruct (beq_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      subst.
      rewrite update_eq in H2.
      inversion H2; subst. apply empty_context_invariance. assumption.
    + (* x≠y *)
      apply T_Var. rewrite update_neq in H2...
  - (* tabs *)
    rename s into y. rename t into T. apply T_Abs.
    destruct (beq_stringP x y) as [Hxy | Hxy].
    + (* x=y *)
      subst. rewrite update_shadow in H5. apply H5.
    + (* x≠y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_stringP y z) as [Hyz | Hyz]; subst; trivial.
      rewrite <- beq_string_false_iff in Hxy.
      rewrite Hxy...
Qed.

(* Main theorem of type preservation *)
Theorem preservation : ∀ t t' T,
  ∅ ⊢ t ∈ T →
  t ⇒ t' →
  ∅ ⊢ t' ∈ T.
Proof with eauto.
  remember (@empty ty) as Γ.
  intros t t' T HT. generalize dependent t'.
  induction HT;
       intros t' HE; subst Γ; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

End STLCBool_FunnyAbs'.

(* Answers Summary *)

Check STLCBool_FunnyAbs.preservation_not_hold.
Check STLCBool_FunnyAbs'.preservation.

(**-- End --**)
