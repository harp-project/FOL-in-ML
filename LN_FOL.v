From MatchingLogic Require Export Logic 
                                  Theories.Definedness
                                  DerivedOperators
                                  Theories.Sorts
                                  Helpers.FOL_helpers.
Import MatchingLogic.Syntax.Notations MatchingLogic.DerivedOperators.Notations.
Require Export extralibrary 
               Coq.Program.Wf 
               Lia 
               FunctionalExtensionality
               Program.Equality.
From stdpp Require Import countable.
Require Export Vector PeanoNat String.
Print Pattern.

Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.

Definition vec := t.

Lemma Forall_map T n (l : vec T n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  apply IHl; auto. simpl_existT. subst. auto.
Qed.

Theorem fold_left_map : forall T Q n (v : vec T n) (App : Q -> T -> Q) (start : Q) f,
  fold_left App start (map f v) = fold_left (fun Acc x => App Acc (f x)) start v.
Proof.
  induction v; intros; simpl; auto.
Qed.

(* Theorem fold_left_pointwise : forall T Q R n (v : vec T n) (App : Q -> T -> Q) 
                                     (start : Q) (f : Q -> Q),
  f (fold_left App start v) = fold_left (fun Acc x => App Acc (f x)) (f start) v. *)

Lemma map_Forall T n (l : vec T n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto.
  eapply IHl; eauto. simpl_existT. now subst.
Qed.

Lemma Forall_map_ext T n (l : vec T n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, In x l -> P x -> P (f x))
->
  Forall P l -> Forall P (map f l).
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto. apply H. constructor. auto.
  apply IHl; auto. intros. apply H. constructor 2. auto. auto. simpl_existT. now subst.
Qed.

Lemma map_Forall_ext T n (l : vec T n) : forall (P : T -> Prop) (f : T -> T),
  (forall x, In x l -> P (f x) -> P x)
->
  Forall P (map f l) -> Forall P l.
Proof.
  induction l; intros; constructor;
  inversion H0; subst. auto. apply H. constructor; auto. auto.
  eapply IHl; auto. intros. apply H. constructor 2. auto. exact H2. simpl_existT.
  now subst.
Qed.

Lemma Forall_impl_ext 
     : ∀ (A : Type) (P Q : A → Prop) n,
         ∀ l : vec A n, (∀ a : A, In a l -> P a → Q a) → Forall P l → Forall Q l.
Proof.
  induction l; intros; constructor; inversion H0; subst.
  apply H. constructor; auto. auto.
  apply IHl; auto. intros. apply H; auto. constructor 2. auto.
  simpl_existT. now subst.
Qed.

Global Hint Constructors Forall : core.

Class funcs_signature :=
  { funs : Type; funs_eqdec : EqDecision funs; ar_funs : funs -> nat }.

Coercion funs : funcs_signature >-> Sortclass.

Class preds_signature :=
  { preds : Type; preds_eqdec : EqDecision preds; ar_preds : preds -> nat }.

Class FOL_variables :=
  {
    vars : Type;
    var_eqdec : EqDecision vars;
    var_countable : Countable vars;
    var_fresh : list vars -> vars;
    var_fresh_is_fresh : 
      forall l, ~List.In (var_fresh l) l;
    nvar : string -> vars;
    nvar_inj : forall (s1 s2 : string), nvar s1 = nvar s2 -> s1 = s2;
  }.

Coercion preds : preds_signature >-> Sortclass.

Section fix_signature.

  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.

  Unset Elimination Schemes.
  Inductive term  : Type :=
  | bvar : nat -> term
  | fvar : vars -> term
  | func : forall (f : funs), vec term (ar_funs f) -> term.
  Set Elimination Schemes.

  Fixpoint fsubst_term (t0 t : term) (n : vars) : term :=
  match t0 with
  | fvar t' => if var_eqdec t' n then t else t0
  | bvar _ => t0
  | func f v => func f (map (fun x => fsubst_term x t n) v)
  end.

  Fixpoint bsubst_term (t0 t : term) (n : nat) : term :=
  match t0 with
  | bvar t' => match compare_nat t' n with
               | Nat_less _ _ _ => bvar t'
               | Nat_equal _ _ _ => t
               | Nat_greater _ _ _ => bvar t' (* (pred t') ? According to Leroy *)
               end
  | fvar _ => t0
  | func f v => func f (map (fun x => bsubst_term x t n) v)
  end.

  Context {Σ_preds : preds_signature}.

  Inductive form  : Type :=
  | fal : form
  | atom : forall (P : preds), vec term (ar_preds P) -> form
  | impl : form  -> form  -> form
  | exs : form  -> form.

  Fixpoint fsubst_form (phi : form) (t : term) (n: vars) : form :=
    match phi with
    | fal => fal
    | atom P v => atom P (map (fun x => fsubst_term x t n) v)
    | impl phi1 phi2 => impl (fsubst_form phi1 t n) (fsubst_form phi2 t n)
    | exs phi => exs (fsubst_form phi t n)
    end.

  Fixpoint bsubst_form (phi : form) (t : term) (n: nat) : form :=
    match phi with
    | fal => fal
    | atom P v => atom P (map (fun x => bsubst_term x t n) v)
    | impl phi1 phi2 => impl (bsubst_form phi1 t n) (bsubst_form phi2 t n)
    | exs phi => exs (bsubst_form phi t (S n))
    end.

  Inductive ForallT {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : ForallT P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> ForallT P l -> ForallT P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, vec A n -> Type :=
  | vec_inB {n} (v : vec A n) : vec_in a (@cons A a n v)
  | vec_inS a' {n} (v : vec A n) : vec_in a v -> vec_in a (@cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (fvar x)) ->
    (forall x, p (bvar x)) -> 
    (forall F v, (ForallT p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. fix strong_term_ind' 1. destruct t as [n|n|F v].
    - apply f2.
    - apply f1.
    - apply f3. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (fvar x)) -> (forall x, p (bvar x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. eapply term_rect'.
    - apply f1.
    - apply f2.
    - intros. apply f3. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (fvar x)) -> (forall x, p (bvar x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f2 f3. eapply term_rect'.
    - apply f1.
    - apply f2.
    - intros. apply f3. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

  Inductive wf_term : term -> nat -> Prop :=
  | wf_fvar x n : wf_term (fvar x) n
  | wf_bvar x n : x < n -> wf_term (bvar x) n
  | wf_funcs f v n :
    Vector.Forall (fun t => wf_term t n) v
  ->
    wf_term (func f v) n
  .

  Inductive wf_form : form -> nat -> Prop :=
  | wf_fal n : wf_form fal n
  | wf_pred P x n : 
    Vector.Forall (fun t => wf_term t n) x
  ->
    wf_form (atom P x) n
  | wf_impl f1 f2 n:
    wf_form f1 n -> wf_form f2 n
  ->
    wf_form (impl f1 f2) n
  | wf_exs f n :
    wf_form f (S n)
  ->
    wf_form (exs f) n.

  Theorem wf_increase_term :
    forall t n, wf_term t n -> forall n', n' >= n -> wf_term t n'.
  Proof.
    induction t; intros.
    * constructor.
    * constructor. inversion H. subst. lia.
    * inversion H. subst. constructor; auto. simpl_existT. subst.
      eapply Forall_impl_ext. 2: exact H4.
      intros. simpl in H1. eapply IH. 2: simpl in H2; exact H2. auto. lia.
  Qed.

  Theorem wf_increase :
    forall φ n, wf_form φ n -> forall n', n' >= n -> wf_form φ n'.
  Proof.
    induction φ; intros.
    * constructor.
    * inversion H; subst. constructor; auto. simpl_existT. subst.
      eapply Forall_impl. 2: exact H4.
      intros. simpl in H1. eapply wf_increase_term. exact H1. auto.
    * inversion H. subst. constructor. eapply IHφ1; eauto. eapply IHφ2; eauto.
    * inversion H. subst. constructor. eapply IHφ; eauto. lia.
  Qed.

  Theorem wf_term_subst :
    forall b t n, wf_term b (S n) -> wf_term t n ->
      wf_term (bsubst_term b t n) n.
  Proof.
    induction b; intros; inversion H; subst.
    * constructor.
    * simpl. break_match_goal.
      - now constructor.
      - auto.
      - lia.
    * simpl. constructor. simpl_existT. subst.
      eapply Forall_impl_ext in H4.
      2: { intros. eapply IH. exact H1. exact H2. exact H0. }
      clear H IH H0. induction v; simpl; constructor.
      inversion H4; auto.
      inversion H4; auto. simpl_existT. subst.
      now apply IHv.
  Qed.

  Theorem wf_form_subst :
    forall φ t n, wf_form φ (S n) -> wf_term t n ->
      wf_form (bsubst_form φ t n) n.
  Proof.
    induction φ; intros; simpl.
    * constructor.
    * inversion H. subst. constructor.
      eapply Forall_impl_ext in H4.
      2: { intros. eapply wf_term_subst. exact H2. exact H0. }
      simpl_existT. subst.
      clear H H0. induction v; simpl; constructor.
      inversion H4; auto.
      inversion H4; auto. simpl_existT. subst. now apply IHv.
    * inversion H. subst. constructor. apply IHφ1; auto. apply IHφ2; auto.
    * inversion H. subst. constructor. apply IHφ; auto. eapply wf_increase_term. exact H0.
      lia.
  Qed.

End fix_signature.

Section semantics.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Type.

  Class interp := B_I
    {
      i_f : forall f : funs, vec domain (ar_funs f) -> domain ;
      i_P : forall P : preds, vec domain (ar_preds P) -> bool ; (* for decidability *)
    }.
    Context {I : interp }.
    Definition env := vars -> domain. (* for free vars *)
    Variable failure : domain. (* for wrong evaluation!!! *)

    Fixpoint mmap {A B : Type} (f : A -> option B) {n : nat} (v : t A n) : option (t B n) :=
    match v in (t _ n0) return (option (t B n0)) with
    | nil => Some nil
    | @cons _ a n0 v' => match f a with
                         | None => None
                         | Some x => match mmap f v' with
                                     | None => None
                                     | Some xs => Some (cons x xs)
                                     end
                         end
    end.

    Fixpoint eval (rho : env) (t : term) : domain :=
      match t with
      | fvar s => rho s
      | bvar s => failure (* for wf terms, this is never used *)
      | func f v => i_f f (Vector.map (eval rho) v)
      end.

    Print evar_open.

    Definition update_env (ρ : env) (x : vars) (d : domain) : env :=
      fun v => if var_eqdec v x then d else ρ v.

    Import List.
    Import ListNotations.

    Fixpoint term_vars (t : term) : list vars :=
    match t with
     | bvar x => []
     | fvar x => [x]
     | func f x => Vector.fold_right (fun t Acc => term_vars t ++ Acc) x []
    end.

    Fixpoint form_vars (f : form) : list vars :=
    match f with
     | fal => []
     | atom P x => Vector.fold_right (fun t Acc => term_vars t ++ Acc) x []
     | impl x x0 => form_vars x ++ form_vars x0
     | exs x => form_vars x
    end.

    Fixpoint form_size (f : form) : nat :=
    match f with
     | fal => 0
     | atom P x => 0
     | impl x x0 => S (form_size x + form_size x0)
     | exs x => S (form_size x)
    end.

    Theorem subst_var_size :
      forall f x y, form_size f = form_size (bsubst_form f (fvar x) y).
    Proof.
      induction f; intros; auto; simpl.
      - now rewrite (IHf1 x y), (IHf2 x y).
      - now rewrite (IHf x (S y)).
    Qed.

    Program Fixpoint sat (rho : env) (phi : form) {measure (form_size phi)} : Prop :=
    match phi with
    | atom P v => i_P P (Vector.map (eval rho) v) = true
    | fal => False
    | impl phi psi => sat rho phi -> sat rho psi
    | exs phi => let x := var_fresh (form_vars phi) in
      exists d : domain, sat (update_env rho x d) (bsubst_form phi (fvar x) 0)
    end.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl. rewrite <- subst_var_size. lia. Defined.
    Next Obligation. Tactics.program_simpl. Defined.

    Proposition sat_atom : forall ρ P v, sat ρ (atom P v) = 
                                            (i_P P (Vector.map (eval ρ) v) = true).
    Proof. reflexivity. Qed.
    Proposition sat_fal : forall ρ, sat ρ fal = False.
    Proof. reflexivity. Qed.
    Proposition sat_impl : forall ρ φ₁ φ₂, sat ρ (impl φ₁ φ₂) = 
                                            (sat ρ φ₁ -> sat ρ φ₂).
    Proof.
      intros. unfold sat, sat_func.
      rewrite fix_sub_eq.
      Tactics.program_simpl. unfold projT1, projT2. intros.
      destruct x, f0; auto.
      rewrite H, H; auto.
      f_equal. extensionality d. rewrite H. auto.
    Qed.
    Proposition sat_exs : forall ρ φ, sat ρ (exs φ) = 
                        (let x := var_fresh (form_vars φ) in
      exists d : domain, sat (update_env ρ x d) (bsubst_form φ (fvar x) 0)).
    Proof.
      intros. unfold sat, sat_func.
      rewrite fix_sub_eq.
      Tactics.program_simpl. unfold projT1, projT2. intros.
      destruct x, f0; auto.
      rewrite H, H; auto.
      f_equal. extensionality d. rewrite H. auto.
    Qed.

    Notation "rho ⊨ phi" := (sat rho phi) (at level 20).

  Theorem sat_dec : forall φ ρ, {ρ ⊨ φ} + {~ ρ ⊨ φ}.
  Proof.
    induction φ; intros.
    * right. auto.
    * rewrite sat_atom. apply bool_dec.
    * destruct (IHφ1 ρ), (IHφ2 ρ).
      1, 3-4: left; rewrite sat_impl; intros; auto.
      congruence.
      right. rewrite sat_impl. intros. auto.
    * admit. (* TODO: technical, using size based induction *)
  Admitted.

End semantics.

Section proof_system.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Print evar_quantify.

  Fixpoint quantify_term (t : term) (v : vars) (n : nat) : term :=
  match t with
   | bvar x => bvar x
   | fvar x => if var_eqdec v x then bvar n else fvar x
   | func f x => func f (Vector.map (fun t => quantify_term t v n) x)
  end.


  Fixpoint quantify_form (φ : form) (v : vars) (n : nat) : form :=
  match φ with
   | fal => fal
   | atom P x => atom P (Vector.map (fun t => quantify_term t v n) x)
   | impl x x0 => impl (quantify_form x v n) (quantify_form x0 v n)
   | exs x => exs (quantify_form x v (S n))
  end.


  Reserved Notation "Γ ⊢_FOL form" (at level 50).
  Inductive Hilbert_proof_sys (Γ : (list form)): form -> Prop :=
  | AX (φ : form)             : wf_form φ 0 -> List.In φ Γ -> Γ ⊢_FOL φ
  | P1F (φ ψ : form)          : wf_form φ 0 -> wf_form ψ 0 -> Γ ⊢_FOL impl φ (impl ψ φ)
  | P2F (φ ψ ξ : form)        : wf_form φ 0 -> wf_form ψ 0 -> wf_form ξ 0 ->
    Γ ⊢_FOL impl (impl φ (impl ψ ξ)) (impl (impl φ ψ) (impl φ  ξ))
  | P3F (φ : form)            : wf_form φ 0 ->
    Γ ⊢_FOL impl (impl (impl φ fal) fal) φ
  | MPF (φ1 φ2 : form)        : wf_form φ1 0 -> wf_form (impl φ1 φ2) 0 ->
    Γ ⊢_FOL φ1 -> Γ ⊢_FOL impl φ1 φ2 -> Γ ⊢_FOL φ2
  | Q5F (φ : form) (t : term) :
    wf_form (exs φ) 0 -> wf_term t 0 ->
    Γ ⊢_FOL impl (bsubst_form φ t 0) (exs φ)
  | Q6F (φ ψ : form)(x : vars) : 
    wf_form φ 0 -> wf_form ψ 0 -> Γ ⊢_FOL impl φ ψ ->
    ~List.In x (form_vars ψ)
  ->
    Γ ⊢_FOL impl (exs (quantify_form φ x 0)) ψ
  where "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form).

End proof_system.

Section soundness_completeness.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Notation "rho ⊨_FOL phi" := (sat _ _ _ rho phi) (at level 50).
  Notation "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form) (at level 50).
  Check sat.
  Definition valid A phi :=
    forall D (fail : D) (I : interp D) (rho : vars -> D),(forall Phi, List.In Phi A -> sat D fail rho Phi)
      -> sat D fail rho phi.

  Theorem soundness :
    forall φ Γ, Γ ⊢_FOL φ -> valid Γ φ.
  Proof.
    intros. induction H; subst; unfold valid; intros.
    * now apply H1.
    * do 2 rewrite sat_impl. intros. auto.
    * repeat rewrite sat_impl. intros. apply H3; auto.
    * repeat rewrite sat_impl. intros.
      destruct (sat_dec D fail φ rho); auto.
      assert (~ sat D fail rho fal) by auto.
      assert (sat D fail rho fal).
      { apply H1. intros. congruence. }
      congruence.
    * unfold valid in *.
      apply IHHilbert_proof_sys1 in H3 as IH1.
      apply IHHilbert_proof_sys2 in H3 as IH2. rewrite sat_impl in IH2. now apply IH2.
    * rewrite sat_impl, sat_exs. intros. admit. (* TODO... *)
    * rewrite sat_impl, sat_exs. intros. unfold valid in *.
      apply IHHilbert_proof_sys in H3. rewrite sat_impl in H3. apply H3.
      destruct H4. simpl in H4.
      remember (var_fresh (form_vars (quantify_form φ x 0))) as FF.
      admit. (* TODO... *)
  Admitted.

  Theorem completeness :
    forall φ Γ, valid Γ φ -> Γ ⊢_FOL φ. Admitted.
End soundness_completeness.

Section FOL_ML_correspondence.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Inductive Symbols :=
  | sym_fun   (name : funs)
  | sym_pred  (name : preds)
  | sym_import_definedness (d : Definedness.Symbols).
  Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
  Proof.
    repeat decide equality.
    apply Σ_funcs.
    apply Σ_preds.
  Qed.

  Instance FOLVars : MLVariables := 
  {|
    Syntax.evar := vars;
    evar_eqdec := var_eqdec;
    svar_eqdec := var_eqdec;
    evar_countable := var_countable;
    svar_countable := var_countable;
    Syntax.svar := vars;
    evar_fresh := var_fresh;
    evar_fresh_is_fresh := var_fresh_is_fresh;
    svar_fresh := var_fresh;
    svar_fresh_is_fresh := var_fresh_is_fresh;
    nevar := nvar;
    nsvar := nvar;
    nevar_inj := nvar_inj;
    nsvar_inj := nvar_inj;
  |}.
  Instance sig : Signature := 
  {|
    variables := FOLVars;
    symbols := Symbols;
    sym_eq := Symbols_dec
  |}.

  Instance definedness_syntax : Definedness.Syntax :=
  {|
     Definedness.inj := sym_import_definedness;
  |}.

  Fixpoint convert_term (t : term) : Pattern :=
  match t with
   | bvar x => patt_bound_evar x
   | fvar x => patt_free_evar x
   | func f x => fold_left (fun Acc t => patt_app Acc (convert_term t)) 
                  (patt_sym (sym_fun f)) x
  end.

  Fixpoint convert_form (f : form) : Pattern :=
  match f with
   | fal => patt_bott
   | atom P x => fold_left (fun Acc t => patt_app Acc (convert_term t))
                  (patt_sym (sym_pred P)) x
   | impl x x0 => patt_imp (convert_form x) (convert_form x0)
   | exs x => patt_exists (convert_form x)
  end.

  Inductive AxName :=
  | AxDefinedness (name : Definedness.AxiomName)
  | AxFun (f : funs)
  | AxPred (p : preds).

  Fixpoint add_forall_prefix (n : nat) (base : Pattern) {struct n} : Pattern :=
  match n with
  | 0 => base
  | S n' => patt_forall (add_forall_prefix n' base)
  end.

  Fixpoint make_list1 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n :: make_list1 n'
  end.

  Fixpoint make_list0 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n' :: make_list0 n'
  end.

  Definition axiom (name : AxName) : Pattern :=
  match name with 
  | AxDefinedness name' => Definedness.axiom name'
  | AxFun f             => add_forall_prefix (ar_funs f) (patt_exists (patt_equal 
                          (List.fold_left
                            (fun Acc (x : nat) => patt_app Acc (patt_bound_evar x)) 
                            (make_list1 (ar_funs f)) (patt_sym (sym_fun f)))
                          (patt_bound_evar 0)))

  | AxPred p            => let φ := (List.fold_left
                            (fun Acc (x : nat) => patt_app Acc (patt_bound_evar x)) 
                            (make_list0 (ar_preds p)) (patt_sym (sym_pred p))) in
                          add_forall_prefix (ar_preds p) 
                            (patt_or (patt_equal φ patt_top) (patt_equal φ patt_bott))
  end.

  Definition named_axioms : NamedAxioms := {| NAName := AxName; NAAxiom := axiom; |}.
  Definition base_FOL_theory : Theory := theory_of_NamedAxioms named_axioms.

  Definition from_FOL_theory (Γ : list form) : Theory :=
    List.fold_right (fun x Acc => Ensembles.Union Pattern (Ensembles.Singleton Pattern (convert_form x)) Acc) base_FOL_theory Γ.

  Notation "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form) (at level 50).
  Notation "Γ ⊢_ML form" := (ML_proof_system Γ form) (at level 50).

  Theorem wf_term_FOL_ML : forall t n,
    wf_term t n -> is_true (well_formed_closed_aux (convert_term t) n 0).
  Proof.
    induction t using term_ind; intros.
    * constructor.
    * simpl. inversion H. now apply Nat.ltb_lt.
    * simpl. inversion H. simpl_existT. subst. clear H. 
      remember (@patt_sym sig (sym_fun F)) as start.
      assert (is_true (well_formed_closed_aux start n 0)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      - simpl. auto.
      - simpl. inversion H3. simpl_existT. subst. intros.
        epose proof (IHv _ H4 (start $ convert_term h)%ml). apply H0.
        simpl. rewrite H, IH; auto. constructor.
    Unshelve. intros. apply IH. now constructor 2. auto.
  Qed.

  Theorem wf_aux_FOL_ML : forall φ n,
    wf_form φ n -> is_true (well_formed_closed_aux (convert_form φ) n 0).
  Proof.
    induction φ; intros; auto.
    * simpl. inversion H. simpl_existT. subst. clear H.
      remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (well_formed_closed_aux start n 0)). { rewrite Heqstart. auto. }
      clear Heqstart. generalize dependent start. induction v.
      - simpl. auto.
      - simpl. inversion H3. simpl_existT. subst. intros.
        epose proof (IHv H4 (start $ convert_term h)%ml). apply H0.
        simpl. rewrite H, wf_term_FOL_ML; auto.
    * simpl. inversion H. subst. rewrite IHφ1, IHφ2; auto.
    * simpl. inversion H. subst. rewrite IHφ; auto.
  Qed.

  Theorem positive_term_FOL_ML : forall t,
    is_true (well_formed_positive (convert_term t)).
  Proof.
    induction t; intros; auto.
    * simpl. remember (@patt_sym sig (sym_fun F)) as start.
      assert (is_true (well_formed_positive start)) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. induction v; intros; auto.
      simpl. apply IHv.
      - intros. apply IH; auto. now constructor 2.
      - simpl. rewrite H, IH; auto. constructor.
  Qed.

  Theorem positive_form_FOL_ML : forall φ,
    is_true (well_formed_positive (convert_form φ)).
  Proof.
    induction φ; intros; auto.
    * simpl. remember (@patt_sym sig (sym_pred P)) as start.
      assert (is_true (well_formed_positive start)) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. induction v; intros; auto.
      simpl. apply IHv.
      simpl. rewrite H, positive_term_FOL_ML; auto.
    * simpl. rewrite IHφ1, IHφ2; auto.
  Qed.

  Corollary wf_FOL_ML_term : forall t,
    wf_term t 0 -> is_true (well_formed (convert_term t)).
  Proof.
    intros. unfold well_formed. unfold is_true.
    apply andb_true_intro. split.
    * apply positive_term_FOL_ML.
    * now apply wf_term_FOL_ML.
  Qed.

  Corollary wf_FOL_ML : forall φ,
    wf_form φ 0 -> is_true (well_formed (convert_form φ)).
  Proof.
    intros. unfold well_formed. unfold is_true.
    apply andb_true_intro. split.
    * apply positive_form_FOL_ML.
    * now apply wf_aux_FOL_ML.
  Qed.

  Theorem in_theory : forall Γ x,
    List.In x Γ -> Ensembles.In _ (from_FOL_theory Γ) (convert_form x).
  Proof.
    induction Γ; intros.
    * inversion H.
    * simpl. inversion H.
      - apply Ensembles.Union_introl. subst. apply Ensembles.In_singleton.
      - apply IHΓ in H0.
        now apply Ensembles.Union_intror.
  Qed.

  Hint Resolve wf_FOL_ML : core.
  Print exists_quantify.
  Print evar_quantify.
  Print quantify_form.
   Theorem quantify_term_correspondence :
    forall t n x, convert_term (quantify_term t x n) = 
                  evar_quantify x n (convert_term t).
  Proof.
    induction t; intros; auto; cbn.
    * now destruct (var_eqdec x0 x).
    * remember (@patt_sym sig (sym_fun F)) as start.
      rewrite fold_left_map.
      assert (start = evar_quantify x n start) by now rewrite Heqstart.
      clear Heqstart.
      generalize dependent start.
      induction v; intros; simpl; auto.
      rewrite IHv, IH.
  Admitted.

  Theorem quantify_form_correspondence :
    forall φ n x, convert_form (quantify_form φ x n) = 
                  evar_quantify x n (convert_form φ).
  Proof.
    induction φ; intros; auto; cbn.
    * admit. (* TODO: Technical, use quantify_term_correspondence *)
    * now rewrite IHφ1, IHφ2.
    * now rewrite IHφ.
  Admitted.

  (* Theorem form_vars_free_vars_in :
    forall φ x, List.In x (form_vars φ) -> x ∈ (free_evars (convert_form φ)).
  Proof.
  
  Admitted. *)
  Theorem term_vars_free_vars_notin :
    forall t x, ~List.In x (term_vars t) -> x ∉ (free_evars (convert_term t)).
  Proof.
    induction t using term_ind; intros.
    * simpl. intro. apply H. simpl. apply sets.elem_of_singleton_1 in H0. auto.
    * intro. simpl in H0. inversion H0.
    * simpl in H. simpl. 
      remember (@patt_sym sig (sym_fun F)) as start.
      assert (x ∉ free_evars start) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. 
      induction v; intros.
      - auto.
      - simpl. epose proof (IHv _ _ (start $ convert_term h)%ml _). clear IHv.
        apply H1.
      Unshelve.
        intros. apply IH. now constructor 2. auto.
        simpl in H. now apply notin_app_r in H.
        simpl in H. apply notin_app_l in H. apply IH in H.
        simpl. intro. apply elem_of_union in H1; inversion H1; contradiction.
        constructor.
  Qed.

  Theorem form_vars_free_vars_notin :
    forall φ x, ~List.In x (form_vars φ) -> x ∉ (free_evars (convert_form φ)).
  Proof.
    induction φ; intros; auto.
    * intro. inversion H0.
    * simpl in H. simpl. 
      remember (@patt_sym sig (sym_pred P)) as start.
      assert (x ∉ free_evars start) by now rewrite Heqstart.
      clear Heqstart. generalize dependent start. 
      induction v; intros.
      - auto.
      - simpl. epose proof (IHv _ (start $ convert_term h)%ml _). clear IHv.
        apply H1.
      Unshelve.
        simpl in H. now apply notin_app_r in H.
        simpl in H. apply notin_app_l in H. apply term_vars_free_vars_notin in H.
        simpl. intro. apply elem_of_union in H1; inversion H1; contradiction.
    * simpl in *. apply notin_app_r in H as H'. apply notin_app_l in H.
      apply IHφ1 in H. apply IHφ2 in H'.
      apply sets.not_elem_of_union. auto.
  Qed.

  Theorem bevar_subst_corr_term :
    forall b t n, convert_term (bsubst_term b t n) = 
                  bevar_subst (convert_term b) (convert_term t) n.
  Proof.
    induction b; intros; auto.
    * simpl. now break_match_goal.
    * simpl. admit. (* TODO: technical *)
  Admitted.

  Theorem bevar_subst_corr_form :
    forall φ t n, convert_form (bsubst_form φ t n) = 
                  bevar_subst (convert_form φ) (convert_term t) n.
  Proof.
    induction φ; intros; auto.
    * admit. (* TODO: technical, with bevar_subst_corr_term *)
    * simpl. now rewrite IHφ1, IHφ2.
    * simpl. now rewrite IHφ.
  Admitted.

  (*******************************************************)
  (* This has to go to FOL helpers *)
  Lemma conj_intro_meta_partial :
  ∀ (Γ : Theory) (A B : Pattern),
    is_true (well_formed A) → is_true (well_formed B) → Γ ⊢_ML A → Γ ⊢_ML patt_imp B (patt_and A B).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H1.
    - apply conj_intro; auto.
    Unshelve. all: auto.
  Qed.

  Lemma and_impl_patt :
    forall (A B C : Pattern) Γ, is_true (well_formed A) → is_true (well_formed B) → is_true (well_formed C) →
    Γ ⊢_ML A -> Γ ⊢_ML ((A and B) ---> C) -> Γ ⊢_ML (B ---> C).
  Proof.
    intros.
    Search patt_imp. Check syllogism_intro.
    eapply syllogism_intro with (B0 := patt_and A B); auto.
    apply conj_intro_meta_partial; auto.
  Qed.

  Lemma conj_intro2 (Γ : Theory) (A B : Pattern) :
    is_true (well_formed A) -> is_true (well_formed B) -> Γ ⊢_ML (A ---> (B ---> (B and A))).
  Proof.
    intros. eapply reorder_meta; auto.
    apply conj_intro; auto.
  Qed.

  Lemma conj_intro_meta_partial2 :
  ∀ (Γ : Theory) (A B : Pattern),
    is_true (well_formed A) → is_true (well_formed B) → Γ ⊢_ML A → Γ ⊢_ML patt_imp B (patt_and B A).
  Proof.
    intros.
    eapply (Modus_ponens _ _ _ _ _).
    - exact H1.
    - Search patt_and. apply conj_intro2; auto.
    Unshelve. all: auto.
  Qed.

  Lemma and_impl_patt2 :
    forall (A B C : Pattern) Γ, is_true (well_formed A) → is_true (well_formed B) → is_true (well_formed C) →
    Γ ⊢_ML A -> Γ ⊢_ML (patt_imp (patt_and B A) C) -> Γ ⊢_ML (patt_imp B C).
  Proof.
    intros.
    Search patt_imp. Check syllogism_intro.
    eapply syllogism_intro with (B0 := patt_and B A); auto.
    pose conj_intro_meta_partial2; auto.
  Qed.

  Lemma patt_and_comm :
    forall (A B : Pattern) Γ, is_true (well_formed A) → is_true (well_formed B)
  ->
    Γ ⊢_ML patt_and A B -> Γ ⊢_ML patt_and B A.
  Proof.
    intros.
    apply pf_conj_elim_r_meta in H1 as P1.
    apply pf_conj_elim_l_meta in H1 as P2. all: auto.
    apply conj_intro_meta; auto.
  Qed.

  Lemma patt_iff_implies_equal :
    forall φ1 φ2 Γ, is_true (well_formed φ1) -> is_true (well_formed φ2) ->
    Γ ⊢_ML (φ1 <---> φ2) -> Γ ⊢_ML (patt_equal φ1 φ2).
  Proof.
    intros. Print Application_context. Check A_implies_not_not_A_ctx. Print patt_total.
    epose proof (A_implies_not_not_A_ctx Γ (φ1 <---> φ2) (ctx_app_r box _)). 
    apply H2; auto. unfold patt_iff, patt_and, patt_or, patt_not.
    unfold well_formed, well_formed_closed in *.
    apply andb_true_iff in H. apply andb_true_iff in H0. destruct H, H0. cbn.
    now rewrite H, H0, H3, H4.
    Unshelve.
    auto.
  Qed.

  Lemma patt_equal_refl :
    forall φ Γ, is_true (well_formed φ) ->
    Γ ⊢_ML patt_equal φ φ.
  Proof.
    intros. pose proof (pf_iff_equiv_refl Γ φ H).
    apply patt_iff_implies_equal in H0; auto.
  Qed.

  (*******************************************************)

  (* Most important lemmas: *)
  Lemma exists_functional_subst :
    forall φ φ' Γ, 
      Γ ⊢_ML patt_imp (patt_and (instantiate (patt_exists φ) φ') (patt_exists (patt_equal φ' (patt_bound_evar 0)))) (patt_exists φ).
  Proof.
  
  Admitted.

  Lemma forall_functional_subst :
    forall φ φ' Γ, 
      Γ ⊢_ML patt_imp (patt_and (patt_forall φ) (patt_exists (patt_equal φ' (patt_bound_evar 0)))) (bevar_subst φ φ' 0).
  Proof.
  
  Admitted.

  Theorem ax_in :
    forall Γ F, Ensembles.In _ (from_FOL_theory Γ) (axiom F).
  Proof.
    induction Γ; intros.
    * simpl. unfold base_FOL_theory. econstructor.
      reflexivity.
    * simpl. apply Ensembles.Union_intror. apply IHΓ.
  Qed.

  Theorem ax_wf :
    forall F, is_true (well_formed (axiom F)).
  Proof.
    unfold axiom. intros.
    break_match_goal.
    * unfold Definedness.axiom. destruct name. simpl. constructor.
    * clear Heqa. remember (ar_funs f) as N. clear HeqN.
      induction N.
      - simpl. constructor.
      - cbn. admit. (* TODO: technical *)
  Admitted.

  Proposition term_functionality :
    forall t Γ, wf_term t 0 ->
      from_FOL_theory Γ ⊢_ML patt_exists (patt_equal (convert_term t) (patt_bound_evar 0)).
  Proof.
    induction t; intros.
    * simpl.
      pose proof (Ex_quan (from_FOL_theory Γ ) (patt_equal (patt_free_evar x) (patt_bound_evar 0)) x).
      simpl in H0. eapply Modus_ponens. 4: exact H0.
      all: auto.
      apply patt_equal_refl.
    * inversion H. inversion H1.
    * assert (from_FOL_theory Γ ⊢_ML axiom (AxFun F)). {
        apply hypothesis. apply ax_wf. apply ax_in.
      } simpl in H0.
      simpl. remember (@patt_sym sig (sym_fun F)) as start.
      clear Heqstart. generalize dependent start.
      assert (Forall (λ t : term, wf_term t 0) v). {
        inversion H. simpl_existT. now subst.
      } revert H0. clear H. induction v; intros.
      - cbn. simpl in H1. exact H1.
      - cbn in *. eapply (IHv _ _ (start $ convert_term h)%ml).
        clear IHv. inversion H0. simpl_existT. subst.
        specialize (IH h ltac:(constructor) Γ H4).
        remember (add_forall_prefix n
            (ex ,
             patt_equal
               (List.fold_left
                  (λ (Acc : Pattern) (x : nat), (Acc $ patt_bound_evar x)%ml)
                  (make_list1 n) (start $ patt_bound_evar (S n))%ml)
               BoundVarSugar.b0)) as A.
        pose proof (forall_functional_subst A (convert_term h) (from_FOL_theory Γ)).
        assert (from_FOL_theory Γ ⊢_ML (all , A and ex , patt_equal (convert_term h) BoundVarSugar.b0 )). { 
          apply conj_intro_meta; auto.
          - admit. (* TODO: technical, well_formedness *)
          - admit. (* TODO: technical, well_formedness *)
        }
        apply Modus_ponens in H; auto. 2-3: admit. (* TODO: technical, well_formedness *)
        simpl in H.
        admit. 
  Admitted.

  Theorem arrow_1 : forall (φ : form) (Γ : list form), 
    Γ ⊢_FOL φ
   -> 
    from_FOL_theory Γ ⊢_ML convert_form φ.
  Proof.
    intros φ Γ IH. induction IH; intros.
    * apply hypothesis. 2: now apply in_theory. now apply wf_FOL_ML.
    * simpl. apply P1; auto.
    * apply P2; auto.
    * apply P3; auto.
    * eapply Modus_ponens. 3: exact IHIH1. 3: exact IHIH2. all: auto.
      inversion H0. subst. auto.
    * simpl.
      epose proof (term_functionality t Γ H0).
      pose proof (exists_functional_subst (convert_form φ) (convert_term t) (from_FOL_theory Γ)).
      simpl in H1. rewrite bevar_subst_corr_form.
      eapply and_impl_patt2. 4: exact H1. 4: exact H2.
      all: apply wf_FOL_ML in H as H';auto.
      - simpl in H. clear H2 H1. unfold well_formed in *.
        apply andb_true_iff. apply andb_true_iff in H'. destruct H'.
        split.
        + simpl in *. now rewrite positive_term_FOL_ML.
        + unfold well_formed_closed. simpl.
          rewrite wf_term_FOL_ML; auto. eapply wf_increase_term. exact H0. lia.
      - rewrite <- bevar_subst_corr_form. apply wf_FOL_ML. inversion H. subst.
        apply wf_form_subst; auto.
    * simpl. rewrite quantify_form_correspondence. eapply Ex_gen; auto.
      apply form_vars_free_vars_notin. auto.
  Qed.


End FOL_ML_correspondence.

Section tests.

  Inductive PA_funcs : Type :=
    Zero : PA_funcs
  | Succ : PA_funcs
  | Plus : PA_funcs
  | Mult : PA_funcs.

  Theorem pa_funs_eqdec : EqDecision PA_funcs.
  Proof.
    unfold EqDecision, Decision; intros. decide equality.
  Qed.

  Definition PA_funcs_ar (f : PA_funcs ) :=
  match f with
   | Zero => 0
   | Succ => 1
   | Plus => 2
   | Mult => 2
   end.

  Inductive PA_preds : Type :=
    Eq : PA_preds.

  Theorem pa_preds_eqdec : EqDecision PA_preds.
  Proof.
    unfold EqDecision, Decision; intros. decide equality.
  Qed.

  Definition PA_preds_ar (P : PA_preds) :=
  match P with
   | Eq => 2
  end.

  Instance PA_funcs_signature : funcs_signature :=
  {| funs := PA_funcs ; funs_eqdec := pa_funs_eqdec; ar_funs := PA_funcs_ar |}.

  Instance PA_preds_signature : preds_signature :=
  {| preds := PA_preds ; preds_eqdec := pa_preds_eqdec; ar_preds := PA_preds_ar |}.

  Context {Σ_vars : FOL_variables}.
  Instance FOLVars2 : MLVariables := 
  {|
    Syntax.evar := vars;
    evar_eqdec := var_eqdec;
    svar_eqdec := var_eqdec;
    evar_countable := var_countable;
    svar_countable := var_countable;
    Syntax.svar := vars;
    evar_fresh := var_fresh;
    evar_fresh_is_fresh := var_fresh_is_fresh;
    svar_fresh := var_fresh;
    svar_fresh_is_fresh := var_fresh_is_fresh;
    nevar := nvar;
    nsvar := nvar;
    nevar_inj := nvar_inj;
    nsvar_inj := nvar_inj;
  |}.
  Instance sig2 : Signature := 
  {|
    variables := FOLVars;
    symbols := Symbols;
    sym_eq := Symbols_dec
  |}.

  Instance definedness_syntax2 : Definedness.Syntax :=
  {|
     Definedness.inj := sym_import_definedness;
  |}.

  Compute (add_forall_prefix 2) (patt_bott).
  Goal axiom (AxFun Mult) = patt_forall (patt_forall (patt_exists (patt_equal 
             (patt_app (patt_app (patt_sym (sym_fun Mult)) (patt_bound_evar 2)) (patt_bound_evar 1))
             (patt_bound_evar 0)))).
  Proof.
    simpl. reflexivity.
  Qed.
  Goal axiom (AxPred Eq) = patt_forall (patt_forall (patt_or (patt_equal 
             (patt_app (patt_app (patt_sym (sym_pred Eq)) (patt_bound_evar 1)) (patt_bound_evar 0)) patt_top)
             (patt_equal 
             (patt_app (patt_app (patt_sym (sym_pred Eq)) (patt_bound_evar 1)) (patt_bound_evar 0)) patt_bott))
             ).
  Proof.
    simpl. reflexivity.
  Qed.
  Goal convert_term (func Plus (cons (func Zero nil) (cons (func Succ (cons (func Zero nil) nil)) nil))) =
     patt_app (patt_app (patt_sym (sym_fun Plus)) (patt_sym (sym_fun Zero))) (patt_app (patt_sym (sym_fun Succ)) (patt_sym (sym_fun Zero))).
   Proof.
     simpl. reflexivity.
   Qed.

End tests.