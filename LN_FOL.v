From MatchingLogic Require Export Logic Theories.Definedness DerivedOperators Theories.Sorts.
Require Export extralibrary.
Require Export Lia.
From stdpp Require Import countable.
Require Export Vector PeanoNat String.
Print Pattern.

Definition vec := t.

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
    | exs phi => exs (bsubst_form phi t n)
    end.

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, vec A n -> Type :=
  | vec_inB {n} (v : vec A n) : vec_in a (@cons A a n v)
  | vec_inS a' {n} (v : vec A n) : vec_in a v -> vec_in a (@cons A a' n v).
  Hint Constructors vec_in : core.
  
  Lemma term_rect' (p : term -> Type) :
    (forall x, p (fvar x)) ->
    (forall x, p (bvar x)) -> 
    (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
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
    Forall (fun t => wf_term t n) v
  ->
    wf_term (func f v) n
  .

  Inductive wf_form : form -> nat -> Prop :=
  | wf_fal n : wf_form fal n
  | wf_pred P x n : 
    Forall (fun t => wf_term t n) x
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


End fix_signature.

Section semantics.
  Context {Σ_vars : FOL_variables}.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Variable domain : Type.

  Class interp := B_I
    {
      i_f : forall f : funs, vec domain (ar_funs f) -> domain ;
      i_P : forall P : preds, vec domain (ar_preds P) -> Prop ;
    }.
    Context {I : interp }.
    Definition env := vars -> domain. (* for free vars *)
    Variable failure : domain. (* for wrong evaluation!!! *)

Print Vector.map.

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
      - now rewrite (IHf x y).
    Qed.

    Program Fixpoint sat (rho : env) (phi : form) {measure (form_size phi)} : Prop :=
    match phi with
    | atom P v => i_P P (Vector.map (eval rho) v)
    | fal => False
    | impl phi psi => sat rho phi -> sat rho psi
    | exs phi => let x := var_fresh (form_vars phi) in
      exists d : domain, sat (update_env rho x d) (bsubst_form phi (fvar x) 0)
    end.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl; lia. Defined.
    Next Obligation. intros. subst. simpl. rewrite <- subst_var_size. lia. Defined.
    Next Obligation. Tactics.program_simpl. Defined.


    Notation "rho ⊨_FOL phi" := (sat rho phi) (at level 20).

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
    wf_form (exs φ) 0 ->
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
    forall φ Γ, Γ ⊢_FOL φ -> valid Γ φ. Admitted.
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
   | func f x => List.fold_left (fun Acc x => patt_app Acc x) (reverse (Vector.fold_left (fun Acc x => convert_term x :: Acc) [] x)) (patt_sym (sym_fun f))
  end.

  Fixpoint convert_form (f : form) : Pattern :=
  match f with
   | fal => patt_bott
   | atom P x => List.fold_left (fun Acc x => patt_app Acc x) (reverse (Vector.fold_left (fun Acc x => convert_term x :: Acc) [] x)) (patt_sym (sym_pred P))
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
  | S n' => add_forall_prefix n' (patt_forall base)
  end.

  Fixpoint make_list1 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => make_list1 n' ++ [n]
  end.

  Fixpoint make_list0 (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => make_list0 n' ++ [n']
  end.

  Definition axiom (name : AxName) : Pattern :=
  match name with 
  | AxDefinedness name' => Definedness.axiom name'
  | AxFun f             => add_forall_prefix (ar_funs f) (patt_exists (patt_equal 
                          (List.fold_right
                            (fun (x : nat) Acc => patt_app Acc (patt_bound_evar x)) 
                            (patt_sym (sym_fun f)) (make_list1 (ar_funs f)))
                          (patt_bound_evar 0)))

  | AxPred p            => let φ := (List.fold_right
                            (fun (x : nat) Acc => patt_app Acc (patt_bound_evar x)) 
                            (patt_sym (sym_pred p)) (make_list0 (ar_preds p))) in
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
    * simpl. admit. (* TODO: Technical *)
  Admitted.

  Theorem wf_aux_FOL_ML : forall φ n,
    wf_form φ n -> is_true (well_formed_closed_aux (convert_form φ) n 0).
  Proof.
    induction φ; intros; auto.
    * inversion H. subst.
      simpl. admit. (* TODO: Technical, use theorem wf_term_FOL_ML *)
    * simpl. inversion H. subst. rewrite IHφ1, IHφ2; auto.
    * simpl. inversion H. subst. rewrite IHφ; auto.
  Admitted.

  Theorem positive_term_FOL_ML : forall t,
    is_true (well_formed_positive (convert_term t)).
  Proof.
    induction t using term_ind; intros; auto.
    * simpl. induction v; intros; auto.
      simpl. (* TODO: Technical*)
  Admitted.

  Theorem positive_form_FOL_ML : forall φ,
    is_true (well_formed_positive (convert_form φ)).
  Proof.
    induction φ; intros; auto.
    * admit. (* TODO: Technical, use positive_term_FOL_ML *)
    * simpl. rewrite IHφ1, IHφ2; auto.
  Admitted.

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
    induction t using term_ind; intros; auto; cbn.
    * now destruct (var_eqdec x0 x).
    * admit. (* TODO: Technical *)
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
    * admit. (* TODO: Technical *)
  Admitted.

  Theorem form_vars_free_vars_notin :
    forall φ x, ~List.In x (form_vars φ) -> x ∉ (free_evars (convert_form φ)).
  Proof.
    induction φ; intros; auto.
    * intro. inversion H0.
    * intro. admit. (* TODO: Technical, use term_vars_free_vars_notin *)
    * simpl in *. apply notin_app_r in H as H'. apply notin_app_l in H.
      apply IHφ1 in H. apply IHφ2 in H'.
      apply sets.not_elem_of_union. auto.
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
    * simpl. admit. (* this requires much work, w/ axioms, additional theorems *)
    * simpl. rewrite quantify_form_correspondence. eapply Ex_gen; auto.
      apply form_vars_free_vars_notin. auto.
  Admitted.


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