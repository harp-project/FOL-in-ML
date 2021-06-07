From MatchingLogic Require Import Logic Theories.Definedness DerivedOperators Theories.Sorts.
Require Import String Ascii.
From Coq Require Import String Ensembles.
From Coq Require Import VectorDef.
Require Import FOL.
Require Import Tarski.
From Coq.Logic Require Import FunctionalExtensionality.
From MatchingLogic Require Import Utils.extralibrary.
Require Import Coq.micromega.Lia.
From Coq Require Import Ensembles Bool.

Section FOL_ML.

Import MatchingLogic.Syntax.Notations.
Import MatchingLogic.Semantics.Notations.
Import MatchingLogic.ProofSystem.
From MatchingLogic Require Import FOL_helpers.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {eqdec_funcs : forall (s1 s2 : syms), {s1 = s2} + {s1 <> s2}}.
Context {eqdec_preds : forall (s1 s2 : preds), {s1 = s2} + {s1 <> s2}}.


(* TODO: Import Definedness *)
Inductive Symbols :=
| sym_fun   (name : syms)
| sym_pred  (name : preds)
| sym_import_definedness (d : Definedness.Symbols)
.

Lemma Symbols_dec : forall (s1 s2 : Symbols), {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
  - decide equality.
Qed.

Instance symbols_H : SymbolsH := {| SHSymbols := Symbols; SHSymbols_dec := Symbols_dec; |}.
Import Lists.List.

Definition mf (e : list nat) := S (list_max e).
Axiom my_evar_fresh : forall l, ~In (mf l) l.


Program Definition FOLVars : MLVariables := 
  {|
    Syntax.evar := nat;
    Syntax.svar := nat;
    evar_fresh := mf;
    evar_fresh_is_fresh := my_evar_fresh;
    svar_fresh := mf;
    svar_fresh_is_fresh := my_evar_fresh;
    nevar := fun s => 0;
    nsvar := fun s => 0;
  |}.
  Next Obligation. Admitted. Next Obligation. Admitted.

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

(* f (1,...,n) -----> ∀. ... ∀.∃.(sym f) $ (n+1) $ (n) $ ... $ 1 = 0 *)

Fixpoint add_forall_prefix (n : nat) (base : Pattern) : Pattern :=
  match n with
  | 0    => base
  | S n' => (add_forall_prefix (pred n') (patt_forall base))
  end.
Definition convert_sym_ax_form (size : nat) (t : term) : Pattern :=
  match t with
  | var n    => patt_bound_evar (size+1-n) (*Because we have the "y" with equality need to add 1 to them
                                             and need to reverse the original order of the argument list*)
  | func f v => patt_bott (*This branch is dead, because in the axiom there is only variables and no function*)
  end.

Definition convertf : nat -> nat + nat :=
  fun x => inr x.

(* We start the conversion from db index 0 *)
Fixpoint convert_term (f : nat -> nat + nat) (t : term) : Pattern :=
  match t with
  | var n'    => match (f n') with
                 | inl n => patt_bound_evar n
                 | inr n => patt_free_evar n
                 end
  | func g v => Vector.fold_left (patt_app) (patt_sym (sym_fun g)) 
                (Vector.map (convert_term f) v)
  end.
  
  
Compute (convert_term convertf $2).

Definition shift_ML (f : nat -> nat + nat) :=
  fun n =>
    match f n with
    | inl n => inl (S n)
    | inr n => inr n
    end.

Definition up_ML (f : nat -> nat + nat) :=
  fun n =>
    match n with
    | 0 => inl 0
    | S n' => (shift_ML f) n'
    end.
    
Fixpoint upn_ML (n : nat) (f : nat -> nat + nat) : nat -> nat + nat :=
  match n with
  | 0 => f
  | S n' => up_ML (upn_ML n' f)
  end.

Compute (convert_term (up_ML convertf) $2).

Fixpoint convert_form (g : nat -> nat + nat) (f : form) : Pattern :=
  match f with
  | fal         => patt_bott
  | atom p v    => Vector.fold_left (patt_app) (patt_sym (sym_pred p)) 
                   (Vector.map (convert_term g) v)
  | bin b f1 f2 => match b with
                   | Impl => patt_imp (convert_form g f1) (convert_form g f2)
                   | Conj => patt_and (convert_form g f1) (convert_form g f2)
                   | Disj => patt_or  (convert_form g f1) (convert_form g f2)
                   end
  | quant q f   => match q with
                   | Ex =>  patt_exists (convert_form (up_ML g) f)
                   | All => patt_forall (convert_form (up_ML g) f)
                   end
  end.
  
Fixpoint upn (n : nat) (t : term) : nat -> term :=
  match n with
  | 0 => t..
  | S n' => up (upn n' t)
  end.
  
Fixpoint size_FOL (phi:form) : nat :=
  match phi with
 | bin x x0 x1 => (size_FOL x0) + (size_FOL x1) + 1
 | quant x x0 => (size_FOL x0) + 1
 | _ => 0
 end.


  
Inductive AxName :=
| AxDefinedness (name : Definedness.AxiomName)
| AxFun (f : syms) (v : vec term (ar_syms f))    (*TODO: Delete v*)
| AxPred (p : preds) (v : vec term (ar_preds p)) (*TODO: Delete v*)
.

Definition axiom (name : AxName) : Pattern :=
match name with 
| AxDefinedness name' => Definedness.axiom name'
| AxFun f v           => add_forall_prefix (ar_syms f) (patt_exists (patt_equal 
                        (Vector.fold_left (patt_app) (patt_sym (sym_fun f)) 
                        (Vector.map (convert_sym_ax_form (ar_syms f)) v))
                        (patt_bound_evar 0)))

| AxPred p v          => add_forall_prefix (ar_preds p)
                         (patt_or 
                           (patt_equal (Vector.fold_left (patt_app) (patt_sym (sym_pred p)) 
                                       (Vector.map (convert_sym_ax_form (ar_preds p)) v)) 
                                       (patt_top))
                           (patt_equal (Vector.fold_left (patt_app) (patt_sym (sym_pred p)) 
                                       (Vector.map (convert_sym_ax_form (ar_preds p)) v)) 
                                       (patt_bott))
                         )
end.

Definition named_axioms : NamedAxioms := {| NAName := AxName; NAAxiom := axiom; |}.
Definition theory_FOL := theory_of_NamedAxioms named_axioms.

Require Import Hilbert.
Require Import VectorTech.

Notation "theory ⊢_ML pattern" := (ML_proof_system theory pattern) (at level 1).
Notation "theory_FOL ⊢_FOL form" := (Hilbert_proof_sys theory_FOL form) (at level 1).

(* Lemma blbabla :
  @bevar_subst (@sig Σ_funcs Σ_preds eqdec_funcs eqdec_preds)
   *)

Lemma blabla n (v : VectorDef.t term n): forall (p : Pattern) g (t : term) f n,
  (forall (p1 p2 p3 : Pattern), bevar_subst (f p1 p2) p3 n = f (bevar_subst p1 p3 n) (bevar_subst p2 p3 n)) 
  ->
  bevar_subst (Vector.fold_left f p (Vector.map g v)) (g t) n =
  (Vector.fold_left f (bevar_subst p (g t) n) (Vector.map (fun x => bevar_subst x (g t) n) (Vector.map g v))).
Proof. 
  induction v.
  - simpl. reflexivity.
  - intros. simpl. replace (f (bevar_subst p (g t) n0) (bevar_subst (g h) (g t) n0)) with (bevar_subst (f p (g h)) (g t) n0). 
  apply IHv. apply H. apply H.
  Qed.

Lemma convert_form_subst_helper1 : forall t,
(fun x => match x with |0 => t | (S n) => $n end) = scons t var.
Proof.
  intro. apply functional_extensionality. intro. destruct x.
  - reflexivity.
  - reflexivity.
Qed.

Lemma app_chain_wfca n m (v : VectorDef.t term m): forall (p : Pattern) g f,
  (forall (p1 p2: Pattern), well_formed_closed_aux (f p1 p2) n 0 = (andb (well_formed_closed_aux p1 n 0) (well_formed_closed_aux p2 n 0)))
  -> 
  well_formed_closed_aux (Vector.fold_left f p (Vector.map g v)) n 0 =
  (Vector.fold_left (andb) (well_formed_closed_aux p n 0) (Vector.map (fun x => well_formed_closed_aux x n 0) (Vector.map g v))).
Proof. 
  induction v.
  - simpl. reflexivity.
  - intros. simpl. replace (andb (well_formed_closed_aux p n 0) (well_formed_closed_aux (g h) n 0)) with (well_formed_closed_aux (f p (g h)) n 0).
  apply IHv. apply H. apply H.
Qed.

Lemma app_chain_wfp m (v : VectorDef.t term m): forall (p : Pattern) g f,
  (forall (p1 p2: Pattern), well_formed_positive (f p1 p2) = (andb (well_formed_positive p1) (well_formed_positive p2)))
  -> 
  well_formed_positive (Vector.fold_left f p (Vector.map g v)) =
  (Vector.fold_left (andb) (well_formed_positive p) (Vector.map (fun x => well_formed_positive x) (Vector.map g v))).
Proof. 
  induction v.
  - simpl. reflexivity.
  - intros. simpl. replace (andb (well_formed_positive p) (well_formed_positive (g h))) with (well_formed_positive (f p (g h))).
  apply IHv. apply H. apply H.
Qed.

Lemma provable_impl_totality: forall Γ φ,
  (well_formed φ = true) -> Γ ⊢_ML φ -> Γ ⊢_ML (patt_total φ).
Proof.
  intros. epose (A_implies_not_not_A_alt Γ φ _ H0).
  epose (Framing_right _ _ _ (patt_sym (Definedness.inj definedness)) m). 
  epose (Prop_bott_right _ (patt_sym (Definedness.inj definedness)) _).
  epose (syllogism_intro _ _ _ _ _ _ _ m0 m1).
  unfold patt_total. unfold patt_defined. unfold patt_not in m2. unfold patt_not. exact m2.
Admitted.

Lemma provable_implies_eq_refl: forall Γ φ,
  (well_formed φ = true) -> Γ ⊢_ML (patt_equal φ φ).
Proof.
  intros. assert (Γ ⊢_ML (patt_iff (φ) (φ))).
  - unfold patt_iff. epose (A_impl_A _ φ _). epose (conj_intro_meta _ _ _ _ _ m m). exact m0.
  - epose (provable_impl_totality _  (patt_iff φ φ) _ H0). unfold patt_equal. exact m.
Admitted.

Lemma provable_subst_eq: forall sz ψ Γ φ1 φ2 x,
  (well_formed_closed φ1) = true -> (well_formed_closed φ2) = true ->
  (well_formed_closed (free_evar_subst ψ φ1 x)) = true -> (well_formed_closed (free_evar_subst ψ φ2 x)) = true -> (le (size ψ) sz) ->
  Γ ⊢_ML (patt_equal φ1 φ2) -> Γ ⊢_ML (patt_equal (free_evar_subst ψ φ1 x) (free_evar_subst ψ φ2 x)).
Proof.
  induction sz; destruct ψ; intros.
  - simpl. destruct (numbers.nat_eq_dec x0 x) eqn:P.
    + simpl. assumption.
    + simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - simpl in H1. inversion H1.
  - simpl in H1. inversion H1.
  - simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - inversion H3.
  - simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - inversion H3.
  - inversion H3.
  - inversion H3.
  - simpl. destruct (numbers.nat_eq_dec x0 x) eqn:P.
    + simpl. assumption.
    + simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - simpl in H1. inversion H1.
  - simpl in H1. inversion H1.
  - simpl. apply provable_implies_eq_refl. unfold well_formed, well_formed_closed. auto.
  - simpl.
  Admitted.

Require Import Vector.
Theorem fold_left_map :
  forall (T T2 T3 : Type) n (l : vec T n) f (f2 : T -> T2 -> T3 -> T) d t2 t3,
  (forall a b t2 t3, f2 (f a b) t2 t3 = f (f2 a t2 t3) (f2 b t2 t3)) ->
  f2 (Vector.fold_left f d l) t2 t3 = Vector.fold_left f (f2 d t2 t3) (Vector.map (fun x => f2 x t2 t3) l).
Proof.
  induction l; intros; auto.
  intros. cbn.
  rewrite IHl; auto. rewrite H. auto.
Qed.

Theorem fold_left_map_gen :
  forall (T : Type) n (l : vec T n) f f2 d,
  (forall a b, f2 (f a b) = f (f2 a) (f2 b)) ->
  f2 (Vector.fold_left f d l) = Vector.fold_left f (f2 d) (Vector.map f2 l).
Proof.
  induction l; intros; auto.
  intros. cbn.
  rewrite IHl; auto. rewrite H. auto.
Qed.

Lemma term_subst_conversion: forall t0 t,
 bevar_subst (convert_term (up_ML convertf) t0) (convert_term convertf t) 0 =
 convert_term convertf t0`[t..].
Proof.
induction t0; intros.
- simpl. destruct (up_ML convertf x) eqn:P.
  + simpl. destruct (compare_nat n 0) eqn:D.
    * lia.
    * rewrite e in P. unfold up_ML, convertf in P. destruct x.
      -- simpl. reflexivity.
      -- inversion P.
    * (* x ≠ 0ból követketik, hogy t.. x az simán pred x lesz... *) admit.
  + simpl. destruct x eqn:D.
    * simpl. inversion P.
    * simpl. inversion P. reflexivity.
- simpl. epose (fold_left_map _ _ _ _ (map (convert_term (up_ML convertf)) v) patt_app bevar_subst ((patt_sym (sym_fun F))) (convert_term convertf t) 0). rewrite e.
  + simpl. repeat rewrite Vector.map_map. clear e. assert ((fun x : term => bevar_subst (convert_term (up_ML convertf) x) (convert_term convertf t) 0) = (fun x : term => convert_term convertf x`[t..])).
    * apply functional_extensionality. intros. erewrite IH. reflexivity. admit.
    * rewrite H. reflexivity.
  + simpl. reflexivity.
Admitted.

Lemma Finally: forall t t0 n,
bevar_subst (convert_term (upn_ML (S n) convertf) (t)) (convert_term convertf (t0)) n =
convert_term (upn_ML n convertf) (t)`[upn n (t0)].
Proof.
induction t; intros.
- simpl. destruct (up_ML (upn_ML n convertf) x) eqn:P.
  + (* simpl. *) destruct (compare_nat n0 n) eqn:D.
    * (* simpl. *) unfold up_ML, convertf in P. destruct n0.
      -- destruct x.
        ++ destruct n.
          ** lia.
          ** simpl. reflexivity.
        ++ unfold shift_ML in P. destruct (upn_ML n (fun x : nat => inr x) x) eqn:D1.
          ** inversion P.
          ** inversion P.
      -- destruct x.
        ++ destruct n.
          ** lia.
          ** simpl. inversion P.
        ++ (* cbn. *) unfold shift_ML in P. destruct (upn_ML n (fun x : nat => inr x) x) eqn:D1.
          ** inversion P. destruct n.
            --- simpl. lia.
            --- (* simpl. *) simpl in D1. subst. 
            (* ha x < n akkor jobb oldalon nem lesz helyettesítés, x < n kijön elvileg D1-ből. *) 
            simpl. Search ">>". admit.
          ** inversion P.
    * destruct n0.
      -- destruct x.
        ++ destruct n.
          ** simpl. reflexivity.
          ** lia.
        ++ rewrite <- e in P. simpl in P. unfold shift_ML in P. destruct (convertf x) eqn:D1.
          ** inversion P.
          ** inversion P.
     -- destruct x.
        ++ destruct n. 
          
Admitted.

Lemma Finally_formulas: forall f t0 n,
bevar_subst (convert_form (upn_ML (S n) convertf) (f)) (convert_term convertf (t0)) n =
convert_form (upn_ML n convertf) (f)[upn n (t0)].
Proof.
  induction f; intros.
  - reflexivity.
  - simpl. epose (fold_left_map _ _ _ _ (map (convert_term (up_ML (upn_ML n convertf))) v) patt_app bevar_subst ((patt_sym (sym_pred P))) (convert_term convertf t0) n). rewrite e. clear e. repeat rewrite Vector.map_map.
    + simpl. assert ((fun x : term => bevar_subst (convert_term (up_ML (upn_ML n convertf)) x) (convert_term convertf t0) n) = (fun x : term => convert_term (upn_ML n convertf) x`[upn n t0])).
      * apply functional_extensionality. intros. (* apply Finally.
      * simpl. rewrite H. reflexivity.
    + reflexivity.
  - simpl. destruct b; simpl; rewrite <- IHf1; rewrite <- IHf2; reflexivity.
  - simpl. destruct q.
    + simpl. epose (IHf t0 (S n)). simpl in e. rewrite e. reflexivity.
    + simpl. epose (IHf t0 (S n)). simpl in e. rewrite e. reflexivity. *)
Admitted.

Lemma inst_conversion: forall φ t,
instantiate (patt_exists (convert_form (up_ML convertf) φ)) (convert_term convertf t) = convert_form convertf (φ[t..]).
Proof.
induction φ; intros.
  - simpl. reflexivity.
  - simpl. rewrite Vector.map_map.  epose (fold_left_map _ _ _ _ (map (convert_term (up_ML convertf)) v) patt_app bevar_subst ((patt_sym (sym_pred P))) (convert_term convertf t) 0). rewrite e.
    + rewrite Vector.map_map. simpl. assert (((fun x : term => bevar_subst (convert_term (up_ML convertf) x) (convert_term convertf t) 0)) = (fun x : term => convert_term convertf x`[t..])).
      * apply functional_extensionality. intros. apply term_subst_conversion.
      * rewrite H. reflexivity.
    + reflexivity.
  - simpl. destruct b; rewrite <- IHφ1; rewrite <- IHφ2; reflexivity.
  - simpl. destruct q.
    + simpl. epose (Finally_formulas φ t 1). simpl in e. rewrite e. reflexivity.
    + simpl. epose (Finally_formulas φ t 1). simpl in e. rewrite e. reflexivity.
Qed.


(* bevar_subst (convert_form (upn_ML 2 convertf) (f)) (convert_term convertf (t0)) n =
   convert_form (upn_ML n convertf) (f)[up (t0..)] *)


Lemma arrow_1 (φ : form) (theory : (list form)):
theory ⊢_FOL φ -> theory_FOL ⊢_ML (convert_form convertf φ). 
Proof.
  intro. induction H; intros.
  - simpl. epose (_1 := P1 theory_FOL (convert_form convertf φ) (convert_form convertf ψ) _ _). apply _1.
  - simpl. epose (_1 := P2 theory_FOL (convert_form convertf φ) (convert_form convertf ψ) (convert_form convertf ξ) _ _ _). apply _1.
  - simpl. epose (_1 := P3 theory_FOL (convert_form convertf φ) _). apply _1.
  - epose (_1 := Modus_ponens theory_FOL _ _ _ _ (IHHilbert_proof_sys1) (IHHilbert_proof_sys2)). apply _1.
  - simpl. rewrite <- inst_conversion. simpl. epose (Ex_quan theory_FOL (convert_form (up_ML convertf) Φ) _). simpl in m. admit.
  - simpl.
   simpl in IHHilbert_proof_sys. epose (Ex_gen _ (convert_form (convertf) Φ[($x)..]) (convert_form (convertf) ψ) _ _ _ (IHHilbert_proof_sys) _). unfold exists_quantify in m. Check Ex_gen. unfold evar_quantify in m.
Admitted.
  
Lemma alma1: forall Φ x,
  evar_quantify x 0 (convert_form convertf Φ[($x)..]) = convert_form (up_ML convertf) Φ.
Proof.
  induction Φ; intros.
  - reflexivity.
  - simpl.
    erewrite (fold_left_map_gen). repeat rewrite Vector.map_map. cbn.
Admitted.

Lemma korte: forall n m,
var n = var m -> n = m.
Proof.
  induction n; intros.
Admitted.

Lemma alma2: forall x0 x,
(var (S x)) <> x0 -> (* Itt volt a baj a multkor, mert ha nem történik meg bal oldalon a behely. akkor lecsökkenti a .. így is úgy is x0-t, így ha x = pred x0, akkor azt IS kicseréli az evar quant... Emiatt kell az, hogy x egy olyan szám legyen, aminek a rákövetkezője ne legyen benne x0-ban (ha egy fv. akár) *)
evar_quantify x 0 (convert_term convertf x0`[($x)..]) = convert_term (up_ML convertf) x0.
Proof.
  induction x0; intros.
  destruct (up_ML convertf x) eqn:P.
    + destruct x.
      * simpl. inversion P. destruct (numbers.nat_eq_dec x0 x0) eqn:D.
        -- simpl. reflexivity.
        -- lia.
      * simpl. destruct (numbers.nat_eq_dec x0 x) eqn:D.
        -- simpl. inversion P.
        -- simpl. inversion P.
    + destruct x.
      * simpl. inversion P.
      * simpl. inversion P. destruct (numbers.nat_eq_dec x0 n) eqn:D.
        -- simpl. inversion P. subst. admit. (* S n ≠ S n contradiction *)
        -- simpl. reflexivity.
    + simpl. erewrite (fold_left_map_gen). simpl. repeat rewrite Vector.map_map. 
      2: reflexivity. 
Admitted.
  
(* evar_quantify (convert_term (up_ML convertf) t) 0 (convert_form convertf Φ[t..]) = convert_form (up_ML convertf) Φ *)
  
(*   Kelle gy olyan fv, hogy fun n => match n with | 0 => x (friss szabad vátltozó ...)
                                                   | S n => (up_ML fn) n
                                                   end. *)
                                                
                                                
  (* evar_quantify x 0 (convert_form convertf Φ) = convert_form (up_ML convertf) Φ *)





End FOL_ML.
Check Syntax.evar.



(* Testing with PA library *)

Require Import PA.

Notation "A → B" := (patt_imp A B) (at level 99, right associativity, B at level 200).
Notation "a $ b" := (patt_app a b) (at level 65, right associativity).
Notation "A /\ B" := (patt_and A B) (at level 80, right associativity).
Notation "A ‌\/ B" := (patt_or A B) (at level 85, right associativity).
Notation "∃, A" := (patt_exists A) (at level 55).
Notation "∀, A" := (patt_forall A) (at level 55).
Notation "A === B" := (patt_equal A B) (at level 100).
Notation "A ∈ B" := (patt_in A B) (at level 70).
Notation "'Bot'" := (patt_bott).
Notation "'fun' F" := (patt_sym (sym_fun F)) (at level 100).
Notation "'pred' P" := (patt_sym (sym_pred P)) (at level 100).

Context {eqdec_funcs1 : forall (s1 s2 : PA_funcs_signature), {s1 = s2} + {s1 <> s2}}.
Context {eqdec_preds1 : forall (s1 s2 : PA_preds_signature), {s1 = s2} + {s1 <> s2}}.



Compute (convert_form (convertf) ( σ $1 == σ $0 --> ∀ σ $0 == σ $1 )[var]).
Compute (convert_form (up_ML convertf) ( σ $1 == σ $0 --> ∀ σ $0 == σ $1 )).

(* Bal oldalra kell még egy evar_quantify x 0 ... *)
Compute ((convert_term (convertf) ($4)`[($2)..]) = (convert_term (up_ML convertf) ($4))).
Compute ((convert_form (up_ML convertf) ($4 == $3 --> ∀ $1 == $3)[($15)..]) = (convert_form (up_ML (up_ML convertf)) ($4 == $3 --> ∀ $1 == $3))).

Compute (instantiate (patt_exists (convert_form (up_ML convertf) ((((σ $0) == (σ $1)))))) (convert_term convertf ($5))).
Compute ((bevar_subst (convert_term (up_ML convertf) ($3)) (convert_term convertf ($2)) 0) = (convert_term convertf ($3)`[($2)..])).

Compute (($2 == $0 --> ∀ $3 == $3)[↑]).

Compute (convert_form (up_ML convertf) ($0 == $2 --> (∀ $1 == $0 --> $4 == $5))).
Compute (convert_form convertf ($0 == $2 --> (∀ $1 == $0 --> $4 == $5))).
Compute (convert_form (convertf) ($0 == $2 --> (∀ $1 == $0 --> $4 == $5))[($3)..]).

(* evar_quantify (convert_term (up_ML convertf) t) 0 (convert_form convertf Φ[t..]) = convert_form (up_ML convertf) Φ *)

Compute (convert_term (up_ML (up_ML convertf)) ($0)`[↑] = convert_term (up_ML convertf) ($0)).
Compute ((($0) == ($1) --> ∀ (($1)==($2) --> ($0) == ($0)))[($1)..]).

Compute ((($0) == ($1))[↑]).
Compute (convert_form (up_ML convertf) (($0) == ($1))[↑] = convert_form convertf (($0) == ($1))).
Compute (convert_form (up_ML convertf) (∀ ($0) == ($1) --> (∃ $5 == $0))[↑] = convert_form convertf (∀ ($0) == ($1) --> (∃ $5 == $0))).

Compute (instantiate ( (convert_form (convertf) (∃ σ $1 == σ $0 --> ∃ σ $1 == σ $0 --> σ $0 == σ $1 ))) (convert_term convertf ($3)) =
convert_form convertf ((σ $1 == σ $0 --> ∃ σ $1 == σ $0 --> σ $0 == σ $1 )[($3)..])).
(* Compute (instantiate (patt_exists (convert_form (up_ML convertf) φ)) (convert_term convertf t) = convert_form convertf (φ[t..])). *)

(* Ez a lényeg ... *)
Compute (bevar_subst (convert_term (up_ML (up_ML (up_ML convertf))) ($3)) (convert_term (convertf) ($2)) 2 = convert_term (up_ML(up_ML convertf)) ($3)`[up(up(($2)..))]).
Compute ((∀ ∀ σ $1 == σ $0 )).

(* Compute (bevar_subst (convert_term (up_ML convertf) t0) (convert_term convertf t) m = convert_term convertf t0`[upn m t]). *)

(* Elvileg ez működik *)
Compute ((upn_ML 3 (fun x : nat => inr (x))) (2) ).
Compute (convert_term (upn_ML 4 convertf) ($2)).
Compute (bevar_subst (convert_term (upn_ML 1 convertf) ($1)) (convert_term convertf ($2)) 0 =
convert_term (upn_ML 0 convertf) ($1)`[upn 0 ($2)]).
Compute (bevar_subst (convert_term (upn_ML 1 convertf) ($0)) (convert_term convertf ($4)) 0 =
convert_term (upn_ML 0 convertf) ($0)`[upn 0 ($4)]).
Compute (bevar_subst (convert_term (upn_ML 3 convertf) ($0)) (convert_term convertf ($3)) 2 =
convert_term (upn_ML 2 convertf) ($0)`[upn 2 ($3)]).
Compute (bevar_subst (convert_term (upn_ML 3 convertf) ($2)) (convert_term convertf ($0)) 2 =
convert_term (upn_ML 2 convertf) ($2)`[upn 2 ($0)]).
(* Compute (bevar_subst (patt_bound_evar (S 1)) (convert_term convertf t0) (S 2) =
convert_term (upn_ML (S 2) convertf) (upn (S 2) t0 (S x))).
(* Compute (bevar_subst (convert_term (upn_ML n+1 convertf) (t)) (convert_term convertf (t0)) n =
convert_term (upn_ML n convertf) (t)`[upn n (t0)]). *)

Compute ((bevar_subst (convert_term 1 ($3)) (convert_term 0 ($2)) 0) = (convert_term 0 ($3)`[($2)..])).
Compute ((bevar_subst (convert_term 1 ($1)) (convert_term 0 ($2)) 0) = (convert_term 0 ($1)`[($2)..])). *)
(* Compute ((convert_form (up_ML convertf) Φ) = (evar_quantify ?x 0 (convert_form convertf Φ))). *)


Compute (($2)`[($2)..]).



(* Converting all PA axioms into Pattern *)(*
Definition ML_PAX_zero_succ : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_zero_succ).
Definition ML_PAX_succ_inj : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_succ_inj).
Definition ML_PAX_add_zero : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_add_zero).
Definition ML_PAX_add_rec : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_add_rec).
Definition ML_PAX_mult_zero : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_mult_zero).
Definition ML_PAX_mult_rec : Pattern := ((@convert_form PA_funcs_signature PA_preds_signature 
                                            eqdec_funcs eqdec_preds)
                                            ax_mult_rec).

(* Merging converted axioms into ML theory *)
Definition ML_PA_Helper1 : Theory := Union (Pattern) 
                                    (Singleton Pattern ML_PAX_zero_succ) (Singleton Pattern ML_PAX_succ_inj).
Definition ML_PA_Helper2 : Theory := Union (Pattern) 
                                    (Singleton Pattern ML_PAX_add_zero) (Singleton Pattern ML_PAX_add_rec).
Definition ML_PA_Helper3 : Theory := Union (Pattern) 
                                    (Singleton Pattern ML_PAX_mult_zero) (Singleton Pattern ML_PAX_mult_rec).
Definition ML_PA_Helper4 : Theory := Union (Pattern) 
                                    (ML_PA_Helper1) (ML_PA_Helper2).
Definition ML_PA_Theory : Theory := Union (Pattern) 
                                    (ML_PA_Helper4) (ML_PA_Helper3). *)

(* Proving simple lemmas with the theory above *)
(* Testing first lemma conversion *)
(* Compute (convert_form  (∀ (zero ⊕ σ $0) == σ $0)). *)
(* Compute ((∀ (zero ⊕ σ $0) == σ $0)[(fun x => (match x with 
| 0  => var 1
| x' => var (S x') end))]). *)

(* ∀ (Eq ((Plus $ (Succ $ 0)) $ Zero) $ (Succ $ 0)) *)
(* 
Lemma zero_is_id_elem_of_plus_right: 
  ML_proof_system ML_PA_Theory (convert_form (∀ (zero ⊕ σ $0) == σ $0)).
Proof.
  simpl. 
   *)

(* End test. *)













