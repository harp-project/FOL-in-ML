Require Import Tarski.
Require Import List.
From MatchingLogic Require Import Utils.extralibrary.

Section Hilbert.
Context {Σ_funcs_hilbert : funcs_signature}.
Context {Σ_preds_hilbert : preds_signature}.

Reserved Notation "Γ ⊢_FOL form" (at level 1).
Inductive Hilbert_proof_sys (Γ : (list form)): form -> Prop :=
| P1F (φ ψ : form)          : Γ ⊢_FOL (φ --> (ψ --> φ))
| P2F (φ ψ ξ : form)        : Γ ⊢_FOL (((φ --> (ψ --> ξ))) --> ((φ --> ψ) --> (φ --> ξ)))
| P3F (φ : form)            : Γ ⊢_FOL (((φ --> fal ) --> fal )--> φ)
| MPF (φ1 φ2 : form)        : Γ ⊢_FOL φ1 -> Γ ⊢_FOL (φ1 --> φ2) -> Γ ⊢_FOL φ2
| Q5F (Φ : form) (t : term) : Γ ⊢_FOL (Φ[t..]) ->  Γ ⊢_FOL (∃ Φ)
| Q6F (Φ ψ : form)(x : nat) : Γ ⊢_FOL ((Φ[($x)..] --> ψ)) ->  Γ ⊢_FOL ((∃ Φ) --> ψ)
where "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form).

End Hilbert.

