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
| Q5F (Φ : form) (t : term) : Γ ⊢_FOL (Φ[t..]) ->  Γ ⊢_FOL (∃ Φ) (* TODO: Ask if it's a good instantiate *)
| Q6F (Φ ψ : form)          : Γ ⊢_FOL ((Φ --> ψ)) ->  Γ ⊢_FOL ((∃ Φ) --> ψ)
where "Γ ⊢_FOL form" := (Hilbert_proof_sys Γ form).

(* TODO: test this *)

End Hilbert.
(* fun x => match compare_nat x 0 with
           | Nat_less _ _ _ => var 0
           | Nat_equal _ _ _ => t
           | Nat_greater _ _ _ => var (pred x) end *)