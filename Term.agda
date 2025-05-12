open import Data.Bool
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.Nat
open import Data.Product
open import Data.String

module Term where

    Id : Set
    Id = String

    data Term : Set where
        natlit : ℕ → Term
        boollit : Bool → Term
        var : Id → Term
        abstr : Id → Term → Term
        app : Term → Term → Term
        letrec : Id → Term → Term → Term

    {-

    Scope : Set
    Scope = List Id

    --this env should probably be changing depending on what happens with the code but can't really think of how to do it properly
    data Term : (Γ : Scope) → Set where
        natlit  : {Γ : Scope} → ℕ                                           → Term Γ
        boollit : {Γ : Scope} → Bool                                        → Term Γ
        var     : {Γ : Scope} → (n : Id) → {n ∈ Γ}                          → Term Γ
        abstr   : {Γ Γ₁ : Scope} → (n : Id) → {n ∈ Γ₁} → Term Γ₁            → Term Γ
        app     : {Γ : Scope} → Term Γ → Term Γ                             → Term Γ
        letrec  : {Γ Γ₁ : Scope} → (n : Id) → {n ∈ Γ₁} → Term Γ₁ → Term Γ₁  → Term Γ

    -- ƛ_⇒_ : (n : Id) → {Γ Γ₁ : Scope} → {n ∈ Γ₁} → Term Γ₁ → Term Γ
    -- ƛ_⇒_ = abstr
    -}