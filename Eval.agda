{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String using (_==_)

open import Term

module Eval where

    data Val : Set where
        nat  : ℕ     → Val
        bool : Bool → Val


    mutual
        record Ref : Set where
            coinductive
            constructor refr
            field
                id : Id
                ref : Term₂

        data Term₂ : Set where
            natlit : ℕ → Term₂
            boollit : Bool → Term₂
            var : Id → Term₂
            abstr : Id → Term₂ → Term₂
            app : Term₂ → Term₂ → Term₂
            recvar : Ref → Term₂
            letrec : Term₂ → Term₂
    
    open Ref public

    data Thunk : Set where
        val : Val → Thunk
        comp : Term₂ → Thunk
    
    Env : Set
    Env = List (Id × Thunk)

    mutual
        lookup : Env → Id → Maybe (Val × Env)
        lookup [] _ = nothing
        lookup e@((n , val x) ∷ xs) i = if n == i then just (x , e) else lookup xs i
        --todo
        lookup e@((n , comp x) ∷ xs) i = if n == i then {! do
            v ← eval x e where
                nothing → nothing
            just (v , (n , val v) ∷ xs)!} else lookup xs i

        --{-# NON_TERMINATING #-}

        eval : Term₂ → Env → Maybe (Val × Env)
        eval (var id) e = lookup e id
        --eval (letrec b) e = {!   !}
        eval (recvar r) e = eval (ref r) e
        eval _ _ = nothing  --do the rest as well
    
    {-
    eval : {Γ : Scope} → Term Γ → Env Γ → Val
    eval (natlit n) _ = nat n 
    eval (boollit b) _ = bool b
    eval _ _ = nat zero
    -} 