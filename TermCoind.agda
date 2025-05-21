{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Data.List using (List; []; _∷_) 
open import Data.Product
open import Function using (case_of_)

data Term : Set where
    TNat : Nat → Term
    TVar : Nat → Term
    TRVar : Nat → Term
    Abs : Term → Term
    App : Term → Term → Term
    LRec : Term → Term → Term

data TLabel : Set where
    TLNat TLVar TLAbs TLApp TLLRec : TLabel


mutual
    record RVar : Set where
        coinductive
        constructor mkRVar
        field
            label : TLabel
            subs : resolve label
            
    resolve : TLabel → Set
    resolve TLNat = Nat                                 --i don't know if nats should be this way
    resolve TLVar = RVar                                --either pointing to the tllrec or tlabs
    resolve TLAbs = Term                                --no closure but substitute
    resolve TLApp = Term × Term
    resolve TLLRec = RVar

    Env : Set
    Env = List RVar
open RVar public

--coinductive in env, then rest inductive, maybe Delay, outside of eval (return rvar) then convert

lookup : Env → Nat → RVar
lookup [] n .label = TLNat       --maybe introduce an error rvar or intermediate? for now just number lol
lookup [] n .subs = 999
lookup (x ∷ e) zero = x
lookup (x ∷ e) (suc n) = lookup e n


eval : Env → Term → RVar
eval _ (TNat n) .label = TLNat
eval _ (TNat n) .subs = n

eval e (TVar n) = lookup e n

eval e (TRVar n) = {!   !}

eval e (Abs t) .label = TLAbs
eval e (Abs t) .subs = t        --todo substitute env into t

eval e (App l a) = {!   !}

-- eval e (App l a) = let r = eval e l in
--     case label r of λ where
--         TLAbs → {! eval ((mkRVar ? ?) ∷ (proj₁ (subs r))) (proj₂ (subs r))  !} 
--         _ → {!   !}

eval e (LRec b i) = {!   !}


translate : Term → RVar
translate (TNat n) .label = TLNat
translate (TNat n) .subs = n

translate (TVar x) = {!   !}
translate (TVar x) = {!   !}

translate (TRVar x) = {!   !}   
translate (TRVar x) = {!   !}

translate (Abs n) = {!   !}
translate (Abs n) = {!   !}

translate (App n n₁) = {!   !}  
translate (App n n₁) = {!   !}

translate (LRec n n₁) = {!   !}
translate (LRec n n₁) = {!   !}