\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness --allow-unsolved-metas #-}
open import Agda.Builtin.Nat

module syntaxhighlighting where

\end{code}

\begin{code}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

\end{code}

\begin{code}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Data.List using (List; []; _∷_) 
open import Data.Product
open import Function using (case_of_)


data Term : (rec : Bool) → Set where
    TNat : {rec : Bool} → Nat → Term rec
    TVar : {rec : Bool} → Nat → Term rec
    TRVar : Term true
    Abs : {rec : Bool} → Term rec → Term rec
    App : {rec : Bool} → Term rec → Term rec → Term rec
    LRec : Term true → Term true → Term false

mutual
    data ITerm : Set where
        ITNat : Nat → ITerm
        ITVar : Nat → ITerm
        ITRVar : RTerm → ITerm
        ITAbs : ITerm → ITerm
        ITApp : ITerm → ITerm → ITerm
        ITLRec : RTerm → ITerm

    record RTerm : Set where
        coinductive
        constructor RTermCtr
        field
            term : ITerm
open RTerm

Env : Set
Env = List ITerm

data Val : Set where --todo maybe add error val
    nat : Nat → Val
    abs : ITerm → Env → Val

mutual
    data IVal : Set where
        concrete : Val → IVal
        delay : RVal → IVal

    record RVal : Set where
        coinductive
        field
            rec : IVal
open RVal

--hard to fill the holes in this, so function closures instead of substitution
-- subst : Env → ITerm → ITerm
-- subst [] t = t
-- subst (v ∷ e) (ITVar zero) = v
-- subst (v ∷ e) (ITVar (suc n)) = subst e (ITVar n)
-- subst (v ∷ e) (ITAbs t) = {!   !}
-- subst e₁@(v ∷ e) (ITApp t t₁) = ITApp (subst {!   !} t) (subst e₁ t₁)
-- subst e₁@(v ∷ e) (ITLRec x) = ITLRec substLRec
--     where
--         substLRec : RTerm
--         substLRec .term = subst e₁ (term x)
-- subst (v ∷ e) t = t

lookup : Env → Nat → ITerm
lookup [] n = ITNat 999
lookup (x ∷ e) zero = x
lookup (x ∷ e) (suc n) = lookup e n

mutual
    -- {-# TERMINATING #-}  --todo remove this, i have this mostly to be able to continue
    eval : Env → ITerm → IVal
    eval e (ITNat x) = concrete (nat x)
    eval e (ITVar x) = delay (mkRVal e (lookup e x))
    eval e (ITRVar x) = delay (mkRVal e (term x))
    eval e (ITAbs t) = concrete (abs t e)
\end{code}
\begin{code}
    eval e (ITApp t a) = case (eval e t) of λ where
        (concrete (abs x y)) → delay (mkRVal (a ∷ e) t)
        (delay x) → {!   !}
        n → n
\end{code}
\begin{code}
    eval e (ITLRec x) = delay (mkRVal e (term x))

    mkRVal : Env → ITerm → RVal
    mkRVal e r .rec = eval e r

\end{code}

\end{document}