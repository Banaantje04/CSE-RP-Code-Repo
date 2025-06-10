\usepackage{agda}

\begin{code}
{-# OPTIONS --guardedness #-}

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
\end{code}

\begin{code}
    data IVal : Set where
        concrete : Val → IVal
        delay : RVal → IVal

    record RVal : Set where
        coinductive
        field
            rec : IVal
\end{code}

\begin{code}
open RVal

lookup : Env → Nat → ITerm
lookup [] n = ITNat 999
lookup (x ∷ e) zero = x
lookup (x ∷ e) (suc n) = lookup e n
\end{code}

\begin{code}
mutual
    {-# TERMINATING #-}
    eval : Env → ITerm → IVal
    eval e (ITNat x) = concrete (nat x)
    eval e (ITVar x) = delay (mkRVal e (lookup e x))
    eval e (ITRVar x) = delay (mkRVal e (term x))
    eval e (ITAbs t) = concrete (abs t e)
    eval e (ITApp t a) = delay applyFunR
        where
            applyFunR : RVal
            applyFunR .rec = applyFunction (delay (mkRVal e t)) a
    eval e (ITLRec x) = delay (mkRVal e (term x))

    mkRVal : Env → ITerm → RVal
    mkRVal e r .rec = eval e r

    applyFunction : IVal → ITerm → IVal
    applyFunction (concrete (abs t e₂)) a = delay (mkRVal (a ∷ e₂) t)
    applyFunction (delay x) a = delay applyFunctionC
        where
            applyFunctionC : RVal
            applyFunctionC .rec = applyFunction (rec x) a
    applyFunction n a = concrete (nat 999)
\end{code}

\begin{code}
{-# NON_TERMINATING #-}
runIVal : IVal → Val
runIVal (concrete x) = x
runIVal (delay x) = runIVal (rec x)
\end{code}

\begin{code}
runIValFuel : Nat → IVal → Val
runIValFuel zero _ = nat 999
runIValFuel (suc f) (concrete x) = x
runIValFuel (suc f) (delay x) = runIValFuel f (rec x)
\end{code}