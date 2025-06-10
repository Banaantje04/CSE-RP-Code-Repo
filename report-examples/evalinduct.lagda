\usepackage{agda}

\begin{code}
open import Agda.Builtin.Nat
open import Data.List using (List; _∷_; [])
open import Function using (case_of_)


data Term : Set where
    TNat : Nat → Term
    TVar : Nat → Term
    Abs : Term → Term
    App : Term → Term → Term
    LRec : Term → Term → Term



Env : Set
Env = List Term

data Val : Set where
    nat : Nat → Val
    abs : Term → Env → Val

-- subst : Env → Term → Term
-- subst [] _ = TNat 999
-- subst (v ∷ e) (TVar zero) = v
-- subst (v ∷ e) (TVar (suc n)) = subst e (TVar n)
-- subst (v ∷ e) t = t

lookup : Env → Nat → Term
lookup [] n = TNat 999
lookup (x ∷ e) zero = x
lookup (x ∷ e) (suc n) = lookup e n
\end{code}

\begin{code}
{-# NON_TERMINATING #-}
eval : Env → Term → Val
eval e (TNat x) = nat x
eval e (TVar x) = eval e (lookup e x)
eval e (Abs t) = abs t e
eval e (App t t₁) = case eval e t of λ where 
    (nat x) → nat 999
    (abs x e₁) → eval (t₁ ∷ e) x
eval e (LRec t t₁) = eval (t ∷ e) t₁
\end{code}



\begin{code}
evalFuel : Nat → Env → Term → Val
evalFuel zero _ _ = nat 999
evalFuel (suc n) e (TNat x) = nat x
evalFuel (suc n) e (TVar x) = evalFuel n e (lookup e x)
evalFuel (suc n) e (Abs t) = abs t e
evalFuel (suc n) e (App t t₁) = case evalFuel n e t of λ where 
    (nat x) → nat 999
    (abs x e₁) → evalFuel n (t₁ ∷ e) x
evalFuel (suc n) e (LRec t t₁) = evalFuel n (t ∷ e) t₁
\end{code}