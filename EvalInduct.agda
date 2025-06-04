open import Agda.Builtin.Nat
open import Data.List using (List; _∷_; [])


data Term : Set where
    TNat : Nat → Term
    TVar : Nat → Term
    TRVar : Term
    Abs : Term → Term
    App : Term → Term → Term
    LRec : Term → Term → Term


data Val : Set where
    nat : Nat → Val
    abs : Term → Val

Env : Set
Env = List Term

subst : Env → Term → Term
subst [] _ = TNat 999
subst (v ∷ e) (TVar zero) = v
subst (v ∷ e) (TVar (suc n)) = subst e (TVar n)
subst (v ∷ e) t = t

lookup : Env → Nat → Term
lookup [] n = TNat 999
lookup (x ∷ e) zero = x
lookup (x ∷ e) (suc n) = lookup e n

eval : Env → Term → Val
eval _ _ = nat 99