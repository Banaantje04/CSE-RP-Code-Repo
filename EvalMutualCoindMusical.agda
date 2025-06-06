{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Data.List using (List; []; _∷_) 
open import Data.Product
open import Function using (case_of_)
open import Codata.Musical.Notation


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
        delay : ∞ IVal → IVal

    -- record RVal : Set where
    --     coinductive
    --     field
    --         rec : IVal
-- open RVal

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
    eval e (ITVar x) = delay (♯ (eval e (lookup e x)))
    eval e (ITRVar x) = delay (♯ (eval e (term x)))
    eval e (ITAbs t) = concrete (abs t e)
    eval e (ITApp t a) = delay (♯ id (delay (♯ (eval e t))))
        -- where
            -- applyFunR : RVal
            -- applyFunR .rec = applyFunction (delay (mkRVal e t)) a
    -- eval e (ITLRec x) = delay (mkRVal e (term x))
    eval e (ITLRec x) = delay (♯ eval e (term x))

    -- mkRVal : Env → ITerm → RVal
    -- mkRVal e r .rec = eval e r
    id : IVal → IVal
    id c = c

    applyFunction : IVal → ITerm → IVal
    -- applyFunction (concrete (abs t e₂)) a = delay (mkRVal (a ∷ e₂) t)
    applyFunction (concrete (abs t e₂)) a = delay {!   !}
    applyFunction (delay x) a = delay {!   !}
        -- where
            -- applyFunctionC : RVal
            -- applyFunctionC .rec = applyFunction (rec x) a
    applyFunction n a = concrete (nat 999)


mutual
    test : IVal → IVal
    test (concrete x) = concrete x
    test (delay x) = delay (♯ test1 (delay (♯ (♭ x))))
    
    test1 : IVal → IVal
    test1 (concrete x) = concrete x
    test1 (delay x) = delay {!   !}


mutual
    translateLRec : Term true → Term true → ITerm
    translateLRec r (TNat n) = ITNat n
    translateLRec r (TVar x) = ITVar x
    translateLRec r TRVar = ITRVar (mkRTerm r r)
    translateLRec r (Abs n) = ITAbs (translateLRec r n)
    translateLRec r (App n b) = ITApp (translateLRec r n) (translateLRec r b)

    mkRTerm : Term true → Term true → RTerm
    mkRTerm r b .term = translateLRec r b

translate : Term false → ITerm
translate (TNat n) = ITNat n
translate (TVar x) = ITVar x
translate (Abs n) = ITAbs (translate n)
translate (App n b) = ITApp (translate n) (translate b)
translate (LRec r b) = ITLRec (mkRTerm r b)


-- {-# NON_TERMINATING #-}
-- runIVal : IVal → Val
-- runIVal (concrete x) = x
-- runIVal (delay x) = runIVal (rec x)


-- runIValFuel : Nat → IVal → Val
-- runIValFuel zero _ = nat 999
-- runIValFuel (suc f) (concrete x) = x
-- runIValFuel (suc f) (delay x) = runIValFuel f (rec x)


-- --coinductive in env, then rest inductive, maybe Delay, outside of eval (return rvar) then convert

-- lookup : Env → Nat → RTerm
-- lookup [] n .label = TLNat       --maybe introduce an error rvar or intermediate? for now just number lol
-- lookup [] n .subs = 999
-- lookup (x ∷ e) zero = x
-- lookup (x ∷ e) (suc n) = lookup e n


-- eval : {rec : Bool} → Env → Term rec → RTerm
-- eval _ (TNat n) .label = TLNat
-- eval _ (TNat n) .subs = n

-- eval e (TVar n) = lookup e n

-- eval e TRVar = {!   !}

-- eval e (Abs t) .label = TLAbs
-- eval e (Abs t) .subs = {!   !}        --todo substitute env into t

-- eval e (App l a) = {!   !}

-- -- eval e (App l a) = let r = eval e l in
-- --     case label r of λ where
-- --         TLAbs → {! eval ((mkRVar ? ?) ∷ (proj₁ (subs r))) (proj₂ (subs r))  !} 
-- --         _ → {!   !}

-- eval e (LRec b i) = {!   !}