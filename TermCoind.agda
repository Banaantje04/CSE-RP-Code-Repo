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

data TLabel : Set where
    TLNat TLVar TLRVar TLAbs TLApp TLLRec : TLabel


mutual
    record RTerm : Set where
        coinductive
        constructor mkRVar
        field
            label : TLabel
            rec : Bool
            subs : resolve label rec
            
    resolve : TLabel → Bool → Set
    resolve TLNat _ = Nat                                 --i don't know if nats should be this way
    resolve TLVar _ = Nat
    resolve TLRVar _ = RTerm                                --either pointing to the tllrec or tlabs
    resolve TLAbs rec = Term rec                                --no closure but substitute
    resolve TLApp rec = Term rec × Term rec
    resolve TLLRec _ = RTerm

open RTerm public

data Val : Set where
    nat : Nat → Val

Env : Set
Env = List RTerm

eval : Env → RTerm → Val
eval e t with (label t , rec t) , subs t
... | (TLNat , n) , r = {!nat (subs t)  !}
... | _ = {!   !}

-- evalNat : (l : TLabel) → RTerm .label {TLNat} .subs {Nat} → Nat
-- evalNat = ?


translateLRec : Term true → Term true → RTerm
translateLRec _ _ .rec = true

translateLRec r (TNat n) .label = TLNat
translateLRec r (TNat n) .subs = n

translateLRec r (TVar x) .label = TLVar
translateLRec r (TVar x) .subs = x

translateLRec r TRVar .label = TLRVar
translateLRec r TRVar .subs = translateLRec r r

translateLRec r (Abs n) .label = TLAbs
translateLRec r (Abs n) .subs = n

translateLRec r (App n b) .label = TLApp  
translateLRec r (App n b) .subs = n , b


translate : Term false → RTerm
translate _ .rec = false

translate (TNat n) .label = TLNat
translate (TNat n) .subs = n

translate (TVar x) .label = TLVar
translate (TVar x) .subs = x

translate (Abs n) .label = TLAbs
translate (Abs n) .subs = n

translate (App n b) .label = TLApp  
translate (App n b) .subs = n , b

translate (LRec r b) .label = TLLRec
translate (LRec r b) .subs = translateLRec r b




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