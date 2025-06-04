open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

module TermInduct where

    data Term : (rec : Bool) → Set where
        TNat : {rec : Bool} → Nat → Term rec
        TVar : {rec : Bool} → Nat → Term rec
        TRVar : Term true
        Abs : {rec : Bool} → Term rec → Term rec
        App : {rec : Bool} → Term rec → Term rec → Term rec
        LRec : Term true → Term true → Term false