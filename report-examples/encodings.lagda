\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

module encodings where
\end{code}

\begin{code}
data Term : (rec : Bool) → Set where
    TNat : {rec : Bool} → Nat → Term rec
    TVar : {rec : Bool} → Nat → Term rec
    TRVar : Term true
    Abs : {rec : Bool} → Term rec → Term rec
    App : {rec : Bool} → Term rec → Term rec → Term rec
    LRec : Term true → Term true → Term false
\end{code}

\begin{code}
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
\end{code}

\begin{code}
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
\end{code}

\end{document}