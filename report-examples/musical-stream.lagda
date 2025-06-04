\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}

open import Level
open import Agda.Builtin.Nat

module musical-stream where
    
infix 1000 ♯_
private
    variable
        a b c : Level

\end{code}

\begin{code}

postulate
    ∞  : (A : Set a) → Set a
    ♯_ : {A : Set a} → A → ∞ A
    ♭  : {A : Set a} → ∞ A → A


{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}



data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

\end{code}

\begin{code}

repeat : {A : Set} → A → Stream A
repeat x = x ∷ ♯ repeat x

map : {A B : Set} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

nats : Stream Nat
nats = zero :: mapS suc nats

\end{code}

\end{document}