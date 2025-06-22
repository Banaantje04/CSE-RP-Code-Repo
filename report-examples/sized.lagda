\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --cubical-compatible --sized-types #-}

open import Size
open import Agda.Builtin.Nat

module sized where

\end{code}

\begin{code}

record Thunk (F : Size → Set) (i : Size) : Set where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public

data Stream (A : Set) (i : Size) : Set where
  _∷_ : A → Thunk (Stream A) i → Stream A i

record StreamA (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → StreamA A j

\end{code}

\begin{code}

repeat : {A : Set} {i : Size} → A → Stream A i
repeat a = a ∷ λ where .force → repeat a

repeatA : {A : Set} {i : Size} → A → StreamA A i
repeatA a = a ∷ λ where .force → repeat a

map : {A B : Set} {i : Size} → (A → B) → Stream A i → Stream B i
map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)

\end{code}

\begin{code}
i : Size
i = ∞

j : Size< i
j = ∞

n : {m : Size} → Size< ↑ m
n {m} = m

str : Stream Nat ∞
str = repeat 69
\end{code}

\end{document}