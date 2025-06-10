\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}
open import Agda.Builtin.Nat

module productivitybreak where

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

id : {A : Set} → A → A
id x = x

x : Nat
x = id (9)

repeat : {A : Set} → A → Stream A
repeat f .head = f
repeat f .tail = repeat f

\end{code}

\end{document}