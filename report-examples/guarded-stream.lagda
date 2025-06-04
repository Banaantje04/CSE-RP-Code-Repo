\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}

module guarded-stream where

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

repeat : {A : Set} → A → Stream A
repeat f .head = f
repeat f .tail = repeat f

map : {A B : Set} → (A → B) → Stream A → Stream B
map f s .head = f (s .head)
map f s .tail = map f (s .tail)

\end{code}

\end{document}