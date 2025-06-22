\usepackage{agda}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}

module mutualcoinduct where

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

mutual
  repeat : {A : Set} → A → Stream A
  repeat f .head  = f
  repeat f .tail  = other f

  other : {A : Set} → A → Stream A
  other f .head = f
  other f .tail = repeat f
\end{code}

\end{document}