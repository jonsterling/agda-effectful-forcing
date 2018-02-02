\paragraph{Baire space}

Brouwer's ``universal spread'' corresponds to what is now called Baire space (whose points are infinite sequences of natural numbers), which we construct by instantiating the previous module at \AgdaDatatype{Nat}.

\begin{code}
module Spread.Baire where

open import Basis
open import Spread.Core Nat public
\end{code}
