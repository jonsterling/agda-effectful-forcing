\begin{code}
open import Basis
\end{code}

%<*spread>
In order to develop intuitionistic analysis, Brouwer introduced a new notion of topological space called a ``spread'', which was based on the idea of taking the basic opens (what we here call prefixes'') of a space as primitive, rather than the points. A spread is a species\footnote{``Species'' is Brouwer's word for what we   now call a ``predicate''.} of these prefixes obeying certain closure conditions, which specifies the basic opens of the space; the points of a spread are then a derived notion. For our purposes, it actually suffices to work relative to the \emph{universal spread}, which is the total species $\top$.

\begin{remark}
  Today, more general notions of spread can be found in both formal topology~\cite{coquand-sambin-smith-valentini:2003} as well as the theory of locales~\cite{maclane-moerdijk:1992}; locales and classical spaces enjoy a duality which is neutralized under the equivalence of the sober spaces and the spatial locales.
\end{remark}

Brouwer thought of these prefixes as finite lists of natural numbers, each of which represented a ``choice''; rather than adopting the natural numbers as the representation of choices, we simply fix a set $X$ which will serve this purpose.\footnote{As a matter of engineering, it is easier to develop a theory if not everything at once is a natural number, even if later on we intend to insantiate it that way.}

\begin{code}
module Spread.Core (X : Set) where

module Prefix where
  data Prefix : Set where
    [] : Prefix
    _⌢_ : Prefix → X → Prefix

  infixl 5 _⌢_

  ∣_∣ : Prefix → Nat
  ∣ [] ∣ = 0
  ∣ U ⌢ x ∣ = suc ∣ U ∣
\end{code}

\AgdaHide{
\begin{code}

  module ⊢ where
    _⟨⌢⟩_ : ∀ {U V : Prefix} {x y} → U ≡ V → x ≡ y → U ⌢ x ≡ V ⌢ y
    refl ⟨⌢⟩ refl = refl
\end{code}
}

\paragraph{Points (choice sequences)}
Finally the notion of a \emph{point} in the universal spread is defined, together with operations for prepending choices and neighorhoods to it: a point is simply an infinite sequence of choices, what Brouwer himself called a ``choice sequence''.

\begin{code}
module Point where
  Point : Set
  Point = Nat → X

  head : Point → X
  head α = α 0

  tail : Point → Point
  tail α = α ∘ suc

  _<∷_ : X → Point → Point
  (x <∷ α) zero = x
  (x <∷ α) (suc i) = α i
\end{code}

The natural notion of equivalence for points is the extensional (pointwise) equivalence.
\begin{code}
  _≈_ : Point → Point → Set
  α ≈ β = ∀ i → α i ≡ β i
\end{code}

\AgdaHide{
\begin{code}
  open Prefix hiding (module ⊢)
\end{code}
}

A prefix can be prepended to a point.
\begin{code}
  _<++_ : Prefix → Point → Point
  [] <++ α = α
  (U ⌢ x) <++ α = U <++ (x <∷ α)

  infixr 3 _<++_
  infix 6 _[_]
\end{code}

We provide an operation to take the $n$th approximation of a point $\alpha$:
\begin{code}
  _[_] : Point → Nat → Prefix
  α [ zero ] = []
  α [ suc n ] = α [ n ] ⌢ α n

\end{code}

\AgdaHide{
\begin{code}
  module ⊢ where
    nth-cong
      : (α β : Point) {i j : Nat}
      → α ≈ β
      → i ≡ j
      → α i ≡ β j
    nth-cong α β h refl =
      h _

    take-cong
      : ∀ {α β m n}
      → m ≡ n
      → α ≈ β
      → α [ m ] ≡ β [ n ]
    take-cong {m = zero} {n = .0} refl q = refl
    take-cong {m = (suc m)} {n = .(suc m)} refl q
      rewrite take-cong {m = m} refl q
        | q m
        = refl

    su-+-transpose
      : ∀ m n
      → suc (n + m) ≡ n + suc m
    su-+-transpose zero zero = refl
    su-+-transpose zero (suc n)
      rewrite su-+-transpose zero n
        = refl
    su-+-transpose (suc m) zero = refl
    su-+-transpose (suc m) (suc n)
      rewrite su-+-transpose (suc m) n
        = refl

    nat-+-zero
      : ∀ n
      → n + 0 ≡ n
    nat-+-zero zero = refl
    nat-+-zero (suc n) rewrite nat-+-zero n = refl

    prepend-len
      : ∀ U n {α}
      → (U <++ α) (n + ∣ U ∣) ≡ α n
    prepend-len [] n rewrite nat-+-zero n = refl
    prepend-len (U ⌢ x) n =
      prepend-len U (suc n)
      ≡.▪
        nth-cong
          (U ⌢ x <++ _)
          _
          (λ i → refl)
          (su-+-transpose ∣ U ∣ n ≡.⁻¹)


    prepend-take-len
      : ∀ U {α}
      → (U <++ α) [ ∣ U ∣ ] ≡ U
    prepend-take-len [] = refl
    prepend-take-len (U ⌢ x) =
      prepend-take-len U
        Prefix.⊢.⟨⌢⟩ prepend-len U 0

    cons-head-tail-id
      : ∀ α
      → α ≈ (head α <∷ tail α)
    cons-head-tail-id α zero = refl
    cons-head-tail-id α (suc i) = refl

    prepend-extensional
      : ∀ U α β
      → α ≈ β
      → (U <++ α) ≈ (U <++ β)
    prepend-extensional [] α β h = h
    prepend-extensional (U ⌢ x) α β h =
      prepend-extensional U (x <∷ α) (x <∷ β) λ
        { zero → refl
        ; (suc j) → h j
        }

    prepend-snoc-id
      : ∀ U α
      → (U <++ α) ≈ (U ⌢ head α <++ tail α)
    prepend-snoc-id U α =
      prepend-extensional U _ _ (cons-head-tail-id α)

\end{code}
}

\paragraph{Species of prefixes}
We give a definition of species of prefixes, and what it means for them to be \emph{monotone} and \emph{hereditary}; instead of \emph{hereditary}, we could have called such species \emph{inductive}. Finally, one we give an ordering on species which is just implication of the underline predicates. As a matter of convention, we write species with German letters.

\begin{code}
module Species where
  open Prefix

  Species : Set₁
  Species = Prefix → Set

  monotone : Species → Set
  monotone 𝔄 = ∀ {U} x → 𝔄 U → 𝔄 (U ⌢ x)

  hereditary : Species → Set
  hereditary 𝔄 = ∀ {U} → (∀ x → 𝔄 (U ⌢ x)) → 𝔄 U

  _⊑_ : Species → Species → Set
  𝔄 ⊑ 𝔅 = ∀ x → 𝔄 x → 𝔅 x
\end{code}
%</spread>

\begin{code}
open Point public hiding (module ⊢)
open Prefix public hiding (module Prefix; module ⊢)
open Species public

\end{code}
