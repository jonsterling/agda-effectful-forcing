{-# OPTIONS --without-K #-}

-- This is the formalization of the paper "Higher-Order Functions and
-- Brouwer's Thesis" by Sterling.

-- This formalization is carried out in Intensional Type Theory
-- extended by the function extensionality axiom. We have been careful
-- not to assume Axiom K, so our development is compatible with
-- homotopy type theory.

-- We have also avoided the use of pattern matching with the identity
-- type, as well as the built-in "rewrite" tactic. Consequently, this
-- development could easily be ported to Cubical Agda using the
-- inductive identity type, avoiding the use of any non-computational
-- axioms.

module index where

-- Our basic assumptions and prelude.
import Basis

-- The main result
import BarTheorem

-- The definition of the Escardó and Brouwer dialogues
import Dialogue.Core

-- The normalization of Escardó dialogues into Brouwer dialogues
import Dialogue.Normalize

-- The syntax of System T
import SystemT.Syntax

-- The two semantics of System T and their compatibility
import SystemT.Semantics
