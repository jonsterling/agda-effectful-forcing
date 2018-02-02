module Dialogue where

import Dialogue.Core as Core
import Dialogue.Normalize as Normalize

open Core hiding (module ⊢) public
open Normalize hiding (module ⊢) public

module ⊢ where
  open Core.⊢ public
  open Normalize.⊢ public
