module MiniProver.Core.Termination (
    isTerminating
  ) where

import MiniProver.Core.Syntax

-- Not terminating => return Nothing
-- Terminating     => the number of argument decreasing on
isTerminating :: Term -> Maybe Int
isTerminating = undefined