module Stream

import GTT

stream : Type -> Type
stream a = tyFix (\streamA => (a, streamA))

smapF : (a -> b) -> (stream a -> stream b) -> stream a -> stream b
smapF f self s = ?rhs
  -- where
  --   pr = fromFix s
