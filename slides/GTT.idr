module GTT



import Fix

record Later (a : Type) where
  constructor Next
  tyGuard : Lazy a



-- Functor Guarded where
--   map f x =  (f x)

-- Applicative Guarded where
--   f <*> x = (f x)
--   pure x = x


partial fix : (Later a -> a) -> a
fix f = Fix.rawfix (\ x => (f (Next x)))

lob : (0 f : Later a -> a) -> fix f === f (Next (fix f))
lob f = Fix.rawlob ?



unguard : (Type -> Type) -> Later Type -> Type
unguard f g = f (tyGuard g)

export partial tyFix : (Type -> Type) -> Type
tyFix f = fix (unguard f)

export tyLob : (f : Type -> Type) -> tyFix f === f (tyFix f)
tyLob f = lob (unguard f)

export fromFix : {0 f : Type -> Type} -> tyFix f -> f (tyFix f)
fromFix x = replace {p = \x => x} (tyLob f) x

export toFix : {0 f : Type -> Type} -> f (tyFix f) -> tyFix f
toFix x = replace {p = \x => x} (sym (tyLob f)) x



