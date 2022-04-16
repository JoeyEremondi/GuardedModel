module GTT



import Fix

Guarded : Type -> Type
Guarded a =  a

next : a -> Guarded a
next x = x

-- Functor Guarded where
--   map f (Delay x) = Delay (f x)

-- Applicative Guarded where
--   (Delay f) <*> (Delay x) = (f x)
--   pure x = Delay x

-- TyGuarded : Guarded Type -> Type
-- TyGuarded (Delay t) = t

partial fix : (Guarded a -> a) -> a
fix f = Fix.rawfix f

lob : (0 f : Guarded a -> a) -> fix f === f (next (fix f))
lob f = Fix.rawlob f

record UnGuard (f : Type -> Type) (g : Guarded Type) where
  constructor ToGuard
  fromGuard : Lazy (f g)

toFromIso : (x : UnGuard f g) -> ToGuard (fromGuard x) === x
toFromIso (ToGuard x) = Refl

fromToIso : {0 f : Type -> Type} -> {g : Guarded Type} -> (x : Lazy (f g)) -> fromGuard (ToGuard x) === x
fromToIso x = Refl

export partial tyFix : (Type -> Type) -> Type
tyFix f = fix (UnGuard f)

export tyLob : (f : Type -> Type) -> tyFix f === UnGuard f (tyFix f)
tyLob f = lob (UnGuard f)

export fromFix : {0 f : Type -> Type} -> tyFix f -> f (tyFix f)
fromFix x = fromGuard (replace {p = \x => x} (tyLob f) x)

export toFix : {0 f : Type -> Type} -> f (tyFix f) -> tyFix f
toFix x = replace {p = \x => x} (sym (tyLob f)) (ToGuard x)

export fromToFix : (x : f (tyFix f)) -> fromFix {f = f} (toFix {f = f} x) === x
fromToFix x = Refl

export toFromFix : (x : tyFix f) -> toFix {f = f} (fromFix {f = f} x) === x
toFromFix x with ((replace {p = \x => x} (tyLob f) x))
  toFromFix x | (ToGuard y) = ?rhs

  --TODO report bug with record iso

-- partial fromFix : {0 f : Type -> Type} -> UnGuard f (tyFix f) -> f (UnGuard f (tyFix f))
-- fromFix (ToFix x) = replace {p = \ x => x} ?pf ?x

-- -- partial fromTyFix : {0 f : Type -> Type} -> f (tyFix f) -> tyFix f
-- -- fromTyFix = \x => UnG x


-- stream : Type -> Type
-- stream a = tyFix (\streamA => (a, streamA))

-- smapF : (a -> b) -> (stream a -> stream b) -> stream a -> stream b
-- smapF f self s = ?rhs
--   -- where
--   --   pr = fromFix s
