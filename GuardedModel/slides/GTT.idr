module GTT

%default partial

Guarded : Type -> Type
Guarded a = Lazy a

next : a -> Guarded a
next x = Delay x

Functor Guarded where
  map f (Delay x) = Delay (f x)

Applicative Guarded where
  (Delay f) <*> (Delay x) = (f x)
  pure x = Delay x

TyGuarded : Guarded Type -> Type
TyGuarded (Delay t) = t

partial fix : (Guarded a -> a) -> a
fix f = f (Delay (fix f))

lob : (f : Guarded a -> a) -> fix f === f (next (fix f))
lob _ = Refl

data UnGuard : (Type -> Type) -> Guarded Type -> Type where
  ToFix : Lazy (f tg) -> UnGuard f tg

partial tyFix : (Type -> Type) -> Type
tyFix f = fix (UnGuard f)

tyLob : (f : Type -> Type) -> tyFix f === UnGuard f (tyFix f)
tyLob f = lob (UnGuard f)

partial fromFix : {0 f : Type -> Type} -> UnGuard f (tyFix f) -> f (UnGuard f (tyFix f))
fromFix (ToFix x) = x

-- partial fromTyFix : {0 f : Type -> Type} -> f (tyFix f) -> tyFix f
-- fromTyFix = \x => UnG x


stream : Type -> Type
stream a = tyFix (\streamA => (a, streamA))

smapF : (a -> b) -> (stream a -> stream b) -> stream a -> stream b
smapF f self s = ?rhs
  where
    pr = fromFix s
