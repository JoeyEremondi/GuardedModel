module GTT

data Guarded : Type -> Type where
  Next : Lazy a -> Guarded a


Functor Guarded where
  map f (Next x) = Next (f x)

Applicative Guarded where
  (Next f) <*> (Next x) = Next (f x)
  pure x = Next x



-- data TyGuarded : Guarded Type -> Type where
--   WrapTy : Lazy a -> TyGuarded (Next a)

-- toGuarded : TyGuarded (Next a) -> Lazy a
-- toGuarded (WrapTy x) = x


-- fromGuarded : Lazy a -> TyGuarded (Next a)
-- fromGuarded x = WrapTy x

-- partial fix : (Guarded a -> a) -> a
-- fix f = f (Next (fix f))

-- lob : (f : Guarded a -> a) -> fix f === f (Next (fix f))
-- lob _ = Refl

-- data UnGuard : (Type -> Type) -> Guarded Type -> Type where
--   UnG : Lazy (f (TyGuarded tg)) -> UnGuard f tg

-- partial tyFix : (Type -> Type) -> Type
-- tyFix f = fix (UnGuard f)

-- tyLob : (f : Type -> Type) -> tyFix f === UnGuard f (Next (tyFix f))
-- tyLob f = lob (UnGuard f)

-- -- partial toTyFix : {0 f : Type -> Type} -> tyFix f -> f (tyFix f)
-- -- toTyFix x = ?ttf

-- partial fromTyFix : (f : Type -> Type) -> f (tyFix f) -> tyFix f
-- fromTyFix = \ f , x => UnG x


-- -- -- -- Example
-- -- stream : Type -> Type
-- -- stream a = tyFix (\ streamA => (a, streamA) )

-- -- smap : stream a -> stream a
-- -- smap  = fix (\smap => \pr => ?r)
