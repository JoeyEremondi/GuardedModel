module Test


%default partial

record Wrapper (a : Type) where
  constructor Wrap
  unwrap : a

wrapUnwrap : (x : Wrapper a) -> Wrap (unwrap x) === x
wrapUnwrap (Wrap x) = ?wr
