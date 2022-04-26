module Fix




export rawfix : (a -> a) -> a
rawfix f = f (rawfix f)

export rawlob : (0 f : a -> a) -> rawfix f === f (rawfix f)
rawlob f = Refl
