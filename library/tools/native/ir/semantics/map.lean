def map (K V : Type) := K → option V

@[irreducible] def map.get {K V : Type} (m : map K V) (key : K) : option V :=
m key

@[irreducible] def map.set {K V : Type} [decidable_eq K] (m : map K V) (key : K) (value : V) : map K V :=
fun k',
if k' = key
then some value
else m k'

attribute [irreducible] map
