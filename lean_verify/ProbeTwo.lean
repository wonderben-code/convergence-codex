import DualDegreeExact
open IsingFiniteVolume DualObstruction PlaquetteLattice DualGraph SimpleGraph
open IsingContourPlaquette IsingContourEnergy ExtendedDual DualDegreeExact
set_option linter.style.openClassical false
open scoped Classical
example {n : ℕ} {σ : Config n} (hev : EvenDegrees (dualGraph σ)) (P : Plaq n) :
    Even (Finset.univ.filter fun e : Fin 4 => sideOf P e ∈ contour σ ∧ Outward P e).card :=
  (evenDegrees_dualGraph_iff σ).mp hev P
