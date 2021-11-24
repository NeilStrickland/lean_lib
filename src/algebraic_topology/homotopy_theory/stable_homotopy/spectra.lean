import category_theory.category.basic 
import category_theory.limits.shapes.products

open category_theory

namespace algebraic_topology
namespace homotopy_theory
namespace stable_homotopy

structure AXIOMATIC_Spectra :=
(objects : Type)
(category : category.{1} objects)
(sphere : ℤ → objects)
/- Many more fields -/

constant Spectra : AXIOMATIC_Spectra

end stable_homotopy
end homotopy_theory
end algebraic_topology

