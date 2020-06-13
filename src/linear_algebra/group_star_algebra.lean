/-

Group algebras considered as star algebras.

This is formally parallel to monoid_algebra, but instead of taking finite formal
combinations of the generators, we take L^1 combinations.

In this file we define `group_star_algebra k G := G →₁  k`, and `add_monoid_star_algebra k G`
in the same way, and then define the convolution product on these.

-/

import data.monoid_algebra
import linear_algebra.star_algebra
import measure_theory.measure_space measure_theory.l1_space

noncomputable theory
open_locale classical topological_space

open set filter topological_space ennreal emetric measure_theory
open finset finsupp

universes u₁ u₂ u₃
variables (k : Type u₁) (G : Type u₂)

section
-- normed_group should be inferable from normed_star_ring 
variables [normed_star_ring k] [normed_group k] [second_countable_topology k] [measurable_space k] [borel_space k] [opens_measurable_space k] [group G] [measure_space G]

-- @[derive [star_algebra]]
def group_star_algebra : Type (max u₁ u₂) := G →ₘ k

end

namespace group_star_algebra

variables {k G}
local attribute [reducible] group_star_algebra

section
variables [normed_star_ring k] [normed_group k] [second_countable_topology k] [measurable_space k] [borel_space k] [opens_measurable_space k] [group G] [measure_space G]

def nntimes (a b : nnreal) : ennreal := ennreal.of_real (a.to_real * b.to_real) 

/-- The product of `f g : group_star_algebra k G` is the ℓ^1 function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x * y = a`. (Think of the group ring of a group.) -/

lemma mul_convergence (f g : G →ₘ k) :  (∫⁻ a : G, (∫⁻ x, ennreal.of_real ((nnnorm (f.to_fun x)) * (nnnorm (g.to_fun (x⁻¹ * a)))))) < ⊤ := 
begin 
  -- use Fubini
  -- use Haar measure to change variables a → x * a
end

-- where is the actual integral defined?
instance : has_mul (group_star_algebra k G) :=
⟨λf g : G →ₘ k, (λ a : G, (∫⁻ x, (f.to_fun x) * (g.to_fun (x⁻¹ * a))))

lemma mul_def {f g : group_star_algebra k G} :
  f * g = (λ a : G, (∫⁻ x, (f.to_fun x) * (g.to_fun (x⁻¹ * a)))
  :=
rfl
