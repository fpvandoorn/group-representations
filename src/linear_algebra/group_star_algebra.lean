/-

Group algebras considered as star algebras.

This is formally parallel to monoid_algebra, but instead of taking finite formal
combinations of the generators, we take L^1 combinations.

In this file we define `group_star_algebra k G := G →₁  k`, and `add_monoid_star_algebra k G`
in the same way, and then define the convolution product on these.

Instead of Haar measure this version uses counting measure

Another way to go: define the co-product G → G × G as a measure on G × G with the same integrable functions
as the product measure.  This has the advantage that we could do it for simple functions.
Note that Haar measure on G × G might not be the product of Haar measures but rather its completion.

-/

import data.monoid_algebra
import linear_algebra.star_algebra
import topology.bases
import measure_theory.measure_space measure_theory.l1_space measure_theory.bochner_integration

import group_theory.presented_group group_theory.order_of_element
import group_theory.free_abelian_group
import algebra.group.hom algebra.group_power
import group_theory.group_action
import group_theory.representation.basic

noncomputable theory
open_locale classical topological_space

open set filter topological_space ennreal emetric measure_theory
open finset finsupp

universes u₁ u₂ u₃
variables (k : Type u₁) (G : Type u₂)

def discrete_group (G : Type u₂) : Type u₂ := G

instance : measurable_space (discrete_group G) := ⊤

instance : measure_space (discrete_group G) := ⟨ measure.count ⟩ 

#print discrete_group.measurable_space

-- basic group example is ℤ^n (free abelian group with n generators) with the counting measure

inductive generator : Type
| x 

variables a b : generator

def zgroup := discrete_group (free_abelian_group generator)

def zgroup2 := (free_abelian_group generator)
instance : measurable_space zgroup2 := ⊤
instance : measure_space zgroup2 := _ -- ⟨  measure.count ⟩ 

#print zgroup2.measurable_space

def gx := free_abelian_group.of generator.x

def s1 := { g : zgroup2 | g = gx }

section
-- normed_group should be inferable from normed_star_ring 
variables [normed_star_ring k] [second_countable_topology k] [measurable_space k] [borel_space k] [opens_measurable_space k] [group G] [measure_space G]
variables [complete_space k] 

lemma measure_insert (μ : measure G) (s : set G) (hs : is_measurable s) (g : G) (hg: g ∉ s) : μ (insert g s) = μ s + μ {g} :=
begin 
  have h1 : is_measurable ({g} : set G) := sorry,
  have hh : disjoint s {g} := begin unfold disjoint, simp*, sorry end,
  have hz : ((insert g s) = (s ∪ {g})) := sorry,
  rw hz,
  apply measure_union hh hs h1, 
end

lemma measure_sum {ι : Type*} {α : Type*} [measurable_space α] (f : ι → measure α) (s : set α) : 
  (measure.sum f) s = ∑' i, f i s :=
begin unfold measure.sum, unfold outer_measure.sum, simp, 
end

lemma dirac_simp {α : Type*} [measurable_space α] (x g : α) : ite (x = g) 1 0 = (measure.dirac x) {g} := sorry

lemma check_count (s : finset G) : ( ↑ s.card = measure.count (↑s : set G)) := 
begin 
  unfold measure.count, apply finset.induction_on s, simp,
  intros g s' hs heq, 
  simp only [*, coe_insert, card_insert_of_not_mem, nat.cast_add, not_false_iff, nat.cast_one],
  rw measure_insert, congr, rw measure_sum, 
  have hh : (∑' i, ite (i=g) (1:ennreal) 0) = ∑' i : G, (measure.dirac i) {g} , 
    { congr, ext1, apply dirac_simp },
  rw [← hh,tsum_ite_eq], sorry,
 end


lemma hn : normed_space ℝ k := begin sorry end

def right_invariant_measure2 (f : G →₁ k) (a : G) (hn : normed_space ℝ k) : Prop := 
  (∫ x : G, f.to_fun x) = ∫ x : G, f.to_fun (x*a)

def right_invariant_measure (μ : measure G)  : Prop := ∀ g : G, ∀ s : set G, is_measurable s → μ s = μ ((λ h,h*g)⁻¹' s) 
  

lemma discrete_measure_is_right_invariant
--  (f : G →₁ k) (a : G) (hn : normed_space ℝ k) : (∫ x : G, f.to_fun x) = ∫ x : G, f.to_fun (x*a) := 
begin 
end

-- @[derive [star_algebra]]
def group_star_algebra : Type (max u₁ u₂) := G →₁ k


namespace group_star_algebra

variables {k G}
local attribute [reducible] group_star_algebra

section
variables [normed_star_ring k] [second_countable_topology k] [measurable_space k] [borel_space k] [opens_measurable_space k] [group G] [measure_space G]

def nntimes (a b : nnreal) : ennreal := ennreal.of_real (a * b) 


/-- The product of `f g : group_star_algebra k G` is the ℓ^1 function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x * y = a`. (Think of the group ring of a group.) -/

lemma mul_measurable (f g : G →₁ k) : measurable (λ a : G, (∫ x : G, 
  nnreal.to_real_hom ((nnnorm (f.to_fun x)) * (nnnorm (g.to_fun (x⁻¹ * a)))))) := 
begin dunfold measurable, 
end

lemma mul_integrable (f g : G →₁ k) : integrable (λ a : G, (∫ x : G, 
  nnreal.to_real_hom ((nnnorm (f.to_fun x)) * (nnnorm (g.to_fun (x⁻¹ * a)))))) := 
begin
end

-- lemma mul_convergence (f g : G →₁ k) :  (∫ a : G, (∫ x, ((nnnorm (f.to_fun x)) * (nnnorm (g.to_fun (x⁻¹ * a)))))) <  := 
-- begin 
--   -- use Fubini
--   -- use Haar measure to change variables a → x * a
-- end

instance : has_mul (group_star_algebra k G) :=
⟨λf g : G →ₘ k, (λ a : G, (∫ x, (f.to_fun x) * (g.to_fun (x⁻¹ * a))))

lemma mul_def {f g : group_star_algebra k G} :
  f * g = (λ a : G, (∫⁻ x, (f.to_fun x) * (g.to_fun (x⁻¹ * a)))
  :=
rfl
