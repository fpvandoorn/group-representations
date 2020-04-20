/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import linear_algebra.basic linear_algebra.finite_dimensional linear_algebra.bilinear_form
import algebra.module logic.unique

universe variables u v w w'

open linear_map

/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. Normally `M` is a vector space, but we don't need that for the definition. -/
def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=
G →* general_linear_group R M

variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ f, f.to_fun⟩

namespace group_representation

/- module facts -/

def complementary [module R M] (N N' : submodule R M) : Prop := 
  ∀ x : M, ∃! (n : N), ∃! (n' : N'), x = n + n' 

def is_projection (π: M →ₗ[R] M) : Prop := π ∘ π = π 

example (π : M →ₗ[R] M) : is_projection π → complementary (ker π) (range π) := 
begin unfold is_projection, intro, unfold ker, unfold range, --unfold complementary, 
end

def projector_on_submodule [module R M] (N : submodule R M) : M →ₗ[R] M := sorry 

def is_orthogonal_complement (B : bilin_form R M) (N N' : submodule R M) : Prop :=
  complementary N N' ∧ ∀ x : N, ∀ y : N', bilin_form.is_ortho B x y 

/- end module facts -/

/- do we want this instance? Then we don't have to write `(ρ g).1 x` instead of `ρ g x`. -/
instance : has_coe (general_linear_group R M) (M →ₗ[R] M) := ⟨λ x, x.1⟩

protected structure equiv (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (α : M ≃ₗ[R] M')
  (commute : ∀(g : G), α ∘ ρ g = π g ∘ α)

structure subrepresentation (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (α : M →ₗ[R] M')
  (commute : ∀(g : G), α ∘ ρ g = π g ∘ α)

def invariant_subspace (ρ : group_representation G R M) (N : submodule R M) : Prop :=
  ∀ x : N, ∀ g : G, ρ g x ∈ N

variables B : bilin_form R M 

def standard_invariant_bilinear_form (ρ : group_representation G R M) (B : bilin_form R M): bilin_form R M := B 
  -- linear_map.to_bilin  λ (x y : M), sum over g in  G, B (ρ g x) (ρ g y)
  -- also divide by |G|

#print standard_invariant_bilinear_form

/- this requires the cokernel of α
lemma subrep_is_invariant (ρ : group_representation G R M) (π : group_representation G R M') :
  Π s : subrepresentation ρ π, invariant_subspace ρ (s.α M) :=
-/

def irreducible (ρ : group_representation G R M) : Prop :=
  ∀ N : submodule R M, invariant_subspace ρ N → N = ⊥ ∨ N = ⊤


/-- Maschke's theorem -/

lemma standard_orthogonal_complement_is_invariant (ρ : group_representation G R M) (B : bilin_form R M) : 
  ∀ N N' : submodule R M, invariant_subspace ρ N → is_orthogonal_complement B N N' → invariant_subspace ρ N' := sorry

theorem maschke (ρ : group_representation G R M) (B : bilin_form R M) : ∀ N : submodule R M,
  invariant_subspace ρ N → ∃ N', invariant_subspace ρ N' ∧ complementary N N' := 
begin intros, have h := standard_orthogonal_complement_is_invariant ρ B , 

end

def Mmap := M →ₗ[R] M 

def invariant_projector (ρ : group_representation G R M) (B : bilin_form R M) : Mmap → Mmap := λ X, X 
-- λ x : M, sum over g, ρ g (π (ρ g⁻¹ x))

theorem maschke2 (ρ : group_representation G R M) (B : bilin_form R M) : ∀ N : submodule R M,
  invariant_subspace ρ N → ∃ N', invariant_subspace ρ N' ∧ complementary N N' := 
begin intros, 
  use invariant_projector ρ B projector_on_submodule N, 
end

end group_representation

/- from [https://github.com/Shenyang1995/M4R/blob/66f1450f206dc05c3093bc4eaa1361309bf8633b/src/G_module/basic.lean#L10-L14].
  Do we want to use this definition instead? This might allow us to write `g • x` instead of `ρ g x` -/
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)
