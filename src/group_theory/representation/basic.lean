/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Douglas, Floris van Doorn
-/
import linear_algebra.finite_dimensional linear_algebra.bilinear_form
import data.fintype.card tactic.apply_fun

universe variables u v w w'

open linear_map

/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. Normally `M` is a vector space, but we don't need that for the definition. -/
def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M] [module R M] :
  Type* :=
G →* general_linear_group R M

variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'}
  [group G] [comm_ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ f, f.to_fun⟩
instance : has_coe (general_linear_group R M) (M →ₗ[R] M) := ⟨λ x, x.1⟩

namespace group_representation

/- module facts -/

open submodule

def complementary {α} [has_top α] [has_bot α] [has_sup α] [has_inf α] (x x' : α) : Prop :=
x ⊔ x' = ⊤ ∧ x ⊓ x' = ⊥

def is_projection (π: M →ₗ[R] M) : Prop := ∀ x, π (π x) = π x

/- Note: this only states that N ⊆ range π, do we want equality here (we need that for orthogonal_projection_on_submodule_range)-/
def is_projection_on_submodule (N : submodule R M) (π: M →ₗ[R] M) : Prop :=
is_projection π ∧ ∀ x : N, π x = x

def is_orthogonal_projection_on_submodule (B : bilin_form R M) (N : submodule R M) (π: M →ₗ[R] M) :
  Prop :=
is_projection_on_submodule N π ∧ ∀ x : M, ∀ y : N, bilin_form.is_ortho B x y → π x = 0

lemma exists_orthogonal_projection_on_submodule (B : bilin_form R M) (N : submodule R M) :
∃ π: M →ₗ[R] M, is_orthogonal_projection_on_submodule B N π := sorry

lemma orthogonal_projection_on_submodule_range (B : bilin_form R M) (N : submodule R M) (π: M →ₗ[R] M) :
  is_projection_on_submodule N π → ∀ x : M, π x ∈ N :=
begin
  unfold is_projection_on_submodule, unfold is_projection, intro, sorry,
end

lemma eq_bot (N : submodule R M) : N = ⊥ ↔ ∀ x : M, x ∈ N → x = 0 :=
begin
  rw [eq_bot_iff], split,
  { intros h x hx, simpa using h hx },
  { intros h x hx, simp [h x hx] }
end

example (π : M →ₗ[R] M) : is_projection π → complementary (ker π) (range π) :=
begin
  unfold is_projection, intro hp, split,
  { rw eq_top_iff', intro x, rw mem_sup, use (linear_map.id - π) x,
    split, { simp [hp] },
    use π x, simp only [and_true, sub_apply, sub_add_cancel, mem_range, eq_self_iff_true, id_apply],
    use x },
  { intros, rw eq_bot, simp only [and_imp, mem_ker, mem_range, mem_inf, exists_imp_distrib],
    intros x hx x' hx', have h2x' := hx', apply_fun π at hx', simp [hp, hx] at hx', cc }
end

def nondegenerate (B : bilin_form R M) : Prop :=
∀ x : M, 0 ≠ x → ∃ y : M, 0 ≠ B x y


lemma nondegenerate_bilinear_form_exists : ∃ B : bilin_form R M, nondegenerate B := sorry
/- sum over a noncanonical basis - does this require R to be a field ?  -/

def is_orthogonal (B : bilin_form R M) (N N' : submodule R M) : Prop :=
∀ x y, x ∈ N → y ∈ N' → bilin_form.is_ortho B x y

@[simps] def orthogonal_complement (B : bilin_form R M) (N : submodule R M) : submodule R M :=
{ carrier := {x:M|∀ y ∈ N, bilin_form.is_ortho B x y},
  zero := λ y hy, bilin_form.ortho_zero y,
  add := λ x y hx hy z hz,
  begin
    unfold bilin_form.is_ortho at *, simp [bilin_form.add_left], simp [hx z hz, hy z hz],
  end,
  smul := λ r x hx y hy,
  by { unfold bilin_form.is_ortho at *, rw [bilin_form.smul_left, hx y hy, mul_zero] } }

--lemma orthogonal_complement_bijective_to_quotient {B : bilin_form R M} (N : submodule R M) :
--  linear_algebra.of_bijective _ _ := sorry

lemma orthogonal_projection_on_submodule_coker (B : bilin_form R M) (N : submodule R M) (π : M →ₗ[R] M) :
  is_projection_on_submodule N π → ∀ x : M, x - π x ∈ orthogonal_complement B N :=
begin
  unfold is_projection_on_submodule, unfold is_projection, intro, sorry,
end

lemma orthogonal_complement_is_complementary
  (B : bilin_form R M) (N : submodule R M)
  (hB : ∀ x, B x x = 0 → x = 0) -- is this assumption too strong?
  : complementary N (orthogonal_complement B N) :=
begin
  intros, split,
  rcases exists_orthogonal_projection_on_submodule B N with ⟨π, hπ⟩,
  { rw eq_top_iff', intro, rw mem_sup, simp, use π x, split,
    apply orthogonal_projection_on_submodule_range B _ _ hπ.1,
    use (x - π x), simp [orthogonal_projection_on_submodule_coker, hπ.1] },
  { rw eq_bot, simp, intros x hx h2x, apply hB, apply h2x, exact hx }
end

lemma is_orthogonal_orthogonal_complement (B : bilin_form R M) (N : submodule R M)
  : is_orthogonal B (orthogonal_complement B N) N :=
begin
  intros x y hx hy,
  exact hx y hy
end

/- end module facts -/

protected structure equiv (ρ : group_representation G R M) (π : group_representation G R M') :
  Type (max w w') :=
  (α : M ≃ₗ[R] M')
  (commute : ∀(g : G), α ∘ ρ g = π g ∘ α)

--structure subrepresentation (ρ : group_representation G R M) (π : group_representation G R M') :
--  Type (max w w') :=
  --(α : M →ₗ[R] M')
  --(commute : ∀(g : G), α ∘ ρ g = π g ∘ α)
  --left_inv := λ m, show (f.inv * f.val) m = m

section field

variables {K : Type v} [field K] {V : Type w} [add_comm_group V] [vector_space K V]
          (H : finite_dimensional K V)
          {ι : Type*} {v : ι → V} (Hb: is_basis K v)

noncomputable example (s : set V) (hs1 : is_basis K (subtype.val : s → V))
  (hs2 : s.finite) (f : V → K) : K :=
begin let sfin := hs2.to_finset, exact sfin.sum f,
end

/- Note that this need not depend on a bilinear form,
it could be done given a basis of N and a way to complete it to a basis of M.
This construction would work for rings. -/
noncomputable def projector_on_submodule {v : ι → V} {Hb: is_basis K v} {B : bilin_form K V}
  (N : submodule K V) : V →ₗ[K] V :=
begin
  let f : ι → V := sorry,
  exact is_basis.constr Hb f,
end

end field

section finite_groups

variable [fintype G]

def sum_over_G1 {s : finset G}  : nat := s.sum 0
#print sum_over_G1

def sum_over_G {s : finset G} (ρ : group_representation G R M) : M →ₗ[R] M :=
s.sum (λ g:G, general_linear_group.to_linear_equiv (ρ g) )
#print sum_over_G

def invariant_subspace (ρ : group_representation G R M) (N : submodule R M) : Prop :=
∀ x : N, ∀ g : G, ρ g x ∈ N

variables B : bilin_form R M

def conjugated_bilinear_form (ρ : group_representation G R M) (B : bilin_form R M) (g : G) :
  bilin_form R M :=
B.comp (ρ g) (ρ g)

def is_invariant (ρ : group_representation G R M) (B : bilin_form R M) : Prop :=
  ∀ g : G, B = B.comp (ρ g) (ρ g)

/- define a subclass of invariant bilinear forms ? -/

def standard_invariant_bilinear_form [fintype G] (ρ : group_representation G R M)
  (B : bilin_form R M) : bilin_form R M :=
finset.univ.sum (λ g : G, B.comp (ρ g) (ρ g))

variables g2 : G

def foo (ρ : group_representation G R M) : M ≃ₗ[R] M := (ρ.to_fun g2).to_linear_equiv
#check foo

#check finset.sum_bij (λ g:G, λ _, g * g2⁻¹ )

lemma sum_apply {α} (s : finset α) (f : α → bilin_form R M) (m m' : M) :
  s.sum f m m' = s.sum (λ x, f x m m') :=
begin sorry
end

lemma is_invariant_standard_invariant_bilinear_form (ρ : group_representation G R M)
  (B : bilin_form R M) : is_invariant ρ (standard_invariant_bilinear_form ρ B) :=
begin
  unfold standard_invariant_bilinear_form,
  intro g1, ext, simp [sum_apply], symmetry,
  apply finset.sum_bij (λ g _, g * g1),
  { intros, apply finset.mem_univ },
  { intros, apply bilin_form.coe_fn_congr, repeat { dsimp, rw ρ.map_mul, refl } },
  { intros g g' _ _ h, simpa using h },
  { intros, use b * g1⁻¹, simp }
end

def irreducible (ρ : group_representation G R M) : Prop :=
∀ N : submodule R M, invariant_subspace ρ N → N = ⊥ ∨ N = ⊤


/-- Maschke's theorem -/

lemma is_invariant_orthogonal_complement {ρ : group_representation G R M} (B : bilin_form R M) :
  ∀ N N' : submodule R M, is_invariant ρ B → invariant_subspace ρ N → is_orthogonal B N' N →
  invariant_subspace ρ N' :=
begin
  unfold is_invariant, unfold invariant_subspace, unfold is_orthogonal,
  intros N N' hρ hN hN' x g, dsimp,
  unfold bilin_form.is_ortho at hN', rw [hρ g] at hN', dsimp at hN',
  -- at this point hN with hN' imply that ρ g x is in the orthogonal complement.  by definition this is N'.
  sorry
end

theorem maschke (ρ : group_representation G R M) (B : bilin_form R M) : ∀ N : submodule R M,
  invariant_subspace ρ N → ∃ N', invariant_subspace ρ N' ∧ complementary N N' :=
begin
  intros N hN,
  let std := standard_invariant_bilinear_form ρ B,
  let N' := orthogonal_complement std N,
  have h := is_invariant_orthogonal_complement std N N'
           (is_invariant_standard_invariant_bilinear_form ρ B) hN
           (is_orthogonal_orthogonal_complement _ _),
  use N', use h,
  apply orthogonal_complement_is_complementary, sorry,
 end

end finite_groups

end group_representation

/--
def Mmap := M →ₗ[R] M

def invariant_projector (ρ : group_representation G R M) (B : bilin_form R M) : Mmap → Mmap := λ X, X
-- λ x : M, sum over g, ρ g (π (ρ g⁻¹ x))

theorem maschke2 (ρ : group_representation G R M) (B : bilin_form R M) : ∀ N : submodule R M,
  invariant_subspace ρ N → ∃ N', invariant_subspace ρ N' ∧ complementary N N' :=
begin intros,
  use invariant_projector ρ B projector_on_submodule N,
end
-/






/- from [https://github.com/Shenyang1995/M4R/blob/66f1450f206dc05c3093bc4eaa1361309bf8633b/src/G_module/basic.lean#L10-L14].

  Do we want to use this definition instead? This might allow us to write `g • x` instead of `ρ g x` -/
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)
