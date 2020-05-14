/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Douglas, Floris van Doorn
-/
import .basic
/- everything we have done that uses bilinear forms-/
universe variables u v w w' w''

open linear_map

variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'} {M'' : Type w''}
  [group G] [comm_ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
  [add_comm_group M''] [module R M'']

namespace submodule

/-- `π` is a projection with as range `N` -/
def is_projection_on_submodule (N : submodule R M) (π : M →ₗ[R] M) : Prop :=
is_projection π ∧ range π = N

def is_orthogonal_projection_on_submodule (B : bilin_form R M) (N : submodule R M) (π : M →ₗ[R] M) :
  Prop :=
is_projection_on_submodule N π ∧ ∀ x : M, ∀ y : N, bilin_form.is_ortho B x y → π x = 0

lemma exists_orthogonal_projection_on_submodule (B : bilin_form R M) (N : submodule R M) :
  ∃ π : M →ₗ[R] M, is_orthogonal_projection_on_submodule B N π :=
sorry

lemma orthogonal_projection_on_submodule_range (B : bilin_form R M) (N : submodule R M)
  (π : M →ₗ[R] M) : is_projection_on_submodule N π → ∀ x : M, π x ∈ N :=
begin
  unfold is_projection_on_submodule, unfold is_projection, intro, sorry,
end

/-- A bilinear form is nondegenerate if `B x (-)` is the zero function only if `x` is zero. -/
def nondegenerate (B : bilin_form R M) : Prop :=
∀ x : M, (∀ y : M, B x y = 0) → x = 0

lemma nondegenerate_bilinear_form_exists : ∃ B : bilin_form R M, nondegenerate B := sorry
/- sum over a noncanonical basis - does this require R to be a field ?  -/

/- `is_orthogonal B N N'` states that `N` and `N'` are orthogonal w.r.t. bilinear form `B`. -/
def is_orthogonal (B : bilin_form R M) (N N' : submodule R M) : Prop :=
∀ x y, x ∈ N → y ∈ N' → bilin_form.is_ortho B x y

/- The orthogonal complement of a submodule w.r.t. a bilinear form. -/
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

/- A bilinear form is definite if `B x x = 0` only when `x = 0`. -/
def is_definite (B : bilin_form R M) : Prop :=
∀ x, B x x = 0 → x = 0

lemma orthogonal_complement_is_complementary (B : bilin_form R M) (N : submodule R M)
  (hB : is_definite B) : complementary N (orthogonal_complement B N) :=
begin
  intros, split,
  rcases exists_orthogonal_projection_on_submodule B N with ⟨π, hπ⟩,
  { rw [covering_iff, eq_top_iff'], intro, rw mem_sup, simp, use π x, split,
    apply orthogonal_projection_on_submodule_range B _ _ hπ.1,
    use (x - π x), simp [orthogonal_projection_on_submodule_coker, hπ.1] },
  { rw [disjoint_def], intros x hx h2x, apply hB, apply h2x, exact hx }
end

lemma is_orthogonal_orthogonal_complement (B : bilin_form R M) (N : submodule R M)
  : is_orthogonal B (orthogonal_complement B N) N :=
by { intros x y hx hy, exact hx y hy }

def conjugated_bilinear_form (ρ : group_representation G R M) (B : bilin_form R M) (g : G) :
  bilin_form R M :=
B.comp (ρ g) (ρ g)

/-- A bilinear form `B` is invariant under a representation `ρ` if `B = B ∘ (ρ g × ρ g)` for all `g`. -/
def is_invariant (ρ : group_representation G R M) (B : bilin_form R M) : Prop :=
∀ g : G, B = B.comp (ρ g) (ρ g)

/-- The standard bilinear form for a finite group `G`, defined by summing over all group elements. -/
def standard_invariant_bilinear_form [fintype G] (ρ : group_representation G R M)
  (B : bilin_form R M) : bilin_form R M :=
finset.univ.sum (λ g : G, B.comp (ρ g) (ρ g))

lemma sum_apply {α} (s : finset α) (f : α → bilin_form R M) (m m' : M) :
  s.sum f m m' = s.sum (λ x, f x m m') :=
begin
  sorry
end

lemma is_invariant_standard_invariant_bilinear_form [fintype G] (ρ : group_representation G R M)
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

lemma is_invariant_orthogonal_complement {ρ : group_representation G R M} (B : bilin_form R M) :
  ∀ N N' : submodule R M, is_invariant ρ B → N.invariant_under ρ → is_orthogonal B N' N →
  N'.invariant_under ρ :=
begin
  unfold is_invariant, unfold invariant_under, unfold is_orthogonal,
  intros N N' hρ hN hN' x g, dsimp,
  unfold bilin_form.is_ortho at hN', rw [hρ g] at hN', dsimp at hN',
  -- at this point hN with hN' imply that ρ g x is in the orthogonal complement.  by definition this is N'.
  sorry
end

theorem maschke [fintype G] (ρ : group_representation G R M) (B : bilin_form R M) :
  ∀ N : submodule R M, N.invariant_under ρ →
  ∃ N' : submodule R M, N'.invariant_under ρ ∧ complementary N N' :=
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

end submodule