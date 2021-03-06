/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Douglas, Floris van Doorn
-/
import linear_algebra.finite_dimensional linear_algebra.bilinear_form
import data.fintype.card tactic.apply_fun
import misc

universe variables u v w w' w''

open linear_map

variables {G : Type u} {R : Type v} {M : Type w} {M' : Type w'} {M'' : Type w''}
  [group G] [comm_ring R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
  [add_comm_group M''] [module R M''] {N N' : submodule R M}
  {K : Type v} [field K] {V : Type w} [add_comm_group V] [vector_space K V]

namespace submodule

/- module facts -/

lemma eq_bot_iff' (N : submodule R M) : N = ⊥ ↔ ∀ x : M, x ∈ N → x = 0 :=
begin
  rw [eq_bot_iff], split,
  { intros h x hx, simpa using h hx },
  { intros h x hx, simp [h x hx] }
end

@[simp] lemma range_coprod (f : M →ₗ[R] M'') (g : M' →ₗ[R] M'') :
  (f.coprod g).range = f.range ⊔ g.range :=
begin
  unfold linear_map.range,
  convert map_coprod_prod _ _ _ _,
  rw prod_top,
end

lemma mem_sup_left {p p' : submodule R M} {x : M} (h : x ∈ p) : x ∈ p ⊔ p' :=
by { have : p ≤ p ⊔ p' := le_sup_left, exact this h }

lemma mem_sup_right {p p' : submodule R M} {x : M} (h : x ∈ p') : x ∈ p ⊔ p' :=
by { have : p' ≤ p ⊔ p' := le_sup_right, exact this h }

/-- A projection is an idempotent linear map -/
@[reducible] def is_projection (π : M →ₗ[R] M) : Prop := ∀ x, π (π x) = π x

-- def is_projection_on (N : submodule R M) (π : M →ₗ[R] M): Prop := ∀ x : N, π x = x ∧ range π ≤ N

-- lemma projections (N : submodule R M) (π : M →ₗ[R] M) : is_projection_on N π → is_projection π :=
-- sorry

/-- Two elements in a lattice are complementary if they have meet ⊥ and join ⊤. -/
def complementary {α} [bounded_lattice α] (x x' : α) : Prop :=
covering x x' ∧ disjoint x x'

lemma complementary.comm {α} [bounded_lattice α] {x x' : α} :
  complementary x x' ↔ complementary x' x :=
by { dsimp [complementary], rw [covering.comm, disjoint.comm] }

namespace complementary
/-- Given two complementary submodules `N` and `N'` of an `R`-module `M`, we get a linear equivalence from `N × N'` to `M` by adding the elements of `N` and `N'`. -/
protected noncomputable def linear_equiv (h : complementary N N') :
  (N × N') ≃ₗ[R] M := -- default precendences are wrong
begin
  apply linear_equiv.of_bijective (N.subtype.coprod N'.subtype),
  { refine (eq_bot_iff' _).mpr _, rintro ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ hxx',
    simp only [mem_ker, subtype_apply, submodule.coe_mk, coprod_apply] at hxx',
    have : x = 0,
    { apply disjoint_def.mp h.2 x hx,
      rw [← eq_neg_iff_add_eq_zero] at hxx', rw hxx', exact neg_mem _ hx' },
    subst this, rw [zero_add] at hxx', subst hxx', refl },
  { simp only [range_coprod, range_subtype, h.1.eq_top] }
end

/-- Given two complementary submodules `N` and `N'` of an `R`-module `M`, the projection onto `N` along `N'`. -/
protected noncomputable def pr1 (h : complementary N N') :
  M →ₗ[R] M :=
N.subtype.comp $ (fst R N N').comp h.linear_equiv.symm

lemma pr1_mem (h : complementary N N') (x : M) :
  h.pr1 x ∈ N :=
(fst R N N' $ h.linear_equiv.symm x).2

/-- Given two complementary submodules `N` and `N'` of an `R`-module `M`, the projection onto `N'` along `N`. -/
protected noncomputable def pr2 (h : complementary N N') :
  M →ₗ[R] M :=
N'.subtype.comp $ (snd R N N').comp h.linear_equiv.symm

lemma pr2_mem (h : complementary N N') (x : M) :
  h.pr2 x ∈ N' :=
(snd R N N' $ h.linear_equiv.symm x).2

@[simp] lemma pr1_add_pr2 (h : complementary N N') (x : M) :
  h.pr1 x + h.pr2 x = x :=
h.linear_equiv.right_inv x

lemma pr1_eq_and_pr2_eq (h : complementary N N') {x y z : M}
  (hx : x ∈ N) (hy : y ∈ N') (hz : z = x + y) : h.pr1 z = x ∧ h.pr2 z = y :=
begin
 subst z, have h2 := h.linear_equiv.left_inv (⟨x, hx⟩, ⟨y, hy⟩),
 simp only [prod.ext_iff, subtype.ext] at h2, exact h2
end

lemma pr1_pr1 (h : complementary N N') (x : M) :
  h.pr1 (h.pr1 x) = h.pr1 x :=
(h.pr1_eq_and_pr2_eq (h.pr1_mem x) (zero_mem _) (by rw add_zero)).1

lemma pr2_pr2 (h : complementary N N') (x : M) :
  h.pr2 (h.pr2 x) = h.pr2 x :=
(h.pr1_eq_and_pr2_eq (zero_mem _) (h.pr2_mem x) (by rw zero_add)).2

lemma range_pr1 (h : complementary N N') : range h.pr1 = N :=
by simp [complementary.pr1, range_comp]

lemma range_pr2 (h : complementary N N') : range h.pr2 = N' :=
by simp [complementary.pr2, range_comp]

end complementary

lemma complementary_ker_range {π : M →ₗ[R] M} (hp : is_projection π) :
  complementary (ker π) (range π) :=
begin
  unfold is_projection at hp, split,
  { rw [covering_iff, eq_top_iff'], intro x, rw mem_sup, use (linear_map.id - π) x,
    split, { simp [hp] },
    use π x, simp only [and_true, sub_apply, sub_add_cancel, mem_range, eq_self_iff_true, id_apply],
    use x },
  { intros, rw [disjoint_def], simp only [and_imp, mem_ker, mem_range, mem_inf, exists_imp_distrib],
    intros x hx x' hx', have h2x' := hx', apply_fun π at hx', simp [hp, hx] at hx', cc }
end

-- instance general_linear_group.coe : has_coe (general_linear_group R M) (M →ₗ[R] M) := ⟨λ x, x.1⟩

end submodule
open submodule

section subspace

noncomputable example (s : set V) (hs1 : is_basis K (subtype.val : s → V))
  (hs2 : s.finite) (f : V → K) : K :=
begin let sfin := hs2.to_finset, exact sfin.sum f,
end

/- finding a complementary subspace -/

/-- The set of subspaces disjoint from N (which means they only have 0 in common) -/
def disjoint_subspaces (N : subspace K V) : set (subspace K V) :=
{ N' | disjoint N N' }

lemma mem_disjoint_subspaces {N M : subspace K V} : M ∈ disjoint_subspaces N ↔
  ∀ x : V, x ∈ N → x ∈ M → x = 0 :=
disjoint_def

instance (N : subspace K V) : nonempty (disjoint_subspaces N) :=
⟨⟨⊥, disjoint_bot_right⟩⟩

theorem exists_maximal_disjoint_subspaces (N : subspace K V) :
  ∃ Nmax : disjoint_subspaces N, ∀N, Nmax ≤ N → N = Nmax :=
begin
  apply zorn.zorn_partial_order_nonempty,
  intros c hc h0c, refine ⟨⟨Sup (subtype.val '' c), _⟩, _⟩,
  { rw [mem_disjoint_subspaces],
    intros x h1x h2x, rw [mem_Sup_of_directed] at h2x,
    { rcases h2x with ⟨_, ⟨⟨y, h0y⟩, h1y, rfl⟩, h2y⟩,
      rw [mem_disjoint_subspaces] at h0y, exact h0y x h1x h2y },
    { simp only [set.nonempty_image_iff, h0c] },
    { rw directed_on_image, exact hc.directed_on }},
  { intros N hN, change N.1 ≤ Sup (subtype.val '' c), refine le_Sup _, simp [hN] }
end

theorem exists_complementary_subspace (N : subspace K V) :
  ∃ N' : subspace K V, complementary N N' :=
begin
  rcases exists_maximal_disjoint_subspaces N with ⟨⟨N', h1N'⟩, h2N'⟩,
  use N',
  refine ⟨_, h1N'⟩,
  classical,
  rw [covering_iff, eq_top_iff'], intro x, by_contra H,
  have : disjoint N (N' ⊔ span K {x}),
  { rw disjoint_def, intros y h1y h2y, rw mem_sup at h2y,
    rcases h2y with ⟨z, hz, w, hw, rfl⟩,
    rw mem_span_singleton at hw, rcases hw with ⟨r, rfl⟩,
    by_cases hr : r = 0,
    { subst hr, rw [zero_smul, add_zero] at h1y ⊢, apply mem_disjoint_subspaces.1 h1N' _ h1y hz },
    { exfalso, apply H,
      rw [← smul_mem_iff _ hr],
      rw [← add_mem_iff_right _ (mem_sup_right hz)],
      apply mem_sup_left h1y }},
  have : N' ⊔ span K {x} = N',
  { have := h2N' ⟨_, this⟩ _, rwa [subtype.mk_eq_mk] at this, rw subtype.le_def, exact le_sup_left },
  apply H, apply mem_sup_right, rw ←this, apply mem_sup_right, apply subset_span,
  apply set.mem_singleton
end

end subspace

/-- A representation of a group `G` on an `R`-module `M` is a group homomorphism from `G` to
  `GL(M)`. Normally `M` is a vector space, but we don't need that for the definition. -/
@[derive inhabited] def group_representation (G R M : Type*) [group G] [ring R] [add_comm_group M]
  [module R M] : Type* :=
G →* M →ₗ[R] M

variables {ρ : group_representation G R M} {π : M →ₗ[R] M}

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ f, f.to_fun⟩

/-- A submodule `N` is invariant under a representation `ρ` if `ρ g` maps `N` into `N` for all `g`. -/
def submodule.invariant_under (ρ : group_representation G R M) (N : submodule R M) : Prop :=
∀ x ∈ N, ∀ g : G, ρ g x ∈ N

open submodule

namespace group_representation

/-- An equivalence between two group representations. -/
protected structure equiv (ρ : group_representation G R M) (ρ' : group_representation G R M') :
  Type (max w w') :=
  (α : M ≃ₗ[R] M')
  (commute : ∀(g : G), α ∘ ρ g = ρ' g ∘ α)

--structure subrepresentation (ρ : group_representation G R M) (π : group_representation G R M') :
--  Type (max w w') :=
  --(α : M →ₗ[R] M')
  --(commute : ∀(g : G), α ∘ ρ g = π g ∘ α)
  --left_inv := λ m, show (f.inv * f.val) m = m

/-- An `R`-module `M` is irreducible if every invariant submodule is either `⊥` or `⊤`. -/
def irreducible (ρ : group_representation G R M) : Prop :=
∀ N : submodule R M, N.invariant_under ρ → N = ⊥ ∨ N = ⊤

/- Maschke's theorem -/

/-- A function is equivariant if it commutes with `ρ g` for all `g : G`. -/
def is_equivariant (ρ : group_representation G R M) (π : M →ₗ[R] M) : Prop :=
∀ g : G, ∀ x : M, π (ρ g x) = ρ g (π x)

/-- The invariant projector modifies a projector `π` to be equivariant. -/
def invariant_multiple_of_projector [fintype G] (ρ : group_representation G R M) (π : M →ₗ[R] M) : M →ₗ[R] M :=
finset.univ.sum (λ g : G, ((ρ g⁻¹).comp π).comp (ρ g))

-- lemma invariant_multiple_of_projector_is_scalar_on [fintype G] (r : R) (ρ : group_representation G R M) (π : M →ₗ[R] M)
--    {N : submodule R M} (hR : N.invariant_under ρ) (hp : is_projection_on N π) :
--   ∀ x : N, invariant_multiple_of_projector ρ π x = r • x :=
-- begin dunfold invariant_multiple_of_projector, intro,
--   suffices : ∀ g : G, (comp (comp (ρ g⁻¹) π) (ρ g)) ↑x = r • ↑x,
--   { sorry },
--   unfold is_projection_on at hp,
--   unfold invariant_under at hR,
--  simp, intro, sorry -- simp [(hp ↥N ((ρ g) x)).1, hR x],
-- end

noncomputable def invariant_projector [fintype G] (hG : is_unit (fintype.card G : R)) (ρ : group_representation G R M) (π : M →ₗ[R] M) : M →ₗ[R] M :=
begin
  let invr := is_unit_iff_exists_inv.1 hG,
  exact (classical.some invr) • invariant_multiple_of_projector ρ π
end

-- /-- `π` is a multiple `r` times a projection. -/
-- def is_multiple_of_projection (π : M →ₗ[R] M) (r : R) : Prop := ∀ x, π (π x) = r • π x

-- lemma is_multiple_of_projection_invariant_multiple_of_projector [fintype G] (ρ : group_representation G R M)
--   (π : M →ₗ[R] M) : is_multiple_of_projection (invariant_multiple_of_projector ρ π) (fintype.card G) :=
-- begin sorry
-- end


lemma is_invariant_ker (h : is_equivariant ρ π) : (ker π).invariant_under ρ :=
by { rintros x hx g, rw [mem_ker, h g x, mem_ker.mp hx, linear_map.map_zero] }

lemma sum_apply {α} (s : finset α) (f : α → M →ₗ[R] M) (m : M) :
  s.sum f m = s.sum (λ x, f x m) :=
begin
  classical,
  refine finset.induction _ _ s,
  { refl },
  { intros x s hx h_ind,
    have : finset.sum (insert x s) f = f x + finset.sum s f := by simp [hx],
    rw this, simp [hx, h_ind] }
end

lemma is_equivariant_invariant_projector [fintype G] (hG : is_unit (fintype.card G : R)) (ρ : group_representation G R M)
  (π : M →ₗ[R] M) : is_equivariant ρ (invariant_projector hG ρ π) :=
begin intros g1 x, dunfold invariant_projector, dsimp, rw linear_map.map_smul, congr' 1,
  dunfold invariant_multiple_of_projector, simp [sum_apply],
  apply finset.sum_bij (λ g _, g * g1),
  { intros, apply finset.mem_univ },
  { intros, dsimp, rw [ ρ.map_mul ],
    suffices : (ρ a⁻¹) (π ((ρ a) ((ρ g1) x))) = (ρ (g1 * (a * g1)⁻¹) (π ((ρ a * ρ g1) x))),
    { rw this, rw ρ.map_mul, refl },
    apply congr_fun, congr, simp [mul_inv] },
  { intros g g' _ _ h, simpa using h },
  { intros, use b * g1⁻¹, simp }
end

lemma submodule_comap_smul (f : M →ₗ[R] M) (p : submodule R M) (r : R) (h : is_unit r) :
  p.comap (r • f) = p.comap f :=
begin
  let ur :=  (classical.some h),
  have : r = (ur : R) := (classical.some_spec h).symm,
  ext b; simp only [submodule.mem_comap, linear_map.smul_apply, this, p.smul_mem_iff' ur],
end

lemma submodule_map_smul (f : M →ₗ[R] M) (p : submodule R M) (r : R) (h : is_unit r) :
  p.map (r • f) = p.map f :=
le_antisymm
  begin rw [map_le_iff_le_comap, submodule_comap_smul f _ r h, ← map_le_iff_le_comap], exact le_refl _ end
  begin rw [map_le_iff_le_comap, ← submodule_comap_smul f _ r h, ← map_le_iff_le_comap], exact le_refl _ end

lemma range_smul (f : M →ₗ[R] M) (r : R) (h : is_unit r) : range (r • f) = range f :=
begin exact submodule_map_smul f _ r h
end

lemma invariant_multiple_of_projector_on_range [fintype G] (ρ : group_representation G R M)
  (π : M →ₗ[R] M) (hp : is_projection π) (hR : (range π).invariant_under ρ) {x : M} (h1 : x ∈ range π) :
  invariant_multiple_of_projector ρ π x = (fintype.card G : R) • x :=
begin
  dunfold invariant_multiple_of_projector, rw sum_apply,
  convert finset.sum_const x, ext g, dsimp, {
    have h2 : (ρ g) x ∈ range π := by { apply hR, exact h1 },
    rw mem_range at h2,
    cases h2 with y h3,
    rw [← h3, hp y, h3],
    suffices : (ρ (g⁻¹ * g)) x = x,
    { rw [ρ.map_mul] at this, exact this },
    rw [mul_left_inv, ρ.map_one], refl },
  rw finset.card_univ, symmetry, apply semimodule.smul_eq_smul
end

lemma invariant_projector_on_range [fintype G] (hG : is_unit (fintype.card G : R))
  (ρ : group_representation G R M)
  (π : M →ₗ[R] M) (hp : is_projection π) (hR : (range π).invariant_under ρ) {x : M} (h1 : x ∈ range π) :
  invariant_projector hG ρ π x = x :=
begin
  dunfold invariant_projector, dsimp,
  rw [invariant_multiple_of_projector_on_range ρ π hp hR h1],
  rw [← mul_smul, mul_comm, classical.some_spec (is_unit_iff_exists_inv.1 hG), one_smul],
end

lemma range_invariant_projector [fintype G] (hG : is_unit (fintype.card G : R)) (ρ : group_representation G R M)
  (π : M →ₗ[R] M) (hp : is_projection π) (hR : (range π).invariant_under ρ) :
  range (invariant_projector hG ρ π) = range π :=
begin  unfold invariant_projector,
  let invr :=  classical.some(is_unit_iff_exists_inv.1 hG),
  have h_invr : (fintype.card G : R) * invr = 1 :=
        classical.some_spec (is_unit_iff_exists_inv.1 hG),
  rw [range_smul _ invr],
  ext x, split,
  { rintro ⟨x,hx,rfl⟩, dunfold invariant_multiple_of_projector, rw sum_apply, apply sum_mem, intros, dsimp, apply hR, rw mem_range, exact ⟨_, rfl⟩ },
  { intro hx,
    let x' := invr • π x,
    use x', use trivial,
    have h1 : x' ∈ range π := by { apply smul_mem, rw mem_range, exact ⟨_, rfl⟩ },
    rw [invariant_multiple_of_projector_on_range ρ π hp hR h1],
    simp only [x'], rw [← mul_smul, h_invr, one_smul], rcases hx with ⟨x, hx, rfl⟩, rw hp x },
    { apply is_unit_iff_exists_inv'.mpr, exact ⟨_, h_invr⟩ }
end


lemma is_projection_invariant_projector [fintype G] (hG : is_unit (fintype.card G : R))
  (ρ : group_representation G R M) (π : M →ₗ[R] M) (hp : is_projection π)
  (hR : (range π).invariant_under ρ) : is_projection (invariant_projector hG ρ π) :=
begin
  intro x,
  have : (invariant_projector hG ρ π) x ∈ range (invariant_projector hG ρ π),
  { rw mem_range, exact ⟨_, rfl⟩ },
  rw [range_invariant_projector hG ρ π hp hR] at this,
  rw [invariant_projector_on_range hG ρ π hp hR this]
end

theorem maschke [fintype G] (ρ : group_representation G R M) (N N' : submodule R M)
  (h : complementary N N') (hN : N.invariant_under ρ) (hG : is_unit (fintype.card G : R)) :
  ∃ N' : submodule R M, N'.invariant_under ρ ∧ complementary N N' :=
begin
  let π := invariant_projector hG ρ h.pr1, use ker π,
  use is_invariant_ker (is_equivariant_invariant_projector hG ρ h.pr1),
  suffices hR : (range (complementary.pr1 h)).invariant_under ρ,
  rw [complementary.comm, ← h.range_pr1, ← range_invariant_projector hG ρ h.pr1 h.pr1_pr1 hR],
  convert complementary_ker_range (is_projection_invariant_projector hG ρ h.pr1 h.pr1_pr1 hR),
  rw complementary.range_pr1, exact hN
end

end group_representation


/- from [https://github.com/Shenyang1995/M4R/blob/66f1450f206dc05c3093bc4eaa1361309bf8633b/src/G_module/basic.lean#L10-L14].

  Do we want to use this definition instead? This might allow us to write `g • x` instead of `ρ g x` -/
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)
