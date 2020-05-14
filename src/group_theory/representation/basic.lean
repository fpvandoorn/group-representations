/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Douglas, Floris van Doorn
-/
import linear_algebra.finite_dimensional linear_algebra.bilinear_form
import data.fintype.card tactic.apply_fun

universe variables u v w w' w''

open linear_map

@[simp] lemma inv_smul_smul {K V : Type*} [field K] [add_comm_group V] [vector_space K V]
  {k : K} {x : V} (h : k ≠ 0) : k⁻¹ • k • x = x :=
by rw [←mul_smul, inv_mul_cancel h, one_smul]

@[simp] lemma smul_inv_smul {K V : Type*} [field K] [add_comm_group V] [vector_space K V]
  {k : K} {x : V} (h : k ≠ 0) : k • k⁻¹ • x = x :=
by rw [←mul_smul, mul_inv_cancel h, one_smul]

lemma subtype.le_def {α : Type*} [partial_order α] {P : α → Prop} {x y : α}
  {hx : P x} {hy : P y} : (⟨x, hx⟩ : subtype P) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.refl _

namespace zorn

/- A version of Zorn's lemma for partial orders where we only have to find an upper bound for nonempty chains -/
theorem zorn_partial_order_nonempty {α : Type u} [partial_order α] [nonempty α]
  (h : ∀c:set α, chain (≤) c → c.nonempty → ∃ub, ∀a∈c, a ≤ ub) : ∃m:α, ∀a, m ≤ a → a = m :=
begin
  apply zorn_partial_order,
  intros c hc, classical,
  cases c.eq_empty_or_nonempty with h2c h2c,
  { have := _inst_2, cases this with x, use x, intro y, rw h2c, rintro ⟨⟩ },
  { exact h c hc h2c },
end

end zorn

section lattice
variables {α : Type*} [semilattice_sup_top α]


/-- Two elements of a lattice are covering if their sup is the top element. -/
def covering (a b : α) : Prop := ⊤ ≤ a ⊔ b

theorem covering.eq_top {a b : α} (h : covering a b) : a ⊔ b = ⊤ :=
eq_top_iff.2 h

theorem covering_iff {a b : α} : covering a b ↔ a ⊔ b = ⊤ :=
eq_top_iff.symm

theorem covering.comm {a b : α} : covering a b ↔ covering b a :=
by rw [covering, covering, sup_comm]

theorem covering.symm {a b : α} : covering a b → covering b a :=
covering.comm.1

@[simp] theorem covering_top_left {a : α} : covering ⊤ a := covering_iff.2 top_sup_eq
@[simp] theorem covering_top_right {a : α} : covering a ⊤ := covering_iff.2 sup_top_eq

theorem covering.mono {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h : covering a c) : covering b d :=
le_trans h (sup_le_sup h₁ h₂)

theorem covering.mono_left {a b c : α} (h : a ≤ b) : covering a c → covering b c :=
covering.mono h (le_refl _)

theorem covering.mono_right {a b c : α} (h : b ≤ c) : covering a b → covering a c :=
covering.mono (le_refl _) h

@[simp] lemma covering_self {a : α} : covering a a ↔ a = ⊤ :=
by simp [covering]

lemma covering.ne {a b : α} (ha : a ≠ ⊤) (hab : covering a b) : a ≠ b :=
by { intro h, rw [←h, covering_self] at hab, exact ha hab }

end lattice

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

/-- Two elements in a lattice are complementary if they have meet ⊥ and join ⊤. -/
def complementary {α} [bounded_lattice α] (x x' : α) : Prop :=
covering x x' ∧ disjoint x x'

lemma complementary_symm {α} [bounded_lattice α] {x x' : α} :
  complementary x x' ↔ complementary x' x :=
sorry

namespace complementary
/-- Given two complementary submodules `N` and `N'` of an `R`-module `M`, we get a linear equivalence from `N × N'` to `M` by adding the elements of `N` and `N'`. -/
protected noncomputable def linear_equiv (h : complementary N N') :
  (N × N') ≃ₗ[R] M := -- default precendences are wrong
begin
  apply linear_equiv.of_bijective (N.subtype.coprod N'.subtype),
  { rw [eq_bot_iff'], rintro ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ hxx',
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

instance general_linear_group.coe : has_coe (general_linear_group R M) (M →ₗ[R] M) := ⟨λ x, x.1⟩

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
G →* general_linear_group R M

variables {ρ : group_representation G R M} {π : M →ₗ[R] M}

instance : has_coe_to_fun (group_representation G R M) := ⟨_, λ f, f.to_fun⟩

/-- A submodule `N` is invariant under a representation `ρ` if `ρ g` maps `N` into `N` for all `g`. -/
def submodule.invariant_under (ρ : group_representation G R M) (N : submodule R M) : Prop :=
∀ x : N, ∀ g : G, ρ g x ∈ N

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
def invariant_projector [fintype G] (ρ : group_representation G R M) (π : M →ₗ[R] M) : M →ₗ[R] M :=
finset.univ.sum (λ g : G, ((ρ g⁻¹).1.comp π).comp (ρ g))

/-- `π` is a multiple `r` times a projection. -/
def is_multiple_of_projection (π : M →ₗ[R] M) (r : R) : Prop := ∀ x, π (π x) = r • π x

lemma is_invariant_ker (h : is_equivariant ρ π) : (ker π).invariant_under ρ :=
begin
  rintros x g, rw [mem_ker, h g x],
  have := x.2, unfold ker comap at this, dsimp [submodule.has_coe] at this, unfold_coes at this,
  sorry
end

lemma is_equivariant_invariant_projector [fintype G] (ρ : group_representation G R M) (π : M →ₗ[R] M) :
  is_equivariant ρ (invariant_projector ρ π) :=
sorry

lemma is_multiple_of_projection_invariant_projector [fintype G] (ρ : group_representation G R M)
  (π : M →ₗ[R] M) : is_multiple_of_projection (invariant_projector ρ π) (fintype.card G) :=
sorry

lemma range_invariant_projector [fintype G] (ρ : group_representation G R M) (π : M →ₗ[R] M) :
  range (invariant_projector ρ π) = range π :=
sorry

lemma complementary_ker_range {π : M →ₗ[R] M} {r : R} (hr : is_unit r)
  (h : is_multiple_of_projection π r) : complementary (ker π) (range π) :=
begin
  sorry
  -- unfold is_projection, intro hp, split,
  -- { rw [covering_iff, eq_top_iff'], intro x, rw mem_sup, use (linear_map.id - π) x,
  --   split, { simp [hp] },
  --   use π x, simp only [and_true, sub_apply, sub_add_cancel, mem_range, eq_self_iff_true, id_apply],
  --   use x },
  -- { intros, rw [disjoint_def], simp only [and_imp, mem_ker, mem_range, mem_inf, exists_imp_distrib],
  --   intros x hx x' hx', have h2x' := hx', apply_fun π at hx', simp [hp, hx] at hx', cc }
end

theorem maschke2 [fintype G] (ρ : group_representation G R M) (N N' : submodule R M)
  (h : complementary N N') (hN : N.invariant_under ρ) (hG : is_unit (fintype.card G : R)) :
  ∃ N' : submodule R M, N'.invariant_under ρ ∧ complementary N N' :=
begin
  let π := invariant_projector ρ h.pr1,
  use ker π,
  use is_invariant_ker (is_equivariant_invariant_projector ρ h.pr1),
  rw [complementary_symm, ← h.range_pr1, ← range_invariant_projector ρ h.pr1],
  convert complementary_ker_range hG (is_multiple_of_projection_invariant_projector ρ h.pr1)
end


end group_representation


/- from [https://github.com/Shenyang1995/M4R/blob/66f1450f206dc05c3093bc4eaa1361309bf8633b/src/G_module/basic.lean#L10-L14].

  Do we want to use this definition instead? This might allow us to write `g • x` instead of `ρ g x` -/
class G_module (G : Type*) [group G] (M : Type*) [add_comm_group M]
  extends has_scalar G M :=
(id : ∀ m : M, (1 : G) • m = m)
(mul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(linear : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)
