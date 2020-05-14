/- Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Douglas, Floris van Doorn
-/

import order.zorn algebra.module

universe variable u

namespace tactic
namespace interactive
setup_tactic_parser
open tactic.interactive
meta def dunfold_coes (loc : parse location) : tactic unit :=
dunfold [
  ``coe, ``coe_t, ``has_coe_t.coe, ``coe_b,``has_coe.coe,
  ``lift, ``has_lift.lift, ``lift_t, ``has_lift_t.lift,
  ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe,
  ``coe_base_aux, ``has_coe_t_aux.coe] loc
  -- note: this adds extra arguments
  -- todo: we need to repeat it, it is not idempotent.
end interactive
end tactic


@[simp] lemma inv_smul_smul {K V : Type*} [field K] [add_comm_group V] [vector_space K V]
  {k : K} {x : V} (h : k ≠ 0) : k⁻¹ • k • x = x :=
by rw [←mul_smul, inv_mul_cancel h, one_smul]

@[simp] lemma smul_inv_smul {K V : Type*} [field K] [add_comm_group V] [vector_space K V]
  {k : K} {x : V} (h : k ≠ 0) : k • k⁻¹ • x = x :=
by rw [←mul_smul, mul_inv_cancel h, one_smul]

lemma subtype.le_def {α : Type*} [partial_order α] {P : α → Prop} {x y : α}
  {hx : P x} {hy : P y} : (⟨x, hx⟩ : subtype P) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.refl _

lemma subtype.prop {α} {p : α → Prop} (x : subtype p) : p x := x.2


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