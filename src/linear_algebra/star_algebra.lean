/-

C* algebras and related concepts.

Classes defined here:
  star_ring R - has an involution * or ∗
  comm_star_ring R - for example, complex.comm_star_ring
  normed_star_ring R - normed_ring with the norm_star property, norm (x∗) = norm x
  c_star_ring R - normed_ring with the norm_mul_norm_le_norm_star_mul property, norm x * norm x ≤ norm (x∗ * x)
    This implies equality (norm_star_mul) as well as norm_star.
  star_algebra R A - analogous to algebra R A
  normed_star_algebra [R] A - a star_algebra which is also a normed_star_ring
  star_banach_algebra [R] A - like normed_star_algebra and a complete_space
  c_star_algebra [R] A - a star_algebra which is also a c_star_ring and a complete_space
-/

import analysis.normed_space.basic
import algebra.invertible algebra.group.units

-- variables (𝕜 : Type*) [normed_field 𝕜]
variables {R : Type*}

set_option default_priority 50
-- class banach_algebra (A : Type*) [normed_ring A] [complete_space A] extends normed_algebra 𝕜 A

/-- Auxilliary class stating that `α` has a star-operation, a postfix operation `∗`, which can be typed using `\ast`. -/
class has_star (α : Type*) :=
  (star : α → α)

postfix `∗`:(max+10) := has_star.star -- type ∗ using \ast

section star_ring
/-- A star ring, *-ring or involutive ring is a ring with an involution `∗`. -/
class star_ring (R : Type*) extends ring R, has_star R :=
  (add_star : ∀ x y : R, (x + y)∗ = x∗ + y∗)
  (mul_star : ∀ x y : R, (x * y)∗ = y∗ * x∗)
  (one_star : (1 : R)∗ = 1)
  (star_star : ∀ x : R, x∗∗ = x)

variables [star_ring R] {x y z : R}

lemma add_star : (x + y)∗ = x∗ + y∗ := star_ring.add_star x y

lemma mul_star : (x * y)∗ = y∗ * x∗ := star_ring.mul_star x y

lemma one_star : (1 : R)∗ = 1 := star_ring.one_star

@[simp] lemma star_star : x∗∗ = x := star_ring.star_star x

@[simp] lemma zero_star : (0 : R)∗ = 0 :=
by { rw ←add_right_eq_self, symmetry, convert @add_star R _ 0 0, rw add_zero }

lemma neg_star : (- x)∗ = - x∗ :=
by { rw [eq_neg_iff_add_eq_zero, ←add_star, add_left_neg, zero_star] }

lemma sub_star : (x - y)∗ = x∗ - y∗ := by simp only [sub_eq_add_neg, add_star, neg_star]

end star_ring


section comm_star_ring
/--
  A commutative *-ring.

  This definition should be
  `class comm_star_ring (R : Type*) extends comm_ring R, star_ring R`
  but that doesn't work for technical reasons relating to the old structure command.
-/
-- Workaround for
class comm_star_ring (R : Type*) extends comm_ring R, has_star R :=
  (add_star : ∀ x y : R, (x + y)∗ = x∗ + y∗)
  (mul_star : ∀ x y : R, (x * y)∗ = y∗ * x∗)
  (one_star : (1 : R)∗ = 1)
  (star_star : ∀ x : R, x∗∗ = x)

variables [comm_star_ring R] {x y z : R}

@[priority 150] instance comm_star_ring.to_star_ring : star_ring R := { .._inst_1 }

lemma mul_star' : (x * y)∗ = x∗ * y∗ := by rw [mul_star, mul_comm]

instance complex.has_star : has_star ℂ := ⟨complex.conj⟩

noncomputable instance complex.comm_star_ring : comm_star_ring ℂ :=
{ add_star := complex.conj_add,
  mul_star := by { intros x y, rw [mul_comm], apply complex.conj_mul },
  one_star := complex.conj_one,
  star_star := complex.conj_conj,
  ..complex.field, ..complex.has_star }

end comm_star_ring


section normed_star_ring
/--
  A normed *-ring, the part of the structure of a normed involutive algebra that does
  not mention the ring over which it lies.

  This definition should be
  ```
  class normed_star_ring (R : Type*) extends normed_ring R, star_ring R :=
  (norm_star : ∀ x : R, norm (x∗) = norm x)
  ```
  but that doesn't work for technical reasons relating to the old structure command.
-/
class normed_star_ring (R : Type*) extends normed_ring R, has_star R :=
  (add_star : ∀ x y : R, (x + y)∗ = x∗ + y∗)
  (mul_star : ∀ x y : R, (x * y)∗ = y∗ * x∗)
  (one_star : (1 : R)∗ = 1)
  (star_star : ∀ x : R, x∗∗ = x)
  (norm_star : ∀ x : R, norm (x∗) = norm x)

variables [normed_star_ring R] {x y z : R}

@[priority 150] instance normed_star_ring.to_star_ring : star_ring R := { .._inst_1 }

@[simp] lemma norm_star : norm (x∗) = norm x := normed_star_ring.norm_star x

end normed_star_ring

section c_star_ring

/--
  A C*-ring, the part of the structure of a C*-algebra that does not mention the ring
  over which it lies.

  This definition should be
  ```
  class c_star_ring (R : Type*) extends normed_ring R, star_ring R :=
  (norm_mul_norm_le_norm_star_mul : ∀ x : R, norm x * norm x ≤ norm (x∗ * x))
  ```
  but that doesn't work for technical reasons relating to the old structure command.
-/
class c_star_ring (R : Type*) extends normed_ring R, has_star R :=
  (add_star : ∀ x y : R, (x + y)∗ = x∗ + y∗)
  (mul_star : ∀ x y : R, (x * y)∗ = y∗ * x∗)
  (one_star : (1 : R)∗ = 1)
  (star_star : ∀ x : R, x∗∗ = x)
  (norm_mul_norm_le_norm_star_mul : ∀ x : R, norm x * norm x ≤ norm (x∗ * x))

variables [c_star_ring R] {x y z : R}

lemma norm_mul_norm_le_norm_star_mul (x : R) : norm x * norm x ≤ norm (x∗ * x) :=
c_star_ring.norm_mul_norm_le_norm_star_mul x

/-- Every C*-ring is a *-ring. -/
def c_star_ring.to_star_ring : star_ring R := { .._inst_1 }

local attribute [instance, priority 10] c_star_ring.to_star_ring

lemma norm_le_norm_star (x : R) : norm x ≤ norm (x∗) :=
begin
  classical,
  by_cases x = 0, { simp [h] },
  apply le_of_mul_le_mul_right,
  exact le_trans (c_star_ring.norm_mul_norm_le_norm_star_mul x) (norm_mul_le _ _),
  simp [norm_pos_iff, h]
end

@[priority 100] instance c_star_ring.to_normed_star_ring : normed_star_ring R :=
{ norm_star :=
    begin
    intro x, apply le_antisymm,
    { convert norm_le_norm_star x∗, rw star_star },
    { apply norm_le_norm_star }
    end,
  .._inst_1 }

lemma norm_star_mul : norm (x∗ * x) = norm x * norm x :=
begin
  apply le_antisymm,
  { convert norm_mul_le _ _ using 2, rw norm_star },
  { exact c_star_ring.norm_mul_norm_le_norm_star_mul x }
end

lemma norm_mul_star : norm (x * x∗) = norm x * norm x :=
by { convert @norm_star_mul _ _ x∗ using 2; simp only [norm_star, star_star] }

end c_star_ring

/- algebras -/

section star_algebra

/-- A star algebra or *-algebra over a commutative star ring `R` -/
class star_algebra (R : Type*) [comm_star_ring R] (A : Type*) [star_ring A] extends algebra R A :=
  (smul_star : ∀ r : R, ∀ x : A, (r • x)∗ = r∗ • x∗)

variables [comm_star_ring R] {A : Type*} [star_ring A] [star_algebra R A]

/- TODO: lemmas -/

end star_algebra

section normed_star_algebra

/- The following hypotheses state `A` is an normed star algebra or normed involutive algebra over `R` -/
variables [comm_star_ring R] {A : Type*} [normed_star_ring A] [star_algebra R A]

/- TODO: lemmas -/

end normed_star_algebra

section star_banach_algebra

/- The following hypotheses state `A` is an star Banach algebra or involutive Banach algebra over `R` -/

variables [comm_star_ring R] {A : Type*} [normed_star_ring A] [complete_space A] [star_algebra R A]
variables (a b c : A)
variable (R)

def spectrum (a : A) : set R := { x : R | ¬ is_unit ( x • 1 - a ) }
def non_zero_spectrum (a : A) : set R := { x : R | x≠0 ∧ ¬ is_unit ( x • 1 - a ) }

#check spectrum R (a * b) 

open_locale classical

lemma reorder_resolvent (a b : A) [h : invertible (1-a*b)] : invertible (1-b*a) :=
begin
  have h1 : h.inv_of - a*b*h.inv_of = 1 := by sorry, 
  apply_fun (λ x, 1 - b*a + b*x*a) at h1,
  simp at h1,
  have h2 : h.inv_of - h.inv_of*a*b = 1 := by sorry, 
  apply_fun (λ x, 1 - b*a + b*x*a) at h2,
  simp at h2,
  exact ⟨1+b*h.inv_of*a, by simp *, by simp *⟩ 
 end

variable {R}
lemma spectrum_comm (a b : A) : non_zero_spectrum R (a * b) = non_zero_spectrum R (b * a) := 
begin unfold non_zero_spectrum, ext, simp, 
  by_cases x=0, repeat {simp [h]},
  have inv_x : invertible x := by sorry,--apply invertible_of_nonzero h, 
  rw [ ← not_iff_not_of_iff], split,
  { intro, apply is_unit_of_invertible _, 
    apply invertible_mul x (1 - ⅟x * a * b), exact inv_x, 
    },
end

end star_banach_algebra


section c_star_algebra

/-The following hypotheses state that `A` is a C*-algebra over `R` -/
variables [comm_star_ring R] {A : Type*} [c_star_ring A] [complete_space A] [star_algebra R A]

/- TODO: lemmas -/

end c_star_algebra
