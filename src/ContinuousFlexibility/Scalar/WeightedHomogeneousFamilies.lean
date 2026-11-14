module

public import ContinuousFlexibility.Scalar.WeightedHomogeneousJets
public import ContinuousFlexibility.Scalar.WeightedUniformTameGerm

/-!
# Fixed-loss bounds for homogeneous operator families

A joint uniform tower is evaluated at zero in the homogeneous inputs.
Its actual first and mixed second derivatives recover the frozen linear
and bilinear maps. The resulting bounds retain one base, one loss and one
state ball, independently of the output order and of the input vectors.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

section Costs

variable {X R Y : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup R] [Module ℝ R]
  [AddCommGroup Y] [Module ℝ Y]

theorem tameJetSize_pure_linear
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ Y)
    (s loss base : ℕ) (x : X) (u : Y) :
    tameJetSize (pairGrading p q) 1 s loss base (x, 0)
      (fun _ : Fin 1 => (0, u)) =
      q (s + loss) u + (1 + p (s + loss) x) * q base u := by
  rw [tameJetSize_one]
  change (1 + (p (s + loss) x + q (s + loss) 0)) *
      (p base 0 + q base u) + (p (s + loss) 0 + q (s + loss) u) = _
  simp only [map_zero, add_zero, zero_add]
  ring

theorem tameJetSize_pure_bilinear
    (p : ℕ → Seminorm ℝ X) (q : ℕ → Seminorm ℝ R)
    (r : ℕ → Seminorm ℝ Y) (s loss base : ℕ) (x : X) (R : R) (u : Y) :
    tameJetSize (pairGrading (pairGrading p q) r) 2 s loss base ((x, 0), 0)
      ![((0, R), 0), ((0, 0), u)] =
      q (s + loss) R * r base u + q base R * r (s + loss) u +
        (1 + p (s + loss) x) * q base R * r base u := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [tameJetSize, Fin.prod_univ_two, Fin.sum_univ_two, h0, h1,
    Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    (1 + ((p (s + loss) x + q (s + loss) 0) + r (s + loss) 0)) *
        (((p base 0 + q base R) + r base 0) *
          ((p base 0 + q base 0) + r base u)) +
      (((p (s + loss) 0 + q (s + loss) R) + r (s + loss) 0) *
          ((p base 0 + q base 0) + r base u) +
        ((p (s + loss) 0 + q (s + loss) 0) + r (s + loss) u) *
          ((p base 0 + q base R) + r base 0)) = _
  simp only [map_zero, add_zero, zero_add]
  ring

end Costs

section Families

variable {X R Y Z : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [TopologicalSpace R] [AddCommGroup R] [Module ℝ R]
  [IsTopologicalAddGroup R] [ContinuousSMul ℝ R]
  [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
  [TopologicalSpace Z] [AddCommGroup Z] [Module ℝ Z] [T2Space Z]

/-- A joint germ of a linear family supplies the exact homogeneous
two-term estimate on one state ball, for every frozen input. -/
theorem uniform_linearFamily_bound_of_jointGerm
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ Y}
    {r : ℕ → Seminorm ℝ Z} {x0 : X} (L : X → Y →ₗ[ℝ] Z)
    (hL : UniformTameGerm (pairGrading p q) r (x0, 0)
      (fun z : X × Y => L z.1 z.2)) :
    ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, p base (x - x0) < ε → ∀ u,
          r s (L x u) ≤ C *
            (q (s + loss) u + (1 + p (s + loss) x) * q base u) := by
  obtain ⟨base, loss, ε, hε, hfixed⟩ := hL
  obtain ⟨J, hJ⟩ := hfixed.2
  refine ⟨base, loss, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hJ 1 s hs
  refine ⟨C, hC, ?_⟩
  intro x hx u
  have hxu : (x, (0 : Y)) ∈
      {z | pairGrading p q base (z - (x0, 0)) < ε} := by
    change p base (x - x0) + q base (0 - 0) < ε
    simpa only [sub_self, map_zero, add_zero] using hx
  have h := hbound (x, 0) hxu (fun _ : Fin 1 => (0, u))
  change r s (J.D 1 (x, 0) (fun _ : Fin 1 => (0, u))) ≤
    C * tameJetSize (pairGrading p q) 1 s loss base (x, 0)
      (fun _ : Fin 1 => (0, u)) at h
  rw [J.linearFamily_first L hxu u, tameJetSize_pure_linear] at h
  exact h

/-- The mixed joint second derivative supplies the exact three-term
estimate for a family with two homogeneous inputs. -/
theorem uniform_bilinearFamily_bound_of_jointGerm
    {p : ℕ → Seminorm ℝ X} {q : ℕ → Seminorm ℝ R}
    {r : ℕ → Seminorm ℝ Y} {t : ℕ → Seminorm ℝ Z}
    {x0 : X} (B : X → R →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hB : UniformTameGerm (pairGrading (pairGrading p q) r) t ((x0, 0), 0)
      (fun z : (X × R) × Y => B z.1.1 z.1.2 z.2)) :
    ∃ base loss : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x, p base (x - x0) < ε → ∀ R u,
          t s (B x R u) ≤ C *
            (q (s + loss) R * r base u + q base R * r (s + loss) u +
              (1 + p (s + loss) x) * q base R * r base u) := by
  obtain ⟨base, loss, ε, hε, hfixed⟩ := hB
  obtain ⟨J, hJ⟩ := hfixed.2
  refine ⟨base, loss, ε, hε, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hJ 2 s hs
  refine ⟨C, hC, ?_⟩
  intro x hx dr u
  have hxRu : ((x, (0 : R)), (0 : Y)) ∈
      {z | pairGrading (pairGrading p q) r base (z - ((x0, 0), 0)) < ε} := by
    change (p base (x - x0) + q base (0 - 0)) + r base (0 - 0) < ε
    simpa only [sub_self, map_zero, add_zero] using hx
  have h := hbound ((x, 0), 0) hxRu ![((0, dr), 0), ((0, 0), u)]
  change t s (J.D 2 ((x, 0), 0) ![((0, dr), 0), ((0, 0), u)]) ≤
    C * tameJetSize (pairGrading (pairGrading p q) r) 2 s loss base
      ((x, 0), 0) ![((0, dr), 0), ((0, 0), u)] at h
  rw [J.bilinearFamily_second B hxRu dr u, tameJetSize_pure_bilinear] at h
  exact h

end Families

end ContinuousFlexibility.Statements
