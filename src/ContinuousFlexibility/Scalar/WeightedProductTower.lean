import ContinuousFlexibility.Scalar.WeightedDecodedProductMap
import ContinuousFlexibility.Scalar.WeightedBilinearTower

/-!
# Fixed-neighborhood towers for actual weighted multiplication

The multiplication is the genuine continuous multilinear product constructed
from the physical weighted jets.  Its uniform derivative tower has the same
base and loss on every chosen low-seminorm ball, including all derivative
orders and the original model topology.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped BigOperators

/-- The two-input one-high sum, proved without exposing a represented
multilinear map or its decoder construction. -/
theorem oneHigh_fin_two {E : Type*} [AddCommGroup E] [Module ℝ E]
    (low high : Seminorm ℝ E) (x y : E) :
    (∑ i : Fin 2, high (![x, y] i) *
      ∏ j ∈ Finset.univ.erase i, low (![x, y] j)) =
      high x * low y + low x * high y := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [Fin.sum_univ_two, h0, h1, Finset.prod_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The triangle inequality on a translated seminorm ball, independently
of any concrete projective representation. -/
theorem seminorm_le_radius_add_center {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) {x x0 : E} {ε : ℝ} (hx : p (x - x0) < ε) :
    p x ≤ ε + p x0 := by
  calc
    p x = p ((x - x0) + x0) := by rw [sub_add_cancel]
    _ ≤ p (x - x0) + p x0 := map_add_le_add _ _ _
    _ ≤ ε + p x0 := add_le_add hx.le (le_refl _)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements.SobolevModelData

open Set ContinuousFlexibility.Analysis
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {A : SobolevModelData}

/-- The actual binary product inherits a two-factor estimate from the
all-arity product estimate, with the same fixed orders. -/
theorem decodedProductMap_twoFactor
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : A.Space,
        A.grading s (bilinearJetValue (decodedProductMap hT hA hinterp hγ 1) x y) ≤
          C * (A.grading (s + loss) x * A.grading base y +
            A.grading base x * A.grading (s + loss) y) := by
  obtain ⟨base, loss, hbase, hprod⟩ := decodedProductMap_oneHigh hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro s _
  obtain ⟨C, hC, hCu⟩ := hprod 1 s
  refine ⟨C, hC, fun x y => ?_⟩
  change A.grading s (decodedProductMap hT hA hinterp hγ 1 ![x, y]) ≤ _
  rw [← oneHigh_fin_two (A.grading base) (A.grading (s + loss)) x y]
  exact hCu ![x, y]

/-- Actual weighted multiplication admits one uniform tower on each open
domain where the same fixed low pair seminorm is bounded. -/
theorem decodedProductMap_fixedNeighborhoodSmoothTame
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ U : Set (A.Space × A.Space), IsOpen U →
      ∀ R : ℝ, 0 ≤ R → (∀ x ∈ U, pairGrading A.grading A.grading base x ≤ R) →
        FixedNeighborhoodSmoothTame (pairGrading A.grading A.grading) A.grading U base loss
          (fun x : A.Space × A.Space => decodedProductMap hT hA hinterp hγ 1 ![x.1, x.2]) := by
  obtain ⟨base, loss, hbase, hB⟩ := decodedProductMap_twoFactor hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro U hU R hR hxR
  exact fixedNeighborhoodSmoothTame_bilinearMultilinear
    (decodedProductMap hT hA hinterp hγ 1) hB hU hR hxR

/-- The actual product has a genuine uniform fixed-loss tower on every
positive-radius low-seminorm ball, without changing the base or loss with
the derivative order, ball center, or radius. -/
theorem decodedProductMap_on_lowBall
    (hT : IsMaterialData D T) (hA : IsSobolevModel D T γ A)
    (hinterp : HasInterpolation A.grading) (hγ : 0 ≤ γ) :
    ∃ base loss : ℕ, 2 ≤ base ∧ ∀ x0 : A.Space × A.Space, ∀ ε : ℝ, 0 < ε →
      FixedNeighborhoodSmoothTame (pairGrading A.grading A.grading) A.grading
        {x | pairGrading A.grading A.grading base (x - x0) < ε} base loss
        (fun x : A.Space × A.Space => decodedProductMap hT hA hinterp hγ 1 ![x.1, x.2]) := by
  obtain ⟨base, loss, hbase, hB⟩ := decodedProductMap_fixedNeighborhoodSmoothTame hT hA hinterp hγ
  refine ⟨base, loss, hbase, ?_⟩
  intro x0 ε hε
  let P : Seminorm ℝ (A.Space × A.Space) := pairGrading A.grading A.grading base
  have hp : Continuous (A.grading base) :=
    (withSeminorms_graded (fun n => A.level n) A.bond).continuous_seminorm base
  have hP : Continuous P := by
    change Continuous (fun z : A.Space × A.Space => A.grading base z.1 + A.grading base z.2)
    exact (hp.comp continuous_fst).add (hp.comp continuous_snd)
  have hU : IsOpen {x | P (x - x0) < ε} :=
    isOpen_lt (hP.comp (continuous_id.sub continuous_const)) continuous_const
  have hR : 0 ≤ ε + P x0 := add_nonneg hε.le (apply_nonneg _ _)
  apply hB {x | P (x - x0) < ε} hU (ε + P x0) hR
  intro x hx
  exact seminorm_le_radius_add_center P hx

end ContinuousFlexibility.Statements.SobolevModelData
