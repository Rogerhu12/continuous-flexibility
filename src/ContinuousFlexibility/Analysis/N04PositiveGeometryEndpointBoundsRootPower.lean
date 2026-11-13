import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsRootMaterial
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs
import ContinuousFlexibility.Analysis.N01cStateInterpolation

/-!
# Distributed angular powers for the actual finite radial root inputs

The finite radial prefix is absorbed into one fixed interpolation loss.
Consequently its angular orders, and not the number of radial factors,
determine the spatial scale in each product. The same base is selected
before every parameter prefix. The input maps are the literal four
normalized height fields multiplied by the original scalar parameter.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04PositiveRootPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- One base and one loss suffice for every parameter order of a fixed
finite radial prefix. The original `H^(3/4)` gain is kept even at zero
parameter order. -/
theorem n04PositiveGeometry_rootHeightInputs_finiteRadial_power
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r)
    (x0 : AnnularState S) (N requestedBase : ℕ) :
    ∃ B loss : ℕ, requestedBase ≤ B ∧ ∀ K s : ℕ,
      ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ i : Fin 4, ∀ a : ℕ, a ≤ N → ∀ b : ℕ, b ≤ s →
      ∀ p ∈ annularOpen D, ∀ U : Set (AnnularState S × ℝ),
      ∀ J : SmoothDirections U (fun z => z.2 *
        mixedDerivative a b (n06RootNormalizedHeightFields D S z.1.1 i) p),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ U, |z.2| ≤ 1 →
      pairGrading (stateGrading S) realGrading B (z - (x0, 0)) ≤ 1 →
      ∀ v : Fin k → (AnnularState S × ℝ),
      (∀ j, pairGrading (stateGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (stateGrading S) realGrading (s + loss) (z - (x0, 0)) ≤ R →
      (∀ j, pairGrading (stateGrading S) realGrading (s + loss) (v j) ≤ R) →
        |J.D k z v| ≤ C * T.E0 p.1 ^ A * T.H p.1 ^ scalarBeta *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let pjoint := pairGrading (stateGrading S) realGrading
  have hp : Monotone pjoint := jointStateGrading_monotone S
  obtain ⟨B, loss, hB, hI⟩ := exists_base_ge_of_spatialPower_continuation
    pjoint hp (jointStateGrading_hasInterpolation hS) requestedBase (N + 7)
    (fun B loss => ∀ s : ℕ, ∃ CI : ℝ, 1 ≤ CI ∧
      ∀ n : ℕ, n ≤ s → ∀ x : AnnularState S × ℝ, pjoint B x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → pjoint (s + loss) x ≤ R →
        pjoint (n + (N + 7)) x ≤ CI * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (fun _ _ _ h => h)
  refine ⟨B, loss, hB, fun K s => ?_⟩
  choose c A hc hA hb using fun b : Fin (s + 1) =>
    n04PositiveGeometry_rootHeightInputs_material_oneHigh hD hT hS (N + b.val)
  let C0 : ℝ := 1 + ∑ b : Fin (s + 1), c b
  let A0 : ℝ := ∑ b : Fin (s + 1), A b
  have hC0 : 1 ≤ C0 := le_add_of_nonneg_right (Finset.sum_nonneg (fun b _ => hc b))
  have hA0 : 0 ≤ A0 := Finset.sum_nonneg (fun b _ => hA b)
  have hc0 (b : Fin (s + 1)) : c b ≤ C0 :=
    (Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ b)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hAA (b : Fin (s + 1)) : A b ≤ A0 :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ b)
  obtain ⟨CI, hCI, hIb⟩ := hI s
  let Q : ℝ := 1 + (K + 1 : ℝ) * CI
  let M : ℝ := 1 + stateGrading S (N + s + 7) x0
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hQ : 1 ≤ Q := le_add_of_nonneg_right
    (mul_nonneg (by positivity) (zero_le_one.trans hCI))
  refine ⟨C0 * M * Q, A0,
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC0 hM) hQ, hA0, ?_⟩
  intro i a ha b hbs q hq U J k hk z hz hzq hzlow v hv R hR hzR hvR
  let j : Fin (s + 1) := ⟨b, Nat.lt_succ_of_le hbs⟩
  have hraw := hb j i a b (by change a + b ≤ N + b; omega)
    q hq U J k B x0 z hz hzq v
  have hcenter : 1 + stateGrading S (N + b + 7) x0 ≤ M :=
    add_le_add_left (stateGrading_monotone S (by omega) x0) 1
  have hpow : 1 ≤ R ^ ((b : ℝ) / ((s : ℝ) + 1)) :=
    Real.one_le_rpow hR (by positivity)
  have horder (x : AnnularState S × ℝ) (hx : pjoint B x ≤ 1)
      (hxR : pjoint (s + loss) x ≤ R) :
      pjoint (N + b + 7) x ≤ CI * R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
    have he : b + (N + 7) = N + b + 7 := by omega
    simpa only [he] using hIb b hbs x hx R hR hxR
  have hoh := oneHighVariationWeight_unit_le_power pjoint B (N + b + 7)
    hk (z - (x0, 0)) v hv (zero_le_one.trans hCI) hpow
    (horder _ hzlow hzR) (fun t => horder _ (hv t) (hvR t))
  have hH : 0 ≤ T.H q.1 ^ scalarBeta := Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le _
  have hE0 : 1 ≤ T.E0 q.1 := hE q.1 hq.1
  have hCE : c j * T.E0 q.1 ^ A j ≤ C0 * T.E0 q.1 ^ A0 :=
    mul_le_mul (hc0 j) (Real.rpow_le_rpow_of_exponent_le hE0 (hAA j))
      (Real.rpow_nonneg (zero_le_one.trans hE0) _) (zero_le_one.trans hC0)
  have hCEH : 0 ≤ C0 * T.E0 q.1 ^ A0 * T.H q.1 ^ scalarBeta :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
      (Real.rpow_nonneg (zero_le_one.trans hE0) _)) hH
  have hscaled := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_right hCE hH) hcenter
      (by positivity : 0 ≤ 1 + stateGrading S (N + b + 7) x0) hCEH)
    hoh (oneHighVariationWeight_nonneg pjoint B (N + b + 7) (z - (x0, 0)) v)
    (mul_nonneg hCEH (zero_le_one.trans hM))
  exact hraw.trans (hscaled.trans_eq (by dsimp only [Q]; ring))

end ContinuousFlexibility.Analysis
