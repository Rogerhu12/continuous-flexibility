import ContinuousFlexibility.Analysis.N04RealizationHeightTowerJets
import ContinuousFlexibility.Analysis.N04RealizationMaterialTransfer
import ContinuousFlexibility.Analysis.N01cCoefficientBaseSelection
import ContinuousFlexibility.Analysis.N01cCoefficientPolarPowerInputs
import ContinuousFlexibility.Analysis.N01cPhysicalGraphNormalization
import ContinuousFlexibility.Analysis.SmoothDirectionsAffine

/-!
# Spatial powers for the actual height-valued towers

The fixed loss of a genuine height tower is interpolated once, before
either the parameter prefix or the spatial order is chosen. The full
physical height factor is retained even at parameter order zero. This
allows the actual point-to-sample transfer to precede any relaxation of
the zeroth-order estimate near a component endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Finite collection and interpolation of an already proved physical
tower estimate. The height factor is unchanged at every parameter order. -/
theorem n04Realization_oneHigh_spatialPower_prefix
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (center : X)
    {oldBase base loss offset : ℕ} (hbase : oldBase ≤ base)
    {U : Set X} {Ω : Set PolarPoint} {H E : PolarPoint → ℝ}
    {f : X → PolarPoint → ℝ} (RF : MixedJetRegularity U Ω f)
    (hH : ∀ q ∈ Ω, 0 ≤ H q) (hE : ∀ q ∈ Ω, 1 ≤ E q)
    (hI : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≤ s → ∀ x : X, p base x ≤ 1 →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) x ≤ R →
        p (n + offset) x ≤ C * R ^ ((n : ℝ) / ((s : ℝ) + 1)))
    (hraw : ∀ k n : ℕ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ a b : ℕ, a + b ≤ n → ∀ q (hq : q ∈ Ω),
      ∀ x ∈ U, ∀ v : Fin k → X,
        |(RF.parameter a b q hq).D k x v| ≤ C * E q ^ A * H q *
          oneHighVariationWeight p oldBase (n + offset) (x - center) v) :
    ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ Ω, ∀ J : SmoothDirections U (fun x => mixedDerivative a b (f x) q),
      ∀ x ∈ U, p base (x - center) ≤ 1 →
      ∀ v : Fin k → X, (∀ i, p base (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + loss) (x - center) ≤ R →
        (∀ i, p (s + loss) (v i) ≤ R) →
        ‖J.D k x v‖ ≤ C * E q ^ A * H q *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  intro K s
  let P : (Fin (K + 1) × Fin (s + 1)) → ℝ → ℝ → Prop := fun i C A =>
    ∀ a b : ℕ, a + b ≤ i.2.val → ∀ q (hq : q ∈ Ω),
    ∀ x ∈ U, ∀ v : Fin i.1.val → X,
      |(RF.parameter a b q hq).D i.1.val x v| ≤ C * E q ^ A * H q *
        oneHighVariationWeight p oldBase (i.2.val + offset) (x - center) v
  have hmono : ∀ i C A C' A', 1 ≤ C → 0 ≤ A → C ≤ C' → A ≤ A' →
      P i C A → P i C' A' := by
    intro i C A C' A' hC _ hCC hAA hb a b hab q hq x hx v
    have hCE : C * E q ^ A ≤ C' * E q ^ A' :=
      mul_le_mul hCC (Real.rpow_le_rpow_of_exponent_le (hE q hq) hAA)
        (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)
        ((zero_le_one.trans hC).trans hCC)
    exact (hb a b hab q hq x hx v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCE (hH q hq))
        (oneHighVariationWeight_nonneg p oldBase (i.2.val + offset) (x - center) v))
  have hbound : ∀ i, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ P i C A := by
    intro i
    obtain ⟨C, A, hC, hA, hb⟩ := hraw i.1.val i.2.val
    refine ⟨1 + C, A, by linarith, hA, ?_⟩
    intro a b hab q hq x hx v
    exact (hb a b hab q hq x hx v).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : C ≤ 1 + C)
            (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)) (hH q hq))
        (oneHighVariationWeight_nonneg p oldBase (i.2.val + offset) (x - center) v))
  obtain ⟨C₀, A, hC₀, hA, hb⟩ := exists_finite_graph_materialConstants P hmono hbound
  obtain ⟨CI, hCI, hIb⟩ := hI s
  let B : ℝ := 1 + (K + 1 : ℝ) * CI
  have hB : 1 ≤ B := le_add_of_nonneg_right
    (mul_nonneg (by positivity) (zero_le_one.trans hCI))
  refine ⟨C₀ * B, A, one_le_mul_of_one_le_of_one_le hC₀ hB, hA, ?_⟩
  intro k hk a b hab q hq J x hx hlow v hv R hR hhigh hvhigh
  let i : Fin (K + 1) × Fin (s + 1) :=
    (⟨k, Nat.lt_succ_of_le hk⟩, ⟨a + b, Nat.lt_succ_of_le hab⟩)
  have hrawq := hb i a b le_rfl q hq x hx v
  have hvold (j : Fin k) : p oldBase (v j) ≤ 1 := (hp hbase (v j)).trans (hv j)
  have hP : 1 ≤ R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    Real.one_le_rpow hR (spatialOrder_fraction_nonneg (a + b) s)
  have hoh := oneHighVariationWeight_unit_le_power p oldBase (a + b + offset)
    hk (x - center) v hvold (zero_le_one.trans hCI) hP
    (hIb (a + b) hab _ hlow R hR hhigh)
    (fun j => hIb (a + b) hab _ (hv j) R hR (hvhigh j))
  have hfactor : 0 ≤ C₀ * E q ^ A * H q :=
    mul_nonneg (mul_nonneg (zero_le_one.trans hC₀)
      (Real.rpow_nonneg (zero_le_one.trans (hE q hq)) _)) (hH q hq)
  rw [J.unique (RF.parameter a b q hq) k x hx, Real.norm_eq_abs]
  calc
    _ ≤ C₀ * E q ^ A * H q *
        oneHighVariationWeight p oldBase (a + b + offset) (x - center) v := hrawq
    _ ≤ C₀ * E q ^ A * H q *
        (B * R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hoh hfactor
    _ = _ := by ring

/-- One interpolation choice controls every finite prefix of the actual
decoded height, with the same physical `H^γ` gain even for `k = 0`. -/
theorem n04Realization_heightTower_spatialPower_bounds
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {M : SobolevModelData}
    (hT : IsMaterialData D T) (hM : IsSobolevModel D T γ M)
    {p : ℕ → Seminorm ℝ X} (hp : Monotone p) (hIp : HasInterpolation p)
    {U : Set X} {f : X → M.Space} {base loss : ℕ}
    (J : SmoothDirections U f)
    (hJ : UniformScalarTowerEstimate p M.grading U base loss f J)
    (hE : ∀ r ∈ Ioo D.a D.b, 1 ≤ T.E0 r) :
    ∃ B L : ℕ, base ≤ B ∧
      ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q ∈ annularOpen D,
        ∀ Jq : SmoothDirections U (fun x => mixedDerivative a b (M.decode (f x)) q),
        ∀ x ∈ U, p B x ≤ 1 →
        ∀ v : Fin k → X, (∀ i, p B (v i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p (s + L) x ≤ R →
          (∀ i, p (s + L) (v i) ≤ R) →
          ‖Jq.D k x v‖ ≤ C * T.E0 q.1 ^ A * T.H q.1 ^ γ *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  apply exists_base_ge_of_spatialPower_continuation p hp hIp base (base + 2 + loss)
  intro B L hB hI
  have hraw := n04Realization_oneHigh_spatialPower_prefix hp (0 : X) hB
    (n04Realization_heightMixedJetRegularity hT hM J)
    (fun q hq => Real.rpow_nonneg (hT.2.1 q.1 hq.1).2.1.le γ)
    (fun q hq => hE q.1 hq.1) hI (by
      intro k n
      obtain ⟨C, A, hC, hA, hb⟩ :=
        n04Realization_heightTower_physicalJets_bound hT hM J hJ k n
      refine ⟨C, A, hC, hA, fun a b hab q hq x hx v => ?_⟩
      simpa only [sub_zero] using hb x hx v a b hab q hq)
  simpa only [sub_zero] using hraw

/-- Transfer to the supplied sample before discarding any height gain.
The points may lie in different material cells, and all constants precede
both points and the actual parameter evaluation. -/
theorem n04Realization_sample_spatialPower_prefix
    {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hγ : 0 < γ) {p : ℕ → Seminorm ℝ X}
    {U : Set X} {f : X → PolarPoint → ℝ} {B L : ℕ}
    {Lshift : ℝ} (hLshift : 0 ≤ Lshift)
    (hb : ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
      ∀ q ∈ annularOpen D,
      ∀ Jq : SmoothDirections U (fun x => mixedDerivative a b (f x) q),
      ∀ x ∈ U, p B x ≤ 1 →
      ∀ v : Fin k → X, (∀ i, p B (v i) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → p (s + L) x ≤ R →
        (∀ i, p (s + L) (v i) ≤ R) →
        ‖Jq.D k x v‖ ≤ C * T.E0 q.1 ^ A * T.H q.1 ^ γ *
          R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1))) :
    ∀ K s : ℕ, ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧
        ∀ k : ℕ, k ≤ K → ∀ a b : ℕ, a + b ≤ s →
        ∀ q ∈ annularOpen D, ∀ sample ∈ Ioo D.a D.b,
        endpointX 1 (Statements.endpointDistance D sample) ≤
          endpointX 1 (Statements.endpointDistance D q.1) + Lshift →
        ∀ Jq : SmoothDirections U (fun x => mixedDerivative a b (f x) q),
        ∀ x ∈ U, p B x ≤ 1 →
        ∀ v : Fin k → X, (∀ i, p B (v i) ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → p (s + L) x ≤ R →
          (∀ i, p (s + L) (v i) ≤ R) →
          ‖Jq.D k x v‖ ≤ C * T.E0 sample ^ A * T.H sample ^ γ *
            R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by
  intro K s
  obtain ⟨C₀, A₀, hC₀, hA₀, hraw⟩ := hb K s
  obtain ⟨CW, A, hCW, hA, htransfer⟩ :=
    n04Realization_material_H_E0_rpow_oneSided hT hD hγ hA₀ hLshift
  refine ⟨C₀ * max 1 CW, A,
    one_le_mul_of_one_le_of_one_le hC₀ (le_max_left _ _), hA, ?_⟩
  intro k hk a b hab q hq sample hsample hshift Jq x hx hlow v hv R hR hhigh hvhigh
  have hrawq := hraw k hk a b hab q hq Jq x hx hlow v hv R hR hhigh hvhigh
  have hsampleFactor : 0 ≤ T.H sample ^ γ * T.E0 sample ^ A :=
    mul_nonneg (Real.rpow_nonneg (hT.2.1 sample hsample).2.1.le _)
      (Real.rpow_nonneg (hT.2.1 sample hsample).2.2.1.le _)
  have hweight : T.H q.1 ^ γ * T.E0 q.1 ^ A₀ ≤
      max 1 CW * (T.H sample ^ γ * T.E0 sample ^ A) :=
    (htransfer q.1 sample hq.1 hsample hshift).trans
      (by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (le_max_right 1 CW) hsampleFactor)
  have hpower : 0 ≤ R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
    Real.rpow_nonneg (zero_le_one.trans hR) _
  calc
    _ ≤ C₀ * T.E0 q.1 ^ A₀ * T.H q.1 ^ γ *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := hrawq
    _ = C₀ * (T.H q.1 ^ γ * T.E0 q.1 ^ A₀) *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) := by ring
    _ ≤ C₀ * (max 1 CW * (T.H sample ^ γ * T.E0 sample ^ A)) *
        R ^ (((a + b : ℕ) : ℝ) / ((s : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight (zero_le_one.trans hC₀)) hpower
    _ = _ := by ring

end ContinuousFlexibility.Analysis
