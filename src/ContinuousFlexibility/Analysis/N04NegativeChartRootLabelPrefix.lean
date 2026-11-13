import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelAngularPrefix
import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelCircleBounds
import ContinuousFlexibility.Analysis.N04NegativeChartInteriorMaterial
import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.MaterialEnvelopeNormalization

/-!
# Fractional prefixes for the literal endpoint labels

Both endpoint labels retain their original sector parameters. Their
displacements are the decoders of the same fixed-base circle family.
The value bound is unweighted; every positive state jet keeps one copy
of the height at the exact selected negative half sample.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped BigOperators

variable {X I : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Change the scalar realization and sample weight before specializing
the parameter space. The power and the finite-prefix quantifiers are
unchanged by this transfer. -/
theorem N04FixedBaseSmoothFamilyOn.circle_angular_sample_prefix
    {T : MaterialData} {γ : ℝ} {H : CircleModelData}
    {p : ℕ → Seminorm ℝ X} {U : Set X} {f : I → X → H.Space}
    (hf : N04FixedBaseSmoothFamilyOn p H.grading U f)
    (hp : Monotone p) (hI : HasInterpolation p)
    (hH : IsCircleModel T γ H) (hpos : ∀ m, 0 < T.H (T.sample m))
    (requestedBase : ℕ) (E W : ℕ → I → ℝ)
    (hE : ∀ m i, 1 ≤ E m i) (hW : ∀ m i, 0 ≤ W m i)
    (hupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ m, T.H (T.sample m) ^ γ ≤ M)
    (hweight : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ m i,
      T.H (T.sample m) ^ γ ≤ C * E m i ^ A * W m i)
    (g : I → ℕ → X → ℝ → ℝ)
    (heq : ∀ i m x, x ∈ U → ∀ θ, g i m x θ = H.decode (f i x) m θ) :
    ∃ base : ℕ, requestedBase ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → ∀ j : ℕ, j ≤ s + 1 → ∀ i m θ,
      ∀ J : SmoothDirections U (fun x => iteratedDeriv j (g i m x) θ),
      ∀ x ∈ U, p base x ≤ 1 → ∀ v : Fin k → X,
      (∀ d, p base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (base + s + shift * K + 1) x ≤ R →
      (∀ d, p (base + s + shift * K + 1) (v d) ≤ R) →
        |J.D k x v| ≤ B * E m i ^ B * parameterHeightWeight (W m i) k *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  obtain ⟨M, hM, hupper⟩ := hupper
  obtain ⟨Ch, A, hCh, hA, hweight⟩ := hweight
  let D : ℝ := Ch + M + 1
  have hD : 0 ≤ D := by dsimp only [D]; linarith only [hCh, hM]
  have hparam (k m i) : T.H (T.sample m) ^ γ ≤
      D * E m i ^ A * parameterHeightWeight (W m i) k := by
    by_cases hk : k = 0
    · have hMD : M ≤ D := by dsimp only [D]; linarith only [hCh]
      have hh := (hupper m).trans (hMD.trans
        (le_mul_of_one_le_right hD (Real.one_le_rpow (hE m i) hA)))
      simpa only [hk, parameterHeightWeight, ↓reduceIte, mul_one] using hh
    · have hCD : Ch ≤ D := by dsimp only [D]; linarith only [hM]
      have hh := (hweight m i).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD
          (Real.rpow_nonneg (zero_le_one.trans (hE m i)) _)) (hW m i))
      simpa only [parameterHeightWeight, if_neg hk] using hh
  obtain ⟨base, hbase, hprefix⟩ :=
    hf.circle_angular_first_prefix hp hI hH hpos requestedBase
  refine ⟨base, hbase, fun K => ?_⟩
  obtain ⟨shift, hshift⟩ := hprefix K
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨C, hC, hb⟩ := hshift s
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (C * D) A
  refine ⟨B, hB, ?_⟩
  intro k hk j hj i m θ J x hx hxlow v hvlow R hR hxhigh hvhigh
  let Q : SmoothDirections U (fun y => iteratedDeriv j (H.decode (f i y) m) θ) :=
    J.congrOn (fun y hy => congrArg (fun u : ℝ → ℝ => iteratedDeriv j u θ)
      (funext (fun η => heq i m y hy η)))
  have hh : |J.D k x v| ≤ C * T.H (T.sample m) ^ γ *
      R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
        (((s + shift * K : ℕ) : ℝ) + 1)) :=
    hb k hk j hj i m θ Q x hx hxlow v hvlow R hR hxhigh hvhigh
  have hcoef : C * T.H (T.sample m) ^ γ ≤
      B * E m i ^ B * parameterHeightWeight (W m i) k := by
    calc
      _ ≤ C * (D * E m i ^ A * parameterHeightWeight (W m i) k) :=
        mul_le_mul_of_nonneg_left (hparam k m i) hC
      _ = ((C * D) * E m i ^ A) * parameterHeightWeight (W m i) k := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hpack (E m i) (hE m i))
        (parameterHeightWeight_nonneg (hW m i) k)
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef
    (Real.rpow_nonneg (zero_le_one.trans hR) _))

namespace N04RealizationStart

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

set_option backward.isDefEq.respectTransparency true

variable (W : N04RealizationStart)

private theorem rootLabel_displacement_decode (side : Bool) (m : ℕ)
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε) (θ : ℝ) :
    n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m side θ - θ =
      (W.S.circle (3 / 4 : ℝ)).decode
        (W.through03.1.1.n04RootLabelCircle W.hS W.hT side z) m θ := by
  have hh := congrFun
    (W.through03.1.1.n04RootLabelCircle_lift W.hS W.hT side z hz m) θ
  simp only [circleAffineLift, add_zero, one_mul] at hh
  linarith only [hh]

/-- The actual left and right label displacements have one fractional
prefix at the exact half sample. This includes the zeroth state and
angular orders and permits any genuine scalar angular tower. -/
theorem negativeRootLabel_angular_prefix (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ base : ℕ, W.base ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ k : ℕ, k ≤ K → ∀ j : ℕ, j ≤ s + 1 → ∀ side m θ,
      ∀ J : SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε)
        (fun z => iteratedDeriv j
          (fun η => n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m side η - η) θ),
      ∀ z ∈ sectorNeighborhood W.S W.base W.ε W.ε,
      parameterGrading W.S base z ≤ 1 → ∀ v : Fin k → Parameter W.S,
      (∀ d, parameterGrading W.S base (v d) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      parameterGrading W.S (base + s + shift * K + 1) z ≤ R →
      (∀ d, parameterGrading W.S (base + s + shift * K + 1) (v d) ≤ R) →
        |J.D k z v| ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hfamily := W.through03.1.1.n04FixedBase_rootLabelCircle W.hS W.hT
    (W.cutoff.sector_flow_slope W.through03.1.1)
  have hi : HasInterpolation (parameterGrading W.S) :=
    hasInterpolation_of_hasSmoothing (sectorPairGrading_monotone W.S)
      (hasSmoothing_pairGrading (solve_sector_hasSmoothing W.hS) hasSmoothing_realGrading)
  have hpos := (material_circle_sample_weights_pos W.hT W.radial.1).2
  have hu := materialSample_H_M_envelope W.hT W.radial.1
    (γ := (3 / 4 : ℝ)) (by norm_num) 0
  have hupper : ∃ M : ℝ, 0 ≤ M ∧ ∀ m, W.T.H (W.T.sample m) ^ (3 / 4 : ℝ) ≤ M :=
    ⟨hu.choose, hu.choose_spec.1.le, fun m => by
      simpa only [Real.rpow_zero, mul_one] using hu.choose_spec.2 m⟩
  exact hfamily.circle_angular_sample_prefix (sectorPairGrading_monotone W.S) hi
    (W.hS.2.1 (3 / 4 : ℝ)) hpos W.base
    (fun m side => W.T.E0 (W.negativeHalfSample e m side))
    (fun m side => W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ))
    (fun _ _ => W.floor _) (fun _ _ => Real.rpow_nonneg (hpos _).le _)
    hupper (W.negativeCircleSample_half_height e)
    (fun side m z θ => n01RootLabel W.S W.C (liftSectorParameter W.S W.C z) m side θ - θ)
    W.rootLabel_displacement_decode

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_angular_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_angular_prefix
