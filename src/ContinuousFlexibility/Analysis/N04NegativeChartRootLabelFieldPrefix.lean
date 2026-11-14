import ContinuousFlexibility.Analysis.N04NegativeChartRootLabelRepresentative
import ContinuousFlexibility.Analysis.PointwiseAffineMaterialJets
import ContinuousFlexibility.Analysis.N04FlowJetsTarget

/-!
# The raw label field at the original state and half sample

The label displacement depends only on the state and angular coordinates.
Its spatial jets therefore cost exactly their angular order. The unit
angle projection has norm at most one; neither the two root coordinates
nor the unused time coordinate adds a power or a constant.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

/-- The original label displacement as a field for the same flow calculus. -/
def negativeChartRootLabelField (h : P × ℝ → ℝ) :
    (P × PolarPoint) × PolarPoint → ℝ :=
  fun q => h (q.1.1, q.2.2) - q.2.2

theorem negativeChartRootLabelField_contDiff {h : P × ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (negativeChartRootLabelField h) :=
  (hh.comp (contDiff_fst.fst.prodMk contDiff_snd.snd)).sub contDiff_snd.snd

/-- The unused root coordinates are fixed, so these are the original
finite state derivatives in their original slot order. -/
theorem negativeChartRootLabelField_stateJet {h : P × ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (k : ℕ) (v : Fin k → P) (t : ℝ) (q : N04FlowPoint) :
    flowParameterField (negativeChartRootLabelField h) k (0, q.1)
      (fun i => (v i, (0 : PolarPoint))) (t, q.2) =
        iteratedFDeriv ℝ k (fun y => h (y, q.2) - q.2) 0 v := by
  let f : P × PolarPoint → ℝ := fun z => negativeChartRootLabelField h (z, (t, q.2))
  have hf : ContDiff ℝ ∞ f :=
    (negativeChartRootLabelField_contDiff hh).comp (contDiff_id.prodMk contDiff_const)
  exact (flowParameterField_eq_joint hf k 0 v q.1).symm

/-- The angular projection has norm at most one, including at order zero. -/
theorem negativeChartRootLabelField_stateJet_spatial_le {h : P × ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (k j : ℕ) (v : Fin k → P) (t : ℝ) (q : N04FlowPoint) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootLabelField h) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ ≤
      |iteratedDeriv j (fun θ => iteratedFDeriv ℝ k (fun y => h (y, θ) - θ) 0 v) q.2| := by
  let f : P × PolarPoint → ℝ := fun z => h (z.1, z.2.2) - z.2.2
  have hf : ContDiff ℝ ∞ f :=
    (hh.comp (contDiff_fst.prodMk contDiff_snd.snd)).sub contDiff_snd.snd
  let g : ℝ → ℝ := fun θ => iteratedFDeriv ℝ k (fun y => h (y, θ) - θ) 0 v
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_flowParameterField hf k 0 v).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun θ : ℝ => (t, θ)))
  have he : (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootLabelField h) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) = fun y => g y.2 :=
    funext (negativeChartRootLabelField_stateJet hh k v t)
  rw [he]
  let L : N04FlowPoint →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ PolarPoint ℝ
  have hL : ‖L‖ ^ j ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ PolarPoint ℝ)
  have hb := (norm_iteratedFDeriv_comp_linear_le_at (x := q) L hg.contDiffAt j).trans
    (mul_le_mul_of_nonneg_left hL (norm_nonneg (iteratedFDeriv ℝ j g (L q))))
  simpa only [L, g, Function.comp_def, ContinuousLinearMap.coe_snd', mul_one,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using hb

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

/-- The needed scalar angular towers are supplied by the existing actual
circle family; their existence is not a quantitative assumption. -/
def negativeRootLabelDisplacementAngularTower (m : ℕ) (side : Bool) (b : ℕ) (θ : ℝ) :
    SmoothDirections (sectorNeighborhood W.S W.base W.ε W.ε)
      (fun x => iteratedDeriv b
        (fun η => n01RootLabel W.S W.C (liftSectorParameter W.S W.C x) m side η - η) θ) := by
  have hf := W.through03.1.1.n04FixedBase_rootLabelCircle W.hS W.hT
    (W.cutoff.sector_flow_slope W.through03.1.1)
  apply (circleDecodedAngularDirections (W.hS.2.1 (3 / 4 : ℝ))
    (hf.choose side) b m θ).congrOn
  intro z hz
  apply congrArg (fun f : ℝ → ℝ => iteratedDeriv b f θ)
  funext η
  have he := congrFun
    (W.through03.1.1.n04RootLabelCircle_lift W.hS W.hT side z hz m) η
  simp only [circleAffineLift, add_zero, one_mul] at he
  linarith only [he]

/-- Any globally smooth representative with the actual complete fibre
germ has the same spatial bound from the original scalar tower. -/
theorem negativeRootLabel_field_spatialJet_le
    (z : Parameter W.S) (hz : z ∈ sectorNeighborhood W.S W.base W.ε W.ε)
    (L : P →L[ℝ] Parameter W.S) (m : ℕ) (side : Bool)
    {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    (heq : ∀ y ∈ V, ∀ θ, h (y, θ) =
      n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ)
    (k j : ℕ) (v : Fin k → P) (t : ℝ) (q : N04FlowPoint) :
    ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
      flowParameterField (negativeChartRootLabelField h) k (0, y.1)
        (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ ≤
      |(W.negativeRootLabelDisplacementAngularTower m side j q.2).D k z (fun i => L (v i))| := by
  have he := W.negativeRootLabel_finiteRepresentative_parameterAngularJet
    z hz L m side hV h0 heq (W.negativeRootLabelDisplacementAngularTower m side) k j q.2 v
  exact (negativeChartRootLabelField_stateJet_spatial_le hh k j v t q).trans_eq
    (congrArg abs he)

/-- One base works before every state prefix and every finite parameter
space. The same constants apply to every smooth representative with the
actual uniform fibre germ, and retain the exact selected half sample. -/
theorem negativeRootLabel_field_prefix (e : ℕ ≃ N04PieceIndex W.D) :
    ∃ base : ℕ, W.base ≤ base ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q],
      ∀ k : ℕ, k ≤ K → ∀ j : ℕ, j ≤ s + 1 → ∀ m side,
      ∀ z ∈ sectorNeighborhood W.S W.base W.ε W.ε,
      parameterGrading W.S base z ≤ 1 → ∀ L : Q →L[ℝ] Parameter W.S,
      ∀ h : Q × ℝ → ℝ, ContDiff ℝ ∞ h → ∀ V : Set Q, IsOpen V → (0 : Q) ∈ V →
      (∀ y ∈ V, ∀ θ, h (y, θ) =
        n01RootLabel W.S W.C (liftSectorParameter W.S W.C (z + L y)) m side θ) →
      ∀ v : Fin k → Q, (∀ i, parameterGrading W.S base (L (v i)) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (base + s + shift * K + 1) z ≤ R →
      (∀ i, parameterGrading W.S (base + s + shift * K + 1) (L (v i)) ≤ R) →
      ∀ t : ℝ, ∀ q : N04FlowPoint,
      ‖iteratedFDeriv ℝ j (fun y : N04FlowPoint =>
        flowParameterField (negativeChartRootLabelField h) k (0, y.1)
          (fun i => (v i, (0 : PolarPoint))) (t, y.2)) q‖ ≤
        B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((j - 1 + shift * k : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hb := W.negativeRootLabel_angular_prefix e
  refine ⟨hb.choose, hb.choose_spec.1, fun K => ?_⟩
  have hk := hb.choose_spec.2 K
  refine ⟨hk.choose, fun s => ?_⟩
  have hs := hk.choose_spec s
  refine ⟨hs.choose, hs.choose_spec.1, ?_⟩
  intro Q _ _ _ k hk' j hj m side z hz hlow L h hh V hV h0 heq v hv R hR hzR hvR t q
  exact (W.negativeRootLabel_field_spatialJet_le z hz L m side hh hV h0 heq k j v t q).trans
    (hs.choose_spec.2 k hk' j hj side m q.2
      (W.negativeRootLabelDisplacementAngularTower m side j q.2)
      z hz hlow (fun i => L (v i)) hv R hR hzR hvR)

end N04RealizationStart
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_field_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.negativeRootLabel_field_prefix
