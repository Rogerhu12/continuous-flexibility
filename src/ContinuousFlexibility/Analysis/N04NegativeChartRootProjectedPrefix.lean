import ContinuousFlexibility.Analysis.N04NegativeChartRootActualComposition
import ContinuousFlexibility.Analysis.N04NegativeChartRootCoordinateBounds
import ContinuousFlexibility.Analysis.N04NegativeChartNormalizedPrefix
import ContinuousFlexibility.Analysis.N04NegativeChartPolarization
import ContinuousFlexibility.Analysis.SmoothDirectionsPermutationSymmetry

/-! The actual root projections retain the original fractional state
budget. A single finite state line supplies diagonal jets; symmetry and
polarization return arbitrary directions without changing the base. -/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

private theorem rootProjected_endpoint_contDiff
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)
    {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun x : P × N04FlowPoint =>
      h (x.1, A.inverse x.1 x.2.1 1 x.2.2) - x.2.2) := by
  have hi : ContDiff ℝ ∞ (fun x : P × N04FlowPoint =>
      A.inverse x.1 x.2.1 1 x.2.2) := by
    simpa only [Function.comp_def, negativeChartRootPlotTimeChange,
      compactScalarFlowTime_one] using A.inverse_smooth.comp
        ((contDiff_fst.prodMk contDiff_snd.fst).prodMk
          ((contDiff_const (c := (1 : ℝ))).prodMk contDiff_snd.snd))
  exact (hh.comp (contDiff_fst.prodMk hi)).sub contDiff_snd.snd

private theorem rootProjected_normalized_prefix
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d c : P × PolarPoint → ℝ} {δ : ℝ} (A : NegativeChartRootFlowData d c δ)
    {h : P × ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (k : ℕ) (v : Fin k → P)
    (s a b D K : ℕ) (hab : a + b ≤ s) (odd : Bool)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) {M R : ℝ} (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hraw : ∀ j, j ≤ s + 1 → ∀ q : N04FlowPoint,
      q.1 ∈ n04FlowParameterBox → 0 < q.1.1 →
      ‖iteratedFDeriv ℝ j (fun q : N04FlowPoint =>
        iteratedFDeriv ℝ k (fun y => h (y, A.inverse y q.1 1 q.2) - q.2) 0 v) q‖ ≤
        M * R ^ (((j - 1 + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1))) :
    CSBound (a + b + if odd then 1 else 0)
      (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
      (fun q => iteratedFDeriv ℝ k (fun y =>
        h (y, A.inverse y (q.1, Real.sqrt δ * q.2.1) 1 q.2.2) - q.2.2) 0 v)
      (M * R ^ (((a + b + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1))) := by
  let g : N04FlowPoint → ℝ := fun q =>
    iteratedFDeriv ℝ k (fun y => h (y, A.inverse y q.1 1 q.2) - q.2) 0 v
  have hg : ContDiff ℝ ∞ g :=
    n04NegativeChart_partial_stateJet_contDiff (rootProjected_endpoint_contDiff A hh) k 0 v
  have hτ : |Real.sqrt δ| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg δ)]
    nlinarith only [Real.sqrt_nonneg δ, Real.sq_sqrt hδ, hδone]
  have hb := n04NegativeChart_rootNormalized_csBound
    (M := M * R ^ (((a + b + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1))) hg hτ
    (a + b + if odd then 1 else 0) (fun j hj q hq hx => by
      have hj' : j ≤ s + 1 := by split_ifs at hj <;> omega
      have hn : j - 1 + D * k ≤ a + b + D * k := by split_ifs at hj <;> omega
      have hnℝ : ((j - 1 + D * k : ℕ) : ℝ) ≤ ((a + b + D * k : ℕ) : ℝ) := by
        exact_mod_cast hn
      exact (hraw j hj' q hq hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR
          (div_le_div_of_nonneg_right hnℝ (by positivity))) hM))
  simpa only [g, Function.comp_def, rootFlowNormalizedArgument_apply] using hb

namespace N04RealizationStart.NegativeOpticalFactors

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
  interiorRaw_parameterTopology interiorRaw_parameterAddGroup interiorRaw_parameterSMul

set_option backward.isDefEq.respectTransparency true

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  {F : W.NegativeOpticalFactors e} {sourceBase loss : ℕ}

/-- The material scale is the same low-input choice throughout. The
stored prefix covers the whole normalized half before a positive band
is subsequently selected. -/
structure RootProjectedPrefixData (Q : F.FullHalfFieldPowerControl sourceBase loss) where
  base : ℕ
  ε : ℝ
  base_le : W.base ≤ base
  sourceBase_le : sourceBase ≤ base
  lowBase_le : Q.root_low_input.choose ≤ base
  ε_pos : 0 < ε
  ε_half : ε ≤ min (W.ε / 2) (1 / 2 : ℝ)
  ε_low : ε ≤ Q.root_low_input.choose_spec.choose
  scale : 1 ≤ Q.rootCompositionScaleCoefficient
  «prefix» : ∀ K : ℕ, 0 < K → ∃ D : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧
    ∀ m (side odd : Bool) (q : PolarPoint), q.1 ∈ Ioc (0 : ℝ) 1 →
    ∀ k, k ≤ K → ∀ a b, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b (W.negativeRootPrefixField m side odd
        (W.negativeChartRootScale e Q.rootCompositionScaleCoefficient m side) z) q),
    ∀ z, z ∈ sectorNeighborhood W.S base ε ε → ∀ v : Fin k → Parameter W.S,
      (∀ i, parameterGrading W.S base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (base + s + D * K + 1) z ≤ R →
      (∀ i, parameterGrading W.S (base + s + D * K + 1) (v i) ≤ R) →
      ‖J.D k z v‖ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((a + b + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1))

private theorem rootProjected_prefix_of_endpoint
    {base : ℕ} {ε C : ℝ} (hbase : W.base ≤ base)
    (hε : ε ≤ W.ε / 2) (hεsmall : ε ≤ 1 / 2) (hC : 1 ≤ C)
    (K D s : ℕ) (M : ℝ) (hM : 0 < M)
    (hraw : ∀ m side z, z ∈ sectorNeighborhood W.S base ε ε →
      parameterGrading W.S base z ≤ 1 →
      ∀ L : (Fin 1 → ℝ) →L[ℝ] Parameter W.S,
      ∀ A : NegativeRootRepresentative F base ε z L m side (W.negativeChartRootScale e C m side),
      ∀ k, k ≤ K → ∀ v : Fin k → (Fin 1 → ℝ),
      (∀ i, parameterGrading W.S base (L (v i)) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (base + s + D * K + 1) z ≤ R →
      (∀ i, parameterGrading W.S (base + s + D * K + 1) (L (v i)) ≤ R) →
      ∀ j, j ≤ s + 1 → ∀ q : N04FlowPoint,
      q.1 ∈ n04FlowParameterBox → 0 < q.1.1 →
      ‖iteratedFDeriv ℝ j (fun q : N04FlowPoint =>
        iteratedFDeriv ℝ k (fun y => A.h (y, A.flow.inverse y q.1 1 q.2) - q.2) 0 v) q‖ ≤
        M * W.T.E0 (W.negativeHalfSample e m side) ^ M *
          parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((j - 1 + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1))) :
    ∃ B : ℝ, 0 < B ∧
    ∀ m (side odd : Bool) (q : PolarPoint), q.1 ∈ Ioc (0 : ℝ) 1 →
    ∀ k, k ≤ K → ∀ a b, a + b ≤ s →
    ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
      (fun z => mixedDerivative a b
        (W.negativeRootPrefixField m side odd (W.negativeChartRootScale e C m side) z) q),
    ∀ z, z ∈ sectorNeighborhood W.S base ε ε → ∀ v : Fin k → Parameter W.S,
      (∀ i, parameterGrading W.S base (v i) ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading W.S (base + s + D * K + 1) z ≤ R →
      (∀ i, parameterGrading W.S (base + s + D * K + 1) (v i) ≤ R) →
      ‖J.D k z v‖ ≤ B * W.T.E0 (W.negativeHalfSample e m side) ^ B *
        parameterHeightWeight (W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)) k *
          R ^ (((a + b + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1)) := by
  classical
  let Cp : Fin (K + 1) → ℝ := fun n => (n04NegativeChart_twoBall_polarization n.val).choose
  have hCp (n : Fin (K + 1)) : 0 ≤ Cp n :=
    (n04NegativeChart_twoBall_polarization n.val).choose_spec.1
  let P : ℝ := 1 + ∑ n : Fin (K + 1), Cp n
  have hCP (n : Fin (K + 1)) : Cp n ≤ P :=
    (Finset.single_le_sum (fun j _ => hCp j) (Finset.mem_univ n)).trans
      (le_add_of_nonneg_left zero_le_one)
  let Cj := (n04NegativeChart_rootProjection_affine_bound
    (X := Parameter W.S) (P := Fin 1 → ℝ) s).choose
  have hCj : 0 < Cj := (n04NegativeChart_rootProjection_affine_bound
    (X := Parameter W.S) (P := Fin 1 → ℝ) s).choose_spec.1
  have hpack := coefficientEnvelope_pack (P * Cj * M) M
  refine ⟨hpack.choose, hpack.choose_spec.1, ?_⟩
  intro m side odd q hq k hk a b hab J z hz v hv R hR hzR hvR
  let E := W.T.E0 (W.negativeHalfSample e m side)
  let H := W.T.H (W.negativeHalfSample e m side) ^ (3 / 4 : ℝ)
  let β : ℝ := ((a + b + D * k : ℕ) : ℝ) / (((s + D * K : ℕ) : ℝ) + 1)
  let T : ℝ := M * E ^ M * parameterHeightWeight H k
  have hE : 1 ≤ E := W.floor _
  have hH : 0 ≤ H := Real.rpow_nonneg (W.hT.2.1 _
    (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  have hT : 0 ≤ T := mul_nonneg
    (mul_nonneg hM.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
    (parameterHeightWeight_nonneg hH k)
  have hpow : 0 ≤ R ^ β := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hzlow := n04NegativeGeometry_parameterGrading_le_one W.S base hεsmall hz
  have hs := W.negativeChartRootScale_bounds e hC m side
  have hdiag (w : Parameter W.S) (hw : parameterGrading W.S base w ≤ 1)
      (hwR : parameterGrading W.S (base + s + D * K + 1) w ≤ R) :
      |J.D k z (fun _ => w)| ≤ Cj * (T * R ^ β) := by
    let L := finiteDirectionMap (fun _ : Fin 1 => w)
    let u : Fin k → (Fin 1 → ℝ) := fun _ => Pi.single (0 : Fin 1) (1 : ℝ)
    have hu (i : Fin k) : L (u i) = w := by
      simp only [L, u, finiteDirectionMap_single, one_smul]
    let A := (negativeRootRepresentative_nonempty F hbase hε z hz L m side
      (W.negativeChartRootScale e C m side)).some
    have hr := hraw m side z hz hzlow L A k hk u
      (fun i => by simpa only [hu i] using hw) R hR hzR
      (fun i => by simpa only [hu i] using hwR)
    have hn := rootProjected_normalized_prefix A.flow A.hh k u s a b D K hab odd
      hs.1.le hs.2.1 hT hR hr
    have hc : CSBound (a + b + if odd then 1 else 0)
        (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℝ))
        (fun p => iteratedFDeriv ℝ k (fun y => A.coordinate y p) 0 u) (T * R ^ β) := by
      simpa only [NegativeRootRepresentative.coordinate] using hn
    have hb := A.projection_bound s hbase hε hs.1 hs.2.2.1 odd k u
      (mul_nonneg hT hpow) a b hab hc q hq J
    simpa only [hu] using hb
  let i : Fin (K + 1) := ⟨k, by omega⟩
  have hp := (n04NegativeChart_twoBall_polarization k).choose_spec.2
    (Parameter W.S) (parameterGrading W.S base) (parameterGrading W.S (base + s + D * K + 1))
    (J.D k z).toMultilinearMap
    (fun u σ => J.comp_perm (sectorNeighborhood_convex W.S base ε ε) k z hz u σ)
    (Cj * (T * R ^ β)) R (mul_nonneg hCj.le (mul_nonneg hT hpow))
    (zero_lt_one.trans_le hR) hdiag v hv hvR
  have hp' := hp.trans (mul_le_mul_of_nonneg_right (hCP i)
    (mul_nonneg hCj.le (mul_nonneg hT hpow)))
  have he : P * (Cj * (T * R ^ β)) =
      (P * Cj * M) * E ^ M * parameterHeightWeight H k * R ^ β := by
    dsimp only [T]; ring
  have hb := (hp'.trans_eq he).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hpack.choose_spec.2 E hE)
      (parameterHeightWeight_nonneg hH k)) hpow)
  simpa only [ContinuousMultilinearMap.coe_coe, Real.norm_eq_abs, E, H, β] using hb

/-- The actual endpoint estimate supplies both root projections with
one common base, neighborhood and material scale before all orders. -/
theorem FullHalfFieldPowerControl.rootProjectedPrefix_nonempty
    (Q : F.FullHalfFieldPowerControl sourceBase loss) :
    Nonempty (RootProjectedPrefixData Q) := by
  have hex := Q.actualRootComposition_prefix
  let base := hex.choose
  let ε := hex.choose_spec.choose
  have h := hex.choose_spec.choose_spec
  have hε := h.2.2.2.2.1
  have hC := h.2.2.2.2.2.2.1
  refine ⟨{
    base := base, ε := ε, base_le := h.1, sourceBase_le := h.2.1,
    lowBase_le := h.2.2.1, ε_pos := h.2.2.2.1, ε_half := hε,
    ε_low := h.2.2.2.2.2.1, scale := hC, «prefix» := ?_ }⟩
  intro K hK
  have hD := h.2.2.2.2.2.2.2 K hK
  refine ⟨hD.choose, fun s => ?_⟩
  have hs := hD.choose_spec s
  apply rootProjected_prefix_of_endpoint (F := F) h.1 (hε.trans (min_le_left _ _))
    (hε.trans (min_le_right _ _)) hC K hD.choose s hs.choose hs.choose_spec.1
  intro m side z hz hzlow L A k hk v hv R hR hzR hvR j hj q hq hqx
  exact hs.choose_spec.2 m side _ (W.negativeChartRootScale_bounds e hC m side).1 le_rfl
    z hz hzlow L A k hk v hv R hR hzR hvR j hj q hq hqx

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.rootProjectedPrefix_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.FullHalfFieldPowerControl.rootProjectedPrefix_nonempty
