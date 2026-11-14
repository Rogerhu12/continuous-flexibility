module

public import ContinuousFlexibility.Analysis.N07aActualChartDifferentials
public import ContinuousFlexibility.Analysis.N07aCoordinateJetNorms
public import ContinuousFlexibility.Analysis.N07aInverseChartDisplacement
public import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# First inverse-chart differences on the canonical strip

The radial and angular difference atoms retain the H^(3/4) gain when
rescaled to the original canonical coordinates. The identity angular
coordinate cancels before taking the derivative.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

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

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

private theorem n07a_fderiv_scaled_pair_bound
    {f g : PolarPoint → ℝ} {x : PolarPoint}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (c : ℝ) :
    ‖fderiv ℝ (fun y => (c * f y, g y)) x‖ ≤
      |c| * ‖fderiv ℝ f x‖ + ‖fderiv ℝ g x‖ := by
  have he : fderiv ℝ (fun y => (c * f y, g y)) x =
      (c • fderiv ℝ f x).prod (fderiv ℝ g x) :=
    ((hf.hasFDerivAt.const_mul c).prodMk hg.hasFDerivAt).fderiv
  rw [he, ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_smul, Real.norm_eq_abs]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (norm_nonneg _)))

theorem n07a_inverseChart_fderiv_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hε : 0 < ε)
    (hrefState : referenceStateConditions D S C)
    (hgeom : CanonicalGeometry D S C K base ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ low : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m y, y ∈ canonicalOpen S K m →
          ‖fderiv ℝ (K.inverseChart (liftSectorParameter S C z) m) y -
              fderiv ℝ (K.inverseChart (C.referenceState, 0) m) y‖ ≤
            e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
              CanonicalGeometry.parameterGrading S low z := by
  let rawLoss := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  let B : ℝ := (hdiff 1).choose
  have hB : 0 < B := (hdiff 1).choose_spec.1
  have hBb := (hdiff 1).choose_spec.2
  let d : ℕ → ℝ := fun m =>
    2 * (1 + (K.right m - K.left m)⁻¹) * (B * T.E0 (T.sample (K.cell m)) ^ B)
  have hd : N07aSampleSubpower T K d := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT 2)
      ((N07aSampleSubpower.const hD hT 1).add
        (n07a_canonicalLengthInverse_subpower hD hT href)))
    (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT B)
      (N07aSampleSubpower.e0_rpow hD hT B))
  have hd0 (m : ℕ) : 0 ≤ d m := by
    have hsample := hT.2.1 _
      (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
    have hlinv : 0 ≤ (K.right m - K.left m)⁻¹ :=
      inv_nonneg.mpr (sub_pos.mpr (hgeom.referenceBounds m).2.1).le
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one hlinv))
      (mul_nonneg hB.le (Real.rpow_nonneg hsample.2.2.1.le B))
  let e : ℕ → ℝ := fun m => (K.physicalRight m - K.physicalLeft m + 1) * d m
  have he : N07aSampleSubpower T K e := N07aSampleSubpower.mul hD hT
    ((n07a_physicalLength_subpower hD hT href).add
      (N07aSampleSubpower.const hD hT 1)) hd
  have he0 (m : ℕ) : 0 ≤ e m := mul_nonneg
    (add_nonneg (sub_pos.mpr (hgeom.referenceBounds m).1).le zero_le_one) (hd0 m)
  refine ⟨1 + rawLoss, e, he, he0, fun z hz m y hy => ?_⟩
  let J (a : CanonicalGeometry.Atom) : PolarPoint → ℝ :=
    (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a -
      CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a) ∘
        n07aCanonicalUnitInversePoint K m
  have hQ : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hJs (a : CanonicalGeometry.Atom) :
      ContDiffOn ℝ ∞ (J a) (canonicalOpen S K m) :=
    ((hcur.1 z hz m a).1.sub (href.1 m a).1).comp
      n07aCanonicalUnitInversePoint_contDiff.contDiffOn
      (n07aCanonicalUnitInversePoint_maps (hgeom.referenceBounds m).2.1)
  have hJd (a : CanonicalGeometry.Atom) : DifferentiableAt ℝ (J a) y :=
    ((hJs a).contDiffAt (hQ.mem_nhds hy)).differentiableAt (by simp)
  have hsample := hT.2.1 _
    (materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m))
  have hH : 0 ≤ T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg hsample.2.1.le _
  have hP : 0 ≤ CanonicalGeometry.parameterGrading S (1 + rawLoss) z := apply_nonneg _ _
  have hE : 0 ≤ B * T.E0 (T.sample (K.cell m)) ^ B :=
    mul_nonneg hB.le (Real.rpow_nonneg hsample.2.2.1.le B)
  have hlinv : 0 ≤ (K.right m - K.left m)⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr (hgeom.referenceBounds m).2.1).le
  have hJb (atom : CanonicalGeometry.Atom) :
      ‖fderiv ℝ (J atom) y‖ ≤ d m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        CanonicalGeometry.parameterGrading S (1 + rawLoss) z := by
    have hb : ‖iteratedFDeriv ℝ 1 (J atom) y‖ ≤
        (2 : ℝ) ^ 1 * ((1 + (K.right m - K.left m)⁻¹) *
          (B * T.E0 (T.sample (K.cell m)) ^ B *
            T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
            CanonicalGeometry.parameterGrading S (1 + rawLoss) z)) := by
      apply norm_iteratedFDeriv_le_of_mixedDerivative hQ (hJs atom) 1 hy
        (mul_nonneg (add_nonneg zero_le_one hlinv) (mul_nonneg (mul_nonneg hE hH) hP))
      intro i j hij
      have hp := n07aCanonicalUnitInversePoint_maps (hgeom.referenceBounds m).2.1 hy
      have hraw := hBb z hz m atom ⟨n07aCanonicalUnitInversePoint K m y, hp⟩
        i j hij.le
      have hpow : (K.right m - K.left m)⁻¹ ^ i ≤ 1 + (K.right m - K.left m)⁻¹ := by
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · simpa only [pow_zero] using le_add_of_nonneg_right hlinv
        · simp only [pow_one]
          exact le_add_of_nonneg_left zero_le_one
      change ‖mixedDerivative i j
        ((CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m atom -
          CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m atom) ∘
            n07aCanonicalUnitInversePoint K m) y‖ ≤ _
      rw [n07a_mixedDerivative_unitInverse, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg hlinv i)]
      exact mul_le_mul hpow hraw (abs_nonneg _) (add_nonneg zero_le_one hlinv)
    rw [norm_iteratedFDeriv_one] at hb
    exact hb.trans_eq (by dsimp only [d]; ring)
  have hL : 0 < K.physicalRight m - K.physicalLeft m :=
    sub_pos.mpr (hgeom.referenceBounds m).1
  have heq : (fun q => K.inverseChart (liftSectorParameter S C z) m q -
        K.inverseChart (C.referenceState, 0) m q) =
      fun q => ((K.physicalRight m - K.physicalLeft m) * J .inverseRadial q,
        J .inverseAngleDefect q) := by
    funext q
    let q' := CanonicalGeometry.canonicalUnitPoint K m (n07aCanonicalUnitInversePoint K m q)
    have hq : q' = q :=
      n07aCanonicalUnitPoint_inverse (hgeom.referenceBounds m).2.1 q
    apply Prod.ext
    · change (K.inverseChart (liftSectorParameter S C z) m q).1 -
          (K.inverseChart (C.referenceState, 0) m q).1 =
        (K.physicalRight m - K.physicalLeft m) *
          (((K.inverseChart (liftSectorParameter S C z) m q').1 - K.physicalLeft m) /
              (K.physicalRight m - K.physicalLeft m) -
            ((K.inverseChart (C.referenceState, 0) m q').1 - K.physicalLeft m) /
              (K.physicalRight m - K.physicalLeft m))
      rw [hq]
      field_simp [hL.ne'] <;> ring
    · change (K.inverseChart (liftSectorParameter S C z) m q).2 -
          (K.inverseChart (C.referenceState, 0) m q).2 =
        ((K.inverseChart (liftSectorParameter S C z) m q').2 - q'.2) -
          ((K.inverseChart (C.referenceState, 0) m q').2 - q'.2)
      rw [hq]
      ring
  have hzstate := liftSectorParameter_mem_stateNeighborhood (S := S) (C := C) hz le_rfl
  have hc := hgeom.charts (liftSectorParameter S C z) hzstate
    (hrefState.liftSectorParameter_sector z) m
  have hzref : (C.referenceState, 0) ∈ stateNeighborhood S C base ε := by
    constructor
    · change stateGrading S base (C.referenceState - C.referenceState) < ε
      have hzero : stateGrading S base (0 : AnnularState S) = 0 :=
        (stateGrading S base).map_zero'
      simpa only [sub_self, hzero] using hε
    · simpa only [abs_zero] using hε
  have hc₀ := hgeom.charts (C.referenceState, 0) hzref hrefState.stateSector m
  have hdG := (hc.2.2.2.2.2.1.contDiffAt (hQ.mem_nhds hy)).differentiableAt (by simp)
  have hdG₀ := (hc₀.2.2.2.2.2.1.contDiffAt (hQ.mem_nhds hy)).differentiableAt (by simp)
  rw [← fderiv_fun_sub hdG hdG₀, heq]
  calc
    _ ≤ |K.physicalRight m - K.physicalLeft m| * ‖fderiv ℝ (J .inverseRadial) y‖ +
        ‖fderiv ℝ (J .inverseAngleDefect) y‖ :=
      n07a_fderiv_scaled_pair_bound (hJd .inverseRadial) (hJd .inverseAngleDefect) _
    _ ≤ |K.physicalRight m - K.physicalLeft m| *
        (d m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          CanonicalGeometry.parameterGrading S (1 + rawLoss) z) +
        (d m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          CanonicalGeometry.parameterGrading S (1 + rawLoss) z) :=
      add_le_add (mul_le_mul_of_nonneg_left (hJb .inverseRadial) (abs_nonneg _))
        (hJb .inverseAngleDefect)
    _ = _ := by rw [abs_of_pos hL]; dsimp only [e]; ring

end ContinuousFlexibility.Analysis
