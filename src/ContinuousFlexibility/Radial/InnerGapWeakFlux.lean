module

public import ContinuousFlexibility.Radial.InnerGapDirichletWeak
public import ContinuousFlexibility.Radial.InnerGapPoissonL2

/-!
# The same gap Poisson operator, weak conormal flux, and full flux matrix

Weak conormal flux is defined by the actual energy-minus-forcing
functional on the actual Poisson lifts. The closed Dirichlet Green
identity proves flux(D f) = -P* f for every physical L² source.
Adding the same Poisson solution changes that flux by the same full
Dirichlet-to-Neumann matrix, including its off-diagonal entries.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory Filter ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace

theorem innerGapPoisson_single (p : Fin 2 → ℝ → ℝ) (i : Fin 2) :
    innerGapPoisson p (EuclideanSpace.single i (1 : ℝ)) = p i := by
  funext r
  simp [innerGapPoisson_apply, PiLp.single_apply]

theorem innerGapPoissonL2_single (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k)) (i : Fin 2) :
    innerGapPoissonL2 D hw ha hcore hpos p hp (EuclideanSpace.single i (1 : ℝ)) =
      innerRadialIntervalToLp D hw ha hcore hpos (p i) (hp i).continuous.continuousOn := by
  apply Lp.ext
  filter_upwards [innerGapPoissonL2_ae D hw ha hcore hpos p hp
      (EuclideanSpace.single i (1 : ℝ)),
    innerRadialIntervalToLp_ae D hw ha hcore hpos (p i) (hp i).continuous.continuousOn]
      with r hP hp
  rw [hP, hp, innerGapPoisson_single]

theorem innerGapPoissonL2_adjoint_apply (D : ReferenceData) (hw : Continuous D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Ioo a b, 0 ≤ D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (F : RadialModeL2 D) (i : Fin 2) :
    (innerGapPoissonL2 D hw ha hcore hpos p hp).adjoint F i =
      ⟪F, innerRadialIntervalToLp D hw ha hcore hpos (p i) (hp i).continuous.continuousOn⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (innerGapPoissonL2 D hw ha hcore hpos p hp) (EuclideanSpace.single i (1 : ℝ)) F
  rw [EuclideanSpace.inner_single_left, conj_trivial, one_mul,
    innerGapPoissonL2_single] at h
  exact h.trans (real_inner_comm _ _)

/-- The variational outgoing flux, evaluated on the actual unit-trace
Poisson lifts. It uses one complete energy witness q. -/
def innerGapWeakFlux (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (q : InnerGapEnergyTriple D) (F : RadialModeL2 D) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i =>
    ⟪q.snd, innerGapEnergyPair D hw ha hcore hpos j (p i) (hp i)⟫_ℝ -
      ⟪F, innerRadialIntervalToLp D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
        (p i) (hp i).continuous.continuousOn⟫_ℝ)

theorem innerGapWeakFlux_apply (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (q : InnerGapEnergyTriple D) (F : RadialModeL2 D) (i : Fin 2) :
    innerGapWeakFlux D hw ha hcore hpos j p hp q F i =
      ⟪q.snd, innerGapEnergyPair D hw ha hcore hpos j (p i) (hp i)⟫_ℝ -
        ⟪F, innerRadialIntervalToLp D hw.continuous ha hcore
          (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le)
          (p i) (hp i).continuous.continuousOn⟫_ℝ := by
  simp only [innerGapWeakFlux, PiLp.toLp_apply]

theorem innerGapFormSpace_poisson_orthogonal (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) (i : Fin 2) :
    ⟪q.snd, innerGapEnergyPair D hw ha hcore hpos j (p i) (hp i)⟫_ℝ = 0 := by
  have h := innerGapFormSpace_green_test D hw hab ha hcore hpos hslope j (p i) (hp i) q hq
  have hz : innerRadialIntervalToLp D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j (p i))
      (innerGapTestSource_continuousOn ha hw (hp i) hpos j) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [innerRadialIntervalToLp_ae D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) (innerGapTestSource D.w j (p i))
      (innerGapTestSource_continuousOn ha hw (hp i) hpos j)] with r hr
    rw [hr]
    by_cases hmem : r ∈ Ioo a b
    · simp only [indicator_of_mem hmem, innerGapTestSource,
        heq i r (Ioo_subset_Icc_self hmem), mul_zero, Pi.zero_apply]
    · simp only [indicator_of_notMem hmem, Pi.zero_apply]
  simpa only [hz, inner_zero_right] using h

theorem innerGapWeakFlux_dirichlet (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b) (F : RadialModeL2 D) :
    innerGapWeakFlux D hw ha hcore hpos j p hp q F =
      -(innerGapPoissonL2 D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp).adjoint F := by
  apply PiLp.ext
  intro i
  rw [innerGapWeakFlux_apply,
    innerGapFormSpace_poisson_orthogonal D hw hab ha hcore hpos hslope p hp heq q hq i,
    PiLp.neg_apply, innerGapPoissonL2_adjoint_apply, zero_sub]

/-- The actual Poisson energy pairing is the same full outgoing-flux
matrix. This proves the cross terms as well as the diagonal energy. -/
theorem innerGapPoissonEnergy_column_pairing (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    ⟪innerGapEnergyPair D hw ha hcore hpos j (innerGapPoisson p ξ)
        (innerGapPoisson_contDiff p hp ξ),
      innerGapEnergyPair D hw ha hcore hpos j (p i) (hp i)⟫_ℝ =
      innerGapFluxOperator D.w a b p ξ i := by
  have hP := innerGapPoisson_homogeneous hw p hp heq ξ
  have hz : (∫ r in a..b, p i r * radialJacobi (j ^ 2) D.w (innerGapPoisson p ξ) r) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
        dsimp only
        rw [hP r hr', mul_zero]
      _ = 0 := intervalIntegral.integral_zero
  have h0 : p i a = if i = 0 then 1 else 0 := by
    simpa only [innerGapEndpoint_zero] using hb 0 i
  have h1 : p i b = if i = 1 then 1 else 0 := by
    simpa only [innerGapEndpoint_one] using hb 1 i
  rw [real_inner_comm, innerGapEnergyPair_inner D hw hab ha hcore hpos hslope,
    innerGapEnergyBilinear_boundary hab ha hw (hp i) (innerGapPoisson_contDiff p hp ξ),
    hz, sub_zero, h0, h1, innerGapFluxOperator_apply D.w a b p hp ξ i]
  fin_cases i <;> norm_num [Statements.bufferSign, innerGapEndpoint] <;> ring

/-- Add the same actual Poisson field and its two energy coordinates to
one Dirichlet witness. -/
def innerGapAffineEnergy (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (q : InnerGapEnergyTriple D) (ξ : EuclideanSpace ℝ (Fin 2)) : InnerGapEnergyTriple D :=
  WithLp.toLp 2
    (q.fst + innerGapPoissonL2 D hw.continuous ha hcore
      (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp ξ,
    q.snd + innerGapEnergyPair D hw ha hcore hpos j (innerGapPoisson p ξ)
      (innerGapPoisson_contDiff p hp ξ))

theorem innerGapAffineEnergy_function (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b : ℝ} (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r) (j : ℝ)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (q : InnerGapEnergyTriple D) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ).fst =
      q.fst + innerGapPoissonL2 D hw.continuous ha hcore
        (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp ξ := by
  simp only [innerGapAffineEnergy, WithLp.toLp_fst]

/-- One and the same Dirichlet solution, Poisson operator, and full flux
matrix satisfy the physical Schur gluing identity for every L² source. -/
theorem innerGapWeakFlux_affine (D : ReferenceData) (hw : ContDiff ℝ ∞ D.w)
    {a b j : ℝ} (hab : a ≤ b) (ha : 0 < a) (hcore : Ioo a b ⊆ radialCore D)
    (hpos : ∀ r ∈ Icc a b, 0 < D.w r)
    (hslope : ∀ r ∈ Icc a b, 0 ≤ r * deriv D.w r / D.w r)
    (p : Fin 2 → ℝ → ℝ) (hp : ∀ k, ContDiff ℝ ∞ (p k))
    (hb : ∀ i k, p k (innerGapEndpoint a b i) = if k = i then 1 else 0)
    (heq : ∀ i r, r ∈ Icc a b → radialJacobi (j ^ 2) D.w (p i) r = 0)
    (q : InnerGapEnergyTriple D) (hq : q ∈ innerGapFormSpace D j a b)
    (F : RadialModeL2 D) (ξ : EuclideanSpace ℝ (Fin 2)) :
    innerGapWeakFlux D hw ha hcore hpos j p hp
      (innerGapAffineEnergy D hw ha hcore hpos j p hp q ξ) F =
      innerGapFluxOperator D.w a b p ξ -
        (innerGapPoissonL2 D hw.continuous ha hcore
          (fun r hr => (hpos r (Ioo_subset_Icc_self hr)).le) p hp).adjoint F := by
  apply PiLp.ext
  intro i
  simp only [innerGapWeakFlux_apply, innerGapAffineEnergy, WithLp.toLp_snd,
    inner_add_left, PiLp.sub_apply]
  rw [innerGapFormSpace_poisson_orthogonal D hw hab ha hcore hpos hslope p hp heq q hq i,
    innerGapPoissonEnergy_column_pairing D hw hab ha hcore hpos hslope p hp hb heq,
    innerGapPoissonL2_adjoint_apply, zero_add]

end ContinuousFlexibility.Radial
