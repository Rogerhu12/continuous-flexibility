module

public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.TameTransfer
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The continuous normalization row for the nonlinear solve

The affine normalization in the manuscript is a genuine closed hyperplane.
The continuity proof uses point evaluations on a compact rectangle and the
uniform boundedness principle on the physical Fréchet space. This avoids
introducing a second realization of the weighted Sobolev spaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped Topology ContDiff BigOperators NNReal

set_option backward.isDefEq.respectTransparency false

private theorem continuous_cosineMode (j : ℕ) : Continuous (Radial.cosineMode j) := by
  unfold Radial.cosineMode
  fun_prop

theorem continuous_referenceMode {u : PolarPoint → ℝ} (hu : Continuous u) (j : ℕ) :
    Continuous (referenceMode u j) := by
  have hf : Continuous (fun p : ℝ × ℝ => u p * Radial.cosineMode j p.2) :=
    hu.mul ((continuous_cosineMode j).comp continuous_snd)
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun r θ => u (r, θ) * Radial.cosineMode j θ)
      hf 0 (2 * Real.pi))

theorem referenceMode_add_of_continuous {u v : PolarPoint → ℝ}
    (hu : Continuous u) (hv : Continuous v) (j : ℕ) (r : ℝ) :
    referenceMode (fun p => u p + v p) j r =
      referenceMode u j r + referenceMode v j r := by
  have huc : Continuous (fun θ : ℝ => u (r, θ) * Radial.cosineMode j θ) :=
    (hu.comp ((continuous_const (y := r)).prodMk continuous_id)).mul (continuous_cosineMode j)
  have hvc : Continuous (fun θ : ℝ => v (r, θ) * Radial.cosineMode j θ) :=
    (hv.comp ((continuous_const (y := r)).prodMk continuous_id)).mul (continuous_cosineMode j)
  have hui := huc.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hvi := hvc.intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  simp only [referenceMode, radialAngularMean, add_mul]
  rw [intervalIntegral.integral_add hui hvi, mul_add]

theorem referenceMode_smul (c : ℝ) (u : PolarPoint → ℝ) (j : ℕ) (r : ℝ) :
    referenceMode (fun p => c * u p) j r = c * referenceMode u j r := by
  simp only [referenceMode, radialAngularMean, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem continuousOn_referenceColumn {D : ReferenceData} (hD : IsRadialReference D) :
    ContinuousOn (referenceColumn D) (Icc D.a D.b) := by
  obtain ⟨_, hacc⟩ := hD.1
  have hgeo := hacc.1
  have hw : ContDiff ℝ ∞ D.w := hgeo.2.2.1.1
  have hphi : ContDiff ℝ ∞ D.phi := hgeo.2.2.2.1.1
  have hchi : ContDiff ℝ ∞ D.chi := hD.2.2.2.1.1
  have hprod : ContDiff ℝ ∞ (fun r => D.w r * D.chi r) := hw.mul hchi
  have hphid : ContDiff ℝ ∞ (deriv D.phi) := (contDiff_infty_iff_deriv.mp hphi).2
  have hterm : Continuous (deriv (fun r => (D.w r * D.chi r) * deriv D.phi r)) :=
    (hprod.mul hphid).continuous_deriv (by simp)
  have hprodd : Continuous (deriv (fun r => D.w r * D.chi r)) :=
    hprod.continuous_deriv (by simp)
  exact hterm.continuousOn.sub
    (((continuous_const.mul hprodd).continuousOn.div continuousOn_id
      (fun r hr => (hgeo.1.trans_le hr.1).ne')).mul hphi.continuous.continuousOn)

theorem referenceRow_add_of_continuous {D : ReferenceData} (hab : D.a ≤ D.b)
    (hcol : ContinuousOn (referenceColumn D) (Icc D.a D.b))
    {u v : PolarPoint → ℝ} (hu : Continuous u) (hv : Continuous v) :
    referenceRow D (fun p => u p + v p) = referenceRow D u + referenceRow D v := by
  have hui : IntervalIntegrable
      (fun r => referenceColumn D r * referenceMode u 2 r) volume D.a D.b :=
    (hcol.mul (continuous_referenceMode hu 2).continuousOn).intervalIntegrable_of_Icc hab
  have hvi : IntervalIntegrable
      (fun r => referenceColumn D r * referenceMode v 2 r) volume D.a D.b :=
    (hcol.mul (continuous_referenceMode hv 2).continuousOn).intervalIntegrable_of_Icc hab
  unfold referenceRow
  simp_rw [referenceMode_add_of_continuous hu hv, mul_add]
  exact intervalIntegral.integral_add hui hvi

theorem referenceRow_smul (D : ReferenceData) (c : ℝ) (u : PolarPoint → ℝ) :
    referenceRow D (fun p => c * u p) = c * referenceRow D u := by
  unfold referenceRow
  simp_rw [referenceMode_smul]
  rw [show (fun r => referenceColumn D r * (c * referenceMode u 2 r)) =
      (fun r => c * (referenceColumn D r * referenceMode u 2 r)) by funext r; ring]
  exact intervalIntegral.integral_const_mul c _

/-- A compact family of continuous scalar evaluations on a barrelled space is
bounded by one continuous seminorm. -/
theorem exists_continuous_seminorm_bound_of_compact
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [BarrelledSpace ℝ E] (L : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hL : Continuous L) (hfield : ∀ x, Continuous (L x))
    {K : Set PolarPoint} (hK : IsCompact K) :
    ∃ p : Seminorm ℝ E, Continuous p ∧ ∀ x z, z ∈ K → |L x z| ≤ p x := by
  classical
  let ps : K → Seminorm ℝ E := fun z =>
    (normSeminorm ℝ ℝ).comp ((LinearMap.proj z.val).comp L)
  have hps : ∀ z, Continuous (ps z) := by
    intro z
    exact ((continuous_apply z.val).comp hL).norm
  have hb : BddAbove (range ps) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    obtain ⟨B, hB⟩ := hK.bddAbove_image (hfield x).norm.continuousOn
    refine ⟨B, ?_⟩
    rintro y ⟨z, rfl⟩
    exact hB (mem_image_of_mem (fun z => ‖L x z‖) z.property)
  have hp : Continuous ((⨆ z, ps z : Seminorm ℝ E) : E → ℝ) := by
    rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup ps hps hb
  refine ⟨⨆ z, ps z, hp, ?_⟩
  intro x z hz
  exact le_ciSup hb (⟨z, hz⟩ : K) x

private theorem referenceRow_bound_of_field_bound {D : ReferenceData}
    (hab : D.a ≤ D.b) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hcol : ∀ r ∈ Icc D.a D.b, |referenceColumn D r| ≤ B)
    (u : PolarPoint → ℝ)
    (hu : ∀ r ∈ Icc D.a D.b, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), |u (r, θ)| ≤ M) :
    |referenceRow D u| ≤
      (B * (|(2 * Real.pi)⁻¹| * (Real.sqrt 2 * |2 * Real.pi - 0|)) * |D.b - D.a|) * M := by
  have hmode (r : ℝ) (hr : r ∈ Icc D.a D.b) :
      |referenceMode u 2 r| ≤
        (|(2 * Real.pi)⁻¹| * (Real.sqrt 2 * |2 * Real.pi - 0|)) * M := by
    unfold referenceMode radialAngularMean
    rw [abs_mul]
    have hi : ‖∫ θ in (0 : ℝ)..2 * Real.pi, u (r, θ) * Radial.cosineMode 2 θ‖ ≤
        (M * Real.sqrt 2) * |2 * Real.pi - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro θ hθ
      have hθ'' : θ ∈ Ioc (0 : ℝ) (2 * Real.pi) := by
        simpa only [uIoc_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)] using hθ
      have hθ' : θ ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hθ''.1.le, hθ''.2⟩
      have hc : |Radial.cosineMode 2 θ| ≤ Real.sqrt 2 := by
        rw [Radial.cosineMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one ((2 : ℕ) * θ)) (Real.sqrt_nonneg 2)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hu r hr θ hθ') hc (abs_nonneg _) hM
    rw [Real.norm_eq_abs] at hi
    calc
      _ ≤ |(2 * Real.pi)⁻¹| * ((M * Real.sqrt 2) * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      _ = _ := by ring
  have hi : ‖∫ r in D.a..D.b, referenceColumn D r * referenceMode u 2 r‖ ≤
      (B * ((|(2 * Real.pi)⁻¹| * (Real.sqrt 2 * |2 * Real.pi - 0|)) * M)) * |D.b - D.a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    have hr'' : r ∈ Ioc D.a D.b := by simpa only [uIoc_of_le hab] using hr
    have hr' : r ∈ Icc D.a D.b := ⟨hr''.1.le, hr''.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hcol r hr') (hmode r hr') (abs_nonneg _) hB
  change |∫ r in D.a..D.b, referenceColumn D r * referenceMode u 2 r| ≤ _
  rw [Real.norm_eq_abs] at hi
  exact hi.trans_eq (by ring)

section RowLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (D : ReferenceData) (hab : D.a ≤ D.b)
  (hcol : ContinuousOn (referenceColumn D) (Icc D.a D.b))
  (L : E →ₗ[ℝ] (PolarPoint → ℝ)) (hfield : ∀ x, Continuous (L x))

/-- The actual integral row, bundled as a linear functional. -/
def referenceRowLinear : E →ₗ[ℝ] ℝ where
  toFun x := referenceRow D (L x)
  map_add' x y := by
    rw [map_add]
    exact referenceRow_add_of_continuous hab hcol (hfield x) (hfield y)
  map_smul' c x := by
    rw [map_smul]
    exact referenceRow_smul D c (L x)

theorem referenceRowLinear_apply (x : E) :
    referenceRowLinear D hab hcol L hfield x = referenceRow D (L x) := rfl

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [BarrelledSpace ℝ E]

theorem continuous_referenceRowLinear (hL : Continuous L) :
    Continuous (referenceRowLinear D hab hcol L hfield) := by
  let K : Set PolarPoint := Icc D.a D.b ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  obtain ⟨p, hp, hpx⟩ := exists_continuous_seminorm_bound_of_compact L hL hfield
    (K := K) (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.bddAbove_image hcol.norm
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hcb : ∀ r ∈ Icc D.a D.b, |referenceColumn D r| ≤ B := by
    intro r hr
    exact (hB₀ (mem_image_of_mem (fun r => ‖referenceColumn D r‖) hr)).trans (le_max_left _ _)
  let c : ℝ := B * (|(2 * Real.pi)⁻¹| * (Real.sqrt 2 * |2 * Real.pi - 0|)) * |D.b - D.a|
  have hc : 0 ≤ c := by positivity
  let cNN : NNReal := NNReal.mk c hc
  let q : Seminorm ℝ E := (normSeminorm ℝ ℝ).comp (referenceRowLinear D hab hcol L hfield)
  have hq : q ≤ cNN • p := by
    intro x
    simp only [smul_apply, NNReal.smul_def, smul_eq_mul, cNN, NNReal.coe_mk]
    exact referenceRow_bound_of_field_bound hab hB (apply_nonneg _ _) hcb (L x)
      (fun r hr θ hθ => hpx x (r, θ) ⟨hr, hθ⟩)
  have hcont : Continuous q := Seminorm.continuous_of_le (hp.const_smul cNN) hq
  exact (WithSeminorms.continuous_iff_continuous_comp (norm_withSeminorms ℝ ℝ)
    (referenceRowLinear D hab hcol L hfield)).2 (fun _ => hcont)

/-- Continuity is obtained without changing the physical realization. -/
def referenceRowCLM (hL : Continuous L) : E →L[ℝ] ℝ where
  toLinearMap := referenceRowLinear D hab hcol L hfield
  cont := continuous_referenceRowLinear D hab hcol L hfield hL

theorem referenceRowCLM_apply (hL : Continuous L) (x : E) :
    referenceRowCLM D hab hcol L hfield hL x = referenceRow D (L x) := rfl

attribute [irreducible] referenceRowCLM

end RowLinear

/-- The decoded height including the free left endpoint constant. -/
def heightPairFieldLinear (S : PhysicalSpacesData) : HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun := heightPairField S
  map_add' x y := by
    funext p
    simp only [heightPairField, Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply]
    ring
  map_smul' c x := by
    funext p
    simp only [heightPairField, Prod.smul_fst, Prod.smul_snd, map_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem heightPairFieldLinear_apply (S : PhysicalSpacesData) (x : HeightPair S) :
    heightPairFieldLinear S x = heightPairField S x := rfl

theorem continuous_heightPairFieldLinear {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hS : IsPhysicalSpaces D T S) :
    Continuous (heightPairFieldLinear S) := by
  apply continuous_pi
  intro p
  exact (((continuous_apply p).comp (hS.1 (3 / 4 : ℝ)).2.2.1).comp continuous_fst).add
    (continuous_snd.mul continuous_const)

/-- The true integral normalization is a continuous linear functional on the
extended physical height space. -/
def heightReferenceRowCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) : HeightPair S →L[ℝ] ℝ := by
  letI : ∀ n, CompleteSpace ((S.height (3 / 4 : ℝ)).level n) := fun n =>
    ((hS.1 (3 / 4 : ℝ)).2.1 n).isComplete.completeSpace_coe
  have hab : D.a ≤ D.b := by
    obtain ⟨_, hacc⟩ := hD.1
    exact hacc.1.2.1.le
  exact referenceRowCLM D hab (continuousOn_referenceColumn hD)
    (heightPairFieldLinear S)
    (fun x => (physical_height_with_cutoff_contDiff hT hS
      (by norm_num : (0 : ℝ) < 3 / 4) x.1 x.2).continuous)
    (continuous_heightPairFieldLinear hS)

theorem heightReferenceRowCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : HeightPair S) :
    heightReferenceRowCLM hD hT hS x = referenceRow D (heightPairField S x) := by
  simp only [heightReferenceRowCLM, referenceRowCLM_apply, heightPairFieldLinear_apply]

attribute [irreducible] heightReferenceRowCLM

/-- The normalization row on the full state. -/
def stateReferenceRowCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) : AnnularState S →L[ℝ] ℝ :=
  (heightReferenceRowCLM hD hT hS).comp
    (ContinuousLinearMap.fst ℝ (HeightPair S) (ℝ × (CircleSpace S × CircleSpace S)))

theorem stateReferenceRowCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    stateReferenceRowCLM hD hT hS x = referenceRow D (stateU S x) := by
  simp only [stateReferenceRowCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', heightReferenceRowCLM_apply, stateU]

attribute [irreducible] stateReferenceRowCLM

/-- The normalization row on constant-control, odd-chart directions. -/
def sectorReferenceRowCLM {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) : StateDirections S →L[ℝ] ℝ :=
  (stateReferenceRowCLM hD hT hS).comp (stateSectorSubmodule S).subtypeL

theorem sectorReferenceRowCLM_apply {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hD : IsRadialReference D)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S) (x : StateDirections S) :
    sectorReferenceRowCLM hD hT hS x = referenceRow D (stateU S x.val) := by
  simp only [sectorReferenceRowCLM, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, stateReferenceRowCLM_apply]

attribute [irreducible] sectorReferenceRowCLM

/-- On a monotone defining grading, a continuous scalar functional has a
bound at one finite order. -/
theorem exists_grade_bound_clm
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : WithSeminorms p) (hmono : Monotone p)
    (L : E →L[ℝ] ℝ) :
    ∃ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |L x| ≤ C * p b x := by
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous hp
    ((normSeminorm ℝ ℝ).comp L.toLinearMap) L.continuous.norm
  refine ⟨s.sup id, C, C.coe_nonneg, fun x => ?_⟩
  have hs : s.sup p ≤ p (s.sup id) := by
    apply Finset.sup_le
    intro i hi
    exact hmono (Finset.le_sup (f := id) hi)
  exact (hC x).trans (mul_le_mul_of_nonneg_left (hs x) C.coe_nonneg)

/-- A continuous scalar row defines a smoothing-compatible hyperplane on
a space with a monotone defining grading. -/
theorem hasSmoothing_ker_of_continuous
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (p : ℕ → Seminorm ℝ E) (hp : WithSeminorms p) (hmono : Monotone p)
    (hsmooth : HasSmoothing p) (row : E →L[ℝ] ℝ) (ψ : E) (hψ : row ψ = 1) :
    HasSmoothing (fun n => (p n).comp row.toLinearMap.ker.subtype) := by
  obtain ⟨b, C, hC, hb⟩ := exists_grade_bound_clm p hp hmono row
  exact hasSmoothing_ker_rankOne row ψ hψ
    (fun _ _ h x => hmono h x) hC hb hsmooth

theorem referenceRow_affine_of_zero
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C) (x : AnnularState S)
    (hx : referenceRow D (stateU S x) = 0) :
    referenceRow D (stateU S (C.referenceState + x)) = 1 := by
  calc
    _ = stateReferenceRowCLM hD hT hS (C.referenceState + x) :=
      (stateReferenceRowCLM_apply hD hT hS _).symm
    _ = stateReferenceRowCLM hD hT hS C.referenceState + stateReferenceRowCLM hD hT hS x :=
      map_add (stateReferenceRowCLM hD hT hS) C.referenceState x
    _ = referenceRow D (stateU S C.referenceState) + referenceRow D (stateU S x) :=
      congrArg₂ (· + ·) (stateReferenceRowCLM_apply hD hT hS C.referenceState)
        (stateReferenceRowCLM_apply hD hT hS x)
    _ = 1 := by rw [href.2.2.2.2.2, hx, add_zero]

theorem referenceRow_affine_of_mem_kernel
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (href : referenceStateConditions D S C)
    (x : StateDirections S) (hx : sectorReferenceRowCLM hD hT hS x = 0) :
    referenceRow D (stateU S (C.referenceState + x.val)) = 1 :=
  referenceRow_affine_of_zero hD hT hS href x.val
    ((sectorReferenceRowCLM_apply hD hT hS x).symm.trans hx)

end ContinuousFlexibility.Statements
