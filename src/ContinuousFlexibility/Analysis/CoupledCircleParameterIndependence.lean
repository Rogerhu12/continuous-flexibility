import ContinuousFlexibility.Analysis.CoupledScalarHeightDerivative
import ContinuousFlexibility.Analysis.NeighborhoodCharacteristicSpeedExtension
import ContinuousFlexibility.Analysis.NeighborhoodCircleFlowBasic

/-!
# Parameter independence of the actual circle residual

The border cutoff is supported where the reference profile is increasing.
Changing its scalar coefficient therefore leaves the characteristic speed
unchanged on every negative component.  Uniqueness of the actual ordinary
flow, followed by its two inverse identities, proves independence of the
given return residual.  At zero independent parameter the same comparison
also removes the height coordinate.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {P : ResidualData S} {base loss : ℕ} {ε : ℝ}

/-- Only the first spatial jets of the height, and their germs, enter the
three corrected coefficients. The primitive's additive constant is irrelevant. -/
theorem coupled_polarCoefficients_eq_of_germs
    {w v : ℝ → ℝ} {h k : PolarPoint → ℝ} {p : PolarPoint}
    (hw : w =ᶠ[𝓝 p.1] v)
    (hk : heightRadial h =ᶠ[𝓝 p] heightRadial k)
    (hp : heightAngular h =ᶠ[𝓝 p] heightAngular k) :
    polarLinearA w h p = polarLinearA v k p ∧
      polarLinearB w h p = polarLinearB v k p ∧
      polarCorrectedC w h p = polarCorrectedC v k p := by
  have hE : profileEnergy w =ᶠ[𝓝 p] profileEnergy v := by
    have hwp := hw.comp_tendsto (continuous_fst.continuousAt : ContinuousAt Prod.fst p)
    filter_upwards [hwp] with x hx
    simp only [Function.comp_apply] at hx
    change radialEnergy (w x.1) = radialEnergy (v x.1)
    rw [hx]
  have hEr : radialPartial (profileEnergy w) p = radialPartial (profileEnergy v) p := by
    rw [radialPartial, radialPartial, hE.fderiv_eq (𝕜 := ℝ)]
  have hkr : radialPartial (heightRadial h) p = radialPartial (heightRadial k) p := by
    rw [radialPartial, radialPartial, hk.fderiv_eq (𝕜 := ℝ)]
  have hpr : radialPartial (heightAngular h) p = radialPartial (heightAngular k) p := by
    rw [radialPartial, radialPartial, hp.fderiv_eq (𝕜 := ℝ)]
  have hpt : angularPartial (heightAngular h) p = angularPartial (heightAngular k) p := by
    rw [angularPartial, angularPartial, hp.fderiv_eq (𝕜 := ℝ)]
  simp only [polarLinearA, polarLinearB, polarCorrectedC, polarScale, polarDiscriminant,
    hE.eq_of_nhds, hk.eq_of_nhds, hp.eq_of_nhds, hEr, hkr, hpr, hpt, and_self]

theorem coupled_minusSpeed_eq_of_profile_germ
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q r : ℝ}
    (hw : stateProfile D S C x =ᶠ[𝓝 r] stateProfile D S C y)
    (hu : q = 0 ∨ x.1 = y.1) (θ : ℝ) :
    minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, θ) =
      minusCharacteristicSpeed (originalCoefficients D S C (y, q)) (r, θ) := by
  have hx := contDiff_stateProfile_of_n01 hS hT h1 x
  have hy := contDiff_stateProfile_of_n01 hS hT h1 y
  have hscaled (p : PolarPoint) :
      q * radialPartial (stateU S x) p = q * radialPartial (stateU S y) p ∧
      q * heightAngular (stateU S x) p = q * heightAngular (stateU S y) p := by
    rcases hu with hq | hxy
    · simp only [hq, zero_mul, and_self]
    · have he : stateU S x = stateU S y := congrArg (heightPairField S) hxy
      simp only [he, and_self]
  have hk : heightRadial (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightRadial (stateHeight D S C (y, q)) := by
    have hwp := hw.comp_tendsto
      (continuous_fst.continuousAt : ContinuousAt Prod.fst (r, θ))
    filter_upwards [hwp] with p hp
    simp only [Function.comp_apply] at hp
    rw [stateHeight_heightRadial_of_contDiff_profile hT hS (z := (x, q)) hx,
      stateHeight_heightRadial_of_contDiff_profile hT hS (z := (y, q)) hy, hp, (hscaled p).1]
  have hp : heightAngular (stateHeight D S C (x, q)) =ᶠ[𝓝 (r, θ)]
      heightAngular (stateHeight D S C (y, q)) := by
    filter_upwards [] with p
    rw [stateHeight_heightAngular_of_contDiff_profile hT hS (z := (x, q)) hx,
      stateHeight_heightAngular_of_contDiff_profile hT hS (z := (y, q)) hy, (hscaled p).2]
  obtain ⟨ha, hb, hc⟩ := coupled_polarCoefficients_eq_of_germs hw hk hp
  simp only [minusCharacteristicSpeed, originalCoefficients, ha, hb, hc]

/-- The actual ordinary flow is unique even though its time equation is
required only on the open component. -/
theorem coupled_minusFlow_eq_of_speed_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε) (hsx : stateSector S x)
    (hspeed : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, θ) =
        minusCharacteristicSpeed (originalCoefficients D S C (y, q)) (r, θ))
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, q) m r θ = C.minusFlow (y, q) m r θ := by
  have hw := contDiff_stateProfile_of_n01 hS hT h1 x
  have hD : IsAccumulatingProfile D := h1.1.1
  obtain ⟨_, _, _, hcontrol, _, _, hflow, _, _, hadm, _⟩ := h1
  have hpositive (p : PolarPoint) (hp : p ∈ annularOpen D) :
      0 < polarDiscriminant (stateProfile D S C x) (stateHeight D S C (x, q)) p ∧
      heightQ (profileEnergy (stateProfile D S C x) p)
        (heightRadial (stateHeight D S C (x, q)) p)
        (angularPartial (heightAngular (stateHeight D S C (x, q))) p) ≠ 0 := by
    have hb := hadm (x, q) hx hsx p hp
    have hwp : 0 < stateProfile D S C x p.1 :=
      mul_pos (hD.choose_spec.1.2.2.2.2.1 p.1 hp.1) (Real.exp_pos _)
    exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb.2.2.2.2.1,
      ((div_pos_iff_of_pos_right hwp).mp
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hb.2.2.1)).ne'⟩
  obtain ⟨G, dG, _, hdG, hderiv, _, hG⟩ :=
    exists_stateCharacteristicSpeed_extension hD hT hS hcontrol (z := (x, q)) hw hpositive m
  have hfx := hflow (x, q) hx m θ
  have hfy := hflow (y, q) hy m θ
  have hu := hfx.2.1.mono (Icc_subset_Icc le_rfl hr.2)
  have hv := hfy.2.1.mono (Icc_subset_Icc le_rfl hr.2)
  have hdu (t : ℝ) (ht : t ∈ Ioo (C.left m) r) :
      HasDerivAt (fun t => C.minusFlow (x, q) m t θ)
        (G (t, C.minusFlow (x, q) m t θ)) t := by
    have ht' : t ∈ Ioo (C.left m) (C.right m) := ⟨ht.1, ht.2.trans_le hr.2⟩
    exact (hfx.2.2.1 t ht').congr_deriv
      (hG t (Ioo_subset_Icc_self ht') _).symm
  have hdv (t : ℝ) (ht : t ∈ Ioo (C.left m) r) :
      HasDerivAt (fun t => C.minusFlow (y, q) m t θ)
        (G (t, C.minusFlow (y, q) m t θ)) t := by
    have ht' : t ∈ Ioo (C.left m) (C.right m) := ⟨ht.1, ht.2.trans_le hr.2⟩
    exact (hfy.2.2.1 t ht').congr_deriv
      ((hspeed t ht' _).symm.trans (hG t (Ioo_subset_Icc_self ht') _).symm)
  have he := continuousAngleTrajectory_difference_eq_mul_exp hr.1 hdG hderiv hu hv hdu hdv
  rw [hfx.1, hfy.1, sub_self, zero_mul] at he
  exact sub_eq_zero.mp he

/-- Equal component speeds and equal left charts identify both actual
inverse maps, and hence the given residual in its original circle space. -/
theorem coupled_returnResidual_eq_of_speed_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q : ℝ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hspeed : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → ∀ θ,
      minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, θ) =
        minusCharacteristicSpeed (originalCoefficients D S C (y, q)) (r, θ))
    (hchart : ∀ m, stateLeftChart S x m = stateLeftChart S y m) :
    R.residual (x, q) = R.residual (y, q) := by
  apply (hS.2.1 (3 / 4 : ℝ)).2.2.2.2.2.1
  funext m θ
  have hf (η : ℝ) : C.minusFlow (x, q) m (C.right m) η =
      C.minusFlow (y, q) m (C.right m) η :=
    coupled_minusFlow_eq_of_speed_eq hT hS h1 hx hy hsx (hspeed m) η
      ⟨(h1.2.2.2.1.1 m).2.1.le, le_rfl⟩
  have hi (η : ℝ) : C.minusReturnInverse (x, q) m η =
      C.minusReturnInverse (y, q) m η := by
    have hyi := (h2.1 (y, q) hy hsy m (C.minusReturnInverse (x, q) m η)).2.1
    rw [← hf, (h2.1 (x, q) hx hsx m η).1] at hyi
    exact hyi.symm
  have hc : rightChartCandidate S C (x, q) m = rightChartCandidate S C (y, q) m := by
    funext η
    simp only [rightChartCandidate, oddPart, hi, hchart]
  have hri (η : ℝ) : C.rightChartInverse (x, q) m η =
      C.rightChartInverse (y, q) m η := by
    have hyi := (h2.1 (y, q) hy hsy m (C.rightChartInverse (x, q) m η)).2.2.2.1
    rw [← hc, (h2.1 (x, q) hx hsx m η).2.2.1] at hyi
    exact hyi.symm
  rw [h2.2.1 (x, q) hx hsx, h2.2.1 (y, q) hy hsy]
  simp only [returnResidualField, evenPart, hi, hchart, hri]

theorem coupled_stateProfile_germ_of_nu_change
    (hborder : RadialTrueBorder D) (hcontrol : controlGeometryConditions D S C)
    {x y : AnnularState S} (htail : x.2.2 = y.2.2) {m : ℕ} {r : ℝ}
    (hr : r ∈ Ioo (C.left m) (C.right m)) :
    stateProfile D S C x =ᶠ[𝓝 r] stateProfile D S C y := by
  obtain ⟨_, _, _, hnegative, _⟩ := hcontrol
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  have hchi : D.chi t = 0 := by
    by_contra hn
    have hp := (hborder.support_subset hn).2
    exact (not_lt_of_ge hp.le) (hnegative m t ht)
  simp only [stateProfile, stateKappa, htail, hchi, mul_zero, zero_add]

/-- The full return residual is unchanged by changing only nu. -/
theorem coupled_returnResidual_eq_of_nu_change
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q : ℝ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hheight : x.1 = y.1) (htail : x.2.2 = y.2.2) :
    R.residual (x, q) = R.residual (y, q) := by
  apply coupled_returnResidual_eq_of_speed_eq hT hS h1 h2 hx hy hsx hsy
  · intro m r hr θ
    exact coupled_minusSpeed_eq_of_profile_germ hT hS h1
      (coupled_stateProfile_germ_of_nu_change h1.1.2.2.2.1 h1.2.2.2.1 htail hr)
      (Or.inr hheight) θ
  · intro m
    exact congrArg
      (fun u : CircleSpace S => fun θ => θ + (S.circle (3 / 4 : ℝ)).decode u m θ)
      (congrArg Prod.snd htail)

/-- At zero independent parameter the full return residual is independent
of the height, with the control and chart coordinates fixed. -/
theorem coupled_returnResidual_zero_parameter_eq_of_tail
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {x y : AnnularState S}
    (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hy : (y, 0) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y) (htail : x.2 = y.2) :
    R.residual (x, 0) = R.residual (y, 0) := by
  have hp : stateProfile D S C x = stateProfile D S C y := by
    funext r
    simp only [stateProfile, stateKappa, htail]
  apply coupled_returnResidual_eq_of_speed_eq hT hS h1 h2 hx hy hsx hsy
  · intro m r hr θ
    exact coupled_minusSpeed_eq_of_profile_germ hT hS h1
      (Filter.Eventually.of_forall fun r => congrFun hp r) (Or.inl rfl) θ
  · intro m
    exact congrArg
      (fun u : CircleSpace S => fun θ => θ + (S.circle (3 / 4 : ℝ)).decode u m θ)
      (congrArg (fun p : ℝ × (CircleSpace S × CircleSpace S) => p.2.2) htail)

private theorem coupled_returnResidual_eq_of_nu_change_parameters
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {x y : AnnularState S × ℝ}
    (hx : x ∈ stateNeighborhood S C base ε)
    (hy : y ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x.1) (hsy : stateSector S y.1)
    (hq : x.2 = y.2) (hheight : x.1.1 = y.1.1)
    (htail : x.1.2.2 = y.1.2.2) : R.residual x = R.residual y := by
  rcases x with ⟨x, q⟩
  rcases y with ⟨y, r⟩
  change q = r at hq
  subst r
  exact coupled_returnResidual_eq_of_nu_change hT hS h1 h2 hx hy hsx hsy hheight htail

/-- The scalar border direction belongs to the same state sector. -/
def coupledSectorNuDirection (S : PhysicalSpacesData) (μ : ℝ) : StateDirections S := by
  refine ⟨(0, (μ, (0, 0))), ?_⟩
  change stateSector S (0, (μ, (0, 0)))
  constructor
  · intro m θ φ
    simp only [map_zero, Pi.zero_apply]
  · intro m θ
    simp only [map_zero, Pi.zero_apply, neg_zero]

theorem coupledSectorNuDirection_val (S : PhysicalSpacesData) (μ : ℝ) :
    (coupledSectorNuDirection S μ).val = (0, (μ, (0, 0))) := rfl

private theorem coupled_sector_nu_line_coordinates
    (z : StateDirections S × ℝ) (μ t : ℝ) :
    (liftSectorParameter S C
      (z + coupledScalarAction (E := StateDirections S × ℝ) t
        (coupledSectorNuDirection S μ, 0))).1.1 = (liftSectorParameter S C z).1.1 ∧
    (liftSectorParameter S C
      (z + coupledScalarAction (E := StateDirections S × ℝ) t
        (coupledSectorNuDirection S μ, 0))).1.2.2 = (liftSectorParameter S C z).1.2.2 ∧
    (liftSectorParameter S C
      (z + coupledScalarAction (E := StateDirections S × ℝ) t
        (coupledSectorNuDirection S μ, 0))).2 = (liftSectorParameter S C z).2 := by
  have hzero : coupledScalarAction t ((0 : CircleSpace S), (0 : CircleSpace S)) =
      (0 : CircleSpace S × CircleSpace S) := coupledScalarAction_zero t
  simp only [coupled_liftSectorParameter_add, coupledSectorNuDirection_val,
    Prod.fst_add, Prod.snd_add,
    coupledScalarAction_fst, coupledScalarAction_snd, coupledScalarAction_zero,
    hzero, coupled_liftSectorParameter_snd, add_zero, and_self]

private theorem coupled_returnResidual_sector_nu_line
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε)
    (μ t : ℝ)
    (ht : z + coupledScalarAction (E := StateDirections S × ℝ) t
      (coupledSectorNuDirection S μ, 0) ∈ sectorNeighborhood S base ε ε) :
    R.residual (liftSectorParameter S C
      (z + coupledScalarAction (E := StateDirections S × ℝ) t
        (coupledSectorNuDirection S μ, 0))) = R.residual (liftSectorParameter S C z) := by
  have href : referenceStateConditions D S C := h1.2.2.1
  have hc := coupled_sector_nu_line_coordinates (C := C) z μ t
  exact coupled_returnResidual_eq_of_nu_change_parameters hT hS h1 h2
    (liftSectorParameter_mem_stateNeighborhood ht le_rfl)
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (href.liftSectorParameter_sector _) (href.liftSectorParameter_sector _)
    hc.2.2 hc.1 hc.2.1

theorem coupled_sector_circle_first_derivative
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S × ℝ) :
    HasProjectiveLineDerivAt (fun y => (sectorJointResidual S C P y).2)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 v).2 z v :=
  (coupled_smoothDirections_first_derivative J hz v).clm_comp
    (ContinuousLinearMap.snd ℝ (S.Source) (EvenCircle S))

/-- The circle projection of the actual joint first jet is also the
ambient state derivative along that sector direction. -/
theorem coupled_circle_first_derivative
    {U : Set (StateDirections S × ℝ)}
    (J : SmoothDirections U (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S) :
    HasProjectiveLineDerivAt (fun x => (P.circle (x, z.2)).val)
      (projectiveJetHeadLinear J.D 0 z Fin.elim0 (v, 0)).2.val
      (liftSectorParameter S C z).1 v.val := by
  have hd := (coupled_sector_circle_first_derivative J hz (v, 0)).clm_comp
    (evenCircleSubmodule S).subtypeL
  simpa only [Submodule.subtypeL_apply, HasProjectiveLineDerivAt,
    sectorJointResidual, jointResidual, liftSectorParameter,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Submodule.coe_add, Submodule.coe_smul, smul_zero, add_zero, add_assoc] using hd

private theorem coupled_circle_eventually_line_mem
    {U : Set (StateDirections S × ℝ)} (hU : IsOpen U)
    {z : StateDirections S × ℝ} (hz : z ∈ U) (v : StateDirections S × ℝ) :
    ∀ᶠ t : ℝ in 𝓝 0,
      z + coupledScalarAction (E := StateDirections S × ℝ) t v ∈ U :=
  coupledScalarAction_eventually_line_mem hU hz v

/-- Nu does not change the actual residual. Thus its first jet is zero
in the original even-circle space, not merely after point evaluation. -/
theorem coupled_circle_nu_firstJet_eq_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (hcircle : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      (P.circle x).val = R.residual x)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) (μ : ℝ) :
    (projectiveJetHeadLinear J.D 0 z Fin.elim0 (coupledSectorNuDirection S μ, 0)).2 = 0 := by
  have hd := coupled_sector_circle_first_derivative J hz (coupledSectorNuDirection S μ, 0)
  have hnear := coupled_circle_eventually_line_mem J.open_domain hz
    (coupledSectorNuDirection S μ, 0)
  have href : referenceStateConditions D S C := h1.2.2.1
  have heq :
      (fun t : ℝ => (sectorJointResidual S C P
        (z + coupledScalarAction (E := StateDirections S × ℝ) t
          (coupledSectorNuDirection S μ, 0))).2) =ᶠ[𝓝 0]
      (fun _ : ℝ => (sectorJointResidual S C P z).2) := by
    filter_upwards [hnear] with t ht
    apply Subtype.ext
    change (P.circle (liftSectorParameter S C
      (z + coupledScalarAction (E := StateDirections S × ℝ) t
        (coupledSectorNuDirection S μ, 0)))).val =
        (P.circle (liftSectorParameter S C z)).val
    exact (hcircle _ (liftSectorParameter_mem_stateNeighborhood ht le_rfl)
      (href.liftSectorParameter_sector _)).trans
      ((coupled_returnResidual_sector_nu_line hT hS h1 h2 hz μ t ht).trans
        (hcircle _ (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
          (href.liftSectorParameter_sector _)).symm)
  exact hd.unique (coupled_lineDerivAt_congr_line
    (hasProjectiveLineDerivAt_const ((sectorJointResidual S C P z).2) z
      (coupledSectorNuDirection S μ, 0)) heq)

theorem coupled_circle_nu_hasLineDerivAt_zero
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (hcircle : ∀ x ∈ stateNeighborhood S C base ε, stateSector S x.1 →
      (P.circle x).val = R.residual x)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {z : StateDirections S × ℝ} (hz : z ∈ sectorNeighborhood S base ε ε) (μ : ℝ) :
    HasProjectiveLineDerivAt (fun x => (P.circle (x, z.2)).val) 0
      (liftSectorParameter S C z).1 (0, (μ, (0, 0))) := by
  have hd := coupled_circle_first_derivative J hz (coupledSectorNuDirection S μ)
  have he := congrArg Subtype.val
    (coupled_circle_nu_firstJet_eq_zero hT hS h1 h2 hcircle J hz μ)
  simpa only [he, Submodule.coe_zero, coupledSectorNuDirection_val] using hd

/-- N08 already identifies the actual height derivative with `q` times
the height row. Its zero-parameter specialization gives zero immediately. -/
theorem coupled_circle_height_zero_hasLineDerivAt
    {G : ScalarInverseData S} {B : ControlColumnData S}
    (h8 : N08Properties D T S C R G P B base loss ε)
    {x : AnnularState S} (hx : (x, 0) ∈ stateNeighborhood S C base ε)
    (hs : stateSector S x) (η : HeightPair S) :
    HasProjectiveLineDerivAt (fun y => (P.circle (y, 0)).val) 0 x (η, (0, (0, 0))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hheight, _⟩ := h8
  simpa only [zero_smul] using hheight (x, 0) hx hs η

theorem coupled_circle_height_firstJet_zero_parameter
    {G : ScalarInverseData S} {B : ControlColumnData S}
    (href : referenceStateConditions D S C)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (J : SmoothDirections (sectorNeighborhood S base ε ε) (sectorJointResidual S C P))
    {x : StateDirections S} (hx : (x, 0) ∈ sectorNeighborhood S base ε ε)
    (η : HeightPair S) :
    (projectiveJetHeadLinear J.D 0 (x, 0) Fin.elim0
      (coupledSectorHeightDirection S η, 0)).2 = 0 := by
  have hd := coupled_circle_first_derivative J hx (coupledSectorHeightDirection S η)
  have hz := coupled_circle_height_zero_hasLineDerivAt h8
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (href.liftSectorParameter_sector (x, 0)) η
  apply Subtype.ext
  exact hd.unique hz

end ContinuousFlexibility.Statements
