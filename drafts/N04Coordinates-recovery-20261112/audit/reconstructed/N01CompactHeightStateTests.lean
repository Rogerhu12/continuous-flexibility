import ContinuousFlexibility.Analysis.ReferenceCompactCosineNormalTest
import ContinuousFlexibility.Analysis.CompactEvenHeightTests
import ContinuousFlexibility.Analysis.CoupledStateScalarAction
import ContinuousFlexibility.Analysis.CoupledLogProfileCoefficientJets
import ContinuousFlexibility.Analysis.N04bRootCoefficientGerms
import ContinuousFlexibility.Scalar.WeightedDecodeLift

/-!
# Compact height tests in the supplied nonlinear state space

The same Sobolev decoder realizes the actual compact cosine test. Only
the height coordinate is varied, so the fixed sector and profile are
preserved. The denominator test below is a consequence of the original
N01 state ball, while the original Through03 determinant still vanishes
at every fixed reference root. No absolute optical-root lower bound is
assumed or concluded.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The genuine compact second-mode test has a preimage in the same
height model, with its exact physical grading and zero endpoint constant. -/
theorem referenceCompactCosine_heightPair
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ Ioo D.a D.b) :
    ∃ η : HeightPair S, η.2 = 0 ∧
      heightPairField S η = referenceCompactCosine u ∧
      ∀ n, heightPairGrading S n η =
        physicalNorm T (3 / 4 : ℝ) n (referenceCompactCosine u) := by
  have hf : ContDiff ℝ ∞ (referenceCompactCosine u) :=
    (hu.comp contDiff_fst).mul ((r11b_contDiff_cosineMode 2).comp contDiff_snd)
  have heven : ∀ r θ, referenceCompactCosine u (r, -θ) =
      referenceCompactCosine u (r, θ) := by
    intro r θ
    simp only [referenceCompactCosine, cosineMode_even]
  have hperiod : Function.Periodic (referenceCompactCosine u) (0, Real.pi) := by
    rintro ⟨r, θ⟩
    change u (r + 0) * cosineMode 2 (θ + Real.pi) = u r * cosineMode 2 θ
    rw [add_zero]
    exact congrArg (fun a : ℝ => u r * a)
      (cosineMode_even_frequency_periodic 1 θ)
  have hsupport : HasCompactRadialSupport D (referenceCompactCosine u) := by
    refine ⟨tsupport u, hc, hs, ?_⟩
    intro r hr θ
    simp only [referenceCompactCosine, image_eq_zero_of_notMem_tsupport hr, zero_mul]
  have hm := heightMember_of_compact_even_periodic hT hf.contDiffOn
    heven hperiod hsupport (3 / 4 : ℝ)
  obtain ⟨v, hv⟩ := (hS.1 (3 / 4 : ℝ)).2.2.2.2.1 _ hm
  refine ⟨(v, 0), rfl, ?_, ?_⟩
  · funext p
    simp only [heightPairField, hv, zero_mul, add_zero]
  · intro n
    change (S.height (3 / 4 : ℝ)).grading n v + realGrading n (0 : ℝ) = _
    rw [map_zero, add_zero]
    simpa only [hv] using
      sobolevGrading_eq_physicalNorm (hS.1 (3 / 4 : ℝ)) v n

def n04CoordinatesHeightTestState (S : PhysicalSpacesData)
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) : AnnularState S :=
  (x.1 + coupledScalarAction t η, x.2)

theorem n04CoordinatesHeightTestState_sector
    {S : PhysicalSpacesData} {x : AnnularState S}
    (hx : stateSector S x) (η : HeightPair S) (t : ℝ) :
    stateSector S (n04CoordinatesHeightTestState S x η t) := hx

theorem n04CoordinatesHeightTestState_grading
    (S : PhysicalSpacesData) (x : AnnularState S) (η : HeightPair S)
    (t : ℝ) (n : ℕ) :
    stateGrading S n (n04CoordinatesHeightTestState S x η t - x) =
      |t| * heightPairGrading S n η := by
  simp only [n04CoordinatesHeightTestState, stateGrading, pairGrading_apply,
    Prod.fst_sub, Prod.snd_sub, sub_self, add_sub_cancel_left,
    coupledScalarAction, map_smul_eq_mul, Real.norm_eq_abs, map_zero, add_zero]

theorem n04CoordinatesHeightTestState_profile
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (x : AnnularState S) (η : HeightPair S) (t : ℝ) :
    stateProfile D S C (n04CoordinatesHeightTestState S x η t) =
      stateProfile D S C x := rfl

theorem n04CoordinatesHeightTestState_height
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (x : AnnularState S) (η : HeightPair S) (t q : ℝ) :
    stateHeight D S C (n04CoordinatesHeightTestState S x η t, q) =
      heightFamily (stateHeight D S C (x, q)) (heightPairField S η) (q * t) := by
  funext p
  change stateRadialHeight D S C x p.1 +
      q * heightPairField S (x.1 + coupledScalarAction t η) p =
    (stateRadialHeight D S C x p.1 + q * heightPairField S x.1 p) +
      (q * t) * heightPairField S η p
  simp only [heightPairField,
    Prod.fst_add, Prod.snd_add, coupledScalarAction_fst,
    coupledScalarAction_snd, map_add, Pi.add_apply,
    coupledScalarAction_linear_eval, coupledScalarAction_real, heightFamily]
  ring

theorem n04CoordinatesHeightTestState_mem
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S} {base : ℕ}
    {ε t q : ℝ} (η : HeightPair S)
    (ht : |t| * heightPairGrading S base η < ε) (hq : |q| < ε) :
    (n04CoordinatesHeightTestState S C.referenceState η t, q) ∈
      stateNeighborhood S C base ε :=
  ⟨(n04CoordinatesHeightTestState_grading S C.referenceState η t base).trans_lt ht, hq⟩

private theorem heightQ_heightFamily_affine
    (w : ℝ → ℝ) {h f : PolarPoint → ℝ} {p : PolarPoint}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ ∞ f) (hr : p.1 ≠ 0) (t : ℝ) :
    heightQ (profileEnergy w p) (heightRadial (heightFamily h f t) p)
        (angularPartial (heightAngular (heightFamily h f t)) p) =
      heightQ (profileEnergy w p) (heightRadial h p)
        (angularPartial (heightAngular h) p) +
      t * (heightRadial f p + profileEnergy w p * angularPartial (heightAngular f) p) := by
  rw [heightRadial_heightFamily (hh.differentiable (by simp))
    (hf.differentiable (by simp)),
    angularPartial_heightAngular_heightFamily hh hf hr]
  simp only [heightFamily, heightQ]
  ring

/-- Testing both signs of an actual height direction on the same state
ball bounds its Q-linear functional. This expression has no profile-root
derivative in its denominator. -/
theorem N01Properties.heightTest_denominator_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (η : HeightPair S) {t q : ℝ} (htpos : 0 < t) (hqpos : 0 < q)
    (ht : |t| * heightPairGrading S base η < ε) (hq : |q| < ε)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    8 * q * t * |heightRadial (heightPairField S η) p +
      profileEnergy D.w p * angularPartial (heightAngular (heightPairField S η)) p| ≤
        D.w p.1 := by
  let F := heightPairField S η
  let H := stateHeight D S C (C.referenceState, q)
  let Q₀ := heightQ (profileEnergy D.w p) (heightRadial H p)
    (angularPartial (heightAngular H) p)
  let B := heightRadial F p + profileEnergy D.w p * angularPartial (heightAngular F) p
  have hgeom := hN.1.1.choose_spec.1
  have hr : p.1 ≠ 0 := (hgeom.1.trans hp.1.1).ne'
  have hw : 0 < D.w p.1 := hgeom.2.2.2.2.1 p.1 hp.1
  have hF : ContDiff ℝ ∞ F := physical_height_with_cutoff_contDiff
    hT hS (by norm_num : (0 : ℝ) < 3 / 4) η.1 η.2
  have hH : ContDiff ℝ ∞ H := n04b_contDiff_stateHeight hT hS hN _
  have hprofile := coupled_stateProfile_reference hN.2.2.1
  have hbounds (s : ℝ) (hs : |s| * heightPairGrading S base η < ε) :
      (7 / 8 : ℝ) * D.w p.1 ≤ Q₀ + q * s * B ∧
        Q₀ + q * s * B ≤ (9 / 8 : ℝ) * D.w p.1 := by
    have hz := n04CoordinatesHeightTestState_mem (C := C) η hs hq
    have hsector := n04CoordinatesHeightTestState_sector hN.2.2.1.stateSector η s
    have hb := hN.2.2.2.2.2.2.2.2.2.1 _ hz hsector p hp
    have he : heightQ (profileEnergy D.w p)
        (heightRadial (stateHeight D S C
          (n04CoordinatesHeightTestState S C.referenceState η s, q)) p)
        (angularPartial (heightAngular (stateHeight D S C
          (n04CoordinatesHeightTestState S C.referenceState η s, q))) p) =
        Q₀ + q * s * B := by
      rw [n04CoordinatesHeightTestState_height]
      exact heightQ_heightFamily_affine D.w hH hF hr (q * s)
    have hlo : (7 / 8 : ℝ) * D.w p.1 ≤ Q₀ + q * s * B :=
      (le_div_iff₀ hw).mp (by
        simpa only [n04CoordinatesHeightTestState_profile, hprofile, he] using hb.2.2.1)
    have hhi : Q₀ + q * s * B ≤ (9 / 8 : ℝ) * D.w p.1 :=
      (div_le_iff₀ hw).mp (by
        simpa only [n04CoordinatesHeightTestState_profile, hprofile, he] using hb.2.2.2.1)
    exact ⟨hlo, hhi⟩
  have hplus := hbounds t ht
  have hminus := hbounds (-t) (by simpa only [abs_neg] using ht)
  change 8 * q * t * |B| ≤ D.w p.1
  rcases le_total 0 B with hB | hB
  · rw [abs_of_nonneg hB]
    nlinarith only [hplus.2, hminus.1]
  · rw [abs_of_nonpos hB]
    nlinarith only [hplus.1, hminus.2]

/-- The same real test line leaves every fixed Through03 root determinant
zero. This follows from the true profile factor, not from assumed vanishing
height jets or from a model of the final canonical atlas. -/
theorem n04CoordinatesHeightTestState_root_determinant
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε t q : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (η : HeightPair S) (ht : |t| * heightPairGrading S base η < ε)
    (hq : |q| < ε) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hroot : deriv D.w p.1 = 0) :
    let z := (n04CoordinatesHeightTestState S C.referenceState η t, q)
    (L.coefficients z).a p * (L.coefficients z).c p - (L.coefficients z).b p ^ 2 = 0 := by
  exact n04b_through03_determinant_eq_zero hT hS hN
    (n04CoordinatesHeightTestState_mem (C := C) η ht hq)
    (n04CoordinatesHeightTestState_sector hN.1.1.2.2.1.stateSector η t) hp hroot

end ContinuousFlexibility.Statements
