module

public import ContinuousFlexibility.Analysis.ReturnCorrectionResidualBilinear
public import ContinuousFlexibility.Analysis.ReturnCorrectionTraceFlux
public import ContinuousFlexibility.Analysis.MaterialDivergenceEnergy
public import ContinuousFlexibility.Analysis.MaterialJetParameterDerivatives

/-!
# The actual symmetric divergence as a bilinear field operator

The coefficient argument consists of the two actual smooth coefficient
errors. The height argument is the original height pair, decoded through
its weighted height-space coordinate. Spatial differentiation is applied
only after differentiability has been proved. The output is extended by
zero outside the annulus, as required by the physical source decoder.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped ContDiff Topology Classical

local instance returnDivergenceBilinearRealNormedSpace : NormedSpace ℝ ℝ :=
    NormedField.toNormedSpace

def annularSmoothFieldSpace (D : ReferenceData) :
    Submodule ℝ (PolarPoint → ℝ) where
  carrier := {f | ContDiffOn ℝ ∞ f (annularOpen D)}
  zero_mem' := contDiffOn_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => contDiffOn_const.smul hf

/-- Actual weighted spatial jets are linear on actual smooth fields. -/
def annularWeightedJetLinear
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (a b c : ℕ) :
    annularSmoothFieldSpace D →ₗ[ℝ] (PolarPoint → ℝ) where
  toFun f := weightedPhysicalJet T γ a b c f.val
  map_add' f g := by
    funext p
    exact weightedPhysicalJet_add hT f.property g.property a b c p
  map_smul' d f := by
    funext p
    exact weightedPhysicalJet_const_mul d f.val a b c p

theorem annularWeightedJetLinear_apply
    {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)
    (γ : ℝ) (a b c : ℕ) (f : annularSmoothFieldSpace D) (p : PolarPoint) :
    annularWeightedJetLinear hT γ a b c f p =
      weightedPhysicalJet T γ a b c f.val p := rfl

/-- The existing smooth coefficient fields form an algebraic subspace;
no auxiliary norm or completion is used. -/
def annularSmoothCoefficientSpace (D : ReferenceData) :
    Submodule ℝ (PolarPoint → ℝ × ℝ) where
  carrier := {A | ContDiffOn ℝ ∞ A (annularOpen D)}
  zero_mem' := contDiffOn_const
  add_mem' := fun hA hB => hA.add hB
  smul_mem' := fun c A hA => contDiffOn_const.smul hA

def smoothCoefficientFirst (D : ReferenceData) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.pi fun p => (LinearMap.fst ℝ ℝ ℝ).comp
    ((LinearMap.proj p).comp (annularSmoothCoefficientSpace D).subtype))

def smoothCoefficientSecond (D : ReferenceData) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.pi fun p => (LinearMap.snd ℝ ℝ ℝ).comp
    ((LinearMap.proj p).comp (annularSmoothCoefficientSpace D).subtype))

def decodedHeightPairLinear (S : PhysicalSpacesData) :
    HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  (S.height (3 / 4 : ℝ)).decode.comp
    (LinearMap.fst ℝ (S.height (3 / 4 : ℝ)).Space ℝ)

theorem decodedHeightPairLinear_apply (S : PhysicalSpacesData)
    (η : HeightPair S) :
    decodedHeightPairLinear S η = (S.height (3 / 4 : ℝ)).decode η.1 := rfl

def decodedHeightPairPartialLinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (v : PolarPoint) :
    HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  spatialDirectionalLinear univ v (decodedHeightPairLinear S)
    (fun η p _ =>
      (physical_height_contDiff_and_flatJets hT hS
        (by norm_num : (0 : ℝ) < 3 / 4) η.1).1.differentiable (by simp) p)

set_option backward.isDefEq.respectTransparency false in
theorem decodedHeightPairPartialLinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (v : PolarPoint) (η : HeightPair S) (p : PolarPoint) :
    decodedHeightPairPartialLinear hS hT v η p =
      fderiv ℝ ((S.height (3 / 4 : ℝ)).decode η.1) p v := by
  simp only [decodedHeightPairPartialLinear, spatialDirectionalLinear_apply,
    mem_univ, if_true, decodedHeightPairLinear_apply]

def symmetricRadialFluxBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
    (smoothCoefficientFirst D) (decodedHeightPairPartialLinear hS hT (0, 1))

def symmetricAngularFluxBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
      (smoothCoefficientFirst D) (decodedHeightPairPartialLinear hS hT (1, 0)) +
    (LinearMap.mul ℝ (PolarPoint → ℝ)).compl₁₂
      (smoothCoefficientSecond D) (decodedHeightPairPartialLinear hS hT (0, 1))

theorem symmetricRadialFluxBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) (p : PolarPoint) :
    symmetricRadialFluxBilinear hS hT A η p =
      (A.val p).1 * angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p := by
  simp only [symmetricRadialFluxBilinear, LinearMap.compl₁₂_apply,
    LinearMap.mul_apply', Pi.mul_apply, smoothCoefficientFirst,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.proj_apply, Submodule.subtype_apply,
    decodedHeightPairPartialLinear_apply, angularPartial]

theorem symmetricAngularFluxBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) (p : PolarPoint) :
    symmetricAngularFluxBilinear hS hT A η p =
      (A.val p).1 * radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) p +
        (A.val p).2 * angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) p := by
  simp only [symmetricAngularFluxBilinear, LinearMap.add_apply, Pi.add_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', Pi.mul_apply,
    smoothCoefficientFirst, smoothCoefficientSecond, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.proj_apply, Submodule.subtype_apply,
    decodedHeightPairPartialLinear_apply, radialPartial, angularPartial]

theorem symmetricErrorFluxes_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) :
    ContDiffOn ℝ ∞ (symmetricRadialFluxBilinear hS hT A η) (annularOpen D) ∧
      ContDiffOn ℝ ∞ (symmetricAngularFluxBilinear hS hT A η) (annularOpen D) := by
  have hu := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).1
  have hr := contDiffOn_radialPartial_of_isOpen (isOpen_Ioo.prod isOpen_univ) hu
  have ht := contDiffOn_angularPartial_of_isOpen (isOpen_Ioo.prod isOpen_univ) hu
  constructor
  · exact (A.property.fst.mul ht).congr
      (fun p _ => symmetricRadialFluxBilinear_apply hS hT A η p)
  · exact ((A.property.fst.mul hr).add (A.property.snd.mul ht)).congr
      (fun p _ => symmetricAngularFluxBilinear_apply hS hT A η p)

def symmetricDivergenceBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] HeightPair S →ₗ[ℝ] (PolarPoint → ℝ) :=
  spatialDirectionalBilinear (annularOpen D) (1, 0)
      (symmetricRadialFluxBilinear hS hT)
      (fun A η p hp =>
        ((symmetricErrorFluxes_contDiffOn hS hT A η).1.contDiffAt
          ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)) +
    spatialDirectionalBilinear (annularOpen D) (0, 1)
      (symmetricAngularFluxBilinear hS hT)
      (fun A η p hp =>
        ((symmetricErrorFluxes_contDiffOn hS hT A η).2.contDiffAt
          ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp))

theorem symmetricDivergenceBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) (p : PolarPoint) :
    symmetricDivergenceBilinear hS hT A η p =
      if p ∈ annularOpen D then
        radialPartial (fun q => (A.val q).1 *
          angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p +
        angularPartial (fun q => (A.val q).1 *
          radialPartial ((S.height (3 / 4 : ℝ)).decode η.1) q +
          (A.val q).2 * angularPartial ((S.height (3 / 4 : ℝ)).decode η.1) q) p
      else 0 := by
  classical
  have hF := funext (symmetricRadialFluxBilinear_apply hS hT A η)
  have hG := funext (symmetricAngularFluxBilinear_apply hS hT A η)
  by_cases hp : p ∈ annularOpen D
  · simp only [symmetricDivergenceBilinear, LinearMap.add_apply, Pi.add_apply,
      spatialDirectionalBilinear_apply, if_pos hp, hF, hG, radialPartial, angularPartial]
  · simp only [symmetricDivergenceBilinear, LinearMap.add_apply, Pi.add_apply,
      spatialDirectionalBilinear_apply, if_neg hp, add_zero]

theorem symmetricDivergenceBilinear_contDiffOn
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) :
    ContDiffOn ℝ ∞ (symmetricDivergenceBilinear hS hT A η) (annularOpen D) := by
  have hF := (symmetricErrorFluxes_contDiffOn hS hT A η).1
  have hG := (symmetricErrorFluxes_contDiffOn hS hT A η).2
  have h := (contDiffOn_radialPartial_of_isOpen (isOpen_Ioo.prod isOpen_univ) hF).add
    (contDiffOn_angularPartial_of_isOpen (isOpen_Ioo.prod isOpen_univ) hG)
  apply h.congr
  intro p hp
  have hp' : p ∈ annularOpen D := hp
  simp only [symmetricDivergenceBilinear, LinearMap.add_apply, Pi.add_apply,
    spatialDirectionalBilinear_apply, if_pos hp', radialPartial, angularPartial]

def symmetricDivergenceSmoothBilinear
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) :
    annularSmoothCoefficientSpace D →ₗ[ℝ] HeightPair S →ₗ[ℝ] annularSmoothFieldSpace D :=
  LinearMap.codRestrict₂ (symmetricDivergenceBilinear hS hT)
    (annularSmoothFieldSpace D).subtype (fun _ _ h => Subtype.ext h)
    (fun A η => ⟨⟨symmetricDivergenceBilinear hS hT A η,
      symmetricDivergenceBilinear_contDiffOn hS hT A η⟩, rfl⟩)

theorem symmetricDivergenceSmoothBilinear_apply
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (A : annularSmoothCoefficientSpace D) (η : HeightPair S) :
    (symmetricDivergenceSmoothBilinear hS hT A η).val =
      symmetricDivergenceBilinear hS hT A η := by
  exact LinearMap.codRestrict₂_apply (symmetricDivergenceBilinear hS hT)
    (annularSmoothFieldSpace D).subtype (fun _ _ h => Subtype.ext h)
    (fun B ζ => ⟨⟨symmetricDivergenceBilinear hS hT B ζ,
      symmetricDivergenceBilinear_contDiffOn hS hT B ζ⟩, rfl⟩) A η

/-- Parameter differentiation of every actual weighted jet commutes
with the smooth coefficient argument of the bilinear divergence. -/
theorem symmetricDivergenceBilinear_physicalJetHasDerivAt
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {γ t : ℝ} (A : ℝ → annularSmoothCoefficientSpace D)
    (A' : annularSmoothCoefficientSpace D) (η : HeightPair S)
    (hfirst : MixedJetHasDerivAt
      (fun s p => ((A s).val (T.radius p.1, p.2)).1)
      (fun p => (A'.val (T.radius p.1, p.2)).1) t)
    (hsecond : MixedJetHasDerivAt
      (fun s p => ((A s).val (T.radius p.1, p.2)).2)
      (fun p => (A'.val (T.radius p.1, p.2)).2) t) :
    PhysicalJetHasDerivAt T γ
      (fun s => symmetricDivergenceBilinear hS hT (A s) η)
      (symmetricDivergenceBilinear hS hT A' η) t := by
  have hd := physicalJetHasDerivAt_symmetric_divergence (γ := γ) hT
    (Filter.Eventually.of_forall fun s => (A s).property.fst)
    (Filter.Eventually.of_forall fun s => (A s).property.snd)
    A'.property.fst A'.property.snd ((hS.1 (3 / 4 : ℝ)).2.2.2.1 η.1).1
    hfirst hsecond
  apply hd.congr_on_annularOpen hT
  · exact Filter.Eventually.of_forall fun s p hp => by
      rw [symmetricDivergenceBilinear_apply, if_pos hp]
  · intro p hp
    rw [symmetricDivergenceBilinear_apply, if_pos hp]

/-- The zeroth jet is the prescribed independent-residual error itself. -/
theorem N01Properties.symmetricDivergenceBilinear_actual
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (R : ReturnEquationData S) (χ : ℕ → ℝ → ℝ) (z : AnnularState S × ℝ)
    (ρ : CircleSpace S) (η : HeightPair S)
    (hA : ContDiffOn ℝ ∞ (fun p => returnCorrectionCoefficientError D S C R χ z p ρ)
      (annularOpen D)) :
    symmetricDivergenceBilinear hS hT ⟨_, hA⟩ η =
      returnCorrectionResidualErrorField D S C R χ z ρ η := by
  classical
  funext p
  rw [symmetricDivergenceBilinear_apply]
  by_cases hp : p ∈ annularOpen D
  · rw [if_pos hp]
    exact (hN.returnCorrectionResidualErrorField_eq_decoded_divergence hS R χ z ρ η p hp).symm
  · rw [if_neg hp]
    exact (returnCorrectionResidualErrorField_zero_outside D S C R χ z ρ η p hp).symm

end ContinuousFlexibility.Statements
