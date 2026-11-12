import ContinuousFlexibility.Analysis.N01CoefficientParameterTower
import ContinuousFlexibility.Analysis.N01CoefficientMixedBounds
import ContinuousFlexibility.Analysis.N01EndpointAngularJets
import ContinuousFlexibility.Analysis.SmoothDirectionsSpatialJets
import ContinuousFlexibility.Analysis.MixedDerivativeHierarchy

/-!
# Actual spatial derivatives of the original N01 coefficient towers

On a fixed negative component, all spatial labels lie in one actual
reference cell. The original one-high bounds therefore supply uniform
seminorm bounds for the given parameter towers. Local FTC identifies
their genuine spatial derivatives with the towers of coefficientFamily
at the corresponding mixed orders. No continuity of higher parameter
jets is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

local instance n01CoefficientSpatialJetsStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem coefficientFamily_eq_mixedDerivative_zero
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) (z : AnnularState S × ℝ) :
    coefficientFamily D S C i a b p z =
      mixedDerivative a b (fun q => coefficientFamily D S C i 0 0 q z) p := by
  simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero]

theorem N01Properties.coefficientFamily_contDiffOn
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) (a b : ℕ) :
    ContDiffOn ℝ ∞ (fun p => coefficientFamily D S C i a b p z) (annularOpen D) := by
  have hzero : ContDiffOn ℝ ∞ (fun p => coefficientFamily D S C i 0 0 p z)
      (annularOpen D) := by
    apply ((hN.original_coefficient_contDiffOn hS hT hz hsector i).sub
      (hN.original_coefficient_contDiffOn hS hT hN.reference_mem_stateNeighborhood
        hN.2.2.1.stateSector i)).congr
    intro p hp
    simp only [coefficientFamily, mixedDerivative, iteratedDeriv_zero, Pi.sub_apply, ite_apply]
  apply (contDiffOn_mixedDerivative (isOpen_Ioo.prod isOpen_univ) hzero a b).congr
  intro p hp
  exact coefficientFamily_eq_mixedDerivative_zero D S C i a b p z

theorem N01Properties.coefficientFamily_hasDerivAt_radial
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) (a b : ℕ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt (fun r => coefficientFamily D S C i a b (r, p.2) z)
      (coefficientFamily D S C i (a + 1) b p z) p.1 := by
  have h := mixedDerivative_hasDerivAt_radial (isOpen_Ioo.prod isOpen_univ)
    (hN.coefficientFamily_contDiffOn hS hT hz hsector i 0 0) a b hp
  have hvalue := (coefficientFamily_eq_mixedDerivative_zero D S C i (a + 1) b p z).symm
  apply (h.congr_deriv hvalue).congr_of_eventuallyEq
  exact Eventually.of_forall (fun r => coefficientFamily_eq_mixedDerivative_zero D S C i a b (r, p.2) z)

theorem N01Properties.coefficientFamily_hasDerivAt_angular
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (i : Fin 3) (a b : ℕ)
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    HasDerivAt (fun θ => coefficientFamily D S C i a b (p.1, θ) z)
      (coefficientFamily D S C i a (b + 1) p z) p.2 := by
  have h := mixedDerivative_hasDerivAt_angular (isOpen_Ioo.prod isOpen_univ)
    (hN.coefficientFamily_contDiffOn hS hT hz hsector i 0 0) a b hp
  have hvalue := (coefficientFamily_eq_mixedDerivative_zero D S C i a (b + 1) p z).symm
  apply (h.congr_deriv hvalue).congr_of_eventuallyEq
  exact Eventually.of_forall (fun θ => coefficientFamily_eq_mixedDerivative_zero D S C i a b (p.1, θ) z)

def N01Properties.componentCoefficientTower
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint)
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    SmoothDirections (sectorNeighborhood S base ε ε)
      (fun z => coefficientFamily D S C i a b p (liftSectorParameter S C z)) :=
  hN.sectorCoefficientTower j i a b p (hcell hp.1)

theorem N01Properties.componentCoefficientTower_uniformBounds
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b : ℕ) :
    UniformScalarJetSeminormBounds
      (fun p : Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) =>
        hN.componentCoefficientTower m j hcell i a b p p.property) := by
  apply uniformScalarJetSeminormBounds_of_oneHigh
    (pairGrading (sectorGrading S) realGrading)
    (sectorPairGrading_continuous S) (sectorPairGrading_monotone S)
    base (fun _ => a + b + loss)
  intro n
  let data := hN.sectorCoefficientTower_bound n (a + b)
  let B : ℝ := data.choose
  have hB : 0 < B := data.choose_spec.1
  have hsample := materialSample_mem_radialCore hT hN.1.1.choose_spec.2.1 j
  have hweights := hT.2.1 _ hsample
  refine ⟨B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B,
    mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg hweights.2.1.le _))
      (Real.rpow_nonneg hweights.2.2.1.le _), ?_⟩
  intro p z hz v
  exact data.choose_spec.2 j i a b p le_rfl (hcell p.property.1) z hz v

theorem N01Properties.componentCoefficientTower_localBounds
    (hN : N01Properties D T S C base loss ε) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b : ℕ) :
    LocalUniformScalarJetSeminormBounds (hN.componentCoefficientTower m j hcell i a b) := by
  intro p hp
  exact ⟨Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ), subset_rfl,
    isOpen_Ioo.prod isOpen_univ, hp,
    hN.componentCoefficientTower_uniformBounds hT m j hcell i a b⟩

private theorem coefficient_component_subset_annular
    (hN : N01Properties D T S C base loss ε) (m : ℕ) :
    Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) ⊆ annularOpen D := by
  intro p hp
  have hends := hN.2.2.2.1.1 m
  exact ⟨⟨hends.1.trans hp.1.1, hp.1.2.trans hends.2.2⟩, mem_univ _⟩

private theorem coefficient_component_continuous
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (i : Fin 3)
    (a b : ℕ) (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε) :
    ContinuousOn (fun p => coefficientFamily D S C i a b p (liftSectorParameter S C x))
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
  (hN.coefficientFamily_contDiffOn hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) i a b).continuousOn.mono
      (coefficient_component_subset_annular hN m)

private theorem coefficient_component_radial
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (i : Fin 3)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε) :
    HasDerivAt (fun r => coefficientFamily D S C i a b (r, p.2) (liftSectorParameter S C x))
      (coefficientFamily D S C i (a + 1) b p (liftSectorParameter S C x)) p.1 :=
  hN.coefficientFamily_hasDerivAt_radial hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) i a b (coefficient_component_subset_annular hN m hp)

private theorem coefficient_component_angular
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (m : ℕ) (i : Fin 3)
    (a b : ℕ) (p : PolarPoint) (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε) :
    HasDerivAt (fun θ => coefficientFamily D S C i a b (p.1, θ) (liftSectorParameter S C x))
      (coefficientFamily D S C i a (b + 1) p (liftSectorParameter S C x)) p.2 :=
  hN.coefficientFamily_hasDerivAt_angular hS hT
    (liftSectorParameter_mem_stateNeighborhood hx le_rfl)
    (hN.2.2.1.liftSectorParameter_sector x) i a b (coefficient_component_subset_annular hN m hp)

def N01Properties.componentCoefficientScalarJet
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (v : Fin n → StateDirections S × ℝ) : PolarPoint → ℝ :=
  localScalarJet (hN.componentCoefficientTower m j hcell i 0 0) n x v

theorem N01Properties.componentCoefficientScalarJet_of_mem
    (hN : N01Properties D T S C base loss ε)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (v : Fin n → StateDirections S × ℝ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :
    hN.componentCoefficientScalarJet m j hcell i n x v p =
      (hN.sectorCoefficientTower j i 0 0 p (hcell hp.1)).D n x v :=
  localScalarJet_of_mem (hN.componentCoefficientTower m j hcell i 0 0) n x v hp

theorem N01Properties.componentCoefficientScalarJet_contDiffOn
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (n : ℕ) (x : StateDirections S × ℝ)
    (hx : x ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
    ContDiffOn ℝ ∞ (hN.componentCoefficientScalarJet m j hcell i n x v)
      (Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ)) :=
  localScalarJet_spatial_contDiffOn (hN.componentCoefficientTower m j hcell i)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (coefficient_component_continuous hN hS hT m i)
    (hN.componentCoefficientTower_localBounds hT m j hcell i)
    (coefficient_component_radial hN hS hT m i) (coefficient_component_angular hN hS hT m i)
    0 0 n x hx v

theorem N01Properties.componentCoefficientScalarJet_mixedDerivative
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b n : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x : StateDirections S × ℝ) (hx : x ∈ sectorNeighborhood S base ε ε)
    (v : Fin n → StateDirections S × ℝ) :
    mixedDerivative a b (hN.componentCoefficientScalarJet m j hcell i n x v) p =
      (hN.sectorCoefficientTower j i a b p (hcell hp.1)).D n x v :=
  localScalarJet_spatial_mixedDerivative (hN.componentCoefficientTower m j hcell i)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (coefficient_component_continuous hN hS hT m i)
    (hN.componentCoefficientTower_localBounds hT m j hcell i)
    (coefficient_component_radial hN hS hT m i) (coefficient_component_angular hN hS hT m i)
    a b n hp x hx v

theorem N01Properties.componentCoefficientScalarJet_hasDerivAt_line
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (m j : ℕ) (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
    (i : Fin 3) (a b n : ℕ) {p : PolarPoint}
    (hp : p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ))
    (x w : StateDirections S × ℝ) {t : ℝ}
    (ht : x + t • w ∈ sectorNeighborhood S base ε ε) (v : Fin n → StateDirections S × ℝ) :
    HasDerivAt
      (fun s => mixedDerivative a b (hN.componentCoefficientScalarJet m j hcell i n (x + s • w) v) p)
      (mixedDerivative a b (hN.componentCoefficientScalarJet m j hcell i (n + 1)
        (x + t • w) (Fin.cons w v)) p) t :=
  localScalarJet_spatial_line_hasDerivAt (hN.componentCoefficientTower m j hcell i)
    (sectorNeighborhood_isOpen S base ε ε) (sectorNeighborhood_convex S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (coefficient_component_continuous hN hS hT m i)
    (hN.componentCoefficientTower_localBounds hT m j hcell i)
    (coefficient_component_radial hN hS hT m i) (coefficient_component_angular hN hS hT m i)
    a b n hp x w ht v

theorem N01Properties.componentCoefficientScalarJet_mixed_bound
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T) (n s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m j (hcell : Ioo (C.left m) (C.right m) ⊆ D.cells j)
      (i : Fin 3) a b, a + b ≤ s → ∀ p,
      p ∈ Ioo (C.left m) (C.right m) ×ˢ (univ : Set ℝ) →
      ∀ x ∈ sectorNeighborhood S base ε ε, ∀ v : Fin n → StateDirections S × ℝ,
      |mixedDerivative a b (hN.componentCoefficientScalarJet m j hcell i n x v) p| ≤
        B * T.H (T.sample j) ^ (3 / 4 : ℝ) * T.E0 (T.sample j) ^ B *
          oneHighVariationWeight (pairGrading (sectorGrading S) realGrading) base (s + loss) x v := by
  let data := hN.sectorCoefficientTower_bound n s
  refine ⟨data.choose, data.choose_spec.1, ?_⟩
  intro m j hcell i a b hab p hp x hx v
  have heq := hN.componentCoefficientScalarJet_mixedDerivative hS hT m j hcell i a b n hp x hx v
  exact (congrArg abs heq).trans_le (data.choose_spec.2 j i a b p hab (hcell hp.1) x hx v)

end ContinuousFlexibility.Statements
