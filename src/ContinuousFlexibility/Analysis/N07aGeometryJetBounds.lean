import ContinuousFlexibility.Analysis.N07aMaterialProductBounds
import ContinuousFlexibility.Analysis.N07aMixedLocalCalculus
import ContinuousFlexibility.Analysis.N07aNeighborhood

/-!
# Absolute bounds for the actual geometric jets

The reference and current-minus-reference clauses combine into one fixed
state loss and a sampled subpower envelope. The envelope is kept as a
whole function, so later products are absorbed only after the complete
finite expression has been formed.
-/

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

theorem N07aSampleSubpower.height_rpow
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    {γ : ℝ} (hγ : 0 < γ) :
    N07aSampleSubpower T K (fun m => T.H (T.sample (K.cell m)) ^ γ) := by
  obtain ⟨A, hA, hAb⟩ := n07a_materialSample_envelope_bound hD hT hγ 0
  apply (N07aSampleSubpower.const hD hT (K := K) A).mono
  intro m
  have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  rw [abs_of_pos (Real.rpow_pos_of_pos (hT.2.1 _ hm).2.1 γ), abs_of_pos hA]
  simpa only [Real.rpow_zero, mul_one] using hAb (K.cell m)

theorem n07a_geometryAtom_jet_decomposition
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (a : CanonicalGeometry.Atom) (p : CanonicalGeometry.unitStrip) (i j : ℕ) :
    mixedDerivative i j
      (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a) p.val =
      CanonicalGeometry.differenceJets D T S C L K z a m i j p +
        mixedDerivative i j
          (CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a) p.val := by
  let f := CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a
  let g := CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m a
  have hf : ContDiffOn ℝ ∞ f CanonicalGeometry.unitStrip := (hcur.1 z hz m a).1
  have hg : ContDiffOn ℝ ∞ g CanonicalGeometry.unitStrip := (href.1 m a).1
  have he : (fun q => (f q - g q) + g q) = f := by
    funext q
    exact sub_add_cancel _ _
  have h := n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
    (hf.sub hg) hg i j p.property
  rw [he] at h
  exact h

private theorem n07a_geometryJet_numeric_bound {u v a b p : ℝ}
    (hu : |u| ≤ a) (hv : |v| ≤ b * p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    |v + u| ≤ (a + b) * (1 + p) := by
  have hab := abs_add_le v u
  nlinarith [mul_nonneg ha hp]

theorem n07a_geometryAtom_absolute_jet_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ m a (p : CanonicalGeometry.unitStrip) i j,
        i + j ≤ s →
          |mixedDerivative i j
            (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m a) p.val| ≤
            e m * (1 + CanonicalGeometry.parameterGrading S (s + loss) z) := by
  let loss : ℕ := hcur.2.1.choose
  have hdiff := hcur.2.1.choose_spec
  refine ⟨loss, fun s => ?_⟩
  let B₀ : ℝ := (href.2 s).choose
  have hB₀ : 0 < B₀ := (href.2 s).choose_spec.1
  have hb₀ := (href.2 s).choose_spec.2
  let B₁ : ℝ := (hdiff s).choose
  have hB₁ : 0 < B₁ := (hdiff s).choose_spec.1
  have hb₁ := (hdiff s).choose_spec.2
  let e₀ : ℕ → ℝ := fun m => B₀ * T.E0 (T.sample (K.cell m)) ^ B₀
  let e₁ : ℕ → ℝ := fun m => B₁ * T.E0 (T.sample (K.cell m)) ^ B₁ *
    T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ)
  have he₀ : N07aSampleSubpower T K e₀ := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.const hD hT B₀) (N07aSampleSubpower.e0_rpow hD hT B₀)
  have he₁ : N07aSampleSubpower T K e₁ := N07aSampleSubpower.mul hD hT
    (N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT B₁)
      (N07aSampleSubpower.e0_rpow hD hT B₁))
    (N07aSampleSubpower.height_rpow hD hT (by norm_num : 0 < (3 / 4 : ℝ)))
  have he₀pos (m : ℕ) : 0 ≤ e₀ m := by
    have hm := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
    exact mul_nonneg hB₀.le (Real.rpow_nonneg (hT.2.1 _ hm).2.2.1.le _)
  have he₁pos (m : ℕ) : 0 ≤ e₁ m :=
    n07a_materialSample_jetFactor_nonneg hD hT hB₁.le (K.cell m)
  refine ⟨fun m => e₀ m + e₁ m, he₀.add he₁,
    fun m => add_nonneg (he₀pos m) (he₁pos m), fun z hz m a p i j hij => ?_⟩
  have h := n07a_geometryJet_numeric_bound (hb₀ m a p.val p.property i j hij)
    (hb₁ z hz m a p i j hij) (he₀pos m) (he₁pos m)
    (apply_nonneg (CanonicalGeometry.parameterGrading S (s + loss)) z)
  exact (congrArg abs (n07a_geometryAtom_jet_decomposition href hcur z hz m a p i j)).le.trans h

end ContinuousFlexibility.Analysis
