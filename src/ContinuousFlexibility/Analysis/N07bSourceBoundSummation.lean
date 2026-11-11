import ContinuousFlexibility.Analysis.N07bSourceBoundMajorant
import ContinuousFlexibility.Analysis.N07bSourceBoundChangeVariables
import ContinuousFlexibility.Analysis.N07bActualCanonicalSourceLift
import ContinuousFlexibility.Analysis.N07bAtlasEnergy

/-!
# Summation and actual lifting under a geometric coefficient bound

The actual angular-jet square integrals equal the physical row densities.
The uniform geometry-only comparison is an explicit additional hypothesis.
Under it, the disjoint atlas and one physical material majorant give both
genuine square summability and the norm of the actual prescribed lift.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Both integrability and the exact row energy identity follow from the
actual chart change of variables and the actual angular jet recursion. -/
theorem n07b_sourceBound_row_integral
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) (b m : ℕ) :
    IntegrableOn
        (n07bSourceRowDensity T K z ((S.height (3 / 4 : ℝ)).decode f.val) b m)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
      n07bActualCanonicalJetEnergy T K z f (3 / 4 : ℝ) 0 b m =
        ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
          n07bSourceRowDensity T K z ((S.height (3 / 4 : ℝ)).decode f.val) b m x := by
  classical
  let f₀ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode f.val
  have hf : ContDiff ℝ ∞ f₀ :=
    (physical_height_contDiff_and_flatJets hT hS (by norm_num : (0 : ℝ) < 3 / 4) f.val).1
  have hP : MeasurableSet
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (hK.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc)
  have hjet (j : Fin (b + 1)) := n07bActualCanonicalAngularJet_memLp hK hz hs hT hS f m j.val
  have heq (j : Fin (b + 1)) (x : PolarPoint) (hx : x ∈ physicalPieceOpen S K z m) :
      n07bActualCanonicalAngularJet K z f m j.val (K.chart z m x) =
        n07bPhysicalSourceJet K z m f₀ j.val x :=
    n07b_canonicalSource_angularJet_comp_chart_of_contDiff hK hz hs m hf j.val hx
  have hi (j : Fin (b + 1)) :
      IntegrableOn (fun x => |planeJacobian (K.chart z m) x| *
        (n07bPhysicalSourceJet K z m f₀ j.val x) ^ 2)
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) := by
    apply (n07b_sourceBound_square_integrable hK hz hs m (hjet j)).congr
    filter_upwards [ae_restrict_mem hP] with x hx
    exact congrArg (fun v : ℝ => |planeJacobian (K.chart z m) x| * v ^ 2)
      (heq j x hx.1)
  have hterm (j : Fin (b + 1)) :
      IntegrableOn (fun x => (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
        (|planeJacobian (K.chart z m) x| * (n07bPhysicalSourceJet K z m f₀ j.val x) ^ 2))
        (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (hi j).const_mul _
  constructor
  · change IntegrableOn (fun x => ∑ j : Fin (b + 1),
      (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
        (|planeJacobian (K.chart z m) x| * (n07bPhysicalSourceJet K z m f₀ j.val x) ^ 2)) _
    exact integrable_finsetSum Finset.univ (fun j _ => hterm j)
  · change (∑ j : Fin (b + 1), (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
      (eLpNorm (n07bActualCanonicalAngularJet K z f m j.val) 2
        (canonicalMeasure S K m)).toReal ^ 2) =
      ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        ∑ j : Fin (b + 1), (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 *
          (|planeJacobian (K.chart z m) x| * (n07bPhysicalSourceJet K z m f₀ j.val x) ^ 2)
    rw [integral_finsetSum Finset.univ (fun j _ => hterm j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, n07b_sourceBound_eLpNorm_sq hK hz hs m (hjet j)]
    apply congrArg (fun v : ℝ => (n07bCanonicalSourceFactor T K (3 / 4 : ℝ) 0 m)⁻¹ ^ 2 * v)
    apply setIntegral_congr_fun hP
    intro x hx
    exact congrArg (fun v : ℝ => |planeJacobian (K.chart z m) x| * v ^ 2)
      (heq j x hx.1)

/-- A uniform comparison of the actual geometric coefficients with `M²`
gives genuine summability of the prescribed angular-jet row energies. -/
theorem n07b_sourceBound_energy_summable
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) (b : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
        n07bSourceGeometricWeight T K z m x *
          n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤ A * T.M x.1 ^ 2) :
    Summable (n07bActualCanonicalJetEnergy T K z f (3 / 4 : ℝ) 0 b) ∧
      (∑' m, n07bActualCanonicalJetEnergy T K z f (3 / 4 : ℝ) 0 b m) ≤
        A * n07bSourcePathConstant b *
          physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2 := by
  let f₀ : PolarPoint → ℝ := (S.height (3 / 4 : ℝ)).decode f.val
  have hf : HeightMember D T (3 / 4 : ℝ) f₀ := (hS.1 (3 / 4 : ℝ)).2.2.2.1 f.val
  let g : PolarPoint → ℝ := fun x => A * n07bSourceMaterialMajorant T b f₀ x
  have hg : IntegrableOn g (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi) :=
    (n07bSourceMaterialMajorant_integrable hT hf b).const_mul A
  have hbound (m : ℕ) : n07bActualCanonicalJetEnergy T K z f (3 / 4 : ℝ) 0 b m ≤
      ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), g x := by
    have hrow := n07b_sourceBound_row_integral hT hS hK hz hs f b m
    rw [hrow.2]
    have hsub : physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) ⊆
        Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi :=
      fun x hx => ⟨((hK.domains z hz hs m).2.2.1 hx.1).1, hx.2.2⟩
    apply integral_mono_ae hrow.1 (hg.mono_set hsub)
    filter_upwards [ae_restrict_mem
      ((hK.domains z hz hs m).1.measurableSet.inter
        (MeasurableSet.univ.prod measurableSet_Ioc))] with x hx
    exact n07b_sourceBound_row_pointwise hT hK hz hs hf.1 b m hx.1 (hcoeff m x hx.1)
  have hsum := n07b_summable_energy_of_piece_integral_bound hK hz hs hg
    (fun m => n07bActualCanonicalJetEnergy_nonneg T K z f (3 / 4 : ℝ) 0 b m) hbound
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  change (∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi,
    A * n07bSourceMaterialMajorant T b f₀ x) ≤ _
  rw [integral_const_mul]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (n07bSourceMaterialMajorant_integral_le hT hf b) hA

/-- The preceding estimate constructs the actual element of the chosen
volume model. The hypothesis is geometric, and the conclusion includes
both the correct decoded source and its squared norm bound. -/
theorem n07b_exists_sourceLift_of_M_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hV : IsVolumeModel T S K V)
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (f : S.Source) (b : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m x, x ∈ physicalPieceOpen S K z m →
      ∀ j : Fin (b + 1), ∀ i : n07bAngularChainIndex j.val,
        n07bSourceGeometricWeight T K z m x *
          n07bAngularChainCoefficient T K z m (3 / 4 : ℝ) j.val i x ^ 2 ≤ A * T.M x.1 ^ 2) :
    ∃ F : V.level (3 / 4 : ℝ) 0 b,
      ‖F‖ ^ 2 ≤ A * n07bSourcePathConstant b *
        physicalNorm T (3 / 4 : ℝ) (b + 1) ((S.height (3 / 4 : ℝ)).decode f.val) ^ 2 ∧
      ∀ m, (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode f.val) := by
  have hsum := n07b_sourceBound_energy_summable hT hS hK hz hs f b hA hcoeff
  obtain ⟨F, _, hforget, hnorm⟩ := n07b_exists_actualCanonicalSourceLift hD hT hS hV
    hK hz hs f (3 / 4 : ℝ) 0 b hsum.1
  exact ⟨F, hnorm.trans_le hsum.2, hforget⟩

end ContinuousFlexibility.Analysis
