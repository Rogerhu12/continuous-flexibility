import ContinuousFlexibility.Analysis.N06FourierCutLinearity
import ContinuousFlexibility.Analysis.N06ReferenceProjectionRepresentatives
import ContinuousFlexibility.Analysis.N06ReferenceGraphFourierProjection
import ContinuousFlexibility.Analysis.N06ReferenceFourierSources
import ContinuousFlexibility.Analysis.N06MaterialJetRows

/-!
# The two actual low-frequency reference columns are fixed by cutoff

The left column is the actual radial flux derivative and the nu column
is the original first cosine mode. Their volume representatives are fixed
in every stored jet by forget injectivity. Thus the source approximant
retaining all three columns is precisely a cutoff plus the unchanged
compatibility-column correction; that last column may have any spectrum.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis ContinuousFlexibility.Radial
open scoped BigOperators Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b base loss : ℕ} {ε : ℝ}

/-- A true periodic physical projection identity fixes its complete original
volume representative, rather than only an arbitrarily chosen zeroth row. -/
theorem n06VolumeFourierCut_fixed_referenceSource
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (v : V.level γ t b)
    (f : PolarPoint → ℝ) (hfp : Function.Periodic f (0, Real.pi))
    (hrep : ∀ m, (V.forget γ t b v m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m f)
    (N : ℕ) (hfix : referenceBasisProjection (Finset.range (N + 1)) f = f) :
    n06VolumeFourierCut hV γ t b N v = v := by
  have hv : v.val ∈ canonicalVolumeGraph S K b := by
    rw [← hV.1 γ t b]
    exact v.property
  apply hV.2.2.1 γ t b
  funext m
  rw [n06VolumeFourierCut_forget]
  apply Lp.ext
  have he := n06MaterialJetRow_reflection (T := T) γ t v.val hv m
  rw [n06MaterialJetRow_zero_eq_forget hV γ t b v m] at he
  have hcut := n06_controlledReferenceSource_fourierCut_ae h hcoordinates m
    (V.forget γ t b v m) he hfp (hrep m) N
  rw [hfix] at hcut
  exact hcut.trans (hrep m).symm

/-- The true left and nu columns, in their original volume level, are
unchanged once modes zero and one are retained. -/
theorem n06VolumeFourierCut_referenceLowModeColumns
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) (γ t : ℝ)
    (columns : Fin 3 → V.level γ t b)
    (hcolumns : ∀ i m, (V.forget γ t b (columns i) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
    (N : ℕ) (hN : 1 ≤ N) :
    n06VolumeFourierCut hV γ t b N (columns 0) = columns 0 ∧
      n06VolumeFourierCut hV γ t b N (columns 1) = columns 1 := by
  have h0 : 0 ∈ Finset.range (N + 1) := by simp
  have h1 : 1 ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hN)
  constructor
  · apply n06VolumeFourierCut_fixed_referenceSource h hcoordinates hV γ t (columns 0)
      (n06ReferenceScalarField D S 0) (n06_referenceScalarField_periodic hS 0)
      (hcolumns 0) N
    change referenceBasisProjection (Finset.range (N + 1))
      (n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)) =
        n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft)
    have he : n06ReferenceTestOperator D (n06ReferenceLeftField S.chiLeft) =
        fun p : PolarPoint => deriv (fun r => D.w r * deriv S.chiLeft r) p.1 :=
      funext (n06_referenceLeftColumn_formula D S.chiLeft)
    rw [he]
    exact n06_referenceBasisProjection_radial h0 _
  · apply n06VolumeFourierCut_fixed_referenceSource h hcoordinates hV γ t (columns 1)
      (n06ReferenceScalarField D S 1) (n06_referenceScalarField_periodic hS 1)
      (hcolumns 1) N
    exact referenceBasisProjection_column D h1

private theorem n06_threeColumn_cut_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (f s k c : E) (a mu ell : ℝ)
    (hs : P s = s) (hk : P k = k) :
    f + (-f + (a • s + mu • k + ell • c)) -
        P (-f + (a • s + mu • k + ell • c)) =
      P f + ell • (c - P c) := by
  rw [map_add, map_neg, map_add, map_add, map_smul, map_smul, map_smul, hs, hk,
    smul_sub]
  abel

/-- Exact equality of the all-three-column approximant and the actual
compatibility-corrected projected source used by the physical graph. -/
theorem n06ReferenceFourierSource_eq_compatibility
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hV : IsVolumeModel T S K V) (B : CanonicalDomainData S K V b)
    (columns : Fin 3 → V.level (3 / 4 : ℝ) 0 b)
    (hcolumns : ∀ i m, (V.forget (3 / 4 : ℝ) 0 b (columns i) m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        canonicalSource S K (C.referenceState, 0) m (n06ReferenceScalarField D S i))
    (N : ℕ) (hN : 1 ≤ N) (F : V.level (3 / 4 : ℝ) 0 b) :
    n06ReferenceFourierSource hV B columns N F =
      n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N F +
        (B.inverse F).val.1.2.2.2 •
          (columns 2 - n06VolumeFourierCut hV (3 / 4 : ℝ) 0 b N (columns 2)) := by
  have hfixed := n06VolumeFourierCut_referenceLowModeColumns hS h hcoordinates hV
    (3 / 4 : ℝ) 0 columns hcolumns N hN
  have he : n06ReferenceForcingMap B columns F =
      -F + ((B.inverse F).val.1.2.1 • columns 0 +
        (B.inverse F).val.1.2.2.1 • columns 1 +
        (B.inverse F).val.1.2.2.2 • columns 2) := by
    simp only [n06ReferenceForcingMap, add_apply, neg_apply,
      ContinuousLinearMap.id_apply, n06ScalarColumnOperator_apply]
  unfold n06ReferenceFourierSource
  rw [he]
  exact n06_threeColumn_cut_source (n06VolumeFourierCutMap hV (3 / 4 : ℝ) 0 b N)
    F (columns 0) (columns 1) (columns 2) (B.inverse F).val.1.2.1
    (B.inverse F).val.1.2.2.1 (B.inverse F).val.1.2.2.2 hfixed.1 hfixed.2

end ContinuousFlexibility.Statements
