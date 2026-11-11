import ContinuousFlexibility.Analysis.SpacesPhysicalShellSynthesis
import ContinuousFlexibility.Analysis.SpacesPhysicalRowEquiv
import ContinuousFlexibility.Analysis.SpacesPhysicalBandReconstruction
import ContinuousFlexibility.Analysis.SpacesPhysicalLocalizationInverse
import ContinuousFlexibility.Analysis.SpacesSequenceRetraction

/-!
# The physical model as an actual tame retract

The localized Fourier analysis and even packet synthesis reconstruct every
closed physical Hilbert level. The zero coordinate follows from the genuine
band sum and the radial partition of unity. Uniqueness of weak derivatives
then identifies all the weighted coordinates. Integer cells are reindexed
isometrically into the fixed natural-number cylinder model in the statement.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal BigOperators Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} (hT : IsMaterialData D T)

/-- Inside the original closed weak graph, the zero coordinate determines
every weighted derivative coordinate. -/
theorem spacesPhysicalLevel_eq_of_zero (s : ℕ) (u v : physicalJetClosedSubmodule hT s)
    (hzero : u.val (zeroJetIndex s) = v.val (zeroJetIndex s)) : u = v := by
  have hu : u.val ∈ physicalJetGraph T s := by
    rw [← physicalJetClosedSubmodule_carrier hT s]
    exact u.property
  have hv : v.val ∈ physicalJetGraph T s := by
    rw [← physicalJetClosedSubmodule_carrier hT s]
    exact v.property
  apply Subtype.ext
  apply PiLp.ext
  intro j
  obtain ⟨du, hdu, hwu⟩ := hu.2 j
  obtain ⟨dv, hdv, hwv⟩ := hv.2 j
  rw [hzero] at hdu
  have hd : du = dv := hasWeakMixedDerivative_unique hdu hdv
  rw [hd] at hwu
  exact Lp.ext (hwu.trans hwv.symm)

theorem spacesCylinderParity_physicalZero (u : PhysicalJetProjectiveLimit hT) :
    spacesCylinderParity 0 (physicalJetProjectiveZero hT u) = physicalJetProjectiveZero hT u := by
  have href := ((mem_physicalJetGraph_iff_normalized hT (u.val 0).val).mp
    (physicalJetProjective_mem_graph u 0)).1
  rw [← physicalJetProjectiveZero_apply hT u 0] at href
  rw [spacesCylinderParity_apply, pow_zero, one_smul, href, ← two_smul ℝ]
  simp only [smul_smul]
  norm_num

theorem spacesPhysicalSynthesisJetRows_analysis (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalSynthesisJetRows hT 0 0 0 0 (by omega) k (spacesPhysicalBandAnalysis hT k u) =
      spacesPhysicalBandAnalysis hT k u := by
  apply lp.ext
  funext n
  rw [spacesPhysicalSynthesisJetRows_apply]
  simp only [pow_zero, one_smul, spacesPhysicalBandAnalysis_apply]
  exact spacesPhysicalCellBand_comp_zero n (T.M (T.radius n)) (spaces_material_M_one_le hT n)
    k 0 0 (spacesPhysicalLocalizedJetFamily hT 0 0 0 u n)

/-- Nonnegative constants for the fixed-loss shell analysis estimate. -/
def spacesPhysicalAnalysisNNConstant (s : ℕ) : ℝ≥0 :=
  ⟨spacesPhysicalBandAnalysisConstant hT s, spacesPhysicalBandAnalysisConstant_nonneg hT s⟩

/-- Synthesis of the analyzed shells converges in each original closed level. -/
theorem spacesPhysicalShellSynthesis_analysis_summable (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    Summable (fun k : ℕ => spacesPhysicalShellSynthesis hT s k (spacesPhysicalBandAnalysis hT k u)) := by
  let E : ℕ → Type := fun n => physicalJetClosedSubmodule hT n
  let bond := physicalJetBond hT
  let A := fun k => (spacesPhysicalBandAnalysis hT k).toLinearMap
  let CA := spacesPhysicalAnalysisNNConstant hT
  have hA : ∀ (n k : ℕ) (x : ProjectiveLimit E bond),
      ‖Real.exp ((n : ℝ) * k) • A k x‖ ≤ CA n * gradedSeminorm E bond (n + 0) x := by
    intro n k x
    exact spacesPhysicalBandAnalysis_bound hT n k x
  let v := shellAnalysisMap (gradedSeminorm E bond) 0 A CA hA (withSeminorms_graded E bond) u
  have hP : ∀ n k b, ‖spacesPhysicalShellSynthesis hT n k b‖ ≤
      (spacesPhysicalShellSynthesisConstant hT n : ℝ) *
        Real.exp (((n + 0 : ℕ) : ℝ) * k) * ‖b‖ := by
    intro n k b
    simpa only [Nat.add_zero] using spacesPhysicalShellSynthesis_norm_le hT n k b
  have hs := summable_shellSynthesis E 0 (spacesPhysicalShellSynthesis hT)
    (spacesPhysicalShellSynthesisConstant hT) hP v s
  simp only [v, shellAnalysisMap_raw, A] at hs
  exact hs

/-- The zeroth jet is recovered by the actual cell Fourier series and the
identity `sum κₙ χₙ = 1`. -/
theorem spacesPhysicalShellSynthesis_analysis_zero_hasSum
    (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    HasSum (fun k : ℕ =>
      (spacesPhysicalShellSynthesis hT s k (spacesPhysicalBandAnalysis hT k u)).val (zeroJetIndex s))
      (physicalJetProjectiveZero hT u) := by
  have h := (spacesCylinderParity 0).hasSum
    ((spacesPhysicalEnvelopeSynthesis hT 0 0).hasSum (spacesPhysicalBandAnalysis_hasSum hT u))
  rw [spacesPhysicalEnvelopeSynthesis_localization, spacesCylinderParity_physicalZero] at h
  exact h.congr_fun fun k => by
    rw [spacesPhysicalShellSynthesis_zero, spacesPhysicalSynthesisJetRows_analysis]

/-- Norm convergence in the closed weak graph identifies all weighted jets,
not merely the zero-order class. -/
theorem spacesPhysicalShellSynthesis_analysis_hasSum (u : PhysicalJetProjectiveLimit hT) (s : ℕ) :
    HasSum (fun k : ℕ => spacesPhysicalShellSynthesis hT s k (spacesPhysicalBandAnalysis hT k u))
      (u.val s) := by
  have hs := spacesPhysicalShellSynthesis_analysis_summable hT u s
  have he : (∑' k : ℕ, spacesPhysicalShellSynthesis hT s k (spacesPhysicalBandAnalysis hT k u)) =
      u.val s := by
    apply spacesPhysicalLevel_eq_of_zero hT s
    let Q : physicalJetClosedSubmodule hT s →L[ℝ] CylinderL2 :=
      (physicalJetCoordinate s (zeroJetIndex s)).comp (physicalJetClosedSubmodule hT s).subtypeL
    have hsum := Q.hasSum hs.hasSum
    exact (hsum.unique (spacesPhysicalShellSynthesis_analysis_zero_hasSum hT u s)).trans
      (physicalJetProjectiveZero_apply hT u s)
  exact he ▸ hs.hasSum

/-- Analysis with values in exactly the Banach space fixed in W02. -/
def spacesPhysicalModelShellAnalysis (k : ℕ) : PhysicalJetProjectiveLimit hT →L[ℝ] PhysicalModelBanach :=
  spacesPhysicalRowsEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (spacesPhysicalBandAnalysis hT k)

theorem spacesPhysicalModelShellAnalysis_apply (k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalModelShellAnalysis hT k u = spacesPhysicalRowsEquiv (spacesPhysicalBandAnalysis hT k u) := by
  rw [spacesPhysicalModelShellAnalysis, ContinuousLinearMap.comp_apply]
  rfl

theorem spacesPhysicalModelShellAnalysis_bound (s k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    ‖Real.exp ((s : ℝ) * k) • spacesPhysicalModelShellAnalysis hT k u‖ ≤
      (spacesPhysicalAnalysisNNConstant hT s : ℝ) * spacesPhysicalGrading hT s u := by
  rw [spacesPhysicalModelShellAnalysis_apply, ← map_smul, spacesPhysicalRowsEquiv_norm]
  exact spacesPhysicalBandAnalysis_bound hT s k u

/-- Synthesis from the same fixed Banach model. -/
def spacesPhysicalModelShellSynthesis (s k : ℕ) :
    PhysicalModelBanach →L[ℝ] physicalJetClosedSubmodule hT s :=
  (spacesPhysicalShellSynthesis hT s k).comp
    spacesPhysicalRowsEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem spacesPhysicalModelShellSynthesis_apply (s k : ℕ) (v : PhysicalModelBanach) :
    spacesPhysicalModelShellSynthesis hT s k v =
      spacesPhysicalShellSynthesis hT s k (spacesPhysicalRowsEquiv.symm v) := by
  rw [spacesPhysicalModelShellSynthesis, ContinuousLinearMap.comp_apply]
  rfl

theorem spacesPhysicalModelShellSynthesis_bound (s k : ℕ) (v : PhysicalModelBanach) :
    ‖spacesPhysicalModelShellSynthesis hT s k v‖ ≤
      (spacesPhysicalShellSynthesisConstant hT s : ℝ) * Real.exp ((s : ℝ) * k) * ‖v‖ := by
  rw [spacesPhysicalModelShellSynthesis_apply]
  simpa only [spacesPhysicalRowsEquiv_symm_norm] using
    spacesPhysicalShellSynthesis_norm_le hT s k (spacesPhysicalRowsEquiv.symm v)

theorem spacesPhysicalModelShellSynthesis_compatible (s k : ℕ) (v : PhysicalModelBanach) :
    physicalJetBond hT s (spacesPhysicalModelShellSynthesis hT (s + 1) k v) =
      spacesPhysicalModelShellSynthesis hT s k v := by
  simp only [spacesPhysicalModelShellSynthesis_apply, spacesPhysicalShellSynthesis_compatible]

theorem spacesPhysicalModelShellSynthesis_analysis (s k : ℕ) (u : PhysicalJetProjectiveLimit hT) :
    spacesPhysicalModelShellSynthesis hT s k (spacesPhysicalModelShellAnalysis hT k u) =
      spacesPhysicalShellSynthesis hT s k (spacesPhysicalBandAnalysis hT k u) := by
  rw [spacesPhysicalModelShellSynthesis_apply, spacesPhysicalModelShellAnalysis_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The canonical physical scale is an actual tame retract of the fixed
exponentially decreasing sequence model, with analysis loss zero and
synthesis loss one. -/
theorem spacesPhysical_tameRetraction : TameRetraction (spacesPhysicalGrading hT) modelGrading := by
  apply tameRetraction_of_shells
    (fun n => physicalJetClosedSubmodule hT n) (physicalJetBond hT) 0 0
    (fun k => (spacesPhysicalModelShellAnalysis hT k).toLinearMap) (spacesPhysicalAnalysisNNConstant hT)
    (fun s k u => spacesPhysicalModelShellAnalysis_bound hT s k u)
    (spacesPhysicalModelShellSynthesis hT) (spacesPhysicalShellSynthesisConstant hT)
  · intro s k v
    simpa only [Nat.add_zero] using spacesPhysicalModelShellSynthesis_bound hT s k v
  · exact spacesPhysicalModelShellSynthesis_compatible hT
  · intro u s
    exact (spacesPhysicalShellSynthesis_analysis_hasSum hT u s).congr_fun
      (fun k => spacesPhysicalModelShellSynthesis_analysis hT s k u)

theorem canonicalSobolevModel_tameRetraction (γ : ℝ) :
    TameRetraction (canonicalSobolevModelData hT γ).grading modelGrading :=
  spacesPhysical_tameRetraction hT

end ContinuousFlexibility.Statements
