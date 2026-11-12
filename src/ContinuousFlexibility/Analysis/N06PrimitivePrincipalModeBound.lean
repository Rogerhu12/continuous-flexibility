import ContinuousFlexibility.Analysis.N06PrimitivePrincipalSource
import ContinuousFlexibility.Analysis.N07aActualPrincipalBlock
import ContinuousFlexibility.Analysis.N07aModeEnergyNorm
import ContinuousFlexibility.Analysis.N07aAngularBlockWeights

/-!
# Actual principal blocks with the reference mode energy inserted

Both affine factors are retained: the cubic principal factor has the
sixth power of the actual interval length, and the L2 mode conversion
has its square root.  The resulting material envelope is subpower and
independent of the input and current state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory Statements CanonicalGeometry

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
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b base loss : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}

local instance n06ModeBoundLevelGroup : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _
local instance n06ModeBoundLevelSpace : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance n06ModeBoundUnknownGroup : NormedAddCommGroup (CanonicalUnknown S K) :=
  inferInstance
local instance n06ModeBoundUnknownSpace : NormedSpace ℝ (CanonicalUnknown S K) :=
  inferInstance
local instance n06ModeBoundGraphGroup : NormedAddCommGroup B.Space :=
  Submodule.normedAddCommGroup _
local instance n06ModeBoundGraphSpace : NormedSpace ℝ B.Space :=
  Submodule.normedSpace _

private def n06ModeBoundEnvelope (T : MaterialData) (K : CanonicalData S)
    (A P Q B₀ : ℝ) (m : ℕ) : ℝ :=
  112 * (1 + (K.right m - K.left m)) ^ 6 * B₀ * T.E0 (T.sample (K.cell m)) ^ B₀ *
    Real.sqrt (n07aReferenceModeBudget A P Q (K.right m - K.left m)
      (T.E0 (T.sample (K.cell m)))) * Real.sqrt (Real.pi * (K.right m - K.left m))

private theorem n06_modeBound_sample_pos
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (m : ℕ) :
    0 < T.E0 (T.sample (K.cell m)) ∧ 0 < T.H (T.sample (K.cell m)) := by
  have hs := materialSample_mem_radialCore hT hD.choose_spec.2.1 (K.cell m)
  have hp := hT.2.1 _ hs
  exact ⟨hp.2.2.1, hp.2.1⟩

private theorem n06_modeBound_envelope_nonneg
    (A P Q B₀ : ℝ) (m : ℕ) (hB₀ : 0 ≤ B₀)
    (hE : 0 < T.E0 (T.sample (K.cell m))) :
    0 ≤ n06ModeBoundEnvelope T K A P Q B₀ m := by
  unfold n06ModeBoundEnvelope
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      hB₀) (Real.rpow_pos_of_pos hE B₀).le) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

private theorem n06_modeBound_from_energy
    {m : ℕ} (hlen : K.left m < K.right m)
    (d s j l : ℕ) (A P Q B₀ : ℝ) (z : Parameter S)
    (hB₀ : 0 ≤ B₀) (hE : 0 < T.E0 (T.sample (K.cell m)))
    (hH : 0 < T.H (T.sample (K.cell m)))
    (u ur urr G v : CanonicalL2 S K m) (hv : n07aAngularReflection m v = v)
    (hen : Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
        (n07aCanonicalUnitMode hlen u j) (n07aCanonicalUnitMode hlen ur j)
        (n07aCanonicalUnitMode hlen urr j)) ≤
      Real.sqrt (n07aReferenceModeBudget A P Q (K.right m - K.left m)
        (T.E0 (T.sample (K.cell m)))) * (‖u‖ + ‖G‖))
    (hbl : ‖((1 + |(((j : ℤ) - l : ℤ) : ℝ)|) ^ s) •
        n07aCanonicalUnitMode hlen v l‖ ≤
      112 * (1 + (K.right m - K.left m)) ^ 6 *
        n07aDifferenceBlockBudget T S K d s B₀ z m * n07aAngularTail ((j : ℤ) - l) *
          Real.sqrt (n07aScaledModeEnergy (K.right m - K.left m) (2 * (j : ℝ))
            (n07aCanonicalUnitMode hlen u j) (n07aCanonicalUnitMode hlen ur j)
            (n07aCanonicalUnitMode hlen urr j))) :
    n07aAngularGap j l ^ s * ‖n07aAngularBand m hlen l v‖ ≤
      n06ModeBoundEnvelope T K A P Q B₀ m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
        parameterGrading S (s + 4 + d) z * n07aAngularTail ((j : ℤ) - l) *
          (‖u‖ + ‖G‖) := by
  have hg : 0 ≤ n07aAngularGap j l ^ s :=
    pow_nonneg (zero_le_one.trans (n07aAngularGap_one_le j l)) s
  rw [norm_smul, Real.norm_eq_abs] at hbl
  simp only [← n07aAngularGap_eq_int, abs_of_nonneg hg] at hbl
  have hρ : 0 ≤ parameterGrading S (s + 4 + d) z := apply_nonneg _ _
  have hbudget : 0 ≤ n07aDifferenceBlockBudget T S K d s B₀ z m := by
    unfold n07aDifferenceBlockBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg hB₀
      (Real.rpow_pos_of_pos hE B₀).le)
      (Real.rpow_pos_of_pos hH (3 / 4 : ℝ)).le) hρ
  have hpref : 0 ≤ 112 * (1 + (K.right m - K.left m)) ^ 6 *
      n07aDifferenceBlockBudget T S K d s B₀ z m * n07aAngularTail ((j : ℤ) - l) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hbudget)
      (n07aAngularTail_nonneg _)
  calc
    _ = Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (n07aAngularGap j l ^ s * ‖n07aCanonicalUnitMode hlen v l‖) := by
      rw [n07aAngularBand_norm_unitMode hlen v hv l]
      ring
    _ ≤ Real.sqrt (Real.pi * (K.right m - K.left m)) *
        (112 * (1 + (K.right m - K.left m)) ^ 6 *
          n07aDifferenceBlockBudget T S K d s B₀ z m * n07aAngularTail ((j : ℤ) - l) *
            (Real.sqrt (n07aReferenceModeBudget A P Q (K.right m - K.left m)
              (T.E0 (T.sample (K.cell m)))) * (‖u‖ + ‖G‖))) :=
      mul_le_mul_of_nonneg_left
        (hbl.trans (mul_le_mul_of_nonneg_left hen hpref)) (Real.sqrt_nonneg _)
    _ = _ := by
      dsimp only [n06ModeBoundEnvelope, n07aDifferenceBlockBudget]
      ring

theorem n06_primitivePrincipal_mode_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (h05 : N05Properties D T S C K V b B)
    (href : ReferenceJets D T S C L K)
    (hcur : CurrentJets D T S C L K base ε)
    (hprincipal : ReferencePrincipal T S C K)
    (hI : ∀ m, K.left m < K.right m) (J : N06PrimitiveReferenceJetFamily B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
      ∀ z (hz : z ∈ sectorNeighborhood S base ε ε)
        (F : V.level (3 / 4 : ℝ) 0 b) m, K.positive m = true → ∀ j l : ℕ,
        n07aAngularBand m (hI m) j (n07aReferenceInverseField (B := B) F m) =
          n07aReferenceInverseField (B := B) F m →
        n07aAngularGap j l ^ s *
          ‖n07aAngularBand m (hI m) l
            (n06PrimitivePrincipalSource href hcur hI J z hz F m)‖ ≤
        e m * T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
          parameterGrading S (s + 4 + d) z * n07aAngularTail ((j : ℤ) - l) *
            (‖n07aReferenceInverseField (B := B) F m‖ +
              ‖n07aReferenceCanonicalRhs href m (hI m) (B.inverse F).val.1
                (V.forget (3 / 4 : ℝ) 0 b F)‖) := by
  have hD : IsAccumulatingProfile D := h01.1.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample (K.cell m)) :=
    (n06_modeBound_sample_pos (K := K) hD hT m).1
  have hH (m : ℕ) : 0 < T.H (T.sample (K.cell m)) :=
    (n06_modeBound_sample_pos (K := K) hD hT m).2
  obtain ⟨A, P, Q, hA, hP, hQ, henergy⟩ :=
    n07a_reference_actualMode_root_bound href hprincipal hE hI
  obtain ⟨d, hblocks⟩ := n07a_actualPrincipal_block_bound h01 h04 href hcur
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B₀, hB₀, hblock⟩ := hblocks s
  have he : N07aSampleSubpower T K (n06ModeBoundEnvelope T K A P Q B₀) :=
    n07a_principalModeEnvelope_subpower hD hT href A P Q B₀
  refine ⟨n06ModeBoundEnvelope T K A P Q B₀, he,
    fun m => n06_modeBound_envelope_nonneg A P Q B₀ m hB₀.le (hE m), ?_⟩
  intro z hz F m hm j l hband
  let u : CanonicalL2 S K m := n07aReferenceInverseField (B := B) F m
  let G : CanonicalL2 S K m := n07aReferenceCanonicalRhs href m (hI m)
    (B.inverse F).val.1 (V.forget (3 / 4 : ℝ) 0 b F)
  let jets : N06PrimitivePositiveJets u := J F m hm
  let v : CanonicalL2 S K m := n06PrimitivePrincipalSource href hcur hI J z hz F m
  have hu : n07aAngularReflection m u = u := n06_primitiveReferenceInverse_reflection h05 F m
  have hv : n07aAngularReflection m v = v :=
    n06PrimitivePrincipalSource_reflection hT hS h01 h03 h04 h05 href hcur hI J z hz F m
  have heq : N07aCanonicalDistributionEquation S K m
      (K.coefficients (C.referenceState, 0) m) u G :=
    n06_primitiveReferenceInverse_positive_distribution hS h01 h03 h04 h05 href F m hm
  have hen := henergy m hm u jets.radial jets.secondRadial G
    jets.radial_weak jets.secondRadial_weak heq j
  have hbl := hblock z hz m hm (hI m) u jets.radial jets.angular jets.secondRadial
    jets.radialAngular jets.angularAngular hu j l hband jets.radial_weak
    jets.angular_weak jets.secondRadial_weak jets.radialAngular_weak
    jets.angularAngular_weak false
  have hvdef : v = n07aRelativePrincipalJet href hcur z hz m (hI m)
      jets.radial jets.angular jets.secondRadial jets.radialAngular jets.angularAngular :=
    n06PrimitivePrincipalSource_positive href hcur hI J z hz F m hm
  rw [← hvdef] at hbl
  simp only [Bool.false_eq_true, ite_false, mul_one] at hbl
  exact n06_modeBound_from_energy (hI m) d s j l A P Q B₀ z hB₀.le (hE m) (hH m)
    u jets.radial jets.secondRadial G v hv hen hbl

end ContinuousFlexibility.Analysis
