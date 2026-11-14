module

public import ContinuousFlexibility.Radial.FixedCentralModelChart
public import ContinuousFlexibility.Radial.InnerCentralFlux
public import ContinuousFlexibility.Radial.InnerCentralCapScale
public import ContinuousFlexibility.Radial.InnerModelFluxError

/-!
# Small conormal errors for the fixed original central column

The full inverse is fixed before the common model radius.  The radius
then simultaneously satisfies the original R09 compression hypothesis,
absorbs the true density drift, and makes the actual two-cut errors small.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real ContinuousFlexibility.Statements
open scoped Matrix.Norms.L2Operator

def fixedCentralModelCutEnergy {B : FixedCentralBorder} {q : ℕ} {T B₀ C K : ℝ}
    (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K) (i : Fin 2) : ℝ :=
  (M.column i).inwardEnergy + bufferSign i * centralRadiusA

def fixedCentralModelPhysicalKappa {B : FixedCentralBorder} {q : ℕ} {T B₀ C K : ℝ}
    (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K) : Fin 2 → ℝ :=
  innerPhysicalCutKappa 1
    (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))
    (fixedCentralModelCutEnergy M)

theorem fixedCentralModelCutEnergy_bounds {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hC : 0 < C)
    (hfar : 2 * C * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T)
    (i : Fin 2) :
    0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i := by
  have hm : 2 * centralRadiusA ≤ centralBufferMass (2 * (q : ℝ)) T / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hfar]
  have hα : 2 * centralRadiusA ≤ (M.column i).inwardEnergy :=
    hm.trans (M.column i).inward_lower
  have hd := innerCentral_drift_bounds i hα
  exact ⟨hd.1, by
    dsimp only [fixedCentralModelCutEnergy]
    linarith only [hd.2.1]⟩

theorem fixedCentralModelPhysicalKappa_pos {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hk : ∀ i, 0 < fixedCentralModelCutEnergy M i) (i : Fin 2) :
    0 < fixedCentralModelPhysicalKappa M i := by
  exact mul_pos (mul_pos zero_lt_one (sq_pos_of_pos (centralDensityRoot_pos _))) (hk i)

theorem fixedCentralModel_error_bound {B : FixedCentralBorder} {q : ℕ}
    {T B₀ C K : ℝ} (hB : BufferHypotheses (B.modelBuffer q T B₀))
    (M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K)
    (hC : 0 < C)
    (he : ∀ i, 0 < fixedCentralModelCutEnergy M i ∧
      (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i)
    (sign : Bool) :
    ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M) (fun _ => 1)
      (M.physicalFluxError 1
        (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
      (8 * C * (1 + C ^ 2)) *
        (B₀ * centralBufferMass (2 * (q : ℝ)) T ^ 2 *
          exp (-centralBufferAction (2 * (q : ℝ)) T)) := by
  have hr := M.physical_error_weighted_bound hB hC 1
    (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))
    (fixedCentralModelCutEnergy M) (fun _ => 1) zero_lt_one
    (fun _ => centralDensityRoot_pos _) (fun i => (he i).1)
    (fun _ => zero_lt_one) (fun i => (he i).2)
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ _ => by norm_num)
    (fun _ => le_refl (centralBufferMass (2 * (q : ℝ)) T))
    (fun _ => le_refl (centralBufferAction (2 * (q : ℝ)) T)) sign
  have ht : 0 < centralBufferAction (2 * (q : ℝ)) T := buffer_action_pos hB 0
  have hx : exp (-2 * centralBufferAction (2 * (q : ℝ)) T) ≤
      exp (-centralBufferAction (2 * (q : ℝ)) T) :=
    exp_le_exp.mpr (by linarith only [ht])
  have hc : 0 ≤ (8 * C * (1 + C ^ 2)) *
      (B₀ * centralBufferMass (2 * (q : ℝ)) T ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg hB.2.2.1.le (sq_nonneg _))
  calc
    _ ≤ 4 * 1 * ((2 * (1 + C ^ 2)) *
        (C * B₀ * centralBufferMass (2 * (q : ℝ)) T ^ 2 *
          exp (-2 * centralBufferAction (2 * (q : ℝ)) T))) := hr
    _ = ((8 * C * (1 + C ^ 2)) *
        (B₀ * centralBufferMass (2 * (q : ℝ)) T ^ 2)) *
          exp (-2 * centralBufferAction (2 * (q : ℝ)) T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx hc
    _ = _ := by ring

/-- One actual fixed-column model family, with no dependence on the
subsequently chosen reference geometry or retained-cone length. -/
theorem FixedCentralBorder.exists_small_error_model_buffers
    (B : FixedCentralBorder) (hR09 : R09Statement) (Tmin : ℝ) :
    ∃ C K B₀ T : ℝ, 0 < C ∧ 0 < K ∧ 0 < B₀ ∧ 8 ≤ T ∧ Tmin ≤ T ∧
      sqrt centralOscillatorA + 2 ≤ T ∧
      (∀ j : ℝ, 2 ≤ j → 2 * C * centralRadiusA ≤ centralBufferMass j T) ∧
      ∀ q : ℕ, 1 ≤ q →
        BufferHypotheses (B.modelBuffer q T B₀) ∧
        ∃ M : InnerBufferLocalizedData (B.modelBuffer q T B₀) C K,
          (∀ i, 0 < fixedCentralModelCutEnergy M i ∧
            (M.column i).inwardEnergy ≤ 2 * fixedCentralModelCutEnergy M i) ∧
          ∀ sign : Bool,
            ‖innerTwoCutWeightedError (fixedCentralModelPhysicalKappa M) (fun _ => 1)
              (M.physicalFluxError 1
                (fun i => centralDensityRoot (bufferCut (B.modelBuffer q T B₀) i))) sign‖ ≤
              (1 : ℝ) / 8 := by
  obtain ⟨C, ε, hC, hε, hcompress⟩ := hR09 64 (by norm_num)
  obtain ⟨K, hK, hlocal⟩ := exists_innerBufferLocalizedData
  let F : ℝ := 8 * C * (1 + C ^ 2)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  let δ : ℝ := (1 / 8 : ℝ) / (1 + F)
  have hδ : 0 < δ := div_pos (by norm_num) (by linarith only [hF])
  obtain ⟨B₀, T, hB₀, hT, hmin, hmodels⟩ :=
    exists_actualCentralModelBuffers (by norm_num : (0 : ℝ) < 1)
      B.column_smooth B.column_compact B.column_positive
      (by rw [B.column_pairing]; norm_num)
      (max Tmin (max (sqrt centralOscillatorA + 2) (4 * C * centralRadiusA)))
      (lt_min hε hδ)
  have hcap : sqrt centralOscillatorA + 2 ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hmin)
  have hfar : 4 * C * centralRadiusA ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmin)
  have hmass (j : ℝ) (hj : 2 ≤ j) :
      2 * C * centralRadiusA ≤ centralBufferMass j T := by
    exact innerCentral_far_cut_mass hj (by linarith only [hT]) hfar
  refine ⟨C, K, B₀, T, hC, hK, hB₀, hT, (le_max_left _ _).trans hmin,
    hcap, hmass, ?_⟩
  intro q hq
  obtain ⟨hB, hsmall⟩ := hmodels q hq
  have hcomp : BufferCompressionConclusion (B.modelBuffer q T B₀) C :=
    hcompress _ (by exact le_rfl) hB
      (fun i => (hsmall i).trans_le (min_le_left ε δ))
  obtain ⟨M⟩ := hlocal _ C hB hcomp
  have hj : (2 : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * q)
  have he := fun i => fixedCentralModelCutEnergy_bounds M hC (hmass _ hj) i
  refine ⟨hB, M, he, ?_⟩
  intro sign
  apply (fixedCentralModel_error_bound hB M hC he sign).trans
  have hs : B₀ * centralBufferMass (2 * (q : ℝ)) T ^ 2 *
      exp (-centralBufferAction (2 * (q : ℝ)) T) ≤ δ :=
    ((hsmall 0).trans_le (min_le_right ε δ)).le
  have hFδ : F * δ ≤ (1 : ℝ) / 8 := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith only [hF] : 0 < 1 + F)).mpr
    nlinarith only [hF]
  exact (mul_le_mul_of_nonneg_left hs hF).trans hFδ

end ContinuousFlexibility.Radial
