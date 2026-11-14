module

public import ContinuousFlexibility.Analysis.N07aBaseInverse

/-!
# Regularity already supplied by the actual base inverse

At the base level the Neumann estimate and the reference inverse bounds
control the actual canonical field, its three scalars, and one weak radial
derivative. No higher regularity of the corrected source is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {b : ℕ} {B : CanonicalDomainData S K V b}

-- Retain the inherited normed structures without repeatedly searching the
-- nested sequence and graph subtypes.
local instance : NormedAddCommGroup (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedAddCommGroup _

local instance : NormedSpace ℝ (V.level (3 / 4 : ℝ) 0 b) :=
  Submodule.normedSpace _

local instance : NormedAddCommGroup (CanonicalUnknown S K) := inferInstance

local instance : NormedSpace ℝ (CanonicalUnknown S K) := inferInstance

local instance : NormedAddCommGroup B.Space := Submodule.normedAddCommGroup _

local instance : NormedSpace ℝ B.Space := Submodule.normedSpace _

private theorem n07a_reference_regular
    (h05 : N05Properties D T S C K V b B) (t : ℝ) (s : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ Q : V.level (3 / 4 : ℝ) t s,
      ∃ W : V.level (3 / 4 : ℝ) (t - B.lossMaterial) s,
        V.forget (3 / 4 : ℝ) (t - B.lossMaterial) s W =
          (fun m => (B.globalInverse (V.forget (3 / 4 : ℝ) t s Q)).1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K
          (B.globalInverse (V.forget (3 / 4 : ℝ) t s Q)) ≤ C0 * ‖Q‖ :=
  h05.2.2.2.2.2.2.2.2.2.2.2.2.1 t s

private theorem n07a_inverse_apply_le
    {L : ReturnCorrectionData S} {P : RelativeInverseData S K V b B}
    {base : ℕ} {ε : ℝ}
    (h06 : N06Properties D S C K L V b B P base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hsector : stateSector S z.1) (F : V.level (3 / 4 : ℝ) 0 b) :
    ‖P.inverse z F‖ ≤ 2 * ‖F‖ :=
  ((P.inverse z).le_opNorm F).trans
    (mul_le_mul_of_nonneg_right (h06.2 z hz hsector).2.2.2.2.2 (norm_nonneg F))

/-- The actual base solution has all base angular derivatives, with a
uniform bound for its field and scalar components. -/
theorem n07a_baseSolution_baseRegularity
    {L : ReturnCorrectionData S} {P : RelativeInverseData S K V b B}
    {base : ℕ} {ε : ℝ}
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ z ∈ stateNeighborhood S C base ε,
      stateSector S z.1 → ∀ F : V.level (3 / 4 : ℝ) 0 b,
      ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) b,
        V.forget (3 / 4 : ℝ) (-B.lossMaterial) b W =
          (fun m => (n07aBaseInverse B P z F).val.1.1 m) ∧
        ‖W‖ + canonicalUnknownScalars S K (n07aBaseInverse B P z F).val.1 ≤
          C0 * ‖F‖ := by
  have h := n07a_reference_regular h05 (0 : ℝ) b
  rw [zero_sub] at h
  obtain ⟨C0, hC0, hbound⟩ := h
  refine ⟨2 * C0, mul_pos (by norm_num) hC0, ?_⟩
  intro z hz hsector F
  obtain ⟨W, hW, hnorm⟩ := hbound (P.inverse z F)
  refine ⟨W, ?_, ?_⟩
  · rw [n07aBaseInverse_global h05]
    exact hW
  rw [n07aBaseInverse_global h05]
  calc
    _ ≤ C0 * ‖P.inverse z F‖ := hnorm
    _ ≤ C0 * (2 * ‖F‖) :=
      mul_le_mul_of_nonneg_left (n07a_inverse_apply_le h06 hz hsector F) hC0.le
    _ = (2 * C0) * ‖F‖ := by ring

/-- N05's first-normal estimate gives an actual weak radial derivative
of the base solution, retaining `b - 1` angular derivatives. -/
theorem n07a_baseSolution_firstNormal
    {L : ReturnCorrectionData S} {P : RelativeInverseData S K V b B}
    {base : ℕ} {ε : ℝ}
    (h05 : N05Properties D T S C K V b B)
    (h06 : N06Properties D S C K L V b B P base ε) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ z ∈ stateNeighborhood S C base ε,
      stateSector S z.1 → ∀ F : V.level (3 / 4 : ℝ) 0 b,
      ∃ W : V.level (3 / 4 : ℝ) (-B.lossMaterial) (b - 1),
        (∀ m φ, CanonicalTest S K m φ →
          (∫ p, V.forget (3 / 4 : ℝ) (-B.lossMaterial) (b - 1) W m p * φ p
            ∂canonicalMeasure S K m) =
          -(∫ p, (n07aBaseInverse B P z F).val.1.1 m p *
            mixedDerivative 1 0 φ p ∂canonicalMeasure S K m)) ∧
        ‖W‖ ≤ C0 * ‖F‖ := by
  cases b with
  | zero => have := h05.1; omega
  | succ n =>
    have h := h05.2.2.2.2.2.2.2.2.2.2.2.2.2 (0 : ℝ) n
    rw [zero_sub] at h
    obtain ⟨C0, hC0, hbound⟩ := h
    refine ⟨2 * C0, mul_pos (by norm_num) hC0, ?_⟩
    intro z hz hsector F
    obtain ⟨W, hW, hnorm⟩ := hbound (P.inverse z F)
    refine ⟨W, ?_, ?_⟩
    · intro m φ hφ
      rw [n07aBaseInverse_global h05]
      exact hW m φ hφ
    · calc
        _ ≤ C0 * ‖P.inverse z F‖ := hnorm
        _ ≤ C0 * (2 * ‖F‖) :=
          mul_le_mul_of_nonneg_left (n07a_inverse_apply_le h06 hz hsector F) hC0.le
        _ = (2 * C0) * ‖F‖ := by ring

end ContinuousFlexibility.Analysis
