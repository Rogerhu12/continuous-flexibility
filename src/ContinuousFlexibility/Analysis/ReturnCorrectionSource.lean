import ContinuousFlexibility.Analysis.ReturnCorrectionCoefficients
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Realizing the return error in the physical source space

The source is the existing kernel of the physical compatibility
functional. Its decoder is injective, and its range is exactly the
weighted height fields with zero physical integral. Consequently an
actual linear or bilinear scalar error field has a unique lift to the
source once its membership and compatibility have been proved.

The constructions use mathlib's `LinearMap.codRestrictOfInjective` and
`LinearMap.codRestrict₂`; no new completion or source representation is
introduced. The last lemmas expose the exact physical-norm criterion
for bounds on the lifted maps.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

/-- The existing height decoder restricted to the existing source
kernel. -/
def physicalSourceDecode (S : PhysicalSpacesData) : S.Source →ₗ[ℝ] (PolarPoint → ℝ) :=
  (S.height (3 / 4 : ℝ)).decode.comp S.Q.toLinearMap.ker.subtype

theorem physicalSourceDecode_apply (S : PhysicalSpacesData) (f : S.Source) :
    physicalSourceDecode S f = (S.height (3 / 4 : ℝ)).decode f.val := by
  simp only [physicalSourceDecode, LinearMap.comp_apply, Submodule.subtype_apply]

theorem physicalSourceDecode_injective
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) : Function.Injective (physicalSourceDecode S) := by
  obtain ⟨_, _, _, _, _, hinj, _⟩ := hS.1 (3 / 4 : ℝ)
  intro f g hfg
  apply Subtype.ext
  apply hinj
  simpa only [physicalSourceDecode_apply] using hfg

/-- Exact range of the source decoder. Both directions use the actual
`IsSobolevModel` realization and the actual compatibility functional. -/
theorem physicalSourceDecode_mem_range_iff
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ) :
    f ∈ LinearMap.range (physicalSourceDecode S) ↔
      HeightMember D T (3 / 4 : ℝ) f ∧ physicalSourceIntegral D f = 0 := by
  obtain ⟨_, _, _, hmember, hrealize, _⟩ := hS.1 (3 / 4 : ℝ)
  constructor
  · rintro ⟨u, rfl⟩
    rw [physicalSourceDecode_apply]
    exact ⟨hmember u.val, physicalSourceIntegral_decode_source_eq_zero hS u⟩
  · rintro ⟨hf, hzero⟩
    obtain ⟨u, hu⟩ := hrealize f hf
    obtain ⟨_, _, _, _, _, _, _, hQ, _⟩ := hS
    have huQ : S.Q u = 0 := by
      rw [hQ, hu]
      exact hzero
    refine ⟨⟨u, LinearMap.mem_ker.mpr huQ⟩, ?_⟩
    rw [physicalSourceDecode_apply]
    exact hu

/-- The source grading is the maximum of the first coordinate norms,
so a bound is equivalent to the corresponding finite collection of
physical Sobolev bounds. -/
theorem sourceGrading_le_iff_physicalNorm
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hS : IsPhysicalSpaces D T S) (n : ℕ) (f : S.Source) {c : ℝ} (hc : 0 ≤ c) :
    S.sourceGrading n f ≤ c ↔
      ∀ i ≤ n, physicalNorm T (3 / 4 : ℝ) i (physicalSourceDecode S f) ≤ c := by
  obtain ⟨_, _, _, _, _, _, _, hnorm⟩ := hS.1 (3 / 4 : ℝ)
  simpa only [PhysicalSpacesData.sourceGrading, Seminorm.comp_apply, Submodule.subtype_apply,
    SobolevModelData.grading, physicalSourceDecode_apply, hnorm] using
      gradedSeminorm_le_iff (fun i => (S.height (3 / 4 : ℝ)).level i)
        (S.height (3 / 4 : ℝ)).bond n f.val hc

section LinearLift

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]
variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Lift an actual scalar linear field to the existing physical source. -/
def liftPhysicalSourceLinear (hS : IsPhysicalSpaces D T S)
    (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ x, HeightMember D T (3 / 4 : ℝ) (F x))
    (hzero : ∀ x, physicalSourceIntegral D (F x) = 0) : E →ₗ[ℝ] S.Source :=
  LinearMap.codRestrictOfInjective F (physicalSourceDecode S)
    (physicalSourceDecode_injective hS)
    (fun x => (physicalSourceDecode_mem_range_iff hS (F x)).mpr ⟨hF x, hzero x⟩)

theorem liftPhysicalSourceLinear_decode (hS : IsPhysicalSpaces D T S)
    (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ x, HeightMember D T (3 / 4 : ℝ) (F x))
    (hzero : ∀ x, physicalSourceIntegral D (F x) = 0) (x : E) :
    physicalSourceDecode S (liftPhysicalSourceLinear hS F hF hzero x) = F x := by
  exact LinearMap.codRestrictOfInjective_comp_apply F (physicalSourceDecode S)
    (physicalSourceDecode_injective hS)
    (fun y => (physicalSourceDecode_mem_range_iff hS (F y)).mpr ⟨hF y, hzero y⟩) x

theorem liftPhysicalSourceLinear_unique (hS : IsPhysicalSpaces D T S)
    (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ x, HeightMember D T (3 / 4 : ℝ) (F x))
    (hzero : ∀ x, physicalSourceIntegral D (F x) = 0)
    (L : E →ₗ[ℝ] S.Source) (hL : ∀ x, physicalSourceDecode S (L x) = F x) :
    L = liftPhysicalSourceLinear hS F hF hzero := by
  apply LinearMap.ext
  intro x
  apply physicalSourceDecode_injective hS
  rw [hL, liftPhysicalSourceLinear_decode]

theorem liftPhysicalSourceLinear_grading_le_iff (hS : IsPhysicalSpaces D T S)
    (F : E →ₗ[ℝ] (PolarPoint → ℝ))
    (hF : ∀ x, HeightMember D T (3 / 4 : ℝ) (F x))
    (hzero : ∀ x, physicalSourceIntegral D (F x) = 0)
    (n : ℕ) (x : E) {c : ℝ} (hc : 0 ≤ c) :
    S.sourceGrading n (liftPhysicalSourceLinear hS F hF hzero x) ≤ c ↔
      ∀ i ≤ n, physicalNorm T (3 / 4 : ℝ) i (F x) ≤ c := by
  rw [sourceGrading_le_iff_physicalNorm hS n _ hc, liftPhysicalSourceLinear_decode]

end LinearLift

section BilinearLift

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Lift an explicitly bilinear scalar error field. The analytic
membership and compatibility proofs are required for every pair of
independent residual and increment arguments. -/
def liftPhysicalSourceBilinear (hS : IsPhysicalSpaces D T S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ x y, HeightMember D T (3 / 4 : ℝ) (B x y))
    (hzero : ∀ x y, physicalSourceIntegral D (B x y) = 0) :
    E →ₗ[ℝ] F →ₗ[ℝ] S.Source :=
  LinearMap.codRestrict₂ B (physicalSourceDecode S) (physicalSourceDecode_injective hS)
    (fun x y => (physicalSourceDecode_mem_range_iff hS (B x y)).mpr ⟨hB x y, hzero x y⟩)

theorem liftPhysicalSourceBilinear_decode (hS : IsPhysicalSpaces D T S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ x y, HeightMember D T (3 / 4 : ℝ) (B x y))
    (hzero : ∀ x y, physicalSourceIntegral D (B x y) = 0) (x : E) (y : F) :
    physicalSourceDecode S (liftPhysicalSourceBilinear hS B hB hzero x y) = B x y := by
  exact LinearMap.codRestrict₂_apply B (physicalSourceDecode S) (physicalSourceDecode_injective hS)
    (fun z w => (physicalSourceDecode_mem_range_iff hS (B z w)).mpr ⟨hB z w, hzero z w⟩) x y

theorem liftPhysicalSourceBilinear_unique (hS : IsPhysicalSpaces D T S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ x y, HeightMember D T (3 / 4 : ℝ) (B x y))
    (hzero : ∀ x y, physicalSourceIntegral D (B x y) = 0)
    (L : E →ₗ[ℝ] F →ₗ[ℝ] S.Source)
    (hL : ∀ x y, physicalSourceDecode S (L x y) = B x y) :
    L = liftPhysicalSourceBilinear hS B hB hzero := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply physicalSourceDecode_injective hS
  rw [hL, liftPhysicalSourceBilinear_decode]

theorem liftPhysicalSourceBilinear_grading_le_iff (hS : IsPhysicalSpaces D T S)
    (B : E →ₗ[ℝ] F →ₗ[ℝ] (PolarPoint → ℝ))
    (hB : ∀ x y, HeightMember D T (3 / 4 : ℝ) (B x y))
    (hzero : ∀ x y, physicalSourceIntegral D (B x y) = 0)
    (n : ℕ) (x : E) (y : F) {c : ℝ} (hc : 0 ≤ c) :
    S.sourceGrading n (liftPhysicalSourceBilinear hS B hB hzero x y) ≤ c ↔
      ∀ i ≤ n, physicalNorm T (3 / 4 : ℝ) i (B x y) ≤ c := by
  rw [sourceGrading_le_iff_physicalNorm hS n _ hc, liftPhysicalSourceBilinear_decode]

end BilinearLift

end ContinuousFlexibility.Statements
