module

public import ContinuousFlexibility.Analysis.N05CanonicalTestDensity
public import ContinuousFlexibility.Analysis.SpacesCylinderEvenJets

/-!
# Closure of actual even canonical test functions

Reflection averaging preserves smoothness, periodicity and the actual
compact radial support of a canonical test. Its continuous L² action
therefore shows that the closure of the even tests is exactly the
reflection-fixed subspace, without a supplied density hypothesis.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

theorem n05CanonicalTest_even {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    CanonicalTest S K m (spacesCylinderEvenFunction φ) := by
  obtain ⟨J, hJ, hJI, hz⟩ := hφ.2.2
  refine ⟨spacesCylinderEvenFunction_contDiff hφ.1,
    spacesCylinderEvenFunction_periodic hφ.2.1, J, hJ, hJI, ?_⟩
  intro r hr θ
  simp only [spacesCylinderEvenFunction, hz r hr θ, hz r hr (Real.pi - θ),
    add_zero, mul_zero]

def n05CanonicalEvenProjection (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    CanonicalL2 S K m →L[ℝ] CanonicalL2 S K m :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ (CanonicalL2 S K m) +
    (n05CanonicalReflection S K m).toContinuousLinearMap)

theorem n05CanonicalEvenProjection_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) :
    n05CanonicalEvenProjection S K m u =
      (1 / 2 : ℝ) • (u + n05CanonicalReflection S K m u) := by
  simp only [n05CanonicalEvenProjection, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap]

theorem n05CanonicalEvenProjection_fixed (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) (hu : n05CanonicalReflection S K m u = u) :
    n05CanonicalEvenProjection S K m u = u := by
  rw [n05CanonicalEvenProjection_apply, hu, ← two_smul ℝ u, smul_smul]
  norm_num

theorem n05CanonicalEvenProjection_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) :
    ‖n05CanonicalEvenProjection S K m u‖ ≤ ‖u‖ := by
  rw [n05CanonicalEvenProjection_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * ‖u + n05CanonicalReflection S K m u‖ ≤
        (1 / 2 : ℝ) * (‖u‖ + ‖n05CanonicalReflection S K m u‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖u‖ := by rw [(n05CanonicalReflection S K m).norm_map]; ring

theorem n05CanonicalEvenProjection_ae (S : PhysicalSpacesData) (K : CanonicalData S)
    (m : ℕ) (u : CanonicalL2 S K m) :
    (n05CanonicalEvenProjection S K m u : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      spacesCylinderEvenFunction (u : PolarPoint → ℝ) := by
  rw [n05CanonicalEvenProjection_apply]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (u + n05CanonicalReflection S K m u),
    Lp.coeFn_add u (n05CanonicalReflection S K m u),
    n05CanonicalReflection_ae S K m u] with p hhalf hadd href
  rw [hhalf]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd]
  simp only [Pi.add_apply]
  simp only [spacesCylinderEvenFunction, href]

theorem n05CanonicalEvenProjection_testL2 {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {φ : PolarPoint → ℝ} (hφ : CanonicalTest S K m φ) :
    n05CanonicalEvenProjection S K m (n05CanonicalTestL2 hφ) =
      n05CanonicalTestL2 (n05CanonicalTest_even hφ) := by
  apply Lp.ext
  have ha := n05CanonicalTestL2_ae hφ
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [n05CanonicalEvenProjection_ae S K m (n05CanonicalTestL2 hφ),
    n05CanonicalTestL2_ae (n05CanonicalTest_even hφ), ha, hr] with p hp he hφp hφr
  change n05CanonicalTestL2 hφ (p.1, Real.pi - p.2) = φ (p.1, Real.pi - p.2) at hφr
  rw [hp, he]
  simp only [spacesCylinderEvenFunction, hφp, hφr]

def n05CanonicalEvenTestCarrier (S : PhysicalSpacesData) (K : CanonicalData S) (m : ℕ) :
    Set (CanonicalL2 S K m) :=
  {u | ∃ (φ : PolarPoint → ℝ) (hφ : CanonicalTest S K m φ),
    (∀ p : PolarPoint, φ (p.1, Real.pi - p.2) = φ p) ∧ n05CanonicalTestL2 hφ = u}

theorem n05CanonicalEvenTestCarrier_fixed (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    n05CanonicalEvenTestCarrier S K m ⊆
      {u : CanonicalL2 S K m | n05CanonicalReflection S K m u = u} := by
  rintro u ⟨φ, hφ, he, rfl⟩
  apply (n05CanonicalReflection_fixed_iff S K m _).mpr
  have ha := n05CanonicalTestL2_ae hφ
  have hr := (n05CanonicalReflection_measurePreserving S K m).quasiMeasurePreserving.ae_eq_comp ha
  filter_upwards [hr, ha] with p hp hq
  change n05CanonicalTestL2 hφ (p.1, Real.pi - p.2) = φ (p.1, Real.pi - p.2) at hp
  exact hp.trans ((he p).trans hq.symm)

theorem n05CanonicalEvenTest_mem_closure (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) (u : CanonicalL2 S K m)
    (hu : n05CanonicalReflection S K m u = u) :
    u ∈ closure (n05CanonicalEvenTestCarrier S K m) := by
  have hd := n05CanonicalTestSubmodule_dense S K m u
  have hp := mem_closure_image (n05CanonicalEvenProjection S K m).continuous.continuousAt hd
  rw [n05CanonicalEvenProjection_fixed S K m u hu] at hp
  apply closure_mono ?_ hp
  rintro w ⟨v, hv, rfl⟩
  rcases hv with ⟨φ, hφ, rfl⟩
  exact ⟨spacesCylinderEvenFunction φ, n05CanonicalTest_even hφ,
    spacesCylinderEvenFunction_reflection φ, (n05CanonicalEvenProjection_testL2 hφ).symm⟩

theorem n05CanonicalEvenTest_closure (S : PhysicalSpacesData)
    (K : CanonicalData S) (m : ℕ) :
    closure (n05CanonicalEvenTestCarrier S K m) =
      {u : CanonicalL2 S K m | n05CanonicalReflection S K m u = u} := by
  apply subset_antisymm
  · apply closure_minimal (n05CanonicalEvenTestCarrier_fixed S K m)
    exact isClosed_eq (n05CanonicalReflection S K m).continuous continuous_id
  · intro u hu
    exact n05CanonicalEvenTest_mem_closure S K m u hu

end ContinuousFlexibility.Statements

