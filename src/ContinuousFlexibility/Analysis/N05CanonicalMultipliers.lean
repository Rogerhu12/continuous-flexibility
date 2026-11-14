module

public import ContinuousFlexibility.Analysis.N05CanonicalModel
public import ContinuousFlexibility.Analysis.N05CanonicalLpMaps

/-!
# Piecewise scalar multipliers on canonical angular jets

A bounded scalar on each piece multiplies every angular jet on that piece.
The weak derivative equations and evenness condition are preserved literally.
The zero-jet projection also gives a bounded map to the unweighted L² sequence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped ContDiff Topology

def n05CanonicalWeightedZeroCoordinate (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (m : ℕ) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) →ₗ[ℝ] CanonicalL2 S K m :=
  w m • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) 0).toLinearMap

theorem n05CanonicalWeightedZeroCoordinate_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (w : ℕ → ℝ) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    n05CanonicalWeightedZeroCoordinate S K s w m v = w m • v 0 := by
  simp only [n05CanonicalWeightedZeroCoordinate, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, PiLp.proj_apply]

theorem n05CanonicalWeightedZeroCoordinate_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ m, ‖w m‖ ≤ B) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    ‖n05CanonicalWeightedZeroCoordinate S K s w m v‖ ≤ B * ‖v‖ := by
  rw [n05CanonicalWeightedZeroCoordinate_apply, norm_smul]
  exact mul_le_mul (hw m) (PiLp.norm_apply_le v 0) (norm_nonneg _) hB

def n05CanonicalWeightedZeroMap (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B) :
    n05CanonicalClosedSubmodule S K s →L[ℝ] CanonicalL2Sequence S K :=
  (n05LpMapCLM (n05CanonicalWeightedZeroCoordinate S K s w) B hB
    (n05CanonicalWeightedZeroCoordinate_bound S K s w B hB hw)).comp
      (n05CanonicalClosedSubmodule S K s).subtypeL

theorem n05CanonicalWeightedZeroMap_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B)
    (v : n05CanonicalClosedSubmodule S K s) (m : ℕ) :
    n05CanonicalWeightedZeroMap S K s w B hB hw v m = w m • v.val m 0 := by
  simp only [n05CanonicalWeightedZeroMap, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, n05LpMapCLM_apply, n05CanonicalWeightedZeroCoordinate_apply]

theorem n05CanonicalWeightedZeroMap_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B)
    (v : n05CanonicalClosedSubmodule S K s) :
    ‖n05CanonicalWeightedZeroMap S K s w B hB hw v‖ ≤ B * ‖v‖ :=
  n05LpMapCLM_bound (n05CanonicalWeightedZeroCoordinate S K s w) B hB
    (n05CanonicalWeightedZeroCoordinate_bound S K s w B hB hw) v.val

theorem n05WeakCanonicalAngularDerivative_smul {S : PhysicalSpacesData}
    {K : CanonicalData S} {m : ℕ} {f g : CanonicalL2 S K m} {j : ℕ}
    (h : WeakCanonicalAngularDerivative S K m f g j) (c : ℝ) :
    WeakCanonicalAngularDerivative S K m (c • f) (c • g) j := by
  intro φ hφ
  calc
    (∫ p, (c • g) p * φ p ∂canonicalMeasure S K m) =
        c * (∫ p, g p * φ p ∂canonicalMeasure S K m) := by
      rw [← n05CanonicalTestPairing_apply S K m φ (n05CanonicalTest_memLp hφ),
        map_smul, smul_eq_mul, n05CanonicalTestPairing_apply]
    _ = c * ((-1 : ℝ) ^ j *
        (∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m)) :=
      congrArg (fun x : ℝ => c * x) (h φ hφ)
    _ = (-1 : ℝ) ^ j * (c *
        (∫ p, f p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m)) := by ring
    _ = (-1 : ℝ) ^ j *
        (∫ p, (c • f) p * mixedDerivative 0 j φ p ∂canonicalMeasure S K m) := by
      rw [← n05CanonicalTestPairing_apply S K m (mixedDerivative 0 j φ)
        (n05CanonicalTest_angular_memLp hφ j) (c • f), map_smul, smul_eq_mul,
        n05CanonicalTestPairing_apply]

def n05CanonicalJetMultiplierCoordinate (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (m : ℕ) :
    PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) →ₗ[ℝ]
      PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
  w m • LinearMap.id

theorem n05CanonicalJetMultiplierCoordinate_apply (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (w : ℕ → ℝ) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    n05CanonicalJetMultiplierCoordinate S K s w m v = w m • v := by
  simp only [n05CanonicalJetMultiplierCoordinate, LinearMap.smul_apply, LinearMap.id_apply]

theorem n05CanonicalJetMultiplierCoordinate_bound (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hw : ∀ m, ‖w m‖ ≤ B) (m : ℕ)
    (v : PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m)) :
    ‖n05CanonicalJetMultiplierCoordinate S K s w m v‖ ≤ B * ‖v‖ := by
  rw [n05CanonicalJetMultiplierCoordinate_apply, norm_smul]
  exact mul_le_mul_of_nonneg_right (hw m) (norm_nonneg _)

def n05CanonicalJetMultiplierRaw (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B) :
    CanonicalVolumeJets S K s →L[ℝ] CanonicalVolumeJets S K s :=
  n05LpMapCLM (n05CanonicalJetMultiplierCoordinate S K s w) B hB
    (n05CanonicalJetMultiplierCoordinate_bound S K s w B hw)

theorem n05CanonicalJetMultiplierRaw_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B)
    (v : CanonicalVolumeJets S K s) (m : ℕ) (j : Fin (s + 1)) :
    n05CanonicalJetMultiplierRaw S K s w B hB hw v m j = w m • v m j := by
  rw [n05CanonicalJetMultiplierRaw, n05LpMapCLM_apply,
    n05CanonicalJetMultiplierCoordinate_apply, PiLp.smul_apply]

theorem n05CanonicalJetMultiplierRaw_preserves_graph (S : PhysicalSpacesData)
    (K : CanonicalData S) (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ m, ‖w m‖ ≤ B) {v : CanonicalVolumeJets S K s}
    (hv : v ∈ canonicalVolumeGraph S K s) :
    n05CanonicalJetMultiplierRaw S K s w B hB hw v ∈ canonicalVolumeGraph S K s := by
  refine ⟨?_, ?_⟩
  · intro m
    apply (n05CanonicalReflection_fixed_iff S K m _).mp
    simp only [n05CanonicalJetMultiplierRaw_apply]
    rw [map_smul, (n05CanonicalReflection_fixed_iff S K m (v m 0)).mpr (hv.1 m)]
  · intro m j
    simp only [n05CanonicalJetMultiplierRaw_apply]
    exact n05WeakCanonicalAngularDerivative_smul (hv.2 m j) (w m)

def n05CanonicalJetMultiplier (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B) :
    n05CanonicalClosedSubmodule S K s →L[ℝ] n05CanonicalClosedSubmodule S K s :=
  ((n05CanonicalJetMultiplierRaw S K s w B hB hw).comp
    (n05CanonicalClosedSubmodule S K s).subtypeL).codRestrict
      (n05CanonicalClosedSubmodule S K s) (by
        intro v
        rw [← SetLike.mem_coe, n05CanonicalClosedSubmodule_carrier]
        apply n05CanonicalJetMultiplierRaw_preserves_graph S K s w B hB hw
        rw [← n05CanonicalClosedSubmodule_carrier]
        exact v.property)

theorem n05CanonicalJetMultiplier_apply (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B)
    (v : n05CanonicalClosedSubmodule S K s) (m : ℕ) (j : Fin (s + 1)) :
    (n05CanonicalJetMultiplier S K s w B hB hw v).val m j = w m • v.val m j :=
  n05CanonicalJetMultiplierRaw_apply S K s w B hB hw v.val m j

theorem n05CanonicalJetMultiplier_bound (S : PhysicalSpacesData) (K : CanonicalData S)
    (s : ℕ) (w : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ m, ‖w m‖ ≤ B)
    (v : n05CanonicalClosedSubmodule S K s) :
    ‖n05CanonicalJetMultiplier S K s w B hB hw v‖ ≤ B * ‖v‖ :=
  n05LpMapCLM_bound (n05CanonicalJetMultiplierCoordinate S K s w) B hB
    (n05CanonicalJetMultiplierCoordinate_bound S K s w B hw) v.val

end ContinuousFlexibility.Statements
