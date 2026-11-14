module

public import ContinuousFlexibility.Analysis.N07aOpenCoefficientWeakJets
public import ContinuousFlexibility.Analysis.N07aVolumeCell
public import ContinuousFlexibility.Analysis.N07aAngularEven

/-!
# Realization of the original coefficient jets in the prescribed volume graph

The angular derivatives and reflection relation are proved for the actual
classes. Changing the material level rescales these classes by exactly the
weight prescribed in `IsVolumeModel`, so every level has the same source.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory ContinuousFlexibility.Statements
open scoped BigOperators

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {K : CanonicalData S} {V : VolumeModelData S K}

theorem N07aCanonicalOpenCoefficient.toLp_even {m : ℕ}
    (χ : N07aCanonicalOpenCoefficient S K m)
    (heven : ∀ p ∈ canonicalOpen S K m, χ.value (p.1, -p.2) = χ.value p) :
    n07aAngularReflection m χ.toLp = χ.toLp := by
  apply (n07aAngularReflection_fixed_iff m χ.toLp).mpr
  have hreflection :=
    (n07aAngularReflection_preserving (S := S) (K := K) m).quasiMeasurePreserving.ae_eq_comp
      χ.toLp_ae
  filter_upwards [hreflection, χ.toLp_ae,
    n07a_canonicalOpen_ae (S := S) (K := K) (m := m)] with p hp hq hpU
  have hpR : (p.1, -p.2) ∈ canonicalOpen S K m := ⟨hpU.1, mem_univ _⟩
  have hpoint : χ.value (p.1, Real.pi - p.2) = χ.value p := by
    have he : (p.1, Real.pi - p.2) = (p.1, -p.2) + (0, Real.pi) := by
      ext <;> simp only [Prod.mk_add_mk, add_zero] <;> ring
    rw [he, χ.periodic _ hpR, heven p hpU]
  exact hp.trans (hpoint.trans hq.symm)

def n07aCanonicalCoefficientJetArray
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m) (s : ℕ) (a : ℕ → ℝ) :
    ∀ m, PiLp 2 (fun _ : Fin (s + 1) => CanonicalL2 S K m) :=
  fun m => WithLp.toLp 2 (fun j => a m • ((χ m).jet 0 j.val).toLp)

theorem n07aCanonicalCoefficientJetArray_apply
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m) (s : ℕ) (a : ℕ → ℝ)
    (m : ℕ) (j : Fin (s + 1)) :
    n07aCanonicalCoefficientJetArray χ s a m j = a m • ((χ m).jet 0 j.val).toLp := by
  simp only [n07aCanonicalCoefficientJetArray, PiLp.toLp_apply]

theorem n07aCanonicalCoefficientJetArray_graph
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m) (s : ℕ) (a : ℕ → ℝ)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → (χ m).value (p.1, -p.2) = (χ m).value p)
    (hmem : Memℓp (n07aCanonicalCoefficientJetArray χ s a) 2) :
    (⟨n07aCanonicalCoefficientJetArray χ s a, hmem⟩ : CanonicalVolumeJets S K s) ∈
      canonicalVolumeGraph S K s := by
  constructor
  · intro m
    change (fun p : PolarPoint => n07aCanonicalCoefficientJetArray χ s a m 0
      (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m]
      (n07aCanonicalCoefficientJetArray χ s a m 0 : PolarPoint → ℝ)
    rw [n07aCanonicalCoefficientJetArray_apply, Fin.val_zero, (χ m).jet_toLp_zero]
    apply (n07aAngularReflection_fixed_iff m _).mp
    rw [map_smul, (χ m).toLp_even (heven m)]
  · intro m j
    change WeakCanonicalAngularDerivative S K m
      (n07aCanonicalCoefficientJetArray χ s a m 0)
      (n07aCanonicalCoefficientJetArray χ s a m j) j.val
    rw [n07aCanonicalCoefficientJetArray_apply, n07aCanonicalCoefficientJetArray_apply,
      Fin.val_zero, (χ m).jet_toLp_zero]
    exact (n07a_weakCanonicalMixed_zero_radial_iff _ _ j.val).mp
      (((n07a_weakCanonicalMixed_zero_radial_iff _ _ j.val).mpr
        ((χ m).toLp_weakAngular j.val)).smul (a m))

local instance n07aJetRealizationLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) :=
  Submodule.normedAddCommGroup _

local instance n07aJetRealizationLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) :=
  Submodule.normedSpace _

def n07aOpenCoefficientVolume (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → (χ m).value (p.1, -p.2) = (χ m).value p)
    (hmem : Memℓp (n07aCanonicalCoefficientJetArray χ s
      (fun m => (n07aVolumeWeight T K γ t m)⁻¹)) 2) : V.level γ t s :=
  ⟨⟨n07aCanonicalCoefficientJetArray χ s (fun m => (n07aVolumeWeight T K γ t m)⁻¹), hmem⟩,
    by
      rw [← SetLike.mem_coe, hV.1 γ t s]
      exact n07aCanonicalCoefficientJetArray_graph χ s _ heven hmem⟩

theorem n07aOpenCoefficientVolume_forget
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (χ : ∀ m, N07aCanonicalOpenCoefficient S K m)
    (heven : ∀ m p, p ∈ canonicalOpen S K m → (χ m).value (p.1, -p.2) = (χ m).value p)
    (hmem : Memℓp (n07aCanonicalCoefficientJetArray χ s
      (fun m => (n07aVolumeWeight T K γ t m)⁻¹)) 2) :
    V.forget γ t s (n07aOpenCoefficientVolume hV γ t s χ heven hmem) =
      fun m => (χ m).toLp := by
  funext m
  rw [n07aVolume_forget_apply hV]
  change n07aVolumeWeight T K γ t m •
    n07aCanonicalCoefficientJetArray χ s (fun m => (n07aVolumeWeight T K γ t m)⁻¹) m 0 = _
  rw [n07aCanonicalCoefficientJetArray_apply, Fin.val_zero, (χ m).jet_toLp_zero,
    smul_smul, mul_inv_cancel₀ (n07aVolumeWeight_pos hD hT γ t m).ne', one_smul]

end ContinuousFlexibility.Analysis
