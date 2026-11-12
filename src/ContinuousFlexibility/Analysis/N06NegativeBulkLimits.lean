import ContinuousFlexibility.Analysis.N06NegativeFiniteForcing
import ContinuousFlexibility.Analysis.N06NegativeForcingParity
import ContinuousFlexibility.Analysis.N06CanonicalCosineCutoff
import ContinuousFlexibility.Analysis.N06GraphCauchy
import ContinuousFlexibility.Radial.R11bWeakNormalLimit

/-!
# The actual negative Green bulk terms converge in the original L2 space

The original graph gives one family of H2 modal representatives. Their
finite values converge to its original canonical height, and their actual
principal expressions converge to the actual principal forcing. The latter
uses the mode equations and the forcing reflection theorem, not convergence
of separate second derivatives.

The finite Green identity retains the literal endpoint Wronskians. A caller
can cancel these finite terms using actual root transmission before applying
the bulk limit. No infinite endpoint trace is introduced or assumed here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Value convergence of the original even cosine cutoffs on any recorded
canonical interval. The zero-order weak row is the identity itself. -/
theorem n06_canonicalCosineCut_value_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ)) :
    ∃ hN : ∀ N, MemLp (n06CylinderCosineCut N U) 2 (canonicalMeasure S K m),
      Tendsto (fun N => (hN N).toLp (n06CylinderCosineCut N U)) atTop (𝓝 U) := by
  let row : Fin (0 + 1) → CanonicalL2 S K m := fun _ => U
  have hrow : ∀ k, WeakCanonicalAngularDerivative S K m (row 0) (row k) k.val := by
    intro k
    have hk : k = 0 := by
      apply Fin.ext
      omega
    subst k
    intro φ hφ
    simp only [Fin.val_zero, pow_zero, one_mul, spaces_mixedDerivative_zero]
  obtain ⟨hJ, hlim⟩ := n06_canonicalCosineCut_jetRow_tendsto row he hrow
  have hN (N : ℕ) : MemLp (n06CylinderCosineCut N U) 2 (canonicalMeasure S K m) := by
    simpa only [Fin.val_zero, spaces_mixedDerivative_zero, row] using hJ N 0
  refine ⟨hN, ?_⟩
  simpa only [Fin.val_zero, spaces_mixedDerivative_zero, row] using
    n06_tendsto_component_of_sum_sq_errors hlim (0 : Fin (0 + 1))

private theorem finite_value_eq_cosineCut_ae
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m) (v : ℕ → ℝ → ℝ)
    (hv : ∀ i, n06HalfCosineCoefficient U i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i) (N : ℕ) :
    r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis
      =ᵐ[canonicalMeasure S K m] n06CylinderCosineCut N U := by
  have hall : ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
      ∀ i ∈ Finset.range (N + 1), n06HalfCosineCoefficient U i y = v i y :=
    (eventually_all_finset _).mpr (fun i _ => hv i)
  have hp : ∀ᵐ p : PolarPoint ∂canonicalMeasure S K m,
      ∀ i ∈ Finset.range (N + 1), n06HalfCosineCoefficient U i p.1 = v i p.1 := by
    apply (congrArg (fun μ : Measure PolarPoint => ∀ᵐ p ∂μ,
      ∀ i ∈ Finset.range (N + 1), n06HalfCosineCoefficient U i p.1 = v i p.1)
        (n06_canonicalMeasure_eq_radial_prod (S := S) (K := K) m)).mpr
    exact Measure.quasiMeasurePreserving_fst.ae hall
  filter_upwards [hp] with p he
  unfold n06CylinderCosineCut r11bFiniteSynthesis
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i hi]

/-- Replacing every actual coefficient by its same AE representative
preserves both membership and the original value limit. -/
theorem n06_canonical_representative_values_tendsto_on_piece
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U : CanonicalL2 S K m)
    (he : (fun p : PolarPoint => U (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] (U : PolarPoint → ℝ))
    (v : ℕ → ℝ → ℝ)
    (hv : ∀ i, n06HalfCosineCoefficient U i
      =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] v i) :
    ∃ hN : ∀ N, MemLp
        (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2
          (canonicalMeasure S K m),
      Tendsto (fun N => (hN N).toLp
        (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis)) atTop (𝓝 U) := by
  obtain ⟨hC, hlim⟩ := n06_canonicalCosineCut_value_tendsto U he
  have hN (N : ℕ) : MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2
        (canonicalMeasure S K m) :=
    (memLp_congr_ae (finite_value_eq_cosineCut_ae U v hv N)).mpr (hC N)
  have heq (N : ℕ) :
      (hN N).toLp (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) =
        (hC N).toLp (n06CylinderCosineCut N U) :=
    (hN N).toLp_congr (hC N) (finite_value_eq_cosineCut_ae U v hv N)
  exact ⟨hN, hlim.congr' (Eventually.of_forall (fun N => (heq N).symm))⟩

def n06NegativeFiniteValue (v : ℕ → ℝ → ℝ) (N : ℕ) : PolarPoint → ℝ :=
  r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis

def n06NegativeFinitePrincipal (v : ℕ → ℝ → ℝ) (N : ℕ) : PolarPoint → ℝ := fun p =>
  n06FiniteMixedField (Finset.range (N + 1)) v 2 0 p -
    p.1 * n06FiniteMixedField (Finset.range (N + 1)) v 0 2 p

/-- The finite values and principal fields are built from one modal
family, and both converge in the original canonical Hilbert space. -/
structure N06NegativeGraphApproximation
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    (U G : CanonicalL2 S K m) where
  left_lt_right : K.left m < K.right m
  modes : ℕ → ℝ → ℝ
  coefficient : ∀ i, n06HalfCosineCoefficient U i
    =ᵐ[volume.restrict (Ioo (K.left m) (K.right m))] modes i
  contDiff : ∀ i, ContDiff ℝ 1 (modes i)
  deriv_ac : ∀ i, AbsolutelyContinuousOnInterval (deriv (modes i)) (K.left m) (K.right m)
  mode_memLp : ∀ i, MemLp (modes i) 2 (volume.restrict (Ioo (K.left m) (K.right m)))
  deriv_memLp : ∀ i, MemLp (deriv (modes i)) 2 (volume.restrict (Ioo (K.left m) (K.right m)))
  second_memLp : ∀ i, MemLp (deriv (deriv (modes i))) 2
    (volume.restrict (Ioo (K.left m) (K.right m)))
  ode : ∀ i, ∀ᵐ y ∂volume.restrict (Ioo (K.left m) (K.right m)),
    deriv (deriv (modes i)) y + (((2 * i : ℕ) : ℝ)) ^ 2 * y * modes i y =
      n06HalfCosineCoefficient G i y
  value_memLp : ∀ N, MemLp (n06NegativeFiniteValue modes N) 2 (canonicalMeasure S K m)
  principal_memLp : ∀ N, MemLp (n06NegativeFinitePrincipal modes N) 2 (canonicalMeasure S K m)
  value_tendsto : Tendsto (fun N => (value_memLp N).toLp (n06NegativeFiniteValue modes N))
    atTop (𝓝 U)
  principal_tendsto : Tendsto
    (fun N => (principal_memLp N).toLp (n06NegativeFinitePrincipal modes N)) atTop (𝓝 G)

/-- All approximation data are consequences of the same original N05
graph and its actual forcing formula. -/
theorem n06N05_negative_graphApproximation
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (u : B.Space) (m : ℕ) (hm : K.positive m = false) :
    ∃ G : CanonicalL2 S K m,
      (G : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        n06NegativePrincipalForcing D S C K u.val.1
          (V.forget (3 / 4 : ℝ) 0 b u.val.2) m ∧
      Nonempty (N06NegativeGraphApproximation (u.val.1.1 m) G) := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2.1
  obtain ⟨G, hG, v, hv⟩ := n06N05_negative_modes_regular hT hS h u m hm
  have hUeven := n06N05_height_reflection h.2 u m
  have hGeven := n06N05_negative_principalSource_reflection hT hS h u m hm G hG
  obtain ⟨hUN, hUlim⟩ := n06_canonical_representative_values_tendsto_on_piece
    (u.val.1.1 m) hUeven v (fun i => (hv i).1)
  obtain ⟨hGN, hGlim⟩ := n06_canonicalCosineCut_value_tendsto G hGeven
  have hode := fun i => (hv i).2.2.2.2.2.2
  have hQeq (N : ℕ) : n06NegativeFinitePrincipal v N
      =ᵐ[canonicalMeasure S K m] n06CylinderCosineCut N G :=
    n06_negative_finite_principal_eq_forcingCut G v hode (Finset.range (N + 1))
  have hQN (N : ℕ) : MemLp (n06NegativeFinitePrincipal v N) 2 (canonicalMeasure S K m) :=
    (memLp_congr_ae (hQeq N)).mpr (hGN N)
  have hQclass (N : ℕ) :
      (hQN N).toLp (n06NegativeFinitePrincipal v N) = (hGN N).toLp (n06CylinderCosineCut N G) :=
    (hQN N).toLp_congr (hGN N) (hQeq N)
  refine ⟨G, hG, ⟨{
    left_lt_right := (h04.1.referenceBounds m).2.1
    modes := v
    coefficient := fun i => (hv i).1
    contDiff := fun i => (hv i).2.1
    deriv_ac := fun i => (hv i).2.2.1
    mode_memLp := fun i => (hv i).2.2.2.1
    deriv_memLp := fun i => (hv i).2.2.2.2.1
    second_memLp := fun i => (hv i).2.2.2.2.2.1
    ode := hode
    value_memLp := hUN
    principal_memLp := hQN
    value_tendsto := hUlim
    principal_tendsto := hGlim.congr' (Eventually.of_forall (fun N => (hQclass N).symm))
  }⟩⟩

/-- Every finite reconstruction retains the true endpoint terms in the
original canonical measure. The reference record supplies only a carrier
for the already proved arbitrary-interval Green theorem. -/
theorem N06NegativeGraphApproximation.green
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    (D : ReferenceData) (N : ℕ) {φ : PolarPoint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, n06NegativeFinitePrincipal P.modes N p * φ p ∂canonicalMeasure S K m) -
      (∫ p, n06NegativeFiniteValue P.modes N p * n06NegativePrincipalTest φ p
        ∂canonicalMeasure S K m) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (φ (K.right m, θ) * radialPartial (n06NegativeFiniteValue P.modes N) (K.right m, θ) -
          n06NegativeFiniteValue P.modes N (K.right m, θ) * radialPartial φ (K.right m, θ)) -
        (φ (K.left m, θ) * radialPartial (n06NegativeFiniteValue P.modes N) (K.left m, θ) -
          n06NegativeFiniteValue P.modes N (K.left m, θ) * radialPartial φ (K.left m, θ)) := by
  let Dm : ReferenceData := { D with a := K.left m, b := K.right m }
  have he := n06_finite_negative_principal_green_half (D := Dm) P.left_lt_right.le
    (Finset.range (N + 1)) P.modes (fun i _ => P.contDiff i) (fun i _ => P.deriv_ac i)
    (fun i _ => P.mode_memLp i) (fun i _ => P.deriv_memLp i)
    (fun i _ => P.second_memLp i) hφ hφp
  simpa only [Dm, radialCore, canonicalMeasure, n06NegativeFiniteValue,
    n06NegativeFinitePrincipal] using he

/-- Both genuine bulk pairings converge for any fixed original L2
tests. This is the limit used after finite endpoint cancellation. -/
theorem N06NegativeGraphApproximation.bulk_pairings_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    {φ ψ : PolarPoint → ℝ}
    (hφ : MemLp φ 2 (canonicalMeasure S K m))
    (hψ : MemLp ψ 2 (canonicalMeasure S K m)) :
    Tendsto (fun N =>
      (∫ p, n06NegativeFinitePrincipal P.modes N p * φ p ∂canonicalMeasure S K m) -
        ∫ p, n06NegativeFiniteValue P.modes N p * ψ p ∂canonicalMeasure S K m)
      atTop (𝓝 ((∫ p, G p * φ p ∂canonicalMeasure S K m) -
        ∫ p, U p * ψ p ∂canonicalMeasure S K m)) := by
  have hQ := r11b_tendsto_integral_mul_of_L2_tendsto P.principal_memLp (Lp.memLp G) hφ
    (by simpa only [Lp.toLp_coeFn] using P.principal_tendsto)
  have hU := r11b_tendsto_integral_mul_of_L2_tendsto P.value_memLp (Lp.memLp U) hψ
    (by simpa only [Lp.toLp_coeFn] using P.value_tendsto)
  exact hQ.sub hU

/-- Smooth closed-cylinder tests satisfy the needed L2 hypotheses;
neither radial endpoint is constrained to have zero test value. -/
theorem N06NegativeGraphApproximation.green_bulk_tendsto
    {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}
    {U G : CanonicalL2 S K m} (P : N06NegativeGraphApproximation U G)
    {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Tendsto (fun N =>
      (∫ p, n06NegativeFinitePrincipal P.modes N p * φ p ∂canonicalMeasure S K m) -
        ∫ p, n06NegativeFiniteValue P.modes N p * n06NegativePrincipalTest φ p
          ∂canonicalMeasure S K m)
      atTop (𝓝 ((∫ p, G p * φ p ∂canonicalMeasure S K m) -
        ∫ p, U p * n06NegativePrincipalTest φ p ∂canonicalMeasure S K m)) := by
  have hPφ : Continuous (n06NegativePrincipalTest φ) :=
    (contDiff_cylinder_radialPartial (contDiff_cylinder_radialPartial hφ)).continuous.sub
      (continuous_fst.mul
        (contDiff_cylinder_angularPartial (contDiff_cylinder_angularPartial hφ)).continuous)
  exact P.bulk_pairings_tendsto (n06_memLp_canonical_of_continuous m hφ.continuous)
    (n06_memLp_canonical_of_continuous m hPφ)

end ContinuousFlexibility.Analysis
