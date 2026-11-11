import ContinuousFlexibility.Analysis.N07bPiecewiseCanonicalLift
import ContinuousFlexibility.Analysis.N07bSourceBoundChangeVariables
import ContinuousFlexibility.Analysis.N07bAtlasEnergy

/-!
# Integrating a common physical majorant for piecewise canonical jets

The actual current chart converts the square of each angular jet to its
Jacobian-weighted physical integral. A single integrable physical majorant
then sums over the disjoint current atlas. No bound on how many pieces
have a given material cell label is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology BigOperators ENNReal

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S} {V : VolumeModelData S K}
  {base : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- The physical integrand of the actual weighted finite angular row. -/
def n07bPiecewiseCanonicalDensity (T : MaterialData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (g : ℕ → PolarPoint → ℝ)
    (γ t : ℝ) (s m : ℕ) (x : PolarPoint) : ℝ :=
  ∑ j : Fin (s + 1), (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
    (|planeJacobian (K.chart z m) x| *
      (mixedDerivative 0 j.val (g m) (K.chart z m x)) ^ 2)

/-- The same actual change of variables gives both integrability of the
physical row and equality with its canonical square energy. -/
theorem n07b_piecewiseCanonicalEnergy_physical
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (g : ℕ → PolarPoint → ℝ) (γ t : ℝ) (s m : ℕ)
    (hg : ∀ j : Fin (s + 1),
      MemLp (mixedDerivative 0 j.val (g m)) 2 (canonicalMeasure S K m)) :
    IntegrableOn (n07bPiecewiseCanonicalDensity T K z g γ t s m)
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) ∧
    n07bPiecewiseCanonicalJetEnergy T K g γ t s m =
      ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi),
        n07bPiecewiseCanonicalDensity T K z g γ t s m x := by
  have hi (j : Fin (s + 1)) : IntegrableOn
      (fun x => (n07bCanonicalSourceFactor T K γ t m)⁻¹ ^ 2 *
        (|planeJacobian (K.chart z m) x| *
          (mixedDerivative 0 j.val (g m) (K.chart z m x)) ^ 2))
      (physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi)) :=
    (n07b_sourceBound_square_integrable hK hz hs m (hg j)).const_mul _
  refine ⟨integrable_finsetSum Finset.univ (fun j _ => hi j), ?_⟩
  unfold n07bPiecewiseCanonicalJetEnergy n07bPiecewiseCanonicalDensity
  rw [integral_finsetSum _ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, n07b_sourceBound_eLpNorm_sq hK hz hs m (hg j)]

/-- A genuine physical energy bound produces the requested source-space
element and its square norm bound, for arbitrary weight and angular order. -/
theorem n07b_exists_piecewiseCanonicalLift_of_density_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hV : IsVolumeModel T S K V) (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (g e : ℕ → PolarPoint → ℝ) (γ t : ℝ) (s : ℕ)
    (heq : ∀ m, EqOn (g m) (e m) (canonicalOpen S K m))
    (he : ∀ m p, p ∈ canonicalClosed S K m → ContDiffAt ℝ ∞ (e m) p)
    (hp : ∀ m r, r ∈ Ioo (K.left m) (K.right m) →
      Function.Periodic (fun θ => g m (r, θ)) Real.pi)
    (href : ∀ m, (fun p : PolarPoint => g m (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S K m] g m)
    {E : PolarPoint → ℝ}
    (hE : IntegrableOn E (Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi))
    (hbound : ∀ m x, x ∈ physicalPieceOpen S K z m ∩
        (univ ×ˢ Ioc (0 : ℝ) Real.pi) →
      n07bPiecewiseCanonicalDensity T K z g γ t s m x ≤ E x) :
    ∃ F : V.level γ t s,
      (∀ m, (V.forget γ t s F m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m] g m) ∧
      ‖F‖ ^ 2 ≤ ∫ x in Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi, E x := by
  have hg (m : ℕ) (j : Fin (s + 1)) :
      MemLp (mixedDerivative 0 j.val (g m)) 2 (canonicalMeasure S K m) :=
    n07b_canonical_mixedDerivative_memLp_of_extension m (heq m) (he m) 0 j.val
  have hpiece (m : ℕ) : n07bPiecewiseCanonicalJetEnergy T K g γ t s m ≤
      ∫ x in physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi), E x := by
    have hrow := n07b_piecewiseCanonicalEnergy_physical hK hz hs g γ t s m (hg m)
    rw [hrow.2]
    have hsub : physicalPieceOpen S K z m ∩ (univ ×ˢ Ioc (0 : ℝ) Real.pi) ⊆
        Ioo D.a D.b ×ˢ Ioc (0 : ℝ) Real.pi := by
      intro x hx
      exact ⟨((hK.domains z hz hs m).2.2.1 hx.1).1, hx.2.2⟩
    apply integral_mono_ae hrow.1 (hE.mono_set hsub)
    filter_upwards [ae_restrict_mem ((hK.domains z hz hs m).1.measurableSet.inter
      (MeasurableSet.univ.prod measurableSet_Ioc))] with x hx
    exact hbound m x hx
  obtain ⟨hsum, htotal⟩ := n07b_summable_energy_of_piece_integral_bound hK hz hs hE
    (fun m => n07bPiecewiseCanonicalJetEnergy_nonneg T K g γ t s m) hpiece
  obtain ⟨F, hforget, hnorm⟩ := n07b_exists_piecewiseCanonicalLift
    hD hT hV g e γ t s heq he hp href hsum
  exact ⟨F, hforget, hnorm.le.trans htotal⟩

end ContinuousFlexibility.Analysis
