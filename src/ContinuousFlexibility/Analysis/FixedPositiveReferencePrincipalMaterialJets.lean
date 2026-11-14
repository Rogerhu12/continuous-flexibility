module

public import ContinuousFlexibility.Analysis.RadialReferencePrincipalJetEnvelope
public import ContinuousFlexibility.Analysis.ReferencePrincipalPhysicalMaterialJets
public import ContinuousFlexibility.Analysis.PositiveChartRangeGeometry

/-!
# Principal bounds for the already chosen positive reference family

The same displayed coordinate and height remain inputs at every order.
Their genuine inverse is used literally. The physical reciprocal profile
is bounded using its actual cells and transported to the original positive
midpoint sample. Only numerical finite-prefix bounds are chosen here.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped Topology ContDiff BigOperators

/-- The three nonzero radial principal expressions have uniform material
jets for the fixed family. No coordinate, height, width, cell or sample is
chosen by this theorem. The forward and inverse inputs are the outputs of
the same prescribed reference material construction. -/
theorem fixedPositiveReference_principal_material_jets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions Γ.reference S C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (cell : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℕ)
    (hcell : ∀ i, n04PositiveMidpoint i ∈ Γ.reference.cells (cell i))
    (Y H : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w) → ℝ → ℝ)
    (hgeometry : ∀ i, PositiveChartRangeGeometry (positiveReferenceCylinderChart (Y i))
      (positiveReferenceCylinderInverse (Y i)) (fun p : PolarPoint => H i p.1)
      (n04PositiveLeft i) (n04PositiveRight i) 0 1)
    (hjets : ∀ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ i,
      (∀ k, k ≤ N → ∀ x : ℝ,
        |iteratedDeriv (k + 1) (Y i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (H i) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A ∧
        |iteratedDeriv k (fun t => (H i t)⁻¹) x| ≤ A * (C0 * T.E0 (T.sample (cell i))) ^ A) ∧
      ∀ x : ℝ, |iteratedDeriv (N + 1) (Function.invFun (Y i)) x| ≤
        A * (C0 * T.E0 (T.sample (cell i))) ^ A) :
    ∀ s : ℕ, ∃ M : ℝ, 1 ≤ M ∧ ∀ i x, x ∈ Ioo (0 : ℝ) 1 →
      let χ := Function.invFun (Y i)
      let W := C0 * T.E0 (T.sample (cell i))
      |iteratedDeriv s (fun t => H i (χ t) ^ 2 * Γ.reference.w (χ t) *
        deriv (Y i) (χ t)) x| ≤ M * W ^ M ∧
      |iteratedDeriv s (fun t => (H i (χ t))⁻¹ ^ 2 * (Γ.reference.w (χ t))⁻¹ *
        deriv χ t) x| ≤ M * W ^ M ∧
      |iteratedDeriv s (fun t => H i (χ t) ^ 2 *
        (deriv Γ.reference.w (χ t) / χ t) * deriv χ t) x| ≤ M * W ^ M := by
  classical
  choose A₀ hA₀ hactual using hjets
  intro s
  obtain ⟨P₀, hP₀, hphysical⟩ :=
    retainedReference_positive_principal_physical_material_jets
      P hSelected hband hq hΓ hw hcoordinates hC hT hC0 hfloor s
  obtain ⟨C₁, hC₁, henvelope⟩ := exists_radialReferencePrincipal_jet_envelope s
  let D : ℝ := 1 + P₀ + ∑ k : Fin (s + 1), A₀ k.val
  have hsum : 0 ≤ ∑ k : Fin (s + 1), A₀ k.val :=
    Finset.sum_nonneg (fun k _ => zero_le_one.trans (hA₀ k.val))
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hP₀, hsum]
  have hP₀D : P₀ ≤ D := by dsimp only [D]; linarith only [hsum]
  have hAD (k : ℕ) (hk : k ≤ s) : A₀ k ≤ D :=
    (Finset.single_le_sum (f := fun j : Fin (s + 1) => A₀ j.val)
      (fun j _ => zero_le_one.trans (hA₀ j.val))
      (Finset.mem_univ (⟨k, by omega⟩ : Fin (s + 1)))).trans
        (by dsimp only [D]; linarith only [hP₀])
  let d : ℕ := 4 * s + 4
  let coefficient : ℝ := C₁ * D ^ d
  let exponent : ℝ := D * (d : ℝ)
  let M : ℝ := 1 + coefficient + exponent
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (zero_le_one.trans hC₁) (pow_nonneg (zero_le_one.trans hD) _)
  have hexponent : 0 ≤ exponent :=
    mul_nonneg (zero_le_one.trans hD) (Nat.cast_nonneg _)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hcoefficient, hexponent]
  have hcoefficientM : coefficient ≤ M := by dsimp only [M]; linarith only [hexponent]
  have hexponentM : exponent ≤ M := by dsimp only [M]; linarith only [hcoefficient]
  refine ⟨M, hM, ?_⟩
  intro i x hx
  let χ : ℝ → ℝ := Function.invFun (Y i)
  let W : ℝ := C0 * T.E0 (T.sample (cell i))
  let Z : ℝ := D * W ^ D
  have hW : 1 ≤ W := hfloor (cell i)
  have hZ : 1 ≤ Z := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ D * W ^ D := mul_le_mul hD (Real.one_le_rpow hW (zero_le_one.trans hD))
        zero_le_one (zero_le_one.trans hD)
  have hbound {A : ℝ} (hA : 1 ≤ A) (hAD : A ≤ D) : A * W ^ A ≤ Z :=
    mul_le_mul hAD (Real.rpow_le_rpow_of_exponent_le hW hAD)
      (Real.rpow_nonneg (zero_le_one.trans hW) _) (zero_le_one.trans hD)
  have hcost : C₁ * Z ^ d ≤ M * W ^ M := by
    calc
      _ = coefficient * W ^ exponent := by
        dsimp only [Z, coefficient, exponent]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hW) D d]
        ring
      _ ≤ coefficient * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hexponentM) hcoefficient
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hcoefficientM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hY : ContDiff ℝ ∞ (Y i) := by
    simpa only [positiveReferenceCylinderChart, Function.comp_def] using
      (hgeometry i).chart_smooth.fst.comp hline
  have hH : ContDiff ℝ ∞ (H i) := by
    simpa only [Function.comp_def] using (hgeometry i).height_smooth.comp hline
  have hχ : ContDiff ℝ ∞ χ := by
    simpa only [positiveReferenceCylinderInverse, Function.comp_def] using
      (hgeometry i).inverse_smooth.fst.comp hline
  have hr : χ x ∈ Ioo (n04PositiveLeft i) (n04PositiveRight i) :=
    ((hgeometry i).inverse_maps_open (x := (x, 0)) ⟨hx, mem_univ _⟩).1
  have hDgeom : RadialProfileGeometry Γ.reference := hΓ.2.1.choose_spec.1
  have hcore : χ x ∈ radialCore Γ.reference :=
    n04PositiveComponent_interval_subset (hDgeom.2.2.1.1.continuous_deriv (by simp)) i hr
  have hwpos : 0 < Γ.reference.w (χ x) := hDgeom.2.2.2.2.1 _ hcore
  have hrpos : 0 < χ x := hDgeom.1.trans hcore.1
  have hphys (k : ℕ) (hk : k ≤ s) :=
    hphysical i (cell i) (hcell i) (χ x) ⟨hr.1.le, hr.2.le⟩ k hk
  have hraw (k : ℕ) (hk : k ≤ s) (u : ℝ) := (hactual s i).1 k hk u
  have hχjets (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s + 1) :
      |iteratedDeriv k χ x| ≤ Z := by
    have he : k - 1 + 1 = k := by omega
    have hi := (hactual (k - 1) i).2 x
    rw [he] at hi
    exact hi.trans (hbound (hA₀ _) (hAD _ (by omega)))
  have hone (k : ℕ) (_ : k ≤ s) : |iteratedDeriv k (fun _ : ℝ => (1 : ℝ)) (χ x)| ≤ Z := by
    rw [iteratedDeriv_const]
    by_cases hk : k = 0
    · simpa only [if_pos hk, abs_one] using hZ
    · simpa only [if_neg hk, abs_zero] using zero_le_one.trans hZ
  have hYa (k : ℕ) (hk : k ≤ s) : |iteratedDeriv k (deriv (Y i)) (χ x)| ≤ Z := by
    rw [← iteratedDeriv_succ']
    exact (hraw k hk (χ x)).1.trans (hbound (hA₀ _) (hAD s le_rfl))
  have hA := henvelope hZ (H i) Γ.reference.w (deriv (Y i)) χ x
    hH.contDiffAt hDgeom.2.2.1.1.contDiffAt
    (contDiff_infty_iff_deriv.mp hY).2.contDiffAt hχ.contDiffAt
    (fun k hk => (hraw k hk (χ x)).2.1.trans (hbound (hA₀ _) (hAD s le_rfl)))
    (fun k hk => (hphys k hk).1.trans (hbound hP₀ hP₀D)) hYa hχjets
  have hI := henvelope hZ (fun t => (H i t)⁻¹) (fun t => (Γ.reference.w t)⁻¹)
    (fun _ => 1) χ x
    (hH.contDiffAt.inv ((hgeometry i).height_positive (χ x, 0)).ne')
    (hDgeom.2.2.1.1.contDiffAt.inv hwpos.ne') contDiffAt_const hχ.contDiffAt
    (fun k hk => (hraw k hk (χ x)).2.2.trans (hbound (hA₀ _) (hAD s le_rfl)))
    (fun k hk => (hphys k hk).2.1.trans (hbound hP₀ hP₀D)) hone hχjets
  have hCj := henvelope hZ (H i) (fun t => deriv Γ.reference.w t / t)
    (fun _ => 1) χ x hH.contDiffAt
    ((contDiff_infty_iff_deriv.mp hDgeom.2.2.1.1).2.contDiffAt.div
      contDiffAt_id hrpos.ne') contDiffAt_const hχ.contDiffAt
    (fun k hk => (hraw k hk (χ x)).2.1.trans (hbound (hA₀ _) (hAD s le_rfl)))
    (fun k hk => (hphys k hk).2.2.trans (hbound hP₀ hP₀D)) hone hχjets
  exact ⟨hA.1.trans hcost, hI.2.trans hcost, hCj.2.trans hcost⟩

end ContinuousFlexibility.Analysis
