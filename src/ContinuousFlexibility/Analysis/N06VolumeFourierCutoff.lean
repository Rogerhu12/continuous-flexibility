import ContinuousFlexibility.Analysis.N06FourierCutWeakGraph
import ContinuousFlexibility.Analysis.AngularFrequency
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong angular Fourier truncation in the original volume level

Every stored angular jet is cut off at the same frequency. The actual weak
graph and its reflection condition are preserved, the original norm is
contracted, and the complete infinite piece sequence converges strongly.
The resulting dense subspace has genuine finite cosine representatives
with arbitrary L2 radial coefficients, including every stored angular jet.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Radial ContinuousFlexibility.Analysis
open scoped BigOperators ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K} {m b : ℕ}

def n06CanonicalFourierCutRow (N : ℕ)
    (v : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m) :=
  WithLp.toLp 2 (fun j => n06CanonicalFourierCutL2 N (v j))

theorem n06CanonicalFourierCutRow_apply (N : ℕ)
    (v : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) (j : Fin (b + 1)) :
    n06CanonicalFourierCutRow N v j = n06CanonicalFourierCutL2 N (v j) := rfl

theorem n06CanonicalFourierCutRow_norm_le (N : ℕ)
    (v : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    ‖n06CanonicalFourierCutRow N v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun j _ =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (n06CanonicalFourierCutL2_norm_le N (v j)))

theorem n06CanonicalFourierCutRow_tendsto
    (v : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)) :
    Tendsto (fun N => n06CanonicalFourierCutRow N v) atTop (𝓝 v) := by
  have h : Tendsto (fun N => fun j : Fin (b + 1) => n06CanonicalFourierCutL2 N (v j))
      atTop (𝓝 (fun j => v j)) :=
    tendsto_pi_nhds.mpr (fun j => n06CanonicalFourierCutL2_tendsto (v j))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S K m)).continuousAt.tendsto.comp h

/-- No piece truncation is made: all original material coordinates remain. -/
def n06CanonicalVolumeFourierCut (N : ℕ) (v : CanonicalVolumeJets S K b) :
    CanonicalVolumeJets S K b :=
  ⟨fun m => n06CanonicalFourierCutRow N (v m),
    (lp.memℓp v).mono' (fun m => n06CanonicalFourierCutRow_norm_le N (v m))⟩

theorem n06CanonicalVolumeFourierCut_apply (N : ℕ)
    (v : CanonicalVolumeJets S K b) (m : ℕ) (j : Fin (b + 1)) :
    n06CanonicalVolumeFourierCut N v m j = n06CanonicalFourierCutL2 N (v m j) := rfl

theorem n06CanonicalVolumeFourierCut_norm_le (N : ℕ) (v : CanonicalVolumeJets S K b) :
    ‖n06CanonicalVolumeFourierCut N v‖ ≤ ‖v‖ :=
  lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun m => n06CanonicalFourierCutRow_norm_le N (v m))

theorem n06CanonicalVolumeFourierCut_mem (N : ℕ) (v : CanonicalVolumeJets S K b)
    (hv : v ∈ canonicalVolumeGraph S K b) :
    n06CanonicalVolumeFourierCut N v ∈ canonicalVolumeGraph S K b := by
  constructor
  · intro m
    exact n06CanonicalFourierCutL2_reflection N (v m 0) (hv.1 m)
  · intro m j
    exact (hv.2 m j).n06_fourierCut N

/-- Dominated convergence is applied to the actual squared piece errors.
The majorant is four times the original summable row norm square. -/
theorem n06CanonicalVolumeFourierCut_tendsto (v : CanonicalVolumeJets S K b) :
    Tendsto (fun N => n06CanonicalVolumeFourierCut N v) atTop (𝓝 v) := by
  have hpoint (m : ℕ) : Tendsto
      (fun N => ‖n06CanonicalFourierCutRow N (v m) - v m‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((n06CanonicalFourierCutRow_tendsto (v m)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => v m) atTop (𝓝 (v m)))).norm.pow 2
  have hbound (N m : ℕ) :
      ‖‖n06CanonicalFourierCutRow N (v m) - v m‖ ^ 2‖ ≤ 4 * ‖v m‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnorm : ‖n06CanonicalFourierCutRow N (v m) - v m‖ ≤ 2 * ‖v m‖ := by
      calc
        _ ≤ ‖n06CanonicalFourierCutRow N (v m)‖ + ‖v m‖ := norm_sub_le _ _
        _ ≤ 2 * ‖v m‖ := by linarith only [n06CanonicalFourierCutRow_norm_le N (v m)]
    calc
      _ ≤ (2 * ‖v m‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
      _ = _ := by ring
  have hsum : Summable (fun m => 4 * ‖v m‖ ^ 2) :=
    (angular_summable_norm_sq v).mul_left 4
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall (fun N m => hbound N m))
  have hsquare : Tendsto (fun N => ‖n06CanonicalVolumeFourierCut N v - v‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [tsum_zero, ← angular_tsum_norm_sq,
      lp.coeFn_sub, Pi.sub_apply, n06CanonicalVolumeFourierCut] using hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsquare
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hroot

/-- The angular cutoff in the selected original source submodule. -/
def n06VolumeFourierCut (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) : V.level γ t b :=
  ⟨n06CanonicalVolumeFourierCut N v.val, by
    rw [← SetLike.mem_coe, hV.1 γ t b]
    apply n06CanonicalVolumeFourierCut_mem
    rw [← hV.1 γ t b]
    exact v.property⟩

theorem n06VolumeFourierCut_apply (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) (m : ℕ) (j : Fin (b + 1)) :
    (n06VolumeFourierCut hV γ t b N v).val m j = n06CanonicalFourierCutL2 N (v.val m j) := rfl

theorem n06VolumeFourierCut_norm_le (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) :
    ‖n06VolumeFourierCut hV γ t b N v‖ ≤ ‖v‖ :=
  n06CanonicalVolumeFourierCut_norm_le N v.val

theorem n06VolumeFourierCut_tendsto (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) (v : V.level γ t b) :
    Tendsto (fun N => n06VolumeFourierCut hV γ t b N v) atTop (𝓝 v) :=
  tendsto_subtype_rng.mpr (n06CanonicalVolumeFourierCut_tendsto v.val)

/-- Every row is the actual derivative of the same finite cosine synthesis. -/
theorem n06VolumeFourierCut_coe_cosine_jet (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) (m : ℕ) (j : Fin (b + 1)) :
    ((n06VolumeFourierCut hV γ t b N v).val m j : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis (Finset.range (N + 1))
          (n06HalfCosineCoefficient (v.val m 0))
          (fun i => iteratedDeriv j.val (referenceAngularBasis i)) := by
  change (n06CanonicalFourierCutL2 N (v.val m j) : PolarPoint → ℝ)
    =ᵐ[canonicalMeasure S K m] _
  have hv : v.val ∈ canonicalVolumeGraph S K b := by
    rw [← hV.1 γ t b]
    exact v.property
  have h₁ := (n06CanonicalFourierCutL2_coe_ae N (v.val m j)).trans
    ((hv.2 m j).n06_fourierCut_angularJet_ae _ (n06FourierCutoff_neg N)).symm
  have h₂ := n06_canonicalFourierCut_angularJet_eq_cosine_ae (v.val m 0) (hv.1 m) N j.val
  simpa only [n06CylinderCosineCut_angularJet] using h₁.trans h₂

private theorem n06_finiteSynthesis_extend
    {s t : Finset ℕ} (hst : s ⊆ t) (a e : ℕ → ℝ → ℝ) :
    r11bFiniteSynthesis t (fun i r => if i ∈ s then a i r else 0) e =
      r11bFiniteSynthesis s a e := by
  funext p
  symm
  calc
    _ = ∑ i ∈ s, (if i ∈ s then a i p.1 else 0) * e i p.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left hi]
    _ = _ := Finset.sum_subset hst (fun i _ hi => by rw [ite_eq_right hi, zero_mul])

/-- One finite frequency set works on all pieces and at all stored orders.
The radial coefficients are only required to belong to the actual radial L2 spaces. -/
def n06VolumeFiniteAngularCore (γ t : ℝ) (b : ℕ) : Submodule ℝ (V.level γ t b) where
  carrier := {v | ∃ s : Finset ℕ, ∃ a : ℕ → ℕ → ℝ → ℝ,
    (∀ m i, MemLp (a m i) 2 (volume.restrict (Ioo (K.left m) (K.right m)))) ∧
    ∀ m (j : Fin (b + 1)), (v.val m j : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
      r11bFiniteSynthesis s (a m) (fun i => iteratedDeriv j.val (referenceAngularBasis i))}
  zero_mem' := by
    refine ⟨∅, fun _ _ _ => 0, fun _ _ => MemLp.zero', ?_⟩
    intro m j
    change ((0 : CanonicalL2 S K m) : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] _
    filter_upwards [Lp.coeFn_zero ℝ 2 (canonicalMeasure S K m)] with p hp
    simpa only [r11bFiniteSynthesis, Finset.sum_empty, Pi.zero_apply] using hp
  add_mem' := by
    classical
    rintro u v ⟨s, a, ha, hu⟩ ⟨t, c, hc, hv⟩
    let d : ℕ → ℕ → ℝ → ℝ := fun m i r =>
      (if i ∈ s then a m i r else 0) + (if i ∈ t then c m i r else 0)
    refine ⟨s ∪ t, d, ?_, ?_⟩
    · intro m i
      have ha' : MemLp (fun r => if i ∈ s then a m i r else 0) 2
          (volume.restrict (Ioo (K.left m) (K.right m))) := by
        by_cases hi : i ∈ s
        · simpa only [ite_eq_left hi] using ha m i
        · simpa only [ite_eq_right hi] using
            (MemLp.zero' : MemLp (fun _ : ℝ => (0 : ℝ)) 2 _)
      have hc' : MemLp (fun r => if i ∈ t then c m i r else 0) 2
          (volume.restrict (Ioo (K.left m) (K.right m))) := by
        by_cases hi : i ∈ t
        · simpa only [ite_eq_left hi] using hc m i
        · simpa only [ite_eq_right hi] using
            (MemLp.zero' : MemLp (fun _ : ℝ => (0 : ℝ)) 2 _)
      exact ha'.add hc'
    · intro m j
      change ((u.val m j + v.val m j : CanonicalL2 S K m) : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] _
      filter_upwards [Lp.coeFn_add (u.val m j) (v.val m j), hu m j, hv m j]
        with p hp hpu hpv
      simp only [Pi.add_apply] at hp
      have hs : s ⊆ s ∪ t := Finset.subset_union_left
      have ht : t ⊆ s ∪ t := Finset.subset_union_right
      rw [hp, hpu, hpv,
        ← congrFun (n06_finiteSynthesis_extend hs
          (a m) (fun i => iteratedDeriv j.val (referenceAngularBasis i))) p,
        ← congrFun (n06_finiteSynthesis_extend ht
          (c m) (fun i => iteratedDeriv j.val (referenceAngularBasis i))) p]
      simp only [r11bFiniteSynthesis, d, add_mul, Finset.sum_add_distrib]
  smul_mem' := by
    rintro c v ⟨s, a, ha, hv⟩
    refine ⟨s, fun m i r => c * a m i r, fun m i => (ha m i).const_mul c, ?_⟩
    intro m j
    change ((c • v.val m j : CanonicalL2 S K m) : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] _
    filter_upwards [Lp.coeFn_smul c (v.val m j), hv m j] with p hp hq
    simp only [Pi.smul_apply, smul_eq_mul] at hp
    rw [hp, hq]
    simp only [r11bFiniteSynthesis, Finset.mul_sum, mul_assoc]

theorem n06VolumeFourierCut_mem_finiteAngularCore (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b N : ℕ) (v : V.level γ t b) :
    n06VolumeFourierCut hV γ t b N v ∈ n06VolumeFiniteAngularCore γ t b := by
  refine ⟨Finset.range (N + 1), fun m => n06HalfCosineCoefficient (v.val m 0), ?_, ?_⟩
  · intro m i
    exact (n06_canonical_angularCoefficient_memLp (v.val m 0)
      (memLp_angleMeasure_of_continuous (contDiff_referenceAngularBasis i).continuous)).const_mul
        Real.pi⁻¹
  · exact n06VolumeFourierCut_coe_cosine_jet hV γ t b N v

/-- Forgetting the material normalization preserves genuine finite angular
support, with radial coefficients in each original unweighted L2 interval. -/
theorem n06VolumeFiniteAngularCore_forget (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) {v : V.level γ t b}
    (hv : v ∈ n06VolumeFiniteAngularCore γ t b) :
    ∃ s : Finset ℕ, ∃ a : ℕ → ℕ → ℝ → ℝ,
      (∀ m i, MemLp (a m i) 2 (volume.restrict (Ioo (K.left m) (K.right m)))) ∧
      ∀ m, (V.forget γ t b v m : PolarPoint → ℝ) =ᵐ[canonicalMeasure S K m]
        r11bFiniteSynthesis s (a m) referenceAngularBasis := by
  obtain ⟨s, a, ha, he⟩ := hv
  let w (m : ℕ) : ℝ := T.M (T.sample (K.cell m)) ^ (-t) * T.H (T.sample (K.cell m)) ^ γ
  refine ⟨s, fun m i r => w m * a m i r, fun m i => (ha m i).const_mul (w m), ?_⟩
  intro m
  rw [hV.2.2.2 γ t b v m]
  filter_upwards [Lp.coeFn_smul (w m) (v.val m 0), he m 0] with p hp hq
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  rw [hp, hq]
  simp only [Fin.val_zero, iteratedDeriv_zero, r11bFiniteSynthesis, Finset.mul_sum, mul_assoc]

theorem n06VolumeFiniteAngularCore_dense (hV : IsVolumeModel T S K V)
    (γ t : ℝ) (b : ℕ) :
    Dense (n06VolumeFiniteAngularCore (V := V) γ t b : Set (V.level γ t b)) := by
  intro v
  have hv : v ∈ (n06VolumeFiniteAngularCore (V := V) γ t b).topologicalClosure := by
    apply (n06VolumeFiniteAngularCore (V := V) γ t b).isClosed_topologicalClosure.mem_of_tendsto
      (n06VolumeFourierCut_tendsto hV γ t b v)
    exact Eventually.of_forall (fun N =>
      (n06VolumeFiniteAngularCore (V := V) γ t b).le_topologicalClosure
        (n06VolumeFourierCut_mem_finiteAngularCore hV γ t b N v))
  change v ∈ ((n06VolumeFiniteAngularCore (V := V) γ t b).topologicalClosure :
    Set (V.level γ t b)) at hv
  rw [Submodule.topologicalClosure_coe] at hv
  exact hv

end ContinuousFlexibility.Statements
