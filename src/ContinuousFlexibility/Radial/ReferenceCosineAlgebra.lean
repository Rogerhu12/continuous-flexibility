import ContinuousFlexibility.Radial.ReferenceCosineWeighted

/-!
# Algebra of the actual finite cosine projections

The coefficient and pairing identities use the genuine L² inner product.
They include finite-sum reproduction, self-adjointness, and the exact
half-turn and reflection symmetries of projected fields.
-/

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace InnerProductSpace

namespace ContinuousFlexibility.Radial

open ContinuousFlexibility.Statements

noncomputable section

theorem referenceAngularCoefficient_add {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (n : ℕ) :
    referenceAngularCoefficient (fun θ => f θ + g θ) n =
      referenceAngularCoefficient f n + referenceAngularCoefficient g n := by
  let hF := memLp_referenceAngularProbability hf
  let hG := memLp_referenceAngularProbability hg
  have he : ((hF.add hG).toLp (fun θ => f θ + g θ)) = hF.toLp f + hG.toLp g :=
    hF.toLp_add hG
  rw [referenceAngularCoefficient_eq_inner (hF.add hG), he, inner_add_right,
    ← referenceAngularCoefficient_eq_inner hF, ← referenceAngularCoefficient_eq_inner hG]

theorem referenceAngularCoefficient_sub {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) (n : ℕ) :
    referenceAngularCoefficient (fun θ => f θ - g θ) n =
      referenceAngularCoefficient f n - referenceAngularCoefficient g n := by
  let hF := memLp_referenceAngularProbability hf
  let hG := memLp_referenceAngularProbability hg
  have he : ((hF.sub hG).toLp (fun θ => f θ - g θ)) = hF.toLp f - hG.toLp g :=
    hF.toLp_sub hG
  rw [referenceAngularCoefficient_eq_inner (hF.sub hG), he, inner_sub_right,
    ← referenceAngularCoefficient_eq_inner hF, ← referenceAngularCoefficient_eq_inner hG]

theorem continuous_sum_referenceAngularBasis (I : Finset ℕ) (c : ℕ → ℝ) :
    Continuous (fun θ => ∑ n ∈ I, c n * referenceAngularBasis n θ) := by
  apply continuous_finset_sum
  intro n _hn
  exact continuous_const.mul (contDiff_referenceAngularBasis n).continuous

theorem memLp_sum_referenceAngularBasis (I : Finset ℕ) (c : ℕ → ℝ) :
    MemLp (fun θ => ∑ n ∈ I, c n * referenceAngularBasis n θ) 2 referenceAngularProbability :=
  memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (continuous_sum_referenceAngularBasis I c))

theorem toLp_sum_referenceAngularBasis (I : Finset ℕ) (c : ℕ → ℝ) :
    (memLp_sum_referenceAngularBasis I c).toLp
      (fun θ => ∑ n ∈ I, c n * referenceAngularBasis n θ) =
        ∑ n ∈ I, c n • referenceAngularBasisL2 n := by
  have he (n : ℕ) :
      ((c n • referenceAngularBasisL2 n : Lp ℝ 2 referenceAngularProbability) : ℝ → ℝ) =ᵐ[referenceAngularProbability]
        (fun θ => c n * referenceAngularBasis n θ) := by
    filter_upwards [Lp.coeFn_smul (c n) (referenceAngularBasisL2 n),
      (memLp_referenceAngularBasis n).coeFn_toLp] with θ hs hb
    calc
      ((c n • referenceAngularBasisL2 n : Lp ℝ 2 referenceAngularProbability) : ℝ → ℝ) θ =
          c n * (referenceAngularBasisL2 n : ℝ → ℝ) θ := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hs
      _ = c n * referenceAngularBasis n θ := congrArg (fun z : ℝ => c n * z) hb
  apply Lp.ext
  filter_upwards [(memLp_sum_referenceAngularBasis I c).coeFn_toLp,
    Lp.coeFn_fun_finsetSum I (fun n => c n • referenceAngularBasisL2 n),
    ae_all_iff.mpr he] with θ hsum hLp hθ
  rw [hsum, hLp]
  exact Finset.sum_congr rfl (fun n _ => (hθ n).symm)

theorem referenceAngularCoefficient_sum_basis (I : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    referenceAngularCoefficient (fun θ => ∑ n ∈ I, c n * referenceAngularBasis n θ) k =
      if k ∈ I then c k else 0 := by
  rw [referenceAngularCoefficient_eq_inner (memLp_sum_referenceAngularBasis I c),
    toLp_sum_referenceAngularBasis]
  by_cases hk : k ∈ I
  · rw [if_pos hk]
    exact orthonormal_referenceAngularBasisL2.inner_right_sum c hk
  · rw [if_neg hk, inner_sum]
    apply Finset.sum_eq_zero
    intro n hn
    have hkn : k ≠ n := fun h => hk (h.symm ▸ hn)
    rw [inner_smul_right, orthonormal_referenceAngularBasisL2.inner_eq_zero hkn, mul_zero]

theorem referenceAngularCoefficient_projection (I : Finset ℕ) (f : ℝ → ℝ) (n : ℕ) :
    referenceAngularCoefficient (angularBasisProjection I f) n =
      if n ∈ I then referenceAngularCoefficient f n else 0 :=
  referenceAngularCoefficient_sum_basis I (referenceAngularCoefficient f) n

theorem angularBasisProjection_sum_basis (I J : Finset ℕ) (hJI : J ⊆ I) (c : ℕ → ℝ) :
    angularBasisProjection I (fun θ => ∑ n ∈ J, c n * referenceAngularBasis n θ) =
      (fun θ => ∑ n ∈ J, c n * referenceAngularBasis n θ) := by
  funext θ
  unfold angularBasisProjection
  simp_rw [referenceAngularCoefficient_sum_basis]
  calc
    (∑ n ∈ I, (if n ∈ J then c n else 0) * referenceAngularBasis n θ) =
        ∑ n ∈ J, (if n ∈ J then c n else 0) * referenceAngularBasis n θ := by
      symm
      apply Finset.sum_subset hJI
      intro n _hnI hnJ
      simp only [if_neg hnJ, zero_mul]
    _ = _ := Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])

theorem angularBasisProjection_pairing {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (I : Finset ℕ) (f : ℝ → ℝ) :
    radialAngularMean (fun θ => angularBasisProjection I f θ * g θ) =
      ∑ n ∈ I, referenceAngularCoefficient f n * referenceAngularCoefficient g n := by
  let hp := memLp_referenceAngularProbability
    (memLp_referenceAngular_interval_of_continuous (continuous_angularBasisProjection I f))
  let hG := memLp_referenceAngularProbability hg
  rw [← integral_referenceAngularProbability, ← reference_memLp_inner_eq_integral hp hG,
    angularBasisProjection_toLp, sum_inner]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [inner_smul_left, ← referenceAngularCoefficient_eq_inner hG]
  simp only [conj_trivial]

theorem angularBasisProjection_pairing_symm {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    (I : Finset ℕ) :
    radialAngularMean (fun θ => angularBasisProjection I f θ * g θ) =
      radialAngularMean (fun θ => f θ * angularBasisProjection I g θ) := by
  have he : (fun θ => f θ * angularBasisProjection I g θ) =
      (fun θ => angularBasisProjection I g θ * f θ) := funext fun _ => mul_comm _ _
  rw [he, angularBasisProjection_pairing hg, angularBasisProjection_pairing hf]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem referenceAngularBasis_periodic (n : ℕ) :
    Function.Periodic (referenceAngularBasis n) Real.pi := by
  cases n with
  | zero => exact fun _ => rfl
  | succ n => exact cosineMode_even_frequency_periodic (n + 1)

theorem referenceAngularBasis_even (n : ℕ) : Function.Even (referenceAngularBasis n) := by
  cases n with
  | zero => exact fun _ => rfl
  | succ n => exact cosineMode_even (2 * (n + 1))

theorem referenceBasisProjection_periodic (I : Finset ℕ) (u : PolarPoint → ℝ) :
    Function.Periodic (referenceBasisProjection I u) (0, Real.pi) := by
  intro x
  simp only [referenceBasisProjection, angularBasisProjection, Prod.fst_add, Prod.snd_add, add_zero]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [referenceAngularBasis_periodic n x.2]

theorem referenceBasisProjection_even (I : Finset ℕ) (u : PolarPoint → ℝ) (r θ : ℝ) :
    referenceBasisProjection I u (r, -θ) = referenceBasisProjection I u (r, θ) := by
  change (∑ n ∈ I, referenceRadialCoefficient u n r * referenceAngularBasis n (-θ)) =
    ∑ n ∈ I, referenceRadialCoefficient u n r * referenceAngularBasis n θ
  exact Finset.sum_congr rfl (fun n _ => by rw [referenceAngularBasis_even n θ])

theorem referenceCosineProjection_periodic (J : Finset ℕ) (u : PolarPoint → ℝ) :
    Function.Periodic (referenceCosineProjection J u) (0, Real.pi) := by
  rw [referenceCosineProjection_eq_basis]
  exact referenceBasisProjection_periodic _ _

theorem referenceCosineProjection_even (J : Finset ℕ) (u : PolarPoint → ℝ) (r θ : ℝ) :
    referenceCosineProjection J u (r, -θ) = referenceCosineProjection J u (r, θ) := by
  rw [referenceCosineProjection_eq_basis]
  exact referenceBasisProjection_even _ _ _ _

end

end ContinuousFlexibility.Radial
