module

public import ContinuousFlexibility.Analysis.N07aAngularPeriodMeasure
public import ContinuousFlexibility.Analysis.N07aAngularEven
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Genuine periodic even representatives of the canonical reflection class

Only the angular variable is extended. The representative agrees with the
given L² class on its prescribed half period, so no radial periodicity or
smoothness across the radial endpoints is required.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- The upstream `SFinite angleMeasure` instances are private to their modules. -/
private instance : MeasureTheory.SFinite ContinuousFlexibility.Statements.angleMeasure := by
  unfold ContinuousFlexibility.Statements.angleMeasure; infer_instance

open Set Filter MeasureTheory ContinuousFlexibility.Statements

def n07aAngularPeriodicRepresentative (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  u (p.1, toIocMod Real.pi_pos 0 p.2)

theorem n07aAngularPeriodicRepresentative_periodic (u : PolarPoint → ℝ) (r : ℝ) :
    Function.Periodic (fun θ => n07aAngularPeriodicRepresentative u (r, θ)) Real.pi := by
  intro θ
  simp only [n07aAngularPeriodicRepresentative, toIocMod_add_right]

def n07aAngularEvenRepresentative (u : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  (n07aAngularPeriodicRepresentative u p +
    n07aAngularPeriodicRepresentative u (p.1, -p.2)) / 2

theorem n07aAngularEvenRepresentative_periodic (u : PolarPoint → ℝ) (r : ℝ) :
    Function.Periodic (fun θ => n07aAngularEvenRepresentative u (r, θ)) Real.pi := by
  intro θ
  dsimp only [n07aAngularEvenRepresentative]
  have h₁ : n07aAngularPeriodicRepresentative u (r, θ + Real.pi) =
      n07aAngularPeriodicRepresentative u (r, θ) :=
    n07aAngularPeriodicRepresentative_periodic u r θ
  have h₂ : n07aAngularPeriodicRepresentative u (r, -θ - Real.pi) =
      n07aAngularPeriodicRepresentative u (r, -θ) :=
    (n07aAngularPeriodicRepresentative_periodic u r).sub_eq (-θ)
  rw [h₁,
    show -(θ + Real.pi) = -θ - Real.pi by ring,
    h₂]

theorem n07aAngularEvenRepresentative_even (u : PolarPoint → ℝ) (r : ℝ) :
    Function.Even (fun θ => n07aAngularEvenRepresentative u (r, θ)) := by
  intro θ
  simp only [n07aAngularEvenRepresentative, neg_neg]
  ring

theorem n07aAngularEvenRepresentative_periodic_pair (u : PolarPoint → ℝ) :
    Function.Periodic (n07aAngularEvenRepresentative u) (0, Real.pi) := by
  rintro ⟨r, θ⟩
  simpa only [Prod.mk_add_mk, add_zero] using n07aAngularEvenRepresentative_periodic u r θ

private theorem n07aAngleMod_neg {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    toIocMod Real.pi_pos 0 (-θ) = Real.pi - θ := by
  calc
    _ = toIocMod Real.pi_pos 0 (Real.pi - θ) := by
      simpa only [sub_eq_add_neg] using (toIocMod_add_left Real.pi_pos 0 (-θ)).symm
    _ = _ := (toIocMod_eq_self Real.pi_pos).mpr (by
      simp only [zero_add, mem_Ioc]
      constructor <;> linarith [hθ.1, hθ.2])

theorem n07aAngularEvenRepresentative_ae {μ : Measure ℝ} [SFinite μ]
    (u : PolarPoint → ℝ)
    (he : (fun p : PolarPoint => u (p.1, Real.pi - p.2)) =ᵐ[μ.prod angleMeasure] u) :
    n07aAngularEvenRepresentative u =ᵐ[μ.prod angleMeasure] u := by
  have hθ : ∀ᵐ θ ∂angleMeasure, θ ∈ Ioo (0 : ℝ) Real.pi := by
    change ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) Real.pi), θ ∈ Ioo (0 : ℝ) Real.pi
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := angleMeasure)).ae hθ
  filter_upwards [he, hprod] with p hp hθp
  have hself : toIocMod Real.pi_pos 0 p.2 = p.2 :=
    (toIocMod_eq_self Real.pi_pos).mpr (by simpa only [zero_add] using Ioo_subset_Ioc_self hθp)
  simp only [n07aAngularEvenRepresentative, n07aAngularPeriodicRepresentative,
    hself, n07aAngleMod_neg hθp, hp]
  ring

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

theorem n07aCanonicalEvenRepresentative_ae (u : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) :
    n07aAngularEvenRepresentative u =ᵐ[canonicalMeasure S K m] u := by
  have he := (n07aAngularReflection_fixed_iff m u).mp hu
  let f : PolarPoint → ℝ := u
  change n07aAngularEvenRepresentative f =ᵐ[canonicalMeasure S K m] f
  change (fun p : PolarPoint => f (p.1, Real.pi - p.2)) =ᵐ[canonicalMeasure S K m] f at he
  rw [n07aCanonicalMeasure_eq_prod] at he ⊢
  exact n07aAngularEvenRepresentative_ae f he

theorem n07aCanonicalEvenRepresentative_memLp (u : CanonicalL2 S K m)
    (hu : n07aAngularReflection m u = u) :
    MemLp (n07aAngularEvenRepresentative u) 2
      ((volume.restrict (Ioo (K.left m) (K.right m))).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  exact n07aCanonical_memLp_full_of_periodic
    ((memLp_congr_ae (n07aCanonicalEvenRepresentative_ae u hu)).mpr (Lp.memLp u))
    (Eventually.of_forall (n07aAngularEvenRepresentative_periodic u))

end ContinuousFlexibility.Analysis
