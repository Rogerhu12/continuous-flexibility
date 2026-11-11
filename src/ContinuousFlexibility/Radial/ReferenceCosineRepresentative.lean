import ContinuousFlexibility.Radial.ReferenceCosineL2
import ContinuousFlexibility.Radial.ReferenceCirclePullback

/-!
# Pointwise even and periodic representatives of cosine synthesis

Reflection is a continuous isometry of the actual product L² space.
Every cosine term is fixed by it, hence so is the convergent synthesis.
Averaging a representative with its reflection then gives a pointwise
even representative, and pullback from the period-π circle gives exact
π-periodicity on the whole physical plane.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

theorem referenceCircleReflection_measurePreserving :
    MeasurePreserving (fun z : α × AddCircle Real.pi => (z.1, -z.2))
      (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)))
      (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) :=
  (MeasurePreserving.id μ).prod (Measure.measurePreserving_neg AddCircle.haarAddCircle)

def referenceCircleReflection :
    Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) →ₗᵢ[ℝ]
      Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))) :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (fun z : α × AddCircle Real.pi => (z.1, -z.2))
    referenceCircleReflection_measurePreserving

theorem referenceCircleReflection_ae
    (v : Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)))) :
    referenceCircleReflection v =ᵐ[μ.prod AddCircle.haarAddCircle]
      fun z : α × AddCircle Real.pi => v (z.1, -z.2) :=
  Lp.coeFn_compMeasurePreserving v referenceCircleReflection_measurePreserving

theorem referenceCircleReflection_tensor (f : Lp ℝ 2 μ) (n : ℕ) :
    referenceCircleReflection (referenceL2Tensor f (referenceCircleCosineLp n)) =
      referenceL2Tensor f (referenceCircleCosineLp n) := by
  have hg : ∀ᵐ z : α × AddCircle Real.pi ∂μ.prod AddCircle.haarAddCircle,
      referenceCircleCosineLp n z.2 = referenceCircleCosine n z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ)
      (ν := (AddCircle.haarAddCircle : Measure (AddCircle Real.pi)))).ae
        (referenceCircleCosineLp_ae n)
  have hgneg := (referenceCircleReflection_measurePreserving (μ := μ)).quasiMeasurePreserving.ae hg
  have htneg := (referenceCircleReflection_measurePreserving (μ := μ)).quasiMeasurePreserving.ae
    (referenceL2Tensor_ae f (referenceCircleCosineLp n))
  apply Lp.ext
  filter_upwards [referenceCircleReflection_ae
      (referenceL2Tensor f (referenceCircleCosineLp n)),
    referenceL2Tensor_ae f (referenceCircleCosineLp n), htneg, hg, hgneg]
    with z href ht htn hg hgn
  change referenceCircleReflection (referenceL2Tensor f (referenceCircleCosineLp n)) z =
    referenceL2Tensor f (referenceCircleCosineLp n) (z.1, -z.2) at href
  change referenceL2Tensor f (referenceCircleCosineLp n) z =
    f z.1 * referenceCircleCosineLp n z.2 at ht
  change referenceCircleCosineLp n z.2 = referenceCircleCosine n z.2 at hg
  change referenceL2Tensor f (referenceCircleCosineLp n) (z.1, -z.2) =
    f z.1 * referenceCircleCosineLp n (-z.2) at htn
  change referenceCircleCosineLp n (-z.2) = referenceCircleCosine n (-z.2) at hgn
  rw [href, htn, ht, hg, hgn, referenceCircleCosine_even]

/-- Reflection invariance passes to the genuine L² limit. -/
theorem referenceCircleReflection_synthesis (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    referenceCircleReflection (referenceCosineL2Synthesis f) =
      referenceCosineL2Synthesis f := by
  have hs := referenceCosineL2Synthesis_hasSum f
  have hr := hs.mapL (referenceCircleReflection (μ := μ)).toContinuousLinearMap
  have hr' : HasSum (fun n => referenceL2Tensor (f n) (referenceCircleCosineLp n))
      (referenceCircleReflection (referenceCosineL2Synthesis f)) := by
    simpa only [referenceCircleReflection_tensor] using hr
  exact hr'.unique hs

/-- Pointwise reflection averaging, before pullback to the physical angle. -/
def referenceCircleEvenRepresentative
    (v : Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))))
    (z : α × AddCircle Real.pi) : ℝ :=
  (v z + v (z.1, -z.2)) / 2

theorem referenceCircleEvenRepresentative_ae
    (v : Lp ℝ 2 (μ.prod (AddCircle.haarAddCircle : Measure (AddCircle Real.pi))))
    (hv : referenceCircleReflection v = v) :
    referenceCircleEvenRepresentative v =ᵐ[μ.prod AddCircle.haarAddCircle] v := by
  have hr := referenceCircleReflection_ae v
  rw [hv] at hr
  filter_upwards [hr] with z hz
  change v z = v (z.1, -z.2) at hz
  unfold referenceCircleEvenRepresentative
  rw [← hz]
  ring

/-- A physical representative with pointwise evenness and π-periodicity. -/
def referenceCosineRepresentative (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2)
    (x : α × ℝ) : ℝ :=
  referenceCircleEvenRepresentative (referenceCosineL2Synthesis f)
    (x.1, (x.2 : AddCircle Real.pi))

theorem referenceCosineRepresentative_periodic
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) (r : α) :
    Function.Periodic (fun θ : ℝ => referenceCosineRepresentative f (r, θ)) Real.pi := by
  intro θ
  change referenceCircleEvenRepresentative (referenceCosineL2Synthesis f)
      (r, ((θ + Real.pi : ℝ) : AddCircle Real.pi)) =
    referenceCircleEvenRepresentative (referenceCosineL2Synthesis f)
      (r, (θ : AddCircle Real.pi))
  rw [AddCircle.coe_add_period]

theorem referenceCosineRepresentative_even
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) (r : α) (θ : ℝ) :
    referenceCosineRepresentative f (r, -θ) = referenceCosineRepresentative f (r, θ) := by
  unfold referenceCosineRepresentative referenceCircleEvenRepresentative
  simp only [AddCircle.coe_neg, neg_neg]
  ring

theorem referenceCosineRepresentative_ae
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    referenceCosineRepresentative f =ᵐ[μ.prod referenceAngularMeasure]
      referenceCirclePullback (referenceCosineL2Synthesis f) := by
  have hc := referenceCircleEvenRepresentative_ae
    (referenceCosineL2Synthesis f) (referenceCircleReflection_synthesis f)
  have hp := (referenceCircleProduct_measurePreserving (μ := μ)).quasiMeasurePreserving.ae hc
  exact hp.trans (referenceCirclePullback_ae (referenceCosineL2Synthesis f)).symm

theorem referenceCosineRepresentative_memLp
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    MemLp (referenceCosineRepresentative f) 2 (μ.prod referenceAngularMeasure) :=
  (memLp_congr_ae (referenceCosineRepresentative_ae f)).2
    (Lp.memLp (referenceCirclePullback (referenceCosineL2Synthesis f)))

theorem referenceCosineRepresentative_toLp
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    (referenceCosineRepresentative_memLp f).toLp (referenceCosineRepresentative f) =
      referenceCirclePullback (referenceCosineL2Synthesis f) := by
  apply Lp.ext
  exact (referenceCosineRepresentative_memLp f).coeFn_toLp.trans
    (referenceCosineRepresentative_ae f)

/-- Exact norm of the actual physical representative. -/
theorem referenceCosineRepresentative_norm_sq
    (f : lp (fun _ : ℕ => Lp ℝ 2 μ) 2) :
    ‖(referenceCosineRepresentative_memLp f).toLp (referenceCosineRepresentative f)‖ ^ 2 =
      ∑' n, ‖f n‖ ^ 2 := by
  rw [referenceCosineRepresentative_toLp, referenceCirclePullback_norm,
    referenceCosineL2Synthesis_norm_sq]

end ContinuousFlexibility.Statements
