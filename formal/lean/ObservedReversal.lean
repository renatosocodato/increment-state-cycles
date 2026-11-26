import IncrementCycles
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
namespace IncrementCycles
namespace ObservedReversal

noncomputable section
variable {H A : Type*} [Fintype H]

/-- Likelihood of a given hidden path and observed word for a finite HMM
with constant stationary mass per hidden state. -/
def joint {n : ℕ} (mass : ℝ) (K : H → H → ℝ) (e : H → A → ℝ)
    (x : Fin (n+1) → H) (w : Fin (n+1) → A) : ℝ :=
  mass * (∏ i : Fin n, K (x i.castSucc) (x i.succ)) *
    ∏ i, e (x i) (w i)

def observed {n : ℕ} (mass : ℝ) (K : H → H → ℝ) (e : H → A → ℝ)
    (w : Fin (n+1) → A) : ℝ :=
  ∑ x : Fin (n+1) → H, joint mass K e x w

def rev {m : ℕ} {B : Type*} (par : B → B) (x : Fin m → B) (i : Fin m) : B :=
  par (x i.rev)

omit [Fintype H] in
theorem joint_reversal {n : ℕ} (mass : ℝ) (K : H → H → ℝ) (e : H → A → ℝ)
    (θ : H → H) (ε : A → A) (hk : ∀ i j, K (θ j) (θ i) = K i j)
    (he : ∀ i a, e (θ i) (ε a) = e i a) (x : Fin (n+1) → H) (w : Fin (n+1) → A) :
    joint mass K e (rev θ x) (rev ε w) = joint mass K e x w := by
  have hK : (∏ i : Fin n, K (rev θ x i.castSucc) (rev θ x i.succ)) =
      ∏ i : Fin n, K (x i.castSucc) (x i.succ) := by
    simp only [rev, Fin.rev_castSucc, Fin.rev_succ, hk]
    exact Equiv.prod_comp Fin.revPerm (fun i : Fin n => K (x i.castSucc) (x i.succ))
  have hE : (∏ i, e (rev θ x i) (rev ε w i)) = ∏ i, e (x i) (w i) := by
    simp only [rev, he]
    exact Equiv.prod_comp Fin.revPerm (fun i => e (x i) (w i))
  simp only [joint, hK, hE]

theorem observed_reversal {n : ℕ} (mass : ℝ) (K : H → H → ℝ) (e : H → A → ℝ)
    (θ : H → H) (ε : A → A) (ht : Function.Involutive θ)
    (hk : ∀ i j, K (θ j) (θ i) = K i j) (he : ∀ i a, e (θ i) (ε a) = e i a)
    (w : Fin (n+1) → A) :
    observed mass K e (rev ε w) = observed mass K e w := by
  classical
  have hr : Function.Involutive (rev (m := n+1) θ) := by
    intro x
    funext i
    simpa only [rev, Fin.rev_rev] using ht (x i)
  let p := hr.toPerm (rev θ)
  unfold observed
  calc
    _ = ∑ x, joint mass K e (rev θ x) (rev ε w) :=
      (Equiv.sum_comp p (fun x => joint mass K e x (rev ε w))).symm
    _ = _ := Finset.sum_congr rfl (fun x _ => joint_reversal mass K e θ ε hk he x w)

/-- The stationary twelve-phase control with independent replacement emissions
has identical probabilities for a word and its physical reverse at every length. -/
theorem control_observed_words {n : ℕ} (ρ η : ℝ) (w : Fin (n+1) → S) :
    observed (1/12) (controlKernel ρ) (fun i a => em η (ctrlEmission i) a) (rev flip w) =
    observed (1/12) (controlKernel ρ) (fun i a => em η (ctrlEmission i) a) w := by
  apply observed_reversal _ _ _ ctrlTheta
  · exact (by decide : ∀ i : Bool × Fin 6, ctrlTheta (ctrlTheta i) = i)
  · intro i j
    exact (ctrl_kernel_reversal ρ i j).symm
  · intro i a
    simpa only [ctrl_reflect] using ctrl_emission_parity η (ctrlEmission i) a

end
end ObservedReversal
end IncrementCycles
