/-
  034_policy_adaptive_adversary.lean

  Catalog ID 34.  Paper 2 (NEO), Lemma 5.

  Author : Shawn Kevin Jason
  Repo   : github.com/shawnjason/Non-Locality  (existing)

  Policy-Adaptive Adversary Construction.

  For any deterministic forward-local policy, there exists an
  admissible environment in which the policy is driven into
  non-extendable commitment.  The adversary exploits two facts:
  (1) the bounded observation window cannot distinguish certain
  extendable from non-extendable futures (the divergence witness,
  catalog ID 31), and (2) a deterministic policy produces the
  same action for observationally equivalent states, so the
  adversary can force that action to occur in the non-extendable
  context.

  This file formalizes the one-step adversarial construction.
  The paper's "block concatenation forces arbitrarily many
  commitments" extends this by iterating; the essential mechanism
  is the single-step version here.

  Standalone (deliberately so for per-file verification on
  live.lean-lang.org).
-/

import Mathlib

namespace NEO.PolicyAdaptiveAdversary

variable {State Obs Action : Type}

-- Observation function: maps a state to the policy's visible window.
variable (observe : State → Obs)

-- Commit function: applies an action to a state, producing the successor.
variable (commit : State → Action → State)

-- Extendability predicate: whether at least one admissible completion exists.
variable (extendable : State → Prop)

/-- **Deterministic Same-Action Lemma.**

    A deterministic policy (encoded as a function `Obs → Action`)
    produces the same action on observationally equivalent states.
    Formal content of "forward-local determinism": same
    observations ⟹ same commitment. -/
theorem deterministic_same_action
    (π : Obs → Action) {s₁ s₂ : State}
    (h_obs_eq : observe s₁ = observe s₂) :
    π (observe s₁) = π (observe s₂) := by
  rw [h_obs_eq]

/-- **Policy-Adaptive Adversary** (NEO Lemma 5, Catalog ID 34).

    Given:
      • two admissible (extendable) states `s₁`, `s₂` with the
        same observation (the divergence witness, catalog ID 31),
      • the property that committing `π`'s action (computed from
        `s₁`'s observation) in state `s₂` makes `s₂` non-extendable
        (the adversarial trap),

    there exists an admissible state where `π`'s deterministic
    commitment leads to a non-extendable outcome.

    The proof: the adversary presents `s₂` (which looks like `s₁`
    to the policy).  The policy deterministically commits the
    same action it would in `s₁`.  The `rwa [← h_obs_eq]` step
    is the formal crux — substituting the equivalent observation
    closes the gap between "action computed from `s₁`'s view" and
    "action computed from `s₂`'s own view." -/
theorem policy_adaptive_adversary
    (π : Obs → Action)
    {s₁ s₂ : State}
    (h_obs_eq : observe s₁ = observe s₂)
    (h_s₂_ext : extendable s₂)
    (h_diverge : ¬ extendable (commit s₂ (π (observe s₁)))) :
    ∃ s : State, extendable s ∧ ¬ extendable (commit s (π (observe s))) := by
  refine ⟨s₂, h_s₂_ext, ?_⟩
  rwa [← h_obs_eq]

end NEO.PolicyAdaptiveAdversary