import GlimpseOfLean.Library.Basic

namespace Introduction

def seq_limit(u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) :=by {
    unfold seq_limit
    intros ε hε

    obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
    -- 根据 `u` 在这个 `δ` 上的假设，我们得到一个自然数 `N` ，使得对于每个自然数 `n` ，如果 `n ≥ N` ，则 `|u_n - x₀| ≤ δ` (2)。
    obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
    -- 我们证明 `N` 是合适的。
    use N
    -- 取一个大于等于 `N` 的 `n` 。我们证明 `|f(u_n) - f(x₀)| ≤ ε`。
    intros n hn
    -- 根据 (1) 对 `u_n` 的应用，我们只需证明 `|u_n - x₀| ≤ δ`。
    apply Hf
    exact Hu n hn
    
  }
